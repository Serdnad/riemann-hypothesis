module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E) (D : 𝓞 F), D ≠ 0 ∧ (∀ i, b i ∈ intOE E) ∧
      ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let β : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun j =>
    algebraMap (𝓞 E) E (NumberField.RingOfIntegers.basis E j)
  have hspanQ : Submodule.span ℚ (Set.range β) = ⊤ := by
    have h := (NumberField.integralBasis E).span_eq
    have hr : Set.range (NumberField.integralBasis E) = Set.range β := by
      ext x
      simp [β, NumberField.integralBasis_apply]
    rw [hr] at h
    exact h
  have hspan : Submodule.span F (Set.range β) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range β) := by rw [hspanQ]; exact Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ F _ hx
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent F (Set.range β)
  have hBfin : B.Finite := (Set.finite_range β).subset hBsub
  haveI := hBfin.fintype
  let e := Fintype.equivFin B
  let b0 : Module.Basis B F E := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, hspan])
  let b : Module.Basis (Fin (Fintype.card B)) F E := b0.reindex e
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    ((Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Fintype.card B))).image
      fun p => b.repr (β p.1) p.2)
  refine ⟨Fintype.card B, b, (D : 𝓞 F), nonZeroDivisors.ne_zero D.2, ?_, ?_⟩
  · intro i
    have hbi : b i = ((e.symm i : B) : E) := by simp [b, b0]
    obtain ⟨j, hj⟩ := hBsub (e.symm i).2
    rw [hbi, ← hj]
    exact RingHom.mem_range.mpr ⟨_, rfl⟩
  · intro x hx i
    obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
    have key : ∀ j, ((D : 𝓞 F) : F) * b.repr (β j) i ∈ (algebraMap (𝓞 F) F).range := by
      intro j
      obtain ⟨z, hz⟩ := hD (b.repr (β j) i) (Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩)
      refine RingHom.mem_range.mpr ⟨z, ?_⟩
      rw [hz, Algebra.smul_def]
    have hxe : algebraMap (𝓞 E) E y = ∑ j, ((NumberField.RingOfIntegers.basis E).repr y j) • β j := by
      conv_lhs => rw [← (NumberField.RingOfIntegers.basis E).sum_repr y]

      rw [map_sum]
      simp [β, map_zsmul]
    rw [hxe]

    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
    exact Subring.sum_mem _ fun j _ => Subring.zsmul_mem _ (key j) _

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coord {ι : Type} (b : Module.Basis ι F E) (i : ι) : AE F E →ₗ[F] AF F :=
  (TensorProduct.lid F (AF F)).toLinearMap ∘ₗ LinearMap.rTensor (AF F) (b.coord i)

theorem coord_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (e : E) (a : AF F) :
    coord b i (e ⊗ₜ[F] a) = b.repr e i • a := by
  simp [coord, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply]

theorem sum_coord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (x : AE F E) :
    ∑ i, b i ⊗ₜ[F] coord b i x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp only [coord_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul,
      Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem coord_mul_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (x : AE F E) (a : AF F) :
    coord b i (x * ((1 : E) ⊗ₜ[F] a)) = coord b i x * a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coord_tmul, coord_tmul, smul_mul_assoc]
  | add x y hx hy =>
    rw [add_mul, map_add (f := _), map_add (f := _), hx, hy, add_mul]

theorem continuous_coord {ι : Type} (b : Module.Basis ι F E) (i : ι) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (coord b i) := by
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  letI : Algebra (AF F) (AE F E) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let f : AE F E →ₗ[AF F] AF F :=
    { toFun := coord b i
      map_add' := map_add _
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [Algebra.smul_def, mul_comm,
          show algebraMap (AF F) (AE F E) r = (1 : E) ⊗ₜ[F] r from rfl, coord_mul_tmul, mul_comm] }
  exact IsModuleTopology.continuous_of_linearMap f

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end
