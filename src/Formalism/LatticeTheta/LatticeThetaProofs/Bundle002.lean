module

public import Formalism.LatticeTheta.Statement
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

@[expose] section

noncomputable section

namespace Formalism.H

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma dualLattice_innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  first
    | exact (LinearMap.BilinForm.nondegenerate_iff (innerₗ V)
        (fun x => by rw [innerₗ_apply_apply]; exact real_inner_self_nonneg) isSymm_inner).2
        (fun x => by rw [innerₗ_apply_apply]; exact inner_self_eq_zero)
    | (unfold LinearMap.BilinForm.Nondegenerate
       intro m hm
       have h := hm m
       rw [innerₗ_apply_apply] at h
       exact inner_self_eq_zero.mp h)

lemma innerₗ_isSymm : LinearMap.BilinForm.IsSymm (innerₗ V) := by
  first
    | exact fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _
    | exact ⟨fun x y => by
        simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _⟩
    | (intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)
    | (constructor; intro x y; simp only [innerₗ_apply_apply, RingHom.id_apply]; exact real_inner_comm _ _)

variable [FiniteDimensional ℝ V]

lemma exists_basis_span_eq (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (e : Module.Basis ι ℝ V),
      Submodule.span ℤ (Set.range e) = Λ := by
  classical
  exact ⟨Module.Free.ChooseBasisIndex ℤ Λ, inferInstance, inferInstance,
    Module.Basis.ofZLatticeBasis ℝ Λ (Module.Free.chooseBasis ℤ Λ),
    Module.Basis.ofZLatticeBasis_span ℝ Λ _⟩

lemma isLattice_of_eq_span {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ V) (L : Submodule ℤ V)
    (h : L = Submodule.span ℤ (Set.range e)) :
    DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
  subst h
  refine ⟨inferInstance, ?_⟩
  intro _
  infer_instance

lemma dualLattice_dual_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) =
      Submodule.span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ V) dualLattice_innerₗ_nondegenerate e)) := LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) dualLattice_innerₗ_nondegenerate e

end Formalism.H
end
end

section

open MeasureTheory Filter Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem innerₗ_nondegenerate : (innerₗ V : LinearMap.BilinForm ℝ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev dualB (e : Module.Basis ι ℝ V) : Module.Basis ι ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate e

theorem inner_dualB (e : Module.Basis ι ℝ V) (i j : ι) :
    ⟪dualB e i, e j⟫ = if j = i then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (innerₗ_nondegenerate (V := V)) e i j
  simpa using h

def dualVec (e : Module.Basis ι ℝ V) (m : ι → ℤ) : V := ∑ i, m i • dualB e i

theorem dualVec_eq (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m = ∑ i, (m i : ℝ) • dualB e i := by
  unfold dualVec
  exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℝ (m i) _).symm

theorem inner_dualVec_basis (e : Module.Basis ι ℝ V) (m : ι → ℤ) (j : ι) :
    ⟪dualVec e m, e j⟫ = m j := by
  rw [dualVec_eq, sum_inner]
  simp_rw [real_inner_smul_left, inner_dualB]
  simp

theorem dual_span_eq (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) = Submodule.span ℤ (Set.range (dualB e)) := by
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate e

theorem dualVec_mem (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m ∈ dual (Submodule.span ℤ (Set.range e)) := by
  rw [dual_span_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem dualVec_injective (e : Module.Basis ι ℝ V) : Function.Injective (dualVec e) := by
  intro m n h
  funext j
  have h1 := congrArg (fun x => ⟪x, e j⟫) h
  simp only [inner_dualVec_basis] at h1
  exact_mod_cast h1

theorem dualVec_surjective (e : Module.Basis ι ℝ V) (μ : V)
    (hμ : μ ∈ dual (Submodule.span ℤ (Set.range e))) : ∃ m, dualVec e m = μ := by
  rw [dual_span_eq] at hμ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hμ
  exact ⟨c, hc⟩

def dualEquiv (e : Module.Basis ι ℝ V) : (ι → ℤ) ≃ dual (Submodule.span ℤ (Set.range e)) :=
  Equiv.ofBijective (fun m => ⟨dualVec e m, dualVec_mem e m⟩)
    ⟨fun m n h => dualVec_injective e (congrArg Subtype.val h),
     fun μ => by
      obtain ⟨m, hm⟩ := dualVec_surjective e μ μ.2
      exact ⟨m, Subtype.ext hm⟩⟩

end Formalism.H
end
end
