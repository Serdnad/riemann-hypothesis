module

import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R]

private theorem dY_add (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (Y Y' : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (Y + Y') g = dY F ρ Y g + dY F ρ Y' g := by
  simp only [dY, Matrix.mul_add, Matrix.add_mul]
  abel

private theorem dY_zero (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (g : F.G₀) : dY F ρ 0 g = 0 := by
  simp [dY]

private theorem dY_smul (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (c : A) (Y : Matrix (Fin n) (Fin n) R) (g : F.G₀) :
    dY F ρ (c • Y) g = c • dY F ρ Y g := by
  simp only [dY, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private theorem ac_add {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f f' : Γ → R} (h : AdicCont I f)
    (h' : AdicCont I f') : AdicCont I fun g => f g + f' g := by
  intro N
  have key := (h N).add (h' N)
  convert key using 1
  funext g
  simp [map_add (f := _)]

private theorem ac_smul {Γ : Type} [TopologicalSpace Γ] {I : Ideal R} {f : Γ → R} (c : A) (h : AdicCont I f) :
    AdicCont I fun g => c • f g := by
  intro N
  have key := (h N).comp (fun x => Ideal.Quotient.mk (I ^ N) (algebraMap A R c) * x)
  convert key using 1
  funext g
  simp [Function.comp, Algebra.smul_def, map_mul]

end

theorem UpperTheory.V.Pa.Det.selSub :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), (∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = SelZ F t ρ w wi V) ∧ ∃ S : Submodule A (F.G₀ → Matrix (Fin n) (Fin n) R), (S : Set _) = Bd F ρ V := by
  apply UpperTheory.V.Pa.sel_lin <;> assumption
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem flagBasis_diag_mul {F : Type} [Field F] {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem flagBasis_conj {F : Type} [Field F] {n : ℕ} (b t : GL (Fin n) F)
    (hb : ∀ i j, j < i → b i j = 0) (ht : ∀ i j, j < i → t i j = 0) :
    (∀ i j, j < i → (b⁻¹ * t * b : GL (Fin n) F) i j = 0) ∧
      ∀ i, (b⁻¹ * t * b : GL (Fin n) F) i i = t i i := by
  have hbm : (b : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => hb i j h
  have htm : (t : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => ht i j h
  have hbi : ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
    letI := b.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hbm
  have hdiag : ∀ i, ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i *
      (b : Matrix (Fin n) (Fin n) F) i i = 1 := by
    intro i
    rw [← flagBasis_diag_mul hbi hbm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact ((hbi.mul htm).mul hbm) hij
  · rw [Units.val_mul, Units.val_mul, flagBasis_diag_mul (hbi.mul htm) hbm,
      flagBasis_diag_mul hbi htm, mul_right_comm, hdiag, one_mul]

theorem UpperTheory.V.Pa.Det.flagBasis :
    ∀ {K H : Type} [Field K] [Group H] {n a : ℕ} (r : H →* GL (Fin n) (PowerSeries K)) (ψ : Fin n → H →* (PowerSeries K)ˣ), (∀ g, mat r g ∈ Ev (PowerSeries K) (PowerSeries K) n a) → Function.Injective ψ → HasFlag (pushRep (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) r) (fun i => pushCh (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) (ψ i)) → ∃ (w : GL (Fin n) (PowerSeries K)) (ty : Fin n → Bool), (∀ i j : Fin n, decide ((i : ℕ) < a) ≠ ty j → w i j = 0) ∧ ∀ g, (∀ i j, j < i → (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j = 0) ∧ ∀ i, (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i i = (ψ i g : PowerSeries K) := by
  intro K H _ _ n a r ψ hev hinj hflag
  set ι := algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) with hι
  have hιi : Function.Injective ι := IsFractionRing.injective _ _
  haveI : Infinite (FractionRing (PowerSeries K)) := by
    refine Infinite.of_injective (fun m : ℕ => ι (PowerSeries.X ^ m)) ?_
    intro m k hmk
    have h := congrArg (fun p => PowerSeries.coeff (R := K) m p) (hιi hmk)
    simp only [PowerSeries.coeff_X_pow, if_true] at h
    by_contra hne
    rw [if_neg hne] at h
    exact one_ne_zero h
  have hev' : ∀ g, mat (pushRep ι r) g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a := by
    intro g
    have hg := hev g
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    have h0 := (Submodule.mem_bot _).1 ((hg i j).2 h)
    have e : mat (pushRep ι r) g i j = ι (mat r g i j) := rfl
    rw [e, h0, map_zero]
    exact Submodule.zero_mem _
  have hψ : Function.Injective (fun i => pushCh ι (ψ i)) := by
    intro i j hij
    apply hinj
    ext g
    have := congrArg (fun f : H →* (FractionRing (PowerSeries K))ˣ => ((f g : (FractionRing (PowerSeries K))ˣ) : FractionRing (PowerSeries K))) hij
    rw [hιi this]
  obtain ⟨w0, ty, hw0, htri⟩ := Det.flagF (pushRep ι r) (fun i => pushCh ι (ψ i)) hev' hψ hflag
  obtain ⟨w, b, hb, hwb, hw⟩ :=
    Det.exists_integral_block_iwasawa_decomposition (A := PowerSeries K) (fun i : Fin n => decide ((i : ℕ) < a)) ty w0 hw0
  refine ⟨w, ty, hw, fun g => ?_⟩
  have hmap : GeneralLinearGroup.map ι (w⁻¹ * r g * w) = b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b := by
    rw [map_mul, map_mul, map_inv, hwb, _root_.mul_inv_rev]
    simp only [pushRep, MonoidHom.comp_apply, mul_assoc]
  have hent : ∀ i j, ι ((w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j) =
      (b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b : GL (Fin n) (FractionRing (PowerSeries K))) i j := by
    intro i j
    rw [← hmap]
    rfl
  obtain ⟨hc1, hc2⟩ := flagBasis_conj b (w0⁻¹ * pushRep ι r g * w0) hb (htri g).1
  refine ⟨fun i j hij => hιi ?_, fun i => hιi ?_⟩
  · rw [hent, hc1 i j hij, map_zero]
  · rw [hent, hc2 i, (htri g).2 i]
    rfl
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.thickNonSS :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (q : PrimeSpectrum B.B), B.IsThick q → NonSS (augmentationIdealKernel B.u) (RingHom.id B.B) q.asIdeal := by
  intro l _ F O _ _ _ n r B q h
  have he : augmentationIdealKernel B.u = (B.GroupAlgebraKernelIdeal : Set (MonoidAlgebra B.B F.G₀)) := by
    have : B.u.D.chBar (pairGens B.u) = B.GroupAlgebraKernelIdeal := by
      unfold UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal UniversalOrdinaryDeterminantRing.E0gens GDet.chBar pairGens
      rw [Set.union_assoc]
    unfold augmentationIdealKernel
    rw [this]
    rfl
  refine ⟨B.kap q, inferInstance, B.toKap q, ?_, ?_⟩
  · ext x
    unfold UniversalOrdinaryDeterminantRing.toKap
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]
  · rw [RingHom.comp_id, he]
    exact h.2
end
