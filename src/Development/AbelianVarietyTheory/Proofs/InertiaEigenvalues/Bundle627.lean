module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle537
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal

theorem phiW_inclL_E_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ c : ι → OA l O, inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • phiW t ϖ P (inclL t ϖ P c) = inclL t ϖ P (Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α Y hY c
  set s0 : OW l O := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hs0

  have key : Y.map (inclO l O) = s0 ^ α • frobMat t ϖ P := by
    ext i j
    obtain ⟨f, hf, hYij⟩ := hY i j
    rw [Matrix.map_apply, hYij, ← ϖ.iW_of_mem t K, Matrix.smul_apply, smul_eq_mul, hs0, ← ϖ.iTot_E t K,
      ← ϖ.iW_of_mem t K, ← map_pow, frobMat, Matrix.map_apply, Matrix.of_apply, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp only [Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, hf τ]
    rfl
  have key2 : (Y.map (frobOA l O)).map (inclO l O) =
      inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • (frobMat t ϖ P).map (frobOW l O) := by
    have h1 : (Y.map (frobOA l O)).map (inclO l O) = (Y.map (inclO l O)).map (frobOW l O) := by
      ext i j; simp only [Matrix.map_apply, frobOW_inclO]
    rw [h1, key]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hs0, frobOW_inclO]
  rw [inclL_apply, phiW_apply, inclL_apply]
  have h2 : (fun i => frobOW l O ((frobMat t ϖ P *ᵥ fun i => inclO l O (c i)) i)) =
      (frobMat t ϖ P).map (frobOW l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, frobOW_inclO]
  have h3 : (fun i => inclO l O ((Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) i)) =
      (Y.map (frobOA l O)).map (inclO l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [h2, h3, key2, Matrix.smul_mulVec, Matrix.mulVec_smul]

end GlobalTheory.BKReal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DenomCris

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem cc_one : WittVector.constantCoeff (1 : Ainf l) ≠ 0 := by
  obtain ⟨e, -, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI : Nontrivial (Per.Fl l) := ⟨e, 1, hne⟩
  rw [map_one]
  exact one_ne_zero

theorem cc_mul {x y : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (hy : WittVector.constantCoeff y ≠ 0) :
    WittVector.constantCoeff (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

theorem cc_pow {x : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (n : ℕ) :
    WittVector.constantCoeff (x ^ n) ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact cc_one
  | succ n ih => rw [pow_succ]; exact cc_mul ih hx

theorem exists_mul_eq_toOB (r : OB l O) : ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ a : OCr l O,
    ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) * r = toOB l O a := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul o y =>
    obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
    obtain ⟨n, a, ha⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne y
    refine ⟨(Per.tm e - 1) ^ n, cc_pow (GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne) n, o ⊗ₜ a, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change o ⊗ₜ[ℤ_[l]] (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Ainf l) (Per.Acris l) ((Per.tm e - 1) ^ n)) * y) =
      o ⊗ₜ[ℤ_[l]] algebraMap (Per.Acris l) (Per.Bcris l) a
    rw [map_pow, map_pow, mul_comm, ha]
  | add r₁ r₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) * a₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) * a₂, ?_⟩
    have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
        (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) * ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hm, map_add (f := _), map_mul (toOB l O), map_mul (toOB l O), hc, hc, ← e₁, ← e₂]
    ring

theorem exists_smul_eq_TWincl : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T), ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ β : TW (OCr l O) T, ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) • b = TWincl (toOB l O) T β := by
  intro l _ O K _ _ _ _ _ _ G _ _ T b
  have hsm : ∀ (r : OCr l O) (z : TW (OCr l O) T),
      TWincl (toOB l O) T (r • z) = toOB l O r • TWincl (toOB l O) T z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x t => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add (f := _), h₁, h₂, map_add (f := _), smul_add]
  have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
      (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul r t =>
    obtain ⟨s, hs, a, e⟩ := exists_mul_eq_toOB r
    exact ⟨s, hs, a ⊗ₜ t, by rw [TensorProduct.smul_tmul', smul_eq_mul, e]; rfl⟩
  | add b₁ b₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, β₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, β₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) • β₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) • β₂, ?_⟩
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) *
          ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [map_add (f := _), hsm, hsm, hc, hc, ← e₁, ← e₂, smul_smul, smul_smul, hm, smul_add, mul_comm (_ ⊗ₜ[ℤ_[l]] _)]

end GlobalTheory.DenomCris
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TensorOneInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  exact C.ι.domain_nontrivial

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  have := bcris_nontrivial l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) (PadicInt.unitCoeff h0 : ℤ_[l])) :=
    (PadicInt.unitCoeff h0).isUnit.map _
  exact (hu.mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)).ne_zero hx

theorem algebraMap_OB_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (algebraMap_injective l)
  have e : ⇑(algebraMap O (OB l O)) =
      (LinearMap.lTensor O (Algebra.linearMap ℤ_[l] (Per.Bcris l))) ∘ (TensorProduct.rid ℤ_[l] O).symm := by
    funext o
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e]
  exact h.comp (TensorProduct.rid ℤ_[l] O).symm.injective

theorem tensor_one_injective : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O),
    Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T
  haveI : Module.Free O ↥T.L.T := T.L.free
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap O (OB l O)) (algebraMap_OB_injective l O)
  have e : (fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x) =
      (LinearMap.rTensor (↥T.L.T) (Algebra.linearMap O (OB l O))) ∘ (TensorProduct.lid O ↥T.L.T).symm := by
    funext x
    simp [Algebra.TensorProduct.one_def]
  rw [e]
  exact h.comp (TensorProduct.lid O ↥T.L.T).symm.injective

end GlobalTheory.TensorOneInj
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CoordTW

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K]
  [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
  (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l])
  (hφ : ∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t)
  (R : Type) [CommRing R] [Algebra ℤ_[l] R]

def inner (t : ↥T.L.T) : O ⊗[ℤ_[l]] R →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun o => AddMonoidHom.mulLeft (algebraMap ℤ_[l] R (φ (o • t)))
      map_zero' := by ext r; simp
      map_add' := by intro a b; ext r; simp [add_smul, add_mul] }
    (fun z o r => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_mulLeft]
      rw [Algebra.smul_def z o, mul_smul, hφ, Algebra.smul_def z r, map_mul]; ring)

theorem inner_tmul (t : ↥T.L.T) (o : O) (r : R) :
    inner T φ hφ R t (o ⊗ₜ[ℤ_[l]] r) = algebraMap ℤ_[l] R (φ (o • t)) * r := by
  simp [inner]

theorem inner_add (t t' : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R (t + t') w = inner T φ hφ R t w + inner T φ hφ R t' w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp only [inner_tmul, smul_add, map_add (f := _), add_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; ring

theorem inner_zero (w : O ⊗[ℤ_[l]] R) : inner T φ hφ R 0 w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp [inner_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

theorem inner_smul (o : O) (t : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R t (o • w) = inner T φ hφ R (o • t) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o' r =>
    rw [TensorProduct.smul_tmul', inner_tmul, inner_tmul, smul_eq_mul, mul_smul, smul_comm o o' t]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

def coord : TW (O ⊗[ℤ_[l]] R) T →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun w =>
        { toFun := fun t => inner T φ hφ R t w
          map_zero' := inner_zero T φ hφ R w
          map_add' := fun t t' => inner_add T φ hφ R t t' w }
      map_zero' := by ext t; simp
      map_add' := by intro a b; ext t; simp }
    (fun o w t => by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; exact inner_smul T φ hφ R o t w)

theorem coord_tmul (w : O ⊗[ℤ_[l]] R) (t : ↥T.L.T) :
    coord T φ hφ R (w ⊗ₜ[O] t) = inner T φ hφ R t w := by
  simp [coord]

theorem coord_mul (a : R) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R (((1 : O) ⊗ₜ[ℤ_[l]] a : O ⊗[ℤ_[l]] R) • w) = a * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, smul_eq_mul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inner_tmul, inner_tmul]; ring
    | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy, mul_add]

theorem coord_one_tmul (t : ↥T.L.T) :
    coord T φ hφ R ((1 : O ⊗[ℤ_[l]] R) ⊗ₜ[O] t) = algebraMap ℤ_[l] R (φ t) := by
  rw [coord_tmul, Algebra.TensorProduct.one_def, inner_tmul, one_smul, mul_one]

theorem coord_algebraMap_smul (z : ℤ_[l]) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R ((algebraMap ℤ_[l] O z) • w) = algebraMap ℤ_[l] R z * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, inner_smul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [inner_tmul, inner_tmul, smul_comm o (algebraMap ℤ_[l] O z) t, hφ, map_mul]; ring
    | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy, mul_add]

theorem coord_toOB (w : TW (OCr l O) T) :
    coord T φ hφ (Per.Bcris l) (TWincl (toOB l O) T w) = acrisToBcris l (coord T φ hφ (Per.Acris l) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    simp only [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq,
      coord_tmul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [toOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, inner_tmul, map_mul,
        AlgHom.commutes]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.CoordTW

namespace GlobalTheory


open GlobalTheory.CoordTW in
theorem exists_coord_acris_bcris : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l]), (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ (ΦA : TW (OCr l O) T →+ Per.Acris l) (ΦB : TW (OB l O) T →+ Per.Bcris l), (∀ (a : Per.Acris l) (w : TW (OCr l O) T), ΦA (((1 : O) ⊗ₜ[ℤ_[l]] a : OCr l O) • w) = a * ΦA w) ∧ (∀ (y : Per.Bcris l) (w : TW (OB l O) T), ΦB (((1 : O) ⊗ₜ[ℤ_[l]] y : OB l O) • w) = y * ΦB w) ∧ (∀ x : ↥T.L.T, ΦB ((1 : OB l O) ⊗ₜ[O] x) = algebraMap ℤ_[l] (Per.Bcris l) (φ x)) ∧ (∀ (N : ℕ) (w : TW (OCr l O) T), ΦA (((l : O) ^ N) • w) = (l : Per.Acris l) ^ N * ΦA w) ∧ (∀ w : TW (OCr l O) T, ΦB (TWincl (toOB l O) T w) = acrisToBcris l (ΦA w)) := by
  intro l _ O K _ _ _ _ _ _ G _ _ T φ hφ
  refine ⟨coord T φ hφ (Per.Acris l), coord T φ hφ (Per.Bcris l), coord_mul T φ hφ _,
    coord_mul T φ hφ _, coord_one_tmul T φ hφ _, fun N w => ?_, coord_toOB T φ hφ⟩
  have h : ((l : O) ^ N) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ N) := by simp
  rw [h, coord_algebraMap_smul]
  simp

end GlobalTheory
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

def galFq (g : GQ l) : Fq l a →+* Fq l a :=
  ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)

theorem val_galFq (g : GQ l) (x : Fq l a) : Fq.val l a (galFq l a g x) = Per.σF g (Fq.val l a x) := rfl

theorem exists_pow_eq (φ : Fq l a →+* Fq l a) : ∃ m : ℕ, ∀ x, φ x = x ^ l ^ m := by
  first
  | exact @_root_.GlobalTheory.FrobeniusPower.main
  | exact _root_.GlobalTheory.FrobeniusPower.main
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrobeniusPower.main ..)
  | (intro h; exact _root_.GlobalTheory.FrobeniusPower.main h _ (fun _ => Iff.rfl))
  | exact _root_.GlobalTheory.FrobeniusPower.main ‹_› _ (fun _ => Iff.rfl)
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | exact fun _ => Iff.rfl)

theorem gal_wA_pow (g : GQ l) :
    ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  obtain ⟨m, hm⟩ := exists_pow_eq l a (galFq l a g)
  refine ⟨(m : ZMod a), fun w => ?_⟩
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m (sigma_pow_eq_one l a)]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff]
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ m) w).coeff n)
  rw [coeff_sigma_pow, ← hm, val_galFq]

end GlobalTheory.BKReal
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KinfFin

theorem seq_add_pow {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) (m k : ℕ) :
    ϖ.seq (m + k) ^ l ^ k = ϖ.seq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, ϖ.seq_succ, ih]

theorem adjoin_mono {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) :
    Monotone fun n => IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine IntermediateField.adjoin_simple_le_iff.2 ?_
  have : ϖ.seq m ^ e = (ϖ.seq (m + k) ^ e) ^ l ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, seq_add_pow]
  rw [this]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _

theorem Kinf_eq_iSup {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) :
    ϖ.Kinf = ⨆ n, IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  rw [PiSys.Kinf, ← IntermediateField.biSup_adjoin_simple, iSup_range]

theorem exists_mem_of_mem_Kinf {l : ℕ} [Fact l.Prime] {e : ℕ} (ϖ : PiSys l e) {x : Om l}
    (hx : x ∈ ϖ.Kinf) : ∃ n, x ∈ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  rw [Kinf_eq_iSup, ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed (adjoin_mono ϖ).directed_le, Set.mem_iUnion] at hx
  exact hx

theorem main : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (ϖ : PiSys l e) (F : IntermediateField ℚ_[l] (Om l)),
    FiniteDimensional ℚ_[l] F → F ≤ ϖ.Kinf → ∃ n : ℕ, F ≤ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  intro l _ e ϖ F hF hle
  classical
  let b := Module.finBasis ℚ_[l] F
  choose N hN using fun i => exists_mem_of_mem_Kinf ϖ (hle (b i).2)
  refine ⟨Finset.univ.sup N, fun x hx => ?_⟩
  change ((⟨x, hx⟩ : F) : Om l) ∈ _
  rw [← b.sum_repr ⟨x, hx⟩, IntermediateField.coe_sum]
  refine sum_mem fun i _ => ?_
  rw [IntermediateField.coe_smul]
  refine IntermediateField.smul_mem _ ?_
  exact adjoin_mono ϖ (Finset.le_sup (f := N) (Finset.mem_univ i)) (hN i)

end GlobalTheory.KinfFin
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

theorem kummer_mem_Fq_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  intro l _ a e _ _ ϖ he k hk
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  have hr : ∀ n, ϖ.ratio k n ^ e = 1 := fun n => by
    have hmem : ϖ.seq n ^ e ∈ ϖ.Kinf := IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix _ hmem,
      div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
    rfl
  have hK : ϖ.kummer k ^ e = 1 := Perfection.ext fun n => by
    erw [map_pow, map_one]
    change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
    rw [← map_pow, hr, map_one]
  have hmem : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← he, pow_succ, hK, one_mul]
  obtain ⟨z, hz⟩ : ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k := ⟨(⟨ϖ.kummer k, hmem⟩ : ↥(resSub l a)), rfl⟩
  refine ⟨z, Fq.val_injective l a ?_, hz.symm⟩
  rw [map_pow, map_one, hz, hK]

end GlobalTheory.BKReal
end
end
