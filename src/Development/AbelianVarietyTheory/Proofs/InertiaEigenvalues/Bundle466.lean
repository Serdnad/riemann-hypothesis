module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle454
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open TensorProduct Module
namespace GlobalTheory.WDDual
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem iso_sum_dual (a : WDRep h V) (b : WDRep h V') : (a.dual.sum b.dual).Iso (a.sum b).dual := by
  refine ⟨Module.dualProdDualEquivDual ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · ext v <;> simp
  · ext v <;> simp

theorem iso_tensor_dual (a : WDRep h V) (b : WDRep h V') :
    (a.dual.tensor b.dual).Iso (a.tensor b).dual := by
  refine ⟨TensorProduct.dualDistribEquiv ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
      ring
    | add x y hx hy => simp only [map_add (f := _), hx, hy]


omit [IsAlgClosure E Ω] in
theorem qPow_neg' (s : ℝ) : qPow w (-s) = (qPow w s)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← qPow_add, neg_add_cancel, qPow_zero])

theorem iso_tw_dual (a : WDRep h V) (s : ℝ) : (a.tw s).dual.Iso (a.dual.tw (-s)) := by
  refine ⟨LinearEquiv.refl ℂ _, fun σ f => ?_, fun f => rfl⟩
  ext v
  simp only [WDRep.tw, WDRep.dual_ρ, WDRep.twist_ρ, unrChar_apply, LinearEquiv.refl_apply,
    LinearMap.dualMap_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, qPow_neg', map_inv, _root_.inv_zpow']
  congr 2
  simp

theorem shiftEnd_single {n : ℕ} (j : Fin n) :
    shiftEnd n (Pi.single j 1) = if hj : (j : ℕ) + 1 < n then Pi.single ⟨j + 1, hj⟩ 1 else 0 := by
  ext k
  rw [shiftEnd_apply]
  split_ifs with h1 h2 h2 <;> simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk, Pi.zero_apply] <;>
    split_ifs <;> first | rfl | (exfalso; have := k.2; have := j.2; omega)

theorem spEig_rev {n : ℕ} (i : Fin n) : WDRep.spEig w n i.rev = (WDRep.spEig w n i)⁻¹ := by
  rw [WDRep.spEig, WDRep.spEig, ← qPow_neg']
  congr 1
  rw [Fin.val_rev]
  have : (i : ℕ) + 1 ≤ n := i.2
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem diagEnd_single {n : ℕ} (c : Fin n → ℂ) (j : Fin n) :
    _root_.GlobalTheory.WeilDeligne.diagEnd c (Pi.single j 1) = c j • (Pi.single j (1 : ℂ) : Fin n → ℂ) := by
  ext k; by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

def spDualMap (n : ℕ) : Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun f i := (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1)
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by ext i; simp; ring

theorem spDualMap_apply {n : ℕ} (f : Dual ℂ (Fin n → ℂ)) (i : Fin n) :
    spDualMap n f i = (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1) := rfl

theorem spDualMap_injective (n : ℕ) : Function.Injective (spDualMap n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro f hf
  refine LinearMap.pi_ext fun j x => ?_
  have := congrFun hf j.rev
  rw [spDualMap_apply, Fin.rev_rev, Pi.zero_apply, mul_eq_zero] at this
  have h1 : f (Pi.single j 1) = 0 := this.resolve_left (pow_ne_zero _ (by norm_num))
  have h2 : (Pi.single j x : Fin n → ℂ) = x • Pi.single j (1 : ℂ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [h2, map_smul, h1, smul_zero]; simp

theorem iso_sp_dual (n : ℕ) : (WDRep.sp h n).dual.Iso (WDRep.sp h n) := by
  refine ⟨LinearMap.linearEquivOfInjective (spDualMap n) (spDualMap_injective n)
    (by simp [Subspace.dual_finrank_eq]), fun σ f => ?_, fun f => ?_⟩
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_ρ, WDRep.sp_ρ,
      LinearMap.dualMap_apply, diagEnd_single, map_smul, smul_eq_mul, _root_.GlobalTheory.WeilDeligne.diagEnd_apply, spEig_rev]
    simp
    ring
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_N, WDRep.sp_N,
      LinearMap.neg_apply, LinearMap.dualMap_apply, shiftEnd_single, shiftEnd_apply]
    by_cases hi : 1 ≤ (i : ℕ)
    · have hr : (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dite_eq_left hr, if_pos hi]
      have he : (⟨(i.rev : ℕ) + 1, hr⟩ : Fin n) = (⟨(i : ℕ) - 1, by omega⟩ : Fin n).rev := by
        ext; simp only [Fin.val_rev]; omega
      rw [he]
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      simp only [hk, Nat.add_sub_cancel, pow_succ]
      ring
    · have hr : ¬ (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dite_eq_right hr, if_neg hi]
      simp

namespace WDClass

theorem lpDual_lpZero : (WD.lpZero (h := h)).lpDual = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpDual_mk]
  exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp [Subspace.dual_finrank_eq]),
    fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpDual_lpSum (x y : WD h) : (x.lpSum y).lpDual = x.lpDual.lpSum y.lpDual := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpSum_mk]
      exact WD.sound (iso_sum_dual a b).symm

theorem lpDual_sumList (l : List (WD h)) : (sumList l).lpDual = sumList (l.map WD.lpDual) := by
  induction l with
  | nil => exact lpDual_lpZero
  | cons x l ih =>
    show (x.lpSum (sumList l)).lpDual = x.lpDual.lpSum (sumList (l.map WD.lpDual))
    rw [lpDual_lpSum, ih]

theorem lpDual_lpTw (y : WD h) (s : ℝ) : (y.lpTw s).lpDual = y.lpDual.lpTw (-s) := by
  induction y using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpTw_mk]
    exact WD.sound (iso_tw_dual a s)

theorem lpDual_lpChar_lpSp (y : WD h) (n : ℕ) :
    (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
  induction y using WD.ind with
  | hP m a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
    exact WD.sound ((iso_tensor_dual a (WDRep.sp h n)).symm.trans
      ((WDRep.Iso.refl a.dual).tensor (iso_sp_dual n)))

end WDClass

theorem lpDual_sum_tw_sp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w),
    (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧
    (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧
    ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) :=
  fun _ _ _ _ _ _ _ _ _ _ =>
    ⟨WDClass.lpDual_sumList, WDClass.lpDual_lpTw, WDClass.lpDual_lpChar_lpSp⟩

end GlobalTheory.WDDual
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.CuspExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (GlobalTheory.LocLanglands.sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [GlobalTheory.LocLanglands.sumList, charPol_lpZero]
  | cons b l ih =>
    have : GlobalTheory.LocLanglands.sumList (b :: l) =
        WD.lpSum b (GlobalTheory.LocLanglands.sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r : IrrGL (k := w.adicCompletion E) → WD h}

end GlobalTheory.LocLanglands.CuspExt

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDListLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpZero (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (WD.lpZero (h := h)).lpTwist ξ hξ = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpTwist_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem lpTwist_lpSum (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpSum_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpSum_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  rfl

theorem lpTwist_lpChar (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpChar_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpChar_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp only [WDRep.tensor_ρ, WDRep.twist_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left,
    LinearMap.smul_apply]

theorem lpChar_lpZero (x : WD h) : x.lpChar (WD.lpZero (h := h)) = WD.lpZero (h := h) := by
  induction x using WD.ind with
  | hP n a =>
  rw [WD.lpZero, WD.lpChar_mk]
  exact WD.sound ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpChar_lpSum (x a b : WD h) : x.lpChar (a.lpSum b) = (x.lpChar a).lpSum (x.lpChar b) := by
  induction x using WD.ind with
  | hP n c =>
  induction a using WD.ind with
  | hP m a =>
  induction b using WD.ind with
  | hP k b =>
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  refine WD.sound ⟨TensorProduct.prodRight ℂ ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
  · induction v using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ)
    ((WD.charPol_natDegree _ σ).trans (WD.lpDim_zero h))

end GlobalTheory.WDListLaws


open GlobalTheory.WDListLaws in
open GlobalTheory.LocLanglands (sumList) in
theorem GlobalTheory.sumList_laws : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  intro E Ω _ _ _ _ _ A w h
  refine ⟨fun l l' hp => ?_, fun l ξ hξ => ?_, fun x y ξ hξ => ⟨lpTwist_lpSum x y ξ hξ, lpTwist_lpChar x y ξ hξ⟩,
    fun x l => ?_, fun l => ⟨?_, fun σ => ?_⟩⟩
  · induction hp with
    | nil => rfl
    | cons x _ ih =>
      show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
      rw [ih]
    | swap x y l =>
      show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
      rw [← WD.lpSum_assoc, WD.lpSum_comm y x, WD.lpSum_assoc]
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · induction l with
    | nil => exact lpTwist_lpZero ξ hξ
    | cons x l ih =>
      show (WD.lpSum x (sumList l)).lpTwist ξ hξ = WD.lpSum _ (sumList _)
      rw [lpTwist_lpSum, ih]
  · induction l with
    | nil => exact lpChar_lpZero x
    | cons y l ih =>
      show x.lpChar (WD.lpSum y (sumList l)) = WD.lpSum _ (sumList _)
      rw [lpChar_lpSum, ih]
  · induction l with
    | nil => exact WD.lpDim_zero h
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).lpDim = _
      rw [WD.lpDim_sum, ih, List.map_cons, List.sum_cons]
  · induction l with
    | nil => exact charPol_lpZero σ
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).charPol σ = _
      rw [WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.globalArtin_localIdele_injective : ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ w : HeightOneSpectrum (𝓞 E), Function.Injective fun x : (w.adicCompletion E)ˣ => art (Neutral.B1.localIdele E w x) := by
  first | exact @GlobalTheory.ArtinLocalInj.artin_localIdele_injective | exact GlobalTheory.ArtinLocalInj.artin_localIdele_injective | (intros; apply GlobalTheory.ArtinLocalInj.artin_localIdele_injective <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segment_nu_nu (Δ : Segment k) (a b : ℂ) : (Δ.nu a).nu b = Δ.nu (a + b) :=
  Segment.ext_first (show (Δ.first.nu a).nu b = Δ.first.nu (a + b) from IrrGL.nu_nu _ _ _) rfl

theorem isLSeg_nu {Δ : Segment k} {x : IrrGL (k := k)} (h : IsLSeg Δ x.rep) (s : ℂ) : IsLSeg (Δ.nu s) (x.nu s).rep :=
  (h.tw _ _).of_equiv (x.twEquiv _ _)

theorem univ_map_speh_segments (d m : ℕ) (Δ : Fin m → Segment k) (s : Fin m → ℝ) :
    Finset.univ.val.map (fun p : Fin (d * m) => ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)) = ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) := by
  rw [Fin.univ_val_map]
  congr 1
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  rw [Function.comp_apply, List.map_ofFn]
  refine List.ofFn_inj.2 (funext fun j => ?_)
  have : ∀ h, finProdFinEquiv.symm (⟨i * m + j, h⟩ : Fin (d * m)) = (i, j) := fun h => by
    rw [Equiv.symm_apply_eq]; ext; simp [finProdFinEquiv_apply_val]; ring
  simp only [Function.comp, this]

end SlopeTestRemainingChoices

theorem speh_quotient_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  intro k _ _ _ _ _ hLM hprec hstage a V _ _ σ m δ Δ s hΔ hδu hs hd hσ d n hdn W _ _ σ' hirr hf
  obtain ⟨φ⟩ := hσ
  obtain ⟨f, hfs⟩ := hf
  let y : Fin d → Fin m → IrrGL (k := k) := fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = a := fun _ => hd
  let Y : Fin (d * m) → IrrGL (k := k) := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = n := by
    rw [← hdn, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (prodIrr (y i) (hN i)) :=
    fun i => (twistEquiv φ _).trans (prodIrrTwistEquiv _ hd _ (isSmoothChar_absPow _))
  obtain ⟨e2⟩ := hstage d m y (fun _ => a) n hN hdn hM'
  let E := (multiProdEquiv _ e1).trans e2
  let Γs : Fin (d * m) → Segment k := fun p =>
    ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact isLSeg_nu (isLSeg_nu (hΔ _) _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply, segment_nu_nu] at hP
    have key := hprec (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j') (hδu j')
      (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ))) (by push_cast at hP ⊢; exact hP)
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    have := abs_lt.1 (hs j)
    have := abs_lt.1 (hs j')
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨univ_map_speh_segments d m Δ s, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hLM k _ (d * m) n Y hM' hLF
  obtain ⟨ψ⟩ := hπ.equiv_of_surjective hirr (f.comp E.symm.toIntertwiningMap)
    (hfs.comp E.symm.toLinearEquiv.surjective)
  exact ⟨d * m, Y, hM', hLF, hπ.of_equiv ψ.symm (.refl _)⟩

end GlobalTheory
end
end
