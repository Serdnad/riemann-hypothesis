module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle539
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_of_mem_ball_small {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A) {ρ : ℝ≥0} (h0 : 0 < ρ)
    (h1 : ρ < 1) (m n : ℕ) {y : PreDisc l u ρ} (hy : y ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n)) :
    ∃ (c : ℕ) (z₁ z₂ : A), algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * y =
      algebraMap A (PreDisc l u ρ) (u ^ m * z₁ + (l : A) ^ (c + n) * z₂) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have hρ0 : (0 : ℝ) < ρ := h0
  have hρ1 : (ρ : ℝ) ≤ 1 := h1.le
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, hw, rfl⟩ := hx
    have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * (algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) *
        IsLocalization.Away.invSelf (l : A) ^ c) = algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) := by
      rw [map_pow, mul_left_comm, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    rcases le_or_gt m b with hb | hb
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
      refine ⟨c, (l : A) ^ a * u ^ k, 0, ?_⟩
      rw [e]; congr 1; ring
    · have hp : (ρ : ℝ) ^ m ≤ (ρ : ℝ) ^ b := pow_le_pow_of_le_one hρ0.le hρ1 hb.le
      have h2 : (l : ℝ) ^ (c + n) ≤ (l : ℝ) ^ a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hw
        have h3 : (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b ≤ (l : ℝ) ^ a * (ρ : ℝ) ^ b :=
          calc (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b = (l : ℝ) ^ c * (ρ : ℝ) ^ b * (l : ℝ) ^ n := by ring
            _ ≤ _ := hw
            _ ≤ (ρ : ℝ) ^ b * (l : ℝ) ^ a := mul_le_mul_of_nonneg_right hp (by positivity)
            _ = _ := mul_comm _ _
        exact le_of_mul_le_mul_right h3 (by positivity)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ((pow_le_pow_iff_right₀ hl1).1 h2)
      refine ⟨c, 0, (l : A) ^ k * u ^ b, ?_⟩
      rw [e]; congr 1; ring
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    obtain ⟨c', z₁', z₂', h'⟩ := hy
    refine ⟨c + c', (l : A) ^ c' * z₁ + (l : A) ^ c * z₁', z₂ + z₂', ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, pow_add] at h h' ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) (l : A)) ^ c' * h +
      (algebraMap A (PreDisc l u ρ) (l : A)) ^ c * h'
  | smul a x _ hx =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    refine ⟨c, a * z₁, a * z₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, pow_add, Algebra.smul_def] at h ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) a) * h

theorem exists_of_norm_toDisc_lt {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A)
    (ht : ∀ x : A, (l : A) * x = 0 → x = 0) (m : ℕ) (hd : ∀ x y : A, (l : A) * x = u ^ m * y → u ^ m ∣ x)
    {ρ : ℝ≥0} (h0 : 0 < ρ) (h1 : ρ < 1) (n : ℕ) (x : A) (hx : ‖toDisc l u ρ x‖ < (ρ : ℝ) ^ m / (l : ℝ) ^ n) :
    ∃ z₁ z₂ : A, x = u ^ m * z₁ + (l : A) ^ n * z₂ := by
  have hb : algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n) :=
    mem_ball_of_gauge_lt l u ρ ((norm_ofPre l u ρ _).symm.trans_lt hx)
  obtain ⟨c, z₁, z₂, h⟩ := exists_of_mem_ball_small hl u h0 h1 m n hb
  have hn : (l : A) ∈ nonZeroDivisors A := mem_nonZeroDivisors_iff_left.2 ht
  have hi : Function.Injective (algebraMap A (PreDisc l u ρ)) :=
    IsLocalization.injective (M := Submonoid.powers (l : A)) _ (Submonoid.powers_le.2 hn)
  rw [← map_mul] at h
  have h2 := hi h
  have key : ∀ (c : ℕ) (w : A), u ^ m ∣ (l : A) ^ c * w → u ^ m ∣ w := fun c => by
    induction c with
    | zero => intro w hw; simpa using hw
    | succ c ih =>
      rintro w ⟨y, hy⟩
      exact ih w (hd _ y (by rw [← hy]; ring))
  obtain ⟨z, hz⟩ := key c (x - (l : A) ^ n * z₂) ⟨z₁, by rw [pow_add] at h2; linear_combination h2⟩
  exact ⟨z, z₂, by linear_combination hz⟩

theorem BK.X_pow_natDegree_mem_J {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum

  simp only [map_add (f := _), map_pow, map_sum, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
  Polynomial.coe_C] at h
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [eq_sub_iff_add_eq]; exact h.symm
  rw [e]
  refine sub_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left (sum_mem fun i hi => ?_))
  obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hw, map_mul, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem mem_J_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  intro l hl K bk A _ s ht hd ρ h0 h1 n
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hρ0 : (0 : ℝ) < ρ := h0
  have hr : 0 < (ρ : ℝ) ^ (bk.Ep.natDegree * n) / (l : ℝ) ^ n := by positivity
  refine ⟨_, half_pos hr, fun x hx => ?_⟩
  obtain ⟨z₁, z₂, rfl⟩ := exists_of_norm_toDisc_lt hl.out.one_lt (s X) ht _ (hd _) h0 h1 n x
    (hx.trans_lt (half_lt_self hr))
  refine add_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · rw [← map_pow, pow_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow bk.X_pow_natDegree_mem_J n)
  · rw [← map_natCast s, ← map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscCoeff

theorem isLocalization_int (l : ℕ) {B : Type} [CommRing B] (u : B) (ρ : ℝ≥0) :
    IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers (l : ℤ))) (PreDisc l u ρ) := by
  have h : Algebra.algebraMapSubmonoid B (Submonoid.powers (l : ℤ)) = Submonoid.powers (l : B) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  rw [h]; infer_instance

instance (l : ℕ) {B : Type} [CommRing B] (u : B) (ρ : ℝ≥0) :
    IsLocalizedModule (Submonoid.powers (l : ℤ)) (IsScalarTower.toAlgHom ℤ B (PreDisc l u ρ)).toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr (isLocalization_int l u ρ)

variable {l : ℕ}

theorem exists_eq {B : Type} [CommRing B] {u : B} {ρ : ℝ≥0} (y : PreDisc l u ρ) :
    ∃ (a : B) (n : ℕ), y = algebraMap B (PreDisc l u ρ) a * IsLocalization.Away.invSelf (l : B) ^ n := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (l : B) y
  refine ⟨a, n, ?_⟩
  rw [← h, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem natCast_mul_invSelf {B : Type} [CommRing B] {u : B} {ρ : ℝ≥0} :
    (l : PreDisc l u ρ) * IsLocalization.Away.invSelf (l : B) = 1 := by
  rw [← map_natCast (algebraMap B (PreDisc l u ρ)), IsLocalization.Away.mul_invSelf]

theorem pow_mul_mono {B : Type} [CommRing B] {u : B} {ρ : ℝ≥0} (a : B) (n : ℕ) :
    (l : PreDisc l u ρ) ^ n * (algebraMap B (PreDisc l u ρ) a * IsLocalization.Away.invSelf (l : B) ^ n) =
      algebraMap B (PreDisc l u ρ) a := by
  rw [mul_left_comm, ← mul_pow, natCast_mul_invSelf, one_pow, mul_one]

variable (l) {A S : Type} [CommRing A] [CommRing S] (s : S →+* A) (u : S) (ρ : ℝ≥0) (c : A →+ S)

def preCoeff : PreDisc l (s u) ρ →ₗ[ℤ] PreDisc l u ρ :=
  IsLocalizedModule.lift (Submonoid.powers (l : ℤ)) (IsScalarTower.toAlgHom ℤ A (PreDisc l (s u) ρ)).toLinearMap
    ((IsScalarTower.toAlgHom ℤ S (PreDisc l u ρ)).toLinearMap.comp c.toIntLinearMap)
    (IsLocalizedModule.map_units (IsScalarTower.toAlgHom ℤ S (PreDisc l u ρ)).toLinearMap)

variable {l s u ρ c}

theorem preCoeff_alg (a : A) :
    preCoeff l s u ρ c (algebraMap A _ a) = algebraMap S (PreDisc l u ρ) (c a) :=
  IsLocalizedModule.lift_apply _ _ _ _ a

theorem preCoeff_mono (a : A) (n : ℕ) :
    preCoeff l s u ρ c (algebraMap A _ a * IsLocalization.Away.invSelf (l : A) ^ n) =
      algebraMap S (PreDisc l u ρ) (c a) * IsLocalization.Away.invSelf (l : S) ^ n := by
  have hl : IsUnit (l : PreDisc l u ρ) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := PreDisc l u ρ) (l : S)
    rwa [map_natCast] at this
  refine (hl.pow n).mul_left_cancel ?_
  rw [pow_mul_mono]
  have e : ((l : ℤ) ^ n) • (algebraMap A (PreDisc l (s u) ρ) a * IsLocalization.Away.invSelf (l : A) ^ n) =
      algebraMap A _ a := by
    rw [zsmul_eq_mul]; push_cast; exact pow_mul_mono a n
  have e2 := congrArg (preCoeff l s u ρ c) e
  rw [LinearMap.map_smul, zsmul_eq_mul, preCoeff_alg] at e2
  push_cast at e2
  exact e2

variable (hc : ∀ a x, c (s a * x) = a * c x)
include hc

theorem norm_preCoeff_le (y : PreDisc l (s u) ρ) : ‖preCoeff l s u ρ c y‖ ≤ ‖y‖ := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hr0 : 0 < r := (norm_nonneg y).trans_lt hr
  have hy := mem_ball_of_gauge_lt l (s u) ρ hr
  suffices h : ∀ x ∈ ball l (s u) ρ r, ∀ a : A, preCoeff l s u ρ c (a • x) ∈ ball l u ρ r by
    have h1 := h y hy 1
    rw [one_smul] at h1
    exact gauge_le l u ρ hr0 h1
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, k, h1, rfl⟩ := hx
    intro a'
    have e : a' • (algebraMap A (PreDisc l (s u) ρ) ((l : A) ^ a * s u ^ b) * IsLocalization.Away.invSelf (l : A) ^ k) =
        algebraMap A _ (s ((l : S) ^ a * u ^ b) * a') * IsLocalization.Away.invSelf (l : A) ^ k := by
      simp only [Algebra.smul_def, map_mul, map_pow, map_natCast]; ring
    have e2 : algebraMap S (PreDisc l u ρ) (c (s ((l : S) ^ a * u ^ b) * a')) * IsLocalization.Away.invSelf (l : S) ^ k =
        c a' • (algebraMap S (PreDisc l u ρ) ((l : S) ^ a * u ^ b) * IsLocalization.Away.invSelf (l : S) ^ k) := by
      rw [hc, Algebra.smul_def, map_mul]; ring
    rw [e, preCoeff_mono, e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, b, k, h1, rfl⟩)
  | zero => intro a'; rw [smul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro a'; rw [smul_add, map_add (f := _)]; exact add_mem (hx a') (hy a')
  | smul a x _ hx => intro a'; rw [smul_smul]; exact hx _

theorem continuous_preCoeff : Continuous (preCoeff l s u ρ c).toAddMonoidHom :=
  AddMonoidHomClass.continuous_of_bound (preCoeff l s u ρ c).toAddMonoidHom 1
    fun y => (norm_preCoeff_le hc y).trans (one_mul _).ge

theorem preCoeff_mul (p : PreDisc l u ρ) (q : PreDisc l (s u) ρ) :
    preCoeff l s u ρ c (preMap l u ρ (s u) ρ s p * q) = p * preCoeff l s u ρ c q := by
  obtain ⟨w, m, rfl⟩ := exists_eq p
  obtain ⟨a, n, rfl⟩ := exists_eq q
  have e : preMap l u ρ (s u) ρ s (algebraMap S _ w * IsLocalization.Away.invSelf (l : S) ^ m) *
      (algebraMap A _ a * IsLocalization.Away.invSelf (l : A) ^ n) =
      algebraMap A (PreDisc l (s u) ρ) (s w * a) * IsLocalization.Away.invSelf (l : A) ^ (m + n) := by
    rw [map_mul, map_pow, preMap_alg, preMap_inv, map_mul]; ring
  rw [e, preCoeff_mono, preCoeff_mono, hc, map_mul]; ring

variable (l s u ρ c)

def discCoeff : Disc l (s u) ρ →+ Disc l u ρ :=
  (preCoeff l s u ρ c).toAddMonoidHom.completion (continuous_preCoeff hc)

variable {l s u ρ c}

theorem discCoeff_ofPre (y : PreDisc l (s u) ρ) :
    discCoeff l s u ρ c hc (ofPre l (s u) ρ y) = ofPre l u ρ (preCoeff l s u ρ c y) :=
  AddMonoidHom.completion_coe _ _ y

theorem continuous_discCoeff : Continuous (discCoeff l s u ρ c hc) :=
  AddMonoidHom.continuous_completion _ _

theorem discCoeff_toDisc (a : A) :
    discCoeff l s u ρ c hc (toDisc l (s u) ρ a) = toDisc l u ρ (c a) :=
  (discCoeff_ofPre hc _).trans (congrArg (ofPre l u ρ) (preCoeff_alg a))

theorem norm_discCoeff_le (y : Disc l (s u) ρ) : ‖discCoeff l s u ρ c hc y‖ ≤ ‖y‖ := by
  refine (denseRange_ofPre l (s u) ρ).induction_on y
    (isClosed_le (continuous_norm.comp (continuous_discCoeff hc)) continuous_norm) fun q => ?_
  rw [discCoeff_ofPre, norm_ofPre, norm_ofPre]
  exact norm_preCoeff_le hc q

theorem discCoeff_mul {j : Disc l u ρ →+* Disc l (s u) ρ} (hj : IsDiscMap (l := _) (u := _) (ρ := _) s j) (x : Disc l u ρ)
    (y : Disc l (s u) ρ) : discCoeff l s u ρ c hc (j x * y) = x * discCoeff l s u ρ c hc y := by
  have hjc : Continuous j :=
    AddMonoidHomClass.continuous_of_bound j 1 fun x => (hj.norm_le x).trans (one_mul _).ge
  have hdc : Continuous (discCoeff l s u ρ c hc) := continuous_discCoeff hc
  have e : j.comp (ofPre l u ρ) = (ofPre l (s u) ρ).comp (preMap l u ρ (s u) ρ s) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : S)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply]
      rw [preMap_alg]
      exact hj.ext a)
  refine (denseRange_ofPre l u ρ).induction_on x
    (isClosed_eq (hdc.comp (hjc.mul continuous_const)) (continuous_id.mul continuous_const)) fun p => ?_
  refine (denseRange_ofPre l (s u) ρ).induction_on y
    (isClosed_eq (hdc.comp (continuous_const.mul continuous_id)) (continuous_const.mul hdc)) fun q => ?_
  rw [show j (ofPre l u ρ p) = ofPre l (s u) ρ (preMap l u ρ (s u) ρ s p) from RingHom.congr_fun e p,
    ← map_mul, discCoeff_ofPre, discCoeff_ofPre, ← map_mul, preCoeff_mul hc]

end GlobalTheory.BSP.DiscCoeff


open GlobalTheory.BSP.DiscCoeff in
theorem GlobalTheory.BSP.exists_discCoeff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) := by
  intro l _ K bk A _ s ι TB ρ _ _ j hj
  exact ⟨fun i => discCoeff l s X ρ (TB.c i) (TB.c_mul i), fun i a => discCoeff_toDisc (TB.c_mul i) a,
    fun i x y => discCoeff_mul (TB.c_mul i) hj x y, fun i y => norm_discCoeff_le (TB.c_mul i) y⟩
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EisImage

theorem isUnit_of_constantCoeff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : WittVector l O) (h : IsUnit (WittVector.constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have h1 : c * WittVector.teichmuller l ((u⁻¹ : Oˣ) : O) - 1 ∈ Ideal.span {(l : WittVector l O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have h2 := IsAdicComplete.le_jacobson_bot (Ideal.span {(l : WittVector l O)}) h1
  have h3 := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ h2
  exact isUnit_of_mul_isUnit_left h3

theorem exists_eq {R : Type} [CommRing R] (l : R) (P : Polynomial R) (hm : P.Monic) (hd : 0 < P.natDegree)
    (hc : ∀ i < P.natDegree, l ∣ P.coeff i) (w : R) (h0 : P.coeff 0 = l * w) :
    ∃ G : Polynomial R, P = Polynomial.X ^ P.natDegree +
      Polynomial.C l * (Polynomial.C w + Polynomial.X * G) := by
  have h1 : Polynomial.C l ∣ (P - Polynomial.X ^ P.natDegree).divX := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_divX, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy (i + 1) P.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact hc _ h
    · rw [if_pos h, h, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]
      exact dvd_zero _
  obtain ⟨G, hG⟩ := h1
  refine ⟨G, ?_⟩
  have h2 := Polynomial.X_mul_divX_add (P - Polynomial.X ^ P.natDegree)
  rw [hG, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hd.ne, sub_zero, h0, map_mul] at h2
  linear_combination -h2

theorem map_E_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsLocalRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ¬ IsUnit (ψ bk.flat) → ∃ w : WittVector l O, IsUnit w ∧ WittVector.map ψ (bk.ev bk.E) = WittVector.teichmuller l (ψ bk.flat) ^ bk.Ep.natDegree + ((l : ℕ) : WittVector l O) * w := by
  intro l _ K bk O _ _ _ _ ψ hψ
  obtain ⟨w₀, hw₀⟩ := bk.coeff_zero
  obtain ⟨G, hG⟩ := exists_eq (l : Wq l bk.a) bk.Ep bk.monic bk.deg_pos bk.dvd_coeff w₀ hw₀
  let f : Polynomial (Wq l bk.a) →+* WittVector l O :=
    (WittVector.map ψ).comp (bk.ev.comp (Polynomial.coeToPowerSeries.ringHom))
  have hX : f Polynomial.X = WittVector.teichmuller l (ψ bk.flat) := by
    change WittVector.map ψ (bk.ev ((Polynomial.X : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧)) = _
    rw [Polynomial.coe_X, bk.ev_X, WittVector.map_teichmuller]
  refine ⟨f (Polynomial.C (w₀ : Wq l bk.a) + Polynomial.X * G), ?_, ?_⟩
  · apply isUnit_of_constantCoeff
    have hu : IsUnit (WittVector.constantCoeff (f (Polynomial.C (w₀ : Wq l bk.a)))) :=
      ((w₀.isUnit.map Polynomial.C).map f).map _
    rw [map_add (f := _), map_mul, hX, map_add (f := _), map_mul, WittVector.constantCoeff_apply (WittVector.teichmuller l _),
      WittVector.teichmuller_coeff_zero]
    by_contra hn
    have h1 : ψ bk.flat * WittVector.constantCoeff (f G) ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hψ
    have h2 := Ideal.sub_mem _ (show _ ∈ IsLocalRing.maximalIdeal O from hn) h1
    rw [add_sub_cancel_right] at h2
    exact h2 hu
  · have h1 := congrArg f hG
    rw [map_add (f := _), map_pow, hX, map_mul, map_natCast Polynomial.C, map_natCast f] at h1
    exact h1

end GlobalTheory.BSP.EisImage
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem TopBasis.exists_sum_of_null {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (σ : ι → S) (hσ : ∀ n : ℕ, {i | σ i ∉ I ^ n}.Finite) :
    ∃ L : A, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, s (σ i) * TB.b i ∈ (I ^ n).map s := by
  classical
  let F : ℕ → Finset ι := fun n => (hσ n).toFinset
  have memF : ∀ n i, i ∈ F n ↔ σ i ∉ I ^ n := fun n i => by simp [F]
  have tail : ∀ m (G : Finset ι), F m ⊆ G →
      ∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F m, s (σ i) * TB.b i ∈ (I ^ m).map s := by
    intro m G hG
    rw [← Finset.sum_sdiff_eq_sub hG]
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h : i ∉ F m := (Finset.mem_sdiff.1 hi).2
    rw [memF] at h
    exact not_not.1 h
  have mono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} h i hi => by
    rw [memF] at hi ⊢
    exact fun h' => hi (Ideal.pow_le_pow_right h h')
  have key : ∀ (n : ℕ) (x : A), x ∈ ((I.map s) ^ n • ⊤ : Submodule A A) ↔ x ∈ (I ^ n).map s := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.map_pow]
  obtain ⟨L, hL⟩ := TB.complete.toIsPrecomplete.prec (f := fun n => ∑ i ∈ F n, s (σ i) * TB.b i)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, key, ← neg_sub]
      exact neg_mem (tail m (F n) (mono hmn)))
  refine ⟨L, fun n => ⟨F n, fun G hG => ?_⟩⟩
  have h1 := hL n
  rw [SModEq.sub_mem, key] at h1
  have h2 := tail n G hG
  have e : L - ∑ i ∈ G, s (σ i) * TB.b i =
      -((∑ i ∈ F n, s (σ i) * TB.b i - L) + (∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F n, s (σ i) * TB.b i)) := by
    ring
  rw [e]
  exact neg_mem (add_mem h1 h2)

theorem exists_sum_null_ev : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (σ : ι → bk.S), (∀ n : ℕ, {i | σ i ∉ bk.J ^ n}.Finite) →
    ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
  fun _ _ _ _ _ TB σ hσ => TB.exists_sum_of_null σ hσ

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem strat_homGal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY g
  let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
  have hG : ∀ z : ℤ_[l], G (algebraMap ℤ_[l] (WCb l) z) = algebraMap ℤ_[l] (WCb l) z :=
    fun z => (galW l (g : GQ l)).commutes z
  have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M := by
    intro m n M; exact Matrix.ext fun i j => hG _
  have hYG : (Y.map bk.evW).map G = (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := by
    exact Matrix.ext fun i j => galW_inclW (g : GQ l) (bk.ev (Y i j))
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  have h1 := congrArg (fun M => M.map G) hY
  simp only [Matrix.map_mul, hzG, hYG] at h1

  have e1 : T' * ((S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) *
      (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) =
      T' * ((Y.map (BK.hf bk.ι)).map (inclW l) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) := by
    have a1 := hT'.gal g
    have a2 := hT.gal g
    have a3 : T'.map (galW l (g : GQ l)) = T'.map G := rfl
    have a4 : T.map (galW l (g : GQ l)) = T.map G := rfl
    have a5 : (Y.map (BK.hf bk.ι)).map (inclW l) = Y.map bk.evW := Matrix.map_map
    rw [a3] at a1
    rw [a4] at a2
    rw [a5]
    calc _ = (T' * (S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) *
          (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := (Matrix.mul_assoc _ _ _).symm
      _ = zW (ρ' g) * (T'.map G * (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) := by
          rw [← a1, Matrix.mul_assoc]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = (T' * Y.map bk.evW) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) := by
          rw [a2, hY, Matrix.mul_assoc]
      _ = _ := Matrix.mul_assoc _ _ _
  obtain ⟨u, hu⟩ := hT'.unit
  rw [← hu] at e1
  have e2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) e1
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at e2
  apply Matrix.map_injective (f := inclW l) inclW_injective
  exact (Matrix.map_mul (f := inclW l)).trans (e2.trans (Matrix.map_mul (f := inclW l)).symm)

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.adicTopologicalBasis_basis_mod_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (tb : TopBasis s I ι) (m : ℕ), letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra; ∃ b : Module.Basis ι (S ⧸ I ^ m) (A ⧸ (I ^ m).map s), ∀ i, b i = Ideal.Quotient.mk _ (tb.b i) := by
  first | exact @GlobalTheory.BSP.TopBasis.basis_mod_pow | exact GlobalTheory.BSP.TopBasis.basis_mod_pow | (intros; apply GlobalTheory.BSP.TopBasis.basis_mod_pow <;> assumption)
end
