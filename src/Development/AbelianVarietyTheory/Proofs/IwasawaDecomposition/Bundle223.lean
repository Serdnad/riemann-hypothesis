module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isAvg_sigma {g : Mx n} (hg : g ∈ UJset ε) : IsAvg ε σ (σ g) :=
  ⟨{g}, 1, isCompact_singleton, Set.singleton_subset_iff.2 hg, zero_le_one, fun ι _ x w M _ h => by
    rw [one_mul]; exact h g rfl⟩

theorem IsAvg.add {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') : IsAvg ε σ (fun w => T w + T' w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨Z ∪ Z', C + C', h1.union k1, Set.union_subset h2 k2, add_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_add_right, Finset.sum_add_distrib, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h4 ι x w M hM fun y hy => hb y (Or.inl hy))
    (k4 ι x w M hM fun y hy => hb y (Or.inr hy)))

theorem IsAvg.comp (hσ : IsURepOn (UJset ε) σ) {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') :
    IsAvg ε σ (fun w => T (T' w)) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨(fun p : Mx n × Mx n => p.1 * p.2) '' (Z ×ˢ Z'), C * C',
    (h1.prod k1).image (continuous_fst.matrix_mul continuous_snd), ?_, mul_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact mul_mem_UJ (h2 hp.1) (k2 hp.2)
  rw [mul_assoc]
  refine h4 ι x (fun j => T' (w j)) (C' * M) (mul_nonneg k3 hM) fun y hy => ?_
  simp only [inner_sigma hσ (h2 hy)]
  refine k4 ι (fun j => σ y⁻¹ (x j)) w M hM fun y' hy' => ?_
  have := hb (y * y') ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
  simpa only [sigma_mul hσ (h2 hy) (k2 hy'), inner_sigma hσ (h2 hy)] using this

theorem IsAvg.smul (c : ℂ) {T : H → H} (h : IsAvg ε σ T) : IsAvg ε σ (fun w => c • T w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  refine ⟨Z, ‖c‖ * C, h1, h2, mul_nonneg (norm_nonneg _) h3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h4 ι x w M hM hb) (norm_nonneg _)

theorem isAvg_zero : IsAvg ε σ (fun _ => 0) :=
  ⟨∅, 0, isCompact_empty, Set.empty_subset _, le_rfl, fun ι _ x w M _ _ => by simp⟩

theorem isAvg_kAvg [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    IsAvg ε σ (kAvg ε σ e) := by
  refine ⟨Kset ε, ∫ k, ‖e k‖ ∂(muK ε), (maximal_compact_facts n ε).2.1, fun k hk => K_le_UJ hk,
    integral_nonneg fun _ => norm_nonneg _, fun ι _ x w M hM hb => ?_⟩
  have hi : ∀ v : H, Integrable (fun k : KG ε => e k • σ (toMK k) v) (muK ε) := fun v =>
    (he.smul ((hσ.2.2 v).comp_continuous (continuous_toMK ε)
      fun k => K_le_UJ (toMK_mem_K k))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [kAvg]
  simp only [fun j => (integral_inner (𝕜 := ℂ) (hi (w j)) (x j)).symm]
  rw [← integral_finsetSum _ fun j _ => (hi (w j)).const_inner (x j), ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((he.norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).mul_const M) (Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ (toMK_mem_K k)) (norm_nonneg _)

theorem isAvg_closure : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ g ∈ UJset ε, IsAvg ε σ (σ g)) ∧ (∀ T T' : H → H, IsAvg ε σ T → IsAvg ε σ T' → IsAvg ε σ (fun w => T w + T' w) ∧ IsAvg ε σ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : H → H), IsAvg ε σ T → IsAvg ε σ (fun w => c • T w)) ∧ (∀ e : KG ε → ℂ, Continuous e → IsAvg ε σ (kAvg ε σ e)) ∧ IsAvg ε σ (fun _ => 0) :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hg => isAvg_sigma hg, fun _ _ h h' => ⟨h.add h', h.comp hσ h'⟩,
    fun c _ h => h.smul c, fun _ he => isAvg_kAvg hσ he, isAvg_zero⟩

end GlobalTheory.TypeSum
end

section

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.ExpansionAverage

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem integrable_K {E : Type} [NormedAddCommGroup E] {F : KG ε → E} (hF : Continuous F) : Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem toMK_mem (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integrable_Dw (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Integrable (fun k : KG ε => e k • Dw σ l (σ (toMK k) w)) (muK ε) :=
  integrable_K (he.smul ((h.continuousOn_Dw hl hw).comp_continuous (continuous_toMK ε) toMK_mem))

theorem Dw_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    Dw σ l (kAvg ε σ e w) = ∫ k, e k • Dw σ l (σ (toMK k) w) ∂(muK ε) := by
  refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
  have h0 : Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) := integrable_Dw h he (l := []) (by simp) hw
  rw [inner_Dw h.1 hl hy hw', kAvg, ← integral_inner h0, ← integral_inner (integrable_Dw h he hl hw),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_Dw h.1 hl hy (hw.translate h.1 (toMK_mem k))]
  ring

theorem form_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ)
    {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    ℓ (kAvg ε σ e w) = ∫ k, e k * ℓ (σ (toMK k) w) ∂(muK ε) := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  have hΛ' : ∀ w, Sm ε σ w → ℓ w = ∑ i, Λ i (Dw σ (S i) w) := hΛ
  rw [hΛ' _ hw']
  simp only [fun i => Dw_kAvg h he (hS i) hw hw',
    fun i => ((Λ i).integral_comp_comm (integrable_Dw h he (hS i) hw)).symm]
  rw [← integral_finsetSum _ fun i _ => (Λ i).integrable_comp (integrable_Dw h he (hS i) hw)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [hΛ' _ (hw.translate h.1 (toMK_mem k)), Finset.mul_sum, map_smul, smul_eq_mul]

theorem continuousOn_and_hasSum_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (S : List (List (Mx n))) (v : ℕ → H) (ℓ : ℕ → (H →ₗ[ℂ] ℂ)) (C : ℕ → ℝ) (f : Mx n → ℂ),
      Words (lieSet ε) S → Ctrl (lieSet ε) (UJset ε) σ S → IsExpn (lieSet ε) (UJset ε) σ S v ℓ C f →
      ContinuousOn f (UJset ε) ∧ ∀ e : KG ε → ℂ, Continuous e → (∀ w, Sm ε σ (kAvg ε σ e w)) → ∀ g ∈ UJset ε,
        HasSum (fun i => ℓ i (σ g (kAvg ε σ e (v i)))) (∫ k, e k * f (g * toMK k) ∂(muK ε)) := by
  intro n ε H _ _ _ σ h S v ℓ C f hS ⟨B, hB, hBd⟩ hE
  have hsc := hE.sobCont hS
  obtain ⟨hv, hC, hb, hsum, hf⟩ := hE
  have hc : ∀ i, ContinuousOn (fun g => ℓ i (σ g (v i))) (UJset ε) := fun i => h.continuousOn_coef (hsc i) (hv i)
  have hbd : ∀ (M : ℝ) i, ∀ g ∈ UJset ε, B g ≤ M → ‖ℓ i (σ g (v i))‖ ≤ M * (C i * sobNorm σ S (v i)) := by
    intro M i g hg hM
    calc ‖ℓ i (σ g (v i))‖ ≤ C i * sobNorm σ S (σ g (v i)) := hb i _ (Sm.translate h.1 (hv i) hg)
      _ ≤ C i * (M * sobNorm σ S (v i)) := mul_le_mul_of_nonneg_left
          ((hBd g hg _ (hv i)).trans (mul_le_mul_of_nonneg_right hM (sobNorm_nonneg _ _ _))) (hC i)
      _ = _ := by ring
  refine ⟨fun g₀ hg₀ => ?_, fun e he hs g hg => ?_⟩
  · have ho : {g | B g < B g₀ + 1} ∈ 𝓝 g₀ := (isOpen_lt hB continuous_const).mem_nhds (lt_add_one (B g₀))
    have h1 : ContinuousOn (fun g => ∑' i, ℓ i (σ g (v i))) (UJset ε ∩ {g | B g < B g₀ + 1}) :=
      continuousOn_tsum (fun i => (hc i).mono Set.inter_subset_left) (hsum.mul_left (B g₀ + 1))
        fun i g hg => hbd _ i g hg.1 (le_of_lt hg.2)
    have h2 : ContinuousOn f (UJset ε ∩ {g | B g < B g₀ + 1}) := h1.congr fun g hg => (hf g hg.1).tsum_eq.symm
    exact (continuousWithinAt_inter ho).1 (h2 g₀ ⟨hg₀, lt_add_one (B g₀)⟩)
  · have hm : ∀ k : KG ε, g * toMK k ∈ UJset ε := fun k => mul_mem_UJ hg (toMK_mem k)
    have hcm : Continuous fun k : KG ε => g * toMK k := continuous_const.mul (continuous_toMK ε)
    obtain ⟨M, hM⟩ := (isCompact_range (hB.comp hcm)).bddAbove
    have hM' : ∀ k : KG ε, B (g * toMK k) ≤ M := fun k => hM ⟨k, rfl⟩
    have hF : ∀ i, Integrable (fun k : KG ε => e k * ℓ i (σ (g * toMK k) (v i))) (muK ε) := fun i =>
      integrable_K (he.mul ((hc i).comp_continuous hcm hm))
    have hS' : Summable fun i => ∫ k, ‖e k * ℓ i (σ (g * toMK k) (v i))‖ ∂(muK ε) := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) (fun i => ?_)
        ((hsum.mul_left M).mul_left (∫ k, ‖e k‖ ∂(muK ε)))
      rw [← integral_mul_const]
      refine integral_mono (hF i).norm ((integrable_K he.norm).mul_const _) fun k => ?_
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd M i _ (hm k) (hM' k)) (norm_nonneg _)
    have key := hasSum_integral_of_summable_integral_norm hF hS'
    simp only [fun k => ((hf _ (hm k)).mul_left (e k)).tsum_eq] at key
    refine Eq.mpr (congrArg (HasSum · _) (funext fun i => ?_)) key
    have := form_kAvg h he (sobCont_translate h.1 (hsc i) hg) (hv i) (hs (v i))
    simp only [fun k => sigma_mul h.1 hg (toMK_mem k)]
    exact this

end GlobalTheory.ExpansionAverage

end
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.FamClosed

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_flow {R : ℝ → (E →L[ℂ] E)} (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {a b : E}
    (h : HasDerivAt (fun t : ℝ => R t a) b 0) (s : ℝ) : HasDerivAt (fun t : ℝ => R t a) (R s b) s := by
  have h1 := ((R s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = R s (R (t - s) a)
  rw [← ContinuousLinearMap.comp_apply, ← hR, add_sub_cancel]

theorem norm_sub_le {f f' : ℝ → E} (hf : ∀ s, HasDerivAt f (f' s) s) {t C : ℝ}
    (hC : ∀ s, |s| ≤ |t| → ‖f' s‖ ≤ C) : ‖f t - f 0‖ ≤ C * |t| := by
  have := (convex_closedBall (0 : ℝ) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := C)
    (fun s _ => (hf s).hasDerivWithinAt) (fun s hs => hC s (by simpa using hs))
    (Metric.mem_closedBall_self (abs_nonneg t)) (y := t) (by simp)
  simpa using this

theorem taylor_bound {R : ℝ → (E →L[ℂ] E)} (h0 : R 0 = 1) (hR : ∀ s t, R (s + t) = (R s).comp (R t)) {M : ℝ}
    (hM : ∀ s, |s| ≤ 1 → ‖R s‖ ≤ M) {a b c : E} (ha : HasDerivAt (fun t : ℝ => R t a) b 0)
    (hb : HasDerivAt (fun t : ℝ => R t b) c 0) {t : ℝ} (ht : |t| ≤ 1) :
    ‖R t a - a - t • b‖ ≤ M * ‖c‖ * |t| * |t| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have h1 : ∀ s, |s| ≤ |t| → ‖R s b - b‖ ≤ M * ‖c‖ * |t| := fun s hs => by
    have := norm_sub_le (hasDerivAt_flow hR hb) (t := s) (C := M * ‖c‖) fun u hu =>
      ((R u).le_opNorm c).trans (mul_le_mul_of_nonneg_right (hM u (hu.trans (hs.trans ht))) (norm_nonneg _))
    simp only [h0, ContinuousLinearMap.one_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have h2 := norm_sub_le (f := fun s : ℝ => R s a - s • b) (f' := fun s => R s b - b)
    (fun s => by
      have := (hasDerivAt_flow hR ha s).fun_sub ((hasDerivAt_id' s).smul_const b)
      rwa [one_smul] at this) h1
  simp only [h0, ContinuousLinearMap.one_apply, zero_smul, sub_zero] at h2
  rwa [sub_right_comm]

theorem hasDerivAt_of_bound {f : ℝ → E} {b : E} {K : ℝ}
    (h : ∀ t, |t| ≤ 1 → ‖f t - f 0 - t • b‖ ≤ K * |t| * |t|) : HasDerivAt f b 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  have h1 : (fun t : ℝ => f t - f 0 - t • b) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
    have := h t (by simpa using ht)
    rwa [norm_pow, Real.norm_eq_abs, sq, ← mul_assoc]
  exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

end GlobalTheory.TypeSum.FamClosed


open GlobalTheory.TypeSum.FamClosed in
theorem GlobalTheory.TypeSum.isClosed_fam (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : Mx n → (E →L[ℂ] E)) (hρ : ModRep ε ρ) : IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) := by
  obtain ⟨h1, hmul, C, N, hC⟩ := hρ
  refine isClosed_of_closure_subset fun v hv => ⟨fun l X => ?_, fun l₁ l₂ a X Y => ?_, fun l₁ l₂ X Y Z hZ => ?_⟩
  · have hX : (X : Mx n) ∈ lieSet ε := X.2
    have h0 : ρ (NormedSpace.exp ((0 : ℝ) • (X : Mx n))) = 1 := by rw [zero_smul, NormedSpace.exp_zero, h1]
    have hR : ∀ s t : ℝ, ρ (NormedSpace.exp ((s + t) • (X : Mx n))) =
        (ρ (NormedSpace.exp (s • (X : Mx n)))).comp (ρ (NormedSpace.exp (t • (X : Mx n)))) := fun s t => by
      rw [exp_add_smul, hmul _ (exp_mem_UJ hX s) _ (exp_mem_UJ hX t)]
    have hc : Continuous fun s : ℝ => C * (1 + hs (NormedSpace.exp (s • (X : Mx n)))) ^ N :=
      continuous_const.mul ((continuous_const.add (continuous_hs.comp (continuous_exp_smul _))).pow N)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image hc.continuousOn
    have hM' : ∀ s : ℝ, |s| ≤ 1 → ‖ρ (NormedSpace.exp (s • (X : Mx n)))‖ ≤ M := fun s hs =>
      (hC _ (exp_mem_UJ hX s)).trans (hM ⟨s, by simpa using hs, rfl⟩)
    refine hasDerivAt_of_bound (K := M * ‖v (X :: X :: l)‖) fun t ht => ?_
    simp only [h0, ContinuousLinearMap.one_apply]
    have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        ‖ρ (NormedSpace.exp (t • (X : Mx n))) (w l) - w l - t • w (X :: l)‖ ≤ M * ‖w (X :: X :: l)‖ * |t| * |t|} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w (hw : w ∈ (Fam ε ρ : Set (List (lie (Jm ε)) → E))) => taylor_bound (R := fun s : ℝ => ρ (NormedSpace.exp (s • (X : Mx n))))
      h0 hR hM' (hw.1 l X) (hw.1 (X :: l) X) ht) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ (a • X + Y) :: l₂) = (a : ℂ) • w (l₁ ++ X :: l₂) + w (l₁ ++ Y :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w (hw : w ∈ (Fam ε ρ : Set (List (lie (Jm ε)) → E))) => hw.2.1 l₁ l₂ a X Y) hcl hv
  · have hcl : IsClosed {w : List (lie (Jm ε)) → E |
        w (l₁ ++ X :: Y :: l₂) - w (l₁ ++ Y :: X :: l₂) = w (l₁ ++ Z :: l₂)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun w (hw : w ∈ (Fam ε ρ : Set (List (lie (Jm ε)) → E))) => hw.2.2 l₁ l₂ X Y Z hZ) hcl hv
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem coefBound_two :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ a c : H, Sm ε σ a → a ≠ 0 → Sm ε σ c → c ≠ 0 → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ γ : H → H → ℂ, (∀ b, Sm ε σ b → SobFun ε σ (γ b)) → (∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w))) → ∀ M : ℝ, 0 ≤ M → (∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ‖γ (σ g' c) (σ g a)‖ ≤ M * (1 + hs g) ^ N * (1 + hs g') ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖γ b w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ hS hB a c ha ha0 hc hc0 N
  obtain ⟨Sa, Ca, hSa, hCa, ba⟩ := hB a ha ha0 N
  obtain ⟨Sc, Cc, hSc, hCc, bc⟩ := hB c hc hc0 N
  refine ⟨Sa ++ Sc, Ca * Cc, words_append hSa hSc, mul_nonneg hCa hCc, ?_⟩
  intro γ h1 h2 M hM hγ b w hb hw
  have step : ∀ g' ∈ UJset ε, ‖γ (σ g' c) w‖ ≤ (Ca * M * sobNorm σ Sa w) * (1 + hs g') ^ N := by
    intro g' hg'
    obtain ⟨ℓ, hℓ, e⟩ := (h1 _ (hc.translate hS.1 hg')).exists_ext
    have hp : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have := ba ℓ hℓ (M * (1 + hs g') ^ N) (mul_nonneg hM hp) (fun g hg => by
      rw [e _ (ha.translate hS.1 hg)]
      exact (hγ g hg g' hg').trans (le_of_eq (by ring))) w hw
    rw [e _ hw] at this
    exact this.trans (le_of_eq (by ring))
  obtain ⟨ℓ, hℓ, e⟩ := (h2 w hw).exists_ext
  have n1 := sobNorm_nonneg σ Sa w
  have n2 := sobNorm_nonneg σ Sc w
  have n3 := sobNorm_nonneg σ Sa b
  have n4 := sobNorm_nonneg σ Sc b
  have key := bc ℓ hℓ (Ca * M * sobNorm σ Sa w) (by positivity) (fun g hg => by
    rw [e _ (hc.translate hS.1 hg), norm_star]
    exact step g hg) b hb
  rw [e _ hb, norm_star] at key
  rw [sobNorm_append, sobNorm_append]
  refine key.trans ?_
  calc Cc * (Ca * M * sobNorm σ Sa w) * sobNorm σ Sc b
      = Ca * Cc * M * sobNorm σ Sc b * sobNorm σ Sa w := by ring
    _ ≤ _ := by gcongr <;> linarith

end GlobalTheory.TypeSum
end

section

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem Std.exists_inner_approx {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) :
    ∃ (m : ℕ) (S : Fin m → List (Mx n)), (∀ i, ∀ X ∈ S i, X ∈ lieSet ε) ∧ ∀ δ : ℝ, 0 < δ → ∃ u : H,
      ∀ z, Sm ε σ z → ‖ℓ z - ⟪u, z⟫_ℂ‖ ≤ δ * ∑ i, ‖Dw σ (S i) z‖ := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  refine ⟨m, S, hS, fun δ hδ => ?_⟩
  have hx : ∀ i, ∃ x ∈ smooth (Jm ε) σ, dist ((InnerProductSpace.toDual ℂ H).symm (Λ i)) x < δ := fun i =>
    Metric.mem_closure_iff.1 (h.dense_smooth _) δ hδ
  choose x hxs hxd using hx
  choose u hu using fun i => exists_adjoint (isUnit_Jm ε) h.1 (S i) (hS i) (x i) (hxs i)
  refine ⟨∑ i, u i, fun z hz => ?_⟩
  rw [hΛ z hz, sum_inner, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← hu i z hz, ← InnerProductSpace.toDual_symm_apply, ← inner_sub_left]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [← dist_eq_norm]
  exact (hxd i).le

theorem avgBd_sobCont : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (T : H → H) (Z : Set (Mx n)) (C : ℝ), IsCompact Z →
    Z ⊆ UJset ε → 0 ≤ C → AvgBd σ T Z C → ∀ (ι : Type) [Fintype ι] (ℓ : ι → (H →ₗ[ℂ] ℂ)) (w : ι → H),
    (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (w j)) → (∀ j, Sm ε σ (T (w j))) → ∀ M : ℝ, 0 ≤ M →
    (∀ y ∈ Z, ‖∑ j, ℓ j (σ y (w j))‖ ≤ M) → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M := by
  intro n ε H _ _ _ σ h T Z C hZ hZU hC hA ι _ ℓ w hℓ hw hTw M hM hb
  choose m S hS hap using fun j => h.exists_inner_approx (hℓ j)
  have hc : ContinuousOn (fun y => ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖) Z :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ =>
      ((h.continuousOn_Dw (hS j i) (hw j)).mono hZU).norm
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn hc
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, ∑ j, ∑ i, ‖Dw σ (S j i) (σ y (w j))‖ ≤ K := fun y hy =>
    ((le_abs_self _).trans (hK₀ y hy)).trans (le_max_left _ _)
  set K' := ∑ j, ∑ i, ‖Dw σ (S j i) (T (w j))‖ with hK'
  have key : ∀ δ : ℝ, 0 < δ → ‖∑ j, ℓ j (T (w j))‖ ≤ C * M + δ * (C * K + K') := by
    intro δ hδ
    choose u hu using fun j => hap j δ hδ
    have hd : ∀ z : ι → H, (∀ j, Sm ε σ (z j)) →
        ‖∑ j, ℓ j (z j) - ∑ j, ⟪u j, z j⟫_ℂ‖ ≤ δ * ∑ j, ∑ i, ‖Dw σ (S j i) (z j)‖ := fun z hz => by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hu j _ (hz j))
    have h1 := hA ι u w (M + δ * K) (by positivity) fun y hy => by
      have e1 := hd (fun j => σ y (w j)) fun j => (hw j).translate h.1 (hZU hy)
      have e2 := norm_le_norm_add_norm_sub (∑ j, ℓ j (σ y (w j))) (∑ j, ⟪u j, σ y (w j)⟫_ℂ)
      have e3 := mul_le_mul_of_nonneg_left (hK y hy) hδ.le
      have e4 := hb y hy
      linarith
    have h2 := hd (fun j => T (w j)) hTw
    have h3 := norm_le_norm_add_norm_sub' (∑ j, ℓ j (T (w j))) (∑ j, ⟪u j, T (w j)⟫_ℂ)
    nlinarith
  have ht : Tendsto (fun δ : ℝ => C * M + δ * (C * K + K')) (𝓝[>] 0) (𝓝 (C * M + 0 * (C * K + K'))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)

end GlobalTheory.TypeSum

end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.isAffineSpaceCoveredMorphism : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → AffCover M M' φ f (Fintype.card J - 1) := by
  first | exact @GlobalTheory.FlagBundle.ProjBundle.affCover | exact GlobalTheory.FlagBundle.ProjBundle.affCover | (intros; apply GlobalTheory.FlagBundle.ProjBundle.affCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι] (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω'), k' τ = k τ + 1 → (∀ τ', τ' ≠ τ → k' τ' = k τ') → A₀ ∈ S.S (genericPoint M.Z) → (∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A))) → ProjPoints M EE M' φ f s → ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  first | exact @GlobalTheory.FlagBundle.exists_fr_stepSet | exact GlobalTheory.FlagBundle.exists_fr_stepSet | (intros; apply GlobalTheory.FlagBundle.exists_fr_stepSet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.geometricallyIntegral_of_affCover : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → GeometricallyIntegral M.s → GeometricallyIntegral M'.s := by
  first | exact @GlobalTheory.FlagBundle.AffCover.geometricallyIntegral | exact GlobalTheory.FlagBundle.AffCover.geometricallyIntegral | (intros; apply GlobalTheory.FlagBundle.AffCover.geometricallyIntegral <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.isFlagRefinementBundle_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) := by
  first | exact @GlobalTheory.FlagBundle.refines_comp | exact GlobalTheory.FlagBundle.refines_comp | (intros; apply GlobalTheory.FlagBundle.refines_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.exists_algHom_functionField_of_specializes_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X), q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) → ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  first | exact @GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint | exact GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint | (intros; apply GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  first | exact @GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback | exact GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback | (intros; apply GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → KeepsRad M M' φ f := by
  first | exact @GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | exact GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | (intros; apply GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover <;> assumption)
end
