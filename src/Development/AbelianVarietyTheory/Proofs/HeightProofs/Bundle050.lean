module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle047
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KAvgDeriv

open MeasureTheory Filter Topology GlobalTheory.KFourier

variable {n : ℕ}

theorem toMK_expK_real {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) (t : ℝ) :
    toMK (expK ε X t) = NormedSpace.exp (t • X) := by
  rw [toMK_expK hX t, Complex.coe_smul]

theorem toMK_mem_UJ {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integral_conj_swap {ε : Fin n → Bool} (e : KG ε → ℂ) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k)
    (φ : Mx n → ℂ) (g : Mx n) (κ : KG ε) :
    ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε) = ∫ k, e k * φ (g * toMK k * toMK κ) ∂(muK ε) := by
  have h1 := integral_mul_left_eq_self (μ := muK ε) (fun k => e k * φ (g * toMK κ * toMK k)) κ⁻¹
  have h2 := integral_mul_right_eq_self (μ := muK ε) (fun k => e (κ⁻¹ * k) * φ (g * toMK k)) κ
  have ea : ∀ k, g * toMK κ * toMK (κ⁻¹ * k) = g * toMK k := fun k => by
    rw [mul_assoc, ← toMK_mul, mul_inv_cancel_left]
  have eb : ∀ k, e (κ⁻¹ * (k * κ)) = e k := fun k => by
    have := he κ⁻¹ k
    rwa [inv_inv, mul_assoc] at this
  calc ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε)
      = ∫ k, e (κ⁻¹ * k) * φ (g * toMK κ * toMK (κ⁻¹ * k)) ∂(muK ε) := h1.symm
    _ = ∫ k, e (κ⁻¹ * k) * φ (g * toMK k) ∂(muK ε) := by simp only [ea]
    _ = ∫ k, e (κ⁻¹ * (k * κ)) * φ (g * toMK (k * κ)) ∂(muK ε) := h2.symm
    _ = _ := by simp only [eb, toMK_mul, mul_assoc]

variable {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ}

theorem measurable_fam (hD : IsDerFam ε F) {f : Mx n → ℂ} (hf : ContinuousOn f (UJset ε))
    (hF0 : ∀ g ∈ UJset ε, F [] g = f g) :
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      Measurable fun k : KG ε => F l (a * toMK k * b) := by
  intro l
  induction l with
  | nil =>
    intro _ a ha b hb
    have hm : ∀ k : KG ε, a * toMK k * b ∈ UJset ε := fun k => mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have e1 : (fun k : KG ε => F [] (a * toMK k * b)) = fun k => f (a * toMK k * b) :=
      funext fun k => hF0 _ (hm k)
    rw [e1]
    exact (hf.comp_continuous ((continuous_const.mul (continuous_toMK ε)).mul continuous_const) hm).measurable
  | cons X l ih =>
    intro hl a ha b hb
    have hX : X ∈ lieSet ε := hl X List.mem_cons_self
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    let s : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    have hs0 : Tendsto s atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun m => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, s]; positivity⟩
    have hmeas : ∀ m : ℕ, Measurable fun k : KG ε =>
        (s m)⁻¹ • (F l (a * toMK k * (b * NormedSpace.exp (s m • X))) - F l (a * toMK k * b)) := fun m => by
      have := ((ih hl' a ha _ (mul_mem_UJ hb (exp_mem_UJ hX (s m)))).sub (ih hl' a ha b hb)).const_smul (s m)⁻¹
      exact this
    refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun k => ?_)
    have hg : a * toMK k * b ∈ UJset ε := mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have hd := (hasDerivAt_iff_tendsto_slope.1 (hD l hl' X hX _ hg)).comp hs0
    refine hd.congr fun m => ?_
    simp only [Function.comp_apply, slope_def_module, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
      mul_assoc]

theorem hasDerivAt_avg (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n}
    (hX : inK ε X) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε))
      (∫ k, e k * F (X :: l) (g * toMK k) ∂(muK ε)) 0 := by
  have hXl : X ∈ lieSet ε := hX.1
  have hl' : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | h
    exacts [hXl, hl Y h]
  have hre : (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε)) =
      fun t => ∫ k, e k * F l (g * toMK k * NormedSpace.exp (t • X)) ∂(muK ε) := by
    funext t
    rw [integral_conj_swap e he, toMK_expK_real hX]
  rw [hre]
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hec.continuousOn
  obtain ⟨C, hC⟩ := hG (X :: l) hl'
  obtain ⟨C0, hC0⟩ := hG l hl
  have hmem : ∀ (k : KG ε) (s : ℝ), g * toMK k * NormedSpace.exp (s • X) ∈ UJset ε := fun k s =>
    mul_mem_UJ (mul_mem_UJ hg (toMK_mem_UJ k)) (exp_mem_UJ hXl s)
  have hhs : ∀ (k : KG ε) (s : ℝ), hs (g * toMK k * NormedSpace.exp (s • X)) = hs g := fun k s => by
    rw [← toMK_expK_real hX, mul_assoc, ← toMK_mul]
    exact ((hermitian_small_ball n ε).2 _ _ (toMK_mem_K _)).1
  have hem : Measurable e := hec.measurable
  have hbd : ∀ (l' : List (Mx n)) (C' : ℝ), (∀ h ∈ UJset ε, ‖F l' h‖ ≤ C' * (1 + hs h) ^ N) →
      ∀ (k : KG ε) (s : ℝ), ‖e k * F l' (g * toMK k * NormedSpace.exp (s • X))‖ ≤ M * (C' * (1 + hs g) ^ N) :=
    fun l' C' hC' k s => by
      rw [norm_mul]
      refine mul_le_mul (hM k trivial) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM k trivial))
      rw [← hhs k s]
      exact hC' _ (hmem k s)
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun k => e k * F l (g * toMK k * NormedSpace.exp (t • X))) (muK ε) :=
    fun t => (hem.mul (measurable_fam hD hf hF0 l hl g hg _ (exp_mem_UJ hXl t))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X)))
      (muK ε) := (hem.mul (measurable_fam hD hf hF0 (X :: l) hl' g hg _ (exp_mem_UJ hXl 0))).aestronglyMeasurable
  have hint : Integrable (fun k => e k * F l (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) (muK ε) :=
    Integrable.mono' (integrable_const (M * (C0 * (1 + hs g) ^ N))) (hmeasF 0) (ae_of_all _ fun k => hbd l C0 hC0 k 0)
  have hdif : ∀ (k : KG ε) (s : ℝ), HasDerivAt (fun t : ℝ => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
      (e k * F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s := fun k s => by
    have h1 := hD l hl X hXl _ (hmem k s)
    have h2 : HasDerivAt (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X)))
        (F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s :=
      HasDerivAt.comp_sub_const (f := fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp (t • X)))
        s s (by rw [sub_self]; exact h1)
    have e2 : (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X))) =
        fun t => F l (g * toMK k * NormedSpace.exp (t • X)) := by
      funext t
      rw [mul_assoc (g * toMK k), ← exp_add_smul, add_sub_cancel]
    rw [e2] at h2
    exact h2.const_mul (e k)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
    (F' := fun t k => e k * F (X :: l) (g * toMK k * NormedSpace.exp (t • X)))
    (bound := fun _ => M * (C * (1 + hs g) ^ N)) (s := Set.univ) Filter.univ_mem (Eventually.of_forall hmeasF) hint hmeasF'
    (ae_of_all _ fun k t _ => hbd (X :: l) C hC k t) (integrable_const _) (ae_of_all _ fun k s _ => hdif k s)
  have e3 : (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) =
      fun k => e k * F (X :: l) (g * toMK k) := by
    funext k
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  simpa only [e3] using key.2

theorem rder_avgK_all (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {y : Mx n} (hy : y ∈ UJset ε) :
    ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ k' : KG ε,
      rder ε u (avgK ε e f y) k' = ∫ k, e k * F u (y * toMK k' * toMK k) ∂(muK ε) := by
  intro u
  induction u with
  | nil =>
    intro _ k'
    rw [rder_nil]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only
    rw [hF0 _ (mul_mem_UJ (mul_mem_UJ hy (toMK_mem_UJ k')) (toMK_mem_UJ k))]
  | cons X l ih =>
    intro hu k'
    have hX : inK ε X := hu X List.mem_cons_self
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hlK Y hY).1
    rw [rder_cons]
    have e1 : (fun t : ℝ => rder ε l (avgK ε e f y) (k' * expK ε X t)) =
        fun t => ∫ k, e k * F l (y * toMK k' * toMK (expK ε X t) * toMK k) ∂(muK ε) := by
      funext t
      rw [ih hlK, toMK_mul, mul_assoc y]
    rw [e1]
    exact (hasDerivAt_avg hD hG hf hF0 hec he hl hX (mul_mem_UJ hy (toMK_mem_UJ k'))).deriv

theorem rder_avgK_one (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ) (hD : IsDerFam ε F)
    (hG : FamGrowth ε N F) (f : Mx n → ℂ) (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g)
    (e : KG ε → ℂ) (hec : Continuous e) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) (u : List (Mx n))
    (hu : ∀ X ∈ u, inK ε X) (y : Mx n) (hy : y ∈ UJset ε) :
    GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  rw [rder_avgK_all hD hG hf hF0 hec he hy u hu 1, toMK_one, mul_one]

end GlobalTheory.KAvgDeriv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integral_conjK (ε : Fin n → Bool) (f : KG ε → ℂ) (a : KG ε) :
    ∫ k, f (a * k * a⁻¹) ∂(muK ε) = ∫ k, f k ∂(muK ε) := by
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  have h1 := integral_mul_right_eq_self (μ := muK ε) (fun k => f (a * k)) a⁻¹
  have h2 := integral_mul_left_eq_self (μ := muK ε) f a
  simp only [mul_assoc] at h1 ⊢
  exact h1.trans h2

theorem integrable_of_continuousK {ε : Fin n → Bool} {f : KG ε → ℂ} (hf : Continuous f) :
    Integrable f (muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem lowV_le (ε : Fin n → Bool) (i : ℕ) : lowV ε i ≤ polyV ε i := by
  cases i with
  | zero => exact bot_le
  | succ j => exact polyV_mono ε (Nat.le_succ j)

theorem integral_sub_mulK {ε : Fin n → Bool} {f g h : KG ε → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    ∫ k, (f - g) k * h k ∂(muK ε) = ∫ k, f k * h k ∂(muK ε) - ∫ k, g k * h k ∂(muK ε) := by
  rw [← integral_sub (integrable_of_continuousK (f := fun k => f k * h k) (hf.mul hh))
    (integrable_of_continuousK (f := fun k => g k * h k) (hg.mul hh))]
  congr 1; funext k; simp [sub_mul]

theorem isKer_unique {ε : Fin n → Bool} {i : ℕ} {e e' : KG ε → ℂ} (he : IsKer ε i e) (he' : IsKer ε i e') :
    e = e' := by
  have hdmem : (e - e') ∈ polyV ε i := sub_mem he.1 he'.1
  have hc : Continuous (e - e') := continuous_of_mem hdmem
  have hce : Continuous e := continuous_of_mem he.1
  have hce' : Continuous e' := continuous_of_mem he'.1
  have hp : (fun k => star ((e - e') k)) ∈ polyV ε i := star_mem hdmem
  have horth : ∀ q ∈ lowV ε i, ∫ k, star (q k) * star ((e - e') k) ∂(muK ε) = 0 := by
    intro q hq
    have hqc : Continuous q := continuous_of_mem (lowV_le ε i hq)
    have h1 := he.2.1 q hq
    have h2 := he'.2.1 q hq
    have h3 : ∫ k, (e - e') k * q k ∂(muK ε) = 0 := by
      rw [integral_sub_mulK hce hce' hqc, h1, h2, sub_self]
    calc ∫ k, star (q k) * star ((e - e') k) ∂(muK ε)
        = ∫ k, (starRingEnd ℂ) ((e - e') k * q k) ∂(muK ε) := by
          congr 1; funext k; rw [map_mul, mul_comm]; rfl
      _ = (starRingEnd ℂ) (∫ k, (e - e') k * q k ∂(muK ε)) := integral_conj
      _ = 0 := by rw [h3, map_zero]
  have h0 : ∫ k, (e - e') k * star ((e - e') k) ∂(muK ε) = 0 := by
    have a1 := he.2.2 _ hp horth
    have a2 := he'.2.2 _ hp horth
    have hs : Continuous (fun k => star ((e - e') k)) := continuous_star.comp hc
    rw [integral_sub_mulK hce hce' hs, a1, a2, sub_self]
  have hns : Continuous (fun k => Complex.normSq ((e - e') k)) := Complex.continuous_normSq.comp hc
  have h1 : ∫ k, Complex.normSq ((e - e') k) ∂(muK ε) = 0 := by
    have : (fun k => (e - e') k * star ((e - e') k)) = fun k => ((Complex.normSq ((e - e') k) : ℝ) : ℂ) :=
      funext fun k => Complex.mul_conj _
    rw [this, integral_complex_ofReal] at h0
    exact_mod_cast h0
  have h2 : (fun k => Complex.normSq ((e - e') k)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h1
  have h3 : (fun k => Complex.normSq ((e - e') k)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
  funext k
  have := congrFun h3 k
  simp only [Pi.zero_apply, map_eq_zero, Pi.sub_apply] at this
  exact sub_eq_zero.1 this

theorem conj_mem {ε : Fin n → Bool} (a : KG ε) {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ (a * k * a⁻¹)) ∈ polyV ε d := by
  have := mul_right_mem a⁻¹ (mul_left_mem a h)
  simpa only [mul_assoc] using this

theorem conj_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k * a⁻¹)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact conj_mem a h

theorem isKer_conj {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) (a : KG ε) :
    IsKer ε i (fun k => e (a * k * a⁻¹)) := by
  have key : ∀ f g : KG ε → ℂ, ∫ k, f (a * k * a⁻¹) * g k ∂(muK ε) = ∫ k, f k * g (a⁻¹ * k * a) ∂(muK ε) := by
    intro f g
    rw [← integral_conjK ε (fun k => f k * g (a⁻¹ * k * a)) a]
    congr 1; funext k
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  refine ⟨conj_mem a he.1, ?_, ?_⟩
  · intro q hq
    rw [key]
    have := conj_mem_low a⁻¹ hq
    simpa only [inv_inv] using he.2.1 _ this
  · intro p hp horth
    rw [key]
    have hp' : (fun k => p (a⁻¹ * k * a)) ∈ polyV ε i := by simpa only [inv_inv] using conj_mem a⁻¹ hp
    have horth' : ∀ q ∈ lowV ε i, ∫ k, star (q k) * p (a⁻¹ * k * a) ∂(muK ε) = 0 := by
      intro q hq
      rw [← integral_conjK ε (fun k => star (q k) * p (a⁻¹ * k * a)) a]
      have := horth _ (conj_mem_low a hq)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    rw [he.2.2 _ hp' horth']
    simp

theorem isKer_class : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  intro n ε i e he a k
  have := isKer_unique (isKer_conj he a) he
  exact congrFun this k

end GlobalTheory.KFourier

end
end

section

namespace GlobalTheory.OrthogonalProjectionPoly

open MeasureTheory

theorem exists_sub_orthogonal {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ q ∈ V, Continuous q) (p : X → ℂ) (hp : Continuous p) :
    ∃ p' ∈ V, ∀ q ∈ V, ∫ x, star (q x) * (p x - p' x) ∂μ = 0 := by
  classical
  let j : V →ₗ[ℂ] C(X, ℂ) :=
    { toFun := fun q => ⟨q, hV q q.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T : V →ₗ[ℂ] Lp ℂ 2 μ := (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap ∘ₗ j
  let W : Submodule ℂ (Lp ℂ 2 μ) := LinearMap.range T
  have : FiniteDimensional ℂ W := LinearMap.finiteDimensional_range T
  let P : C(X, ℂ) := ⟨p, hp⟩
  obtain ⟨p', hp'⟩ := LinearMap.mem_range.1 (W.starProjection_apply_mem (ContinuousMap.toLp 2 μ ℂ P))
  refine ⟨p', p'.2, fun q hq => ?_⟩
  have h0 := W.starProjection_inner_eq_zero (ContinuousMap.toLp 2 μ ℂ P) (T ⟨q, hq⟩) ⟨⟨q, hq⟩, rfl⟩
  rw [← hp'] at h0
  have h1 : ContinuousMap.toLp 2 μ ℂ P - T p' = ContinuousMap.toLp 2 μ ℂ (P - j p') := by
    rw [map_sub]
    rfl
  rw [h1] at h0
  have h2 : inner ℂ (ContinuousMap.toLp 2 μ ℂ (P - j p')) (T ⟨q, hq⟩) =
      ∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ :=
    ContinuousMap.inner_toLp μ (P - j p') (j ⟨q, hq⟩)
  rw [h2] at h0
  calc ∫ x, star (q x) * (p x - (p' : X → ℂ) x) ∂μ
      = ∫ x, (starRingEnd ℂ) (q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x)) ∂μ := by
        congr 1
        funext x
        rw [map_mul, Complex.conj_conj, starRingEnd_apply, _root_.mul_comm]
    _ = (starRingEnd ℂ) (∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ) := integral_conj
    _ = 0 := by rw [h0, map_zero]

theorem exists_proj_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : ↥(Formalism.REAL.KG ε) → ℂ), Continuous p →
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ (k : ↥(Formalism.REAL.KG ε)), Star.star (q k) * (p k - p' k) ∂ Formalism.REAL.muK ε = (0 : ℂ) := by
  intro n ε d p hp
  exact exists_sub_orthogonal (Formalism.REAL.muK ε) (GlobalTheory.KFourier.polyV ε d)
    (fun q hq => GlobalTheory.KFourier.continuous_of_mem hq) p hp

end GlobalTheory.OrthogonalProjectionPoly
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem coord_mul_eq_sum (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) (a k : KG ε) :
    coord ε c (a * k) = ∑ l : Fin n, coord ε (c.1, l, c.2.2) a * coord ε (l, c.2.1, c.2.2) k := by
  simp only [coord, toMK_mul, Matrix.mul_apply]
  split_ifs
  · rfl
  · rw [star_sum]; exact Finset.sum_congr rfl fun l _ => by rw [star_mul', mul_comm]

theorem integrable_muK_of_continuous {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem conv_mono_mem (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) :
    ∀ (d : ℕ), s.length ≤ d → ∀ h : KG ε → ℂ, Continuous h →
      (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction s with
  | nil =>
    intro d _ h _
    simpa [mono] using const_mem ε d (∫ k, h k ∂(muK ε))
  | cons c s ih =>
    intro d hd h hh
    have hd' : s.length + 1 ≤ d := by simpa using hd
    have e : (fun k' : KG ε => ∫ k, mono ε (c :: s) (k'⁻¹ * k) * h k ∂(muK ε)) =
        ∑ l : Fin n, (fun k' : KG ε => coord ε (c.1, l, c.2.2) k'⁻¹) *
          (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * (coord ε (l, c.2.1, c.2.2) k * h k) ∂(muK ε)) := by
      funext k'
      simp only [Finset.sum_apply, Pi.mul_apply]
      simp only [← integral_const_mul]
      rw [← integral_finsetSum]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        have h1 : mono ε (c :: s) (k'⁻¹ * k) = coord ε c (k'⁻¹ * k) * mono ε s (k'⁻¹ * k) := by simp [mono]
        simp only [h1, coord_mul_eq_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      · intro l _
        refine integrable_muK_of_continuous (continuous_const.mul ?_)
        exact ((continuous_mono ε s).comp (continuous_const.mul continuous_id)).mul
          ((continuous_coord ε _).mul hh)
    rw [e]
    refine Submodule.sum_mem _ fun l _ => ?_
    exact polyV_mono ε (show 1 + (d - 1) ≤ d by omega)
      (mul_mem (coord_inv_mem ε _) (ih (d - 1) (by omega) _ ((continuous_coord ε _).mul hh)))

theorem conv_mem {ε : Fin n → Bool} {d : ℕ} {e : KG ε → ℂ} (he : e ∈ polyV ε d) {h : KG ε → ℂ}
    (hh : Continuous h) : (fun k' : KG ε => ∫ k, e (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact conv_mono_mem ε s d hs h hh
  | zero =>
    simpa using const_mem ε d 0
  | add x y hx hy ihx ihy =>
    convert add_mem ihx ihy using 1
    funext k'
    simp only [Pi.add_apply, add_mul]
    refine integral_add (integrable_muK_of_continuous ?_) (integrable_muK_of_continuous ?_)
    · exact ((continuous_of_mem (d := d) hx).comp (continuous_const.mul continuous_id)).mul hh
    · exact ((continuous_of_mem (d := d) hy).comp (continuous_const.mul continuous_id)).mul hh
  | smul a x _ ih =>
    convert Submodule.smul_mem _ a ih using 1
    funext k'
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem avgK_mem : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i →
    ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε,
      GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  intro n ε i e he f hf y hy
  have hh : Continuous fun k : KG ε => f (y * toMK k) :=
    hf.comp_continuous (continuous_const.mul (GlobalTheory.TypeSum.continuous_toMK ε))
      fun k => GlobalTheory.TypeSum.mul_mem_UJ hy (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))
  convert conv_mem he hh using 1
  funext k'
  rw [← integral_mul_left_eq_self (μ := muK ε) _ k']
  simp only [avgK, inv_mul_cancel_left, toMK_mul, Matrix.mul_assoc]

end GlobalTheory.KFourier

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

theorem _root_.GlobalTheory.T.componentRing_away_genericSection_quotient : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (D' N' : ℕ) (hD : D' + 1 = WeightFamilies.dimY D j + 1) (eN : Fin (N' + 1) ≃ Fin N) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [FiniteDimensional (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N)], (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ a : B.KO, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) → (∀ q : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (Fin.cast hD q.1, eN q.2))) → gF (X.inc wL (w (eN j₀))) ≠ 0 → (∀ k, x k * gF (X.inc wL (w (eN j₀))) = gF (X.inc wL (w (eN (j₀.succAbove k))))) → ∃ χ : RZs X la N Ω gF w →ₐ[Kp X la N] Kp X la N ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N', Function.Surjective χ ∧ RingHom.ker χ = Ideal.map (phiZ X la N Ω gF w) (Jid X la w) ∧ ∀ ω : Ω, χ (CurveLoc.psiZ X la N w gF ω) = (1 : Kp X la N) ⊗ₜ[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') ω := by
  first | exact @GlobalTheory.componentRing_away_quotient | exact GlobalTheory.componentRing_away_quotient | (intros; apply GlobalTheory.componentRing_away_quotient <;> assumption)
end
