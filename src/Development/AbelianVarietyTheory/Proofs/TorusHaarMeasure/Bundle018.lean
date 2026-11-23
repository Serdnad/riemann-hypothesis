module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.exp_neg_phla {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    Real.exp (-_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la x) = X.nfac la x ^ 2 := by
  have hpos := _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) + Real.log (X.nfac la x) by
    ring, Real.exp_add, Real.exp_log hpos]
  ring


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_rmul (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.pnorm la P x :=
  _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_lact (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = X.pnorm la P x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hN
  change ‖P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x)‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = ‖P x‖ * X.nfac la x
  rw [hP.2.2 γ hγ x hx, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hN r X la γ hγ x hx]


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.measurable_cut {f : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ}
    (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator fun x => ENNReal.ofReal (f x)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise (ENNReal.continuous_ofReal.comp_continuousOn hf)
    continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.exists_sum_le {N : ℕ} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : Fin N → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : ∀ k, X.IsBddSec la (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨1 + ∑ k, C k ^ 2, by positivity, fun x hx => ?_⟩
  have hle : ∀ k, X.pnorm la (P k) x ^ 2 ≤ C k ^ 2 := by
    intro k
    have h0 : 0 ≤ X.pnorm la (P k) x := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      exact mul_nonneg (norm_nonneg _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la).le
    exact pow_le_pow_left₀ h0 (hC k x hx) 2
  calc ∑ k, X.pnorm la (P k) x ^ 2 ≤ ∑ k, C k ^ 2 := Finset.sum_le_sum fun k _ => hle k
    _ ≤ 1 + ∑ k, C k ^ 2 := by linarith


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le {a C t : ℝ} (hC : 0 < C) (h : a ≤ C) (ht : 0 ≤ t) :
    ENNReal.ofReal (C ^ (-t)) ≤ ENNReal.ofReal a ^ (-t) := by
  rcases lt_or_ge 0 a with ha | ha
  · rw [ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha h (by linarith))
  · rw [ENNReal.ofReal_of_nonpos ha]
    rcases ht.lt_or_eq with ht | ht
    · rw [ENNReal.zero_rpow_of_neg (by linarith)]
      exact le_top
    · subst ht
      simp

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)

end GlobalTheory.Up.DivMetricPf
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.VanishAtSimpleZero

open Filter Metric

theorem lintegral_eq_top {n : ℕ} (hn : 0 < n) {g S : V n → ℝ} {a c ρ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hρ : 0 < ρ) (hg : ∀ᶠ z in 𝓝 (0 : V n), a ≤ g z)
    (hS : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < S z ∧ S z ≤ c * ‖z‖ ^ 2) :
    ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) = ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hg.and hS)
  have hr0 : 0 < min ε ρ := lt_min hε hρ
  have hsubε : ball (0 : V n) (min ε ρ) ⊆ ball 0 ε := ball_subset_ball (min_le_left _ _)
  have hsubρ : ball (0 : V n) (min ε ρ) ⊆ ball 0 ρ := ball_subset_ball (min_le_right _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have hinf : ∫⁻ z in ball (0 : V n) (min ε ρ), ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) = ⊤ := by
    have hδ : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
    have hT := ReciprocityTheory.L2DbarEstimates.I.vanish_div n hn ReciprocityTheory.L2DbarEstimates.C.mvDiv hr0 hc hδ
    refine top_unique (le_of_tendsto' hT fun k => ?_)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz _ => ?_))
    have hpos : 0 < c * ‖z‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.2 hz) 2)
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hpos ?_ ?_)
    · have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · simp
  have hlow : ENNReal.ofReal a * ∫⁻ z in ball (0 : V n) (min ε ρ),
      ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) ≤
      ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ (lintegral_mono_set hsubρ)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz hzb => ?_))
    obtain ⟨hgz, hSz⟩ := hball z (hsubε hzb)
    obtain ⟨hS0, hSle⟩ := hSz hz
    rw [← ENNReal.ofReal_mul ha.le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hgz (Real.rpow_le_rpow_of_nonpos hS0 hSle (by simp))
      (Real.rpow_nonneg (by positivity) _) (ha.le.trans hgz))
  rw [hinf, ENNReal.mul_top (by simpa using ha)] at hlow
  exact top_unique hlow

theorem vanish_of_simple_zero {n : ℕ} (hn : 0 < n) {u w : V n → ℂ} {s : Fin n → V n → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ContinuousAt u 0) (hs : ∀ k, DifferentiableAt ℂ (s k) 0)
    (hw : DifferentiableAt ℂ w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0)
    (hint : ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖u z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-(n : ℝ))) < ⊤) : u 0 = 0 := by
  by_contra hu0
  set f : V n → V n := fun z => (WithLp.toLp 2 fun k => s k z / w z : V n) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    by_contra hnd
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp [ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.iso_zero hfd.hasFDerivAt hdet hf0
  have hSpos : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < ∑ k, ‖s k z‖ ^ 2 := by
    filter_upwards [closedBall_mem_nhds (0 : V n) hδ] with z hz hz0
    refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity) (Ne.symm fun hsum => hz0 ?_)
    refine hiso z hz ?_
    have hk : ∀ k, s k z = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 hsum k (Finset.mem_univ _)
      simpa using this
    ext k
    simp [hf, hk k]
  have hbig : ∀ k, ∃ C > 0, ∀ᶠ z in 𝓝 (0 : V n), ‖s k z‖ ≤ C * ‖z‖ := fun k => by
    obtain ⟨C, hC, hCw⟩ := ((hs k).hasFDerivAt.isBigO_sub).exists_pos
    refine ⟨C, hC, hCw.bound.mono fun z hz => ?_⟩
    simpa [hs0 k] using hz
  choose C hC hCb using hbig
  have hSle : ∀ᶠ z in 𝓝 (0 : V n), ∑ k, ‖s k z‖ ^ 2 ≤ (∑ k, C k ^ 2 + 1) * ‖z‖ ^ 2 := by
    filter_upwards [Filter.eventually_all.2 hCb] with z hz
    calc ∑ k, ‖s k z‖ ^ 2 ≤ ∑ k, (C k * ‖z‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
      _ = (∑ k, C k ^ 2) * ‖z‖ ^ 2 := by rw [Finset.sum_mul]; simp [mul_pow]
      _ ≤ _ := by nlinarith [sq_nonneg ‖z‖]
  have hpos : 0 < ‖u 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hu0) 2
  have hcont : ContinuousAt (fun z => ‖u z‖ ^ 2) 0 := hu.norm.pow 2
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖u 0‖ ^ 2 / 2 ≤ ‖u z‖ ^ 2 :=
    hcont.eventually (le_mem_nhds (show ‖u 0‖ ^ 2 / 2 < ‖u 0‖ ^ 2 by linarith))
  have htop := lintegral_eq_top hn (g := fun z => ‖u z‖ ^ 2) (S := fun z => ∑ k, ‖s k z‖ ^ 2)
    (by positivity) (by positivity : (0 : ℝ) < ∑ k, C k ^ 2 + 1) hρ hg
    (by filter_upwards [hSpos, hSle] with z h1 h2 hz0 using ⟨h1 hz0, h2⟩)
  exact absurd hint (by rw [htop]; exact lt_irrefl _)

end GlobalTheory.VanishAtSimpleZero

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanishAtS_holds : VanishAtSStatement (E := E) := by
  intro r X x1 hn _ _ u w0 s ρ hρ hdu hds hdw hw0 hs0 hdet hint
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X x1
  have hb : Metric.ball (0 : V (nd X)) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have key := VanishAtSimpleZero.vanish_of_simple_zero hn (u := fun z => u (cpt X x1 z))
    (w := fun z => w0 (cpt X x1 z)) (s := fun k z => s k (cpt X x1 z)) hρ
    ((hdu.differentiableAt hb).continuousAt) (fun k => (hds k).differentiableAt hb)
    (hdw.differentiableAt hb) (by simpa [h0] using hw0) (fun k => by simpa [h0] using hs0 k) hdet hint
  simpa [h0] using key

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ofReal_tsum_sq_le_tsum_div_mul_tsum {ι : Type*} (a k : ι → ℝ) (hs : Summable a)
    (hk : ∀ i, 0 < k i) :
    ENNReal.ofReal ((∑' i, a i) ^ 2) ≤
      (∑' i, ENNReal.ofReal (a i ^ 2 / k i)) * ∑' i, ENNReal.ofReal (k i) := by
  have ht : Filter.Tendsto (fun s : Finset ι => ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)) Filter.atTop
      (𝓝 (ENNReal.ofReal ((∑' i, a i) ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.pow hs.hasSum 2)
  refine le_of_tendsto' ht fun s => ?_
  have h1 : (∑ i ∈ s, a i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i / Real.sqrt (k i))
      (fun i => Real.sqrt (k i))
    have e1 : ∀ i, a i / Real.sqrt (k i) * Real.sqrt (k i) = a i := fun i =>
      div_mul_cancel₀ _ (Real.sqrt_pos.2 (hk i)).ne'
    have e2 : ∀ i, Real.sqrt (k i) ^ 2 = k i := fun i => Real.sq_sqrt (hk i).le
    simp only [e1, div_pow, e2] at h0
    exact h0
  have hd : ∀ i, 0 ≤ a i ^ 2 / k i := fun i => div_nonneg (sq_nonneg _) (hk i).le
  calc ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)
      ≤ ENNReal.ofReal ((∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i) := ENNReal.ofReal_le_ofReal h1
    _ = (∑ i ∈ s, ENNReal.ofReal (a i ^ 2 / k i)) * ∑ i ∈ s, ENNReal.ofReal (k i) := by
      rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => hd i),
        ENNReal.ofReal_sum_of_nonneg fun i _ => hd i,
        ENNReal.ofReal_sum_of_nonneg fun i _ => (hk i).le]
    _ ≤ _ := mul_le_mul' (ENNReal.sum_le_tsum s) (ENNReal.sum_le_tsum s)

theorem ae_mem_OmF_muF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (OntoB.isOpen_OmF X x0).measurableSet)

theorem poincare_sqIntegrable_fundSet :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) := by
  intro hunf r X x0 hx0 la W bb κ hκ hW _ F P hF hP hPF hsum FF hFF
  obtain ⟨hκm, hκp, hκB, hκa, ⟨C, hC, hκC⟩, -⟩ := hκ
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => OntoE.phiF X P W y * ENNReal.ofReal (κ y)⁻¹ with hψ
  have hψm : Measurable ψ :=
    (OntoE.phiF_meas X hP.1.continuousOn hW.1).mul hκm.inv.ennreal_ofReal
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [hψ, OntoE.phiF_B X hP.2 hW x hx b hb, hκB x hx b hb]
  have hψd : ∀ x ∈ X.dom, ψ x = ENNReal.ofReal (‖P x‖ ^ 2 / κ x) * W x := by
    intro x hx
    simp only [hψ, OntoE.phiF_dom X P W hx]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  have hfin : ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hF
    filter_upwards [ae_mem_OmF_muF X x0] with z hz
    rw [hψd _ hz, hPF z hz, hκa z hz]
  rw [hunf r X x0 hx0 FF hFF ψ hψm hψB] at hfin
  have hpt : ∀ x ∈ X.dom, ENNReal.ofReal (‖poin X la P x‖ ^ 2) * W x ≤
      C * ∑' γ : X.Γ, ψ (lact γ.1 x) := by
    intro x hx
    have hγx : ∀ γ : X.Γ, lact γ.1 x ∈ X.dom := fun γ => OntoS.dom_lact X γ.2 hx
    have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := by
      intro γ
      rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have h1 : ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ :=
      norm_tsum_le_tsum_norm (hsum x hx)
    have h2 := ofReal_tsum_sq_le_tsum_div_mul_tsum _ (fun γ : X.Γ => κ (lact γ.1 x)) (hsum x hx)
      fun γ => (hκp _ (hγx γ)).1
    have h3 : ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 x)) ≤ C := by
      refine le_trans (ENNReal.tsum_le_tsum fun γ => ENNReal.ofReal_le_ofReal ?_) (hκC x hx)
      obtain ⟨h0, h1⟩ := hκp _ (hγx γ)
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have h4 : ∑' γ : X.Γ, ψ (lact γ.1 x) =
        (∑' γ : X.Γ, ENNReal.ofReal (‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ ^ 2 / κ (lact γ.1 x))) *
          W x := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [hψd _ (hγx γ), hn, hW.2.2 γ.1 γ.2 x hx]
    rw [h4, ← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    calc ENNReal.ofReal (‖poin X la P x‖ ^ 2)
        ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)
      _ ≤ _ := h2
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' h3 le_rfl
  unfold InFF
  calc _ ≤ ∫⁻ z in FF, C * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 fun z hz => hpt _ (hFF.2.1 hz)
    _ = C * ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        lintegral_const_mul' _ _ hC.ne
    _ < ⊤ := ENNReal.mul_lt_top hC hfin

end GlobalTheory
end
