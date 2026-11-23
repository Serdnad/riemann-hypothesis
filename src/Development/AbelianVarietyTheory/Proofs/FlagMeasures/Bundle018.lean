module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle003
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Covering.Besicovitch

@[expose] public section

section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt

open scoped Pointwise Classical in
open Function in
private lemma quotientEquivProdOfLE_apply_fst {W : Type} [AddCommGroup W] {C B : AddSubgroup W} (h : C ≤ B)
    (c : W ⧸ C) : ((AddSubgroup.quotientEquivProdOfLE h) c).1 = ((Quotient.out c : W) : W ⧸ B) := by
  conv_lhs => rw [← QuotientAddGroup.out_eq' c]
  rfl

open scoped Pointwise Classical in
open Function in
private lemma finsum_prod_fst_eq_card_mul {X Y : Type} [Finite Y] (g : X → ℂ) (hg : (support g).Finite) :
    ∑ᶠ p : X × Y, g p.1 = (Nat.card Y : ℂ) * ∑ᶠ x, g x := by
  have := Fintype.ofFinite Y
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ),
    finsum_eq_sum_of_support_subset (s := hg.toFinset), Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    show ∑ _y : Y, g x = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro x hx
    simpa using hx
  · intro p hp
    simpa using hp

open scoped Pointwise Classical in
open Function in
private lemma support_quotient_out_finite_of_image_finite {W : Type} [AddCommGroup W] {B : AddSubgroup W} (φ : W → ℂ)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    (support fun c : W ⧸ B => φ (Quotient.out c)).Finite := by
  refine hφ.subset fun c hc => ⟨Quotient.out c, hc, QuotientAddGroup.out_eq' c⟩

open scoped Pointwise Classical in
open Function in
private lemma finsum_quotient_out_eq_relIndex_mul_of_le {W : Type} [AddCommGroup W] {C B : AddSubgroup W} (hCB : C ≤ B)
    (hidx : C.relIndex B ≠ 0) (φ : W → ℂ) (hinv : ∀ w b : W, b ∈ B → φ (w + b) = φ w)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    ∑ᶠ c : W ⧸ C, φ (Quotient.out c) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  have hfin : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hidx
  have hcls : ∀ c : W ⧸ C, φ (Quotient.out c) =
      φ (Quotient.out ((AddSubgroup.quotientEquivProdOfLE hCB) c).1) := by
    intro c
    rw [quotientEquivProdOfLE_apply_fst]
    obtain ⟨b, hb⟩ : ∃ b ∈ B, Quotient.out ((Quotient.out c : W) : W ⧸ B) = Quotient.out c + b := by
      refine ⟨-(Quotient.out c) + Quotient.out ((Quotient.out c : W) : W ⧸ B), ?_, by abel⟩
      exact QuotientAddGroup.leftRel_apply.mp (Quotient.exact' (QuotientAddGroup.out_eq' _).symm)
    rw [hb.2, hinv _ _ hb.1]
  rw [finsum_congr hcls, finsum_comp_equiv (AddSubgroup.quotientEquivProdOfLE hCB)
      (f := fun p => φ (Quotient.out p.1)), finsum_prod_fst_eq_card_mul _ (support_quotient_out_finite_of_image_finite φ hφ)]
  rfl

open scoped Pointwise Classical in
open Function in
private lemma finsum_out_div_relIndex_eq_of_le {W : Type} [AddCommGroup W] {A B C : AddSubgroup W}
    {φ : W → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex A ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) / (C.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  obtain ⟨hBA, -, hinv, hsupp⟩ := hB
  have hidx : C.relIndex B ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA] at hC
    exact left_ne_zero_of_mul hC
  rw [finsum_quotient_out_eq_relIndex_mul_of_le hCB hidx φ hinv hsupp, ← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA,
    Nat.cast_mul, mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hidx)]


open scoped Pointwise Classical in
open Function in
theorem _root_.GlobalTheory.IdxInt.cint_eq_of_fine : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ),
    _root_.GlobalTheory.IdxInt.Fine A φ B → _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  intro W _ A B φ hB
  have h : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dite_eq_left h]
  have hB0 := h.choose_spec
  have hidx : (B ⊓ h.choose).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB0.2.1
  rw [← finsum_out_div_relIndex_eq_of_le hB0 inf_le_right hidx, finsum_out_div_relIndex_eq_of_le hB inf_le_left hidx]

end GlobalTheory.IdxInt
end

section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.UpperDensBounds

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem tendsto_const_mul_nhdsGT {k : ℝ} (hk : 0 < k) :
    Tendsto (fun r : ℝ => k * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun r : ℝ => k * r) (𝓝 0) (𝓝 (k * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hk hr

theorem ball_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    l (Metric.ball 0 (k * s)) = ENNReal.ofReal (k ^ Module.finrank ℝ V) * l (Metric.closedBall x s) := by
  rw [Measure.addHaar_ball_of_pos l 0 (mul_pos hk hs), Measure.addHaar_closedBall l x hs.le, mul_pow,
    ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem mul_div_scale (t : ℝ) (ht : 0 < t) (d : ℕ) (a b : ℝ≥0∞) :
    ENNReal.ofReal (t ^ d) * (a / (ENNReal.ofReal (t ^ d) * b)) = a / b := by
  have hp : ENNReal.ofReal (t ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hp ENNReal.ofReal_ne_top]

end GlobalTheory.UpperDensBounds


open GlobalTheory.UpperDensBounds in
theorem GlobalTheory.upperDens_bounds_of_almost_homogeneous : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  intro V _ _ _ _ _ l ν _ _ c _ hc ε η h0 h1 H x hx
  have he : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  set d := Module.finrank ℝ V
  unfold GlobalTheory.HaarDensChart.upperDens
  constructor
  ·
    set u : ℝ := (1 + ε)⁻¹ with hu
    have hu0 : 0 < u := inv_pos.mpr hp
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (u ^ d) *
        (ν (Metric.ball 0 (u * s)) / l (Metric.ball 0 (u * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (u ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT hu0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT hu0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x hu0 hs0, mul_div_scale u hu0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 + ε) * (u * s) = s := by rw [hu, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    have := hs.2
    rw [hr] at this
    exact this.trans (measure_mono Metric.ball_subset_closedBall)
  ·
    set t : ℝ := (1 + ε) / (1 - ε) with htdef
    have ht0 : 0 < t := div_pos hp he
    have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (t ^ d) *
        (ν (Metric.ball 0 (t * s)) / l (Metric.ball 0 (t * s)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (t ^ d) * c)) :=
      ENNReal.Tendsto.const_mul (hc.comp (tendsto_const_mul_nhdsGT ht0)) (Or.inr ENNReal.ofReal_ne_top)
    rw [← ht.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [(tendsto_const_mul_nhdsGT ht0).eventually (H x hx), self_mem_nhdsWithin] with s hs hs0
    have hs0 : 0 < s := hs0
    rw [ball_scale l x ht0 hs0, mul_div_scale t ht0 d]
    refine ENNReal.div_le_div_right ?_ _
    have hr : (1 - ε) * (t * s) = (1 + ε) * s := by
      rw [htdef, ← mul_assoc, mul_div_cancel₀ _ he.ne']
    refine le_trans (measure_mono (Metric.closedBall_subset_ball ?_)) hs.1
    rw [hr]; nlinarith
end
end

section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem measure_ball_eq_lintegral_upperDens : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  intro V _ _ _ _ _ l ν _ _ η C hC ρ hρ
  set U : Set V := Metric.ball (0 : V) η with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball

  have key : ∀ x ∈ U, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (Metric.closedBall x r) ≤ ((C : ℝ≥0) • l) (Metric.closedBall x r) := by
    intro x hx
    have h0 : limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) < (C : ℝ≥0∞) := hC x (mem_ball_zero_iff.1 hx)
    filter_upwards [Filter.eventually_lt_of_limsup_lt h0, self_mem_nhdsWithin] with r hr hr0
    have hpos : l (Metric.closedBall x r) ≠ 0 := (Metric.measure_closedBall_pos l x hr0).ne'
    have hfin : l (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((ENNReal.div_lt_iff (Or.inl hpos) (Or.inl hfin)).1 hr).le

  have hle : ∀ s ⊆ U, ν s ≤ ((C : ℝ≥0) • l) s := fun s hs =>
    (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le ((C : ℝ≥0) • l)
      Measure.AbsolutelyContinuous.rfl s
      (fun x hx => (Besicovitch.tendsto_filterAt ν x).frequently (key x (hs hx)).frequently)
  have hac : ν.restrict U ≪ l := by
    intro s hs
    rw [Measure.restrict_apply' hUo.measurableSet]
    refine le_antisymm ?_ (by simp)
    calc ν (s ∩ U) ≤ ((C : ℝ≥0) • l) (s ∩ U) := hle _ Set.inter_subset_right
      _ ≤ ((C : ℝ≥0) • l) s := measure_mono Set.inter_subset_left
      _ = 0 := by simp [hs]

  have hae : ∀ᵐ x ∂l, x ∈ U →
      GlobalTheory.HaarDensChart.upperDens l ν x = (ν.restrict U).rnDeriv l x := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν.restrict U) l] with x hx hxU
    have hev : (fun r : ℝ => ν.restrict U (Metric.closedBall x r) / l (Metric.closedBall x r))
        =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) := by
      obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hUo x hxU
      filter_upwards [Ioo_mem_nhdsGT εpos] with r hr
      rw [Measure.restrict_eq_self _ ((Metric.closedBall_subset_ball hr.2).trans hε)]
    show limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) = _
    exact (hx.congr' hev).limsup_eq
  have hsub : Metric.ball (0 : V) ρ ⊆ U := Metric.ball_subset_ball hρ
  calc ν (Metric.ball 0 ρ) = ν.restrict U (Metric.ball 0 ρ) :=
        (Measure.restrict_eq_self _ hsub).symm
    _ = l.withDensity ((ν.restrict U).rnDeriv l) (Metric.ball 0 ρ) := by
        rw [Measure.withDensity_rnDeriv_eq _ _ hac]
    _ = ∫⁻ x in Metric.ball 0 ρ, (ν.restrict U).rnDeriv l x ∂l :=
        withDensity_apply _ Metric.isOpen_ball.measurableSet
    _ = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
        refine setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet ?_
        filter_upwards [hae] with x hx hxρ
        exact (hx (hsub hxρ)).symm

end GlobalTheory
end

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {B : Type} [CommRing B]

def depSet (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B) (a : B) :
    Set (Fin n → B) :=
  {y | (∀ i, ip c y (x i) = g i) ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i}

theorem depSet_subset_mul (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B)
    (a b : B) : depSet c x g a ⊆ depSet c x g (b * a) := by
  rintro y ⟨h, s, hs⟩
  refine ⟨h, fun i => b * s i, ?_⟩
  rw [mul_smul, hs, Finset.smul_sum]
  simp [mul_smul]

theorem dep_isUnit_of_skew (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {u : B} (hu : c u = -u) (h0 : u ≠ 0) : IsUnit u := by
  obtain ⟨θ, e, -, he, hce⟩ := exists_trace_one c hc hω
  refine isUnit_of_mul_isUnit_left (y := e) (hf _ ?_ ?_)
  · rw [map_mul, hu, hce]; ring
  · intro h
    exact h0 (he.mul_left_eq_zero.1 h)

theorem dep_unit_or_idem (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {a : B} (h0 : a ≠ 0) :
    (∃ b, b * a = 1) ∨ ∃ b, (b * a) + c (b * a) = 1 ∧ (b * a) * c (b * a) = 0 := by
  by_cases hu : IsUnit a
  · exact Or.inl hu.exists_left_inv
  right
  have h1 : a * c a = 0 := by
    by_contra h
    exact hu (isUnit_of_mul_isUnit_left (hf _ (by rw [map_mul, hc, mul_comm]) h))
  have h2 : a + c a ≠ 0 := fun h =>
    hu (dep_isUnit_of_skew c hc hω hf (by linear_combination h) h0)
  have h3 : c (a + c a) = a + c a := by rw [map_add (f := _), hc, add_comm]
  obtain ⟨b, hb⟩ := (hf _ h3 h2).exists_left_inv
  have hb' : c b * (a + c a) = 1 := by
    have := congrArg c hb
    rwa [map_mul, h3, map_one] at this
  have hcb : c b = b := by linear_combination b * hb' - c b * hb
  refine ⟨b, ?_, ?_⟩
  · rw [map_mul, hcb]; linear_combination hb
  · rw [map_mul, hcb]; linear_combination b * b * h1

theorem dep_idem_eq (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (hf : ∀ t, c t = t → t ≠ 0 → IsUnit t) {ε ε' : B} (h1 : ε + c ε = 1) (h2 : ε * c ε = 0)
    (h1' : ε' + c ε' = 1) (h2' : ε' * c ε' = 0) : ε' = ε ∨ ε' = c ε := by
  by_cases h : ε' = ε
  · exact Or.inl h
  right
  have hu : IsUnit (ε' - ε) := dep_isUnit_of_skew c hc hω hf
    (by rw [map_sub]; linear_combination h1' - h1) (sub_ne_zero.2 h)
  have : (ε' - ε) * (ε' - c ε) = 0 := by
    linear_combination h2 - h2' + ε' * h1' - ε' * h1
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

theorem dep_kernel (c : B →+* B) (hc : ∀ u, c (c u) = u) {k n : ℕ} (x d : Fin k → Fin n → B)
    (hd : ∀ a b, ip c (x a) (d b) = if a = b then 1 else 0) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) (z : Fin n → B) (ρ s : Fin k → B) (hz : ∀ i, ip c z (x i) = 0)
    (hs : ε • z = ∑ i, s i • x i) (hA : ∀ i, c (ε * ip c z (d i)) + ε * ρ i = 0)
    (hB : ∀ l, (c ε • z + ∑ j, (c ε * ρ j) • d j) l +
      c ((c ε • z + ∑ j, (c ε * ρ j) • d j) l) = 0) : z = 0 ∧ ρ = 0 := by
  have hw : c ε • z + ∑ j, (c ε * ρ j) • d j = c ε • (z + ∑ j, ρ j • d j) := by
    simp only [smul_add, Finset.smul_sum, mul_smul]
  have hw0 : c ε • z + ∑ j, (c ε * ρ j) • d j = 0 := by
    funext l
    have := hB l
    rw [hw] at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Pi.zero_apply] at this ⊢
    set u := (z + ∑ j, ρ j • d j) l
    linear_combination c ε * this - c u * h2 + u * h2 - c ε * u * h1
  have hd' : ∀ a b, ip c (d b) (x a) = if a = b then 1 else 0 := fun a b => by
    rw [← cj_ip c hc, hd]; split_ifs <;> simp
  have hη : ∀ i, c ε * ρ i = 0 := fun i => by
    have := congrArg (fun v => ip c v (x i)) hw0
    simpa [ip_add_left, ip_sum_left, ip_smul_left, hd', hz, ip_zero_left] using this
  have hε : ∀ i, ε * ρ i = 0 := fun i => by
    have := hA i
    rw [map_mul] at this
    linear_combination ε * this - c (ip c z (d i)) * h2 + ρ i * h2 - ε * ρ i * h1
  have hs0 : ∀ i, s i = 0 := fun i => by
    have h3 := hA i
    rw [hε, add_zero] at h3
    have h4 := congrArg c h3
    rw [hc, map_zero] at h4
    have := congrArg (fun v => ip c v (d i)) hs
    simpa [ip_sum_left, ip_smul_left, hd, h4] using this.symm
  refine ⟨?_, funext fun i => ?_⟩
  · simp only [hη, zero_smul, Finset.sum_const_zero, add_zero] at hw0
    simp only [hs0, zero_smul, Finset.sum_const_zero] at hs
    rw [← one_smul B z, ← h1, add_smul, hs, hw0, add_zero]
  · have := hε i
    have := hη i
    simp only [Pi.zero_apply]
    linear_combination hε i + hη i - ρ i * h1

theorem ncard_depSet_idem_le [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B}
    (hω : IsUnit (ω - c ω)) {q : ℕ} (hq : Fintype.card B = q ^ 2) {k n : ℕ}
    (x : Fin k → Fin n → B) (hx : Prim c x) (g : Fin k → B) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) : (depSet c x g ε).ncard ≤ q ^ n := by
  obtain ⟨d, hd⟩ := hx
  have hK : Nat.card {t : B // c t = t} = q := by
    have := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc (fun a y => by simp)).1
    rw [Nat.card_eq_fintype_card (α := B), hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  let F : depSet c x g ε × (Fin k → B) → (Fin k → B) × (Fin n → {t : B // c t = t}) :=
    fun p => (fun i => c (ε * ip c p.1.1 (d i)) + ε * p.2 i,
      fun l => ⟨(c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l +
        c ((c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l), by rw [map_add (f := _), hc, add_comm]⟩)
  have hF : Function.Injective F := by
    rintro ⟨⟨y, hy, s, hs⟩, r⟩ ⟨⟨y', hy', s', hs'⟩, r'⟩ h
    obtain ⟨hA, hB⟩ := Prod.ext_iff.1 h
    have key := dep_kernel c hc x d hd h1 h2 (y - y') (r - r') (s - s')
      (fun i => by rw [ip_sub_left, hy, hy', sub_self])
      (by simp only [smul_sub, hs, hs', Pi.sub_apply, sub_smul, Finset.sum_sub_distrib])
      (fun i => by
        have := congrFun hA i
        simp only [F, map_mul] at this
        simp only [ip_sub_left, map_mul, map_sub, Pi.sub_apply]
        linear_combination this)
      (fun l => by
        have := congrArg Subtype.val (congrFun hB l)
        simp only [F, Pi.add_apply, map_add (f := _)] at this
        simp only [smul_sub, mul_sub, sub_smul, Finset.sum_sub_distrib, Pi.add_apply,
          Pi.sub_apply, map_add, map_sub]
        linear_combination this)
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 key.1)) (sub_eq_zero.1 key.2)
  have h3 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun (α := Fin n), hK,
    mul_comm] at h3
  have h4 : 0 < Nat.card (Fin k → B) := Nat.card_pos
  simpa using Nat.le_of_mul_le_mul_left h3 h4

theorem ncard_dependent_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) →
    ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n →
    ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B),
    Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
      ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  intro B _ _ c hc ω hω hf q hq2 hq k n hkn x hx g
  by_cases hex : ∃ ε : B, ε + c ε = 1 ∧ ε * c ε = 0
  · obtain ⟨ε, h1, h2⟩ := hex
    have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        depSet c x g ε ∪ depSet c x g (c ε) := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb1, hb2⟩
      · left
        have := depSet_subset_mul c x g a (ε * b) hy'
        rwa [mul_assoc, hb, mul_one] at this
      · have := depSet_subset_mul c x g a b hy'
        rcases dep_idem_eq c hc hω hf h1 h2 hb1 hb2 with h | h
        · left; rwa [h] at this
        · right; rwa [h] at this
    have hA := ncard_depSet_idem_le c hc hω hq x hx g h1 h2
    have hB := ncard_depSet_idem_le c hc hω hq x hx g (ε := c ε) (by rw [hc, add_comm, h1])
      (by rw [hc, mul_comm, h2])
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    omega
  · have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        (fun s : Fin k → B => ∑ i, s i • x i) '' Set.univ := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb⟩
      · obtain ⟨-, s, hs⟩ := depSet_subset_mul c x g a b hy'
        rw [hb, one_smul] at hs
        exact ⟨s, trivial, hs.symm⟩
      · exact absurd ⟨_, hb⟩ hex
    have h1 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (Set.ncard_image_le (Set.toFinite _))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, hq, Fintype.card_fin,
      ← pow_mul] at h1
    have h2 : q ^ (2 * k) ≤ q ^ n := Nat.pow_le_pow_right (by omega) hkn
    omega

end GlobalTheory.GramCount
end

section


theorem _root_.GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ), (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) → (∀ i, Continuous (d i)) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_partials | exact GlobalTheory.hasFDerivAt_of_continuous_partials | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_partials <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.measure_eq_of_lintegral_smooth_eq' : ∀ (N : ℕ) (m₁ m₂ : Measure (Fin N → ℝ)) [IsFiniteMeasureOnCompacts m₂], (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) → ∫⁻ x, ENNReal.ofReal (φ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (φ x) ∂m₂) → m₁ = m₂ := by
  first | exact @GlobalTheory.measure_eq_of_lintegral_smooth_eq | exact GlobalTheory.measure_eq_of_lintegral_smooth_eq | (intros; apply GlobalTheory.measure_eq_of_lintegral_smooth_eq <;> assumption)
end
