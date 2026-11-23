module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)

theorem log_le_one_add_mul_log {a b B : ℝ} (ha : Real.exp 1 ≤ a) (hb : 0 < b) (hB : 0 ≤ B)
    (hab : b ≤ a + B) : Real.log b ≤ (1 + B) * Real.log a := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ha0 : 0 < a := by linarith
  have hla : 1 ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  have h1 : b ≤ a * (1 + B) := by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ a by linarith) hB]
  have h2 : Real.log b ≤ Real.log a + Real.log (1 + B) := by
    rw [← Real.log_mul ha0.ne' (by linarith)]
    exact Real.log_le_log hb h1
  have h3 : Real.log (1 + B) ≤ B := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + B by linarith)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hla hB]

theorem ListTailLog.proof (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement := by
  intro X _ _ _ D A R hr Om C₁
  obtain ⟨L, s, hL, hs, hs1, hYo, hden, hrc, hrEc, B, hB⟩ := hC D A R
  have hrE : ∀ x ∈ R.Yo, Real.exp 1 ≤ rSec L s x := fun x hx => by
    rw [← hYo] at hx
    have hpos : 0 < ‖s x x‖ * Real.exp (-L.φ x x) :=
      mul_pos (norm_pos_iff.2 hx) (Real.exp_pos _)
    have : logNormSec L s x ≤ 0 := Real.log_nonpos hpos.le (hs1 x)
    simp only [rSec]
    linarith
  have hC₁ : 0 ≤ max C₁ 0 * (1 + max B 0) :=
    mul_nonneg (le_max_right _ _) (by linarith [le_max_right B 0])
  obtain ⟨CE, hCE⟩ := hE D A Om L s hL hs (hYo ▸ hden) hs1 _ hC₁
  obtain ⟨CE', hCE'⟩ := hS D (max B 0) CE
  refine ⟨CE', fun th u hT => ?_⟩
  obtain ⟨hA, hpos, hmono⟩ := hM D A R.Yo R.r Om C₁ th u R.isOpen_Yo hT
  have hu : ∀ i, IsLemmaEPot A Om L s (max C₁ 0 * (1 + max B 0)) (u i) := fun i => by
    have hTi := hT i
    refine ⟨by rw [hYo]; exact hTi.u_smooth, by rw [hYo]; exact hA i,
      by rw [hYo]; exact hTi.u_nonpos, fun x hx => ?_, ?_⟩
    · rw [hYo] at hx
      have hl := log_le_one_add_mul_log (b := R.r x) (hrE x hx) (by linarith [hr x hx, Real.exp_pos 1])
        (le_max_right B 0) (by linarith [(abs_le.1 (hB x hx)).2, le_max_left B 0])
      have h0 : 0 ≤ Real.log (R.r x) :=
        Real.log_nonneg (by linarith [hr x hx, Real.add_one_le_exp (1 : ℝ)])
      have := mul_le_mul_of_nonneg_left hl (le_max_right C₁ 0)
      have := mul_le_mul_of_nonneg_right (le_max_left C₁ 0) h0
      have := hTi.le_u x hx
      nlinarith
    · rcases hTi.smooth_or_pole with h | h
      · exact Or.inl h
      · right
        rw [hYo]
        exact h
  have h2 : TailLogBound A R.Yo (rSec L s) (fun j => potForm (th j) (u j)) CE := by
    have h1 := hCE u hu
    rw [hYo] at h1
    intro R₀ hR₀
    obtain ⟨hi, hle⟩ := h1 R₀ hR₀
    obtain ⟨hi', hle'⟩ := hmono _
      (fun x => Set.indicator_nonneg (fun y hy => Real.log_nonneg
        (by linarith [hrE y hy.1, Real.add_one_le_exp (1 : ℝ)])) x)
      (fun x hx => Set.indicator_of_notMem (by exact fun h => hx h.1) _) hi
    exact ⟨hi', hle'.trans hle⟩
  exact hCE' A R.Yo R.r (rSec L s) _ R.isOpen_Yo hrc hrEc hr hrE
    (fun x hx => (hB x hx).trans (le_max_left B 0)) hpos h2

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC mInt MIntegrable logNormSec)

noncomputable section

variable {e : ℕ} {W : Type} [TopologicalSpace W] {A : FinHolAtlas e W} {L : LocPot W}
  {s : W → W → ℂ}

theorem secNorm_eq_local (hs : IsSection A L s) {x y : W} (hy : y ∈ L.U x) :
    secNorm L s y = ‖s x y‖ * Real.exp (-L.φ x y) :=
  hs.2 y x y ⟨L.mem_U y, hy⟩

theorem smooth_secNorm_sq (hL : IsPotential A L) (hs : IsSection A L s) :
    A.Smooth fun x => secNorm L s x ^ 2 := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U ((A.chart j).symm y),
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U _), ⟨hy.1, L.mem_U _⟩, ?_⟩
  set p := (A.chart j).symm y
  have h1 : ContDiffOn ℝ ∞ (fun z => ‖s p ((A.chart j).symm z)‖ ^ 2)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p) :=
    contDiff_norm_sq ℝ |>.comp_contDiffOn
      (((hs.1 p j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ)
  have h2 : ContDiffOn ℝ ∞ (fun z => Real.exp (-L.φ p ((A.chart j).symm z)) ^ 2)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p) :=
    (Real.contDiff_exp.comp_contDiffOn (hL.1 p j).neg).pow 2
  refine ((h1.mul h2).mono (fun z (hz : z ∈ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U p)) => hz.2)).congr fun z hz => ?_
  simp only [Function.comp_apply]
  rw [secNorm_eq_local hs hz.2.2, mul_pow]

theorem smooth_log_secNorm_sq_add (hL : IsPotential A L) (hs : IsSection A L s) {ε : ℝ}
    (hε : 0 < ε) : A.Smooth fun x => Real.log (secNorm L s x ^ 2 + ε) := by
  intro j
  have h1 : ContDiffOn ℝ ∞ (fun z => secNorm L s ((A.chart j).symm z) ^ 2 + ε)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) :=
    (smooth_secNorm_sq hL hs j).add contDiffOn_const
  exact h1.log fun z _ => (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'

def secZero (L : LocPot W) (s : W → W → ℂ) : Set W := {x | secNorm L s x = 0}

theorem mem_secZero_iff_local (hs : IsSection A L s) {x y : W} (hy : y ∈ L.U x) :
    y ∈ secZero L s ↔ s x y = 0 := by
  show secNorm L s y = 0 ↔ _
  rw [secNorm_eq_local hs hy, mul_eq_zero, norm_eq_zero]
  simp [(Real.exp_pos _).ne']

theorem isAnalyticSubset_secZero (hs : IsSection A L s) : A.IsAnalyticSubset (secZero L s) := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_sep_iff]
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨hy, fun _ => (mem_secZero_iff_local hs hy).1 h⟩
  · rintro ⟨hy, h⟩
    exact ⟨(mem_secZero_iff_local hs hy).2 (h 0), hy⟩

theorem interior_secZero {r : ℕ} {m : Fin r → ℕ} {Δ : Fin r → Set W} (hs : IsSection A L s)
    (hsnc : IsSNC A L s m Δ) : interior (secZero L s) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨U, hUZ, hU, hxU⟩ := mem_interior.1 hx
  obtain ⟨ψ, -, hxψ, hψL, σ, -, -, v, -, hv0, hsx⟩ := hsnc x
  have hcoord : ∀ y ∈ ψ.source, y ∈ U → ∃ i, ψ y i = 0 := by
    intro y hy hyU
    have h0 : s x y = 0 := (mem_secZero_iff_local hs (hψL hy)).1 (hUZ hyU)
    rw [hsx y hy, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (hv0 y hy)
    · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h0
      cases hσ : σ k with
      | none => simp [hσ] at hk
      | some i =>
        simp only [hσ] at hk
        exact ⟨i, eq_zero_of_pow_eq_zero hk⟩
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' U) := ψ.isOpen_inter_preimage_symm hU
  have hxO : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' U :=
    ⟨ψ.map_source hxψ, by simp [ψ.left_inv hxψ, hxU]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO _ hxO
  let w : Fin e → ℂ := fun i => if ψ x i = 0 then ((δ / 2 : ℝ) : ℂ) else ψ x i
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    by_cases h : ψ x i = 0
    · simp only [w, if_pos h, ne_eq, Complex.ofReal_eq_zero]
      linarith
    · simp only [w, if_neg h]
      exact h
  have hwb : w ∈ Metric.ball (ψ x) δ := by
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hδ]
    intro i
    by_cases h : ψ x i = 0
    · rw [Pi.sub_apply]
      simp only [w]
      rw [if_pos h, h, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [w, Pi.sub_apply, if_neg h, sub_self, norm_zero]
      exact hδ
  obtain ⟨hwt, hwU⟩ := hball hwb
  obtain ⟨i, hi⟩ := hcoord _ (ψ.map_target hwt) hwU
  rw [ψ.right_inv hwt] at hi
  exact hw0 i hi

def greenSplit (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) (x : W) : ℝ :=
  (-2) * logNormSec L s x + Real.log (secNorm L s x ^ 2 + ε)

theorem greenEp_eq_split {ε : ℝ} (hε : 0 < ε) {x : W} (hx : x ∉ secZero L s) :
    greenEp L s ε x = greenSplit L s ε x := by
  have hn : secNorm L s x ≠ 0 := hx
  have hn2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hlog : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp greenSplit
  rw [hlog, one_add_div hn2, Real.log_div (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne' hn2,
    Real.log_pow]
  push_cast
  ring

theorem mIntegrable_greenSplit [CompactSpace W] [T2Space W] {r : ℕ} {m : Fin r → ℕ}
    {Δ : Fin r → Set W} (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m Δ)
    {ε : ℝ} (hε : 0 < ε) (Φ : Fin e → LocPot W) (hΦ : ∀ i, IsPotential A (Φ i)) :
    MIntegrable A Φ (greenSplit L s ε) := by
  have h1 := ReciprocityTheory.AnForm.M.logNormIntegrable A L s m Δ hL hs hsnc Φ hΦ
  have h2 := ReciprocityTheory.AnForm.M.mIntegrableCont A Φ hΦ _
    (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth A (smooth_log_secNorm_sq_add hL hs hε))
  intro j K hK hc
  have : IntegrableOn (fun y => -2 * (logNormSec L s ((A.chart j).symm y) *
      ReciprocityTheory.AnForm.M.locDens A Φ j y) + Real.log (secNorm L s ((A.chart j).symm y) ^ 2 + ε) *
      ReciprocityTheory.AnForm.M.locDens A Φ j y) K :=
    ((h1 j K hK hc).const_mul (-2)).add (h2 j K hK hc)
  refine this.congr_fun (fun y _ => ?_) hc.measurableSet
  simp only [greenSplit]
  ring

theorem mInt_greenEp_eq_split {r : ℕ} {m : Fin r → ℕ} {Δ : Fin r → Set W} (hs : IsSection A L s)
    (hsnc : IsSNC A L s m Δ) {ε : ℝ} (hε : 0 < ε) (Φ : Fin e → LocPot W) :
    mInt A Φ (greenEp L s ε) = mInt A Φ (greenSplit L s ε) :=
  by
    unfold ReciprocityTheory.AnForm.M.mInt
    split_ifs with h
    · exact ReciprocityTheory.AnForm.M.integralWith_congr_null A h.some Φ
        (isAnalyticSubset_secZero hs) (interior_secZero hs hsnc) (fun _ hx => greenEp_eq_split hε hx)
    · rfl

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem BdWeight.proof (hP : BdPartition.Statement) (hI : IndicatorSmooth.Statement)
    (hN : NormSqSmooth.Statement) : BdWeight.Statement := by
  intro X _ _ _ D A R g hg hg0 hcoc
  obtain ⟨χ, hχs, hχ0, hχ1, hχsupp⟩ := hP D A R
  refine ⟨bdWeight R χ g, ?_, ?_, ?_⟩
  · intro j i
    have hterm : ∀ l, A.SmoothOn (bdDom R j)
        ((bdDom R l).indicator fun z => χ l z * ‖g j l z‖ ^ 2) := fun l =>
      hI D A (bdDom R j) (bdDom R l) (χ l) (fun z => ‖g j l z‖ ^ 2) (isOpen_bdDom R j)
        (isOpen_bdDom R l) (hχs l) (hχsupp l) (hN D A _ (g j l) (hg j l))
    have h := ContDiffOn.sum (s := Finset.univ) (fun l _ => hterm l i)
    convert h using 1
    ext x
    simp [bdWeight]
  · intro j y hy
    obtain ⟨l, hl⟩ : ∃ l, 0 < χ l y := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have h1 := hχ1 y
      have h2 : ∑ l, χ l y ≤ 0 := Finset.sum_nonpos fun l _ => h l
      linarith
    have hyl : y ∈ bdDom R l := hχsupp l (subset_tsupport _ (ne_of_gt hl))
    have hgne : g j l y ≠ 0 := hg0 j l y ⟨hy, hyl⟩
    unfold bdWeight
    refine Finset.sum_pos' (fun i _ => Set.indicator_nonneg
      (fun z _ => mul_nonneg (hχ0 i z) (sq_nonneg _)) y) ⟨l, Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem hyl]
    exact mul_pos hl (pow_pos (norm_pos_iff.mpr hgne) 2)
  · rintro j k y ⟨hyj, hyk⟩
    unfold bdWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hyl : y ∈ bdDom R l
    · simp only [Set.indicator_of_mem hyl]
      rw [hcoc j k l y ⟨⟨hyj, hyk⟩, hyl⟩, norm_mul, mul_pow]
      ring
    · simp [hyl]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

noncomputable section

theorem BdMetric.proof (hCC : ChartCont.Statement) (hT : BdTransition.Statement)
    (hC : BdCocycle.Statement) (hL : LogNormHolo.Statement) (hW : BdWeight.Statement) :
    BdMetric.Statement := by
  intro X _ _ _ D A R
  choose g hgH hg using fun j k => hT D A R j k
  have hO : ∀ j k, IsOpen (bdDom R j ∩ bdDom R k) := fun j k =>
    (isOpen_bdDom R j).inter (isOpen_bdDom R k)
  have hgC : ∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k) := fun j k =>
    (hCC D A _ (hO j k)).2 _ (hgH j k)
  have hcoc := hC D A R g hgC fun j k y hy => (hg j k y hy).2
  obtain ⟨w, hwS, hwP, hwE⟩ := hW D A R g hgH (fun j k y hy => (hg j k y hy).1) hcoc

  have hd : ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
      Real.log (w j y) / 2 = Real.log ‖g j k y‖ + Real.log (w k y) / 2 := by
    intro j k y hy
    have hg0 : ‖g j k y‖ ≠ 0 := norm_ne_zero_iff.mpr (hg j k y hy).1
    rw [hwE j k y hy, Real.log_mul (pow_ne_zero 2 hg0) (hwP k y hy.2).ne', Real.log_pow]
    push_cast
    ring
  refine ⟨fun j y => Real.log (w j y) / 2, fun j i => ?_, fun j k y hy => ?_, fun j k y hy => ?_⟩
  · exact ((hwS j i).log fun z hz => (hwP j _ hz.2).ne').div_const 2
  · obtain ⟨V, hV, hyV, hVW, G, hG, hGe⟩ :=
      hL D A _ (g j k) (hO j k) (hgH j k) (fun z hz => (hg j k z hz).1) y hy
    refine ⟨V, hV, hyV, G, hG, fun z hz => ?_⟩
    show Real.log (w j z) / 2 - Real.log (w k z) / 2 = (G z).re
    rw [hd j k z hz.2, ← hGe z hz.1]
    ring
  · have hgp : 0 < ‖g j k y‖ := norm_pos_iff.mpr (hg j k y hy).1
    simp only
    rw [hd j k y hy, (hg j k y hy).2, norm_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
      Real.exp_log hgp]
    field_simp

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem RegRCont.proof : RegRCont.Statement := by
  intro X _ D A R y hy
  set j := bdIdx R y
  have hyU : y ∈ bdDom R j := mem_bdDom_bdIdx R y
  let g : (Fin D → ℂ) → ℝ := fun z =>
    Real.exp 1 + R.f j z - ∑ i ∈ R.S j, Real.log (‖z i‖ ^ 2)
  have key : ∀ y' ∈ bdDom R j ∩ R.Yo,
      R.ψ j y' ∉ coordDiv (R.S j) ∧ R.r y' = g (R.ψ j y') := by
    rintro y' ⟨⟨hs, hW⟩, hY⟩
    have hinv : (R.ψ j).symm (R.ψ j y') = y' := (R.ψ j).left_inv hs
    have hnot : R.ψ j y' ∉ coordDiv (R.S j) :=
      (R.mem_Yo_iff j _ hW).1 (by rw [hinv]; exact hY)
    refine ⟨hnot, ?_⟩
    have h := R.r_chart j (R.ψ j y') ⟨hW, hnot⟩
    rw [hinv] at h
    exact h
  have hg : ContinuousAt g (R.ψ j y) := by
    have hW : R.ψ j y ∈ R.W j := hyU.2
    have hnd := (key y ⟨hyU, hy⟩).1
    have hf : ContinuousAt (R.f j) (R.ψ j y) :=
      (R.f_cont j).continuousAt ((R.isOpen_kappaOpenNeighbourhood j).mem_nhds hW)
    refine (continuousAt_const.add hf).sub ?_
    refine tendsto_finsetSum (R.S j) fun i hi => ?_
    have hzi : R.ψ j y i ≠ 0 := fun h0 => hnd ⟨i, hi, h0⟩
    have hc : ContinuousAt (fun z : Fin D → ℂ => ‖z i‖ ^ 2) (R.ψ j y) :=
      ((continuous_apply i).norm.pow 2).continuousAt
    exact hc.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hzi))
  have hO : IsOpen (bdDom R j ∩ R.Yo) := (isOpen_bdDom R j).inter R.isOpen_Yo
  have heq : g ∘ R.ψ j =ᶠ[𝓝 y] R.r :=
    Filter.eventually_of_mem (hO.mem_nhds ⟨hyU, hy⟩) fun y' h => ((key y' h).2).symm
  exact ((hg.comp ((R.ψ j).continuousAt hyU.1)).congr heq).continuousWithinAt

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open scoped ContDiff

theorem NormSqSmooth.proof : NormSqSmooth.Statement := by
  intro X _ D A U g hg j
  have h1 : ContDiffOn ℝ ∞ (g ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    ((hg j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact h2.comp_contDiffOn h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdTransition.proof (hDense : RegYoDense.Statement) (hEq : BdEqHolo.Statement)
    (hDiv : BdDivides.Statement) : BdTransition.Statement := by
  intro X _ D A R j k
  obtain ⟨u, hu, huc, hue⟩ := hDiv D A R k j
  obtain ⟨v, -, hvc, hve⟩ := hDiv D A R j k
  have hO : bdDom R k ∩ bdDom R j = bdDom R j ∩ bdDom R k := Set.inter_comm _ _
  rw [hO] at hu huc hue
  set O := bdDom R j ∩ bdDom R k with hOdef
  have hOopen : IsOpen O := (isOpen_bdDom R j).inter (isOpen_bdDom R k)

  have hYo : Set.EqOn (fun y => u y * v y) (fun _ => (1 : ℂ)) (O ∩ R.Yo) := by
    intro y ⟨hyO, hyY⟩
    have hne : bdEq R j y ≠ 0 := fun h0 => ((hEq D A R j).2 y hyO.1).1 h0 hyY
    have h1 : bdEq R j y = (u y * v y) * bdEq R j y := by
      rw [mul_assoc, ← hve y hyO, ← hue y hyO]
    have h2 : (u y * v y) * bdEq R j y = 1 * bdEq R j y := by rw [← h1, one_mul]
    exact mul_right_cancel₀ hne h2

  have hall : Set.EqOn (fun y => u y * v y) (fun _ => (1 : ℂ)) O :=
    hYo.of_subset_closure (huc.mul hvc) continuousOn_const Set.inter_subset_left
      ((hDense D A R).open_subset_closure_inter hOopen)
  refine ⟨u, hu, fun y hy => ⟨fun h0 => ?_, hue y hy⟩⟩
  have := hall hy
  simp only [h0, zero_mul] at this
  exact zero_ne_one this

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
