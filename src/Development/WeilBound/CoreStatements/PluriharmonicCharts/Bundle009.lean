module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.re_bridge

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem isNull_union {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {N N' : Set X}
    (h : IsNull A N) (h' : IsNull A N') : IsNull A (N ∪ N') := by
  intro j
  rw [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (h j) (h' j)

theorem isNull_zeros {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsNull R.A {x | eval (R.lift x x) (map (Int.castRingHom ℂ) s) = 0} := by
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι P D hP
  exact fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j

end PositivityTheory.Xgp.re_bridge

theorem PositivityTheory.Xgp.t_re_bridge : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u := by
  intro hE K _ ι _ P J D R X _ _ _ A π hπ dg br hP hdeg L Φ hL hΦ hS Am f g u N hAm hfg hN hu hI
  obtain ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ := hfg
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hAm hB
  have hsf : IsSectionOn P (Am.tensor (HermLine.sqMetric β)) f := by
    refine ⟨α, fun k => ?_, hf, hfP⟩
    show Am.a k + (β k : ℤ) = α k
    rw [← hαβ k]
    ring
  have hsg : IsSectionOn P (HermLine.sqMetric (ι := ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩
  have hQ : ∀ j, IsPotential R.A (potOf R (L j)) := fun j => isPotential_potOf R (hL j)
  rw [GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.ptsIntegral_logNormRat
      (GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hE) hP hL hAm hB hsf hsg,
    ptsIntegral_eq_mInt' hE resBridge R hP hL hAB hsf, ptsIntegral_eq_mInt' hE resBridge R hP hL hB hsg,
    ← (degreeFormulaInt A R.A π hπ dg br hdeg Φ hΦ u hI).2]
  have hlin := mIntLinear R.A _ hQ (-1) _ _ (brIntegrable R L _ g hP hL hB hsg)
    (brIntegrable R L _ f hP hL hAB hsf)
  have hnull := PositivityTheory.Xgp.re_bridge.isNull_union hN (PositivityTheory.Xgp.re_bridge.isNull_union
    (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hf hfP) (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hg hgP))
  have key := (mInt_congr_samePot D R.X R.A
    (N ∪ ({x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪
      {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}))ᶜ
    (fun j => potOf R (L j)) (fun j => (Φ j).pullback π hπ.1)
    (fun x => -1 * logNorm (HermLine.sqMetric β) g (R.lift x x) +
      logNorm (Am.tensor (HermLine.sqMetric β)) f (R.lift x x)) (u ∘ π)
    (by rwa [compl_compl]) (fun j x _ => hS j x (Set.mem_univ x))
    (fun j x _ => PositivityTheory.Xgp.re_bridge.isC2At_of_isPotential R.A
      (isPotentialPullback A R.A π hπ _ (hΦ j)) x) ?_).1
  · rw [← key, hlin]
    ring
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx
    obtain ⟨hxN, hxf, hxg⟩ := hx
    have hz := (R.mem x x (R.mem_U x)).1
    have hf0 := norm_pos_iff.mpr hxf
    have hg0 := norm_pos_iff.mpr hxg
    have hA0 := Am.pos _ hz
    have hB0 := (HermLine.sqMetric (ι := ι) β).pos _ hz
    show _ = u (π x)
    rw [← hu x hxN]
    show -1 * Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h (R.lift x x)) +
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        (Am.h (R.lift x x) * (HermLine.sqMetric β).h (R.lift x x))) =
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / Am.h (R.lift x x))
    rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
      Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
      Real.log_div hf0.ne' hg0.ne']
    ring
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.vert_deg

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem isNull_zeros {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsNull R.A {x | eval (R.lift x x) (map (Int.castRingHom ℂ) s) = 0} := by
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι P D hP
  exact fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j

theorem exists_log {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U)
    {F : X → ℂ} (hF : A.HoloOn U F) {x : X} (hx : x ∈ U) (h0 : F x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
      ∀ y ∈ V, F y ≠ 0 ∧ Real.log ‖F y‖ = (G y).re := by
  refine ⟨{y | y ∈ U ∧ F y / F x ∈ Complex.slitPlane}, ?_, ⟨hx, ?_⟩, fun y hy => hy.1,
    fun y => Complex.log (F y / F x) + ((Real.log ‖F x‖ : ℝ) : ℂ), fun j y hy => ?_, fun y hy => ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hc := GlobalTheory.CompanionTheory.Ar.PB.Proj.continuousAt_of_holoOn A hF hz.1
    filter_upwards [hU.mem_nhds hz.1, (hc.div_const (F x)).eventually_mem
      (Complex.isOpen_slitPlane.mem_nhds hz.2)] with w h1 h2
    exact ⟨h1, h2⟩
  · rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · have h1 : AnalyticAt ℂ (fun y' => F ((A.chart j).symm y') / F x) y :=
      (hF j y ⟨hy.1, hy.2.1⟩).div analyticAt_const h0
    exact (h1.clog hy.2.2).add analyticAt_const
  · have hq : F y / F x ≠ 0 := Complex.slitPlane_ne_zero hy.2
    have hy0 : F y ≠ 0 := fun h => hq (by rw [h, zero_div])
    refine ⟨hy0, ?_⟩
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hy0) (norm_ne_zero_iff.2 h0)]
    ring

theorem exists_samePot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {T : Finset ℕ} {α : ℕ → ℝ} {A B : HermLine ι}
    (h : A = B ∨ VertClose P T α A B) :
    ∃ N : Set R.X, IsNull R.A N ∧ SamePot R.A Nᶜ (potOf R A) (potOf R B) := by
  rcases h with rfl | ⟨f, g, df, dg, hf, hg, hfP, hgP, -, hn, -, -⟩
  · refine ⟨∅, fun j => by simp, fun x _ => ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun _ => 0,
      fun j => analyticOnNhd_const, fun y _ => by simp⟩⟩
  · refine ⟨{x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪
      {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}, fun j => ?_, fun x hx => ?_⟩
    · rw [Set.preimage_union, Set.inter_union_distrib_left]
      exact measure_union_null (isNull_zeros R hP hf hfP j) (isNull_zeros R hP hg hgP j)
    · simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx
      obtain ⟨V, hV, hxV, hVU, G, hG, hGe⟩ :=
        exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x f) (R.mem_U x) hx.1
      obtain ⟨V', hV', hxV', -, G', hG', hGe'⟩ :=
        exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x g) (R.mem_U x) hx.2
      refine ⟨V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun y => G y - G' y, fun j y hy => ?_, fun y hy => ?_⟩
      · exact (hG j y ⟨hy.1, hy.2.1⟩).sub (hG' j y ⟨hy.1, hy.2.2⟩)
      · have hz := R.mem x y (hVU hy.1)
        have e := congrArg Real.log (hn _ hz)
        rw [Real.log_mul (norm_ne_zero_iff.2 (hGe y hy.1).1) (B.pos _ hz.1).ne',
          Real.log_mul (norm_ne_zero_iff.2 (hGe' y hy.2).1) (A.pos _ hz.1).ne',
          (hGe y hy.1).2, (hGe' y hy.2).2] at e
        show Real.log (A.h (R.lift x y)) - Real.log (B.h (R.lift x y)) = (G y - G' y).re
        rw [Complex.sub_re]
        linarith

end PositivityTheory.Xgp.vert_deg

theorem PositivityTheory.Xgp.t_vert_deg : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L L' : Fin D → HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, L j = L' j ∨ VertClose P T α (L j) (L' j)) → ∀ (Am : HermLine ι) (s : MRing ι), IsSmoothHerm Am → IsSectionOn P Am s → ptsIntegral P (pot L) (logNorm Am s) = ptsIntegral P (pot L') (logNorm Am s) := by
  intro hE K _ ι _ P D L L' T α hP hL hL' hV Am s hAm hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  choose N hN hS using fun j => PositivityTheory.Xgp.vert_deg.exists_samePot R hP (hV j)
  rw [ptsIntegral_eq_mInt' hE resBridge R hP hL hAm hs, ptsIntegral_eq_mInt' hE resBridge R hP hL' hAm hs]
  refine (mInt_congr_samePot D R.X R.A (⋃ j, N j)ᶜ _ _ _ _ (fun j => ?_) (fun j x hx => hS j x ?_)
    (fun j x _ => PositivityTheory.Xgp.vert_deg.isC2At_of_isPotential _ (isPotential_potOf R (hL' j)) x)
    (fun _ _ => rfl)).1
  · rw [compl_compl, Set.preimage_iUnion, Set.inter_iUnion]
    exact measure_iUnion_null fun i => hN i j
  · exact fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩)
end
