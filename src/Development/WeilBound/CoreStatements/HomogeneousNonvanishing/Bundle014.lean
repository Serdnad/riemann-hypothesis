module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FderivAffCoordZero
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle010
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle008
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NonvanishingDense
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle012
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle009
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle013
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SmoothContinuousAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

namespace RC

open HolomorphicMinorCharts

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem section_pull {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {π : Y → X} (h : HoloMap B A π) {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) : IsSection B (L.pullback π h.1) fun x y => s (π x) (π y) :=
  ⟨fun x => holo_comp_map h (hs.1 (π x)), fun x x' y hy => hs.2 (π x) (π x') (π y) hy⟩

theorem nrm_mul (L L' : LocPot X) (s s' : X → X → ℂ) (x y : X) :
    ‖s x y * s' x y‖ * Real.exp (-(L + L').φ x y) =
      (‖s x y‖ * Real.exp (-L.φ x y)) * (‖s' x y‖ * Real.exp (-L'.φ x y)) := by
  rw [add_φ, norm_mul, neg_add, Real.exp_add]
  ring

theorem section_mul {A : FinHolAtlas e X} {L L' : LocPot X} {s s' : X → X → ℂ} (hs : IsSection A L s)
    (hs' : IsSection A L' s') : IsSection A (L + L') fun x y => s x y * s' x y := by
  refine ⟨fun x j w hw => (hs.1 x j w ⟨hw.1, hw.2.1⟩).mul (hs'.1 x j w ⟨hw.1, hw.2.2⟩), fun x x' y hy => ?_⟩
  rw [nrm_mul, nrm_mul, hs.2 x x' y ⟨hy.1.1, hy.2.1⟩, hs'.2 x x' y ⟨hy.1.2, hy.2.2⟩]

theorem log_mul_le {L L' : LocPot X} {s s' : X → X → ℂ} (h : ∀ y, logNormSec L s y ≤ 0)
    (h' : ∀ y, logNormSec L' s' y ≤ 0) (y : X) : logNormSec (L + L') (fun x y => s x y * s' x y) y ≤ 0 := by
  have h1 := h y
  have h2 := h' y
  unfold logNormSec at *
  rw [Real.log_nonpos_iff (by positivity)] at *
  rw [nrm_mul]
  exact mul_le_one₀ h1 (by positivity) h2

theorem log_mul_eq {L L' : LocPot X} {s s' : X → X → ℂ} {y : X} (hy : y ∉ bdry fun x y => s x y * s' x y) :
    logNormSec (L + L') (fun x y => s x y * s' x y) y = logNormSec L s y + logNormSec L' s' y := by
  have h1 : s y y * s' y y ≠ 0 := hy
  unfold logNormSec
  rw [nrm_mul, Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (left_ne_zero_of_mul h1)) (Real.exp_pos _).ne')
    (mul_ne_zero (norm_ne_zero_iff.mpr (right_ne_zero_of_mul h1)) (Real.exp_pos _).ne')]

theorem exists_scale [CompactSpace X] {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L)
    (hs : IsSection A L s) : ∃ L' : LocPot X, IsPotential A L' ∧ IsSection A L' s ∧ ∀ y, logNormSec L' s y ≤ 0 := by
  have hc : Continuous fun y => ‖s y y‖ * Real.exp (-L.φ y y) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    refine ContinuousAt.congr (((holo_continuousAt (hs.1 x) (L.mem_U x)).norm).mul
      (CSnc.smooth_continuousAt (L.isOpen_U x) (hL.1 x) (L.mem_U x)).neg.rexp) ?_
    filter_upwards [(L.isOpen_U x).mem_nhds (L.mem_U x)] with y hy
    exact hs.2 x y y ⟨hy, L.mem_U y⟩
  obtain ⟨M, hM⟩ := (isCompact_range hc).bddAbove
  have hsm : A.Smooth fun _ => M := fun j => contDiffOn_const
  have key : ∀ x y, ‖s x y‖ * Real.exp (-(L + LocPot.ofFun fun _ => M).φ x y) =
      ‖s x y‖ * Real.exp (-L.φ x y) * Real.exp (-M) := fun x y => by
    rw [add_φ, neg_add, Real.exp_add, mul_assoc]
    rfl
  refine ⟨L + LocPot.ofFun fun _ => M, isPotentialAdd A _ _ hL (isPotential_ofFun A _ hsm),
    ⟨fun x => holo_mono (hs.1 x) fun y hy => hy.1, fun x x' y hy => ?_⟩, fun y => ?_⟩
  · rw [key, key, hs.2 x x' y ⟨hy.1.1, hy.2.1⟩]
  · unfold logNormSec
    rw [Real.log_nonpos_iff (by positivity), key, Real.exp_neg M, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    have h1 : ‖s y y‖ * Real.exp (-L.φ y y) ≤ M := hM ⟨y, rfl⟩
    have := Real.add_one_le_exp M
    linarith

theorem exists_line {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (b : K → ℤ) :
    ∃ L : HermLine ι, IsSmoothHerm L ∧ L.a = b := by
  refine ⟨HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) b, ?_, rfl⟩
  change ContDiffOn ℝ _ (fun z => ∏ k, (fsMetric (ι := ι k)).ρ (GP.blk (ι := ι) k z) ^ b k) _
  refine contDiffOn_prod fun k _ z hz => ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (fsMetric (ι := ι k)).ρ (GP.blk (ι := ι) k z)) z :=
    ContDiffAt.comp (g := (fsMetric (ι := ι k)).ρ) z (GP.contDiffAt_fs (GP.blk_ne hz k))
      ((GP.blk (ι := ι) k).contDiff.restrict_scalars ℝ).contDiffAt
  have h2 := ((fsMetric (ι := ι k)).pos _ (GP.blk_ne hz k)).ne'
  rcases b k with n | n
  · simpa using h1.pow n
  · simp only [zpow_negSucc]
    exact (h1.pow (n + 1)).inv (pow_ne_zero _ h2)

theorem one (hPull : PullbackStatement) {D : ℕ} [CompactSpace Y] [T2Space Y] {B : FinHolAtlas D Y} {Θ : LocPot Y}
    (hΘ : IsPotential B Θ) (hΘ' : IsPosPot B Θ) {σ : Type} (S : AnSys D σ) {π : Y → S.X} (h : HoloMap B S.A π)
    {n : ℕ} {m : Fin n → ℕ} {W : Fin n → Set Y}
    (hsnc : IsSNC B (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) m W) {L : LocPot Y} {s : Y → Y → ℂ}
    (hb : bdry (fun x y => S.s (π x) (π y)) ⊆ bdry s)
    (hr : ∀ y, y ∉ bdry s → rW (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) y ≤ rW L s y) (a : σ) :
    ∃ C' t' : ℝ, 0 < t' ∧ ∀ C₅ C t₀ : ℝ, 0 ≤ C₅ → S.C₅ ≤ C₅ → |C'| ≤ C → 0 < t₀ → t₀ ≤ t' → t₀ ≤ Real.exp (-1) →
      IsSingWeight B L s ((S.th a).pullback π h.1) (S.ph a ∘ π) C₅ ∧
      IsRegFamily B Θ L s ((S.th a).pullback π h.1) (S.ph a ∘ π) (fun t => S.phT a t ∘ π) C t₀ ∧
      IsRegFamilyC2 B s (S.ph a ∘ π) (fun t => S.phT a t ∘ π) := by
  obtain ⟨C', t', h1, h2, h3⟩ := hPull S.A B π h S.Θ S.L Θ S.s S.m S.W m W S.potΘ S.posΘ hΘ hΘ' S.potL S.sec S.snc
    S.norm_le hsnc (S.th a) (S.ph a) (S.phT a) S.C₅ S.C S.t₀ (S.sing a) (S.reg a) (S.c2 a)
  have hn : ∀ y, logNormSec (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) y ≤ 0 := fun y => S.norm_le (π y)
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.singular_weight_monotone_regularization D Y B Θ _ _ n m W (isPotentialPullback S.A B π h _ S.potL)
    (section_pull h S.sec) hsnc hn hΘ hΘ'
  refine ⟨C', t', h2.1, fun C₅ C t₀ a1 a2 a3 a4 a5 a6 => ?_⟩
  exact r_enlarge D Y B Θ _ L _ s _ _ _ C₅ C t₀ a1 ((abs_nonneg _).trans a3) a6 hn hb hr (m1 _ _ _ _ a2 h1)
    (m2 _ _ _ _ _ _ _ a3 a4 a5 a6 h2 h1.1) h3

end RC

open RC HolomorphicMinorCharts in
theorem r_combine : PullbackStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (Amp : HermLine ι) (β : MRing ι) (b : K → ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ) (π₁ : R.X → S₁.X) (π₂ : R.X → S₂.X) (h₁ : HoloMap R.A S₁.A π₁) (h₂ : HoloMap R.A S₂.A π₂), IsPotential R.A (potOf R Amp) → IsPosPot R.A (potOf R Amp) → IsMultiHomog β b → β ∉ P → (∀ z ∈ mcPts P, evC z β = 0 → z ∈ mcPts J) → (∀ x, π₁ x ∈ bdry S₁.s → evC (R.lift x x) β = 0) → (∀ x, π₂ x ∈ bdry S₂.s → evC (R.lift x x) β = 0) → ∃ (L : LocPot R.X) (s : R.X → R.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (C₅ C t₀ : ℝ), IsPotential R.A L ∧ IsSection R.A L s ∧ IsSNC R.A L s m W ∧ (∀ y, logNormSec L s y ≤ 0) ∧ (∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0) ∧ t₀ ≤ S₁.t₀ ∧ t₀ ≤ S₂.t₀ ∧ (∀ a, IsSingWeight R.A L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁) C t₀ ∧ IsRegFamilyC2 R.A s (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁)) ∧ ∀ a, IsSingWeight R.A L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) C t₀ ∧ IsRegFamilyC2 R.A s (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) := by
  intro hPull K _ ι _ P J D R Amp β b σ _ S₁ S₂ π₁ π₂ h₁ h₂ hΘ hΘ' hβ hβP hβJ hb₁ hb₂
  obtain ⟨n₀, m₀, W₀, hsnc₀⟩ := R.snc β b hβP hβ hβJ
  have hsnc : ∀ (L : LocPot R.X) (s : R.X → R.X → ℂ), IsPotential R.A L → IsSection R.A L s →
      (∀ x ∈ bdry s, evC (R.lift x x) β = 0) → ∃ (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set R.X), IsSNC R.A L s m W :=
    fun L s hL hs hb => r_snc D R.X R.A _ _ n₀ m₀ W₀ L s hsnc₀ hL hs hb
      fun x x' y hy => eval_ne_so hβ (R.compat x x' y hy)
  obtain ⟨Lb, hLb, hLa⟩ := exists_line (ι := ι) fun k => (b k : ℤ)
  obtain ⟨L₃, p₃, s₃, l₃⟩ := exists_scale (isPotential_potOf R hLb)
    (isSection_lift R (A := Lb) (s := β) ⟨b, fun k => congrFun hLa k, hβ, hβP⟩)
  have p₁ := isPotentialPullback S₁.A R.A π₁ h₁ _ S₁.potL
  have p₂ := isPotentialPullback S₂.A R.A π₂ h₂ _ S₂.potL
  have s₁ := section_pull h₁ S₁.sec
  have s₂ := section_pull h₂ S₂.sec
  have l₁ : ∀ y, logNormSec (S₁.L.pullback π₁ h₁.1) (fun x y => S₁.s (π₁ x) (π₁ y)) y ≤ 0 :=
    fun y => S₁.norm_le (π₁ y)
  have l₂ : ∀ y, logNormSec (S₂.L.pullback π₂ h₂.1) (fun x y => S₂.s (π₂ x) (π₂ y)) y ≤ 0 :=
    fun y => S₂.norm_le (π₂ y)
  obtain ⟨n₁, m₁, W₁, c₁⟩ := hsnc _ _ p₁ s₁ hb₁
  obtain ⟨n₂, m₂, W₂, c₂⟩ := hsnc _ _ p₂ s₂ hb₂
  have p := isPotentialAdd R.A _ _ (isPotentialAdd R.A _ _ p₁ p₂) p₃
  have sec := section_mul (section_mul s₁ s₂) s₃
  set L := S₁.L.pullback π₁ h₁.1 + S₂.L.pullback π₂ h₂.1 + L₃ with hL
  set s : R.X → R.X → ℂ := fun x y => S₁.s (π₁ x) (π₁ y) * S₂.s (π₂ x) (π₂ y) *
    eval (R.lift x y) (map (Int.castRingHom ℂ) β) with hs
  have hbd : ∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0 := fun x => by
    refine ⟨fun h => ?_, fun h => mul_eq_zero_of_right _ h⟩
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact hb₁ x h
      · exact hb₂ x h
    · exact h
  obtain ⟨n, m, W, c⟩ := hsnc L s p sec fun x => (hbd x).mp
  have hlog : ∀ y, y ∉ bdry s → logNormSec L s y =
      logNormSec (S₁.L.pullback π₁ h₁.1) (fun x y => S₁.s (π₁ x) (π₁ y)) y +
      logNormSec (S₂.L.pullback π₂ h₂.1) (fun x y => S₂.s (π₂ x) (π₂ y)) y +
      logNormSec L₃ (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) β)) y := fun y hy => by
    have h0 : S₁.s (π₁ y) (π₁ y) * S₂.s (π₂ y) (π₂ y) * eval (R.lift y y) (map (Int.castRingHom ℂ) β) ≠ 0 := hy
    rw [← log_mul_eq (s := fun x y => S₁.s (π₁ x) (π₁ y)) (s' := fun x y => S₂.s (π₂ x) (π₂ y))
      (left_ne_zero_of_mul h0)]
    exact log_mul_eq (s := fun x y => S₁.s (π₁ x) (π₁ y) * S₂.s (π₂ x) (π₂ y))
      (s' := fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) β)) hy
  choose C₁ t₁ ht₁ H₁ using one hPull hΘ hΘ' S₁ h₁ c₁ (L := L) (s := s) (fun x hx => (hbd x).mpr (hb₁ x hx))
    fun y hy => by
      have := hlog y hy
      have := l₂ y
      have := l₃ y
      unfold rW
      linarith
  choose C₂ t₂ ht₂ H₂ using one hPull hΘ hΘ' S₂ h₂ c₂ (L := L) (s := s) (fun x hx => (hbd x).mpr (hb₂ x hx))
    fun y hy => by
      have := hlog y hy
      have := l₁ y
      have := l₃ y
      unfold rW
      linarith
  obtain ⟨δ, hδ, hδe, hδ₁, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.exp (-1) ∧ (∀ a, δ ≤ t₁ a) ∧ ∀ a, δ ≤ t₂ a := by
    have e0 : ∀ t : ℝ, 0 < t → ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ t := fun t ht => by
      filter_upwards [Ioc_mem_nhdsGT ht] with δ h using h.2
    exact ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)).and ((e0 _ (Real.exp_pos _)).and
      ((eventually_all.mpr fun a => e0 _ (ht₁ a)).and (eventually_all.mpr fun a => e0 _ (ht₂ a))))).exists
  have hpos : σ → 0 < min (min S₁.t₀ S₂.t₀) δ := fun a => lt_min (lt_min (S₁.reg a).1 (S₂.reg a).1) hδ
  have n1 : 0 ≤ ∑ a, |C₁ a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n2 : 0 ≤ ∑ a, |C₂ a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨L, s, n, m, W, max (max S₁.C₅ S₂.C₅) 0, ∑ a, |C₁ a| + ∑ a, |C₂ a|, min (min S₁.t₀ S₂.t₀) δ, p, sec, c,
    log_mul_le (log_mul_le l₁ l₂) l₃, hbd, (min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _), fun a => H₁ a _ _ _ (le_max_right _ _)
      ((le_max_left _ _).trans (le_max_left _ _)) ?_ (hpos a) ((min_le_right _ _).trans (hδ₁ a))
      ((min_le_right _ _).trans hδe), fun a => H₂ a _ _ _ (le_max_right _ _)
      ((le_max_right _ _).trans (le_max_left _ _)) ?_ (hpos a) ((min_le_right _ _).trans (hδ₂ a))
      ((min_le_right _ _).trans hδe)⟩
  · have := Finset.single_le_sum (f := fun a => |C₁ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  · have := Finset.single_le_sum (f := fun a => |C₂ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem c_arint : SheetIndepStatement → PtsIndepStatement → GoodProjExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → arInt P s (conjLine A) (fun j => conjLine (L j)) = arInt P s A L := by
  intro hS hP hG K _ ι _ P e L A s hV hL hA hs
  have hex := hG K ι P e hV
  have hgood : IsGoodProj P hex.choose := hex.choose_spec
  let Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] Fin (e + 1) → ℂ :=
    { toFun := fun w i => starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ (w c)) i)
      map_add' := by
        intro a b
        have h : (fun c => starRingEnd ℂ ((a + b) c)) =
            (fun c => starRingEnd ℂ (a c)) + (fun c => starRingEnd ℂ (b c)) := by
          funext c
          simp
        funext i
        show starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ ((a + b) c)) i) = _
        rw [h, map_add (f := _)]
        simp
      map_smul' := by
        intro r a
        have h : (fun c => starRingEnd ℂ ((r • a) c)) =
            starRingEnd ℂ r • (fun c => starRingEnd ℂ (a c)) := by
          funext c
          simp
        funext i
        show starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ ((r • a) c)) i) = _
        rw [h, map_smul]
        simp }
  have hΨ' : ∀ (w : ((k : K) → ι k) → ℂ) (i : Fin (e + 1)),
      Ψ' w i = starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ (w c)) i) := fun _ _ => rfl
  obtain ⟨hgood', heq⟩ := c_ptsat hS K ι P e hex.choose Ψ' L A s hV hgood hΨ' hL hA hs
  have hcs : ∀ B : HermLine ι, IsSmoothHerm B → IsSmoothHerm (conjLine B) := by
    intro B hB
    have hmaps : Set.MapsTo (conjPt : ((k : K) × ι k → ℂ) → (k : K) × ι k → ℂ)
        {z : (k : K) × ι k → ℂ | ∀ (k : K), ∃ (i : ι k), z ⟨k, i⟩ ≠ 0}
        {z : (k : K) × ι k → ℂ | ∀ (k : K), ∃ (i : ι k), z ⟨k, i⟩ ≠ 0} := by
      intro z hz k
      obtain ⟨i, hi⟩ := hz k
      exact ⟨i, by simpa [conjPt] using hi⟩
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞)) (conjPt : ((k : K) × ι k → ℂ) → (k : K) × ι k → ℂ) := by
      refine contDiff_pi.2 fun p => ?_
      have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : (k : K) × ι k → ℂ => z p) := contDiff_apply ℝ (fun _ => ℂ) p
      have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℂ => starRingEnd ℂ x) := by
        have h3 : (fun x : ℂ => starRingEnd ℂ x) = (Complex.conjCLE : ℂ → ℂ) := by
          funext x
          simp
        rw [h3]
        exact Complex.conjCLE.contDiff
      exact h2.comp h1
    have hB' : ContDiffOn ℝ (↑(⊤ : ℕ∞)) B.h
        {z : (k : K) × ι k → ℂ | ∀ (k : K), ∃ (i : ι k), z ⟨k, i⟩ ≠ 0} := hB
    exact hB'.comp hc.contDiffOn hmaps
  have hLc : ∀ j, IsSmoothHerm (conjLine (L j)) := fun j => hcs _ (hL j)
  have hAc : IsSmoothHerm (conjLine A) := hcs _ hA
  have hsc : IsSectionOn P (conjLine A) s := by
    obtain ⟨a, ha, h2⟩ := hs
    exact ⟨a, ha, h2⟩
  have hind := hP K ι P e hex.choose Ψ' (fun j => conjLine (L j)) (conjLine A) s hV hgood hgood'
    hLc hAc hsc
  unfold arInt ptsIntegral
  rw [dite_eq_left hex, dite_eq_left hex]
  exact hind.trans heq

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem cm_type_label_twist_permutation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (g : HostAut H), ∃ π : CMType H ≃ CMType H, (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) ∧ ∀ s, labelEmb c (Sum.map π π s) = (labelEmb c s).comp g.s.toRingHom := by
  intro E _ _ _ H l c g
  let F : HostAut H → CMType H → CMType H := fun g τ =>
    ⟨τ.1.comp g.σ.toRingHom, by
      show τ.1 (g.σ (H.rt : E)) = _
      rw [g.fix]
      exact τ.2⟩
  refine ⟨⟨F g, F g.symm, fun τ => ?_, fun τ => ?_⟩, fun _ => rfl, ?_⟩
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ (g.σ.symm x)) = τ.1 x
    rw [RingEquiv.apply_symm_apply]
  · refine Subtype.ext (RingHom.ext fun x => ?_)
    show τ.1 (g.σ.symm (g.σ x)) = τ.1 x
    rw [RingEquiv.symm_apply_apply]
  · rintro (τ | τ)
    · exact RingHom.ext fun x => Subtype.ext rfl
    · refine RingHom.ext fun x => Subtype.ext ?_
      show τ.1 ((g.s (H.bar x) : 𝓞 E) : E) = τ.1 ((H.bar (g.s x) : 𝓞 E) : E)
      rw [g.s_bar]

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

open HolomorphicMinorCharts in
theorem isClosed_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnLogRes P J e) : IsClosed {q : R.X × ((Σ k, ι k) → ℂ) | Minors (R.lift q.1 q.1) q.2} :=
  isClosed_minors (U := R.U) (lam := R.lift) (V := fun _ : (Σ k, ι k) → ℂ => Set.univ)
    (mu := fun _ w => w) (fun x => ⟨R.isOpen_U x, R.mem_U x⟩)
    (fun x p => holo_continuousAt (R.holo x p) (R.mem_U x)) R.compat (fun _ => ⟨isOpen_univ, trivial⟩)
    (fun _ p => (continuous_apply p).continuousAt) (fun _ _ w _ => so_refl w)

open HolomorphicMinorCharts in
theorem dense_nonvan {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnLogRes P J e) (hP : IsArithVar P (e + 1)) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) (hgP : g ∉ P) :
    Dense {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro N hN ⟨x₀, hx₀⟩
  obtain ⟨x, hxN, hxJ⟩ : ∃ x ∈ N, R.lift x x ∉ mcPts J := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := R.A.cover x₀
    have h1 := ((R.A.chart j).isOpen_inter_preimage_symm hN).measure_pos MeasureTheory.volume
      ⟨R.A.chart j x₀, (R.A.chart j).map_source hj, by rwa [Set.mem_preimage, (R.A.chart j).left_inv hj]⟩
    exact h1.ne' (MeasureTheory.measure_mono_null (fun w hw => Set.mem_inter hw.1 (h _ hw.2)) (R.null j))
  have hc := isClosedMap_snd_of_compactSpace _
    ((isClosed_res R).inter (hN.isClosed_compl.preimage continuous_fst))
  have hz := R.mem x x (R.mem_U x)
  have h1 := nonvanishing_dense K ι P (e + 1) g hP hgP hz
  obtain ⟨z, hz1, hz2, hz3⟩ := mem_closure_iff.mp h1 _ hc.isOpen_compl (by
    rintro ⟨⟨x', w⟩, ⟨h2, h3⟩, h4⟩
    obtain rfl : w = R.lift x x := h4
    obtain rfl := R.inj x x' hxJ (so_symm (so_of_minors h2 (R.mem _ _ (R.mem_U _)).1 hz.1))
    exact h3 hxN)
  obtain ⟨x', hx'⟩ := r_onto K ι P J e R hP z hz2
  refine ⟨x', ?_, fun h => hz3 ((eval_ne_so hg hx').mp h)⟩
  by_contra h
  exact hz1 ⟨(x', z), ⟨minors_of_so hx', h⟩, rfl⟩

open HolomorphicMinorCharts in
theorem r_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (P J : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D σ) (Re : Realis S (imageZ v₁ P)) (R : AnLogRes P J D), IsBlockMap κ₁ v₁ → IsArithVar P (D + 1) → AlgOver Re → ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π), (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧ (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' → SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) = Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) ∧ ∃ (β : MRing ι) (b : K → ℕ), IsMultiHomog β b ∧ β ∉ P ∧ ∀ x, π x ∈ bdry S.s → evC (R.lift x x) β = 0 := by
  intro K _ ι _ K₁ _ ι₁ _ κ₁ v₁ P J D σ S Re R hv₁ hP hA
  obtain ⟨K₀, _, ι₀, _, κ, v, U, lam, β₀, b₀, hv, hE, hπ₁, hβ, hβP, hβ0⟩ := hA
  obtain ⟨-, hsm, hm₁, hev₁⟩ := j_pull K₁ ι₁ K ι κ₁ v₁ hv₁
  obtain ⟨-, -, hm₀, hev₀⟩ := j_pull K₀ ι₀ K₁ ι₁ κ v hv
  have hmem : ∀ x, ∀ y ∈ R.U x, (fun p => R.lift x y (v₁ p)) ∈ mcPts (imageZ v₁ P) := fun x y hy =>
    hm₁ P _ (R.mem x y hy)
  obtain ⟨π, hπ, hπo⟩ := r_holmap K₀ ι₀ _ D D S.X R.X S.A R.A U lam R.U (fun x y p => R.lift x y (v₁ (v p))) hE
    (fun x => ⟨R.isOpen_U x, R.mem_U x⟩) (fun x p => R.holo x _) (fun x y hy => hm₀ _ _ (hmem x y hy))
    (fun x x' y hy => so_pull hv (so_pull hv₁ (R.compat x x' y hy)))
  have c1 : ∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁ :=
    fun x x₁ h => hE.inj _ _ (so_trans (hπo x) (so_symm (so_trans (hπ₁ x₁) (so_pull hv h))))
  choose ρ hρ using fun x => r_onto K₁ ι₁ _ Re.J D Re.R Re.arith _ (hmem x x (R.mem_U x))
  refine ⟨π, hπ, c1, fun a ref' hr => ?_, fun a t ht ht' x => ?_, ?_⟩
  · obtain ⟨f, af, hfJ, hfP, hf⟩ := exists_homog_not_mem Re.R.homog Re.R.nondeg
    obtain ⟨bf, hbf⟩ := homog_rename hv₁ hf
    have hO := isOpen_nonvan R hbf
    refine r_pluri D R.X R.A _ _ _ (isPotential_potOf R (hsm _ _ hr (Re.ref_smooth a)))
      (isPotentialPullback S.A R.A π hπ _ (S.sing a).1) hO (dense_nonvan R hP hbf hfP) fun x hx => ?_
    set O := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) (rename v₁ f)) ≠ 0} with hOd
    have hoff : ∀ y ∈ O, Re.R.lift (ρ y) (ρ y) ∉ mcPts Re.J := fun y hy h =>
      hy ((hev₁ (R.lift y y) f).trans ((eval_ne_so hf (hρ y)).mp (h.2 f hfJ)))
    have hcl := isClosed_minors (U := Re.R.U) (lam := Re.R.lift) (V := R.U) (mu := fun x y p => R.lift x y (v₁ p))
      (fun x => ⟨Re.R.isOpen_U x, Re.R.mem_U x⟩) (fun x p => holo_continuousAt (Re.R.holo x p) (Re.R.mem_U x))
      Re.R.compat (fun x => ⟨R.isOpen_U x, R.mem_U x⟩) (fun x p => holo_continuousAt (R.holo x _) (R.mem_U x))
      (fun x x' y hy => so_pull hv₁ (R.compat x x' y hy))
    have hcont : ∀ y ∈ O, ContinuousAt ρ y := fun y hy =>
      continuousAt_of_closed_rel hcl (fun y => minors_of_so (hρ y)) fun x' hx' =>
        (Re.R.inj _ _ (hoff y hy) (so_trans (hρ y) (so_symm
          (so_of_minors hx' (Re.R.mem _ _ (Re.R.mem_U _)).1 (hmem y y (R.mem_U y)).1)))).symm
    have hso : ∀ x' x₁ y, y ∈ R.U x' → ρ y ∈ Re.R.U x₁ →
        SameOrbit (Re.R.lift x₁ (ρ y)) fun p => R.lift x' y (v₁ p) := fun x' x₁ y h1 h2 =>
      so_trans (Re.R.compat _ _ _ ⟨h2, Re.R.mem_U _⟩) (so_trans (hρ y) (so_pull hv₁ (R.compat _ _ _ ⟨R.mem_U _, h1⟩)))
    have han : ∀ y ∈ O, ∀ j k, y ∈ (R.A.chart j).source → ρ y ∈ (Re.R.A.chart k).source →
        AnalyticAt ℂ (Re.R.A.chart k ∘ ρ ∘ (R.A.chart j).symm) (R.A.chart j y) := fun y hy j k hj hk =>
      analyticAt_factor (U := Re.R.U (ρ y)) (lam := Re.R.lift (ρ y)) (V := R.U y)
        (mu := fun w p => R.lift y w (v₁ p)) (Re.R.holo _) (Re.R.mem_U _) (fun p => R.holo y _) (R.mem_U y)
        (hcont y hy) (Re.R.mem _ _ (Re.R.mem_U _)).1 (Re.R.immersion _ (hoff y hy))
        (by
          filter_upwards [(R.isOpen_U y).mem_nhds (R.mem_U y),
            hcont y hy ((Re.R.isOpen_U _).mem_nhds (Re.R.mem_U (ρ y)))] with w h1 h2
          exact hso _ _ _ h1 h2) j k hj hk
    obtain ⟨V₁, hV₁, hxV₁, G₁, hG₁, hE₁⟩ := Re.ref_pot a (ρ x) trivial
    have hN : IsOpen (R.U x ∩ (O ∩ ρ ⁻¹' (V₁ ∩ Re.R.U (ρ x)))) := (R.isOpen_U x).inter
      (ContinuousOn.isOpen_inter_preimage (fun y hy => (hcont y hy).continuousWithinAt) hO
        (hV₁.inter (Re.R.isOpen_U _)))
    obtain ⟨W, hW, hxW, hWN, G, hG, hEG⟩ := orbit_re (A := R.A) (Re.ref a) hN
      (lam := fun y p => R.lift x y (v₁ p)) (mu := fun y => Re.R.lift (ρ x) (ρ y))
      (fun p => holo_mono (R.holo x _) Set.inter_subset_left)
      (fun p => holo_comp (Re.R.holo (ρ x) p) (fun y hy => hy.2.2.2) (fun y hy => hcont y hy.2.1)
        fun y hy => han y hy.2.1)
      (fun y hy => (Re.R.mem _ _ hy.2.2.2).1) (fun y hy => so_symm (hso _ _ _ hy.1 hy.2.2.2))
      (x := x) ⟨R.mem_U x, hx, hxV₁, Re.R.mem_U _⟩
    have hG₂ : R.A.HoloOn W fun y => G₁ (ρ y) := holo_comp hG₁ (fun y hy => (hWN hy).2.2.1)
      (fun y hy => hcont y (hWN hy).2.1) fun y hy => han y (hWN hy).2.1
    refine ⟨W, hW, hxW, fun y => G y + G₁ (ρ y), fun j w hw => (hG j w hw).add (hG₂ j w hw), fun y hy => ?_⟩
    have a1 := hEG y hy
    have a2 := hE₁ _ (hWN hy).2.2.1
    simp only [potOf, LocPot.pullback] at a1 a2 ⊢
    rw [hr.2, c1 x _ (hρ x), c1 y _ (hρ y), Complex.add_re]
    linarith
  · have h1 := Re.line_eq a t ht ht' (ρ x)
    obtain ⟨c, hc, h⟩ := hρ x
    have hnz := (hmem x x (R.mem_U x)).1
    rw [h, log_h_orbit _ hc hnz, log_h_orbit _ hc hnz, Re.line_deg] at h1
    rw [c1 x _ (hρ x)]
    linarith
  · obtain ⟨b₁, hb₁⟩ := homog_rename hv hβ
    obtain ⟨b, hb⟩ := homog_rename hv₁ hb₁
    refine ⟨_, b, hb, hβP, fun x hx => ?_⟩
    rw [hev₁, hev₀]
    exact (eval_ne_so hβ (hπo x)).mp (hβ0 _ hx)

end PositivityTheory.UnitarySelfGeneration
end
