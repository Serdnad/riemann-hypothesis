module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle004
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedMeasureConvergenceSnc
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle076
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle055
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle003
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def positionPerm {n : ℕ} (m : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' m).symm

theorem positionPerm_last {n : ℕ} (m : Fin (n + 1)) : positionPerm m (Fin.last n) = m := by
  simp [positionPerm]

theorem positionPerm_castSucc {n : ℕ} (m : Fin (n + 1)) (j : Fin n) :
    positionPerm m (Fin.castSucc j) = m.succAbove j := by
  simp [positionPerm]

def word {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) : Fin (n + 1) → HermLine ι :=
  fun j => if (j : ℕ) < m then a else if (j : ℕ) < k then a₀ else A'

theorem word_comp_low {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) (hk : m < k) :
    word (n := n) a a₀ A' k m ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀ := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last, hk]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      simp [h]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem word_comp_high {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) :
    word (n := n) a a₀ A' k (m + 1) ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      have h1 : (i : ℕ) < m + 1 := by omega
      simp [h, h1]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m + 1 := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem forall_snoc {n : ℕ} {p : HermLine ι → Prop} {L : Fin n → HermLine ι} {x : HermLine ι}
    (hL : ∀ j, p (L j)) (hx : p x) : ∀ j, p ((Fin.snoc L x : Fin (n + 1) → HermLine ι) j) := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa using hx
  | cast i => simpa using hL i

theorem cone_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    (∀ k, ∃ i, (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, right_ne_zero_of_mul hi⟩
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem logRatio_smul {a a₀ : HermLine ι} (hd : a.a = a₀.a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := by
  have hcone := cone_smul c z hc
  unfold logRatio
  by_cases h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos (hcone.mpr h), if_pos h, a.smul c z hc, a₀.smul c z hc, hd]
    have hprod : (∏ k, ‖c k‖ ^ a₀.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [Real.log_mul hprod (a₀.pos z h).ne', Real.log_mul hprod (a.pos z h).ne']
    ring
  · rw [if_neg (fun h' => h (hcone.mp h')), if_neg h]

theorem logRatio_smooth {a a₀ : HermLine ι} (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logRatio a a₀) := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ((h0.log fun z hz => (a₀.pos z hz).ne').sub (h1.log fun z hz => (a.pos z hz).ne')).congr ?_
  intro z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz
  simp only [logRatio, if_pos hz']

theorem tensor_logRatio_h {a a₀ : HermLine ι}
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)).h z = a.h z := by
  have h0 := a₀.pos z hz
  have h1 := a.pos z hz
  show a₀.h z * Real.exp (-logRatio a a₀ z) = a.h z
  rw [logRatio, if_pos hz, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h0,
    ← mul_div_assoc, mul_div_right_comm, div_self h0.ne', one_mul]

theorem word_step (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k m : ℕ)
    (hP : IsArithVar P (n + 1)) (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) (hA' : IsSmoothHerm A')
    (hd : a.a = a₀.a) (hk : k ≤ n + 1) (hm : m < k) :
    I P (n + 1) (word a a₀ A' k (m + 1)) - I P (n + 1) (word a a₀ A' k m) =
      -ptsIntegral P (pot (mixWord (n := n) a a₀ A' k m)) (logRatio a a₀) := by
  have hu : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := fun c z hc => logRatio_smul hd c z hc
  have hMs : ∀ j, IsSmoothHerm (mixWord (n := n) a a₀ A' k m j) := fun j => by
    simp only [mixWord]
    split_ifs <;> assumption
  have hWs : ∀ r (j : Fin (n + 1)), IsSmoothHerm (word (n := n) a a₀ A' k r j) := fun r j => by
    simp only [word]
    split_ifs <;> assumption
  have hmn : m < n + 1 := lt_of_lt_of_le hm hk
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have hlr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := logRatio_smooth ha ha₀
  have hT : IsSmoothHerm (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)) := by
    show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => a₀.h z * Real.exp (-logRatio a a₀ z))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
    exact h0.mul hlr.neg.exp
  have e1 : I P (n + 1) (word (n := n) a a₀ A' k (m + 1)) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) := by
    rw [← word_comp_high a a₀ A' k m hmn, hI.1 P (n + 1) _ _ hP (hWs (m + 1))]
  have e0 : I P (n + 1) (word (n := n) a a₀ A' k m) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀) := by
    rw [← word_comp_low a a₀ A' k m hmn hm, hI.1 P (n + 1) _ _ hP (hWs m)]
  have e2 : I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m)
        (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu))) := by
    refine metricLocal K ι I hI P (n + 1) _ _ hP (forall_snoc (p := IsSmoothHerm) hMs ha)
      (forall_snoc (p := IsSmoothHerm) hMs hT) ?_ ?_
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        show a.a = a₀.a + 0
        rw [add_zero, hd]
      | cast i => simp only [Fin.snoc_castSucc]
    · intro j z hz
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact (tensor_logRatio_h hu z hz.1).symm
      | cast i => simp only [Fin.snoc_castSucc]
  have e3 := metricChange K ι I hI P n (mixWord (n := n) a a₀ A' k m) a₀ (logRatio a a₀) hu hP hMs ha₀
    (logRatio_smooth ha ha₀)
  rw [e1, e0, e2, e3]
  ring

theorem positionTelescope : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) →
      IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 →
      I P (n + 1) (fun j => if (j : ℕ) < k then a else A') -
          I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') =
        -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  intro K _ ι _ I hI P n a a₀ A' k hP ha ha₀ hA' hd hk
  have h1 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a else A') = word (n := n) a a₀ A' k k := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [word, h]
  have h0 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a₀ else A') = word (n := n) a a₀ A' k 0 := by
    funext j
    simp [word]
  have hs := Finset.sum_range_sub (fun r => I P (n + 1) (word (n := n) a a₀ A' k r)) k
  rw [h1, h0, ← hs, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact word_step I hI P n a a₀ A' k i hP ha ha₀ hA' hd hk (Finset.mem_range.mp hi)

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele
end
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.mixed_measure_convergence_snc : GroundTheory.Heights₂.Heights.AnalyticLimit.UniformIntegrability.Statement → TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas (e + 1) X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X), IsPotential A L' → IsSection A L' v → IsSNC A L' v ![1] ![Dg] → IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg) → ∀ (th : Fin (e + 1) → LocPot X) (ph : Fin (e + 1) → X → ℝ) (phT : Fin (e + 1) → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε) (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) ∧ ∫ y, GroundTheory.Heights₂.Heights.AnalyticLimit.greenEp L' v ε y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform | exact GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem regGlobalStatement_holds : RegGlobalStatement := by
  intro e X _ _ _ A B Θ L s n m W hΘ hΘpos hL hS hSNC hs hAd th ph C₅ hSW hGB
  obtain ⟨B', x, hAd', hGB', hsrc⟩ := GlobalTheory.T.refine_adapted_atlas_with_gradient A B L th s ph C₅ hs hAd hGB
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd'
  choose S mm hm1 hbd hrl using hM
  have hcl : IsClosed (bdry s) := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨hth, hphs, hpsh, hb⟩ := hSW
  obtain ⟨C₅', hC₅'0, hconv⟩ := GlobalTheory.T.log_bound_transfer_between_radii C₅ M
  obtain ⟨hlogd, hmono, hle, htend, hsmall, hmin⟩ := GlobalTheory.T.epsilon_schedule_properties
  have hrWge : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hball : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      z ∈ (B'.chart j).target ∧ (B'.chart j).symm z ∉ bdry s := by
    intro j z hz
    have hzt : z ∈ (B'.chart j).target := h2 j (ball_subset_closedBall hz.1)
    exact ⟨hzt, fun hzb => hz.2 ((hbd j z hzt).1 hzb)⟩
  have hq : ∀ j, ContDiffOn ℝ ∞ (fun z => th.φ (x j) ((B'.chart j).symm z)) (ball (0 : Fin e → ℂ) 2) :=
    fun j => (smoothOn_of_compatible hAB (th.isOpen_U (x j)) (hth.1 (x j)) j).mono fun z hz =>
      ⟨h2 j (ball_subset_closedBall hz),
        hsrc j ((B'.chart j).map_target (h2 j (ball_subset_closedBall hz)))⟩
  have hphj : ∀ j, ContDiffOn ℝ ∞ (ph ∘ (B'.chart j).symm)
      (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j)) :=
    fun j => (smoothOn_of_compatible hAB hcl.isOpen_compl hphs j).mono fun z hz => hball j z hz
  have hlevi : ∀ j, ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j))
      (fun z => (fun z => th.φ (x j) ((B'.chart j).symm z)) z + (ph ∘ (B'.chart j).symm) z) := by
    intro j
    refine ⟨(((hq j).mono Set.diff_subset).add (hphj j)).of_le h2le, fun z hz w => ?_⟩
    exact GlobalTheory.T.levi_nonneg_in_chart_of_psh A B' th ph (bdry s)ᶜ (x j) j hAB hth hcl.isOpen_compl hphs hpsh (hsrc j) z (hball j z hz) w
  have hbnd : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      -C₅' * Real.log (rLoc (S j) (mm j) z) ≤ (ph ∘ (B'.chart j).symm) z ∧
        (ph ∘ (B'.chart j).symm) z ≤ C₅' := by
    intro j z hz
    obtain ⟨-, hzb⟩ := hball j z hz
    have hr := hrl j z (ball_subset_closedBall hz.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz.1)
    exact (hconv _ _ (ph ((B'.chart j).symm z)) 0 (hrWge _) hrl' hr).1 (hb _ hzb).1 (hb _ hzb).2
  have hgrad : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      ‖fderiv ℝ (ph ∘ (B'.chart j).symm) z‖ ≤
        C₅' * rLoc (S j) (mm j) z ^ C₅' * Real.exp (rLoc (S j) (mm j) z / 2) := by
    intro j z hz
    have hz2 : z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j) :=
      ⟨ball_subset_ball (by norm_num) hz.1, hz.2⟩
    obtain ⟨-, hzb⟩ := hball j z hz2
    have hr := hrl j z (ball_subset_closedBall hz2.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz2.1)
    exact (hconv _ _ 0 _ (hrWge _) hrl' hr).2 (hGB' j z hz.1 hzb)
  have hch := fun j => GlobalTheory.T.local_levi_psh_regularization e (S j) (mm j) (fun z => th.φ (x j) ((B'.chart j).symm z))
    (ph ∘ (B'.chart j).symm) C₅' M (hm1 j) (hq j) (hphj j) (hlevi j) (hbnd j) (hgrad j)
  choose Cj tj g hCj1 htj0 htje hgt hgC2 using hch

  obtain ⟨C', t', ht'0, hcmp⟩ := GlobalTheory.T.glued_local_regularizations_on_atlas A B' L th s ph C₅ M x S mm hAB h2 hsrc hs hcl hbd hrl
    ⟨hth, hphs, hpsh, hb⟩
  set Cm : ℝ := 1 + ∑ j, |Cj j| with hCmdef
  have hCm : ∀ j, Cj j ≤ Cm := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2' := le_abs_self (Cj j)
    linarith
  have hCm1 : 1 ≤ Cm := by
    have : 0 ≤ ∑ j, |Cj j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set Cl : ℝ := |C'| + Cm with hCldef
  have hCl1 : 1 ≤ Cl := by have := abs_nonneg C'; linarith
  have hClj : ∀ j, Cj j ≤ Cl := fun j => by have := abs_nonneg C'; linarith [hCm j]
  obtain ⟨a, ha0, ha⟩ := hsmall Cl
  obtain ⟨tm, htm0, htm⟩ := hmin B'.n tj htj0
  set t₀ : ℝ := min (min tm t') (min a (Real.exp (-Real.exp 1))) with ht₀def
  have ht₀0 : 0 < t₀ := lt_min (lt_min htm0 ht'0) (lt_min ha0 (Real.exp_pos _))
  have ht₀j : ∀ j, t₀ ≤ tj j := fun j => ((min_le_left _ _).trans (min_le_left _ _)).trans (htm j)
  have ht₀' : t₀ ≤ t' := (min_le_left _ _).trans (min_le_right _ _)
  have ht₀a : t₀ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have ht₀e : t₀ ≤ Real.exp (-Real.exp 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hLL : ∀ t, 0 < t → t ≤ t₀ → 0 ≤ Real.log (Real.log (1 / t)) := fun t ht htt => by
    have := (log_inv_bounds ht (htt.trans ht₀e)).2; linarith

  have hy54 : ∀ j, ∀ y ∈ chartBall B' j (5 / 4), B'.chart j y ∈ ball (0 : Fin e → ℂ) (5 / 4) ∧
      B'.chart j y ∈ closedBall (0 : Fin e → ℂ) 2 ∧ (B'.chart j).symm (B'.chart j y) = y := by
    intro j y hy
    exact ⟨hy.2, ball_subset_closedBall (ball_subset_ball (by norm_num) hy.2), (B'.chart j).left_inv hy.1⟩
  have hsand : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) y + g j t (B'.chart j y) ∧
        th.φ (x j) y + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := by
    intro t ht htt j y hy
    obtain ⟨hz, -, hsy⟩ := hy54 j y hy
    have h := ((hgt j t ht (htt.trans (ht₀j j))).2.2.2.2.1 (B'.chart j y) hz)
    have h' : polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ∧
        th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := h
    rw [hsy] at h'
    exact h'
  have hloc : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ (g j t ∘ B'.chart j) y ∧
        (y ∉ bdry s → ph y ≤ (g j t ∘ B'.chart j) y ∧
          (rW L s y ≤ Real.log (1 / t) → (g j t ∘ B'.chart j) y ≤ ph y + t ^ ((1 : ℝ) / 3))) := by
    intro t ht htt j y hy
    obtain ⟨hz, hz2, hsy⟩ := hy54 j y hy
    obtain ⟨-, -, hgb, hgn, -, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    obtain ⟨hb1, hb2⟩ := hgb _ hz
    have hll := hLL t ht htt
    refine ⟨hb1.trans (hClj j), le_trans ?_ hb2, fun hyb => ?_⟩
    · have := mul_le_mul_of_nonneg_right (hClj j) hll
      show -Cl * _ ≤ -Cj j * _
      linarith
    · have hzt : B'.chart j y ∈ (B'.chart j).target := h2 j hz2
      have hzc : B'.chart j y ∉ ReciprocityTheory.AnForm.A.coordDiv (S j) := fun hc =>
        hyb (hsy ▸ (hbd j _ hzt).2 hc)
      obtain ⟨hn1, hn2⟩ := hgn _ ⟨hz, hzc⟩
      have hr := hrl j _ hz2 (by rw [hsy]; exact hyb)
      rw [hsy] at hr
      simp only [Function.comp_apply, hsy] at hn1 hn2 ⊢
      refine ⟨hn1, fun hrw => hn2 ?_⟩
      have := (abs_le.1 hr).1
      linarith
  have hmono' : ∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ (g j t' ∘ B'.chart j) y + epsT Cl t' := by
    intro t t'' ht htt' ht'' j y hy
    obtain ⟨hz, -, -⟩ := hy54 j y hy
    have h := (hgt j t ht ((htt'.trans ht'').trans (ht₀j j))).2.2.2.2.2 t'' htt' (ht''.trans (ht₀j j)) _ hz
    have := epsT_le_epsT (hClj j) (ht.trans_le htt') (ht''.trans ht₀e)
    simp only [Function.comp_apply]
    linarith

  obtain ⟨K, hK0, hgl⟩ := GlobalTheory.T.regularization_glue_C2_explicit A B' Θ th s ph hAB hcov h2 hΘ hΘpos hth hcl hphs
  have hback : ∀ t, 0 < t → t ≤ t₀ → ∀ j, A.SmoothOn (chartBall B' j (5 / 4)) (g j t ∘ B'.chart j) ∧
      IsPshOn A (chartBall B' j (5 / 4)) (th + LocPot.ofFun (g j t ∘ B'.chart j)) := by
    intro t ht htt j
    obtain ⟨hgs, hglevi, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    exact GlobalTheory.T.smoothOn_of_chart_levi_nonneg A B' th (x j) j (ball (0 : Fin e → ℂ) (5 / 4)) (g j t) hAB hth (hsrc j) isOpen_ball
      (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))) hgs hglevi.2
  have hov : ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B' j (5 / 4) ∩ chartBall B' k (5 / 4),
      |(g j t ∘ B'.chart j) y - (g k t ∘ B'.chart k) y| ≤ epsT Cl t := by
    intro t ht htt j k y hy
    obtain ⟨sj1, sj2⟩ := hsand t ht htt j y hy.1
    obtain ⟨sk1, sk2⟩ := hsand t ht htt k y hy.2
    have hc := abs_le.1 (hcmp t ht (htt.trans ht₀') j k y hy)
    have hte := htt.trans ht₀e
    have e1 := epsT_le_epsT (hCm j) ht hte
    have e2 := epsT_le_epsT (hCm k) ht hte
    have e3 := epsT_le_epsT (le_abs_self C') ht hte
    have e4 : epsT Cl t = epsT |C'| t + epsT Cm t := by
      simp only [hCldef, epsT]; ring
    simp only [Function.comp_apply]
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  obtain ⟨F, hF, hFC2⟩ := hgl t₀ (epsT Cl) (fun t j => g j t ∘ B'.chart j) ht₀0 (htend Cl)
    (fun t ht htt => ⟨hle Cl t hCl1 ht (htt.trans ht₀e), ha t ht (htt.trans ht₀a),
      fun j => (hback t ht htt j).1,
      ⟨Cl + Cl * Real.log (Real.log (1 / t)), fun j y hy => by
        obtain ⟨h1, h2', -⟩ := hloc t ht htt j y hy
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ Cl) (hLL t ht htt)
        rw [abs_le]; constructor <;> linarith⟩,
      fun j => (hback t ht htt j).2, hov t ht htt⟩)
    (fun j K' hK' hK'c => by
      have hsub : K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv (S j) := by
        intro z hz
        have hzt : z ∈ (B'.chart j).target :=
          h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1))
        exact ⟨(hK' hz).1, fun hc => (hK' hz).2 ((hbd j z hzt).2 hc)⟩
      exact GlobalTheory.T.C2_tendsto_pullback_through_chart (B'.chart j) (g j) (ph ∘ (B'.chart j).symm) K'
        (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1)))
        (hgC2 j K' hsub hK'c))
  obtain ⟨C, hC⟩ := GlobalTheory.T.regularization_glue_bounds A B' Θ L th s ph C₅ K Cl t₀ (fun t j => g j t ∘ B'.chart j) F hΘ hΘpos hth hs hcov
    (fun y hy => (hb y hy).1) hK0 hCl1 ht₀0 ht₀e hF hloc hmono'
  exact ⟨C, t₀, F, hC, hFC2⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end
