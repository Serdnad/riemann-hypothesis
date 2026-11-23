module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import GroundTheory.PAdicHodge.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import GroundTheory.LocalFields.MaximalUnramified
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle238
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.LocalFields.FormalGroups.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Ideal.BigOperators
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

section

open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestBump

variable {ι : Type} [Fintype ι]

def nsq (y : ι → ℂ) : ℝ := ∑ j, ‖y j‖ ^ 2

lemma contDiff_coordSq (i : ι) {n : WithTop ℕ∞} : ContDiff ℝ n fun y : ι → ℂ => ‖y i‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) i)

lemma contDiff_nsq {n : WithTop ℕ∞} : ContDiff ℝ n (nsq : (ι → ℂ) → ℝ) :=
  ContDiff.sum fun j _ => contDiff_coordSq j

lemma coordSq_le_nsq (y : ι → ℂ) (i : ι) : ‖y i‖ ^ 2 ≤ nsq y :=
  Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

lemma nsq_smul (t : ℂ) (v : ι → ℂ) : nsq (t • v) = ‖t‖ ^ 2 * nsq v := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

def radial : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma radial_one : radial 1 = 1 :=
  radial.one_of_mem_closedBall (Metric.mem_closedBall_self radial.rIn_pos.le)

lemma radial_zero_of_le {x : ℝ} (h : x ≤ 1 / 2) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

lemma radial_zero_of_ge {x : ℝ} (h : 3 / 2 ≤ x) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

def angular {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, by positivity, by linarith⟩

lemma angular_one {δ : ℝ} (hδ : 0 < δ) : angular hδ 1 = 1 :=
  (angular hδ).one_of_mem_closedBall (Metric.mem_closedBall_self (angular hδ).rIn_pos.le)

lemma lt_of_angular_ne {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (h : angular hδ x ≠ 0) : 1 - δ < x := by
  by_contra hx
  refine h ((angular hδ).zero_of_le_dist ?_)
  rw [Real.dist_eq, abs_of_nonpos (by linarith [not_lt.1 hx])]
  change δ ≤ _
  linarith [not_lt.1 hx]

def bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) (y : ι → ℂ) : ℝ :=
  radial (nsq y) * angular hδ (‖y i₀‖ ^ 2 / nsq y)

def smallF (t : ℂ) : ℝ := radial (‖t‖ ^ 2)

lemma contDiff_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} :
    ContDiff ℝ (n : WithTop ℕ∞) (bigF i₀ hδ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases h : 0 < nsq y
  · exact (radial.contDiff.contDiffAt.comp y contDiff_nsq.contDiffAt).mul
      ((angular hδ).contDiff.contDiffAt.comp y
        ((contDiff_coordSq i₀).contDiffAt.div contDiff_nsq.contDiffAt h.ne'))
  · have h0 : nsq y < 1 / 2 := by linarith [not_lt.1 h]
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(contDiff_nsq (n := 0)).continuous.continuousAt.eventually (gt_mem_nhds h0)] with z hz
    simp [bigF, radial_zero_of_le (le_of_lt hz)]

lemma hasCompactSupport_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (bigF i₀ hδ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 2) fun y hy => ?_
  by_contra hne
  have hr : radial (nsq y) ≠ 0 := fun h => hne (by simp [bigF, h])
  have hlt : nsq y < 3 / 2 := by
    by_contra hge
    exact hr (radial_zero_of_ge (not_lt.1 hge))
  refine hy ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have := coordSq_le_nsq y i
  nlinarith [norm_nonneg (y i)]

lemma contDiff_smallF {n : ℕ∞} : ContDiff ℝ (n : WithTop ℕ∞) smallF :=
  radial.contDiff.comp (contDiff_norm_sq ℝ)

lemma hasCompactSupport_smallF : HasCompactSupport smallF := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun t ht => ?_
  refine radial_zero_of_ge ?_
  have : 2 < ‖t‖ := by simpa using ht
  nlinarith

end GlobalTheory.CompanionTheory.TestBump


open GlobalTheory.CompanionTheory.TestBump in
theorem GlobalTheory.CompanionTheory.TestBump.cplxBump : CplxBump := by
  classical
  intro ι _ _ i₀ δ hδ
  refine ⟨bigF i₀ hδ, smallF, contDiff_bigF i₀ hδ, hasCompactSupport_bigF i₀ hδ, contDiff_smallF,
    hasCompactSupport_smallF, ?_, ?_, fun t => radial.nonneg, fun v => mul_nonneg radial.nonneg (angular hδ).nonneg, ?_⟩
  · have h1 : nsq (Pi.single i₀ 1 : ι → ℂ) = 1 := by
      simp only [nsq]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    simp [bigF, h1, radial_one, angular_one]
  · intro t ht
    simp [smallF, ht, radial_one]
  · intro v hv
    have hv1 : nsq v = 1 := hv
    have hFv : bigF i₀ hδ v = angular hδ (‖v i₀‖ ^ 2) := by
      simp [bigF, hv1, radial_one]
    refine ⟨fun t => ?_, fun h => ?_⟩
    · rw [hFv]
      by_cases ht : t = 0
      · subst ht
        have hz : radial (0 : ℝ) = 0 := radial_zero_of_le (by norm_num)
        simp [bigF, smallF, nsq, hz]
      · have hn : nsq (t • v) = ‖t‖ ^ 2 := by rw [nsq_smul, hv1, mul_one]
        have ht2 : ‖t‖ ^ 2 ≠ 0 := by positivity
        simp only [bigF, smallF, hn, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
        rw [mul_div_cancel_left₀ _ ht2]
    · exact lt_of_angular_ne hδ (by rwa [hFv] at h)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.local_bridge_lubin_tate_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | exact GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum

theorem adic_sum_exists {W : Type} [CommRing W] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (N : ℕ) (hN : 0 < N) (b : ℕ → W) :
    ∃ L : W, ∀ M, ∃ c : W,
      L - ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n = (p : W) ^ (M / N) * c := by
  set I : Ideal W := Ideal.span {(p : W)} with hI
  set g : ℕ → W := fun M => ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n with hg
  have key : ∀ e M₁ M₂, e * N ≤ M₁ → M₁ ≤ M₂ → g M₂ - g M₁ ∈ I ^ e := by
    intro e M₁ M₂ h₁ h₂
    simp only [hg]
    rw [← Finset.sum_Ico_eq_sub _ h₂]
    refine Ideal.sum_mem _ fun n hn => ?_
    have hn' : e ≤ n / N := (Nat.le_div_iff_mul_le hN).2 (h₁.trans (Finset.mem_Ico.1 hn).1)
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hn'
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := W) inferInstance
    (f := fun k => g (k * N)) (by
      intro m n hmn
      rw [SModEq.sub_mem]
      simp only [smul_eq_mul, Ideal.mul_top]
      have := key m (m * N) (n * N) le_rfl (Nat.mul_le_mul_right N hmn)
      have h2 := (I ^ m).neg_mem this
      simpa using h2)
  refine ⟨L, fun M => ?_⟩
  have h₁ : L - g (M / N * N) ∈ I ^ (M / N) := by
    have := hL (M / N)
    rw [SModEq.sub_mem] at this
    simp only [smul_eq_mul, Ideal.mul_top] at this
    have h2 := (I ^ (M / N)).neg_mem this
    simpa using h2
  have h₂ : g M - g (M / N * N) ∈ I ^ (M / N) := key _ _ _ le_rfl (Nat.div_mul_le_self M N)
  have h₃ : L - g M ∈ I ^ (M / N) := by
    have := (I ^ (M / N)).sub_mem h₁ h₂
    simpa using this
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h₃
  obtain ⟨c, hc⟩ := h₃
  exact ⟨c, by rw [mul_comm, hc]⟩

theorem sum_exists {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B)
    (hw : ∀ a, w a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hgen : ∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t))
    (ϖ y : B) (N : ℕ) (hN : 0 < N) (hϖ : ϖ ∈ S) (hy : y ∈ S) (hN' : ϖ ^ N = (p : B) * y)
    (s : ℕ → B) (hs : ∀ n, s n ∈ S) :
    ∃ r ∈ S, ∀ M, ∃ c ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = (p : B) ^ (M / N) * c := by
  have hu : ∀ n, ϖ ^ (n % N) * y ^ (n / N) * s n ∈ S := fun n =>
    S.mul_mem (S.mul_mem (S.pow_mem hϖ _) (S.pow_mem hy _)) (hs n)
  choose a ha using fun n => hgen _ (hu n)
  have hpow : ∀ n, ϖ ^ n * s n = (p : B) ^ (n / N) * ∑ t ∈ T, t * w (a n t) := by
    intro n
    rw [← ha n]
    have hϖn : ϖ ^ n = ((p : B) ^ (n / N) * y ^ (n / N)) * ϖ ^ (n % N) := by
      have h0 : ϖ ^ n = ϖ ^ (N * (n / N) + n % N) := by rw [Nat.div_add_mod]
      rw [h0, pow_add, pow_mul, hN', mul_pow]
    rw [hϖn]
    ring
  choose α hα using fun t => adic_sum_exists (W := W) p N hN (fun n => a n t)
  choose c hc using fun t M => hα t M
  refine ⟨∑ t ∈ T, t * w (α t), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), fun M => ?_⟩
  refine ⟨∑ t ∈ T, t * w (c t M), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), ?_⟩
  have hterm : ∀ t, w (α t) = ∑ n ∈ Finset.range M, (p : B) ^ (n / N) * w (a n t)
      + (p : B) ^ (M / N) * w (c t M) := by
    intro t
    have h := congrArg w (hc t M)

    simp only [map_sub, map_sum, map_mul, map_pow, map_natCast] at h
    rw [← h]; ring
  simp only [hpow, hterm, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hswap : ∑ n ∈ Finset.range M, ∑ t ∈ T, (p : B) ^ (n / N) * (t * w (a n t))
      = ∑ t ∈ T, ∑ n ∈ Finset.range M, t * ((p : B) ^ (n / N) * w (a n t)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => by ring
  rw [hswap, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem sum_with_tails {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B) :
    (∀ a, w a ∈ S) → (∀ t ∈ T, t ∈ S) → (∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t)) →
    (∀ x, (∀ m : ℕ, ∃ s ∈ S, x = (p : B) ^ m * s) → x = 0) →
    ∀ (ϖ y : B) (N : ℕ), 0 < N → ϖ ∈ S → y ∈ S → ϖ ^ N = (p : B) * y →
    ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ M, ∃ a ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = ϖ ^ M * a := by
  intro hw hT hgen hsep ϖ y N hN hϖ hy hN' s hs
  obtain ⟨r, hrS, hr⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN' s hs
  refine ⟨r, hrS, fun M => ?_⟩
  obtain ⟨rM, hrMS, hrM⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN'
    (fun n => s (M + n)) (fun n => hs _)
  refine ⟨rM, hrMS, ?_⟩
  have hd : r - ∑ n ∈ Finset.range M, ϖ ^ n * s n - ϖ ^ M * rM = 0 := by
    refine hsep _ fun m => ?_
    obtain ⟨c₁, hc₁S, hc₁⟩ := hr (M + N * m)
    obtain ⟨c₂, hc₂S, hc₂⟩ := hrM (N * m)
    have hdiv₁ : (M + N * m) / N = M / N + m := Nat.add_mul_div_left _ _ hN
    have hdiv₂ : (N * m) / N = m := Nat.mul_div_cancel_left _ hN
    rw [hdiv₁] at hc₁
    rw [hdiv₂] at hc₂
    refine ⟨(p : B) ^ (M / N) * c₁ - ϖ ^ M * c₂,
      S.sub_mem (S.mul_mem (S.pow_mem (natCast_mem S p) _) hc₁S)
        (S.mul_mem (S.pow_mem hϖ _) hc₂S), ?_⟩
    rw [Finset.sum_range_add] at hc₁
    have e₁ : r = ∑ n ∈ Finset.range M, ϖ ^ n * s n
        + ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        + (p : B) ^ (M / N + m) * c₁ := by rw [← hc₁]; ring
    have e₂ : rM = ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) + (p : B) ^ m * c₂ := by
      rw [← hc₂]; ring
    have e₃ : ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        = ϖ ^ M * ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e₁, e₂, e₃]
    ring
  exact sub_eq_zero.1 hd

end GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum
end
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

theorem _root_.GlobalTheory.T.sum_local_degrees_over_l : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (T : Finset (HeightOneSpectrum (𝓞 F))), (∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) → ∑ v ∈ T, locDeg v = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank | exact GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank | (intros; apply GlobalTheory.CompanionTheory.GreenbergWiles.sum_locDeg_eq_finrank <;> assumption)
end
