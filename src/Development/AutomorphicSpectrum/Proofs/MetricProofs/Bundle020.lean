module

import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace AnMono

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_isPosPot (A : FinHolAtlas e X) (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem log_inv_ge {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / t) ∧ 0 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  exact ⟨h1, Real.log_nonneg h1⟩

theorem quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_ge ht hte
  exact div_nonneg h2 (by linarith)

theorem epsT_mono {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    epsT C t ≤ epsT C' t := by
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (quot_nonneg ht hte)

theorem mul_epsT_mono {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    C * epsT C t ≤ C' * epsT C' t := by
  have hx := quot_nonneg ht hte
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem exp_one_le_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    Real.exp 1 ≤ rW L s y := by
  have := hs y
  unfold rW
  linarith

theorem one_le_log_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    1 ≤ Real.log (rW L s y) := by
  have := Real.log_le_log (Real.exp_pos 1) (exp_one_le_rW L s hs y)
  rwa [Real.log_exp] at this

theorem isSingWeight_mono (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X) (ph : X → ℝ) {C₅ C₅' : ℝ} (hC : C₅ ≤ C₅')
    (h : IsSingWeight A L s th ph C₅) : IsSingWeight A L s th ph C₅' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  obtain ⟨h5, h6⟩ := h4 y hy
  have hl := one_le_log_rW L s hs y
  constructor
  · nlinarith
  · linarith

theorem isRegFamily_enlarge (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X)
    (ph : X → ℝ) (phT : ℝ → X → ℝ) {C t₀ C' t₁ : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hs : ∀ y, logNormSec L s y ≤ 0)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀)
    (hte : t₁ ≤ Real.exp (-1)) : IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y =>
    (Real.exp_pos 1).le.trans (exp_one_le_rW L s hs y)
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-1) := htt.trans hte
  have hε := epsT_mono hCC ht hte'
  have hll := (log_inv_ge ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_,
    fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_mono hC (ht.trans_le htt') (ht'.trans hte)
    linarith

theorem continuous_of_smooth (A : FinHolAtlas e X) (u : X → ℝ) (h : A.Smooth u) : Continuous u := by
  apply ReciprocityTheory.AnForm.M.PLAux.smooth_continuous <;> assumption

theorem tendstoUniformlyOn_self {α β : Type*} [UniformSpace β] (f : α → β) (p : Filter ℝ)
    (K : Set α) : TendstoUniformlyOn (fun _ : ℝ => f) f p K := by
  intro v hv
  exact Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hv

theorem isRegFamilyC2_const (A : FinHolAtlas e X) (s : X → X → ℂ) (u : X → ℝ) :
    IsRegFamilyC2 A s u (fun _ => u) := fun j K _ _ =>
  ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _⟩

theorem isPsh_add_rsmul (A : FinHolAtlas e X) (Θ th : LocPot X) (u : X → ℝ) {ε : ℝ}
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th) (hu : A.Smooth u)
    (hε : 0 ≤ ε) (h : IsPsh A (th + LocPot.ofFun u)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε) := by
  refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th u hΘ hΘp hth hu hε ?_
  intro x j y hy w
  have hfun : (th + LocPot.ofFun u + Θ.rsmul 0).φ x ∘ (A.chart j).symm =
      (th + LocPot.ofFun u).φ x ∘ (A.chart j).symm := by
    funext z
    show th.φ x _ + u _ + 0 * Θ.φ x _ = th.φ x _ + u _
    ring
  rw [hfun]
  exact h x j y ⟨hy.1, hy.2.1⟩ w

theorem smooth_member [CompactSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ)
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X)
    (u : X → ℝ) (hth : IsPotential A th) (hu : A.Smooth u) (hp : IsPsh A (th + LocPot.ofFun u)) :
    ∃ C₀, IsSingWeight A L s th u C₀ ∧
      IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
        IsRegFamilyC2 A s u (fun _ => u) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_of_smooth A u hu).continuousOn
  have hb : ∀ y, |u y| ≤ |M| + 1 := fun y => by
    have := hM y (Set.mem_univ y)
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M]
  set C₀ : ℝ := |M| + 1 with hC₀
  have hC0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀, ⟨hth, fun j => (hu j).mono ?_, fun x j y hy w => ?_, fun y _ => ?_⟩, ?_,
    isRegFamilyC2_const A s u⟩
  · exact fun z hz => ⟨hz.1, Set.mem_univ _⟩
  · exact hp x j y ⟨hy.1, hy.2.1⟩ w
  · have hl := one_le_log_rW L s hs y
    have h := abs_le.1 (hb y)
    constructor
    · nlinarith
    · exact h.2
  · have he : 0 < Real.exp 1 := Real.exp_pos 1
    refine ⟨Real.exp_pos _, ?_, fun t ht htt => ?_⟩
    · exact Real.exp_lt_one_iff.2 (by linarith)
    have hl := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht htt
    have hq := GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg ht htt
    have hε : 0 ≤ epsT C₀ t := by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 hq
    have hε' : ∀ t', 0 < t' → t' ≤ Real.exp (-Real.exp 1) → 0 ≤ C₀ * epsT C₀ t' := fun t' h0 h1 => by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 (mul_nonneg hC0 (GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg h0 h1))
    have h3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨hu, fun y => (abs_le.1 (hb y)).2, fun y _ => le_rfl, fun y => ?_,
      isPsh_add_rsmul A Θ th u hΘ hΘp hth hu hε hp, fun y _ _ => by linarith, fun y _ => ?_,
      fun t' htt' ht' y => ?_⟩
    · have h := abs_le.1 (hb y)
      nlinarith [hl.2]
    · have := mul_nonneg hε (he.le.trans (exp_one_le_rW L s hs y))
      linarith
    · have := hε' t' (ht.trans_le htt') ht'
      linarith

end AnMono

theorem enlarging_constants_smooth_members :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
      (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
      IsPotential A Θ → IsPosPot A Θ →
      (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧
      (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) →
        IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th →
        IsRegFamily A Θ L s th ph phT C' t₀') ∧
      ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) →
        ∃ C₀, IsSingWeight A L s th u C₀ ∧
          IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
            IsRegFamilyC2 A s u (fun _ => u) := by
  intro e X _ _ _ A Θ L s nb m W _ _ _ hs hΘ hΘpos
  have hΘp := AnMono.isPsh_of_isPosPot A Θ hΘpos
  refine ⟨fun th ph C₅ C₅' hC h => AnMono.isSingWeight_mono A L s hs th ph hC h,
    fun th ph phT C t₀ C' t₀' hC h0 h1 h2 hF hth => ?_,
    fun th u hth hu hp => AnMono.smooth_member A Θ L s hΘ hΘp hs th u hth hu hp⟩
  exact AnMono.isRegFamily_enlarge A Θ L s th ph phT hΘ hΘp hth hs hF hC h0 h1 h2

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold

theorem ent_of_lt {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) {i : ℕ} (h : i < N) :
    GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i = mu τ ⟨i, h⟩ := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.ent
  rw [dif_pos h]

theorem abs_le_norm {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) (i : Fin N) :
    |mu τ i| ≤ ‖mu‖ := by
  have h1 : ‖mu τ i‖ ≤ ‖mu τ‖ := norm_le_pi_norm (mu τ) i
  have h2 : ‖mu τ‖ ≤ ‖mu‖ := norm_le_pi_norm mu τ
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

theorem gapCond_of_threshold {T : Type} [Fintype T] {N j p : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (hp : 2 < p) (hj : 1 ≤ j) (hjN : j < N) (hd : GlobalTheory.CompanionTheory.Ar.Top.Dominant mu)
    (ht : GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu) :
    GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.NefThreshold GlobalTheory.CompanionTheory.Ar.Top.gap at ht
  unfold GlobalTheory.CompanionTheory.Ar.Top.Dominant at hd
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold GapCond
  refine ⟨?_, ‖mu‖, 4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2), ?_, ?_, ?_⟩
  · intro τ i hi hiN
    have h1 : i < N := by omega
    have h0 : i - 1 < N := by omega
    simp only [Nat.add_sub_cancel]
    rw [ent_of_lt mu τ h1, ent_of_lt mu τ h0]
    exact hd τ ⟨i - 1, h0⟩ ⟨i, h1⟩ (Fin.mk_le_mk.2 (by omega))
  · intro τ i hi hiN
    have h0 : i - 1 < N := by omega
    simp only
    rw [ent_of_lt mu τ h0]
    exact abs_le_norm mu τ _
  · intro τ
    simp only [Nat.add_sub_cancel]
    rw [div_le_iff₀ hp']
    linarith [ht τ, mul_comm ((p : ℝ) - 2) (GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (j - 1) - GlobalTheory.CompanionTheory.Ar.Top.ent mu τ j)]
  · have e : ((p : ℝ) - 2) * (4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2)) = 4 * (Fintype.card T) * ‖mu‖ := by
      field_simp
    exact e.ge

theorem lmuNum_eq_sum {T : Type} [Fintype T] {N j : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ) (hjN : j < N)
    (hx : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i)
    (hy : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) :
    lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  classical
  unfold lmuNum
  set xx : T → ℕ → ℝ := fun τ i => if h : i < N then x (τ, ⟨i, h⟩) else 0 with hxx
  have hrow : ∀ τ, ∑ i : Fin N, -mu τ i * x (τ, i) =
      ∑ i ∈ Finset.range N, -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i := by
    intro τ
    rw [← Fin.sum_univ_eq_sum_range (fun i => -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hxx, dif_pos i.isLt, ent_of_lt mu τ i.isLt]
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hrow τ, ← Finset.sum_range_add_sum_Ico _ hjN.le, Finset.sum_Ico_eq_sum_range, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.1 hi
    have hiN : i < N := by omega
    have hx' := hx τ ⟨i, hiN⟩ hij
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hx']
    ring
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmj : m < N - j := Finset.mem_range.1 hm
    have hiN : j + m < N := by omega
    have hy' := hy τ ⟨j + m, hiN⟩ (by simp)
    have e1 : N - 1 - (j + m) + 1 = N - j - m := by omega
    have e2 : N - 1 - (j + m) = N - j - m - 1 := by omega
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hy']
    rw [e1, e2]
    ring

theorem gapCond_and_lmuNum : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  intro T _ N j p mu x w l hp hj hjN hd ht hx hy
  exact ⟨gapCond_of_threshold mu hp hj hjN hd ht, lmuNum_eq_sum mu x w l hjN hx hy⟩

end GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SamePotInt

variable {D : ℕ}

theorem exists_fderiv_fderiv_re {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    ∃ B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ, ∀ v w,
      fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w = (B v w).re := by
  let Φ : ((Fin D → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ)
  have hev : (fderiv ℝ fun z => (H z).re) =ᶠ[𝓝 y] fun z => Φ (fderiv ℂ H z) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have h1 : HasFDerivAt H ((fderiv ℂ H z).restrictScalars ℝ) z :=
      hz.differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact (Complex.reCLM.hasFDerivAt.comp z h1).fderiv
  have hd : DifferentiableAt ℂ (fderiv ℂ H) y := hH.fderiv.differentiableAt
  refine ⟨fderiv ℂ (fderiv ℂ H) y, fun v w => ?_⟩
  have h2 : HasFDerivAt (fun z => Φ (fderiv ℂ H z))
      (Φ.comp ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hd.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem hessC_re_eq_zero {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    hessC (fun z => (H z).re) y = 0 := by
  obtain ⟨B, hB⟩ := exists_fderiv_fderiv_re hH
  ext i j
  simp only [hessC, Matrix.zero_apply, hB, map_smul, _root_.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  ring

theorem hessC_eq_of_eventuallyEq_add_re {a a' : (Fin D → ℂ) → ℝ} {H : (Fin D → ℂ) → ℂ}
    {y : Fin D → ℂ} (ha : ContDiffAt ℝ 2 a y) (hH : AnalyticAt ℂ H y)
    (hev : a' =ᶠ[𝓝 y] fun z => a z + (H z).re) : hessC a' y = hessC a y := by
  have hb : ContDiffAt ℝ 2 (fun z => (H z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hH.contDiffAt.restrict_scalars ℝ)
  have h2 : fderiv ℝ (fderiv ℝ a') y =
      fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ fun z => (H z).re) y := by
    have hda : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ a z :=
      (ha.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hdb : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun z => (H z).re) z :=
      (hb.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have h1 : fderiv ℝ a' =ᶠ[𝓝 y] fun z => fderiv ℝ a z + fderiv ℝ (fun z => (H z).re) z := by
      filter_upwards [hev.eventuallyEq_nhds, hda, hdb] with z hz hza hzb
      rw [hz.fderiv_eq]
      exact fderiv_add hza hzb
    rw [h1.fderiv_eq]
    exact fderiv_add ((ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have h0 := hessC_re_eq_zero hH
  rw [← add_zero (hessC a y), ← h0]
  ext i j
  simp only [hessC, Matrix.add_apply, h2, _root_.add_apply]
  push_cast
  ring

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_eq_of_samePot (A : FinHolAtlas e X) {U : Set X} {P Q : Fin e → LocPot X}
    (hPQ : ∀ i, SamePot A U (P i) (Q i)) (hC : ∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ U) :
    locDens A P j y = locDens A Q j y := by
  have key : ∀ i, hessC (fun y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro i
    obtain ⟨V, hVo, hxV, G, hG, hPQV⟩ := hPQ i _ hU
    have hsrc : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
    have ha : ContDiffAt ℝ 2 (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      have h := hC i _ hU j hsrc
      rw [(A.chart j).right_inv hy] at h
      exact h
    have hH : AnalyticAt ℂ (fun y' => G ((A.chart j).symm y')) y := hG j y ⟨hy, hxV⟩
    refine hessC_eq_of_eventuallyEq_add_re ha hH ?_
    have hV : (A.chart j).symm ⁻¹' V ∈ 𝓝 y :=
      ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hVo.mem_nhds hxV)
    filter_upwards [hV] with z hz
    exact sub_eq_iff_eq_add'.mp (hPQV _ hz)
  simp only [locDens, maDens, key]

end SamePotInt

theorem mInt_congr_samePot : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ →
    (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) →
    mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  intro e X _ _ _ A U P Q g g' hN hPQ hC hg
  have hpt : ∀ (j : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart j).target → (A.chart j).symm y ∈ U →
      g ((A.chart j).symm y) = g' ((A.chart j).symm y) ∧ locDens A P j y = locDens A Q j y :=
    fun j y hy hU => ⟨hg _ hU, SamePotInt.locDens_eq_of_samePot A hPQ hC j hy hU⟩
  have hae : ∀ (j : Fin A.n), ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin e → ℂ)),
      y ∈ (A.chart j).target → (A.chart j).symm y ∈ U := by
    intro j
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (hN j)
    intro y hy
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    exact ⟨hy.1, hy.2⟩
  constructor
  · by_cases h : Nonempty (ChartPartition A)
    · simp only [mInt, dif_pos h, integralWith]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine MeasureTheory.setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      obtain ⟨h1, h2⟩ := hpt j y hyt (hy hyt)
      simp only [h1, h2]
    · simp only [mInt, dif_neg h]
  · unfold MIntegrable
    refine forall_congr' fun j => forall_congr' fun K => forall_congr' fun hK =>
      forall_congr' fun hKc => ?_
    refine MeasureTheory.integrableOn_congr_fun_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hKc.isClosed.measurableSet]
    filter_upwards [hae j] with y hy hyK
    obtain ⟨h1, h2⟩ := hpt j y (hK hyK) (hy (hK hyK))
    simp only [h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors : ∀ (N j : ℕ), j ≤ N → IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧ ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k, (gramHead (sigForm N j) k g).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | exact GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors <;> assumption)
end
