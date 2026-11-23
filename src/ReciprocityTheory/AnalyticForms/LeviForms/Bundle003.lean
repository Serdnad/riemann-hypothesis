module

public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChartA
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006

@[expose] public section

section

namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma log_term_nonneg {x : ℂ} (hx : ‖x‖ ≤ 2) : 0 ≤ Real.log (4 / ‖x‖ ^ 2) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h]; simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; nlinarith

lemma rLoc_ge (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    Real.exp 1 ≤ rLoc S m x := by
  unfold rLoc
  have : 0 ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (log_term_nonneg (hx i))
  linarith

lemma rLoc_pos (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    0 < rLoc S m x := (Real.exp_pos 1).trans_le (rLoc_ge S m hx)

lemma norm_coord_le_of_ball {R : ℝ} (hR : R ≤ 2) {x : Fin D → ℂ} (hx : x ∈ ball (0 : Fin D → ℂ) R)
    (i : Fin D) : ‖x i‖ ≤ 2 :=
  (norm_le_pi_norm x i).trans ((mem_ball_zero_iff.1 hx).le.trans hR)

def mTot (S : Finset (Fin D)) (m : Fin D → ℕ) : ℝ := ∑ i ∈ S, (m i : ℝ)

lemma mTot_nonneg (S : Finset (Fin D)) (m : Fin D → ℕ) : 0 ≤ mTot S m :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma rLoc_le_far (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} {s : ℝ} (hs : 0 < s)
    (hx : ∀ i, s ≤ ‖x i‖) : rLoc S m x ≤ Real.exp 1 + mTot S m * Real.log (4 / s ^ 2) := by
  unfold rLoc mTot
  rw [Finset.sum_mul]
  have : ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / s ^ 2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos (by norm_num) (pow_pos (hs.trans_le (hx i)) 2))
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hs 2) (pow_le_pow_left₀ hs.le (hx i) 2)))
      (Nat.cast_nonneg _)
  linarith

def pmoff (S : Finset (Fin D)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' (closedBall z t \ coordDiv S))

section Osc

variable {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}

lemma pmo_bdd (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) : BddAbove (u '' (closedBall z s \ coordDiv S)) :=
  ⟨C₅, by rintro _ ⟨x, hx, rfl⟩; exact hub x ⟨hs hx.1, hx.2⟩⟩

lemma pmo_nonempty (z : Fin D → ℂ) {s : ℝ} (hs : 0 < s) :
    (u '' (closedBall z s \ coordDiv S)).Nonempty := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  exact ⟨u x, x, ⟨hx, not_mem_coordDiv_of hs hf⟩, rfl⟩

lemma le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) {x : Fin D → ℂ} (hx : x ∈ closedBall z s \ coordDiv S) :
    u x ≤ pmoff S u z s :=
  le_csSup (pmo_bdd hub hs) (mem_image_of_mem u hx)

lemma pmo_le (z : Fin D → ℂ) {s c : ℝ} (hs : 0 < s) (h : ∀ x ∈ closedBall z s \ coordDiv S, u x ≤ c) :
    pmoff S u z s ≤ c :=
  csSup_le (pmo_nonempty z hs) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

lemma pmo_mono (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ}
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (hs' : closedBall z s' ⊆ ball 0 R) :
    pmoff S u z s ≤ pmoff S u z s' :=
  csSup_le_csSup (pmo_bdd hub hs') (pmo_nonempty z hs)
    (image_mono (sdiff_subset_sdiff_left (closedBall_subset_closedBall hss)))

lemma pmo_lower (hR : R ≤ 2) (hC₅ : 0 ≤ C₅) (m : Fin D → ℕ)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅)
    {z : Fin D → ℂ} {s : ℝ} (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    -C₅ * Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) ≤ pmoff S u z s := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  have hxA : x ∉ coordDiv S := not_mem_coordDiv_of hs hf
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR hx
  refine le_trans ?_ (le_pmo (fun y hy => (hb y hy).2) hsR ⟨hx, hxA⟩)
  refine le_trans ?_ (hb x ⟨hxB, hxA⟩).1
  have h1 := rLoc_pos S m (norm_coord_le_of_ball hR hxB)
  have h2 := rLoc_le_far S m hs hf
  have : Real.log (rLoc S m x) ≤ Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) :=
    Real.log_le_log h1 h2
  nlinarith

lemma pmo_le_polyMax {w : (Fin D → ℂ) → ℝ} (hw : UpperSemicontinuousOn w (ball 0 R))
    (hwu : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ w x) {z : Fin D → ℂ} {s : ℝ}
    (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    pmoff S u z s ≤ polyMax w z s :=
  pmo_le z hs fun x hx => (hwu x ⟨hsR hx.1, hx.2⟩).trans (le_polyMax hw hsR hx.1)

lemma polyMax_le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅)
    {w : (Fin D → ℂ) → ℝ} {κ : ℝ}
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0, ∃ y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') (hsR : closedBall z s' ⊆ ball 0 R) :
    polyMax w z s ≤ max (pmoff S u z s') (-κ) := by
  refine polyMax_le' hs fun x hx => ?_
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR (closedBall_subset_closedBall hss.le hx)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨y, hy, hyd, hwy⟩ := hW3 x hxB (min δ (s' - s)) (lt_min hδ (by linarith))
  have hyz : y ∈ closedBall z s' := by
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle y x z
    linarith [min_le_right δ (s' - s)]
  have : u y ≤ pmoff S u z s' := le_pmo hub hsR ⟨hyz, hy.2⟩
  have : max (u y) (-κ) ≤ max (pmoff S u z s') (-κ) := max_le_max this le_rfl
  linarith [min_le_left δ (s' - s)]

end Osc

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
end

section

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

namespace TailBoundAlt

theorem bdry_rW_meas {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L)
    (hs : IsSection A L s) : MeasurableSet (bdry s) ∧ Measurable (rW L s) := by
  classical
  obtain ⟨hrc, -⟩ := rW_open A L s hL hs
  have hbm : MeasurableSet (bdry s) := (LeviFormBoundaryTopology.isClosed_bdry hs).measurableSet
  refine ⟨hbm, ?_⟩
  have heq : rW L s = (bdry s)ᶜ.piecewise (rW L s) (fun _ => Real.exp 1) := by
    funext y
    by_cases hy : y ∈ bdry s
    · have hy' : s y y = 0 := hy
      simp [Set.piecewise, hy, rW, logNormSec, hy']
    · simp [Set.piecewise, hy]
  rw [heq]
  exact ContinuousOn.measurable_piecewise hrc continuousOn_const hbm.compl

theorem lintegral_rW_le {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (hΦ : ∀ i, IsPotential A (Φ i))
    (hΦp : ∀ i, IsPsh A (Φ i)) (hL : IsPotential A L) (hs : IsSection A L s)
    (hsnc : IsSNC A L s m W) (hle : ∀ y, logNormSec L s y ≤ 0) :
    ∫⁻ y in (bdry s)ᶜ, ENNReal.ofReal (rW L s y) ∂maMeasure A Φ ≤
      ENNReal.ofReal (Real.exp 1 * mInt A Φ (fun _ => 1) - 2 * mInt A Φ (logNormSec L s)) := by
  obtain ⟨-, hrm⟩ := bdry_rW_meas A L s hL hs
  have hlm : Measurable (logNormSec L s) := by
    have : logNormSec L s = fun y => (Real.exp 1 - rW L s y) / 2 := by
      funext y; simp only [rW]; ring
    rw [this]
    exact (measurable_const.sub hrm).div_const 2
  have hforward {g : X → ℝ} (hg : Measurable g) (hgi : MIntegrable A Φ g) :
      Integrable g (maMeasure A Φ) ∧ mInt A Φ g = ∫ y, g y ∂maMeasure A Φ := by
    by_cases hP : Nonempty (ChartPartition A)
    · have hμ : maMeasure A Φ = ∑ j, chartMeasure A hP.some Φ j := by
        simp [maMeasure, hP, chartMeasure]
      have hc j := chartMeasure_integrable_integral A hP.some Φ hΦ hΦp j hg hgi
      rw [hμ]
      refine ⟨integrable_finsetSum_measure.2 fun j _ => (hc j).1, ?_⟩
      rw [integral_finsetSum_measure fun j _ => (hc j).1]
      simp only [mInt, dif_pos hP, integralWith]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hc j).2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    · simp [maMeasure, mInt, hP]
  have hlI := logNormIntegrable A L s m W hL hs hsnc Φ hΦ
  obtain ⟨hI, h2⟩ := hforward hlm hlI
  obtain ⟨hI1, h1⟩ := hforward (g := fun _ => (1 : ℝ)) measurable_const
    (mIntegrableCont A Φ hΦ _ continuous_const)
  letI : IsFiniteMeasure (maMeasure A Φ) := (integrable_const_iff_isFiniteMeasure one_ne_zero).1 hI1
  have hrI : Integrable (rW L s) (maMeasure A Φ) := (integrable_const _).sub (hI.const_mul 2)
  have hr0 : 0 ≤ᵐ[maMeasure A Φ] rW L s := Filter.Eventually.of_forall fun y =>
    le_trans (Real.exp_pos 1).le (rW_ge L s hle y)
  calc ∫⁻ y in (bdry s)ᶜ, ENNReal.ofReal (rW L s y) ∂maMeasure A Φ
      ≤ ∫⁻ y, ENNReal.ofReal (rW L s y) ∂maMeasure A Φ := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ y, rW L s y ∂maMeasure A Φ) :=
        (ofReal_integral_eq_lintegral_ofReal hrI hr0).symm
    _ = _ := by
        congr 1
        rw [h1, h2]
        have : ∫ y, rW L s y ∂maMeasure A Φ =
            ∫ y, (Real.exp 1 - 2 * logNormSec L s y) ∂maMeasure A Φ := rfl
        rw [this, integral_sub (integrable_const _) (hI.const_mul 2), integral_const_mul,
          integral_const, integral_const, smul_eq_mul, smul_eq_mul]
        ring

theorem cons_pot {e : ℕ} {X : Type} [TopologicalSpace X] (_A : FinHolAtlas (e + 1) X)
    (p : LocPot X → Prop) (Q : LocPot X) (Φ : Fin e → LocPot X) (hQ : p Q) (hΦ : ∀ i, p (Φ i)) :
    ∀ i, p ((Fin.cons Q Φ : Fin (e + 1) → LocPot X) i) := by
  intro i
  induction i using Fin.cases with
  | zero => simpa using hQ
  | succ i => simpa using hΦ i

end TailBoundAlt

end

end ReciprocityTheory.AnForm.P
end

section

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def MIntUpdateAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (P Q : LocPot X),
    (∀ i, IsPotential A (F i)) → IsPotential A P → IsPotential A Q → ∀ g : X → ℝ, Continuous g →
      mInt A (Function.update F k (P + Q)) g =
        mInt A (Function.update F k P) g + mInt A (Function.update F k Q) g

theorem update_comp_swap {e : ℕ} {X : Type} [TopologicalSpace X] (F : Fin (e + 1) → LocPot X)
    (k : Fin (e + 1)) (P : LocPot X) :
    Function.update F k P ∘ Equiv.swap 0 k = Fin.cons P (Fin.tail (F ∘ Equiv.swap 0 k)) := by
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ, Fin.tail]
    rw [Function.update_of_ne]
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact Fin.succ_ne_zero j'

theorem mInt_update_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (P : LocPot X) (g : X → ℝ) :
    mInt A (Function.update F k P) g = mInt A (Fin.cons P (Fin.tail (F ∘ Equiv.swap 0 k))) g := by
  rw [← update_comp_swap, mIntSymm]

theorem mInt_update_add : MIntUpdateAddStatement := by
  intro e X _ _ _ A F k P Q hF hP hQ g hg
  have hΦ : ∀ i, IsPotential A (Fin.tail (F ∘ Equiv.swap 0 k) i) := fun i => hF _
  rw [mInt_update_eq, mInt_update_eq A F k P, mInt_update_eq A F k Q]
  exact mIntAdd A P Q _ hP hQ hΦ g (mIntegrableCont A _ (fun i => Fin.cases hP hΦ i) g hg)
    (mIntegrableCont A _ (fun i => Fin.cases hQ hΦ i) g hg)

end

end ReciprocityTheory.AnForm.P
end
