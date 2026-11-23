module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : ℂ :=
  herm (Hpk k r) (Matrix.of x *ᵥ z') z

def pairConst (k : ℕ) (T T' : ℝ) : ℝ := 2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1))

def RhsTest : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ g : ℂ → ℝ≥0∞, Measurable g →
      rhsW k r z z' μW μW' μsec (fun x => g (pairF k r z z' x)) =
        ENNReal.ofReal (a * a') * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def PairPush : Prop :=
  ∀ (k r : ℕ) (νg : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) νg →
    ∀ z z' : Fin (2 * r + k + 1) → ℂ, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (pairF k r z z' x) ∂νg = ENNReal.ofReal (pairConst k (Tz k r z) (Tz k r z')) *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def rmulM {k r : ℕ} (p : Mat k r) (x : Mt k r) : Mt k r := Matrix.of x * p

def TransW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ p ∈ UWb k r, p *ᵥ ((Real.sqrt (Tz k r z) : ℂ) • wLast k r) = z

def UnimodW : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ p ∈ UWb k r, ν.map (rmulM p) = ν

def OrbitPushG : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z' → 0 < Tz k r z' →
    ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ f : (Fin k → ℂ) × ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg =
        ENNReal.ofReal (volU k * 2 ^ (k + 1) / Tz k r z' ^ k) * hypMeas k (Tz k r z') f

theorem volU_pos (j : ℕ) : 0 < volU j :=
  Finset.prod_pos fun i _ => by positivity

theorem continuous_pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (pairF k r z z') := by
  unfold pairF herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec
    ((show Continuous fun x : Mt k r => Matrix.of x from continuous_id).matrix_mulVec continuous_const))

theorem gauge_of_lim {k r : ℕ} (νg : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) νg)
    (hL : ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) :
    IsGaugeOn k r (UWb k r) νg := by
  refine ⟨hH, ?_⟩
  have h1 : (1 : Mat k r) ∈ UWb k r := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩⟩ <;> simp [UH]
  have e : ∀ ρ, tBall k r 1 ρ = expBall (k := k) (r := r) (UWb k r) ρ := fun ρ => by
    ext x
    simp [tBall, bBall]
  have h2 := hL 1 h1
  simp only [e] at h2
  exact h2

def annU (T T' : ℝ) : Set ℂ := {ζ | T * T' < Complex.normSq ζ ∧ Complex.normSq ζ < 4 * (T * T')}

theorem annU_open (T T' : ℝ) : IsOpen (annU T T') :=
  (isOpen_lt continuous_const Complex.continuous_normSq).inter
    (isOpen_lt Complex.continuous_normSq continuous_const)

theorem testJ (k : ℕ) (T T' : ℝ) (hTT : 0 < T * T') :
    0 < ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ∧
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ < ⊤ := by
  have hAo : IsOpen (annU T T') := annU_open T T'
  constructor
  ·
    have hVo : IsOpen {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
      (isOpen_lt continuous_const Complex.continuous_normSq).inter
        (isOpen_lt Complex.continuous_normSq continuous_const)
    have hVne : {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.Nonempty := by
      refine ⟨((Real.sqrt (5 / 2 * (T * T')) : ℝ) : ℂ), ?_, ?_⟩ <;>
        rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] <;> linarith
    have hVpos := hVo.measure_pos volume hVne
    have hle : ∀ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
        {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ ≤
        ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')
      · have hU : ζ ∈ annU T T' := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
        have hV : ζ ∈ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        rw [Set.indicator_of_mem hV, Set.indicator_of_mem hU, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos (by linarith [hζ.1])]
        exact pow_le_pow_left₀ hTT.le (by linarith [hζ.1]) _
      · have hV : ζ ∉ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        simp [Set.indicator_apply, hV]
    calc (0 : ℝ≥0∞) < ENNReal.ofReal ((T * T') ^ (k - 1)) *
          volume {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.2 (pow_pos hTT _)).ne' hVpos.ne'
      _ = ∫⁻ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
          {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ := by
          rw [lintegral_const_mul _ (measurable_one.indicator hVo.measurableSet),
            lintegral_indicator_one hVo.measurableSet]
      _ ≤ _ := lintegral_mono hle
  · have hM : ∀ ζ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ≤
        ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : ζ ∈ annU T T'
      · rw [Set.indicator_of_mem hζ, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos hζ.1.le]
        exact pow_le_pow_left₀ (by linarith [hζ.1]) (by linarith [hζ.2]) _
      · simp [Set.indicator_apply, hζ]
    have hsub : annU T T' ⊆ Metric.ball 0 (2 * Real.sqrt (T * T') + 1) := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖ζ‖ ^ 2 < (2 * Real.sqrt (T * T')) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, mul_pow, Real.sq_sqrt hTT.le]
        linarith [hζ.2]
      have h2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
      linarith
    have hfin : volume (annU T T') < ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top
    calc _ ≤ ∫⁻ ζ, ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ :=
          lintegral_mono hM
      _ = ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * volume (annU T T') := by
          rw [lintegral_const_mul _ (measurable_one.indicator hAo.measurableSet),
            lintegral_indicator_one hAo.measurableSet]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem constVal_of (hR : RhsTest) (hP : PairPush) : ConstVal := by
  intro k r z z' μW μW' a a' μsec hW νg c hH hL hrep
  have hg := gauge_of_lim νg hH hL
  have hT := hW.T_pos
  have hT' := hW.T'_pos
  have hTT : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
  have hgm : Measurable ((annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_one.indicator (annU_open _ _).measurableSet
  have hφm : Measurable (fun x => (annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)
      (pairF k r z z' x)) := hgm.comp (continuous_pairF k r z z').measurable
  have h1 := hR k r z z' μW μW' a a' μsec hW _ hgm
  have h2 := hP k r νg hW.k_pos hg z z' hW.z_mem hW.z'_mem hT hT' _ hgm
  have h3 := hrep _ hφm
  obtain ⟨hJ0, hJt⟩ := testJ k (Tz k r z) (Tz k r z') hTT
  rw [h3, h2, ← mul_assoc] at h1

  have h4 := (ENNReal.mul_left_inj hJ0.ne' hJt.ne).1 h1
  have hv := volU_pos k
  have hv1 := volU_pos (k - 1)
  have hpc : 0 < pairConst k (Tz k r z) (Tz k r z') := by
    unfold pairConst
    positivity
  have ha := hW.a_pos
  have ha' := hW.a'_pos
  have h5 := congrArg ENNReal.toReal h4
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpc.le, ENNReal.toReal_ofReal (by positivity)] at h5
  have hc : c.toReal = a * a' / pairConst k (Tz k r z) (Tz k r z') := by
    rw [← h5]
    field_simp
  rw [hc]
  unfold pairConst wbConst
  have hTk : 0 < (Tz k r z * Tz k r z') ^ k := pow_pos hTT k
  field_simp

end PI.RhsWLim.W
end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

def opBase (k r : ℕ) (T' : ℝ) : Fin (2 * r + k + 1) → ℂ := (Real.sqrt T' : ℂ) • wLast k r

def opCo (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : (Fin k → ℂ) × ℂ :=
  (fun i => v (wI k r (Fin.castSucc i)), v (wI k r (Fin.last k)))

def opOrb (k r : ℕ) (T' : ℝ) (x : Mt k r) : (Fin k → ℂ) × ℂ := opCo k r (Matrix.of x *ᵥ opBase k r T')

def opVec (k r : ℕ) (p : (Fin k → ℂ) × ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val < r + k then p.1 ⟨i.val - r, by omega⟩
  else if i.val = r + k then p.2 else 0

def opAct (k r : ℕ) (s : Mat k r) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ := opCo k r (s *ᵥ opVec k r p)

def hypS (k : ℕ) (T' : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  {p | ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2 = -T'}

def hypPar (k : ℕ) (T' : ℝ) (q : EuclideanSpace ℂ (Fin k) × ℝ) : (Fin k → ℂ) × ℂ :=
  (fun i => q.1 i, (Real.sqrt (‖q.1‖ ^ 2 + T') : ℂ) * Complex.exp (q.2 * Complex.I))

def hypM (k : ℕ) (T' : ℝ) : Measure ((Fin k → ℂ) × ℂ) :=
  (1 / 2 : ℝ≥0∞) • (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))).map (hypPar k T')

abbrev TrE (k : ℕ) := EuclideanSpace ℝ (Option (Fin k × Bool))

def opBeta (k : ℕ) (q : TrE k) (a : Fin k) : ℂ :=
  ((q (some (a, false)) : ℂ) + (q (some (a, true)) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)

def opGen (k r : ℕ) (q : TrE k) : Mat k r := fun i j =>
  if hi : r ≤ i.val ∧ i.val < r + k then (if j.val = r + k then opBeta k q ⟨i.val - r, by omega⟩ else 0)
  else if i.val = r + k then
    (if hj : r ≤ j.val ∧ j.val < r + k then star (opBeta k q ⟨j.val - r, by omega⟩)
     else if j.val = r + k then (q none : ℂ) * Complex.I else 0)
  else 0

def opE (k r : ℕ) (T' : ℝ) (ρ : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) '' Metric.ball 0 ρ

def tVol (k : ℕ) (ρ : ℝ) : ℝ := (volume (Metric.ball (0 : TrE k) ρ)).toReal

def HypInv : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ s ∈ UWb k r, (hypM k T').map (opAct k r s) = hypM k T'

def OrbRepY : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ Q : Measure ((Fin k → ℂ) × ℂ), (∀ s ∈ UWb k r, Q.map (opAct k r s) = Q) → Q (hypS k T')ᶜ = 0 →
      (∀ C, IsCompact C → Q C < ⊤) → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ Q = c • νg.map (opOrb k r T')

def GaugeK : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νK : Measure (Mt k r), IsGaugeOn k r (UWset k r (wLast k r)) νK

def TubeLimK : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg νK : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    IsGaugeOn k r (UWset k r (wLast k r)) νK →
    Tendsto (fun ρ : ℝ => (νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0)
      (𝓝 (νK Set.univ).toReal)

def HypLocal : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    Tendsto (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0) (𝓝 (T' ^ k / 2 ^ (k + 1)))

def OpEMeas : Prop :=
  ∀ (k r : ℕ) (T' : ℝ) (ρ : ℝ), MeasurableSet (opE k r T' ρ)

def HypLF : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → hypM k T' (hypS k T')ᶜ = 0 ∧ ∀ C, IsCompact C → hypM k T' C < ⊤

theorem op_volU_pos (j : ℕ) : 0 < volU j :=
  Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (Nat.cast_pos.mpr (Nat.factorial_pos i))

theorem continuous_opOrb (T' : ℝ) : Continuous (opOrb k r T') := by
  have h : Continuous fun x : PI.RhsWLim.Mt k r => Matrix.of x *ᵥ opBase k r T' :=
    Continuous.matrix_mulVec (by exact continuous_id) continuous_const
  unfold opOrb opCo
  exact (continuous_pi fun i => (continuous_apply (PI.RhsWLim.wI k r (Fin.castSucc i))).comp h).prodMk
    ((continuous_apply (PI.RhsWLim.wI k r (Fin.last k))).comp h)

theorem continuous_hypPar (k : ℕ) (T' : ℝ) : Continuous (hypPar k T') := by
  unfold hypPar
  fun_prop

theorem hypMeas_eq (k : ℕ) (T' : ℝ) {f : (Fin k → ℂ) × ℂ → ℝ≥0∞} (hf : Measurable f) :
    hypMeas k T' f = ∫⁻ p, f p ∂hypM k T' := by
  have hm : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  unfold hypM hypMeas
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_map hf hm,
    lintegral_prod (fun a => f (hypPar k T' a)) (hf.comp hm).aemeasurable]
  rfl

theorem orbitPush_of (h2 : GaugeVolUk) (hK : GaugeK) (hT : TubeLimK) (hI : HypInv) (hR : OrbRepY)
    (hL : HypLocal) (hE : OpEMeas) (hF : HypLF) : OrbitPush := by
  intro k r T' hk hT' νg hνg f hf
  obtain ⟨νK, hνK⟩ := hK k r hk
  obtain ⟨c, hctop, hc⟩ := hR k r T' hk hT' νg hνg (hypM k T')
    (hI k r T' hk hT') (hF k T' hT').1 (hF k T' hT').2
  have hmeas : Measurable (opOrb k r T') := (continuous_opOrb T').measurable
  have hU : 0 < PI.RhsWLim.volU k := op_volU_pos k
  have hK1 : (νK Set.univ).toReal = PI.RhsWLim.volU k := by
    rw [h2 k r νK hνK, ENNReal.toReal_ofReal hU.le]
  have hlim1 := hT k r T' hk hT' νg νK hνg hνK
  rw [hK1] at hlim1
  have hlim2 := hL k r T' hk hT'
  have heqfun : (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) =
      fun ρ => c.toReal * ((νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) := by
    funext ρ
    rw [hc, smul_apply, Measure.map_apply hmeas (hE k r T' ρ), smul_eq_mul, ENNReal.toReal_mul,
      mul_div_assoc]
  rw [heqfun] at hlim2
  have hkey : T' ^ k / 2 ^ (k + 1) = c.toReal * PI.RhsWLim.volU k :=
    tendsto_nhds_unique hlim2 (hlim1.const_mul c.toReal)
  have hRHS : hypMeas k T' f = c * ∫⁻ p, f p ∂(νg.map (opOrb k r T')) := by
    rw [hypMeas_eq k T' hf, hc, lintegral_smul_measure, smul_eq_mul]
  show ∫⁻ x, f (opOrb k r T' x) ∂νg = _
  rw [← lintegral_map hf hmeas, hRHS, ← mul_assoc]
  have hX : PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal = 1 := by
    have hT'k : (0 : ℝ) < T' ^ k := pow_pos hT' k
    rw [show PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal =
        2 ^ (k + 1) / T' ^ k * (c.toReal * PI.RhsWLim.volU k) by ring, ← hkey]
    field_simp
  have hcc : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
  rw [hcc, ← ENNReal.ofReal_mul (div_pos (mul_pos hU (by positivity)) (pow_pos hT' k)).le, hX,
    ENNReal.ofReal_one, one_mul]

end PI.RhsWLim.W
end
end

section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace PI.RhsWLim.W

theorem chartLim : ChartLim := by
  intro E _ _ _ _ _ _ X _ Φ ν δ hδ hδ0 hν
  obtain ⟨ε0, hε0, hν⟩ := hν
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hnhds : Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2)) ∈ 𝓝 (δ 0) :=
    ENNReal.Icc_mem_nhds hδ0 he.ne'
  obtain ⟨η1, hη1, hball⟩ := Metric.mem_nhds_iff.mp (hδ hnhds)
  refine ⟨min η1 ε0, lt_min hη1 hε0, fun {ρ} hρ hdist => ?_⟩
  have hρ0 : 0 < ρ := Set.mem_Ioi.mp hρ
  have hρ' : ρ < min η1 ε0 := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hρ0] at hdist
  have hρη : ρ < η1 := lt_of_lt_of_le hρ' (min_le_left _ _)
  have hρε : ρ < ε0 := lt_of_lt_of_le hρ' (min_le_right _ _)
  have hV0 : volume (Metric.ball (0 : E) ρ) ≠ 0 := (Metric.measure_ball_pos volume (0 : E) hρ0).ne'
  have hVt : volume (Metric.ball (0 : E) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hbd : ∀ x ∈ Metric.ball (0 : E) ρ,
      δ x ∈ Set.Icc (δ 0 - ENNReal.ofReal (ε / 2)) (δ 0 + ENNReal.ofReal (ε / 2)) :=
    fun x hx => hball (Metric.ball_subset_ball hρη.le hx)
  have hup : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≤
      (δ 0 + ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) := by
    calc ∫⁻ x in Metric.ball (0 : E) ρ, δ x
        ≤ ∫⁻ _ in Metric.ball (0 : E) ρ, (δ 0 + ENNReal.ofReal (ε / 2)) :=
          setLIntegral_mono' measurableSet_ball fun x hx => (hbd x hx).2
      _ = (δ 0 + ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) := setLIntegral_const _ _
  have hlo : (δ 0 - ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ) ≤
      ∫⁻ x in Metric.ball (0 : E) ρ, δ x := by
    calc (δ 0 - ENNReal.ofReal (ε / 2)) * volume (Metric.ball (0 : E) ρ)
        = ∫⁻ _ in Metric.ball (0 : E) ρ, (δ 0 - ENNReal.ofReal (ε / 2)) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Metric.ball (0 : E) ρ, δ x :=
          setLIntegral_mono' measurableSet_ball fun x hx => (hbd x hx).1
  have htop1 : δ 0 + ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hδ0, ENNReal.ofReal_ne_top⟩
  have hAt : ∫⁻ x in Metric.ball (0 : E) ρ, δ x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top htop1 hVt) hup
  have hVr : 0 < (volume (Metric.ball (0 : E) ρ)).toReal := ENNReal.toReal_pos hV0 hVt
  have hupR : (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal ≤
      ((δ 0).toReal + ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top htop1 hVt) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add hδ0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at h1
  have hloR : ((δ 0).toReal - ε / 2) * (volume (Metric.ball (0 : E) ρ)).toReal ≤
      (∫⁻ x in Metric.ball (0 : E) ρ, δ x).toReal := by
    have h1 := ENNReal.toReal_mono hAt hlo
    rw [ENNReal.toReal_mul] at h1
    have h2 : (δ 0).toReal - ε / 2 ≤ (δ 0 - ENNReal.ofReal (ε / 2)).toReal := by
      have h3 := ENNReal.le_toReal_sub (a := δ 0) (b := ENNReal.ofReal (ε / 2)) ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal (by linarith)] at h3
    exact le_trans (mul_le_mul_of_nonneg_right h2 hVr.le) h1
  have h4 := (div_le_iff₀ hVr).mpr hupR
  have h5 := (le_div_iff₀ hVr).mpr hloR
  rw [hν ρ hρ0 hρε, Real.dist_eq, abs_lt]
  constructor <;> linarith

end PI.RhsWLim.W
end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem rhsWLim_of (hM : MBaseMem) (hB : TBallMeas) (hG : GaugeExists) (hR : RhsHaar) (hU : HaarUniq)
    (hC : ConstVal) : RhsWLim := by
  intro k r z z' μW μW' a a' μsec hD
  have hk := hD.k_pos
  obtain ⟨νg, hνg, ⟨ε, hε, hpos⟩, hlim⟩ := hG k r hk
  obtain ⟨ν, hν, ⟨ε', hε', hfin⟩, hrep⟩ := hR k r z z' μW μW' a a' μsec hD
  obtain ⟨c, hc, hνc⟩ := hU k r ν νg hk hν hνg ⟨min ε ε', lt_min hε hε', fun ρ h0 hlt =>
    ⟨hfin ρ h0 (lt_of_lt_of_le hlt (min_le_right _ _)),
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).1,
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).2⟩⟩
  have hrep' : ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      rhsW k r z z' μW μW' μsec φ = c * ∫⁻ x, φ x ∂νg := by
    intro φ hφ
    rw [hrep φ hφ, hνc, lintegral_smul_measure, smul_eq_mul]
  have hcv := hC k r z z' μW μW' a a' μsec hD νg c hνg hlim hrep'
  have hm := hM k r z z' μW μW' a a' μsec hD
  have hmeas : ∀ ρ, MeasurableSet (mBall k r z z' μsec ρ) := fun ρ => hB k r (mBase k r z z' μsec) ρ
  have heq : ∀ ρ, (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ
      = c.toReal * ((νg (tBall k r (mBase k r z z' μsec) ρ)).toReal / bVol k r ρ) := by
    intro ρ
    rw [hrep' _ (measurable_one.indicator (hmeas ρ)), lintegral_indicator_one (hmeas ρ),
      ENNReal.toReal_mul, mul_div_assoc]
    all_goals rfl
  refine (tendsto_congr heq).2 ?_
  rw [← hcv]
  have := (hlim _ hm).const_mul c.toReal
  rw [mul_one] at this
  exact this

end PI.RhsWLim.W
end
end

section

noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem volURatio : VolURatio := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [volU, Finset.prod_range_succ, Nat.add_sub_cancel]
  ring

end PI.RhsWLim.W
end
end
