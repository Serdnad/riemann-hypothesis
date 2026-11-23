module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LintegralMulRightOfMem
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Formalism.PeriodIntegrals.Bundle003
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  apply PI.AprimeInfA.polish_of_lcsc <;> assumption

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem meas_avg (H : Subgroup G) (ν : Measure H) [SFinite ν] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun g : G => ∫⁻ h, f (g * (h : G)) ∂ν) := by
  have hc : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
    continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
  exact (hf.comp hc.measurable).lintegral_prod_right'

theorem avg_mul_mem (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞)
    (g : G) (k : H) : ∫⁻ h, f (g * k * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  have := lintegral_mul_left_eq_self (μ := ν) (fun h : H => f (g * (h : G))) k
  simpa [mul_assoc] using this

theorem avg_out (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hk]
  exact avg_mul_mem H ν f g k

theorem meas_avg_q (H : Subgroup G) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => ∫⁻ h, f (q.out * (h : G)) ∂ν) ∘ Quotient.mk'') =
      fun g => ∫⁻ h, f (g * (h : G)) ∂ν := by
    funext g
    exact avg_out H ν f g
  rw [this]
  exact meas_avg H ν hf

theorem lint_eq (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant] [IsFiniteMeasure ν]
    (μ : Measure G) [SFinite μ] (hr : ∀ k : H, μ.map (· * (k : G)) = μ) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ν univ * ∫⁻ g, f g ∂μ =
      ∫⁻ q, (∫⁻ h, f (q.out * (h : G)) ∂ν) ∂(μ.map (QuotientGroup.mk : G → G ⧸ H)) := by
  rw [lintegral_map (meas_avg_q H ν hf) measurable_quotient_mk'']
  have e1 : ∀ g : G, ∫⁻ h, f ((g : G ⧸ H).out * (h : G)) ∂ν = ∫⁻ h, f (g * (h : G)) ∂ν := avg_out H ν f
  rw [lintegral_congr e1]
  have hmeas2 : AEMeasurable (Function.uncurry fun (g : G) (h : H) => f (g * (h : G))) (μ.prod ν) := by
    have hc2 : Continuous (fun p : G × H => p.1 * (p.2 : G)) :=
      continuous_fst.mul (continuous_subtype_val.comp continuous_snd)
    exact (hf.comp hc2.measurable).aemeasurable
  rw [lintegral_lintegral_swap hmeas2]
  have : ∀ h : H, ∫⁻ g, f (g * (h : G)) ∂μ = ∫⁻ g, f g ∂μ := fun h => by
    rw [← lintegral_map hf (measurable_mul_const (h : G)), hr h]
  rw [lintegral_congr this, lintegral_const, mul_comm]

variable {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

def iotaQ (H : Subgroup G) (p : G → X) (q : G ⧸ H) : X := p q.out

theorem desc_uniq (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsMulLeftInvariant]
    (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) (p : G → X) (hp : Continuous p)
    (hpH : ∀ g g' : G, p g = p g' ↔ g⁻¹ * g' ∈ H) (μ₁ μ₂ : Measure G) [SFinite μ₁] [SFinite μ₂]
    (h₁ : ∀ k : H, μ₁.map (· * (k : G)) = μ₁) (h₂ : ∀ k : H, μ₂.map (· * (k : G)) = μ₂)
    (hm : μ₁.map p = μ₂.map p) : μ₁ = μ₂ := by
  classical
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hfin⟩
  haveI : IsClosed (H : Set G) := hH
  haveI : PolishSpace G := polish_of_lcsc G
  haveI : PolishSpace (G ⧸ H) := polish_of_lcsc _
  haveI : BorelSpace (G ⧸ H) := CosetSpace.borelSpace
  have hmk : ∀ g : G, iotaQ H p (g : G ⧸ H) = p g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H g
    show p (g : G ⧸ H).out = p g
    rw [hk]
    refine ((hpH g (g * k)).2 ?_).symm
    rw [inv_mul_cancel_left]
    exact k.2
  have hcomp : (iotaQ H p ∘ (QuotientGroup.mk : G → G ⧸ H)) = p := funext hmk
  have hιc : Continuous (iotaQ H p) := by
    rw [(QuotientGroup.isQuotientMap_mk H).continuous_iff, hcomp]
    exact hp
  have hinj : Function.Injective (iotaQ H p) := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact (hpH _ _).1 h
  have hemb : MeasurableEmbedding (iotaQ H p) := hιc.measurableEmbedding hinj
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ H) := measurable_quotient_mk''
  have hq : μ₁.map (QuotientGroup.mk : G → G ⧸ H) = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := by
    calc μ₁.map (QuotientGroup.mk : G → G ⧸ H)
        = ((μ₁.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) :=
          (hemb.comap_map _).symm
      _ = (μ₁.map p).comap (iotaQ H p) := by rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = (μ₂.map p).comap (iotaQ H p) := by rw [hm]
      _ = ((μ₂.map (QuotientGroup.mk : G → G ⧸ H)).map (iotaQ H p)).comap (iotaQ H p) := by
          rw [Measure.map_map hemb.measurable hπ, hcomp]
      _ = μ₂.map (QuotientGroup.mk : G → G ⧸ H) := hemb.comap_map _
  ext S hS
  have hf : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hS
  have e1 := lint_eq H ν μ₁ h₁ _ hf
  have e2 := lint_eq H ν μ₂ h₂ _ hf
  rw [hq, ← e2, lintegral_indicator_one hS, lintegral_indicator_one hS] at e1
  exact (ENNReal.mul_right_inj h0 hfin).1 e1

end Abstract

end PI.RhsWLim.W.RI
end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def tBall (k r : ℕ) (m : Mat k r) (ρ : ℝ) : Set (Mt k r) :=
  {x | (fun i j => (m⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}

def MBaseMem : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → mBase k r z z' μsec ∈ UWb k r

def TBallMeas : Prop :=
  ∀ (k r : ℕ) (m : Mat k r) (ρ : ℝ), MeasurableSet (tBall k r m ρ)

def GaugeExists : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νg : Measure (Mt k r), IsHaarOn (UWb k r) νg ∧
    (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → 0 < νg (bBall k r ρ) ∧ νg (bBall k r ρ) < ⊤) ∧
    ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)

def RhsHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∃ ν : Measure (Mt k r), IsHaarOn (UWb k r) ν ∧
      (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (bBall k r ρ) < ⊤) ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → rhsW k r z z' μW μW' μsec φ = ∫⁻ x, φ x ∂ν

def HaarUniq : Prop :=
  ∀ (k r : ℕ) (ν₁ ν₂ : Measure (Mt k r)), 1 ≤ k → IsHaarOn (UWb k r) ν₁ → IsHaarOn (UWb k r) ν₂ →
    (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε →
      ν₁ (bBall k r ρ) < ⊤ ∧ 0 < ν₂ (bBall k r ρ) ∧ ν₂ (bBall k r ρ) < ⊤) →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ν₁ = c • ν₂

def ConstVal : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ (νg : Measure (Mt k r)) (c : ℝ≥0∞),
      IsHaarOn (UWb k r) νg →
      (∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) →
      (∀ φ : Mt k r → ℝ≥0∞, Measurable φ → rhsW k r z z' μW μW' μsec φ = c * ∫⁻ x, φ x ∂νg) →
      c.toReal = (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹

def sVol (k r : ℕ) (S : Set (Mat k r)) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : lieE S) ρ)).toReal

def IsGaugeOn (k r : ℕ) (S : Set (Mat k r)) (ν : Measure (Mt k r)) : Prop :=
  IsHaarOn S ν ∧ Tendsto (fun ρ : ℝ => (ν (expBall (k := k) (r := r) S ρ)).toReal / sVol k r S ρ) (𝓝[>] 0) (𝓝 1)

def wLast (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))

def GaugeVolUk : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), IsGaugeOn k r (UWset k r (wLast k r)) ν →
    ν Set.univ = ENNReal.ofReal (volU k)

def hypMeas (k : ℕ) (T' : ℝ) (f : (Fin k → ℂ) × ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∫⁻ y : EuclideanSpace ℂ (Fin k), ∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
    f (fun i => y i, (Real.sqrt (‖y‖ ^ 2 + T') : ℂ) * Complex.exp (θ * Complex.I))

def OrbitPush : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ f : (Fin k → ℂ) × ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (fun i => (Matrix.of x *ᵥ ((Real.sqrt T' : ℂ) • wLast k r)) (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ ((Real.sqrt T' : ℂ) • wLast k r)) (wI k r (Fin.last k))) ∂νg =
        ENNReal.ofReal (volU k * 2 ^ (k + 1) / T' ^ k) * hypMeas k T' f

def PolarHyp : Prop :=
  ∀ (k : ℕ) (T T' : ℝ), 1 ≤ k → 0 < T → 0 < T' → ∀ g : ℝ → ℂ → ℝ≥0∞, Measurable (Function.uncurry g) →
    hypMeas k T' (fun v => g ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) =
      ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * T ^ k)) *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) *
          g (Real.sqrt ((Complex.normSq ζ - T * T') / T)) (-(ζ / (Real.sqrt T : ℂ)))

def VolURatio : Prop :=
  ∀ k : ℕ, 1 ≤ k → volU k = volU (k - 1) * (2 * Real.pi) ^ k / ((k - 1).factorial : ℝ)

def ChartLim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] (X : Type) [MeasurableSpace X] (Φ : E → X) (ν : Measure X) (δ : E → ℝ≥0∞),
    ContinuousAt δ 0 → δ 0 ≠ ⊤ →
    (∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (Φ '' Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x) →
    Tendsto (fun ρ : ℝ => (ν (Φ '' Metric.ball 0 ρ)).toReal / (volume (Metric.ball (0 : E) ρ)).toReal)
      (𝓝[>] 0) (𝓝 (δ 0).toReal)

def ChartJac : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] (Φ : E → E) (ν : Measure E) (δ : E → ℝ≥0∞),
    ContDiffAt ℝ 1 Φ 0 → (fderiv ℝ Φ 0).det ≠ 0 → ContinuousAt δ (Φ 0) → δ (Φ 0) ≠ ⊤ →
    (∃ U ∈ 𝓝 (Φ 0), ∀ A ⊆ U, MeasurableSet A → ν A = ∫⁻ x in A, δ x) →
    Tendsto (fun ρ : ℝ => (ν (Φ '' Metric.ball 0 ρ)).toReal / (volume (Metric.ball (0 : E) ρ)).toReal)
      (𝓝[>] 0) (𝓝 ((δ (Φ 0)).toReal * |(fderiv ℝ Φ 0).det|))

end PI.RhsWLim.W
end
end
