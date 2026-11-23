module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle156
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormula
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle145
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle151
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle148
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle147
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_potential_from_snc_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), Adapted M P S → FromSnc M P → ∃ (r : M.Xc → ℝ) (f : Fin P.N → (Fin D.n → ℂ) → ℝ) (Bf : ℝ), (∀ z ∈ D.Xo, 1 ≤ r (M.proj z)) ∧ (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) (P.chart j).target ∧ ∀ y ∈ (P.chart j).target, |f j y| ≤ Bf) ∧ ∀ j, ∀ y ∈ (P.chart j).target \ ReciprocityTheory.AnForm.A.coordDiv (S j), r ((P.chart j).symm y) = Real.exp 1 + f j y + ∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_potential_from_snc_charts | exact GlobalTheory.CompanionTheory.Relay.exists_potential_from_snc_charts | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_potential_from_snc_charts <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_cover_arithmetic_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a ∧ D ∉ mCoordIdeal M.x ∧ ∀ zb ∈ mcPts (mCoordIdeal M.x), eval zb (map (Int.castRingHom ℂ) D) ≠ 0 → (GroundTheory.Heights₂.Heights.Inter.ptsOverPt (mCoordIdeal M'.x) Cv.v zb).ncard = Cv.deg := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BaseCount.base_count | exact GlobalTheory.CompanionTheory.Ar.PB.BaseCount.base_count | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BaseCount.base_count <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem realis_bijective_of_degree_one : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), Re.deg = 1 → Re.br = ∅ → Function.Bijective Re.π := by
  intro K _ ι _ D σ S P Re h1 h2
  have hd := Re.degree
  rw [h1, h2] at hd
  obtain ⟨g, hgl, hgr, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one S.A Re.R.A Re.π Re.holo hd
  exact Function.bijective_iff_has_inverse.2 ⟨g, hgl, hgr⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_pullback_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_pullback_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main <;> assumption)
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Helpers

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_eq_of_orbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem affCoord_cj (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) :
    affCoord p (cj z) = cj (affCoord p z) := by
  funext q
  simp [affCoord, cj, map_div₀]

theorem ne_zero_of_orbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z (cj z')) {q : Σ k, ι k}
    (hq : z q ≠ 0) : z' q ≠ 0 := by
  obtain ⟨c, -, rfl⟩ := h
  intro h0
  exact hq (by simp [cj, h0])

theorem analyticAt_affCoord {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → (Σ k, ι k) → ℂ} {a : E} (p : (k : K) → ι k)
    (hf : ∀ q, AnalyticAt ℂ (fun y => f y q) a) (h0 : ∀ k, f a ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun y => affCoord p (f y)) a := by
  rw [analyticAt_pi_iff]
  intro q
  exact (hf q).div (hf ⟨q.1, p q.1⟩) (h0 q.1)

theorem analyticAt_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : AnalyticAt ℂ ψ w) : AnalyticAt ℂ (star ∘ ψ ∘ star) (star w) := by
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  have hs : Filter.Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star w)) (𝓝 w) := by
    simpa using (continuous_star.tendsto (star w))
  filter_upwards [hs.eventually h.eventually_analyticAt] with v hv
  simpa using hv.differentiableAt.star_star

theorem ker_fderiv_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : DifferentiableAt ℂ ψ w) (hk : (fderiv ℂ ψ w).ker = ⊥) :
    (fderiv ℂ (star ∘ ψ ∘ star) (star w)).ker = ⊥ := by
  rw [h.hasFDerivAt.star_star.fderiv, eq_bot_iff]
  intro v hv
  have hv' : star (fderiv ℂ ψ w (star v)) = 0 := by simpa using hv
  have h1 : fderiv ℂ ψ w (star v) = 0 := by simpa using hv'
  have h2 : star v ∈ (fderiv ℂ ψ w).ker := by simpa using h1
  rw [hk] at h2
  have h3 : star v = 0 := by simpa using h2
  simpa using h3

end Helpers

theorem conj_analytic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)) := by
  intro K _ ι _ e X _ A P U lift hL c hc hcc j k w hw
  obtain ⟨hUo, hUm, hH, hM, hCp, -, -, hIm⟩ := hL
  obtain ⟨hw1, hw2⟩ := hw
  have hw2' : c ((A.chart j).symm w) ∈ (A.chart k).source := hw2
  generalize hx₀ : (A.chart j).symm w = x₀ at hw2'
  generalize hx₁ : c x₀ = x₁ at hw2'
  choose p hp using (hM x₁ x₁ (hUm x₁)).1
  have hp0 : ∀ b, lift x₀ x₀ ⟨b, p b⟩ ≠ 0 := fun b =>
    ne_zero_of_orbit_cj (hx₁ ▸ hc x₀) (by subst hx₁; exact hp b)
  have hsym₁ : (A.chart k).symm (A.chart k x₁) = x₁ := (A.chart k).left_inv hw2'
  have hψ : AnalyticAt ℂ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) (A.chart k x₁) := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₁ q k (A.chart k x₁) ⟨(A.chart k).map_source hw2', by simpa [hsym₁] using hUm x₁⟩
    · simpa [hsym₁] using hp b
  have hker := hIm x₁ p hp k hw2'
  have hHa : AnalyticAt ℂ (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₀ q j w ⟨hw1, by simpa [Set.mem_preimage, hx₀] using hUm x₀⟩
    · simpa [hx₀] using hp0 b
  have hsc : ContinuousAt (A.chart j).symm w := (A.chart j).continuousAt_symm hw1
  have hcs : ContinuousAt (fun y => c ((A.chart j).symm y)) w := hcc.continuousAt.comp hsc
  have hFc : ContinuousAt (fun z => star (A.chart k (c ((A.chart j).symm z)))) w := by
    have h1 : ContinuousAt (A.chart k) (c ((A.chart j).symm w)) := by
      rw [hx₀, hx₁]; exact (A.chart k).continuousAt hw2'
    exact continuous_star.continuousAt.comp (ContinuousAt.comp (f := fun y => c ((A.chart j).symm y)) h1 hcs)
  have hFw : star (A.chart k (c ((A.chart j).symm w))) = star (A.chart k x₁) := by
    rw [hx₀, hx₁]
  have e1 : ∀ᶠ y in 𝓝 w, (A.chart j).symm y ∈ U x₀ :=
    hsc ((hUo x₀).mem_nhds (by rw [hx₀]; exact hUm x₀))
  have e2 : ∀ᶠ y in 𝓝 w, c ((A.chart j).symm y) ∈ (A.chart k).source ∩ U x₁ :=
    hcs (((A.chart k).open_source.inter (hUo x₁)).mem_nhds (by
      change c ((A.chart j).symm w) ∈ _
      rw [hx₀, hx₁]; exact ⟨hw2', hUm x₁⟩))
  refine GlobalTheory.T.analytic_of_immersion_composition (fun z => star (A.chart k (c ((A.chart j).symm z))))
    (star ∘ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) ∘ star)
    (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w ?_ ?_ hHa hFc ?_
  · rw [hFw]; exact analyticAt_star_comp hψ
  · rw [hFw]; exact ker_fderiv_star_comp hψ.differentiableAt hker
  · filter_upwards [e1, e2] with y h1 h2
    obtain ⟨h2s, h2u⟩ := h2
    generalize hy' : (A.chart j).symm y = y' at h1 h2s h2u
    have ho1 : SameOrbit (lift x₁ (c y')) (lift (c y') (c y')) := hCp _ _ _ ⟨h2u, hUm _⟩
    have ho2 : SameOrbit (lift y' y') (lift x₀ y') := hCp _ _ _ ⟨hUm _, h1⟩
    have ho : SameOrbit (lift x₁ (c y')) (cj (lift x₀ y')) :=
      sameOrbit_trans ho1 (sameOrbit_trans (hc y') (sameOrbit_cj ho2))
    have hst : (star : ((Σ k, ι k) → ℂ) → _) (cj (affCoord p (lift x₀ y'))) = affCoord p (lift x₀ y') := by
      funext q; simp [cj]
    simp only [Function.comp, star_star, hy', (A.chart k).left_inv h2s]
    rw [affCoord_eq_of_orbit p ho, affCoord_cj, hst]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.biholomorphic_lift_system : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}, J = ⊤ → ∀ {e : ℕ} (R : AnLogRes P J e) {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X), (∀ y, g (h y) = y) → (∀ x, h (g x) = x) → HoloMap A R.A g → HoloMap R.A A h → IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top <;> assumption)
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.lift_system_complex_conjugation : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧ ∀ x, c (c x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_divisor_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → 𝔐.IsCover d → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ∃ Fl : 𝔐'.Flag, Fl.deg = d ∧ ColFlags 𝔐 bW bO j Fl := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace MuPos

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
      ⋂ k, ⋃ i, {z : (Σ k, J k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_logH {A : HermLine J} (hA : IsSmoothHerm A) {n : ℕ}
    {g : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (hg : AnalyticAt ℂ g t)
    (hz : ∀ k, ∃ i, g t ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun s => Real.log (A.h (g s))) t := by
  have h1 : ContDiffAt ℝ 2 A.h (g t) :=
    ((hA.contDiffAt (isOpen_blockNonzero.mem_nhds hz)).of_le (by norm_cast))
  have h2 : ContDiffAt ℝ 2 g t := hg.restrictScalars.contDiffAt
  exact (h1.comp t h2).log (A.pos _ hz).ne'

theorem levi_const_mul {n : ℕ} {f : (Fin n → ℂ) → ℝ} {t : Fin n → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f t)
    (v : Fin n → ℂ) : levi (fun y => c * f y) t v = c * levi f t v := by
  have h := ReciprocityTheory.AnForm.levi_add_smul c (contDiffAt_const (c := (0 : ℝ))) hf v
  simp only [zero_add] at h
  rw [h]
  simp [levi]

theorem exists_analytic_sum {n : ℕ} (s : Finset ℕ) (f : ℕ → (Fin n → ℂ) → ℝ) (t : Fin n → ℂ)
    (h : ∀ r ∈ s, ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ u in 𝓝 t, f r u = (G u).re) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ u in 𝓝 t, ∑ r ∈ s, f r u = (G u).re := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, analyticAt_const, by simp⟩
  | insert r s hr ih =>
    obtain ⟨G₁, hG₁, e₁⟩ := h r (Finset.mem_insert_self r s)
    obtain ⟨G₂, hG₂, e₂⟩ := ih fun r' hr' => h r' (Finset.mem_insert_of_mem hr')
    refine ⟨fun u => G₁ u + G₂ u, hG₁.add hG₂, ?_⟩
    filter_upwards [e₁, e₂] with u h₁ h₂
    rw [Finset.sum_insert hr, h₁, h₂, Complex.add_re]

theorem levi_split {n : ℕ} {fM fA F : (Fin n → ℂ) → ℝ} {G : (Fin n → ℂ) → ℂ} {t : Fin n → ℂ} {p q : ℝ}
    (hq : q ≠ 0) (hM : ContDiffAt ℝ 2 fM t) (hA : ContDiffAt ℝ 2 fA t) (hG : AnalyticAt ℂ G t)
    (hE : ∀ᶠ s in 𝓝 t, fM s = q * (F s + (G s).re) + p * fA s) (v : Fin n → ℂ) :
    levi fM t v = q * levi F t v + p * levi fA t v := by
  have hRe : ContDiffAt ℝ 2 (fun y => (G y).re) t :=
    Complex.reCLM.contDiff.contDiffAt.comp t (hG.restrictScalars.contDiffAt)
  have hMA : ContDiffAt ℝ 2 (fun y => fM y + (-p) * fA y) t := hM.add (contDiffAt_const.mul hA)
  have hR : ContDiffAt ℝ 2 (fun y => (fM y + (-p) * fA y) + (-q) * (G y).re) t :=
    hMA.add (contDiffAt_const.mul hRe)
  have hF : F =ᶠ[𝓝 t] fun y => q⁻¹ * ((fM y + (-p) * fA y) + (-q) * (G y).re) := by
    filter_upwards [hE] with y hy
    rw [hy]
    field_simp
    ring
  rw [ReciprocityTheory.AnForm.levi_congr hF v, levi_const_mul _ hR, ReciprocityTheory.AnForm.levi_add_smul (-q) hMA hRe,
    ReciprocityTheory.AnForm.levi_add_smul (-p) hM hA, ReciprocityTheory.AnForm.levi_re_analytic hG]
  field_simp
  ring

def sqDiv (A B : HermLine J) (p : ℕ) : HermLine J where
  a := (2 : ℤ) • A.a - (p : ℤ) • B.a
  h z := A.h z ^ 2 * (B.h z ^ p)⁻¹
  pos z hz := by
    have h1 := A.pos z hz
    have h2 := B.pos z hz
    positivity
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc]
    have : ∀ k, ‖c k‖ ^ ((2 : ℤ) • A.a - (p : ℤ) • B.a) k =
        (‖c k‖ ^ A.a k) ^ 2 * ((‖c k‖ ^ B.a k) ^ p)⁻¹ := fun k => by
      have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [zpow_sub₀ h0, mul_comm (2 : ℤ), mul_comm (p : ℤ), _root_.zpow_mul, _root_.zpow_mul, div_eq_mul_inv]
      simp only [zpow_natCast, zpow_ofNat]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, mul_pow, mul_inv]
    ring

theorem sqDiv_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (p : ℕ) :
    IsSmoothHerm (sqDiv A B p) :=
  (hA.pow 2).mul ((hB.pow p).inv fun z hz => (pow_pos (B.pos z hz) p).ne')

end MuPos

open MuPos

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem chart_levi_split (D : ComponentData II Ψ K J Ω W) (S : Finset ℕ) (hS : S ⊆ D.S)
    (A : HermLine J) (hA : IsSmoothHerm A) (F : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℝ) (a : Fin D.nCharts) (p q : ℕ) (hq : q ≠ 0)
    (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (ht : ‖t‖ ≤ 1 / 2)
    (hform : ∀ s ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, Real.log (A.h ((D.chart a).γ s)) =
      q * (F s + ∑ r ∈ S, Real.log (D.vertFactor r ((D.chart a).γ s))) + p * Real.log (D.A'.h ((D.chart a).γ s)))
    (v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) :
    levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v =
      q * levi F t v + p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
  have hb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t hb
  have hz : ∀ k, ∃ i, (D.chart a).γ t ⟨k, i⟩ ≠ 0 := ((D.chart a).mem t hb).1
  obtain ⟨G, hG, hGe⟩ := exists_analytic_sum S (fun r s => Real.log (D.vertFactor r ((D.chart a).γ s))) t
    fun r hr => (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D r (hS hr)).2 a t hb
  refine levi_split (G := G) (by exact_mod_cast hq) (contDiffAt_logH hA hγ hz)
    (contDiffAt_logH D.A'_pos.1 hγ hz) hG ?_ v
  filter_upwards [hGe, Metric.isOpen_ball.mem_nhds hb] with s h₁ h₂
  rw [hform s h₂, h₁]

theorem chart_levi_sqDiv (D : ComponentData II Ψ K J Ω W) (A : HermLine J) (hA : IsSmoothHerm A)
    (a : Fin D.nCharts) (p : ℕ) (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (ht : ‖t‖ ≤ 1 / 2) (v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) :
    levi (fun s => Real.log ((sqDiv A D.A' p).h ((D.chart a).γ s))) t v =
      2 * levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v -
        p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
  have hb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t hb
  have hz : ∀ k, ∃ i, (D.chart a).γ t ⟨k, i⟩ ≠ 0 := ((D.chart a).mem t hb).1
  have h1 := contDiffAt_logH hA hγ hz
  have h2 := contDiffAt_logH D.A'_pos.1 hγ hz
  have hE : (fun s => Real.log ((sqDiv A D.A' p).h ((D.chart a).γ s))) =ᶠ[𝓝 t]
      fun s => 2 * Real.log (A.h ((D.chart a).γ s)) + (-(p : ℝ)) * Real.log (D.A'.h ((D.chart a).γ s)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hb] with s hs
    have hzs : ∀ k, ∃ i, (D.chart a).γ s ⟨k, i⟩ ≠ 0 := ((D.chart a).mem s hs).1
    have p1 := A.pos _ hzs
    have p2 := D.A'.pos _ hzs
    show Real.log (A.h _ ^ 2 * (D.A'.h _ ^ p)⁻¹) = _
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [ReciprocityTheory.AnForm.levi_congr hE v, ReciprocityTheory.AnForm.levi_add_smul _ (contDiffAt_const.mul h1) h2,
    levi_const_mul _ h1]
  ring

theorem posU_of_nefOnFibres : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), IsFullIntersectionSystem II → S'.IsTied → (∀ B : ℕ, 4 * D.f + 2 ≤ B → NefOnFibres (mCoordIdeal D.y) (muTwDeg Hd B)) → PosU S' := by
  intro hPB K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hII hT hNef B p q hB hp hpq
  obtain ⟨δ₀, hδ₀, hApos⟩ := GlobalTheory.T.uniform_levi_positivity_on_charts K J II Ψ Ω W D
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq1 : 1 ≤ q := hp.trans hpq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hδ : 0 < p * δ₀ / (2 * q) := by positivity
  have hev := (GlobalTheory.T.regularized_weight_dominates_eventually K J II Ψ Ω W D Hd M w S' hT).and
    (GlobalTheory.T.regularized_levi_lower_bound_eventually K J II Ψ Ω W D Hd M w S' hT _ hδ)
  have key : ∀ LF LA V : ℝ, 0 ≤ V → -(p * δ₀ / (2 * q) * V) ≤ LF → δ₀ * V ≤ LA →
      0 ≤ q * LF + p * LA ∧ 0 ≤ 2 * (q * LF + p * LA) - p * LA := by
    intro LF LA V hV h1 h2
    have e1 : -(p * δ₀ / 2 * V) ≤ q * LF := by
      have := mul_le_mul_of_nonneg_left h1 hq0.le
      have e : (q : ℝ) * -(p * δ₀ / (2 * q) * V) = -(p * δ₀ / 2 * V) := by
        field_simp
      linarith
    have e2 : p * (δ₀ * V) ≤ p * LA := mul_le_mul_of_nonneg_left h2 hp0.le
    have e3 : 0 ≤ p * δ₀ * V := by positivity
    constructor <;> nlinarith
  obtain ⟨t₀, ht₀, hsub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 hev
  refine ⟨t₀, ht₀, fun t' ht' ht'₀ => ?_⟩
  obtain ⟨⟨-, -, hMU⟩, hreg⟩ := hsub ⟨ht', ht'₀⟩
  obtain ⟨hsm, hdeg, hform⟩ := hMU B p q
  set A := MUc Hd S' B p q t' with hAdef
  have hsplit : ∀ (a : Fin D.nCharts) (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), ‖t‖ ≤ 1 / 2 → ∀ v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ,
      levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v =
        q * levi (fun s => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v +
          p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
    intro a t ht v
    refine chart_levi_split D (D.SB B) (Finset.filter_subset _ _) A hsm _ a p q (by omega) t ht (fun s hs => ?_) v
    exact hform _ ((D.chart a).mem s hs)
  have hsemi : IsSemipositiveH (mCoordIdeal D.y) A := by
    refine GlobalTheory.T.semipositive_levi_of_log_metric K J II Ψ Ω W D A hsm fun a t ht v => ?_
    have e := hsplit a t ht v
    have b1 := hreg a t ht v
    have b2 := hApos a t ht v
    rw [e]
    exact (key _ _ _ (by positivity) b1 b2).1
  have hN : IsSemipositiveH (mCoordIdeal D.y) (sqDiv A D.A' p) := by
    refine GlobalTheory.T.semipositive_levi_of_log_metric K J II Ψ Ω W D _ (sqDiv_smooth hsm D.A'_pos.1 p) fun a t ht v => ?_
    have e0 := chart_levi_sqDiv D A hsm a p t ht v
    have e := hsplit a t ht v
    have b1 := hreg a t ht v
    have b2 := hApos a t ht v
    rw [e0, e]
    exact (key _ _ _ (by positivity) b1 b2).2
  refine ⟨hsemi, ?_, ?_⟩
  · rw [hdeg]
    exact GlobalTheory.T.nef_on_fibres_add_nonneg hPB K J _ _ _ p q (hNef B hB) fun k => (D.a'_pos k).le
  · refine GlobalTheory.T.ample_on_generic_fibre_of_semipositive hPB II hII K J _ (sqDiv A D.A' p) A D.a' 2 p hN hsm D.a'_pos (by norm_num) hp ?_
    ext k
    simp [sqDiv, D.A'_deg]

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section


theorem _root_.GlobalTheory.T.measure_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.MuMeasureLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | exact GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit <;> assumption)
end
