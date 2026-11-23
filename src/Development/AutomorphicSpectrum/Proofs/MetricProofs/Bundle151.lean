module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle148
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventually
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle021
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle033
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.SemilocResidueDegOfFibreIncomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.twisted_chart_local_coordinates_alt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ (b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsNormFn M τ a k₀ ca cb RW fun x => logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) x + c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isNormFn_logNormSec_diagSec | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isNormFn_logNormSec_diagSec | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isNormFn_logNormSec_diagSec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.regularized_weight_dominates_eventually : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ᶠ t' in 𝓝[>] (0 : ℝ), (∀ x, S'.B.ph x ≤ S'.bregWeight t' x) ∧ M.atlas.Smooth (S'.bregWeight t') ∧ ∀ B p q : ℕ, IsSmoothHerm (MUc Hd S' B p q t') ∧ (MUc Hd S' B p q t').a = (q : ℤ) • muTwDeg Hd B + (p : ℤ) • D.a' ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((MUc Hd S' B p q t').h z) = q * (Real.log (S'.ref.h z) + S'.bregWeight t' (M.proj z) + ∑ r ∈ D.SB B, Real.log (D.vertFactor r z)) + p * Real.log (D.A'.h z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth | exact GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.bregWeight_ge_and_MUc_smooth <;> assumption)
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem isCompatChart_atlas {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) (j : Fin A.n) :
    IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem potential_pos_of_section :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (Φ : LocPot M.Xc), IsPotential M.atlas Φ → (∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re) → IsPosPot M.atlas Φ := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D M Φ hΦ hloc x j y hy v hv
  classical
  set e := M.atlas.chart j with he
  have hcompat : IsCompatChart M.atlas e := isCompatChart_atlas M.atlas j
  have hsrc : e.symm y ∈ e.source := e.map_target hy.1
  obtain ⟨U, hUo, hyU, hUsub, s, hs, hsh, G, hG, hrel⟩ := hloc x (e.symm y) ⟨hy.2, trivial⟩
  set V : Set (Fin D.n → ℂ) := e.target ∩ e.symm ⁻¹' U with hV
  have hVo : IsOpen V := e.isOpen_inter_preimage_symm hUo
  have hyV : y ∈ V := ⟨hy.1, hyU⟩
  have hVn : V ∈ 𝓝 y := hVo.mem_nhds hyV
  set τ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hτdef
  have hτ : AnalyticOnNhd ℂ τ V := fun u hu => analyticAt_pi_iff.2 fun p => hsh p j u hu
  have hg : AnalyticAt ℂ (G ∘ e.symm) y := hG j y hyV
  have hτmem : ∀ u ∈ V, τ u ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (τ u) = e.symm u := fun u hu => hs _ hu.2
  have hz : τ y ∈ mcPts (mCoordIdeal D.y) := (hτmem y hyV).1
  have hpz : M.proj (τ y) = e.symm y := (hτmem y hyV).2
  have hτy : AnalyticAt ℂ τ y := hτ y hyV
  set w := fderiv ℂ τ y v with hwdef

  set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL
  have hLd : HasDerivAt L v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    simp only [id, one_smul] at h
    exact h
  have hL0 : L 0 = y := by simp [hL]
  have hLn : ∀ᶠ σ in 𝓝 (0 : ℂ), L σ ∈ V :=
    hLd.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hVn)
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => τ (L σ) with hγdef
  have hγ0 : γ 0 = τ y := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ w 0 :=
    (hτy.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq (0 : ℂ) hLd hL0.symm

  have htan : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) (τ y) w := by
    intro f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw
    rw [hγ0] at hder
    have hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hLn] with σ hσ
      exact (hτmem _ hσ).1.2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)

  have hnt : ∀ c : K → ℂ, w ≠ torusSmul c (τ y) := by
    intro c hwc
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ :=
      projHoloLocal II Ψ K ι Ω E D M e hcompat (τ y) hz (by rw [hpz]; exact hsrc)
    have hFz : HasFDerivAt F (fderiv ℂ F (τ y)) (τ y) :=
      (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt
    have hFγ : HasFDerivAt F (fderiv ℂ F (τ y)) (γ 0) := hγ0 ▸ hFz
    have hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W :=
      hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hγ0 ▸ hzW))
    have h1 : fderiv ℂ F (τ y) w = v := by
      refine (hFγ.comp_hasDerivAt (0 : ℂ) hγw).unique (hLd.congr_of_eventuallyEq ?_)
      filter_upwards [hLn, hWγ] with σ hσ hσW
      rw [Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hτmem _ hσ).1⟩).2, (hτmem _ hσ).2, e.right_inv hσ.1]
    set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (τ y) with hδ
    have hδ0 : δ 0 = τ y := by
      funext p
      simp [hδ, torusSmul]
    have hδd : HasDerivAt δ (torusSmul c (τ y)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (τ y p)
      simpa [hδ, torusSmul] using h
    have hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y) := fun σ =>
      ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _
    have hδproj : ∀ σ, M.proj (δ σ) = M.proj (τ y) := fun σ =>
      ((M.fibre (τ y) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W :=
      hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
    have h2 : fderiv ℂ F (τ y) (torusSmul c (τ y)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (τ y)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (e (M.proj (τ y)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

  have hO : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    MuRegSmooth.isOpen_blocks.mem_nhds hz.1
  have hlogA : ContDiffAt ℝ 2 (fun z => Real.log (D.A'.h z)) (τ y) :=
    ((D.A'_pos.1.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log (D.A'.pos _ hz.1).ne'
  have hc1 : ContDiffAt ℝ 2 ((fun z => Real.log (D.A'.h z)) ∘ τ) y :=
    hlogA.comp y (hτy.restrictScalars.contDiffAt (n := 2))
  have hc2 : ContDiffAt ℝ 2 (fun u => ((G ∘ e.symm) u).re) y := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hg.restrictScalars.contDiffAt (n := 2))
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  have hev : (Φ.φ x ∘ e.symm) =ᶠ[𝓝 y]
      fun u => ((fun z => Real.log (D.A'.h z)) ∘ τ) u + (1 : ℝ) * ((G ∘ e.symm) u).re := by
    filter_upwards [hVn] with u hu
    have := hrel _ hu.2
    simp only [Function.comp_apply, one_mul, hτdef]
    linarith
  have hpos := D.A'_pos.2 (τ y) hz w htan hnt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hg, levi_comp v hτy hlogA]
  rw [mul_zero, add_zero]
  exact hpos

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (a : Fin D.nCharts) (k : Fin M.atlas.n), ∀ t ∈ Metric.ball (0 : Fin D.n → ℂ) 1, M.proj ((D.chart a).γ t) ∈ (M.atlas.chart k).source → AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t ∧ Function.Bijective (fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M a k t ht hsrc
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t ht
  have hev : ∀ᶠ t' in 𝓝 t, (D.chart a).γ t' ∈ mcPts (mCoordIdeal D.y) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds ht) fun t' h => (D.chart a).mem t' h
  have hFan : AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t :=
    LevelTowerAlt.analyticAt_proj D M (LevelTowerAlt.compat_atlas M.atlas k) hγ hev hsrc
  refine ⟨hFan, ?_⟩
  have htend : Tendsto (fun t' => M.proj ((D.chart a).γ t')) (𝓝 t) (𝓝 (M.proj ((D.chart a).γ t))) := by
    have h1 : Tendsto (D.chart a).γ (𝓝 t) (𝓝[mcPts (mCoordIdeal D.y)] ((D.chart a).γ t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto, hev⟩
    exact ((M.cont _ ((D.chart a).mem t ht)).tendsto).comp h1
  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj ((D.chart a).γ t))
  have hHan : ∀ p, AnalyticAt ℂ (fun t' => s (M.proj ((D.chart a).γ t')) p) t :=
    fun p => LevelTowerAlt.analyticAt_holoOn_proj D M (hsh p) hγ hev hxU
  let P : (Σ kk, J kk) → ((Σ kk, J kk) → ℂ) →L[ℂ] ℂ := fun p =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ kk, J kk) => ℂ) p
  have hγp : ∀ p, AnalyticAt ℂ (fun t' => (D.chart a).γ t' p) t :=
    fun p => ((P p).analyticAt _).comp hγ
  choose m hm using ((D.chart a).mem t ht).1
  have hrel : ∀ᶠ t' in 𝓝 t, (∃ c : K → ℂ, (∀ kk, c kk ≠ 0) ∧
      s (M.proj ((D.chart a).γ t')) = torusSmul c ((D.chart a).γ t')) ∧
      ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0 := by
    have hU : ∀ᶠ t' in 𝓝 t, M.proj ((D.chart a).γ t') ∈ U := htend (hUo.mem_nhds hxU)
    have hnz : ∀ᶠ t' in 𝓝 t, ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0 :=
      Filter.eventually_all.mpr fun kk => (hγp ⟨kk, m kk⟩).continuousAt.eventually_ne (hm kk)
    filter_upwards [hU, hev, hnz] with t' h1 h2 h3
    refine ⟨?_, h3⟩
    obtain ⟨h4, h5⟩ := hs _ h1
    exact (M.fibre _ h2 _ h4).mp h5.symm
  obtain ⟨cf, hcf⟩ : ∃ cf : (Fin D.n → ℂ) → K → ℂ, cf = fun t' kk =>
      s (M.proj ((D.chart a).γ t')) ⟨kk, m kk⟩ / (D.chart a).γ t' ⟨kk, m kk⟩ := ⟨_, rfl⟩
  have hcfeq : ∀ᶠ t' in 𝓝 t, ∀ p : (Σ kk, J kk),
      s (M.proj ((D.chart a).γ t')) p = cf t' p.1 * (D.chart a).γ t' p := by
    filter_upwards [hrel] with t' ht'
    obtain ⟨⟨c, hc, he⟩, hn⟩ := ht'
    have hck : ∀ kk, cf t' kk = c kk := by
      intro kk
      rw [hcf]
      simp only [he, torusSmul]
      exact mul_div_cancel_right₀ _ (hn kk)
    intro p
    rw [hck, he]
    rfl
  have hcf0 : ∀ kk, cf t kk ≠ 0 := by
    obtain ⟨⟨c, hc, he⟩, hn⟩ := hrel.self_of_nhds
    intro kk
    rw [hcf]
    simp only [he, torusSmul]
    rw [mul_div_cancel_right₀ _ (hn kk)]
    exact hc kk
  have hcfan : ∀ kk, AnalyticAt ℂ (fun t' => cf t' kk) t := by
    intro kk
    rw [hcf]
    exact (hHan _).div (hγp _) (hm kk)
  have hFt : M.atlas.chart k (M.proj ((D.chart a).γ t)) ∈ (M.atlas.chart k).target :=
    (M.atlas.chart k).map_source hsrc
  have hGan : ∀ p, AnalyticAt ℂ (fun y => s ((M.atlas.chart k).symm y) p)
      (M.atlas.chart k (M.proj ((D.chart a).γ t))) := by
    intro p
    refine hsh p k _ ⟨hFt, ?_⟩
    simp only [Set.mem_preimage, (M.atlas.chart k).left_inv hsrc]
    exact hxU
  have hG : DifferentiableAt ℂ (fun y => s ((M.atlas.chart k).symm y))
      (M.atlas.chart k (M.proj ((D.chart a).γ t))) :=
    differentiableAt_pi.mpr fun p => (hGan p).differentiableAt
  have hHeq : (fun t' => s (M.proj ((D.chart a).γ t'))) =ᶠ[𝓝 t]
      (fun t' => s ((M.atlas.chart k).symm (M.atlas.chart k (M.proj ((D.chart a).γ t'))))) := by
    filter_upwards [htend ((M.atlas.chart k).open_source.mem_nhds hsrc)] with t' h
    rw [(M.atlas.chart k).left_inv h]
  set L := fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t with hL
  set G' := fderiv ℂ (fun y => s ((M.atlas.chart k).symm y))
    (M.atlas.chart k (M.proj ((D.chart a).γ t))) with hG'
  have hc0 := hG.hasFDerivAt.comp t hFan.differentiableAt.hasFDerivAt
  have hH : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t'))) (G'.comp L) t :=
    hc0.congr_of_eventuallyEq hHeq
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    apply (D.chart a).immersion t ht v
    refine ⟨fun kk => -(fderiv ℂ (fun t' => cf t' kk) t v) / cf t kk, ?_⟩
    funext p
    have h1 : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t')) p)
        ((P p).comp (G'.comp L)) t :=
      (P p).hasFDerivAt.comp t hH
    have hγ' : HasFDerivAt (fun t' : Fin D.n → ℂ => (D.chart a).γ t' p)
        ((P p).comp (fderiv ℂ (D.chart a).γ t)) t :=
      (P p).hasFDerivAt.comp t hγ.differentiableAt.hasFDerivAt
    have h2 := (hcfan p.1).differentiableAt.hasFDerivAt.mul hγ'
    have h3 := h2.congr_of_eventuallyEq (hcfeq.mono fun t' h => h p)
    have h4 := DFunLike.congr_fun (h1.unique h3) v
    simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, P, ContinuousLinearMap.proj_apply] at h4
    have h0 := hcf0 p.1
    have h5 : (0 : ℂ) = cf t p.1 * fderiv ℂ (D.chart a).γ t v p +
        (D.chart a).γ t p * fderiv ℂ (fun t' => cf t' p.1) t v := h4
    show fderiv ℂ (D.chart a).γ t v p = -(fderiv ℂ (fun t' => cf t' p.1) t v) / cf t p.1 * (D.chart a).γ t p
    rw [div_mul_eq_mul_div, eq_div_iff h0]
    linear_combination -h5
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (L : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)))).mp hinj⟩
end

section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights

theorem genDeg_of_resExists (hE : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement := by
  have hPts : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hE
  have hFI : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncomp.full
  have hFD : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement := GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
  have hSec : GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection.Statement :=
    GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection.proof hE GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.full
      (GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.of_remaining
        GroundTheory.Heights₂.Heights.AutoClose.chart_norm_count hFD)
      GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.full
  have hCyc : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.Statement :=
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.of_remaining GroundTheory.Heights₂.Heights.ForSecondHalf.projDeg_all hFI
      (GroundTheory.Heights₂.Heights.ForSecondHalf.semilocMaxIdeals_of_fibreIncomp hFI)
      (GroundTheory.Heights₂.Heights.ForSecondHalf.semilocResidueDeg_of_fibreIncomp hFI hFD) hFD
  exact GroundTheory.Heights₂.Heights.Targets.GenDeg.of_pts hPts hSec hCyc

theorem pfCoord_of_genDeg (hGD : ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  exact GroundTheory.Heights₂.Heights.Targets.PFCoord.of_found hGD
    (fun F _ K _ ι _ => GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full F ι)
    GroundTheory.Heights₂.Heights.Targets.genFibreExists GlobalTheory.CompanionTheory.Ar.Giv.fibreDim
    GroundTheory.Heights₂.Heights.Inter.Closed.Targets.CoordFibreDeg

theorem genDeg_and_pfCoord :
    ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement →
      ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  intro hE
  exact ⟨genDeg_of_resExists hE, pfCoord_of_genDeg (genDeg_of_resExists hE)⟩

end GlobalTheory.CompanionTheory.Ar.Pub
end
