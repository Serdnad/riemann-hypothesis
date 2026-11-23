module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenOfUnit
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle107
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle028
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle047
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB

@[expose] public section

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) := by
  obtain ⟨h0, h1, h2⟩ := ha
  refine ⟨zpow_ne_zero n h0, ?_, ?_⟩
  · rcases n with m | m
    · simpa using pow_mem h1 m
    · simpa [zpow_negSucc] using pow_mem h2 (m + 1)
  · rcases n with m | m
    · simpa using pow_mem h2 m
    · simpa [zpow_negSucc] using pow_mem h1 (m + 1)

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.gen_unit <;> assumption

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  obtain ⟨ht0, ht⟩ := ht
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hs0 : s ≠ 0 := by
    intro h
    apply hu0
    rw [h, zero_div]
  refine ⟨hs0, ?_⟩
  have hunit : IsUnit (⟨s / t, hu1⟩ : regAt ξ p) :=
    ⟨⟨⟨s / t, hu1⟩, ⟨(s / t)⁻¹, hu2⟩, Subtype.ext (mul_inv_cancel₀ hu0),
      Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have hst : (⟨s / t, hu1⟩ : regAt ξ p) • t = s := by
    rw [Subring.smul_def, smul_eq_mul]
    exact div_mul_cancel₀ s ht0
  rw [ht, ← hst, Submodule.span_singleton_smul_eq hunit]

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.gen_untens <;> assumption

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := h.1
  rw [Finset.prod_ne_zero_iff] at h0
  exact h0 k (Finset.mem_univ k)

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨(map_ne_zero i).mpr h0, hreg a h1, ?_⟩
  rw [← map_inv₀]
  exact hreg _ h2

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

end LevelTowerAlt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.Ample

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem coneTangent {P : Ideal (MRing J)} {e : ℕ}
    {τ : (Fin e → ℂ) → (Σ k, J k) → ℂ} {y : Fin e → ℂ} (hτ : DifferentiableAt ℂ τ y)
    (hm : ∀ᶠ y' in 𝓝 y, τ y' ∈ mcPts P) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (τ y) (fderiv ℂ τ y w) := by
  intro f hf
  set F := MvPolynomial.map (Int.castRingHom ℂ) f
  have h0 : (fun y' => MvPolynomial.eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hm] with y' hy'
    exact hy'.2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => MvPolynomial.eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ : Fin 1 => f) y = 2 / Real.pi * levi f y (Pi.single 0 1) := by
  have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hne : (∅ : Finset (Fin 1)) ≠ {0} := by decide
  have key : (cxHessian f y 0 0).re = levi f y (Pi.single 0 1) := by
    simp only [cxHessian, levi]
    generalize fderiv ℝ (fderiv ℝ f) y = H
    generalize H (Pi.single 0 1) (Pi.single 0 1) + H (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1) = u
    simp
  have hm : mixedDisc (fun _ : Fin 1 => cxHessian f y) = cxHessian f y 0 0 := by
    unfold mixedDisc
    rw [hU, Finset.sum_pair hne]
    simp [Matrix.det_unique]
  unfold maDensity
  rw [hm, key]
  simp

theorem geomDeg_nonneg {P W : Ideal (MRing J)} {N : HermLine J} (hN : IsSemipositiveH P N) (hW : P ≤ W) :
    0 ≤ geomDeg W N 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · refine MeasureTheory.integral_nonneg fun y => finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hg
    · have hev := hg.choose_spec.2
      set gm := hg.choose
      have hP : ∀ᶠ y' in 𝓝 y, gm y' ∈ mcPts P := hev.mono fun y' h => ⟨h.2.1.1, fun f hf => h.2.1.2 f (hW hf)⟩
      have hz := hP.self_of_nhds
      have han : AnalyticAt ℂ gm y :=
        GroundTheory.Heights₂.Heights.Inter.analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
      have hlog : ContDiffAt ℝ 2 (fun z => Real.log (N.h z)) (gm y) :=
        ((hN.1.contDiffAt (StokesStep.isOpen_multicone.mem_nhds hz.1)).of_le
          (WithTop.coe_le_coe.2 le_top)).log (N.pos _ hz.1).ne'
      have h1 := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) han hlog
      have h2 := hN.2 _ hz _ (coneTangent han.differentiableAt hP (Pi.single 0 1))
      have h3 := maDensity_one ((fun z => Real.log (N.h z)) ∘ gm) y
      rw [h1] at h3
      rw [_root_.one_mul]
      exact le_of_le_of_eq (mul_nonneg (by positivity) h2) h3.symm
    · exact le_rfl
  · exact le_rfl

end LevelTowerAlt.Ample

theorem LevelTowerAlt.ample_generic_fibre_of_combination : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  intro hI II hII K _ J _ P N A a' m p hN hA ha' hm hp heq W d hd hW hPW
  classical
  have hK : Nonempty K := hW.1
  have hDG := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system ⟨II, hII⟩)
  have hF := GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K J
  have hPos := GroundTheory.Heights₂.Heights.Targets.Positivity.full ℚ J _ hF
  let fs : (K → ℤ) → HermLine J := fun b => HermLine.ofMetrics (fun k => fsMetric (J k)) b
  have hfs : ∀ b, IsSmoothHerm (fs b) := fun b => GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs b
  have hfsn : ∀ b : K → ℤ, (∀ k, 0 ≤ b k) → ∀ W', IsArithVar W' 2 → 0 ≤ geomDeg W' (fs b) 1 := by
    intro b hb W' hW'
    have h1 := hDG K J W' 1 (fun _ => fs b) hW' fun _ => hfs b
    have h2 := (hPos _ 1 (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW')).1
      (fun _ => b) fun _ k => hb k
    show 0 ≤ ptsIntegral W' (pot fun _ : Fin 1 => fs b) (fun _ => 1)
    rw [h1]
    exact_mod_cast h2
  let ℓ : Fin 3 → HermLine J := ![N, fs ((p : ℤ) • a' - 1), fs 1]
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := fun j => by
    fin_cases j
    · exact hN.1
    · exact hfs _
    · exact hfs _
  have hnef : ∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (ℓ j) 1 := fun j W' h1 h2 => by
    fin_cases j
    · exact LevelTowerAlt.Ample.geomDeg_nonneg hN (hPW.trans h2)
    · refine hfsn _ (fun k => ?_) W' h1
      have h3 := ha' k
      have h4 : (1 : ℤ) ≤ p := by exact_mod_cast hp
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      nlinarith
    · exact hfsn _ (fun _ => zero_le_one) W' h1
  have e1 := (GlobalTheory.T.log_integral_multilinear II hII K J W d (Fin 3) ℓ (fun _ _ => 1) hW hℓ).1
  have e2 := (GlobalTheory.T.log_integral_multilinear II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).1
  have e3 := (GlobalTheory.T.log_integral_multilinear II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).2
    (fun _ => Top.combLine ℓ fun _ => 1) (fun _ => Top.combLine (fun _ : Unit => A) fun _ => (m : ℤ)) (Equiv.refl _)
    (fun _ => (GlobalTheory.T.hermitian_combination_smooth_conj K J _ ℓ _).1 hℓ) (fun _ => (GlobalTheory.T.hermitian_combination_smooth_conj K J _ _ _).1 fun _ => hA) fun _ => by
      show ∑ _ : Unit, (m : ℤ) • A.a = ∑ j, (1 : ℤ) • (ℓ j).a
      rw [Fin.sum_univ_three]
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, heq]
      show _ = N.a + ((p : ℤ) • a' - 1) + 1
      abel
  rw [e1, e2] at e3
  have hpos : 0 < ∑ w : Fin d → Fin 3, (∏ k : Fin d, ((1 : ℤ) : ℝ)) *
      ptsIntegral W (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) := by
    simp only [Int.cast_one, Finset.prod_const_one, _root_.one_mul]
    refine Finset.sum_pos' (fun w _ => ?_) ⟨fun _ => 2, Finset.mem_univ _, ?_⟩
    · exact GlobalTheory.T.ptsIntegral_log_nonneg hI.kleimanNefF (fun K _ J _ => (PB.Known.fieldNumbers ℚ K J).1) PB.Known.divSuppArith II hII K J W d (fun k => ℓ (w k)) hW
        (fun k => hℓ _) fun k => hnef _
    · have h1 := hDG K J W d (fun _ => fs 1) hW fun _ => hfs _
      have h2 := (hPos _ d (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW)).2
      show 0 < ptsIntegral W (pot fun _ : Fin d => fs 1) (fun _ => 1)
      rw [h1]
      exact_mod_cast h2
  rw [← e3, Fintype.sum_unique] at hpos
  have hc : (0 : ℝ) ≤ ∏ k : Fin d, ((m : ℤ) : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  exact (pos_iff_pos_of_mul_pos hpos).1 (lt_of_le_of_ne hc fun h => by
    rw [← h, zero_mul] at hpos
    exact lt_irrefl _ hpos)
end

section

open MeasureTheory Metric Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.A (Mollifier molli coordDiv)

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem molli_le_of_le {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : ReciprocityTheory.AnForm.A.IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, φ y ≤ c) : molli ρ t φ z ≤ c := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc _ ≤ ∫ y, ρ.scaled t y * c := by
        refine integral_mono (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z)
          ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _) fun y => ?_
        by_cases hy : ρ.scaled t y = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
        have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
        rw [indicator_of_mem hmem]
        exact hc _ hmem
    _ = c := by rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem neBot_Yo (R : RegChartData A) (x : X) : (𝓝[R.Yo] x).NeBot := by
  obtain ⟨k, hk⟩ := R.cover x
  have hs := R.toPotentialCharts.mid_subset_source k (R.inner_subset_mid k hk)
  have hne := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S k) (R.chart k).open_target ((R.chart k).map_source hs)
  have ht : Tendsto (R.chart k).symm (𝓝[(R.chart k).target \ coordDiv (R.S k)] (R.chart k x)) (𝓝[R.Yo] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((R.chart k).continuousAt_symm ((R.chart k).map_source hs)).tendsto
      rw [(R.chart k).left_inv hs] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [R.mem_Yo k _ ((R.chart k).map_target hy.1), (R.chart k).right_inv hy.1]
      exact hy.2
  exact ht.neBot

theorem phReg_le [CompactSpace X] [T2Space X] (R : RegChartData A) (ρ : Mollifier D) (Kt : ℝ → ℝ)
    (hK : Tendsto Kt (𝓝[>] 0) atTop) {V K' : Set X} {g : X → ℝ} (hV : IsOpen V) (hg : ContinuousOn g V)
    (hph : ∀ x ∈ V ∩ R.Yo, g x = R.ph x) (hK'V : K' ⊆ V) (hK' : IsCompact K') (j : Fin R.N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K', x ∈ R.mid j → R.phReg ρ (Kt t) t j x ≤ g x + ε := by
  obtain ⟨δ, B, hδ, hT⟩ := TruncPsh.proof X D A R
  obtain ⟨U, hU, -, hUb, hUp⟩ := hT j
  set L := R.chart j '' (K' ∩ closure (R.mid j)) with hL
  have hsub : K' ∩ closure (R.mid j) ⊆ (R.chart j).source := fun x hx => R.closure_mid j hx.2
  have hLc : IsCompact L := (hK'.inter_right isClosed_closure).image_of_continuousOn ((R.chart j).continuousOn.mono hsub)
  set O := (R.chart j).target ∩ (R.chart j).symm ⁻¹' V with hO
  have hOo : IsOpen O := (R.chart j).isOpen_inter_preimage_symm hV
  have hLO : L ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(R.chart j).map_source (hsub hx), ?_⟩
    show (R.chart j).symm _ ∈ V
    rw [(R.chart j).left_inv (hsub hx)]
    exact hK'V hx.1
  let F : (Fin D → ℂ) → ℝ := fun y => R.q j y + g ((R.chart j).symm y)
  have hF : ContinuousOn F O := ((R.q_smooth j).continuousOn.mono inter_subset_left).add
    (hg.comp ((R.chart j).continuousOn_symm.mono inter_subset_left) fun y hy => hy.2)
  obtain ⟨η, hη, hηO⟩ := hLc.exists_cthickening_subset_open hOo hLO
  obtain ⟨d, hd, hdF⟩ := Metric.uniformContinuousOn_iff.1
    ((hLc.cthickening (r := η)).uniformContinuousOn_of_continuous (hF.mono hηO)) ε hε
  obtain ⟨M, hM⟩ := hLc.exists_bound_of_continuousOn (hF.mono hLO)
  have hsm : ∀ {a : ℝ}, 0 < a → ∀ᶠ t in 𝓝[>] (0 : ℝ), t < a := fun ha =>
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ha)
  filter_upwards [self_mem_nhdsWithin, hsm hδ, hsm (half_pos hη), hsm (half_pos hd), hK.eventually_ge_atTop M]
    with t ht t1 t2 t3 t4 x hx hxm
  have ht0 : (0 : ℝ) < t := ht
  have hxL : R.chart j x ∈ L := ⟨x, ⟨hx, subset_closure hxm⟩, rfl⟩
  have hxs := hsub ⟨hx, subset_closure hxm⟩
  have hFx : F (R.chart j x) = R.q j (R.chart j x) + g x := by simp only [F, (R.chart j).left_inv hxs]
  have h1 : molli ρ t (R.trunc (Kt t) j) (R.chart j x) ≤ F (R.chart j x) + ε := by
    refine molli_le_of_le ρ hU (hUp _).1 ht0 ((closedBall_subset_closedBall t1.le).trans (hUb x hxm)) fun y hy => ?_
    have hyx : dist y (R.chart j x) ≤ t := hy
    have hyO : y ∈ O := hηO (mem_cthickening_of_dist_le y _ _ _ hxL (by linarith))
    refine TruncTransfer.limsupExt_max_le (R.chart j).open_target (R.S j) (R.u j) _ _ t hyO.1 ht0 fun y' hy' hy't hy'S => ?_
    have h2 : dist y' (R.chart j x) < 2 * t := by
      have := dist_triangle y' y (R.chart j x)
      have h3 : dist y' y < t := hy'
      linarith
    have hy'c : y' ∈ cthickening η L := mem_cthickening_of_dist_le y' _ _ _ hxL (by linarith)
    have h4 := hdF y' hy'c _ (self_subset_cthickening L hxL) (by linarith)
    have h5 : R.u j y' = F y' := by
      show R.q j y' + R.ph _ = R.q j y' + g _
      rw [hph _ ⟨(hηO hy'c).2, by
        rw [R.mem_Yo j _ ((R.chart j).map_target hy't), (R.chart j).right_inv hy't]
        exact hy'S⟩]
    rw [Real.dist_eq] at h4
    have h6 := hM _ hxL
    rw [Real.norm_eq_abs] at h6
    refine max_le ?_ ?_
    · rw [h5]
      linarith [(abs_lt.1 h4).2]
    · linarith [(abs_le.1 h6).1]
  show molli ρ t (R.trunc (Kt t) j) (R.chart j x) - R.q j (R.chart j x) ≤ _
  linarith

theorem regUnif : RegUnif := by
  intro K _ J _ P n M Xo B S V g hS hV hg hph
  obtain ⟨C₀, t₀, ht₀, hb⟩ := ChartMollifiedBounds.proof TruncPsh.proof M.Xc n M.atlas S.R S.ρ
  have h3 : ∀ t x, S.regWeight t x = S.R.glue
      (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) (S.e1 t) x := fun _ _ => rfl
  have hup : ∀ t, 0 < t → ∀ x c, (∀ j, x ∈ S.R.mid j → S.R.phReg S.ρ (S.K t) t j x ≤ c) →
      S.regWeight t x ≤ c + S.e1 t := by
    intro t ht0 x c h
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    rw [h3]
    refine LogLogRegularisation.glue_le S.R.toPotentialCharts _ hε0 fun j hj => ?_
    have h2 := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * S.e1 t) (S.cutoff.bounds j x hj).2
    have := h j hj
    show S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x ≤ c
    linarith
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ x, S.regWeight t x ≤ C₀ + 1) ∧ ∀ x ∈ V, g x ≤ S.regWeight t x := by
    filter_upwards [S.eventually_chartLevi hS, self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀), hS.K_tendsto.eventually_ge_atTop 0,
      hS.e1_tendsto_zero.eventually (eventually_le_nhds one_pos)] with t hsm ht htt hK he
    have ht0 : (0 : ℝ) < t := ht
    have hε0 : 0 ≤ S.e1 t := ht0.le.trans (S.e1_ge t ht0)
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := hup t ht0 x C₀ fun j hj => ((hb t ht0 htt).2 (S.K t) hK j x hj).2.1
      linarith
    · have hlow : ∀ x ∈ S.R.Yo, S.R.ph x ≤ S.regWeight t x := by
        intro x hx
        obtain ⟨k, hk⟩ := S.R.cover x
        have hkm := S.R.inner_subset_mid k hk
        have a1 := ((hb t ht0 htt).2 (S.K t) hK k x hkm).2.2 hx
        have a2 := LogLogRegularisation.le_glue S.R.toPotentialCharts
          (fun j x => S.R.phReg S.ρ (S.K t) t j x + 4 * S.e1 t * S.η j x) hε0 hkm
        simp only [S.cutoff.eq_zero k x hk, mul_zero, add_zero] at a2
        rw [h3]
        linarith
      have := neBot_Yo S.R x
      have c1 : Tendsto g (𝓝[S.R.Yo] x) (𝓝 (g x)) := (hg.continuousAt (hV.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
      have c2 : Tendsto (S.regWeight t) (𝓝[S.R.Yo] x) (𝓝 (S.regWeight t x)) :=
        ((GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.continuous_of_smooth M.atlas hsm.1).tendsto x).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto_of_tendsto c1 c2 ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx)] with y hy hyV
      rw [hph y ⟨hyV, hy⟩]
      exact hlow y hy
  refine ⟨⟨C₀ + 1, h1⟩, fun K' hK'V hK' => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  filter_upwards [h1, self_mem_nhdsWithin, hS.e1_tendsto_zero.eventually (eventually_lt_nhds (half_pos hε)),
    eventually_all.2 fun j => phReg_le S.R S.ρ S.K hS.K_tendsto hV hg hph hK'V hK' j (half_pos hε)] with t a1 ht a2 a3 x hx
  have a4 := hup t ht x (g x + ε / 2) fun j hj => a3 j x hx hj
  have a5 := a1.2 x (hK'V hx)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end LevelTowerAlt.Comparison₂
end
end
