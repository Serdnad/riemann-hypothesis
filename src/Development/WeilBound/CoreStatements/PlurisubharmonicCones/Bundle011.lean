module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle127
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle117
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

theorem levi_margin {n : ℕ} {f : (Fin n → ℂ) → ℝ} (hf : ContDiffOn ℝ 2 f (Metric.ball 0 1))
    (hp : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ v, v ≠ 0 → 0 < levi f t v) :
    ∃ δ > (0 : ℝ), ∀ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, δ * ‖v‖ ^ 2 ≤ levi f t v := by
  have hc := ReciprocityTheory.AnForm.continuousOn_levi Metric.isOpen_ball hf
  set S : Set ((Fin n → ℂ) × (Fin n → ℂ)) := Metric.closedBall 0 (1 / 2) ×ˢ Metric.sphere 0 1 with hS
  have hSc : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hsub : S ⊆ Metric.ball 0 1 ×ˢ Set.univ := fun p hp' =>
    ⟨Metric.closedBall_subset_ball (by norm_num) hp'.1, trivial⟩
  obtain ⟨δ, hδ, hle⟩ := hSc.exists_forall_le' (hc.mono hsub) (a := 0) fun p hp' =>
    hp _ (hsub hp').1 _ fun h0 => by
      have := hp'.2
      rw [h0] at this
      simp at this
  refine ⟨δ, hδ, fun t ht v => ?_⟩
  by_cases hv : v = 0
  · rw [hv, ReciprocityTheory.AnForm.levi_zero]
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 := hle (t, ‖v‖⁻¹ • v) ⟨by simpa using ht, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']⟩
    simp only [ReciprocityTheory.AnForm.levi_smul_dir] at h1
    calc δ * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * levi f t v) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = levi f t v := by field_simp

theorem coneTangent_fderiv {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {e : ℕ}
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

end LevelTowerAlt

theorem LevelTowerAlt.levi_positive_reference_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∃ δ > (0 : ℝ), ∀ a, ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, δ * ‖v‖ ^ 2 ≤ levi (fun t' => Real.log (D.A'.h ((D.chart a).γ t'))) t v := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D
  have key : ∀ a, ∃ δ > (0 : ℝ), ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v,
      δ * ‖v‖ ^ 2 ≤ levi (fun t' => Real.log (D.A'.h ((D.chart a).γ t'))) t v := by
    intro a
    have hφ : ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1,
        ContDiffAt ℝ 2 (fun z => Real.log (D.A'.h z)) ((D.chart a).γ t) := fun t ht => by
      have hz := (D.chart a).mem t ht
      exact ((D.A'_pos.1.contDiffAt (StokesStep.isOpen_multicone.mem_nhds hz.1)).of_le
        (WithTop.coe_le_coe.mpr le_top)).log (D.A'.pos _ hz.1).ne'
    refine LevelTowerAlt.levi_margin (fun t ht => ?_) fun t ht v hv => ?_
    · exact ((hφ t ht).comp t
        (((D.chart a).analytic t ht).restrictScalars (𝕜 := ℝ)).contDiffAt).contDiffWithinAt
    · have hτ := (D.chart a).analytic t ht
      have h1 := ReciprocityTheory.AnForm.levi_comp v hτ (hφ t ht)
      change 0 < levi ((fun z => Real.log (D.A'.h z)) ∘ (D.chart a).γ) t v
      rw [h1]
      refine D.A'_pos.2 _ ((D.chart a).mem t ht) _ (LevelTowerAlt.coneTangent_fderiv hτ.differentiableAt ?_ v)
        fun c hc => hv ((D.chart a).immersion t ht v ⟨c, hc⟩)
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with y hy using (D.chart a).mem y hy
  choose δ hδ h using key
  obtain ⟨m, hm, hle⟩ : ∃ m > (0 : ℝ), ∀ a, m ≤ δ a := by
    rcases isEmpty_or_nonempty (Fin D.nCharts) with h0 | h0
    · exact ⟨1, one_pos, fun a => h0.elim a⟩
    · obtain ⟨a₀, h₀⟩ := Finite.exists_min δ
      exact ⟨δ a₀, hδ a₀, h₀⟩
  exact ⟨m, hm, fun a t ht v => (mul_le_mul_of_nonneg_right (hle a) (by positivity)).trans (h a t ht v)⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

variable {K : Type} {J : K → Type}

theorem orb_symm {z z' : (Σ k, J k) → ℂ} (h : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z') :
    ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp only
  rw [← _root_.mul_assoc, inv_mul_cancel₀ (hc p.1), _root_.one_mul]

theorem orb_trans {z z' z'' : (Σ k, J k) → ℂ} (h : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z')
    (h' : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z'') : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp only [_root_.mul_assoc]

theorem orb_limit {α : Type} {F : Filter α} [F.NeBot] {a b : α → (Σ k, J k) → ℂ} {a₀ b₀ : (Σ k, J k) → ℂ}
    (ha : ∀ p, Tendsto (fun w => a w p) F (𝓝 (a₀ p))) (hb : ∀ p, Tendsto (fun w => b w p) F (𝓝 (b₀ p)))
    (h : ∀ᶠ w in F, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (a w) (b w)) (h₀ : ∀ k, ∃ i, a₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, b₀ ⟨k, i⟩ ≠ 0) : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit a₀ b₀ := by
  choose ib hib using h₁
  choose ia hia using h₀
  have key : ∀ p : (Σ k, J k), a₀ p * b₀ ⟨p.1, ib p.1⟩ = a₀ ⟨p.1, ib p.1⟩ * b₀ p := by
    intro p
    have e1 : Tendsto (fun w => a w p * b w ⟨p.1, ib p.1⟩) F (𝓝 (a₀ p * b₀ ⟨p.1, ib p.1⟩)) :=
      (ha p).mul (hb _)
    have e2 : Tendsto (fun w => a w ⟨p.1, ib p.1⟩ * b w p) F (𝓝 (a₀ ⟨p.1, ib p.1⟩ * b₀ p)) :=
      (ha _).mul (hb p)
    refine tendsto_nhds_unique (e1.congr' ?_) e2
    filter_upwards [h] with w hw
    obtain ⟨c, -, hc⟩ := hw
    rw [hc]
    ring
  let c : K → ℂ := fun k => a₀ ⟨k, ib k⟩ / b₀ ⟨k, ib k⟩
  have hrel : ∀ p : (Σ k, J k), a₀ p = c p.1 * b₀ p := by
    intro p
    have hb0 := hib p.1
    simp only [c]
    field_simp
    rw [key p]
  refine ⟨c, fun k => ?_, funext hrel⟩
  intro hck
  apply hia k
  rw [hrel ⟨k, ia k⟩]
  simp [hck]

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, (A.chart j).left_inv hj]
    exact hx
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

variable [Fintype K] [∀ k, Fintype (J k)]

theorem cxModel_of_res {P : Ideal (MRing J)} {d : ℕ} (R : AnLogRes P ⊤ d) (hne : (mcPts P).Nonempty) :
    Nonempty (CxModel P d) := by
  classical
  letI := R.top
  haveI := R.compact
  haveI := R.t2
  have htop : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing J)) := by
    intro z hz
    have h1 := hz.2 1 Submodule.mem_top
    simp at h1
  have hex : ∀ z ∈ mcPts P, ∃ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z :=
    fun z hz => R.surj z hz (htop z)
  have hmemU : ∀ x, R.lift x x ∈ mcPts P := fun x => R.mem x x (R.mem_U x)
  have hinj : ∀ x x', ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) (R.lift x' x') → x = x' :=
    fun x x' h => R.inj x x' (htop _) h
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨x₀, -⟩ := hex z₀ hz₀
  let proj : ((Σ k, J k) → ℂ) → R.X := fun z =>
    if h : ∃ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z then h.choose else x₀
  have hproj : ∀ z ∈ mcPts P, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift (proj z) (proj z)) z := by
    intro z hz
    have h := hex z hz
    simp only [proj, dif_pos h]
    exact h.choose_spec
  have hproj_eq : ∀ z ∈ mcPts P, ∀ x, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift x x) z → proj z = x := by
    intro z hz x hx
    exact hinj _ _ (orb_trans (hproj z hz) (orb_symm hx))
  have hlift : ∀ x y, y ∈ R.U x → proj (R.lift x y) = y := by
    intro x y hy
    exact hproj_eq _ (R.mem x y hy) y (R.compat y x y ⟨R.mem_U y, hy⟩)
  have hcont : ContinuousOn proj (mcPts P) := by
    intro z hz
    show Tendsto proj (𝓝[mcPts P] z) (𝓝 (proj z))
    refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) ?_
    intro xs _ hxs
    have hG : (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)).NeBot := by
      rw [← Filter.map_neBot_iff proj, Filter.push_pull, inf_comm]
      exact hxs
    have hpx : Tendsto proj (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)) (𝓝 xs) :=
      tendsto_comap.mono_left inf_le_right
    have hid : Tendsto id (𝓝[mcPts P] z ⊓ comap proj (𝓝 xs)) (𝓝 z) :=
      tendsto_id.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
    have hlim : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (R.lift xs xs) z := by
      refine orb_limit (F := 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs))
        (a := fun w => R.lift xs (proj w)) (b := fun w => w) ?_ ?_ ?_ (hmemU xs).1 hz.1
      · intro p
        exact (continuousAt_of_holoOn R.A (R.holo xs p) (R.mem_U xs)).tendsto.comp hpx
      · intro p
        exact ((continuous_apply p).tendsto z).comp hid
      · have hU : ∀ᶠ w in 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs), proj w ∈ R.U xs :=
          hpx ((R.isOpen_U xs).mem_nhds (R.mem_U xs))
        have hM : ∀ᶠ w in 𝓝[mcPts P] z ⊓ comap proj (𝓝 xs), w ∈ mcPts P :=
          Filter.mem_inf_of_left self_mem_nhdsWithin
        filter_upwards [hU, hM] with w hw hwm
        exact orb_trans (R.compat xs (proj w) (proj w) ⟨hw, R.mem_U _⟩) (hproj w hwm)
    exact (hproj_eq z hz xs hlim).symm
  have hfib : ∀ z ∈ mcPts P, ∀ z' ∈ mcPts P,
      proj z = proj z' ↔ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z := by
    intro z hz z' hz'
    constructor
    · intro he
      have h1 := hproj z hz
      have h2 := hproj z' hz'
      rw [he] at h1
      obtain ⟨c, hc, hcz⟩ := orb_trans (orb_symm h2) h1
      exact ⟨c, hc, hcz⟩
    · rintro ⟨c, hc, hcz⟩
      have h3 : ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit z' z := ⟨c, hc, hcz⟩
      exact (hproj_eq z' hz' (proj z) (orb_trans (hproj z hz) (orb_symm h3))).symm
  have hsurj : ∀ x, ∃ z ∈ mcPts P, proj z = x :=
    fun x => ⟨R.lift x x, hmemU x, hlift x x (R.mem_U x)⟩
  have hsec : ∀ x, ∃ U : Set R.X, IsOpen U ∧ x ∈ U ∧ ∃ s : R.X → (Σ k, J k) → ℂ,
      (∀ y ∈ U, s y ∈ mcPts P ∧ proj (s y) = y) ∧ ∀ p, R.A.HoloOn U fun y => s y p := by
    intro x
    exact ⟨R.U x, R.isOpen_U x, R.mem_U x, fun y => R.lift x y,
      fun y hy => ⟨R.mem x y hy, hlift x y hy⟩, fun p => R.holo x p⟩
  exact ⟨CxModel.mk R.X R.A proj hsurj hfib hcont hsec⟩

end LevelTowerAlt

theorem LevelTowerAlt.nonempty_component_model : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), Nonempty (XModel D) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hy : ∀ k, ∃ i, D.y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := D.arith.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap]
    simp [h0]
  obtain ⟨R⟩ := GlobalTheory.T.exists_analytic_log_resolution K J Ω D.y D.n D.arith D.smoothGeneric
  exact LevelTowerAlt.cxModel_of_res R (GlobalTheory.T.multiprojective_points_nonempty K J Ω D.y hy)
end
