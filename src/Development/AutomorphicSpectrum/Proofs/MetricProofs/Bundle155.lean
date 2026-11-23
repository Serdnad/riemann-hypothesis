module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle152
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle153
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_measure : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main <;> assumption)
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

open Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_cross {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (k : K) (a b : ι k) :
    z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  simp only
  ring

theorem sameOrbit_of_cross {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (a b : ι k), z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩) :
    SameOrbit z z' := by
  choose j hj using hz'
  refine ⟨fun k => z ⟨k, j k⟩ / z' ⟨k, j k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz k
    refine div_ne_zero (fun h0 => ?_) (hj k)
    have := h k i (j k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hj k)) this
  · funext ⟨k, a⟩
    have := h k a (j k)
    have hjk := hj k
    simp only
    field_simp
    linear_combination this

theorem continuousAt_of_holo {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm)
      (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩).continuousAt
      ((A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem exists_conj_of_isLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X}
    {lift : X → X → (Σ k, ι k) → ℂ} (hS : IsLiftSys A P U lift) :
    ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧
      ∀ x, c (c x) = x := by
  obtain ⟨hU, hmem, hholo, hlift, hcompat, hsurj, hinj, -⟩ := hS
  choose c hc using fun x => hsurj _ (cj_mem_mcPts (hlift x x (hmem x)))
  refine ⟨c, hc, ?_, fun x => ?_⟩
  · refine continuous_iff_ultrafilter.2 fun x F hF => ?_
    obtain ⟨x', -, hx'⟩ := isCompact_univ.ultrafilter_le_nhds (F.map c) (by simp)
    have hcF : Tendsto c F (𝓝 x') := hx'
    have hev : ∀ᶠ y in (F : Filter X), y ∈ U x ∧ c y ∈ U x' :=
      Filter.Eventually.and (hF ((hU x).mem_nhds (hmem x))) (hcF ((hU x').mem_nhds (hmem x')))
    have horb : ∀ᶠ y in (F : Filter X), SameOrbit (lift x' (c y)) (cj (lift x y)) := by
      filter_upwards [hev] with y hy
      exact sameOrbit_trans (hcompat x' (c y) (c y) ⟨hy.2, hmem _⟩)
        (sameOrbit_trans (hc y) (sameOrbit_cj (hcompat y x y ⟨hmem y, hy.1⟩)))
    have hl1 : ∀ p, Tendsto (fun y => lift x' (c y) p) F (𝓝 (lift x' x' p)) := fun p =>
      (continuousAt_of_holo A (hholo x' p) (hmem x')).tendsto.comp hcF
    have hl2 : ∀ p, Tendsto (fun y => cj (lift x y) p) F (𝓝 (cj (lift x x) p)) := fun p =>
      (Complex.continuous_conj.tendsto _).comp
        ((continuousAt_of_holo A (hholo x p) (hmem x)).tendsto.mono_left hF)
    have hcross : ∀ (k : K) (a b : ι k),
        lift x' x' ⟨k, a⟩ * cj (lift x x) ⟨k, b⟩ = lift x' x' ⟨k, b⟩ * cj (lift x x) ⟨k, a⟩ :=
      fun k a b => tendsto_nhds_unique_of_eventuallyEq
        ((hl1 ⟨k, a⟩).mul (hl2 ⟨k, b⟩)) ((hl1 ⟨k, b⟩).mul (hl2 ⟨k, a⟩))
        (horb.mono fun y hy => sameOrbit_cross hy k a b)
    have horb' : SameOrbit (lift x' x') (cj (lift x x)) :=
      sameOrbit_of_cross (hlift x' x' (hmem x')).1 (cj_nonzero (hlift x x (hmem x)).1) hcross
    have hxx : x' = c x := hinj _ _ (sameOrbit_trans horb' (sameOrbit_symm (hc x)))
    exact hxx ▸ hcF
  · refine hinj _ _ (sameOrbit_trans (hc (c x)) ?_)
    have := sameOrbit_cj (hc x)
    rwa [cj_cj] at this

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h := hz.2 1 Submodule.mem_top
  simp at h

theorem fderiv_injective_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {τ : E → F} {σ : F → E} {a : E}
    (hτ : DifferentiableAt ℂ τ a) (hσ : DifferentiableAt ℂ σ (τ a))
    (h : σ ∘ τ =ᶠ[nhds a] id) : Function.Injective (fderiv ℂ τ a) := by
  have h1 : fderiv ℂ (σ ∘ τ) a = (fderiv ℂ σ (τ a)).comp (fderiv ℂ τ a) :=
    fderiv_comp a hσ hτ
  have h2 : fderiv ℂ (σ ∘ τ) a = ContinuousLinearMap.id ℂ E := by
    rw [h.fderiv_eq]; exact fderiv_id
  intro u v huv
  have hu : (fderiv ℂ (σ ∘ τ) a) u = u := by rw [h2]; rfl
  have hv : (fderiv ℂ (σ ∘ τ) a) v = v := by rw [h2]; rfl
  rw [← hu, ← hv, h1]
  simp [huv]

theorem differentiableAt_affCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0) (k : Fin R.A.n) (hk : x ∈ (R.A.chart k).source) :
    DifferentiableAt ℂ (fun w => affCoord p (R.lift x ((R.A.chart k).symm w)))
      (R.A.chart k x) := by
  have hmem : R.A.chart k x ∈ (R.A.chart k).target ∩ (R.A.chart k).symm ⁻¹' R.U x :=
    ⟨(R.A.chart k).map_source hk, by
      simpa only [Set.mem_preimage, (R.A.chart k).left_inv hk] using R.mem_U x⟩
  rw [differentiableAt_pi]
  intro q
  have hn : AnalyticAt ℂ ((fun y => R.lift x y q) ∘ (R.A.chart k).symm) (R.A.chart k x) :=
    R.holo x q k _ hmem
  have hd : AnalyticAt ℂ ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm)
      (R.A.chart k x) := R.holo x ⟨q.1, p q.1⟩ k _ hmem
  have hne : ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm) (R.A.chart k x) ≠ 0 := by
    simp only [Function.comp, (R.A.chart k).left_inv hk]
    exact hp q.1
  exact (hn.div hd hne).differentiableAt

theorem isLiftSys_of_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} (hJ : J = ⊤) {e : ℕ} (R : AnLogRes P J e) {X : Type}
    [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X)
    (hgh : ∀ y, g (h y) = y) (hhg : ∀ x, h (g x) = x) (hg : HoloMap A R.A g)
    (hh : HoloMap R.A A h) :
    IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  subst hJ
  refine ⟨fun x => (R.isOpen_U (g x)).preimage hg.1, fun x => R.mem_U (g x),
    fun x p => holoOn_comp hg (R.holo (g x) p), fun x y hy => R.mem _ _ hy,
    fun x x' y hy => R.compat _ _ _ hy, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy⟩ := R.surj z hz (not_mem_mcPts_top z)
    exact ⟨h y, by simpa only [hgh] using hy⟩
  · intro x x' hs
    have := R.inj (g x) (g x') (not_mem_mcPts_top _) hs
    rw [← hhg x, ← hhg x', this]
  · intro x p hp j hj
    obtain ⟨k, hk⟩ := R.A.cover (g x)
    set a := A.chart j with ha
    set c := R.A.chart k with hc
    have hax : a.symm (a x) = x := a.left_inv hj
    have hcx : c.symm (c (g x)) = g x := c.left_inv hk
    set τ : (Fin e → ℂ) → (Fin e → ℂ) := c ∘ g ∘ a.symm with hτdef
    set σ : (Fin e → ℂ) → (Fin e → ℂ) := a ∘ h ∘ c.symm with hσdef
    have hτx : τ (a x) = c (g x) := by simp only [hτdef, Function.comp, hax]
    have hτ : AnalyticAt ℂ τ (a x) := hg.2 j k (a x)
      ⟨a.map_source hj, show g (a.symm (a x)) ∈ c.source by rw [hax]; exact hk⟩
    have hσ : AnalyticAt ℂ σ (c (g x)) := hh.2 k j (c (g x))
      ⟨c.map_source hk, show h (c.symm (c (g x))) ∈ a.source by rw [hcx, hhg]; exact hj⟩

    have hcont : ContinuousAt (g ∘ a.symm) (a x) :=
      hg.1.continuousAt.comp (a.continuousAt_symm (a.map_source hj))
    have hnear : ∀ᶠ y in nhds (a x), g (a.symm y) ∈ c.source ∧ y ∈ a.target := by
      refine (hcont.eventually_mem (c.open_source.mem_nhds ?_)).and
        (a.open_target.mem_nhds (a.map_source hj))
      simpa only [Function.comp, hax] using hk
    have hleft : σ ∘ τ =ᶠ[nhds (a x)] id := by
      filter_upwards [hnear] with y hy
      simp only [hσdef, hτdef, Function.comp, c.left_inv hy.1, hhg, id, a.right_inv hy.2]
    have hinj := fderiv_injective_of_leftInv hτ.differentiableAt
      (by rw [hτx]; exact hσ.differentiableAt) hleft
    have hF := differentiableAt_affCoord R (g x) p hp k hk
    have himm := R.immersion (g x) (not_mem_mcPts_top _) p hp k hk
    set F : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
      fun w => affCoord p (R.lift (g x) ((R.A.chart k).symm w)) with hFdef
    have hcomp : (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) =ᶠ[nhds (a x)] F ∘ τ := by
      filter_upwards [hnear] with y hy
      simp only [hFdef, hτdef, Function.comp, ← hc, c.left_inv hy.1]
    have hder : fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x) =
        (fderiv ℂ F (c (g x))).comp (fderiv ℂ τ (a x)) := by
      rw [hcomp.fderiv_eq, fderiv_comp (a x) (by rw [hτx]; exact hF) hτ.differentiableAt, hτx]
    show (fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x)).ker = ⊥
    rw [hder, eq_bot_iff]
    intro v hv
    have h1 : (fderiv ℂ F (c (g x))) ((fderiv ℂ τ (a x)) v) = 0 := by simpa using hv
    have h2 : (fderiv ℂ τ (a x)) v ∈ (fderiv ℂ F (c (g x))).ker := by simpa using h1
    rw [himm] at h2
    have h3 : (fderiv ℂ τ (a x)) v = 0 := by simpa using h2
    have h4 : v = 0 := hinj (h3.trans (map_zero _).symm)
    simp [h4]

end GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.regularized_levi_lower_bound_eventually : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ δ > (0 : ℝ), ∀ᶠ t' in 𝓝[>] (0 : ℝ), ∀ a, ∀ t : Fin D.n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, -(δ * ‖v‖ ^ 2) ≤ levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v := by
  first | exact @GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually | exact GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually | (intros; apply GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp

section PosDom
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem potential_contDiffAt (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x : X)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).of_le two_le_infty).contDiffAt
    (((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
      (P.isOpen_U x)).mem_nhds hy)

theorem isPosPot_rsmul (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (hpos : IsPosPot A P) {c : ℝ} (hc : 0 < c) : IsPosPot A (P.rsmul c) := by
  intro x j y hy w hw
  have h : levi ((P.rsmul c).φ x ∘ (A.chart j).symm) y w =
      c * levi (P.φ x ∘ (A.chart j).symm) y w :=
    TailChernBound.levi_smul' c (potential_contDiffAt A P hP x j hy) w
  rw [h]
  exact mul_pos hc (hpos x j y hy w hw)

theorem isPsh_add_rsmul_succ (A : FinHolAtlas e X) (Θ Φ : LocPot X) (hΘ : IsPotential A Θ)
    (hΘp : IsPosPot A Θ) (hΦ : IsPotential A Φ) (C : ℝ) (hC : IsPsh A (Θ.rsmul C + Φ)) :
    IsPsh A (Φ + LocPot.ofFun (fun _ => 0) + Θ.rsmul (C + 1)) := by
  intro x j y hy w
  have hyΦ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Φ.U x := ⟨hy.1, hy.2.1.1⟩
  have hyΘ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hΘa := potential_contDiffAt A Θ hΘ x j hyΘ
  have hΦa := potential_contDiffAt A Φ hΦ x j hyΦ
  have e1 : (Φ + LocPot.ofFun (fun _ => 0) + Θ.rsmul (C + 1)).φ x ∘ (A.chart j).symm =
      fun z => (C + 1) * (Θ.φ x ∘ (A.chart j).symm) z + 1 * (Φ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Φ.φ x _ + 0 + (C + 1) * Θ.φ x _ = (C + 1) * Θ.φ x _ + 1 * Φ.φ x _
    ring
  have e2 : (Θ.rsmul C + Φ).φ x ∘ (A.chart j).symm =
      fun z => C * (Θ.φ x ∘ (A.chart j).symm) z + 1 * (Φ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show C * Θ.φ x _ + Φ.φ x _ = C * Θ.φ x _ + 1 * Φ.φ x _
    ring
  have h0 := hC x j y ⟨hy.1, hy.2.2, hy.2.1.1⟩ w
  rw [e2, TailChernBound.levi_lin C 1 hΘa hΦa w] at h0
  rw [e1, TailChernBound.levi_lin (C + 1) 1 hΘa hΦa w]
  have h1 : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w :=
    TailBoundAlt.isPsh_of_isPosPot A Θ hΘp x j y hyΘ w
  linarith

end PosDom

theorem exists_posPot_dominating : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (Φ : ReciprocityTheory.AnForm.M.LocPot M.Xc), ReciprocityTheory.AnForm.M.IsPotential M.atlas Φ → ∃ Θ : ReciprocityTheory.AnForm.M.LocPot M.Xc, ReciprocityTheory.AnForm.M.IsPotential M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPosPot M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPsh M.atlas (Φ + ReciprocityTheory.AnForm.M.LocPot.ofFun (fun _ => 0) + Θ) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M Φ hΦ
  classical
  obtain ⟨Θ₀, hΘ₀, hloc⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K J (mCoordIdeal D.y) D.n M D.A' D.A'_pos.1
  have hpos := GlobalTheory.T.local_section_of_potential_on_model II Ψ K J Ω W D M Θ₀ hΘ₀ hloc
  obtain ⟨C, hC0, hC, -⟩ := ReciprocityTheory.AnForm.P.TailBoundAlt.exists_psh_chern_bound M.atlas Θ₀ Φ hΘ₀ hpos hΦ
  exact ⟨Θ₀.rsmul (C + 1), ReciprocityTheory.AnForm.M.isPotentialRsmul M.atlas (C + 1) Θ₀ hΘ₀,
    isPosPot_rsmul M.atlas Θ₀ hΘ₀ hpos (by linarith),
    isPsh_add_rsmul_succ M.atlas Θ₀ Φ hΘ₀ hpos hΦ C hC⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.vertical_factor_smooth_hermitian_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  first | exact @GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric | exact GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

theorem _root_.GlobalTheory.T.resolution_exists_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ResExistsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK <;> assumption)
end
