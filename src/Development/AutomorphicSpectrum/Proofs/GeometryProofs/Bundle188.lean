module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle179
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsThetaFrameMulUnit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle180
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetraction
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle175
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle182
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianFamilyHodgeLattice
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle181
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle183
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle011
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.ExpChart GlobalTheory.HolHom in
theorem exp_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (N : ℕ) (f : Fin N → Γ(G.left, V)) (ε : ℝ) (Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left) ∧ (∀ b ∈ ball b₀ ε, Ψ b 0 = 1 ∧ (∀ a : Fin g, IsDerivAt0 (fun z => (Ψ b z).left) (Pi.single a 1) (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)) ∧ ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V ∧ ∀ a, valAt' (Ψ b z).left V (t a) = z a) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) → (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (fun a => valAt' x.left V (t a)) := open GlobalTheory.CompanionTheory.Ar.Flat.ExpChart GlobalTheory.HolHom in by
  intro R _ G _ _ g n M B ψ hsm hB b₀ hb₀
  obtain ⟨V, t, ρ, hV, hρ, hss, hθ, hrat⟩ := GlobalTheory.T.exists_exp_chart_standard_smooth R G g M (ψ b₀) hsm
  letI : Algebra R Γ(G.left, V) := (ExpChart.cst G.hom V).toAlgebra
  haveI : Algebra.IsStandardSmooth R Γ(G.left, V) := hss
  have halg : ∀ r, algebraMap R Γ(G.left, V) r = ExpChart.cst G.hom V r := fun _ => rfl
  have h₀ := (hθ (ψ b₀) hρ).1
  let χ₀ : Γ(G.left, V) →+* ℂ := evalHom (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V h₀
  have hχv : ∀ a, valAt' (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V a = χ₀ a := fun a => valR_eq _ _ h₀ a
  have hχc : χ₀.comp (algebraMap R Γ(G.left, V)) = ψ b₀ := RingHom.ext fun r => by
    show χ₀ (ExpChart.cst G.hom V r) = ψ b₀ r
    rw [← hχv]; exact val_cst V _ h₀ r
  have ht₀ : ∀ c, χ₀ (t c) = 0 := fun c => by rw [← hχv]; exact (hθ (ψ b₀) hρ).2.1 c
  have hder : ∀ (θ : R →+* ℂ) (a : Fin g), θ ρ ≠ 0 → ∃ D : Γ(G.left, V) →+ ℂ,
      (∀ f, D f = TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V f)) ∧
      (∀ r, D (ExpChart.cst G.hom V r) = 0) ∧
      (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * D f' +
        valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f' * D f) := by
    intro θ a hr
    have hin := (hθ θ hr).1
    obtain ⟨D, hD, hL⟩ := tan_der (tan_base M θ (Pi.single a 1)) hin
    refine ⟨D, hD, fun r => ?_, hL⟩
    have hv := (le_preimage_dual_iff (tan_base M θ (Pi.single a 1)) V).2 hin
    rw [hD, valR_eq _ _ hv, valR_cst G.hom V _ _ (tan_over M θ (Pi.single a 1)) hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl']
  have hD₀ : ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) →
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0 := by
    intro D hc hl hz
    obtain ⟨c, hcD, -⟩ := GlobalTheory.T.derivation_vanishing_constants R G g M (ψ b₀) hsm V hV h₀ D hc (fun f f' => by
      rw [hχv, hχv]; exact hl f f')
    have hc0 : ∀ a, c a = 0 := fun a => by
      have := hcD (t a)
      rw [hz a] at this
      simp only [(hθ (ψ b₀) hρ).2.2] at this
      simpa using this.symm
    ext f
    rw [hcD f]
    simp [hc0]
  have hS₀ : ∀ c, ∃ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) ∧
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0 := by
    intro c
    obtain ⟨D, hD, hc, hl⟩ := hder (ψ b₀) c hρ
    refine ⟨D, hc, fun x y => ?_, fun c' => ?_⟩
    · rw [hl, hχv, hχv]
    · rw [hD]; exact (hθ (ψ b₀) hρ).2.2 c c'
  obtain ⟨N, f, ε, δ, Ψa, hε, hδ, hεB, hΨ₀, hprop, hdiff, hft, huniq⟩ :=
    GlobalTheory.T.derivation_determines_chart R Γ(G.left, V) n g B ψ hB.1 hB.2 b₀ hb₀ χ₀ t hχc ht₀ hD₀ hS₀

  have hev : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 ∧
      ∀ j, ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
    have hc : ∀ u, ContinuousAt (fun b => ψ b u) b₀ := fun u =>
      (hB.2 u).continuousOn.continuousAt (hB.1.mem_nhds hb₀)
    have h1 : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 := (hc ρ).eventually_ne hρ
    have h2 : ∀ j, ∀ᶠ b in 𝓝 b₀,
        ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
      intro j
      obtain ⟨u, k, hu⟩ := hrat (f j)
      have hq : ContinuousAt (fun b => ψ b u / ψ b ρ ^ k) b₀ := (hc u).div ((hc ρ).pow k) (pow_ne_zero k hρ)
      have hq0 : ψ b₀ u / ψ b₀ ρ ^ k = χ₀ (f j) := by
        rw [div_eq_iff (pow_ne_zero k hρ), ← hu _ hρ, hχv]
      have hb := hq.eventually (Metric.ball_mem_nhds _ hδ)
      filter_upwards [hb, h1] with b hb1 hb2
      have : valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) = ψ b u / ψ b ρ ^ k := by
        rw [eq_div_iff (pow_ne_zero k hb2)]; exact hu _ hb2
      rw [this, ← hq0]
      simpa [dist_eq_norm] using hb1
    filter_upwards [h1, eventually_all.2 h2] with b a1 a2 using ⟨a1, a2⟩
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', h1', h2', h3'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε₁ ∧ ε' ≤ ε ∧ ε' ≤ δ :=
    ⟨min ε₁ (min ε δ), lt_min hε₁ (lt_min hε hδ), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hex : ∀ b z, ∃ x : Over.mk (spMap (ψ b)) ⟶ G, b ∈ ball b₀ ε → z ∈ ball (0 : Fin g → ℂ) ε →
      ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = Ψa b z a := by
    intro b z
    by_cases h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε
    · obtain ⟨x, hx, hv⟩ := exists_pt hV (ψ b) (Ψa b z) (fun r => congrArg (fun q => q r) (hprop b h.1 z h.2).1)
      exact ⟨x, fun _ _ => ⟨hx, hv⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Ψ hΨ using hex
  have hbε : ∀ b ∈ ball b₀ ε', b ∈ ball b₀ ε := fun b hb => ball_subset_ball h2' hb
  have hzε : ∀ z ∈ ball (0 : Fin g → ℂ) ε', z ∈ ball (0 : Fin g → ℂ) ε := fun b hb => ball_subset_ball h2' hb
  have hzero : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε' := mem_ball_self hε'
  have hone : ∀ b ∈ ball b₀ ε', Ψ b 0 = 1 := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := hball b (ball_subset_ball h1' hb)
    have hin := (hθ (ψ b) hb1).1
    have hc : (evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w _) hin r
    have hv : ∀ a, evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin a = valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V a :=
      fun a => (valR_eq _ _ hin a).symm
    have := (huniq b (ball_subset_ball h3' hb) _ hc (fun j => by rw [hv]; exact hb2 j)).2
    have hz : (fun c => evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin (t c)) = 0 := by
      funext c
      rw [hv]; exact (hθ (ψ b) hb1).2.1 c
    rw [hz] at this
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    refine pt_ext hV hx hin fun a => ?_
    rw [hvx, ← this, hv]
  have hHol : ∀ p ∈ ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε', HolAt (fun q : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ q.1 q.2).left) p := by
    intro p hp
    have hop : IsOpen (ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε') := isOpen_ball.prod isOpen_ball
    have hnb := hop.mem_nhds hp
    have hop' : IsOpen (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) := isOpen_ball.prod isOpen_ball
    refine holAt_of_affine hV (hΨ _ _ (hbε _ hp.1) (hzε _ hp.2)).1 ?_ fun a => ?_
    · filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).1
    · have hd : DifferentiableAt ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψa bz.1 bz.2 a) p :=
        (hdiff a).differentiableAt (hop'.mem_nhds ⟨hbε _ hp.1, hzε _ hp.2⟩)
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).2 a
  have hfib : ∀ b ∈ ball b₀ ε', HolAt (fun z => (Ψ b z).left) 0 := by
    intro b hb
    have := (hHol (b, 0) ⟨hb, hzero⟩).precomp (k := fun z : Fin g → ℂ => (b, z)) (z := 0)
      ((differentiableAt_const b).prodMk differentiableAt_id)
    exact this
  refine ⟨V, t, N, f, ε', Ψ, hε', (ball_subset_ball h2').trans hεB, ?_, fun b hb => ⟨hone b hb, fun a => ?_, fun z hz => ?_⟩, ε', hε', fun b hb x hxV hnear => ?_⟩
  · exact isHolTo_of_holAt (isOpen_ball.prod isOpen_ball) hHol
  ·
    obtain ⟨hb1, -⟩ := hball b (ball_subset_ball h1' hb)
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    obtain ⟨v', hv'⟩ := (hfib b hb).exists_isDerivAt (Pi.single a 1)
    have hb' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left) = (Ψ b 0).left := by
      rw [tan_base M (ψ b) (Pi.single a 1), hone b hb]
    obtain ⟨D₁, hD₁, hL₁⟩ := tan_der hv'.1 hx
    obtain ⟨D₂, hD₂, hL₂⟩ := tan_der hb' hx
    have hnb : ball (0 : Fin g → ℂ) ε' ∈ 𝓝 (0 : Fin g → ℂ) := ball_mem_nhds _ hε'
    have hval : ∀ c, D₁ (t c) = if a = c then 1 else 0 := by
      intro c
      have e : (fun z => valAt' (Ψ b z).left V (t c)) =ᶠ[𝓝 0] fun z => z c := by
        filter_upwards [hnb] with z hz
        rw [(hΨ b z (hbε b hb) (hzε z hz)).2]
        exact (hprop b (hbε b hb) z (hzε z hz)).2.1 c
      rw [hD₁, hv'.2 V hx, e.fderiv_eq, (hasFDerivAt_apply c (0 : Fin g → ℂ)).fderiv]
      simp [Pi.single_apply, eq_comm]
    have hcon1 : ∀ r, D₁ (ExpChart.cst G.hom V r) = 0 := by
      intro r
      have e : (fun z => valAt' (Ψ b z).left V (ExpChart.cst G.hom V r)) =ᶠ[𝓝 0] fun _ => ψ b r := by
        filter_upwards [hnb] with z hz
        exact val_cst V _ (hΨ b z (hbε b hb) (hzε z hz)).1 r
      rw [hD₁, hv'.2 V hx, e.fderiv_eq]
      simp
    obtain ⟨D₃, hD₃, hcon2, -⟩ := hder (ψ b) a hb1
    have hD23 : ∀ f, D₂ f = D₃ f := fun f => by rw [hD₂, hD₃]
    have hz : D₁ - D₂ = 0 := by
      refine (hprop b (hbε b hb) 0 (hzε 0 hzero)).2.2 _ (fun r => ?_) (fun x y => ?_) (fun c => ?_)
      · show D₁ (ExpChart.cst G.hom V r) - D₂ (ExpChart.cst G.hom V r) = 0
        rw [hcon1, hD23, hcon2, sub_zero]
      · simp only [AddMonoidHom.sub_apply]
        rw [hL₁, hL₂, hvx, hvx]
        ring
      · simp only [AddMonoidHom.sub_apply]
        rw [hval, hD₂, (hθ (ψ b) hb1).2.2 a c, sub_self]
    have heq : v' = spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left := by
      refine point_ext hV ((le_preimage_dual_iff hv'.1 V).2 hx) ((le_preimage_dual_iff hb' V).2 hx) fun f => ?_
      refine TrivSqZeroExt.ext ((fst_valR hv'.1 hx f).trans (fst_valR hb' hx f).symm) ?_
      have := DFunLike.congr_fun hz f
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this
      rw [← hD₁, ← hD₂, this]
    rw [← heq]
    exact (isDerivAt0_iff _ _ _).2 hv'
  · obtain ⟨hx, hvx⟩ := hΨ b z (hbε b hb) (hzε z hz)
    refine ⟨hx, fun a => ?_⟩
    rw [hvx]
    exact (hprop b (hbε b hb) z (hzε z hz)).2.1 a
  · have hbδ := ball_subset_ball h3' hb
    have hc : (evalHom x.left V hxV).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w x) hxV r
    have hv : ∀ a, evalHom x.left V hxV a = valAt' x.left V a := fun a => (valR_eq _ _ hxV a).symm
    have hΨb₀ : ∀ a, valAt' (Ψ b₀ 0).left V a = χ₀ a := fun a => by
      rw [(hΨ b₀ 0 (mem_ball_self hε) (hzε 0 hzero)).2, hΨ₀]
    have hn : ∀ j, ‖evalHom x.left V hxV (f j) - χ₀ (f j)‖ < δ := fun j => by
      rw [hv, ← hΨb₀]
      exact (hnear j).trans_le h3'
    obtain ⟨-, hχ⟩ := huniq b hbδ _ hc hn
    have hmem : (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε' := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε']
      intro c
      obtain ⟨j, hj⟩ := hft c
      have := hnear j
      rw [hΨb₀, hj, ht₀, sub_zero] at this
      exact this
    refine ⟨hmem, ?_⟩
    obtain ⟨hx, hvx⟩ := hΨ b _ (hbε b hb) (hzε _ hmem)
    refine pt_ext hV hxV hx fun a => ?_
    rw [hvx, ← hv, hχ]
    simp only [hv]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.uniformised_eigen_frames_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ), (∀ i, LinearIndependent (𝓞 E) (e i)) → ∃ Φ : CFn Xo c, ∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anDef | exact GlobalTheory.CompanionTheory.Ar.Flat.anDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anDef <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles MonoidalCategory CartesianMonoidalCategory MonObj

theorem _root_.GlobalTheory.T.hodge_tate_free_integral_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), CharZero Ω ∧ IsLocallyNoetherian 𝔐.X ∧ IsProper (Limits.pullback.snd 𝔐.t.G.hom 𝔐.ξ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (fun a g => g ≫ 𝔐.t.act.act a) (fun n g g' c => Out.WeilIs 𝔐.t.G 𝔐.t.PP.L n g g' (unitOn c)))) ∧ 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ ∀ s, mseg y s ≠ 0 → IsNoetherianRing (chartRing o (mseg y) s) ∧ IsIntegrallyClosed (chartRing o (mseg y) s) ∧ IsFractionRing (chartRing o (mseg y) s) Ω ∧ ∃ x : Sp (chartRing o (mseg y) s) ⟶ 𝔐.X, spMap (algebraMap (chartRing o (mseg y) s) Ω) ≫ x = 𝔐.ξ ∧ ∀ q : Cpt 𝔐.ξ, q.1 ∈ Set.range x ↔ (InChart 𝔐.ξ (mseg y) s q ∧ OverZp 𝔐 p q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point | exact GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem _root_.GlobalTheory.T.hodge_eigen_projector_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ Dn : ℕ, 0 < Dn ∧ ∀ (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = (Dn : Ω) • v) ∧ ∀ q : Cpt 𝔐.ξ, (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧ ((∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) → ∀ e ∈ 𝔐.V s q, (Dn : Ω) • e ∈ 𝔐.M.lat q) ∧ ∀ p ∈ S, InFibre 𝔐.ξ p q → ∀ κ : Ω, HT.Sandwich 𝔐 p κ → ∀ e ∈ 𝔐.V s q, ((Dn : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc | exact GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.ModelChart

theorem exists_bdryChart_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X' : Scheme.{0}) (jx : X' ⟶ Y.X) (t : SAB H X') (m : SABMap t Y.t jx) (τ : c.F →+* ℂ) (n a : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X')), a ≤ n → IsHolTo (Metric.ball 0 1) p → (∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F))) → (∀ u ∈ Flat.punct n a 1, ∀ x : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)), x ≫ pullback.fst _ _ = p u ≫ jx → Set.range x ⊆ Set.range Y.jQ) → ∃ (ρ : ℝ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (h : Sp C.R ⟶ X'), 0 < ρ ∧ ρ ≤ 1 ∧ Nonempty (SABMap C.t t h) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ h = p ((ρ : ℂ) • z) := by
  intro E _ _ _ H D l Xo c Y X' jx t m τ n a p han hp hs hpt
  classical
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let fP := pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let sZ := pullback.snd jx fP
  let fZ := pullback.fst jx fP
  let j := pullback.fst sZ Y.jQ
  let g := pullback.snd sZ Y.jQ
  have := Y.jQ_open
  have hj : IsOpenImmersion j := inferInstance
  let k : pullback sZ Y.jQ ⟶ Xo.X := g ≫ pullback.fst _ _

  obtain ⟨tZ, ⟨mZ⟩⟩ := exists_sab fZ t
  obtain ⟨tU, ⟨mU⟩⟩ := exists_sab g Y.oF.t
  obtain ⟨q₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m mZ
  obtain ⟨q₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m mU
  have e₁ : g ≫ Y.jQ ≫ fP = j ≫ fZ ≫ jx := by
    have a₁ : j ≫ sZ = g ≫ Y.jQ := pullback.condition
    have a₂ : fZ ≫ jx = sZ ≫ fP := pullback.condition
    rw [a₂, ← Category.assoc g, ← a₁, Category.assoc]
  rw [e₁] at q₂
  have q₁' : SABMap tZ Y.t (fZ ≫ jx) := q₁
  obtain ⟨mj, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel q₁' q₂
  obtain ⟨mk, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap mU

  let p' : (Fin n → ℂ) → (Sp ℂ ⟶ X') := fun u => if u ∈ Metric.ball (0 : Fin n → ℂ) 1 then p u else p 0
  have hp'e : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u = p u := fun u hu => if_pos hu
  have hp' : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) p' := GlobalTheory.LocLift.isHolTo_congr hp hp'e
  have hs' : ∀ u, (p' u ≫ jx) ≫ Y.s = spMap τ ≫ spMap (algebraMap (𝓞 c.F) c.F) := fun u => by
    have : p' u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) := by
      by_cases hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1
      · rw [hp'e u hu]; exact hs u hu
      · simp only [p', if_neg hu]; simpa [h0] using hs 0 h0
    rw [Category.assoc, this]
    simp [spMap]
  let q : (Fin n → ℂ) → (Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    fun u => pullback.lift (p' u ≫ jx) (spMap τ) (hs' u)
  have hq : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) q :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ Y.s (spMap (algebraMap (𝓞 c.F) c.F)) n _ _ _ hs' Metric.isOpen_ball
      (GlobalTheory.LocLift.isHolTo_comp_hom hp' jx) (GlobalTheory.PeriodTests.isHolTo_const Metric.isOpen_ball _)
  have hc : ∀ u, p' u ≫ jx = q u ≫ fP := fun u => (pullback.lift_fst _ _ _).symm
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback jx fP) := fun u => pullback.lift (p' u) (q u) (hc u)
  have hy : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) y :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ jx fP n _ _ _ hc Metric.isOpen_ball hp' hq
  have hpu : ∀ z ∈ Flat.punct n a 1, ∃ w : Sp ℂ ⟶ pullback sZ Y.jQ, w ≫ j = y z ∧
      w ≫ k ≫ Xo.s = spMap (τ.comp (IntermediateField.inclusion c.le).toRingHom) := fun z hz => by
    have hr : Set.range (q z) ⊆ Set.range Y.jQ :=
      hpt z hz (q z) ((pullback.lift_fst _ _ _).trans (by rw [hp'e z hz.1]))
    let w₀ := IsOpenImmersion.lift Y.jQ (q z) hr
    have hw₀ : w₀ ≫ Y.jQ = q z := IsOpenImmersion.lift_fac _ _ _
    have hys : y z ≫ sZ = w₀ ≫ Y.jQ := (pullback.lift_snd _ _ _).trans hw₀.symm
    refine ⟨pullback.lift (y z) w₀ hys, pullback.lift_fst _ _ _, ?_⟩
    have h₁ : pullback.lift (y z) w₀ hys ≫ k = w₀ ≫ pullback.fst _ _ := by
      simp only [k, g]; rw [pullback.lift_snd_assoc]
    rw [← Category.assoc, h₁, Category.assoc, pullback.condition, ← Category.assoc]
    have h₂ : w₀ ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap τ := by
      rw [← Y.jQ_over, ← Category.assoc, hw₀]
      exact pullback.lift_snd _ _ _
    rw [h₂]
    simp [spMap]
  obtain ⟨ρ, C, i, e, hρ, hρ1, -, ⟨mi⟩, -, -, hψ⟩ :=
    Flat.exists_bdryChart_of_hol E H D l Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) _ tZ _ j k tU n a y
      han hj ⟨mj⟩ ⟨mk⟩ hy hpu
  obtain ⟨mh, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mZ mi
  refine ⟨ρ, C, i ≫ fZ, hρ, hρ1, ⟨mh⟩, fun z hz => ?_⟩
  have hin : (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg z]
  rw [← Category.assoc, hψ z hz, ← hp'e _ hin]
  exact pullback.lift_fst _ _ _

end GlobalTheory.CompanionTheory.Ar.ModelChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem frame_lieModel_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) :=
  @PositivityTheory.Xgn.quotient_uniformization_model

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.effective_scaled_weight_of_retraction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ) (k q' : ℕ) (s : G.Ω), (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) → SplitComps Y → 0 < k → 0 < q' → s ≠ 0 → G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s → ∃ (Fx : FixedData Y A.Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx), genPt Fx.ξf = genPt G.𝔐.ξ₀ ∧ Fx.kA = k ∧ Fx.q' = q' ∧ (∀ r, Fx.n r = (k * q' : ℕ) * ν r) ∧ o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧ Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧ (∀ x : A.Sys.X, ∃ (U : Set A.Sys.X) (lam : A.Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, A.Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (A.Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((A.Sys.A.chart j).symm z) i / lam ((A.Sys.A.chart j).symm z) p) (A.Sys.A.chart j x)).ker = ⊥) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | exact GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | (intros; apply GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.abelian_family_hodge_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (t : SAB H (Sp R)) (jj : Sp R ⟶ 𝔐.X) (m : SABMap t 𝔐.t jj) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B₀ : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B₀ ψ) (b : Fin n → ℂ) (Bb : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (sc : Fin r → Fin g → R) (σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ)), b ∈ B₀ → (∀ a' x, e.ex b (Bb a' x) = e.ex b x ≫ t.act.act a') → 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ → (∀ h : genPt 𝔐.ξ ⤳ centre (spMap (ψ b) ≫ jj), (𝔐.V lab).IsFrameAt s ⟨centre (spMap (ψ b) ≫ jj), h⟩) → (∀ i, ∃ v : epsAt (spMap (ψ b) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (ψ b) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (sc i)).left ≫ m.φ) → LinearIndependent ℂ (fun i k => ψ b (sc i k)) ∧ Submodule.span ℂ (Set.range fun i k => ψ b (sc i k)) = eigSp Bb (σ lab) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig | exact GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_hodge_lattice_germ_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)), IsCptGen ξ → M.IsActOf t.act.act ρ → (∀ q : Cpt ξ, HFree (S.g q).B r) → ∃ 𝓗 : HodgeLat M.lat ρ H.bar r, S.Gives 𝓗 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.germ_gives_hodgeLat | exact GlobalTheory.CompanionTheory.Ar.Flat.germ_gives_hodgeLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.germ_gives_hodgeLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem ptsIntegral_eq_sum_fundamental : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t :=
  SheetDecomposition.sheet_pieces_component

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem _root_.GlobalTheory.T.analytic_chart_vanishing_section : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W N : X.Opens) (x : Sp ℂ ⟶ X), Smooth s → IsCptGen ξ → genPt ξ ∈ W → x ≫ s = 𝟙 _ → genPt ξ ⤳ centre x → centre x ∈ N → ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsChart s B Y ∧ b₁ ∈ B ∧ Y b₁ = x ∧ (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) ∧ ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.exists_stable_eigen_tangents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | exact GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig <;> assumption)
end
