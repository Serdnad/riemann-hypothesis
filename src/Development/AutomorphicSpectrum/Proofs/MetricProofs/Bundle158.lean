module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle134
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle140
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle141
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle111
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle121
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle152
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle020
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolution
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle144
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle124
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle151
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X) (hc : Continuous pr), IsWAtlas M BM.Rb τ a k₀ ca cb RW pr → ∃ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (Dg : Set RW.X) (cst : ℝ), IsPotential RW.A L' ∧ IsSection RW.A L' v ∧ IsSNC RW.A L' v ![1] ![Dg] ∧ IsSNC RW.A (BM.L.pullback pr hc + L') (fun x y => BM.s (pr x) (pr y) * v x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) Dg) ∧ (∀ w, logNormSec L' v w ≤ 0) ∧ IsNormFn M τ a k₀ ca cb RW fun x => logNormSec L' v x + cst := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM τ a b k₀ ca cb hb hj hblk hca hcb _ RW pr hc hW
  choose ψ kb σ i₀ V u hL using
    GlobalTheory.T.flag_adjacent_twisted_measure K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a b k₀ ca cb hb hj hblk hca hcb RW pr hW
  obtain ⟨c, hc0⟩ := GlobalTheory.T.twisted_chart_local_coordinates K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.secPot RW (GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA M τ a k₀) V
      (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c,
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec ψ i₀ u, GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSet k₀ RW, c, ?_, ?_, ?_, ?_, hc0, ?_⟩
  · exact GlobalTheory.T.secPot_isPotential K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact GlobalTheory.T.twisted_chart_holomorphic_alt K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  · exact GlobalTheory.T.twisted_chart_coordinates_regular K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact GlobalTheory.T.twisted_chart_continuous_projection K ι Φ y Ψ N j M n (d + 2) BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hW.1 c
  · exact GlobalTheory.T.twisted_chart_local_coordinates_alt K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hj hblk hca hcb hW c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem base_orbit {σ : Type} {blk : σ → Option K} {z₁ z : (Σ k, ι k) → ℂ} (h : SameOrbit z₁ z) :
    SameOrbit (basePart blk z₁) (basePart blk z) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem comp_orbit {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {b₁ b : (Σ k, ι' k) → ℂ} (h : SameOrbit b₁ b) :
    SameOrbit (b₁ ∘ v) (b ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hv.2.2.1 q]

theorem ideal_orbit {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b) : mCoordIdeal b₁ = mCoordIdeal b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact StepW.TorusAct.mCoordIdeal_torus c hc b

theorem valAt_orbit {x : (Σ k, ι k) → Ω} {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b)
    (hb : b ∈ mcPts (mCoordIdeal x)) (s : Ω) : valAt x s b₁ = valAt x s b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ((StepW.TorusAct.main K ι Ω x b c hc).2 hb).2 s

end Orbit

theorem img_spec (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j)
    (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F₀' : FrameData ι' Ψ N M'.Ω M'.blk)
    (F₀ : FrameData ι Ψ N M.Ω M.blk) (hz : z ∈ mcPts (mCoordIdeal y')) (hF' : M'.IsFrame F₀') (hF : M.IsFrame F₀)
    (hg' : M'.GoodAt F₀' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F₀ (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) :
    img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) ∧ IsImg Cv z (img Cv F₀' F₀ z) := by
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨h₀, hh₀, hz₀⟩ := GlobalTheory.T.exists_block_diag_frame_change K' ι' Φ' y' Ψ N j M' F₀' z hz hF' hg'
  have hT₀ := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F₀' F₀ hb hF' hF hg' hg
  have hH₀ : ∀ τ, IsBlockDiag j (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ) ∧
      (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ).det ≠ 0 := fun τ =>
    ⟨(hT₀ τ).1.mul (hh₀ τ).1, by rw [det_mul]; exact mul_ne_zero (hT₀ τ).2 (hh₀ τ).2⟩
  have hform := GlobalTheory.T.flag_cover_frames_value_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F₀' F₀ h₀ hb hF' hF hg' hg
    (fun τ => (hh₀ τ).1) hz₀
  have hwb : basePart M.blk (img Cv F₀' F₀ z) = basePart M'.blk z ∘ Cv.v := img_base Cv F₀' F₀ z
  have hw : img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) :=
    (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F₀ (img Cv F₀' F₀ z) _ hF (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg) hH₀
      (by rw [hwb]; exact hform)).1
  refine ⟨hw, ?_⟩
  intro z₁ h1 F' F hF1' hF1 hg1' hg1 h hfl
  have hbo : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) := base_orbit h1
  have hbov := comp_orbit Cv.block hbo
  rw [ideal_orbit hbo] at hg1'
  rw [ideal_orbit hbov] at hg1
  have htrans : ∀ τ, Cv.trans F' F (basePart M'.blk z₁) τ = Cv.trans F' F (basePart M'.blk z) τ := fun τ => by
    ext a c
    exact valAt_orbit hbo hb _
  obtain ⟨-, hhinv, hflag⟩ := hfl
  have hpl : ∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k',
      plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) =
        a * plk M' F₀' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h₀ p.1) := fun p k' hp => by
    obtain ⟨a, ha, e⟩ := hflag p k' hp
    obtain ⟨a₀, ha₀, e₀⟩ := hz₀ p k' hp
    obtain ⟨c, hc, rfl⟩ := h1
    refine ⟨a⁻¹ * c k' * a₀, mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (hc k')) ha₀, fun m' => ?_⟩
    have e1 := e m'
    have e2 := e₀ m'
    have e3 : ∑ I, valAt M'.x (F'.u ⟨k', m'⟩ I) (basePart M'.blk fun p => c p.1 * z p) *
        minorIJ (h p.1) I (stepCols N j p.2) = plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) :=
      Finset.sum_congr rfl fun I _ => by rw [valAt_orbit hbo hb]
    rw [e3] at e1
    simp only at e1
    rw [e2] at e1
    field_simp
    linear_combination -e1
  have hind := GlobalTheory.T.flag_cover_two_frames_comparison K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F₀' F F₀ h h₀ hb hF1' hF' hF1 hF hg1' hg' hg1 hg
    (fun τ => (hhinv τ).1) (fun τ => (hh₀ τ).1) hpl
  have hT := GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hb hF1' hF1 hg1' hg1
  obtain ⟨-, z₀, o1, o2, fl⟩ := GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F (img Cv F₀' F₀ z)
    (fun τ => Cv.trans F' F (basePart M'.blk z) τ * h τ) hF1 (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg1)
    (fun τ => ⟨(hT τ).1.mul (hhinv τ).1, by rw [det_mul]; exact mul_ne_zero (hT τ).2 (hhinv τ).2⟩)
    (fun p k hp => by
      obtain ⟨a₁, ha₁, e₁⟩ := hform p k hp
      obtain ⟨a₂, ha₂, e₂⟩ := hind p k hp
      refine ⟨a₁ * a₂⁻¹, mul_ne_zero ha₁ (inv_ne_zero ha₂), fun m => ?_⟩
      rw [e₁ m, hwb, e₂ m]
      field_simp)
  refine ⟨z₀, o1, Cj.sameOrbit_trans (hwb ▸ o2) (Cj.sameOrbit_symm hbov), ?_⟩
  simp only [htrans]
  exact fl

theorem local_img : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ z hz
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  obtain ⟨V, f, hV, hzV, hf, hs⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F' F hz hF' hF hg' hg
  refine ⟨V, f, hV, hzV, hf, fun z' hz' => ?_⟩
  obtain ⟨g1, g2, e⟩ := hs z' hz'
  rw [e]
  exact img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z' F' F hz'.2 hF' hF g1 g2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

section


theorem _root_.GlobalTheory.T.stokes_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.StokesLimitTVb.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.VbLimit.stokesLimitTVb | exact GlobalTheory.CompanionTheory.Ar.Giv.VbLimit.stokesLimitTVb | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.VbLimit.stokesLimitTVb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.Descent

open ReciprocityTheory.AnForm.M

section General
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem holoOn_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {f : X → ℂ} (hU : IsOpen U) (h : A.HoloOn U f) : ContinuousOn f U := by
  intro t ht
  obtain ⟨j, hj⟩ := A.cover t
  have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) (A.chart j t) :=
    h j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using ht⟩
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) t :=
    ContinuousAt.comp h1.continuousAt ((A.chart j).continuousAt hj)
  have h3 : ((f ∘ (A.chart j).symm) ∘ A.chart j) =ᶠ[𝓝 t] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
    simp [(A.chart j).left_inv hu]
  exact (h2.congr h3).continuousWithinAt

theorem exists_continuous_descent {P : Ideal (MRing J)} {d : ℕ} (M : CxModel P d)
    (F : ((Σ k, J k) → ℂ) → ℝ) (hF : ContinuousOn F {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ), (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, F (torusSmul c z) = F z) :
    ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts P, κ (M.proj z) = F z := by
  choose r hr hpr using M.surj
  have key : ∀ z ∈ mcPts P, F (r (M.proj z)) = F z := by
    intro z hz
    obtain ⟨c, hc, e⟩ := (M.fibre _ (hr _) z hz).1 (hpr _)
    calc F (r (M.proj z)) = F (torusSmul c (r (M.proj z))) := (hinv c hc _ (hr _)).symm
      _ = F z := by rw [← e]
  refine ⟨fun x => F (r x), ?_, key⟩
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections x
  have hsc : ContinuousOn s U := continuousOn_pi.2 fun p => holoOn_continuousOn hU (hh p)
  have hcomp : ContinuousOn (F ∘ s) U := hF.comp hsc fun y hy => (hs y hy).1.1
  refine (hcomp.continuousAt (hU.mem_nhds hx)).congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  have h := key (s y) (hs y hy).1
  rw [(hs y hy).2] at h
  exact h.symm

theorem log_h_torusSmul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h (torusSmul c z)) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have h1 : A.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have h2 : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [h1, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => h2 k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => h2 k)]
  simp only [Real.log_zpow]

theorem log_h_continuousOn {A : HermLine J} (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log hA.continuousOn fun z hz => (A.pos z hz).ne'

end General

theorem logDiff_descends : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb hNb hdeg
  have hA : ∀ p, ∃ A : HermLine J, p ∈ D.SB B → A.a = D.vdeg p ∧ IsSmoothHerm A ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z := by
    intro p
    by_cases hp : p ∈ D.SB B
    · obtain ⟨A, h1, h2, -, h3⟩ :=
        (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D p (Finset.mem_of_mem_filter p hp)).1
      exact ⟨A, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨S.ref, fun h => absurd h hp⟩
  choose A hA using hA
  have hdegk : ∀ k, (Nb.a k : ℝ) = (S.ref.a k : ℝ) + ∑ p ∈ D.SB B, ((A p).a k : ℝ) := by
    intro k
    have href : S.ref.a = Hd.aMu := S.ref_deg
    have hs : ∑ p ∈ D.SB B, (A p).a k = ∑ p ∈ D.SB B, D.vdeg p k :=
      Finset.sum_congr rfl fun p hp => by rw [(hA p hp).1]
    have : Nb.a k = S.ref.a k + ∑ p ∈ D.SB B, (A p).a k := by
      rw [hdeg, href, hs]
      simp [muTwDeg, Finset.sum_apply]
    rw [this]
    push_cast
    rfl
  obtain ⟨κ, hκ, hκe⟩ := exists_continuous_descent M
    (fun z => Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log ((A p).h z))
    (((log_h_continuousOn hNb).sub (log_h_continuousOn S.ref_smooth)).sub
      (continuousOn_finsetSum _ fun p hp => log_h_continuousOn (hA p hp).2.1))
    (by
      intro c hc z hz
      have hb := hz.1
      simp only [log_h_torusSmul _ hc hb, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := D.SB B)]
      simp only [hdegk, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      ring)
  refine ⟨κ, hκ, fun z hz => ?_⟩
  rw [hκe z hz]
  congr 1
  exact Finset.sum_congr rfl fun p hp => by rw [(hA p hp).2.2 z hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.Descent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_positive_potential_dominating : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (Φ : ReciprocityTheory.AnForm.M.LocPot M.Xc), ReciprocityTheory.AnForm.M.IsPotential M.atlas Φ → ∃ Θ : ReciprocityTheory.AnForm.M.LocPot M.Xc, ReciprocityTheory.AnForm.M.IsPotential M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPosPot M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPsh M.atlas (Φ + ReciprocityTheory.AnForm.M.LocPot.ofFun (fun _ => 0) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_posPot_dominating | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_posPot_dominating | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_posPot_dominating <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.height_polynomial_reflection_sum : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.thmA_limit | exact GlobalTheory.CompanionTheory.Ar.PB.thmA_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.thmA_limit <;> assumption)
end

section


theorem _root_.GlobalTheory.T.top_mixed_limit_of_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.TopNMixedLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit | exact GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ptsIntegrable_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement :=
  fun h => GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (GlobalTheory.T.resolution_exists_of_resolution_statement h)

end GlobalTheory.CompanionTheory.Ar.Giv
end
