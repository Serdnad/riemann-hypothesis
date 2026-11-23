module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle686
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle763
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle709
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle717
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle736
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.adelicData_extend_largerFields_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExt0 := by
  first | exact @GlobalTheory.Mem.R3.Rw.datExt0_of_hypotheses | exact GlobalTheory.Mem.R3.Rw.datExt0_of_hypotheses | (intros; apply GlobalTheory.Mem.R3.Rw.datExt0_of_hypotheses <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_pointPoly_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw) (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have h0 := GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw)
    (GlobalTheory.T.chernTop_pointClass_hodge_metric_lie_nonneg E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL)
  have h1 := GlobalTheory.T.hodgeMetric_pointClassForm_mass_eq_covolume E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have hc := (GlobalTheory.TrueCx.covol_pos (U.X k)).le
  refine ⟨fun ε => ?_, ?_⟩
  · rcases Int.units_eq_one_or ε with rfl | rfl
    · rw [h1]; exact ENNReal.ofReal_ne_top
    · rw [h0]; exact ENNReal.zero_ne_top
  · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, h1, h0, ENNReal.toReal_ofReal hc]; simp

end GlobalTheory.LieBase
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.LieBaseGood

theorem lieGram_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ch, a, ha, g, rk, τ₀, B, hP, hHolo, hys, hy0, hpoly, hbd, A, hA, Q, hQ, hcard, hind, hform, horth⟩ :=
    GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint E H Dw l Xo c O β Y T F e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ρ, hρ, hρ2, c₀, N₀, hb⟩ := GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart X.dim a ha g rk τ₀ B hP
  let W : Set (ReciprocityTheory.L2DbarEstimates.V X.dim) :=
    (ch.target ∩ ch.symm ⁻¹' GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j)) ∩
      WithLp.ofLp ⁻¹' GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ
  have hWo : IsOpen W := (ch.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
    ((GlobalTheory.HodgeChartRow.isOpen_punctured ha ρ).preimage (PiLp.continuous_ofLp 2 _))
  let G₀ : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin g) (Fin g) ℂ :=
    fun u => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹
  let Q' : ∀ τ : E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u => Q τ u.ofLp
  have hdo : Differentiable ℂ (WithLp.ofLp : ReciprocityTheory.L2DbarEstimates.V X.dim → Fin X.dim → ℂ) :=
    (EuclideanSpace.equiv (Fin X.dim) ℂ).differentiable
  have hQ' : ∀ τ i k, DifferentiableOn ℂ (fun u => Q' τ u i k) (Metric.ball 0 1) := by
    intro τ i k
    refine (hQ τ i k).comp hdo.differentiableOn fun u hu k' => ?_
    exact (PiLp.norm_apply_le u k').trans_lt (by simpa using hu)
  have hind' : LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q' p.1 0 p.2) := by
    simpa [Q'] using hind
  have hG₀ : ∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧
      GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c₀ N₀ G₀ v := by
    intro v hv
    obtain ⟨hpd, hcd, hgb⟩ := hb v hv.2
    refine ⟨?_, hcd, hgb⟩
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hpd.det_pos.ne')).ne_zero
  have horth' : ∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q' τ v * G₀ v * (Q' τ' v)ᴴ = 0 := by
    intro v hv τ τ' hne
    have := horth (ch.symm v) (ch.map_target hv.1.1) hv.1.2 τ τ' hne
    rwa [ch.right_inv hv.1.1] at this
  obtain ⟨r', hr', c', N', hfr⟩ := GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands X.dim g (Finset.univ.map (Fin.castLEEmb ha)) W G₀ c₀ N₀ (E →+* ℂ)
    Dw.mult Q' 1 hWo one_pos hQ' hcard hind' hG₀ horth'
  refine ⟨ch, Finset.univ.map (Fin.castLEEmb ha), hHolo, hys, ?_, ?_, A, hA, c', N', ?_⟩
  · intro b _
    rw [hy0]
    rfl
  · intro z hz
    rw [hbd z hz]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.castLE ha i, by simp, hi⟩
    · rintro ⟨b, hb', hb0⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb'
      exact ⟨i, hb0⟩
  · have h1 : ∀ᶠ z in nhds y, z ∈ ch.source ∧ ch z ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V X.dim) (min r' ρ) :=
      Filter.Eventually.and (ch.open_source.mem_nhds hys) ((ch.continuousAt hys).preimage_mem_nhds
        (by rw [hy0]; exact Metric.ball_mem_nhds _ (lt_min hr' hρ)))
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzO τ
    obtain ⟨hzs, hzb⟩ := hz
    rw [mem_ball_zero_iff] at hzb
    have hzW : ch z ∈ W := by
      refine ⟨⟨ch.map_source hzs, Set.mem_preimage.2 (by rw [ch.left_inv hzs]; exact hzO)⟩, ?_, ?_⟩
      · exact fun k => (PiLp.norm_apply_le _ k).trans_lt (hzb.trans_le (min_le_right _ _))
      · intro i hi
        exact (hbd z hzs).2 ⟨i, hi⟩ hzO
    have hGB := hfr (ch z) hzW (hzb.trans_le (min_le_left _ _)) τ
    refine GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram X.dim _ _ c' N' _ _ (ch z) ?_ hGB
    filter_upwards [hWo.mem_nhds hzW] with u hu
    have := hform (ch.symm u) (ch.map_target hu.1.1) hu.1.2 τ
    rw [ch.right_inv hu.1.1] at this
    exact this.symm

end GlobalTheory.LieBaseGood
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.barycentricSubdivision_star_step_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab φ : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → IsTwInv H φ → IsBaryStage H.bar q ψ lab φ (i + 1) → ∃ φ' : InvFun (𝓞 E), IsTwInv H φ' ∧ IsBaryStage H.bar q ψ lab φ' i := by
  first | exact @GlobalTheory.PolFan.baryStep | exact GlobalTheory.PolFan.baryStep | (intros; apply GlobalTheory.PolFan.baryStep <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_starSubdivision_removes_maxMultiplicity_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
      Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' ≤ M ∧ MultCellsAmong H.bar q φ' M n := by
  first | exact @GlobalTheory.PolFan.exists_star_drop_multCells | exact GlobalTheory.PolFan.exists_star_drop_multCells | (intros; apply GlobalTheory.PolFan.exists_star_drop_multCells <;> assumption)
end
