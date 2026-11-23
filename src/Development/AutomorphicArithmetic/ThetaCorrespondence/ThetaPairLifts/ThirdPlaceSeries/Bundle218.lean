module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle098
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle157
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle215
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle127
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle200
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle196
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle112
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle136
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667

@[expose] public section

section



section
section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.DefCore
theorem defect_bound_of_connected_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _hP
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hp hi hg hw hh hF
  obtain ⟨hdef, hfin, hne, hdict⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A 0 hp hi hg hw hh hF
  obtain ⟨G, _, _, lev, χ, hact, hfree, hsl⟩ := _root_.GlobalTheory.T.exists_finite_group_actLev_char p i PP A 0 hp hi hg hw hh hF
  have hflat := _root_.GlobalTheory.T.flatExistsAt_last_index_of_fnAlgClosed p i PP A 0 hp hi hg hw hh hF
  have h := (GlobalTheory.T.eigenlattice_slope_lower_bound_definite_case D _ _ _ _ _ _ (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) G lev χ
    (wtA (p.κ i)) (p.κ i).n _ hdef hfin hne hdict hact hfree hw.dom hg.2.2.2 hflat).2
  unfold Gk at hsl
  linarith
theorem lifts_two_mul_defBound_sub_unitE_le_muCore : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  intro hP
  obtain ⟨M1, C1, hC1, h1⟩ := _root_.GlobalTheory.CovTop.DefCore.defect_bound_of_connected_alt hP
  obtain ⟨M2, C2, hC2, h2⟩ := _root_.GlobalTheory.T.two_defBound_sub_unitError_le_muCore_alt hP
  have hW : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  have hH1 : _root_.GlobalTheory.CovTop.HostNAlt M1 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt M1
  have hH2 : _root_.GlobalTheory.CovTop.HostNAlt M2 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt M2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.HostNAlt at *
  refine Closed.imp ((hW.and hH1).and hH2) ?_
  rintro eps Fm CH - ⟨⟨⟨Cw, -, xw, hw⟩, ⟨A1, -, x1, ha1⟩⟩, ⟨A2, -, x2, ha2⟩⟩
  refine ⟨max C1 C2, le_max_of_le_left hC1, max (max xw x1) x2, fun x hx hle ι p hp i hi hg => ?_⟩
  have hle1 : xw ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hle2 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have hle3 : x2 ≤ x := le_trans (le_max_right _ _) hle
  have w := hw x hx hle1 ι p hp i
  have a1 := ha1 x hx hle2 ι p hp i
  have a2 := ha2 x hx hle3 ι p hp i
  have hu := unitE_nonneg p i _ _ _ w a1
  by_cases hF : FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c)
  · have := h1 p i _ _ hp hi hg w a1 hF
    nlinarith [le_max_left C1 C2]
  · have := h2 p i _ _ hp hi hg w a2 hF
    nlinarith [le_max_right C1 C2]
end GlobalTheory.CovTop.DefCore
end
end
section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.two_mul_defBound_sub_le_muCore_of_gramAt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore | exact _root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore | (intros; apply _root_.GlobalTheory.CovTop.DefCore.lifts_two_mul_defBound_sub_unitE_le_muCore <;> assumption)
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.SerRefCore
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SerRefPt
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Core
end GlobalTheory.SerRefPt
namespace GlobalTheory.SerRefPt
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

theorem fw_eq_zero_or_exists_norm_algComb (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (hR : p.PointConditions')
    (hM : More p) (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m) (h0 : RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j)
    (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool) (h : RealPin p.R p.cG ρ) :
    (∀ y ∈ (p.R.FW j).WK, y = 0) ∨ ∃ ν, IsNorm p.R p.v₀ (ρ.B t j b) ν ∧ ∀ s g P, ρ.IsDatum t j b s g P →
      P ∈ ρ.lat t j b (smallInt (Fm.D x i)) g → AlgComb p.nexp p.v₀ j (ν • ρ.theta t j b g P) := by
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 hP Fm x hx i p hR hM t j h0)
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w hw h0.unif
  have hG : (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).toRealDat.IsFam := { c.fam with }
  have hMo : (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).toRealDat.IsModels := { c.models with }
  have hCh : (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).toRealDat.IsChain := { c.chain with }
  have hTh : (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w).phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w) (F2 p) B'.κ B'.v₀ B'.O t j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  have hpin' : RealPin (_root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w) p.cG ρ :=
    ⟨h.psi, h.inf, h.cartT, h.onbS, h.onbT, h.latS, h.latT, h.frS, h.frT, h.vac, h.Pg, h.grp, h.mu0, h.eta, h.delta, h.deltaPl,
      h.ap, h.am⟩
  have hsp : (Fm.D x i).host.cls (Fm.D x i).host.pde = PrimeClass.splitK ∧
      (Fm.D x i).host.cls (Fm.D x i).host.pde' = PrimeClass.splitK :=
    ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩
  have H := core_cases (T := setCE p.T c') (Rl := _root_.GlobalTheory.UnframePt.fullHeckeRealDatMovedReadings p.R w) hA hRF hS (GlobalTheory.UnframeForms.movedYS p.nexp w) hρ b hpin' hRat hsp
  rw [hv] at H
  rcases H with H | ⟨ν, hN, H⟩
  · exact Or.inl H
  · exact Or.inr ⟨ν, hN, fun s g P hd hl => algComb_of_moved p.nexp w p.v₀ j (H s g P hd hl)⟩
theorem serRef_of_reciprocity_ray_class : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.SerRefAlt := by
  intro hP hA hRF hS
  have hL := _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt
  have hT := _root_.GlobalTheory.BigOn.Exp.twAdm_alt
  unfold _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace at hL
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt at hT
  unfold _root_.GlobalTheory.BigOn.Exp.SerRefAlt
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT).imp fun Fm x hx i p hp hM w _ j h => ?_
  intro ρ hρ ν hpin hN hR0
  refine ⟨ν, hN, hR0, fun s g P hd hl => ?_⟩
  rcases _root_.GlobalTheory.SerRefPt.fw_eq_zero_or_exists_norm_algComb hP hA hRF (GlobalTheory.SerStd.seriesRatS_of hS) Fm x hx i p hp hM _ j
    (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j) ρ hρ _ hpin with H | ⟨ν₁, hN₁, H⟩
  · have h0 := theta_eq_zero p.nexp p.v₀ hρ _ j _ H hR0 hd
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [h0, smul_zero]
      exact AlgComb.zero
    exact h1
  · obtain ⟨ζ, hζ, e⟩ := exists_root_of_isNorm p.R p.v₀ _ hN₁ hN
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [e, mul_smul]
      exact (H s g P hd hl).smul hζ
    exact h1
end GlobalTheory.SerRefPt
end
end
end
