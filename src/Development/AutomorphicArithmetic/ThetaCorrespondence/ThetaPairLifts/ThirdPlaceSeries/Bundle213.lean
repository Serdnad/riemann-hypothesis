module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
public import Development.AutomorphicArithmetic.LocalEmbeddings.BadRepAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle198
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RefExpPadicValLeShiftOfWeightFree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle089
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle151
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle098
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle073
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle211
public import Formalism.LocalRingCardinality.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle100
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle212
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem

@[expose] public section

section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefFlat
theorem flatExistsAt_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → FlatExistsAt (p.T.U ((i : ℕ) + 1)) (xiR D) (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF
  obtain ⟨hDC, -, -, -⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A M hR hi hG hW hH hF
  intro Z τ
  refine ⟨GlobalTheory.FlatLine.Definite.nonempty_flatSec _ _ hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ, fun s => ?_⟩
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_definiteRationalPointData_component _ _ _ _ _ _ _ _ _ hDC Z
  have h1 := (GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s
  have h2 := _root_.GlobalTheory.T.degLie_eq_neg_flatDegVal_at_last_index p i PP A M hR hi hG hW hH hF Z P τ
  rw [neg_neg]
  linarith
end GlobalTheory.DefFlat
end
end

section

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_type_lattice_comparison_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (Fm.D x ι).ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  intro _ _ _
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  exact GlobalTheory.CovTop.BadRep.badRep_at p i Y hY
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem row_hRB_univ_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotRowBoundCondition Q Lk := by
  intro hDS hHC hRD hCW Q Lk
  refine Row.of_sel fun 𝒜 σ _ _ Fm hc x hx i => ?_
  exact _root_.GlobalTheory.T.indefinite_scale_theta_bound_right_alt hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge
    (_root_.GlobalTheory.T.indefinite_scale_theta_equality_alt hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B).1
end GlobalTheory.Fc.R1
end
end
end

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.joint_of_famAllQ_of_servedQ : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → _root_.GlobalTheory.MiTop.JointCondition W := by
  first | exact @_root_.GlobalTheory.MiTop.joint_of_famAllQ_alt | exact _root_.GlobalTheory.MiTop.joint_of_famAllQ_alt | (intros; apply _root_.GlobalTheory.MiTop.joint_of_famAllQ_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_family_column_data_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → (∀ k : _root_.GlobalTheory.Fam.FamilyConstants a, ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (row := row) (col := col) k w₀ w F) → ∃ col, (a.fam row col).RowOK ∧ LawsX (a.fam row col).t ∧ _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkTailCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkCommutes (a.fam row col) ∧ _root_.GlobalTheory.MiTop.FamilyRatioCondition (a.fam row col) := by
  first | exact @_root_.GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt | exact _root_.GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt | (intros; apply _root_.GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt <;> assumption)
end
end

section



section
section
set_option autoImplicit false

noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum.ToWeight
theorem refinedSum_weight_of_refinedTheta_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceTheta → _root_.GlobalTheory.RefSum.ReferenceWeight := fun hP hS hF hT =>
  Closed.imp (Closed.and (Closed.and hT (_root_.GlobalTheory.BadLog.logSum_badPrimes_le_alt hS))
      (Closed.and hF (Closed.and (_root_.GlobalTheory.T.lenT_zBase_unitE_nCol_bounds hS) (_root_.GlobalTheory.T.quotient_weight_gap_bounds' hS))))
    fun Fm _ _ ⟨⟨⟨C₁, h₁, hT⟩, C₂, h₂, hB⟩, ⟨_, _, hF⟩, ⟨_, _, hZ⟩, _, _, hW⟩ => by
      obtain ⟨x0, h⟩ := ((hT.and hB).and hF).and (hZ.and hW)
      refine ⟨C₁ + (30 + C₂), by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
      obtain ⟨⟨⟨hT, hB⟩, hF⟩, hZ, hW⟩ := h x hx hle ι p hp
      obtain ⟨S, e, s, hS, hs, he⟩ := hT i hi Y hY u1 hq
      obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hZ i
      obtain ⟨w1, w2, -, -, -, -, -, -, w3⟩ := hW i hi u1 hq
      have hB := hB i hi Y hY
      have hm : 2 * ((nCol (dat p i) / 2 : ℕ) : ℝ) ≤ nCol (dat p i) := by exact_mod_cast Nat.mul_div_le _ 2
      have hsz := size_le (by exact_mod_cast z5) (by exact_mod_cast z6) z2 (Nat.cast_nonneg _) hm z4 z3 h₂ hB
      refine ⟨_, _, _, primeSum_add (Fm.D x ι).host.E (B := badPrimes p.T.Q.H Y.d.l₂)
        (a := ((nCol (dat p i) / 2 : ℕ) : ℝ) * ((Fm.D x ι).R.f * (Fm.D x ι).R.r)) hS badPrimes_prime (by positivity), ?_,
        fun q hq' => ?_⟩
      · have a1 := mul_le_mul_of_nonneg_left hsz (Nat.cast_nonneg (lenT p i (Fm.parT x hx ι).PP))
        have a2 := mul_le_mul_of_nonneg_left z1 (show (0 : ℝ) ≤ 30 + C₂ by positivity)
        unfold zBase at a2
        linarith
      · refine (_root_.GlobalTheory.T.reference_exponent_valuation_bound hP _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, hi.le⟩ hY.1 w1 w2 ⟨_, hF i hi Y hY⟩ u1
          (shift (dat p i) u1 (nCol (dat p i))) (nCol (dat p i) / 2) (1 / 2500) q hq').trans ?_
        rw [EReal.coe_add]
        exact add_le_add (w3 ▸ he q hq') le_rfl
end GlobalTheory.RefSum.ToWeight
end
end
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem _root_.GlobalTheory.T.refW_of_prints_size_flatDeg_refTheta : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceTheta → _root_.GlobalTheory.RefSum.ReferenceWeight := by
  first | exact @_root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt | exact _root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt | (intros; apply _root_.GlobalTheory.RefSum.ToWeight.refinedSum_weight_of_refinedTheta_alt <;> assumption)
end
end
end

section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.geoSt_of_pageSt' : _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.GeometricStatement' := by
  first | exact @_root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt | exact _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt | (intros; apply _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt <;> assumption)
end
end

section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

theorem _root_.GlobalTheory.T.latIoAt' : _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.SerBase.latIoAt_alt | exact _root_.GlobalTheory.BigOn.Exp.SerBase.latIoAt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.SerBase.latIoAt_alt <;> assumption)
end
end
