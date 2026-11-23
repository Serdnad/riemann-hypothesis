module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle247
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle844
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle558
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle245
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle151
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle389
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle158
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle277
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle279
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle265
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle274
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle250
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle267
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle183
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle189
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle157
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

@[expose] public section

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt
theorem localGalois_parameter_mem_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  intro hN _ hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.T.good_cusp_param_at_member_of_heq_locR hN hL) (_root_.GlobalTheory.T.exists_loc_with_place_and_index_at_member hN hL))
    (_root_.GlobalTheory.T.exists_twisted_place_at_member hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c _ H Rw hRw
  obtain ⟨⟨hp, hl⟩, v, hv⟩ := H
  have hW := _root_.GlobalTheory.GalLoc.RowParamAt.locW_of_nTrue_alt c.a.nt Rw hRw
  refine GlobalTheory.TwInputs.rowParam_of_cuspParam (w.D Z) Rw (hp Rw hRw) ?_ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw _)
  intro j h1 h2 σ hσ hg
  obtain ⟨i, -, -⟩ := hl v hv j h1 h2 σ hσ
  exact GlobalTheory.HeightCounting.CuspOfParam.goodRow_cuspidal (w.D Z) Rw ⟨i⟩ hW (hp Rw hRw) j h1 h2 σ hσ hg
end GlobalTheory.GalLoc.RowParamAt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.local_param_at_member_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  first | exact @_root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | exact _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieChiPin
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → PairedCharacterCondition.tieChi (D := D) := by
  intro hPr hL D P hRow hLab hChi i k hl v
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hPr.fin hL D P hRow
  have hsp : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨htame, hχ, u, hu, hlab⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hPr hL D P hChi S hS i k v hsp
  refine ⟨u, hu, fun w hw => ⟨fun hw0 => ?_, fun hc => ?_⟩⟩
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd, hw0]
    rw [_root_.GlobalTheory.LabFixed.labLP_twist_eq_labAt_ofDet hPr hL D P S hS i k v hsp hχ, hlab]
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd]
    exact _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt hPr hL D P hLab S hS i k v hsp hχ u htame hlab w hc _
end GlobalTheory.TieChiPin
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAll
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  intro hP hHC hCusp hL D I hJ
  have a : _root_.GlobalTheory.NRows.RowsAAlt D := _root_.GlobalTheory.T.thetaLocal_a_conditions_of_jumpsCard hP hL D I.P hJ
  obtain ⟨J⟩ := _root_.GlobalTheory.T.nonempty_join_of_agree hHC hCusp hL D I.P I.X I.agree
  obtain ⟨lamLoc, rank⟩ := GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars D I.isot I.lam
  obtain ⟨b, trip⟩ := _root_.GlobalTheory.T.b_conditions_pairLift_splitBC_repOfLoc_of_a hP hL D I.P J a I.adm1 lamLoc
  have Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D := I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) a b
  have c : GlobalTheory.NRows.RowsC D := _root_.GlobalTheory.T.c_statement_of_pair_lift_splitBC_repOfLoc hL D I.P J a b I.adm1 I.isot Conclusion1 trip
  refine ⟨a, b, c, fun i => ?_, rank⟩
  exact _root_.GlobalTheory.T.type_nonzero_recursion_of_eigen' hL D I.P I.X I.agree I.typeNZ i
    (_root_.GlobalTheory.T.eigString_of_agree_aux41_adm7_tieLab hP.fin hL D I.P I.X I.agree Conclusion1.1 a.temp a.tieLab i)
    (_root_.GlobalTheory.T.eigGood_of_archimedean_signature_adm5 hL D I.P I.X Conclusion1.1 a.tieLab I.mtPar I.adm1 a.tie0 b.a4 a.a5 I.e0loc I.e0read i)
end GlobalTheory.RowsAll
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_conditions_of_inputs_of_jumpsCard : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  first | exact @_root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
