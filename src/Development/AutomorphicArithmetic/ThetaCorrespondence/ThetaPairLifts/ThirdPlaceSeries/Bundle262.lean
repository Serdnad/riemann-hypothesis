module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSqOfRamificationIdx
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle271
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle647
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle569
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle559
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle608
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaEqLam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle378
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle395
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle607
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle026
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange

@[expose] public section

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Rigid
theorem rigid_raw_packet_eq_pow_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a
end GlobalTheory.HeightCounting.Rigid
end
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.ParLawsBare
open GlobalTheory.RowTie GlobalTheory.NPin Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.GlobalTheory.ParLawsBare.mainTheorem : Prop :=  _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ (D : D7) (cf : CharFrame D) rep Rw,
    IsEmpty D.nd.Loc → _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw → _root_.GlobalTheory.HeightCounting.Up.ParityLaws D
end GlobalTheory.ParLawsBare
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.JointConditionThird
theorem upper_ramification_joint_condition_third_jump_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalDatumCompatibility D' := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  refine GlobalTheory.DesignBC.jointCond_of_definite _ fun j h1 h2 => ?_
  have h := (w.st x.o.Z).B.toPre.V_posDef j h1 h2
  intro τ
  exact Or.inl (h τ)
end GlobalTheory.HeightCounting.Up.JointConditionThird
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.IdxAt
theorem exists_divisor_eigenvalueIndex_labeling_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t _ _ _ => ∃ (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd), Nonempty (E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) := by
  intro _ hL
  have e0 : EvLgG fun _ _ _ _ => True :=
    evG_good.imp fun _ _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ => trivial⟩
  unfold _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint
  refine e0.imp fun K _ _ _ _ hK => ?_
  refine hK.imp fun B f T _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  letI : Algebra (↥t.r.z.core.Q.c.F) (w.D Z).what₂.LL := t.r.z.alg
  refine ⟨GlobalTheory.Mem.Top.DivRec.x0 t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange, GlobalTheory.eigIdxFiniteTypes _ _, ⟨fun σ => ?_⟩⟩
  have hc := (t.r.intersectionNumber_baseChange.ok.ok2.what₂ (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.μ0).comm
  let p := GlobalTheory.Mem.Top.DivRec.labOf t.r.Z t.r.intersectionNumber_baseChange σ
  exact ⟨p.1.1, Formalism.L2.DIV.InertDat3.mem_ixFin_fst _ hc p.2⟩
end GlobalTheory.HeightCounting.Up.IdxAt
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

theorem _root_.GlobalTheory.T.exists_eigIdx_labeling_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ T w Z Wt _ t _ _ _ => ∃ (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd), Nonempty (E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt | exact _root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IdxAt.exists_divisor_eigenvalueIndex_labeling_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up
theorem heckeCharacter_tuple_layer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ n _ => ∀ μ, Used0 (w.D Z) μ → t.r.z.R.toLevCh.xiH (t.r.Y.tupT μ) = n.tp.xi μ := by
  intro _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ μ hμ => ?_
  have a := t.r.z.lev.xiH (t.r.Y.tupT μ)
  have b := t.r.Y.tupTie μ hμ
  have d := congrFun n.xi μ
  refine a.trans (Eq.trans ?_ d.symm)
  exact congrArg w.I.xi ((t.r.tup_ix _).symm.trans b)
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

theorem _root_.GlobalTheory.T.xiH_tupT_eq_tp_xi_of_used0_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ n _ => ∀ μ, Used0 (w.D Z) μ → t.r.z.R.toLevCh.xiH (t.r.Y.tupT μ) = n.tp.xi μ := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.heckeCharacter_tuple_layer_alt | exact _root_.GlobalTheory.HeightCounting.Up.heckeCharacter_tuple_layer_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.heckeCharacter_tuple_layer_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.PinLayer

theorem specialization_at_member_of_layer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a P := by
  intro hP hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  have e' : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  have hT : TypesTrue (w.D Z).ntypes (TC.cf w.I w.l Z).P (TC.cf w.I w.l Z).W := by
    show TypesTrue _ w.I.C.P w.I.C.W
    rw [w.C_eq]
    exact t.grp
  have hEl : Elem (w.D Z) := by
    refine ⟨fun y => ?_, fun j g => ((w.D Z).hc ((w.D Z).eTau.symm g)).e_int j, fun v hv => ?_⟩
    · exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
        (starRingEnd (w.D Z).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
    · have hc : ∀ p ∈ (w.D Z).host.levelPrimes, p.Prime ∧ p % ((w.D Z).host.QS * (w.D Z).host.q * (w.D Z).host.d) = 1 :=
        (w.st Z).B.level_cond
      rcases hv with hv | hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.1 v hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.2 v hv
  exact _root_.GlobalTheory.PinLayer.pinAt_of_side_alt c.a hP.greenC hT (GlobalTheory.HeightCounting.Up.valLL0_colW w Z)
    (fun σ => Formalism.IndefR.principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT σ)) c.row.rep_eq
    (fun σ σ' h => t.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) hEl
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) e'.labc e'.zeta
end GlobalTheory.PinLayer
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : _root_.GlobalTheory.NPin.CharacterChoiceData hL (w.D Z), _root_.GlobalTheory.HeightCounting.Up.PinnedAtCharacterChoice c.a P := by
  first | exact @_root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt | exact _root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt | (intros; apply _root_.GlobalTheory.PinLayer.specialization_at_member_of_layer_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.TypesAt
theorem inertialTypes_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  intro _ hL
  refine EvG.imp evG_good fun K _ _ _ _ _ => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T _ _ _ _ _ w Z Wt p0 t nch n xd c _ _ _
  exact typesTrue_rows t
end GlobalTheory.HeightCounting.Up.TypesAt
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

theorem _root_.GlobalTheory.T.typesTrue_at_member_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => TypesTrue (w.D Z).ntypes t.r.z.R.C.P t.r.z.R.C.W := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.TypesAt.inertialTypes_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.TypesAt.inertialTypes_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.TypesAt.inertialTypes_at_member_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.Mem.LamPosTw
theorem lambda_pos_of_twisted_mu_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → 0 < (w.D Z).what₂.lamP ((w.D Z).what₂.muTw v) j σ := by
  intro hP hL
  have e1 := evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  have e0 : EvLgG fun _ _ _ _ => True :=
    e1.imp fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ => trivial⟩
  unfold _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint
  refine (e0.inter e1).imp fun K _ _ _ _ H => ?_
  obtain ⟨hK, hH⟩ := H
  refine hK.imp fun B f T hO _ _ w Z Wt p0 t nch n xd c _ _ _ v hTw j hj1 hjm σ hne => ?_
  letI : Algebra (↥t.r.z.core.Q.c.F) (w.D Z).what₂.LL := t.r.z.alg
  have host : Formalism.IndefR.Links.HostHyp (w.D Z) := (hH (w.st Z) hO).1
  obtain ⟨p, hp⟩ := GlobalTheory.Mem.LamPosTw.hasLab_exists hP.decay (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0
    t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange host σ
  have hi : j - 1 < (w.D Z).R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin (w.D Z).R.m) : ℕ) + 1 = j := by simp only; omega
  have hmu : (w.D Z).what₂.muTw v = t.r.Y.tup (t.r.z.R.mu ((w.D Z).plEq v)) := by
    rcases (w.D Z).what₂.muAt_or v with h | h
    · exact absurd h hTw
    · rw [← h]; exact t.r.Y.muAt v
  have key := GlobalTheory.Mem.LamPosTw.eigenvalue_eq_of_label (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.Z t.r.z.pins
    t.r.intersectionNumber_baseChange host σ p ⟨j - 1, hi⟩ (t.r.z.R.mu ((w.D Z).plEq v)) hp (Or.inr ⟨v, (t.r.Y.muAt v).symm⟩) (by rw [hj']; exact hne)
  rw [hj'] at key
  rw [hmu, key]
  exact t.r.intersectionNumber_baseChange.prim.posScal.2 _ _ _ _
end GlobalTheory.Mem.LamPosTw
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.lamP_muTw_pos_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → 0 < (w.D Z).what₂.lamP ((w.D Z).what₂.muTw v) j σ := by
  first | exact @_root_.GlobalTheory.Mem.LamPosTw.lambda_pos_of_twisted_mu_alt | exact _root_.GlobalTheory.Mem.LamPosTw.lambda_pos_of_twisted_mu_alt | (intros; apply _root_.GlobalTheory.Mem.LamPosTw.lambda_pos_of_twisted_mu_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ParamsLayer
theorem parameters_gap_regular_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ ∀ (τ : (w.D Z).what₂.Tau) (n : ℕ), n + 1 < (w.D Z).R.r → 100 * ((w.D Z).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) n - Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) (n + 1) := by
  intro _ hL
  have e := (evG_of_ev GlobalTheory.Mem.RowsLed.ev_exists_sizeData_of_rows).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  refine EvG.imp e fun K _ _ _ _ hK => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w Z Wt p0 t nch n xd c _ _ _
  obtain ⟨L, -, hP⟩ := hK.1 B f T w Z Wt p0 t hO
  exact ⟨⟨L, hP⟩, (hK.2 (w.st Z) hO).1.gapR⟩
end GlobalTheory.HeightCounting.Up.ParamsLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

theorem _root_.GlobalTheory.T.exists_parameter_choice_and_lamAt_gap_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ ∀ (τ : (w.D Z).what₂.Tau) (n : ℕ), n + 1 < (w.D Z).R.r → 100 * ((w.D Z).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) n - Formalism.L2.NTheta.lamAt ((w.D Z).hc τ) (n + 1) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ParamsLayer.parameters_gap_regular_alt | exact _root_.GlobalTheory.HeightCounting.Up.ParamsLayer.parameters_gap_regular_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ParamsLayer.parameters_gap_regular_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading
namespace GlobalTheory.HeightCounting.Up.CoefficientAgreement
theorem coefficientField_tied_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => t.r.z.R.C = TC.cf w.I w.l Z := by
  intro _ hL
  exact _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.atMem_of_forall' fun K B f T w Z Wt p0 t nch n c => t.r.z.lev.C
end GlobalTheory.HeightCounting.Up.CoefficientAgreement
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

theorem _root_.GlobalTheory.T.coefField_eq_TC_cf_at_member_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ => t.r.z.R.C = TC.cf w.I w.l Z := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.coefficientField_tied_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.coefficientField_tied_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.CoefficientAgreement.coefficientField_tied_at_member_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.InW1TwistAtMember
theorem twist_mem_weightOne_subspace_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  intro _ _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  intro a
  rw [n.tie.twOf_eq a]
  exact GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.D Z) nch n.tie B.coeffGaloisSubfield_isGalois _ ((w.D Z).nd.w_tw a)
end GlobalTheory.HeightCounting.InW1TwistAtMember
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.nonzero_index_place_tw_of : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  first | exact @_root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | exact _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | (intros; apply _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt <;> assumption)
end
end
end

section



section
section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
structure LocalLanglandsHypothesis (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop where
  pr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt
  ser : SerN
  arch : _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL
  par : _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL
  pt : _root_.GlobalTheory.HeightCounting.Up.PointStatement hL
  parMem : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw)
end
end GlobalTheory.Mem.Top.Bl
end
end
end
end
