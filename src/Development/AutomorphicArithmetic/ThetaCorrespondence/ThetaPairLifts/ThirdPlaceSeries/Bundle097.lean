module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle078
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle067
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle069
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle080
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle060
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.choiceSide_alt {low Pq S hk eig θ} {Bs : SideB D cf A.row low Pq S hk eig θ} (x : ChoiceSide D cf M Bs.exp C tp) : ChoiceSide m.D (m.cf cf) (m.mt M) (m.sideB_alt Bs).exp (m.ch C) (m.tp tp) := @_root_.GlobalTheory.HeightCounting.ChoiceSide.mk (_) (_) (_) (_) (_) (_)
    (nct := @_root_.Formalism.BasicNotions.NChTie.mk (_) (_)
      (twOf_eq := (by with_unfolding_all exact (x.nct.twOf_eq :)))
      (twSide_eq := (by with_unfolding_all exact (x.nct.twSide_eq :)))
      (Q_eq := (by with_unfolding_all exact (x.nct.Q_eq :)))
      (psi_eq := (by with_unfolding_all exact (x.nct.psi_eq :)))
      (embedding_baseField_condition := (by with_unfolding_all exact (x.nct.embedding_baseField_condition :))))
    (choice := @_root_.GlobalTheory.HeightCounting.ChoiceC.mk (_) (_)
      (twI_conj := (by with_unfolding_all exact (x.choice.twI_conj :)))
      (sd_place := (by with_unfolding_all exact (x.choice.sd_place :)))
      (emb_side := (by with_unfolding_all exact (x.choice.emb_side :)))
      (sd_conj := (by with_unfolding_all exact (x.choice.sd_conj :)))
      (one := (by with_unfolding_all exact (x.choice.one :)))
      (conj := (by with_unfolding_all exact (x.choice.conj :))))
    (off := (by with_unfolding_all exact (x.off :)))
    (adm := (by with_unfolding_all exact (x.adm :)))
    (psi := (by with_unfolding_all exact (x.psi :)))
    (eMt_level := (by with_unfolding_all exact (x.eMt_level :)))
end
section
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_mtAd_psiVectorLocal_of_yRel :
    ∀ {hL : UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre}
      {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P}
      (L : LocAll (lay0 (Dof x))) (l : StrictHenselianAcyclicLevel hL x)
      {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0),
      YRel L Y → ∃ ad : MtAd Y (localMultiplicityFamily L l), ad.PV = psiVectorLocal L l :=
  @GlobalTheory.HeightCounting.Fin3.exists_mtAd_psi_vector_of_yRel
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.tauTrue_alt {a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C} (x : TauTrue a.exp) : TauTrue ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a).exp := (by with_unfolding_all exact (x :))
end
end GlobalTheory.LayerMove
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.selection_closed_of_wu_decay_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.SG.JoinSISel.BaseVectorImageFull (Fm.D x i))
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH), Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  intro 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have jGap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm,
      _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) fun x _ _ i => Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
    (Formalism.L2.SG.GapClosed.gapEv_closed_of (D3 3 𝒜) fun _ hc => hc.2.2.1).imp fun Fm _ _ h hc => by
      obtain ⟨y, hy⟩ := h hc
      exact ⟨y, fun x _ _ hxy i => hy x hxy i⟩
  have hM : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection (fun Fm hc => sel Fm (d3_a hc)) Fm hc fun x hx h i =>
      _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationMultiplicityCondition ((_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc) x hx h i) :=
    rRows.imp fun Fm CH _ h hc => by
      obtain ⟨C, _, x0, H⟩ := h hc
      exact ⟨x0, fun x hx hs hx0 i => (H x hx hs hx0 i).1.miStar⟩
  have hFX := _root_.Formalism.L2.SG.JoinSISel.closed_finX_of_gapHyp (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
    (selS := fun Fm hc => selS Fm (d3_a hc)) (Formalism.L2.SG.Pf.finXC_of hWu hRF)
    jGap
  have hC5 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm :=
    _root_.Formalism.L2.SG.JoinSISel.complementFive_closed_of_image_v0 (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
      (selS := fun Fm hc => selS Fm (d3_a hc)) (selP := fun Fm hc => selP Fm (d3_a hc)) (selDH := fun Fm hc => selDH Fm (d3_a hc))
      (selC := fun Fm hc => selC Fm (d3_a hc)) (selK := fun Fm hc => (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) Fm (d3_a hc)) (selI := fun Fm hc => (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc))
      (fun Fm hc => selJ Fm (d3_a hc)) hM hFX jOn
  exact hC5
end
end
