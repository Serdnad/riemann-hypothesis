module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle121
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle150
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle162
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle163
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle157
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle432

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.central_adapted_element_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → (κ ∈ rowJ W.S.X W.Q.instEq ↔ Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H) := by
  first | exact @_root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | exact _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt | (intros; apply _root_.GlobalTheory.LevZeroMem.mem_rowJ_iff_rTup_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)),
    Continuous (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F) ∧
      ∀ γ ∈ GQ (Vc D j), ∀ h, _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * h) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h := by
  first | exact @_root_.GlobalTheory.ThetaFormV.formToVectorMap_continuous_and_left_invariant | exact _root_.GlobalTheory.ThetaFormV.formToVectorMap_continuous_and_left_invariant | (intros; apply _root_.GlobalTheory.ThetaFormV.formToVectorMap_continuous_and_left_invariant <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_lift_automorphic_form_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (y : D.what₂.Mj (D.nd.j i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)), (F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = (P.M.loc i).real x → inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i))) F ⟨Y.φ y, Y.φ_mem y⟩ := by
  first | exact @_root_.GlobalTheory.ThetaRead.main_alt_alt | exact _root_.GlobalTheory.ThetaRead.main_alt_alt | (intros; apply _root_.GlobalTheory.ThetaRead.main_alt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_lift_equivariance_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ → ∀ (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y y' : ↥Y.C), (F' : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : Y.A) = Y.ρ g y → _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (GlobalTheory.ThetaTri.valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' y' = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ φ F y := by
  first | exact @_root_.GlobalTheory.ThetaTri.lamI_inv_alt | exact _root_.GlobalTheory.ThetaTri.lamI_inv_alt | (intros; apply _root_.GlobalTheory.ThetaTri.lamI_inv_alt <;> assumption)
end
end

section



section
noncomputable section
namespace GlobalTheory.PtSt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
theorem reducedMultiplicity_of_rows' :
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  intro hL D I R i _
  have hInt : Rows.IsotInternal D.what₂ := I.isot
  have h42 : SumRepresentations.Conclusion42 D := (I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) R.a R.b).2.2
  have h1 := map_MjSig_eq D i hInt (h42 i) (R.c.parUp i) (R.c.downMem i) (R.typeNZ i)
  exact ⟨h1, (SumRepresentations.good_part_image_iff D.nd D.naut i hInt (h42 i) h1).2 (R.c.goodPart i)⟩
end GlobalTheory.PtSt
end
end
end

section



section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial
open Formalism.MainNotions.N.PlaceLabelTeichmuller
namespace UpperTheory.GalC
attribute [local instance] GlobalTheory.PassOp.factGk GlobalTheory.PassOp.neZeroGk
theorem exists_good_alt (hCen : ∀ (D : D7) (_ : PairedCharacterCondition.Pend D), GlobalTheory.Pass.CentralElt D) {D : D7} {nch : NChoice D} (hP : _root_.UpperTheory.GalC.GaloisPreconditions D nch)
    (hT : Tie4 D) : ∃ c : CutD D, c.Good := by
  classical
  obtain ⟨-, ⟨Q, hDZ, hEig⟩, -, hSer⟩ := hT
  have h0 : SumRepresentations.tie0 D := hP.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := hP.adm.1.1.2.2.1
  have h5 : SumRepresentations.adm5 D := hP.adm.1.1.2.2.2.2.2.2
  have h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D := hP.Conclusion1.1
  let Xs : ∀ i, Set (D.nd.X i) := fun i => {x | ∃ PI, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F ≠ 0}
  have hZ : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ D.nd.Z i := fun i x hx => (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
  have hgood : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ Xs i := fun i x hx => by
    obtain ⟨PI, hPI⟩ := D.naut.pt_surj i x
    obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i PI)
    exact ⟨PI, hPI, F, hF, by
      rw [(_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx]; exact hF0⟩
  refine ⟨⟨fun i => (D.nd.Zgood i).Nonempty, Xs, fun i ⟨x, hx⟩ => ⟨x, hgood i x hx⟩⟩,
    fun _ => Iff.rfl, hgood, fun i x hx ⟨PI, hPI, F, hF, hne⟩ => ?_, fun i _ => ?_, fun i _ P x ⟨PI, hPI, F, hF, hne⟩ hx k w hw => ?_⟩
  · by_contra hxg
    exact hne ((_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg)
  · obtain ⟨z, hact⟩ := exists_unit_one_add_generator D (hCen D Q) i
    refine ⟨Q.zO i z, Q.zO_comm i z, fun x hx u hu => ?_, fun x hx u hu => ?_⟩
    · have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
        rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx, map_natCast]) u hu
      rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
    · have := hEig i z x 0 (fun PI hPI F hF => by
        have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0 := by
          by_contra hne
          exact hx ⟨PI, hPI, F, hF, hne⟩
        rw [hact, e, smul_zero, map_zero, zero_smul]) u hu
      rw [this, zero_smul]
  · obtain ⟨s, hg, hs⟩ := exists_tuple D _ _ F hne
    have hn := nc_of_type D Q hDZ h1 h0 i PI hg (fun k v => exists_type D Q i PI F hF k v _ (hs k v)) k w hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨Pa', hB'⟩ := h1 i P
    have hperm : Pa.Perm Pa' := ((h41 i).2.1 PI P (by rw [hPI]; exact Option.some_ne_none x)
      (hPI.trans hx.symm)).1 Pa Pa' hB hB'
    have hB2 := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB'
    have hsp := GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw
    rwa [← hB.2.2.2.1 w hsp, hB2.2.2.2.1 w hsp] at hn
end UpperTheory.GalC
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut
namespace GlobalTheory.UnrNoChi
variable {D : D7} (i : D.nd.Loc)
end GlobalTheory.UnrNoChi
theorem GlobalTheory.UnrNoChi.main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  intro D L nch i r π ρ hF _ _ hHG hr _ hρ
  have hUnr := _root_.Formalism.MainNotions.N.admG4_of_goodR D i r hF.Conclusion1.1 hr
  have hSub := Formalism.MainNotions.N.galois_condition_six_of D i r hF.Conclusion2.2.1 hHG hr
  refine ⟨?_, ?_⟩
  · intro x _ hxZ u hu
    by_contra hu0
    refine hxZ (hSub x ⟨u, hu0, fun g => ?_⟩)
    have h := hu g
    rw [rTwO, GlobalTheory.UnrNoChi.mapM_twistM', Matrix.smul_mulVec] at h
    conv_rhs => rw [← h]
    rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      one_smul]
  · intro v hvl hvS hvQ x _ γ hγ
    have hχ := GlobalTheory.UnrNoChi.chi_one_eq_one i r π ρ hρ (hUnr π v hvl hvS hvQ γ hγ)
    have hx : rO D.nd i r x γ = 1 := by simp [rO, hUnr x v hvl hvS hvQ γ hγ]
    rw [rTwO, twistM]
    simp [hx, hχ]
end
end
