module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle401
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle025
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle422
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle423
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle424
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.prvG6_of_admissible' : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @_root_.GlobalTheory.ClosingSixth.conclusionG6_of_adm_alt | exact _root_.GlobalTheory.ClosingSixth.conclusionG6_of_adm_alt | (intros; apply _root_.GlobalTheory.ClosingSixth.conclusionG6_of_adm_alt <;> assumption)
end
end

section



section
noncomputable section
namespace GlobalTheory.NPin
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

structure CharacterChoiceData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) where
  cf : CharFrame D
  C : NChoice D
  tp : TupTied D cf C
  chr : NCharTied D cf C tp
  val : ValLL0 D cf
  Q_eq : ∀ i, D.nd.Q i = C.Q (D.nd.w i)
  T : WDTie D.nd D.naut
  lab : LabTrue D T
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T
  M : MtFam D
  H : _root_.GlobalTheory.HeightCounting.HeckeOpenStatements D M tp.tup
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T H.au
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  rep_inj : ∀ σ σ', (rep σ).Iso (rep σ') → σ = σ'
  row : ∀ i, _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (D.naut.locW i σ w)) (D.naut.satW i)
  locW_eq : ∀ i i' σ w, D.naut.locW i σ w = D.naut.locW i' σ w
  jE : D.host.E →+* Qb
  ty : TypesOpen D jE
  wd : WDSide D T
  wdOf : ∀ (i : D.nd.Loc) a (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) w,
    D.naut.wdOf i r w = wd.wdOf (D.nd.l i) (D.naut.iotaQC i) r w ∧
    (D.naut.IsCrysW i r w ↔ wd.IsCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsPotCrysW i r w ↔ wd.IsPotCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsdRW i r w ↔ wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    ∀ τ, D.naut.jumpsW i r τ = wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ
def weilDeligneOfLocalIrrep (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls π.toIrrRep)
structure IsFaithfulReading {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T) : Prop where
  rc : ∀ i w hw, (S i w hw).rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w
  row : ∀ i (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w) σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ →
    IsLocS (P.rep σ).S s ((S i s.w hw).row σ).toIrrRep
  rep : ∀ i (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w) Q,
    IsLocS (n := D.R.nV) (P.H.av.S i Q) s ((S i s.w hw).rep Q).toIrrRep
  mu : ∀ i w hw (j : Fin D.R.m), j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) w (S i w hw).mu
  eta : ∀ i w hw, IsComp P.cf.eta w (S i w hw).eta
structure CharacterChoiceJoin {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) : Type 1 where
  form : ∀ i, MtForm D P.M i
  rowM : ∀ i : D.nd.Loc, RowMod D P.rep (D.nd.j i)
  th : ∀ (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i →
    ThetaMod D P.M i (rowM i) (P.tp.tup (D.nd.mu i) j) P.cf.eta
end GlobalTheory.NPin
end
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem _root_.GlobalTheory.T.admT_of_artin_reciprocity_and_local_conditions : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  first | exact @_root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | exact _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly | (intros; apply _root_.GlobalTheory.admT_of_adm5_eigSpan_tieInePoly <;> assumption)
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

abbrev _root_.GlobalTheory.T.LocalBesselMultiplicityOne' : Prop :=  Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.LabTrue D T → _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → GlobalTheory.SerSys.LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.LabPin.TypeLab D rep
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.MtIndep
section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end rep
section loc
variable {D : D7}
def phiSubmodule {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D)
    (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  ⨆ (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W)) (h : NG.IsIrrRep (M μ j h1 h2).wt.ρ S')
    (_ : Good X Y σ' c j (A.au.cls j h1 h2 { (M μ j h1 h2).wt with S := S', irrS := h })),
    (NG.isoTyp (M μ j h1 h2).wt.ρ S').comap (M μ j h1 h2).real
theorem phi_submodule_heq {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE)
    (M : MtFam D) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (h1' : 1 ≤ j') (h2' : j' ≤ D.R.m) (hμ : μ = μ') (hj : j = j') :
    HEq (_root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' c μ j h1 h2) (_root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' c μ' j' h1' h2') := by
  subst hμ hj; rfl
end loc
end GlobalTheory.HeightCounting.MtIndep
namespace GlobalTheory.HeightCounting.MtIndep
section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}
theorem supr_type_v_eq_phi_submodule (hS : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq Y Cb) (σ' : D.ntypes.Par) (i : X.nd.Loc) :
    (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) =
    _root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' (Y.muC i) (X.nd.mu i) (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 := by
  have hc : ∀ P, (∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)) ↔
      Good X Y σ' (Y.muC i) (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
        { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P }) := by
    intro P
    have hl : Y.naut.locV i P = fun w => D.nbc.locAU (X.nd.j i) (Cb.embAV i P) w := funext (Cb.embAV_loc i P)
    have hs : Y.naut.satV i P = D.nbc.satAU (X.nd.j i) (Cb.embAV i P) := funext (Cb.embAV_sat i P)
    have hf : Y.naut.infWt i = D.nbc.infW (X.nd.j i) (D.nbc.wtAU (X.nd.j i) (Cb.embAV i P)) := Cb.embAV_inf i P
    rw [← hS.emb i P]
    unfold Good
    refine exists_congr fun Sig => and_congr_right fun _ => ?_
    unfold IsBCV BCd
    rw [hl, hs, hf]
    exact Iff.rfl
  apply le_antisymm
  · refine iSup₂_le fun P hP => ?_
    rw [hS.typeV i P]
    exact le_iSup_of_le (hS.S i P) (le_iSup_of_le (hS.irr i P) (le_iSup_of_le ((hc P).1 hP) le_rfl))
  · refine iSup_le fun S' => iSup_le fun hirr => iSup_le fun hg => ?_
    by_cases hb : (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real = ⊥
    · exact hb.le.trans bot_le
    · obtain ⟨P, hP⟩ := hS.surj i S' hirr hb
      have ht : Y.naut.typeV i P = (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real := by
        rw [hS.typeV i P, isoTyp_eq (hS.irr i P).1 hP]
      have hcl : A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P } =
          A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := S', irrS := hirr } :=
        (A.au.iso _ _ _ _ _).2 ⟨⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩, hP⟩
      have hP' : P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)} :=
        (hc P).2 (hcl ▸ hg)
      exact le_iSup₂_of_le (f := fun P _ => Y.naut.typeV i P) P hP' ht.ge
end loc2
theorem typeV_iSup_indep_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i i' : X.nd.Loc) (σ' : D.ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big X T Sp Y Cb hS i i' σ' hmu hj
  rw [_root_.GlobalTheory.HeightCounting.MtIndep.supr_type_v_eq_phi_submodule hS σ' i, _root_.GlobalTheory.HeightCounting.MtIndep.supr_type_v_eq_phi_submodule hS σ' i']
  have hc : Y.muC i = Y.muC i' := by
    obtain ⟨h1, h2⟩ := X.nd.j_range i
    have e := hS.muC i ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    have e' := hS.muC i' ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    rw [hmu] at e
    exact A.chr.e1.injective (Subtype.ext (e.trans e'.symm))
  rw [hc]
  exact _root_.GlobalTheory.HeightCounting.MtIndep.phi_submodule_heq X Y A M σ' _ _ _ _ _ hmu hj
end GlobalTheory.HeightCounting.MtIndep
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.HeckeLat
end GlobalTheory.HeightCounting.HeckeLat
open GlobalTheory.HeightCounting.HeckeLat in
theorem GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P ⟨h1, h2, hk1, hk2, hsp, hP⟩ x hx
  obtain ⟨Φ, hc, hf, hw, hint, W0, hW0, hW0c, hrel⟩ := descend_integral D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  have hPb : P ∉ In.Sb := fun h => hP (by
    rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
    exact Or.inr (Finset.mem_coe.mpr (hSb h)))
  have hMW : ∀ y ∈ (S.A j).MK, y ∈ WKr D S j := fun y hy => by
    rw [WKr_of D S h1 h2]; exact hy.1
  have hML : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), Φ y ∈ BsupT D T S i j b := by
    have key : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), ∀ a : 𝓞 D.what₂.LL,
        Φ (a • y) ∈ BsupT D T S i j b := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro a
        obtain ⟨o, ho⟩ := hint a ⟨y, hMW y hy⟩
        rw [← algebraMap_smul D.what₂.LL a y]
        refine ho ▸ Submodule.smul_mem _ o ?_
        exact Submodule.subset_span ⟨⟨y, hMW y hy⟩, hy, hw _⟩
      | zero => intro a; rw [smul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => intro a; rw [smul_add, map_add (f := _)]; exact add_mem (hy a) (hz a)
      | smul a' y _ hy => intro a; rw [smul_smul]; exact hy _
    intro y hy
    simpa using key y hy 1
  have hhr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    rw [dite_eq_left ⟨h1, h2⟩]
    rfl
  have hkΦ : ∀ y, hkT D T S In i j b k P (Φ y) = ((cHkT D T i b P : T.O i) ^ k) • Φ (In.hL j k P y) := by
    intro y
    rw [← algebraMap_smul (FractionRing (T.O i)), map_pow, hf _ _ hhr]
    rfl
  obtain ⟨n, hn⟩ := In.hL_int j k P h1 h2 hsp hPb hk2
  obtain ⟨u, hu⟩ := (normV_isUnit D T i P hP).pow n
  have hstep : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), y ∈ goodL D S In.θ j →
      hkT D T S In i j b k P (Φ y) ∈ BI D T S In i j b := by
    intro y hy hg
    rw [hkΦ]
    refine Submodule.smul_mem _ _ ⟨?_, ?_⟩
    · have h3 := hML _ (hn y hy hg)
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (T.O i), Nat.cast_pow, ← hu] at h3
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : T.O i) h3
      rwa [smul_smul, Units.inv_mul, one_smul] at h4
    · exact descend_mem_V0T D T S In i j b Φ hc ha he _ (hL_goodL D S In j k P h1 h2 ⟨hk1, hk2, hsp, hPb⟩ y hg)
  have hET : ∀ a y, Φ (eqL D S In.θ j a y) = eqT D T S In i j b a (Φ y) := by
    intro a y
    cases a with
    | none => simp only [eqL, eqT, LinearMap.sub_apply, Module.End.one_apply, map_sub, he]
    | some u =>
      simp only [eqL, eqT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, ha, hc,
        LinearEquiv.coe_coe]
  have hx0 : ∀ a, eqT D T S In i j b a x = 0 := by
    intro a
    have h3 := goodTwistSideForms_le_span_goodLiftForms D S In T i j b h1 h2 (eIdem_all D) Φ hc ha he hw hx.2
    refine (Submodule.span_le (p := LinearMap.ker (eqT D T S In i j b a))).mpr ?_ h3
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hET, (mem_goodL_iff D S In.θ j y).mp hy a, map_zero]
  obtain ⟨m, o, g, rfl⟩ := Submodule.mem_span_set'.mp hx.1
  choose w hwM hwg using fun t => (g t).2
  have hg : ∀ t, (g t : FmT D T S i j b) = Φ (w t) := fun t => (hwg t).trans (hw _).symm
  simp only [hg] at hx0 ⊢
  haveI : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hsol := hrel (fun t a => eqL D S In.θ j a (w t)) (fun t a => eqL_rational D S In j h1 h2 W0 hW0 hW0c a (w t)) o (by
    intro a

    rw [← hx0 a, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hET, LinearMap.map_smul_of_tower])
  clear hx0 hx
  induction hsol using Submodule.span_induction with
  | mem o ho =>
    obtain ⟨c, hc0, hco⟩ := ho
    have h3 : ∑ t, o t • Φ (w t) = Φ (∑ t, ((c t : ↥D.LL0) : D.what₂.LL) • (w t : S.WL j)) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hc, ← hco, algebraMap_smul]
    rw [h3]
    refine hstep _ (Submodule.sum_mem _ fun t _ => ?_) ((mem_goodL_iff D S In.θ j _).mpr fun a => ?_)
    · let a : 𝓞 D.what₂.LL := ⟨((c t : ↥D.LL0) : D.what₂.LL),
        (RingOfIntegers.isIntegral_coe (c t)).map (algebraMap ↥D.LL0 D.what₂.LL).toIntAlgHom⟩
      have h4 := Submodule.smul_mem _ a (Submodule.subset_span (R := 𝓞 D.what₂.LL) (s := ((S.A j).MK : Set (S.WL j))) (hwM t))
      rwa [← algebraMap_smul D.what₂.LL a] at h4
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simpa only [map_smul] using hc0 a
  | zero => simp
  | add o o' _ _ ho ho' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
    exact add_mem ho ho'
  | smul r o _ ho =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ ho
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain
namespace GlobalTheory.TypeRec.Model
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG
section Compl
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [hp : Fact p.Prime]
end Compl
open Classical in
theorem exists_isRc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) :
    ∃ rc, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc := by
  refine ⟨fun k v n π => if h : ∃ σ, Nonempty (π ≅ pull I k v σ) then
    (T.e _).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls h.choose))
    else D.naut.lpZero _, fun k v n σ π h => ?_⟩
  have h' : ∃ σ, Nonempty (π ≅ pull I k v σ) := ⟨σ, h⟩
  beta_reduce
  rw [dite_eq_left h', Equiv.apply_symm_apply, cls_eq_of_iso I k v _ σ ⟨h'.choose_spec.some.symm ≪≫ h.some⟩]
theorem locR_eq_rc_of_isRc_and_true_reading {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D} {rc}
    (h : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) {rep cp} (hc : IsComp I rep cp) {loc : D.what₂.FT → ∀ w, D.naut.LP w} {sat}
    (hr : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (loc σ w)) sat) (σ k v) :
    loc σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  obtain ⟨s, hs, τ, h1, h2⟩ := hc σ k v
  apply (T.e _).injective
  rw [h2, h k v _ τ _ ⟨CategoryTheory.Iso.refl _⟩]
  have key : ∀ (w) (hs : s.w = w) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
      GlobalTheory.HeightCounting.IsLocS (rep σ).S s (hs ▸ τ) → T.e w (loc σ w) =
        _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) := by
    rintro _ rfl τ h1
    exact hr.1 σ s τ h1
  exact key _ hs τ h1
end GlobalTheory.TypeRec.Model
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
theorem tupEtaInv_unrAt_splitOut_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∀ w, SplitOut X.nd i w → (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j _hj w hw
  obtain ⟨_hsplit, hl, hS, hQ⟩ := hw
  have hS' : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
      w ∈ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde))) := fun h =>
    hS ((X.nd.S_def i w).2 ⟨h, hl⟩)
  have hmu0 : (cf.mu0 j).UnrAt w := (cf.isMu0 j).unr w (fun k hk => by
    fin_cases k
    · exact hS' (Or.inl hk)
    · exact hS' (Or.inr (Or.inl hk)))
  have hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQeq : X.nd.Q i = C.Q (X.nd.w i) := (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
  have hpsi : (tp.psi (X.nd.w i)).UnrAt w :=
    ((tp.psi_is (X.nd.w i) (X.nd.w_tw i)).ram w).2 (by rw [← hQeq]; exact hQ)
  have hdel : (cf.delAt (D.what₂.places.resChar (X.nd.w i))).UnrAt w := by
    rw [X.nd.w_l i]
    unfold CharFrame.delAt
    split_ifs with h
    · exact cf.isDel'.unr w (fun hp => hS' (Or.inr (Or.inr (by rw [if_pos h]; exact hp))))
    · exact cf.isDel.unr w (fun hp => hS' (Or.inr (Or.inr (by rw [if_neg h]; exact hp))))
  have hxi : (tp.xi (X.nd.mu i)).UnrAt w := by
    rw [X.nd.mu_w i, tp.xi_tw]
    exact HChar.UnrAt.mul hdel hpsi
  exact HChar.UnrAt.mul (HChar.UnrAt.mul hmu0 hxi) (HChar.UnrAt.inv (cf.isEta.unr w))
end GlobalTheory.HeightCounting
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting


theorem locBr_of_autSpec_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq Y Cb → ∃ Br : LocBr Y, Br.nbr = Sp.nbr := by
  intro D cf jE A M C tup big X T Sp Y Cb hA
  refine ⟨⟨Sp.nbr, Sp.nbr_ind, Sp.self_good, ?_⟩, rfl⟩
  intro i w hw
  have hφ : ∀ x : X.nd.O i, iotaOQ X.nd Y.naut i x =
      (((Sp.nbr i w hw).toLL x : ↥(Sp.nbr i w hw).LL.1) : Loc.Om (X.nd.l i)) := by
    intro x
    show Y.naut.iotaQ i (algebraMap _ _ x) = _
    rw [hA.iotaQ i]
    exact Sp.nbr_iq i w hw x
  have hL := A.wd.loc (X.nd.l i) (Y.naut.iotaQC i) w hw (X.nd.O i) (Sp.nbr i w hw) (Sp.nbr_ind i w hw)
    (iotaOQ X.nd Y.naut i) hφ
  refine ⟨hφ, ?_, ?_⟩
  · intro m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.1 m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (iotaOQ X.nd Y.naut i) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (iotaOQ X.nd Y.naut i) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
  · intro LL' hLL m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.2 LL' hLL m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
end GlobalTheory.HeightCounting
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain
namespace GlobalTheory.CoefDuty
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}
def BuiltAlt (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)
def AutomorphicSideExists (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ big, ∃ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L
def ForcedByAutomorphicSemisimpleData (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (P : D7 → Prop) : Prop :=
  ∃ big, ∀ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → P (withLoc L)
end GlobalTheory.CoefDuty
end
end
end
