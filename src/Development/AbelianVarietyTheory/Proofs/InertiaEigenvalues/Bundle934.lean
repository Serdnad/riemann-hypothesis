module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle922
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle916
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle926
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableInfMeasure
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwInputs.Move.Forms

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def fiOfEq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) : NX.FormsIso (X.R.FW a) (X.R.FW b) :=
  hab ▸
    { eK := RingEquiv.refl _
      eK_LL := fun _ => rfl
      e := LinearEquiv.refl _ _
      eG := MulEquiv.refl _
      eW := fun _ => LinearIsometryEquiv.refl _ _
      wk := fun _ => Iff.rfl
      mkK := fun _ => Iff.rfl
      rho := fun _ _ => rfl
      chi := fun _ => rfl
      j := fun _ _ => rfl }

theorem fiOfEq_eG (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (g : X.Γ) : (fiOfEq X hab).eG g = g := by
  subst hab; rfl

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
  (YS : NX.NExpRealS X.R X.cG S)

theorem fiOfEq_forms (j : Fin D.R.m) {a b : Fin D'.R.m} (ha : (j : ℕ) = a) (hb : (j : ℕ) = b) (hab : a = b) (x : (X.R.FW j).WK) :
    (fiOfEq X' hab).e ((m.forms j a ha).φ x) = (m.forms j b hb).φ x := by
  subst hab; rfl

include h in
theorem lt_m {n : ℕ} (h2 : n + 1 ≤ D'.R.m) : n < D.R.m := by
  have h3 : D.R.m = D'.R.m := by rw [h.gal.R]
  omega

abbrev dat : NX.RatDat D'.ntw :=
  NX.ratDatR X'.R X'.cG (m.kKsOf (e := e) YS (NX.idxOf D 0)) (m.kKsOf_spec h YS _)

abbrev back (i' : D'.ntw.Tw) : D.ntw.Tw := cast h.Tw_eq.symm i'

theorem back_heq (i' : D'.ntw.Tw) : HEq (back h i') i' := cast_heq _ _

def eFm (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) : 1 ≤ j → j ≤ D'.R.m →
    (D'.nexp.Fm i' j b ≃ₗ[FractionRing (D'.ntw.O i')] NX.Fm (dat h m YS) i' j b) :=
  match j with
  | 0 => fun h1 _ => absurd h1 (by decide)
  | n + 1 => fun _ h2 => m.eFOf h YS _ _ (back_heq h i') ⟨n, lt_m h h2⟩ b

def ks (j : Fin D.R.m) : KsIso ι (show S.Ks ≃+* (dat h m YS).Ks from (YS.fi j).eK.trans m.eK)
    (show S.G ≃* (dat h m YS).G from (YS.fi j).eG.trans m.γ) (S.A ((j : ℕ) + 1)) ((dat h m YS).A ((j : ℕ) + 1)) := m.ksOf h YS j

theorem eFm_cast {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (h1 h2)
    (x : D.nexp.Fm i ((j : ℕ) + 1) b) :
    eFm h m YS i' ((j : ℕ) + 1) b h1 h2 (h.fmCast hi _ b x) =
      fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) (YS.eF i _ b (Nat.le_add_left _ _) j.2 x) := by
  obtain rfl : i = back h i' := eq_of_heq (hi.trans (back_heq h i').symm)
  exact h.eFMove_fmCast hi (S' := dat h m YS) (ks h m YS j) _ x

theorem sup_move (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (x : D'.nexp.Fm i' j b) :
    x ∈ D'.nexp.Bsup i' j b ↔ eFm h m YS i' j b h1 h2 x ∈ NX.Bsup (dat h m YS) i' j b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  rw [eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2 x, fmOf_mem_Bsup, ← hsup]
  exact ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).1.symm

theorem rho_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.RhoStab (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (KsIso.rhoStab_iff (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩)).1 (YS.rho _ h1 (lt_m h h2))

theorem chi_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.ChiInLL0 (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact KsIso.chiInLL0 (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩) h.LL0 (YS.chi _ h1 (lt_m h h2))

theorem act_move (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (g : G0g D'.nd) (x : D'.nexp.Fm i' j b) :
    eFm h m YS i' j b h1 h2 (D'.nexp.actG i' j b g x) =
      NX.actG (dat h m YS) i' j b (rho_move h m YS j h1 h2) (chi_move h m YS j h1 h2) g (eFm h m YS i' j b h1 h2 x) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨g, rfl⟩ := h.grpEquiv.surjective g
  have e1 : D'.nexp.actG i' (n + 1) b (h.grpEquiv g) (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.actG _ (n + 1) b g x) :=
    eq_of_heq ((((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.1 _ _
      (h.grpEquiv_heq g).symm).symm.trans (h.fmCast_heq hi _ b _).symm)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, YS.act]
  refine fmOf_actG (S' := dat h m YS) _ _ _ _ _ _ _ _ ?_ _
  refine (dat h m YS).eG.symm_apply_eq.2 ?_
  refine Eq.symm ((m.cG_eG h _).trans (congrArg h.grpEquiv ?_))
  exact (YS.geq _ _).trans (S.eG.apply_symm_apply g)

def tie (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) : NX.NExpRealS X'.R X'.cG (dat h m YS) where
  fi j := fiOfEq X' (NX.idxOf_succ D' j)
  geq j g := congrArg (fun g => X'.cG (X'.R.eG g)) (fiOfEq_eG X' _ g)
  rho := rho_move h m YS
  chi := chi_move h m YS
  eF := eFm h m YS
  bsup i j b h1 h2 := ⟨1, one_ne_zero, fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).1 hx,
    fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).2 hx⟩
  act := act_move h m YS

theorem read_move (j : Fin D.R.m) (y : (S.A ((j : ℕ) + 1)).WK) :
    SameMap (evidence X j ((YS.fi j).e y))
      (evidence X' (h.cm j) ((fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e ((ks h m YS j).φ y).1)) := by
  have e1 := fiOfEq_forms m j (a := NX.idxOf D' ((j : ℕ) + 1)) (b := h.cm j)
    (congrArg Fin.val (NX.idxOf_succ D' (h.cm j))).symm rfl (NX.idxOf_succ D' (h.cm j)) ((KsIso.ofFormsIso (YS.fi j)).φ y)
  exact (congrArg (fun z => SameMap (evidence X j ((YS.fi j).e y)) (evidence X' (h.cm j) z)) e1).mpr
    (m.read j (h.cm j) rfl ((KsIso.ofFormsIso (YS.fi j)).φ y))

theorem rdRel_move (hsup) (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) (hs : SameSetup ρ ρ') (hρ : ρ.Good) (hρ' : ρ'.Good) (c : ℂ) :
    RdRel h (fun i j b => realRd YS X.geo.v₀ hρ i j b c) (fun i j b => realRd (tie h m YS hsup) X'.geo.v₀ hρ' i j b c) := by
  intro i i' hi j b f
  have hG := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).1
  refine Function.hfunext hG.symm fun g' g hg => heq_of_eq ?_
  change c⁻¹ * evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b
      (eFm h m YS i' ((j : ℕ) + 1) b (Nat.le_add_left _ _) (h.cm j).2 (h.fmCast hi _ b f)) g' =
    c⁻¹ * evK YS X.geo.v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) g
  have key : ∀ z : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) z) g' =
        evK YS X.geo.v₀ hρ i j b z g := fun z => by
    induction z using TensorProduct.induction_on with
    | zero =>
      exact (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_zero).trans
          ((congrFun (map_zero _) _).trans (congrFun (evK YS X.geo.v₀ hρ i j b).map_zero g).symm)
    | add x y hx hy =>
      refine (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        ((fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_add x y)).trans ?_
      refine (congrFun ((evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b).map_add _ _) g').trans ?_
      rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy]
    | tmul a y =>
      exact congrArg₂ (· * ·)
        ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).2.1 _ _ hs.e b _ _ (h.frac_heq hi a).symm).symm
        (read_move h m YS j y _ _ (m.v₀ j (h.cm j) rfl) _ _ hg.symm).symm
  exact congrArg (c⁻¹ * ·) ((congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
    (eFm_cast h m YS hi j b _ _ f)).trans (key _))

variable {YS} (H : NX.NExpRealH X.R X.cG S YS)


omit H in
include h m in
theorem hecke_sameMap (j : Fin D.R.m) {R : Finset (GA D (Wc D j))} {R' : Finset (GA D' (Wc D' (h.cm j)))}
    (hF : ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' (h.cm j)) R' F'))
    {T₁ T₂ : Mult.MMap (model X j)} {T₁' T₂' : Mult.MMap (model X' (h.cm j))} (h1 : SameMap T₁ T₁') (h2 : SameMap T₂ T₂') {c : ℂ}
    (h3 : T₁ = c • Mult.heckeOn (model X j) R T₂) : T₁' = c • Mult.heckeOn (model X' (h.cm j)) R' T₂' := by
  obtain ⟨hG, hW, -⟩ := hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl
  refine MultilinearMap.ext fun v' => funext fun g' => ?_
  obtain ⟨v, hv⟩ := exists_sameVec h.gal.R h.gal.host h.Tau h.eTau hW (m.MW j (h.cm j) rfl) v'
  obtain ⟨g, hg⟩ : ∃ g : GA D (Wc D j), HEq g g' := ⟨cast hG.symm g', cast_heq _ _⟩
  have e1 := hF (T₂ v) (T₂' v') (Function.hfunext hG fun a a' haa => heq_of_eq (h2 v v' hv a a' haa))
  have e2 : ∀ {A B : Type} {f : A → ℂ} {f' : B → ℂ} {a : A} {b : B}, A = B → HEq f f' → HEq a b → f a = f' b := by
    intro A B f f' a b h1 h2 h3
    subst h1; subst h2; subst h3; rfl
  rw [← h1 v v' hv g g' hg, h3]
  exact congrArg (c * ·) (e2 hG e1 hg)

end GlobalTheory.TwInputs.Move.Forms

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move.RatUp

variable {D : D7} (r : Rest D)

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    HEq ((baseUp r B).F.placeMap ((a))) (B.F.placeMap a) := by
  have h : (fun Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
      (IsPlaceModel (baseUp r B).F.ψ (symplO _ _) (heisO (baseUp r B).F.ψ _ _) ((by with_unfolding_all exact (a :))) (baseUp r B).F.lat 1 (baseUp r B).F.f₀
        ((by with_unfolding_all exact (Tm :))))) = IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ :=
    funext fun Tm => propext ⟨fun g => ⟨(by with_unfolding_all exact (g.1 :)), (by with_unfolding_all exact (g.2 :)), (by with_unfolding_all exact (g.3 :))⟩, fun g => ⟨(by with_unfolding_all exact (g.1 :)), (by with_unfolding_all exact (g.2 :)), (by with_unfolding_all exact (g.3 :))⟩⟩
  delta Frame.placeMap
  with_unfolding_all exact heq_of_eq (congrArg Classical.epsilon h)

open Classical in
theorem vecAt_up {S T : HSp D} (B : Base S T) : (baseUp r B).vecAt = (B.vecAt) := by
  delta ExportSeries.Base.vecAt Frame.vec
  rewrite [show (baseUp r B).F.placeMap = ((by with_unfolding_all exact (B.F.placeMap :))) from (by with_unfolding_all exact ((funext fun a => eq_of_heq (placeMap_up r B a)) :))]
  dsimp only [halfIdem, Frame.datumFn, ExportSeries.Base.locFn, baseUp, twistUp]
  rfl

private theorem series_up {S T : HSp D} (B : Base S T) :
    @series (overD D r) S T (baseUp r B).F = @series D S T B.F := by
  funext ω f g
  refine LinearMap.ext fun P => funext fun x => ?_
  delta series thetaKO
  with_unfolding_all refine congrArg (fun v : WO S T → ℂ => ω (g, x) v 0) ?_
  dsimp only [Frame.fock, pureTensorO, aPlusAll, aPlus, crea, Datum.dRho, baseUp]
  rfl

theorem theta_up {S T : HSp D} (B : Base S T) : (baseUp r B).theta = (B.theta) := by
  delta ExportSeries.Base.theta ExportSeries.Base.vecBase
  rewrite [vecAt_up r B, series_up r B]
  rfl

theorem genSet_up {S T : HSp D} (B : Base S T) (ω) (t : Twist D Circle) :
    (baseUp r B).genSet (((ω : PairRep S T))) (twistUp r t) = ((B.genSet ω t : GA (overD D r) S → PolF (overD D r) T.rank S.rank → Set (GA (overD D r) T → ℂ))) := by
  delta ExportSeries.Base.genSet ExportSeries.Base.gen ExportSeries.Base.vecFlat
  rewrite [vecAt_up r B, series_up r B]
  rfl

def univUp {A : Type} [AddCommGroup A] (t : UnivTwist D A) : UnivTwist (overD D r) A := ⟨(by with_unfolding_all exact (t.del :)), (by with_unfolding_all exact (t.kap :))⟩

theorem xiCoef_up {S T : HSp D} {A : Type} [AddCommGroup A] [Fintype A] (B : Base S T) (ω) (u : UnivTwist D A) :
    (baseUp r B).xiCoef (((ω : PairRep S T))) (univUp r u) = ((B.xiCoef ω u : (Q : Finset (Pl (overD D r).host.E)) → ((PP : Pl (overD D r).host.E) → A → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) → GA (overD D r) S → PolF (overD D r) T.rank S.rank → (↥Q → A) → GA (overD D r) T → ℂ)) := by
  delta ExportSeries.Base.xiCoef ExportSeries.Base.xi ExportSeries.Base.vecFam
  rewrite [vecAt_up r B, series_up r B]
  rfl

section Lat

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (h : CopyTw D (overD D r) ι e)
include h

theorem embLL0_up : embLL0 (overD D r) = (embLL0 D).comp e.toRingHom := RingHom.ext fun x => (h.embLL0_eq x).symm

theorem labLL0_up (τ : D.what₂.Tau) : e.toRingHom.comp (labLL0 (overD D r) ((τ))) = (labLL0 D τ) := by
  refine RingHom.ext fun x => (embLL0 D).injective ((h.embLL0_eq _).trans ?_)
  have a := DFunLike.congr_fun (embLL0_labLL0 (D := overD D r) ((by with_unfolding_all exact (τ :)))) x
  have c := DFunLike.congr_fun (embLL0_labLL0 (D := D) τ) ((by with_unfolding_all exact (x :)))
  refine Eq.trans a ?_
  exact (by with_unfolding_all exact (c.symm :))

theorem coefLat_up {S T : HSp D} (B : Base S T) (O : Subring ℂ) (g : Bridge.Gf S) :
    (baseUp r B).coefLat (embLL0 (overD D r)) (labLL0 (overD D r)) O ((g)) = (B.coefLat (embLL0 D) (labLL0 D) O g) := by
  have a := GlobalTheory.CoefLatIso.coefLatFn_ringEquiv D S.rank _ _ e (embLL0 D) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) O B.w.lam (B.latAt g)
  have c : (fun τ : D.what₂.Tau => e.toRingHom.comp (((by with_unfolding_all exact ((labLL0 (overD D r)) :)) : D.what₂.Tau → (D.host.E →+* ↥(overD D r).LL0)) τ)) =
      labLL0 D := funext fun τ => (by with_unfolding_all exact ((labLL0_up h τ) :))
  rw [← embLL0_up h, c] at a
  exact (by with_unfolding_all exact ((congrArg (fun L : Submodule O (GLR D S.rank → ℂ) => (harm T.rank B.w B.F.BS).restrictScalars O ⊓
    L.comap ((harmFn T.rank B.w B.F.BS).restrictScalars O)) a) :))

end Lat

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem se_theta : (setupUp r ρ).theta ((i)) ((j)) b = (ρ.theta i j b) := by
  funext h P
  have e : @Eq (type_of% (ρ.B i j b).theta) ((by with_unfolding_all exact ((baseUp r (ρ.B i j b)).theta :))) (ρ.B i j b).theta :=
    (by with_unfolding_all exact ((theta_up r (ρ.B i j b)) :))
  exact (by with_unfolding_all exact ((congrArg (fun t : type_of% (ρ.B i j b).theta => t (ρ.om i j b 1) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (P :)))) e) :))

theorem se_gens : (setupUp r ρ).gens ((i)) ((j)) b = (ρ.gens i j b) := by
  funext k Q ψ
  exact (by with_unfolding_all exact ((genSet_up r (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))))) :))

private theorem univOf_up (Q : Finset (Pl D.host.E)) (M : ℕ) :
    univOf (overD D r).nexp i Q M (setupUp r ρ).rc =
      univUp r (univOf D.nexp i Q M ρ.rc) := by
  dsimp only [setupUp, univOf, univUp, coord, Recip.pull, Recip.sym, resOf, IsResAt]
  rfl

theorem se_xi : (setupUp r ρ).xi ((i)) ((j)) b (overD D r).nexp = (ρ.xi i j b D.nexp) := by
  funext Q M
  let Q₀ := admissibleConjugatePairPlaces (overD D r).ntw i Q M
  let u := univOf D.nexp i Q₀ M ρ.rc
  let ω := ρ.om i j b 1
  let Φ := ExportSeries.Base.univFam u (ρ.β j)
  have atFam := congrArg
    (fun F : type_of% ((ρ.B i j b).xiCoef ω u) => F (half (ρ.ch i) Q₀) Φ)
    (xiCoef_up r (ρ.B i j b) ω u)
  delta Setup.xi
  rewrite [univOf_up r ρ i Q₀ M]
  dsimp only [setupUp, ω, Φ, u, Q₀, univUp, ExportSeries.Base.univFam,
    admissibleConjugatePairPlaces, Formalism.MainNotions.NAdm.AdmQ,
    Formalism.MainNotions.NAdm.TWSet] at atFam ⊢
  exact atFam

variable {r ρ i j b} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (h : CopyTw D (overD D r) ι e)
include h

theorem se_lat (O : Subring ℂ) (g : GA D (Vc D j)) : (setupUp r ρ).lat ((i)) ((j)) b O ((g)) = (ρ.lat i j b O g) :=
  (by with_unfolding_all exact ((coefLat_up h (ρ.B i j b) O (finPt _ g)) :))

theorem datum_up {s g P} (d : ρ.IsDatum i j b s g P) : (setupUp r ρ).IsDatum ((i)) ((j)) b ((s)) ((g)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), by
    have a := se_lat (ρ := ρ) (i := i) (j := j) (b := b) h (ρ.eO i b).range g
    have c := (le_of_eq a.symm) ((by with_unfolding_all exact (d.mem :)) : ((by with_unfolding_all exact (P :))) ∈ _)
    exact (by with_unfolding_all exact (c :))⟩

theorem datum_dn {s g P} (d : (setupUp r ρ).IsDatum ((i)) ((j)) b s g P) : ρ.IsDatum i j b ((s)) ((g)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), by
    have a := se_lat (ρ := ρ) (i := i) (j := j) (b := b) h (ρ.eO i b).range ((by with_unfolding_all exact (g :)))
    have c := (le_of_eq a) ((by with_unfolding_all exact (d.mem :)) : ((by with_unfolding_all exact (P :))) ∈ _)
    exact (by with_unfolding_all exact (c :))⟩


omit h in
variable (r) in
def rdUp (rd : Rd ρ D.nexp i j b) : Rd (setupUp r ρ) (overD D r).nexp ((i)) ((j)) b := (rd)

theorem rat_up {hρ : ρ.Good} {hρ' : (setupUp r ρ).Good} {rd : Rd ρ D.nexp i j b} (g : SeriesTie.Rat hρ rd) :
    SeriesTie.Rat hρ' (rdUp r rd) := by
  refine ⟨fun s x P d => ?_, fun k Q ψ h1 h2 s x P d => ?_, fun Q M h1 s x P d h2 a => ?_⟩
  · rewrite [se_theta r ρ i j b]
    exact (by with_unfolding_all exact ((g.1 _ _ _ (datum_dn h d)) :))
  · rewrite [se_gens r ρ i j b]
    exact (by with_unfolding_all exact ((g.2.1 k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) _ _ _ (datum_dn h d)) :))
  · rewrite [se_xi r ρ i j b]
    exact (by with_unfolding_all exact ((g.2.2 ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h1 :))) _ _ _ (datum_dn h d) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (a :)))) :))

theorem rat_dn {hρ : ρ.Good} {hρ' : (setupUp r ρ).Good} {rd : Rd ρ D.nexp i j b} (g : SeriesTie.Rat hρ' (rdUp r rd)) :
    SeriesTie.Rat hρ rd := by
  refine ⟨fun s x P d => ?_, fun k Q ψ h1 h2 s x P d => ?_, fun Q M h1 s x P d h2 a => ?_⟩
  · have c := g.1 _ _ _ (datum_up h d)
    rewrite [se_theta r ρ i j b] at c
    exact (by with_unfolding_all exact (c :))
  · have c := g.2.1 k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) _ _ _ (datum_up h d)
    rewrite [se_gens r ρ i j b] at c
    exact (by with_unfolding_all exact (c :))
  · have c := g.2.2 ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h1 :))) _ _ _ (datum_up h d) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (a :)))
    rewrite [se_xi r ρ i j b] at c
    exact (by with_unfolding_all exact (c :))

end Setup

theorem rat_copy_iff {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ') (hρ : ρ.Good) (hρ' : ρ'.Good) (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ')
    (hrd : RdRel h rd rd') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) :
    SeriesTie.Rat hρ (rd i j b) ↔ SeriesTie.Rat hρ' (rd' i' (h.cm j) b) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  obtain rfl := SameData.eq_up r hs
  have e0 : @Eq D.ntw.Tw ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (i' :))) := (by with_unfolding_all exact ((@eq_of_heq D.ntw.Tw i ((by with_unfolding_all exact (i' :))) ((by with_unfolding_all exact (hi :)))) :))
  have e1 : ∀ (i' : (overD D r).ntw.Tw) (hi : HEq ((by with_unfolding_all exact (i' :)) : D.ntw.Tw) i') (j' : Fin (overD D r).R.m),
      rd' i' j' b = (by with_unfolding_all exact ((rdUp r (rd ((by with_unfolding_all exact (i' :))) ((by with_unfolding_all exact (j' :))) b)) :)) := fun i' hi j' => by
    refine LinearMap.ext fun f => ?_
    have a := hrd _ i' hi ((by with_unfolding_all exact (j' :))) b ((by with_unfolding_all exact (f :)))
    have c : h.fmCast hi ((j' : ℕ) + 1) b ((by with_unfolding_all exact (f :))) = (by with_unfolding_all exact (f :)) := (by with_unfolding_all exact ((eq_of_heq (h.fmCast_heq hi ((j' : ℕ) + 1) b ((by with_unfolding_all exact (f :))))) :))
    have a' : HEq (rd' i' j' b (h.fmCast hi ((j' : ℕ) + 1) b ((by with_unfolding_all exact (f :))))) (rd ((by with_unfolding_all exact (i' :))) ((by with_unfolding_all exact (j' :))) b ((by with_unfolding_all exact (f :)))) := (by with_unfolding_all exact (a :))
    rewrite [c] at a'
    exact (by with_unfolding_all exact ((@eq_of_heq (GA (overD D r) (Wc (overD D r) j') → ℂ) (rd' i' j' b f) ((by with_unfolding_all exact ((rd ((i')) ((j')) b ((f))) : _))) ((by with_unfolding_all exact (a' :)))) :))
  subst e0
  rewrite [e1 _ hi (h.cm j)]
  exact ⟨fun g => (by with_unfolding_all exact ((rat_up h (hρ' := hρ') g) :)), fun g => rat_dn h (hρ' := hρ') ((by with_unfolding_all exact (g :)))⟩

end GlobalTheory.TwInputs.Move.RatUp

end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix

noncomputable section

namespace GlobalTheory.RSResidue

theorem rsHat_zero_props_two : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → ∀ (φ φ' : Sm E a), φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω → φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω' → ∀ (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E), Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧ (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 = GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ ∀ (z : Neutral.B1.Ideles E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 = ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  intro E _ _ _ a ω ω' hω hω' φ φ' h h' ℓ Φ hΦ J η
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hc' : ∀ g, rsHat ℓ φ.1 φ'.1 Φ J η g 0 = (∫ u, rsInf ℓ φ.1 φ'.1 Φ g u ∂infMeasure E a) * c := hc
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hc']
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc', norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ g
    have e : rsPsi ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y =>
      rsPsi_ratGL_mul ℓ h.2.1 h'.2.1 Φ J η γ g y
    simp only [rsHat, e]
  · intro z g
    have e : ∀ u, rsInf ℓ φ.1 φ'.1 Φ (GeneralLinearGroup.scalar (Fin a) z * g) u =
        ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * rsInf ℓ φ.1 φ'.1 Φ g u := fun u => by
      simp only [rsInf, mul_assoc (GeneralLinearGroup.scalar (Fin a) z) g, h.2.2.1, h'.2.2.1, map_mul]
      ring
    rw [hc', hc', funext e, integral_const_mul]
    ring

end GlobalTheory.RSResidue
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ParAsm

theorem one_le_nV (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.m_add_three_le_k
  simp only [Ranks.nV, Ranks.r] at *
  omega

end GlobalTheory.ParAsm
end
