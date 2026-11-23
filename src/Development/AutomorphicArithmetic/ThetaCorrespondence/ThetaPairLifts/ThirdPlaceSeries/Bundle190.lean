module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle083
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle153
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle187
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle118
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle143
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle148
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle115
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle392
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle161
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle166
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle188
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle086
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct


open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twLe_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistUpperBound₂ := by
  intro _ _ _ hA hX
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA hX) fun Fm x hx i p hr hm w hw j ⟨a, c⟩ ρ hρ ν rd hf hc => ?_
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have h0 := baseOf_of_pin (cG := p.cG) p.charW.base.lev hρ hf.pin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  obtain ⟨c1, c2⟩ := c ρ hρ hf.adapted
  obtain ⟨-, e, h1, h2⟩ := hf.adapted
  exact _root_.GlobalTheory.BigOn.Exp.TupLe.realTw_le_alt _root_.GlobalTheory.T.seesaw_places_statement _root_.GlobalTheory.T.tuple_flat_estimate _root_.GlobalTheory.T.tupLe_traceSt _root_.GlobalTheory.T.tuple_coef_le _root_.GlobalTheory.T.small_tuple_statement_alt hr hm hL hw a.1 hρ hf.pin hf.level
    { h0 with } e h1 h2 c1 c2 hf.norm hf.rat hc
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_tuple_free_moves_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g ∈ _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj, GlobalTheory.FinPl.Moves _ g (a.g.x j).L (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) := by
  first | exact @_root_.GlobalTheory.PenLev.tuple_free_level_moves_alt | exact _root_.GlobalTheory.PenLev.tuple_free_level_moves_alt | (intros; apply _root_.GlobalTheory.PenLev.tuple_free_level_moves_alt <;> assumption)
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
noncomputable section
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem mem_rJ_of_red_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (z : GA D (D.sp.Y 0)) (hz : z ∈ GfC (D.sp.Y 0))
    (hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0))
    (hR : ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg,
      Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1) :
    z ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  refine ⟨hz, ?_⟩
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS ?_
  rintro PP (hP | hP)
  · exact hR PP hP
  · exact absurd hP (Finset.notMem_empty _)
theorem reduced_character_conj_eq_of_mem_level_group (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (hκ : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    _root_.GlobalTheory.MiTop.realCharacter W (k * κ * k⁻¹) = _root_.GlobalTheory.MiTop.realCharacter W κ := by
  have h1 : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hk.2
  have h2 : Formalism.IndefR.Lev.finE (Yc D 0) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hκ.2
  have e := levFn_conj D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) h1 h2
  unfold _root_.GlobalTheory.MiTop.realCharacter Formalism.IndefR.Lev.levChi
  erw [map_mul, map_mul, map_inv, e]
theorem mem_rJ_iff_conj_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ k * κ * k⁻¹ ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  have := (Subgroup.mul_mem_cancel_right (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := k * κ) (Subgroup.inv_mem _ hk)).trans
    (Subgroup.mul_mem_cancel_left (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := κ) hk)
  exact this.symm
theorem matches_mul_of_mem_rJ (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {z t k : GA D (D.sp.Y 0)} (hzf : z ∈ GfC (D.sp.Y 0))
    (hzc : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (ht : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t) :
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * t * k) := by
  have hkf : k ∈ GfC (D.sp.Y 0) := hk.1
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hzf ht.1) hkf, fun κ => ?_⟩
  have hz := Subgroup.mem_center_iff.mp hzc
  have hc : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹ := by
    have e : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = z * (t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹) * z⁻¹ := by group
    rw [e, ← hz, mul_inv_cancel_right]
  obtain ⟨h1, h2⟩ := ht.2 (k * κ * k⁻¹)
  rw [hc]
  refine ⟨(_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).trans h1, fun hκ => ?_⟩
  rw [h2 ((_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).1 hκ), _root_.GlobalTheory.MiTop.reduced_character_conj_eq_of_mem_level_group W hk hκ]
theorem matching_coset_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → GlobalTheory.MiTop.Framed B → GlobalTheory.MiTop.Framed B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∃ a₁, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a₁ ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a₁ = _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' hF hF' a₀ a a₀' a' hA hA'
  obtain ⟨z, hzf, hzc, c, hcf, hcc, k, hk, he⟩ :=
    _root_.GlobalTheory.T.matching_translates_bottom_alt W hW.bot hr u B (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) hA.2.2.2.1 (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a') hA'.2.2.2.1 hA.2.2.2 hA'.2.2.2
  have hcc' := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hcc)
  have hX : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o c⁻¹ *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * _root_.GlobalTheory.MiTop.translationElement f B a₀ a := by
    unfold _root_.GlobalTheory.MiTop.translationElement
    rw [show a₀ * (a * c⁻¹) = c⁻¹ * (a₀ * a) by rw [← hcc' (a₀ * a), mul_assoc], map_mul]
    have key : ∀ {G : Type} [Group G] (x e y b : G), x⁻¹ * (e * y) * b = x⁻¹ * e * x * (x⁻¹ * y * b) := by
      intros; group
    exact key (G := GA D (D.sp.Y 0)) _ _ _ _
  have e1 : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
    rw [hX, he, map_inv]
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  have hA₁ : _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ (a * c⁻¹) := by
    refine ⟨hA.1, Subgroup.mul_mem _ hA.2.1 (Subgroup.inv_mem _ hcf),
      Subgroup.mul_mem _ hA.2.2.1 (Subgroup.inv_mem _ hcc), ?_⟩
    rw [e1]
    exact _root_.GlobalTheory.MiTop.matches_mul_of_mem_rJ W hzf hzc hk hA'.2.2.2
  have hz : z ∈ _root_.GlobalTheory.MiTop.rJ_z W := _root_.GlobalTheory.MiTop.mem_rJ_of_red_alt W z hzf
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
  refine ⟨a * c⁻¹, hA₁, z * k, Subgroup.mul_mem _ hz hk, ?_⟩
  rw [e1, ← (Subgroup.mem_center_iff.mp hzc (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')), mul_assoc]
end GlobalTheory.MiTop
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.unramified_places_declared' : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, EmbeddingTypes.hypDecl i (X.dc i) ep ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) := by
  first | exact @_root_.GlobalTheory.NLink.splitPrime_hyps_alt | exact _root_.GlobalTheory.NLink.splitPrime_hyps_alt | (intros; apply _root_.GlobalTheory.NLink.splitPrime_hyps_alt <;> assumption)
end
end
