module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEqIffExpansionEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LinearUnifIso

theorem exists_hom_of_pullback_id {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {f : S ⟶ S}
    (hf : f = 𝟙 S) (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ φ : G' ⟶ G, IsMonHom φ ∧ φ.left = bc.hom.left ≫ pullback.fst G.hom f := by
  have h₁ : IsGrpPullback G' G (𝟙 S) (bc.hom.left ≫ pullback.fst G.hom f) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G f)).congr ((Category.id_comp _).trans hf) rfl
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  obtain ⟨e, he, h⟩ := grpPullback_iso h₁ (isGrpPullback_of_iso (Iso.refl G))
  exact ⟨e.hom, he, (Category.comp_id _).symm.trans h⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I D' e G')

theorem mono_torus : Mono g.i := by
  refine ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩

theorem hom_ext_torus (hG : GlobalFnsSt) (f₁ f₂ : thickObj R I e G' ⟶ thickObj R I e G) [IsMonHom f₁] [IsMonHom f₂]
    (hq : f₁ ≫ g.q = f₂ ≫ g.q) (hi : g'.i ≫ f₁ = g'.i ≫ f₂) : f₁ = f₂ := by
  obtain ⟨τ, hτ⟩ := TorusCoord.exists_torus g f₁ f₂ hq
  have := mono_torus g
  have := g.i_hom
  have := g'.q_flat
  have := g'.q_surj
  have := g'.q_affine
  have hc : ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (a : Z ⟶ thickObj R I e G'),
      a ≫ f₁ = (a ≫ τ ≫ g.i) * (a ≫ f₂) := fun Z a => by
    rw [← MonObj.comp_mul, ← hτ]
  have h1 : τ = 1 := by
    refine (splitTorusPointsEquiv _ D.X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
    rw [map_one]
    refine (splitTorusPointsEquiv_val _ D.X _ τ χ.toAdd).trans ?_
    refine eq_one_of_fibre_const_of_section hG _ _ _ (TLinPf.isAb_pullback _ _ D'.P.isAb) g'.q _
      η[thickObj R I e G'] (fun Z a b hab => ?_) ?_
    · obtain ⟨σ, hσ⟩ := TorusCoord.exists_torus g' a b hab
      have e₁ : a ≫ τ = b ≫ τ := by
        rw [← cancel_mono g.i, Category.assoc, Category.assoc]
        have ha := hc Z a
        have hb := hc Z b
        have k₁ : a ≫ f₁ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₁) := by
          rw [hσ, MonObj.mul_comp, Category.assoc, hi]
        have k₂ : a ≫ f₂ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₂) := by
          rw [hσ, MonObj.mul_comp, Category.assoc]
        rw [k₁, k₂, hb, mul_left_comm] at ha
        rw [mul_left_comm] at ha
        rw [mul_left_comm (a ≫ τ ≫ g.i)] at ha
        exact (mul_right_cancel (mul_left_cancel ha)).symm
      rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, ← Over.comp_left,
        ← Over.comp_left, e₁]
    · have e₁ : η[thickObj R I e G'] ≫ τ = 1 := by
        rw [← cancel_mono g.i, MonObj.one_comp, Category.assoc]
        have ha := hc _ η[thickObj R I e G']
        rw [IsMonHom.one_hom f₁, IsMonHom.one_hom f₂] at ha
        exact (mul_eq_right.1 ha.symm)
      rw [← FunDescent.comp_appTop_apply, ← Over.comp_left, e₁]
      refine (splitTorusPointsEquiv_val _ D.X _ 1 χ.toAdd).symm.trans ?_
      rw [map_one]
      rfl
  rw [hτ, h1, MonObj.one_comp, _root_.one_mul]

theorem exists_torus_map (h : thickObj R I e G' ⟶ thickObj R I e G)
    (b : thickObj R I e D'.P.A ⟶ thickObj R I e D.P.A) [IsMonHom b] (hq : h ≫ g.q = g'.q ≫ b)
    {F : D'.P.A.left ⟶ D.P.A.left} (w : LB.Iso D'.P.L (D.P.L.pull F)) (xe : D'.X → D.X)
    (hψ : ∀ x κ, D'.Oφ g'.pG x κ ≫ F = h.left ≫ D.Oφ g.pG (xe x) κ)
    (H : ∀ x, PMaps w (D'.Oφ g'.pG x) (D.Oφ g.pG (xe x)) Oinvε (g'.t x) (g.t (xe x)) h.left) :
    ∃ s : splitTorus _ D'.X ⟶ splitTorus _ D.X, s ≫ g.i = g'.i ≫ h ∧
      ∀ x z, gm s.left z ⊤ (charUnit _ D.X (xe x)) = gm (𝟙 _) z ⊤ (charUnit _ D'.X x) := by
  have hd : (g'.i ≫ h) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g'.isKernel.w, Category.assoc, IsMonHom.one_hom]
  have hs := g.isKernel.lift_fst _ _ hd
  refine ⟨_, hs, fun x z => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have v₁ := PowTorus.val_on_torus g (xe x) hJ (g.isKernel.lift _ _ hd)
  have v₂ := PowTorus.val_on_torus g' x hJ' (𝟙 _)
  rw [hs] at v₁
  rw [Category.id_comp] at v₂
  have v₃ : val (g.t (xe x)) (g'.i.left ≫ h.left) z J =
      (∏ k, gw w (g'.i.left ≫ D'.Oφ g'.pG x k) z (J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
        (J' (g'.i.left ≫ D'.Oφ g'.pG x k)) ^ Oinvε k) * val (g'.t x) g'.i.left z J' :=
    (val_of _ (g'.i.left ≫ h.left) z J (fun k => J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F)) (fun k => by
      rw [Category.assoc, Category.assoc, hψ])).trans
    (H x _ g'.i.left z _ _ (fun k => hJ ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
      (fun k => hJ' (g'.i.left ≫ D'.Oφ g'.pG x k)))
  rw [PowTorus.prod_on_torus g' x (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at v₃
  exact v₁.symm.trans (v₃.trans v₂)

theorem gm_torusEnd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {u : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X u t) {Z : Scheme.{0}}
    (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X) :
    gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (u χ)) := by
  rw [← ht χ]
  exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm

theorem gm_comp_of_id {X Y Z : Scheme.{0}} (s : Y ⟶ X) (a : Γ(X, ⊤)ˣ) (a' : Γ(Y, ⊤)ˣ)
    (h : ∀ y, gm s y ⊤ a = gm (𝟙 Y) y ⊤ a') (r : Z ⟶ Y) (z : Z) : gm (r ≫ s) z ⊤ a = gm r z ⊤ a' := by
  have e : pullU s ⊤ a = a' := unit_ext fun y _ =>
    (gm_pull (𝟙 Y) s y ⊤ trivial a).trans (by rw [Category.id_comp]; exact h y)
  rw [← e]
  exact (gm_pull r s z ⊤ trivial a).symm

end LinearUnifIso


open LinearUnifIso in
theorem act_comm_of_isPullUnif_id : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ I _ hI D D' A A' G G' _ _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PrimGen

open GlobalTheory.FieldBaseChange

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_lower (v : AddValuation F (WithTop ℚ)) {n : ℕ} (c : Fin n → F) :
    ∃ r : ℚ, ∀ i, (r : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (v (c i)).untopD 0).bddBelow
  refine ⟨m, fun i => ?_⟩
  have h := hm ⟨i, rfl⟩
  cases e : v (c i) with
  | top => exact le_top
  | coe y =>
    simp only [e, WithTop.untopD_coe] at h
    exact WithTop.coe_le_coe.2 h

theorem exists_vge (U : UnifPre (maximalIdeal V) D A G) (v : AddValuation F (WithTop ℚ)) {k : ℕ}
    {σ : U.SecGF F k} {s : Fam D.toPre F k} (h : U.ExpandsG F k σ s) (α : D.toPre.X) :
    ∃ r : ℚ, VGe D F v k α (s.s α) r := by
  obtain ⟨n, c, x, -, -, hs⟩ := (expandsG_iff U F k σ s).1 h
  obtain ⟨r, hr⟩ := exists_lower v c
  refine ⟨r, n, c, fun i => (x i).2 α,
    fun i => termPull D.toPre (FractionRing V) F k α (genericTerm D k α ((x i).2 α)), fun i => ?_, hr, fun j => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ =>
      ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval ((x i).2 α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing V) F))))))).symm
  · exact (congrArg (chartLin (famBase D.toPre F) _ j) (hs α)).trans (map_sum (chartLin (famBase D.toPre F) _ j) _ _)

theorem exists_prim_span (hU : UUStatement) {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ}
    (hQ : QForm.IsQ D.toPre ϖ Q) [IsAlgClosed F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) :
    ∃ ϑ : Fam D.toPre F 1, Prim D Q v ϑ ∧
      ∀ s : Fam D.toPre F 1, (∃ r : ℚ, VGe D F v 1 0 (s.s 0) r) → ∃ c : F, s = c • ϑ := by
  classical
  obtain ⟨b, hli, hb, hsp⟩ := hU V ϖ hϖ D Q hQ F v hv (Or.inl inferInstance) 1 le_rfl
  have : Subsingleton (Fin (1 ^ (D.toPre.rank + D.toPre.P.g))) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ (D.toPre.rank + D.toPre.P.g)) := ⟨0, by rw [one_pow]; exact one_pos⟩
  have hsp' : ∀ s, NuGe D Q F v 1 s 0 → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ s = c • b i₀ := fun s hs => by
    obtain ⟨c, hc, e⟩ := (hsp s).1 hs
    exact ⟨c i₀, hc i₀, e.trans (Fintype.sum_subsingleton _ i₀)⟩
  refine ⟨b i₀, ⟨hb i₀, fun r hr h => ?_⟩, ?_⟩
  · obtain ⟨ζ, s', hζ, hs', e⟩ := (n1c V ϖ hϖ D Q hQ F v hv 1 le_rfl (b i₀) (hb i₀)).1 ⟨r, hr, h⟩
    obtain ⟨c, hc, rfl⟩ := hsp' s' hs'
    rw [isSmul_iff, smul_smul] at e
    have e1 : ζ * c = 1 := smul_left_injective F (hli.ne_zero i₀) (e.symm.trans (one_smul F _).symm)
    have h0 : (0 : WithTop ℚ) < v (ζ * c) := by
      rw [AddValuation.map_mul]
      exact lt_add_of_lt_of_nonneg hζ hc
    rw [e1, AddValuation.map_one] at h0
    exact lt_irrefl _ h0
  · rintro s ⟨r, hr⟩
    have h1 : NuGe D Q F v 1 s (-(|r| + 1)) := by
      rw [n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) s]
      intro α hα
      obtain rfl := Finset.mem_singleton.1 hα
      refine hr.mono ?_
      rw [QForm.Q_zero hϖ D hQ]
      have := neg_abs_le r
      simp only [Int.cast_zero, zero_div, add_zero]
      linarith
    obtain ⟨ζ, hζ0, hζ⟩ := exists_val_eq hv (r := |r| + 1) (by positivity)
    have h2 := NuGe.smul Q hζ.ge ((isSmul_iff ζ s _).2 rfl) h1
    rw [neg_add_cancel] at h2
    obtain ⟨c, -, e⟩ := hsp' _ h2
    exact ⟨ζ⁻¹ * c, by rw [mul_smul, ← e, inv_smul_smul₀ hζ0]⟩

end GlobalTheory.UT.PrimGen

namespace GlobalTheory.UT

open GlobalTheory.FieldBaseChange

theorem exists_prim_generator : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ : W0 U.toUnifPre, w₀.IsGen → ∃ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ IsGenSec A.A A.L 1 th := by
  intro hL _ _ _ hU V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U w₀ hw
  obtain ⟨ϑ, hp, hsp⟩ := PrimGen.exists_prim_span hU hϖ hQ hv
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 1) le_rfl w₀ hw
  refine ⟨e.symm ϑ, ϑ, (he _ _).2 (e.apply_symm_apply ϑ), hp, fun t => ?_⟩
  obtain ⟨σ, -, hσ⟩ := (he t _).2 rfl
  obtain ⟨c, hc⟩ := hsp _ (PrimGen.exists_vge U.toUnifPre v hσ 0)
  have ht : t = (c • e.symm ϑ : SecOver (abelianBase A F) _) :=
    e.injective (hc.trans (by rw [map_smul, e.apply_symm_apply]))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c, fun j => ?_⟩
  rw [ht]
  rfl

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionQk

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_cubAtT {T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {y : T'.left} {J} (hJ : Good D.P.L y J)
    (χ : D.X) (x w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T (DegPre.cT D T χ) x w) ρ.left y J = th D y J (cP D _ χ) (ρ ≫ x) (ρ ≫ w) := by
  have := val_cub D.cub ρ hJ (cP D T χ) x w
  rwa [comp_cP] at this

theorem exists_pull (ρ : TF (R := R) F ⟶ T) (g : GtPt D T) :
    ∃ g' : GtPtF D F, g'.b = ρ ≫ g.b ∧
      ∀ χ y J, Good D.P.L y J → val (g'.s χ) (𝟙 _) y J = val (g.s χ) ρ.left y J := by
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (g.s χ) ρ.left) (𝟙 _) y J = val (g.s χ) ρ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g', hb, hv⟩ := exists_gt (D := D) (F := F) (ρ ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) ρ.left)
    (fun χ => pullGen_isGen _ _ _ _ (g.isGen χ) _) (fun χ U _ h => by
      refine Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i) ?_
      fin_cases i
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left)
          ((MonObj.comp_mul ρ (cP D T χ) g.b).trans (congrArg (· * (ρ ≫ g.b)) (comp_cP D ρ χ)))
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (comp_cP D ρ χ)
      · rfl
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult χ χ') ρ.left).trans (val_mul hJ _ _ _))
      refine Eq.trans (congrArg₂ (· * ·) rfl ?_) e
      refine Eq.trans ?_ (val_cubAtT ρ hJ χ (cP D T χ') g.b).symm
      rw [comp_cP])
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩

theorem isIota_zero (hB : D.TauBimult) {h : GtPtF D F} (hh : h.IsZero) : GtPtF.IsIota 0 h := by
  obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
  refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

theorem exists_qk (hB : D.TauBimult) (ρ : TF (R := R) F ⟶ T) (k : ℕ) (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (hk : (gs k).IsZero) :
    ∃ p : QkPt D F k, p.y = 0 ∧ GtPt.IsPullF F ρ.left g p.g := by
  choose pl hb hv using fun g : GtPt D T => exists_pull ρ g
  have zero : ∀ g : GtPt D T, g.IsZero → (pl g).IsZero := fun g hg =>
    (isZero_iff _).2 ⟨by rw [hb, hg.1]; exact MonObj.comp_one (M := D.P.A) ρ, fun χ y J hJ =>
      (hv g χ y J hJ).trans ((val_corr hJ (hg.2 χ) _).trans (val_one _))⟩
  have add : ∀ g g' g'' : GtPt D T, g.IsAdd g' g'' → (pl g).IsAdd (pl g') (pl g'') := fun g g' g'' h =>
    (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, h.1]; exact MonObj.comp_mul ρ g.b g'.b, fun χ y J hJ => by
      rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) ρ.left).trans (val_mul hJ _ _ _))
      exact Eq.trans (congrArg₂ (· * ·) rfl (val_cubAtT ρ hJ χ g.b g'.b).symm) e⟩
  refine ⟨⟨0, pl g, pl (gs k), ⟨fun i => pl (gs i), zero _ h₀, fun i => add _ _ _ (hs i), rfl⟩,
    isIota_zero hB (zero _ hk)⟩, rfl, congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (hb g),
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (hv g χ y J hJ).trans ?_
  rw [val_pull hJ, Category.id_comp]

theorem base_pow (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (i : ℕ) : (gs i).b = g.b ^ i := by
  induction i with
  | zero => rw [pow_zero]; exact h₀.1
  | succ i ih => rw [pow_succ, ← ih]; exact (hs i).1

theorem torsionPoint_qk : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.b ^ k = 1 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ p : QkPt D.toPre F k, p.y = 0 ∧ GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g := by
  intro hG R _ _ _ I hI hne D A G _ _ U k x gp hx hm
  obtain ⟨hadd, hzero⟩ := GlobalTheory.gtCoord_additive hG R I hI hne D A G U
  choose gs hgs using fun i : ℕ => (GlobalTheory.T.existsUnique_torusExtensionPoint_of_groupPoint R I hI hne D A G U (x ^ i)).exists
  have h₀ : (gs 0).IsZero := hzero _ (by simpa only [pow_zero] using hgs 0)
  have hk : (gs k).IsZero := hzero _ (by simpa only [hx] using hgs k)
  have hs : ∀ i, GtPt.IsAdd (gs i) gp (gs (i + 1)) := fun i =>
    hadd (x ^ i) x _ _ _ (hgs i) hm (by simpa only [pow_succ] using hgs (i + 1))
  exact ⟨(base_pow gp gs h₀ hs k).symm.trans hk.1,
    fun F _ _ => exists_qk D.tau_bimult (toUnit _) k gp gs h₀ hs hk⟩

end GlobalTheory.TorsionQk
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_eq_iff_expansion_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (s s' : U.SecK k) (F F' : Fam D.toPre (FractionRing R) k), U.Expands k s F → U.Expands k s' F' → (s = s' ↔ F = F') := by
  first | exact @GlobalTheory.eq_iff_expansion_eq | exact GlobalTheory.eq_iff_expansion_eq | (intros; apply GlobalTheory.eq_iff_expansion_eq <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_oAct_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] (ιD : D.OAct O), ∃ (_ : Module O D'.X) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) := by
  intro hG R R' _ _ _ _ φ D D' hD O _ _ _ ιD
  have gp := pull_grp hD
  obtain ⟨o', ho'⟩ := polOActPull _ _ _ D.P D'.P _ gp (LBIso.symm ⟨hD.w, hD.w_gen⟩) O ιD.onB
  letI inst : Module O D'.X := hD.xe.module O
  have hs : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y := fun a y =>
    hD.xe.apply_symm_apply _
  have he : ∀ a, o'.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a) := fun a => by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have := ho' a
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at this ⊢
      exact this
    · exact (Over.w (o'.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))).symm
  refine ⟨inst, ⟨o', fun a y => ?_, fun a => ?_⟩, hs, he⟩
  · refine Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hs, ιD.c_lin, Over.comp_left, Over.comp_left, Category.assoc, ho', ← Category.assoc,
      ← Category.assoc (D'.c y).left, hD.c_pr]
  · exact tauBal_of_isPullDeg hG R R' φ D D' hD _ _ _ _ (ιD.onB.hom a) (ιD.onB.hom (star a)) (ιD.onB.rosati a)
      (he a) (he (star a)) _ _ _ _ (hs a) (hs (star a)) (ιD.c_lin a) (ιD.c_lin (star a)) (ιD.tau_bal a)

end GlobalTheory
end
end
