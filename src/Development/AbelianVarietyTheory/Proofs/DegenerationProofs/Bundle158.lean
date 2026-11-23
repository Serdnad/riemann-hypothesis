module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle153
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle152
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull

theorem exists_pre_below : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  intro hL K₀ K _ _ i D P₀ Φ gp ⟨w₀, hw₀⟩ c₀ cadd hc
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨cub⟩ := (hL.cube _ P₀ ⟨P₀.L, rig, P₀.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P₀
  choose psi hpsi using fun χ : D.X => DVR.exists_gen_of_local (V := FractionRing K₀) P₀.L P₀.isLB (K := PUnit)
    (fun _ => ptK (c₀ χ)) (fun _ => -1)
  let D₀ : DegPre K₀ :=
    { P := P₀, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨w, hw, hr⟩ := TripleMap.exists_rigidified P₀.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P₀.A)
    (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap i) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen
  have hx : ∀ χ, D.xK χ ≫ Φ = genMap i.injective ≫ ptK (c₀ χ) := fun χ => by
    show (jK K ≫ (D.c χ).left) ≫ Φ = genMap i.injective ≫ jK K₀ ≫ (c₀ χ).left
    rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  choose ψ hψ vψ using fun χ : D.X => exists_down_om ((isGen_iff w).2 hw) P₀.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => D.xK χ) (genMap i.injective) (fun _ => hx χ) (psi χ) (hpsi χ)
  obtain ⟨hD, e, -, -⟩ := exists_isPullDeg_of_val i D₀ (TauTwist.withPsi D ψ hψ) gp w hw hr (AddEquiv.refl _) hc
    (fun x z J J' hJ hJ' => by
      have v := vψ x _ (𝟙 _) z J J' hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at v
      exact v)
  exact ⟨D₀, ψ, hψ, hD, rfl, heq_of_eq e⟩

end GlobalTheory.FieldPull
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G')
  (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G)

def LevelIso : Prop :=
  ∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧
    (U'.gt e).pG.left ≫ prA hD = (j e).hom.left ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ prA hD =
        (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧
      PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x)
        ((U.gt e).t (hD.xe x)) (j e).hom.left

def AgreeAll (k : ℕ) (σ : H0 U.LG.L k) (σ' : H0 U'.LG.L k) : Prop :=
  ∀ e : ℕ, Agree U U' hD e k (j e).hom.left σ σ'

def Enough : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ') ∧
    ∀ σ₀ : H0 U'.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ'.f i = resTop _ (scal G'.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ'

def GenericRel (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R)))
      (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))) : Prop :=
  w.IsGen ∧ ∀ k : ℕ, 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), AgreeAll U U' hD j k σ σ' →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL →
      (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' →
      gs (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL))
          (σ.f (fun _ => jL)) =
        (Geo.Tor.gw w r z jL (fun _ => jL') ^ k).val *
          gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL'))
            (σ'.f (fun _ => jL'))

open ThickIso TorusCoordPull in
theorem exists_levelIso (hG : GlobalFnsSt) : ∃ j, LevelIso U U' hD j := by
  choose j hm hj using fun e : ℕ => exists_iso hD (U.gt e) (U'.gt e) hG
  refine ⟨j, fun e => ?_⟩
  have h₀ := hj e _ (𝟙 _)
  have hp : (U'.gt e).pG.left ≫ abMap hD = (j e).hom.left ≫ (U.gt e).pG.left := by
    simpa only [Category.id_comp] using h₀.1
  have hO := Oφ_pull hD (U.gt e).pG (U'.gt e).pG (j e).hom.left hp
  refine ⟨hm e, (hj (e + 1) _ (thickMap R I e G')).unique_right ?_, hp, fun x => ⟨hO x,
    pmaps_of_good ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB (hO x) ((U'.gt e).t_gen x)
      ((U.gt e).t_gen _) fun y J J' hJ hJ' => h₀.2 x y J J' hJ hJ'⟩⟩
  simpa only [Category.id_comp] using h₀.succ (U.gt_q e) (U.gt_t e) (U'.gt_q e) (U'.gt_t e)

variable {U U' hD j}

theorem LevelIso.agreeAll (hj : LevelIso U U' hD j) {k : ℕ} {σ : H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D'.toPre.SecB k α} (hE : ∀ e, U.ExpandsAt e k σ f)
    (hE' : ∀ e, U'.ExpandsAt e k σ' f')
    (hf : ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
      (f (hD.xe x))) : AgreeAll U U' hD j k σ σ' := fun e =>
  agree_of_expandsAt _ _ hD e k _ (hj e).2.2.1 (fun x => ((hj e).2.2.2 x).1) (fun x => ((hj e).2.2.2 x).2)
    (hE e) (hE' e) hf

theorem LevelIso.enough (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) (hU : ∀ k, 1 ≤ k → U.ExpBij k)
    (hU' : ∀ k, 1 ≤ k → U'.ExpBij k) : Enough U U' hD j := by
  intro k hk
  constructor
  · intro σ₀
    obtain ⟨s, hs⟩ := exists_restrict U k σ₀
    obtain ⟨F, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).1 s
    obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
    obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).2 F'
    exact ⟨r' * r, _, _, mul_ne_zero hr' hr, scale_of_restrict _ hs h₁ r', hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩
  · intro σ₀
    obtain ⟨s', hs⟩ := exists_restrict U' k σ₀
    obtain ⟨F', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).1 s'
    obtain ⟨F, hF⟩ := exists_push hD _ hG k F'
    obtain ⟨s, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).2 F
    exact ⟨r * r', _, _, mul_ne_zero hr hr', scale_of_restrict _ hs h₁' r, hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩


open LinearUnifIso in
theorem LevelIso.act_comm (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O]
    [Module O D.toPre.X] [Module O D'.toPre.X] {o : D.OAct O} {o' : D'.OAct O} {oA : A.OAct O} {oA' : A'.OAct O}
    {oG : RingAct G O} {oG' : RingAct G' O} (lin : U.OLinear O o oA oG) (lin' : U'.OLinear O o' oA' oG')
    (hx : ∀ (x : O) y, hD.xe (x • y) = x • hD.xe y)
    (hB : ∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x))
    (a : O) (e : ℕ) : (Over.pullback (thick R I e)).map (oG'.act a) ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map (oG.act a) := by
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : o'.onB.act a ≫ ψ = ψ ≫ o.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ, Category.assoc, ← P, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, hB])
  obtain ⟨hm, -, hp, ht⟩ := hj e
  have hq : (j e).hom ≫ (U.gt e).q = (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
      Category.assoc, Category.assoc, P, eψ]
    exact hp.symm.trans (Category.assoc _ _ _)
  obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
    (fun x => (ht x).2)
  obtain ⟨t, tc, ti⟩ := lin.i_lin e a
  obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
  have := oG.hom a
  have := oG'.hom a
  have hts : t' ≫ s = s ≫ t := by
    refine PowTorus.torus_ext _ _ fun χ z => ?_
    obtain ⟨x, rfl⟩ := hD.xe.surjective χ
    rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
      ← gm_torusEnd tc', Category.id_comp]
  refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
      ← Functor.map_comp, ← Functor.map_comp, hψa]
  · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]

end GlobalTheory.GenericIso
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ZH

theorem thmU_of_allSet : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.UU.AllSet (fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.gen = s.gen) → ThmUSt := by
  intro hL hext hall V _ _ _ _ hV A G _ _ hG hE hS gen hgen
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_uniformisationData_of_semiAbelianSymmetry hL hext V hV A G hG hE hS gen hgen
  obtain ⟨D, U, hU⟩ := hall V A G s
  exact ⟨D, U, hU.trans hs⟩
end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.polarized_abelian_pullback_line_bundle : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  first | exact @GlobalTheory.Ex.Trait.act_comm_of_torsion | exact GlobalTheory.Ex.Trait.act_comm_of_torsion | (intros; apply GlobalTheory.Ex.Trait.act_comm_of_torsion <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

open SpreadAb (grpObj_of_dominant isPullback_square)

theorem exists_grpObj : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) (f : X ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ X), IsPullback φ A.hom f (spMap (algebraMap R K)) → Smooth f → IsProper f → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (ψ : R' →+* K), Function.Injective ψ → ψ.comp g = algebraMap R K → ∀ (G' : Over (Sp R')) (π : G'.left ⟶ X) (φ' : A.left ⟶ G'.left), IsPullback π G'.hom f (spMap g) → φ' ≫ π = φ → φ' ≫ G'.hom = A.hom ≫ spMap ψ → ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback A G' (spMap ψ) φ' := by
  intro R K _ _ _ _ _ _ X f A _ _ φ h _ _
  obtain ⟨a₁, ha₁, H₁⟩ := exists_hom (pullback.fst f f ≫ f) f (isPullback_square h) ((μ[A]).left ≫ φ) (by
    rw [(isPullback_square h).w, Category.assoc, h.w, Over.w_assoc]
    rfl)
  obtain ⟨a₂, ha₂, H₂⟩ := exists_hom f f h ((ι[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc])
  obtain ⟨a₃, ha₃, H₃⟩ := exists_hom (𝟙 _) f (IsPullback.id_vert (spMap (algebraMap R K)))
    ((η[A]).left ≫ φ) (by rw [Category.assoc, h.w, Over.w_assoc]; simp)
  refine ⟨a₁ * a₂ * a₃, mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃,
    fun R' _ g hg ψ hψ hψg G π φ' hG hφ₁ hφ₂ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hg
  obtain ⟨⟨u₁, u₂⟩, u₃⟩ := hg
  have hc : spMap ψ ≫ spMap g = spMap (algebraMap R K) := by
    rw [← hψg, ← Spec.map_comp]; rfl
  have hφ : IsPullback φ' A.hom G.hom (spMap ψ) := IsPullback.of_right (by rwa [hφ₁, hc]) hφ₂ hG
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom ψ) hψ
  have : Flat G.hom := MorphismProperty.of_isPullback (P := @Flat) hG inferInstance
  have : IsSeparated G.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hG inferInstance
  obtain ⟨m, hm₁, hm₂⟩ := H₁ R' g u₁ _ _ _ (isPullback_square hG).w
  obtain ⟨i, hi₁, hi₂⟩ := H₂ R' g u₂ _ _ _ hG.w
  obtain ⟨e, he₁, he₂⟩ := H₃ R' g u₃ _ (spMap g) (𝟙 _) (by simp)
  have L : ∀ (Y : Over (Sp R')) (u : Y.left ⟶ X), u ≫ f = Y.hom ≫ spMap g → ∃ v : Y ⟶ G, v.left ≫ π = u :=
    fun Y u w => ⟨Over.homMk (hG.lift u Y.hom w) (hG.lift_snd _ _ _), hG.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (G ⊗ G) m (hm₁.trans (isPullback_square hG).w)
  obtain ⟨i', hi'⟩ := L G i (hi₁.trans hG.w)
  obtain ⟨e', he'⟩ := L (𝟙_ _) e (he₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  exact grpObj_of_dominant (spMap ψ) G A φ' hφ m' i' e'
    (fun φ₂ ⟨k₁, k₂⟩ => by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hm']
        refine hm₂ φ₂ (pullback.hom_ext ?_ ?_)
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₁).trans (Category.assoc _ _ _))
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← hφ₁]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans (Category.assoc _ _ _))
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc, ← Over.w (fst G G), reassoc_of% k₁, hφ₂,
          Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, hi']
        exact hi₂ φ' hφ₁
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc])
    (by
      apply hG.hom_ext
      · rw [Category.assoc, Category.assoc, hφ₁, he']
        exact he₂ _ hc
      · rw [Category.assoc, Category.assoc, Over.w, hφ₂, Over.w_assoc]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.GenSpread
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.valuation_over_finite_dvr_extension : ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧ (∃ i' : FractionRing W →+* FractionRing W', (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧ ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 → ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧ ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K, ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  first | exact @GlobalTheory.FiniteDVRValuation.main | exact GlobalTheory.FiniteDVRValuation.main | (intros; apply GlobalTheory.FiniteDVRValuation.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.exists_linearUniformisation_baseChange_admissible : Laws → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ g : R →+* R', Function.Injective g → I.map g ≤ I' → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (ψ : P'.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left), IsGrpPullback P'.D.toPre.P.A P.D.toPre.P.A (spMap g) ψ := by
  first | exact @GlobalTheory.Ex.Trait.exists_pelUnif_baseChange | exact GlobalTheory.Ex.Trait.exists_pelUnif_baseChange | (intros; apply GlobalTheory.Ex.Trait.exists_pelUnif_baseChange <;> assumption)
end
