module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedUnramifiedCoverOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}

theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem r_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  have : (homOfLE h).op = 𝟙 _ := rfl
  simp only [resG, this, CategoryTheory.Functor.map_id]; rfl

theorem r_appLE (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V) (a : Γ(X, U)) :
    resG Y h ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← f.appLE_map e (homOfLE h).op]; rfl

theorem appLE_r (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(X, U')) :
    (f.appLE U V e).hom (resG X h a) = (f.appLE U' V (e.trans (fun _ hy => h hy))).hom a := by
  rw [← f.map_appLE e (homOfLE h).op]; rfl

theorem appLE_appLE (f : Z ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e : W ≤ (f ≫ g) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = ((f ≫ g).appLE U W e).hom a := by
  rw [← Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂]; rfl

theorem pull_le (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j PUnit.unit) :=
  LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit

theorem le_pull (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) : f ⁻¹ᵁ M.U (j PUnit.unit) ≤ (M.pull f).U j :=
  fun _ h => Set.mem_iInter.2 fun _ => h

theorem pull_g (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (e : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    ((M.pull f).g j j').val = (f.appLE _ _ e).hom (M.g (j PUnit.unit) (j' PUnit.unit)).val := by
  show ((∏ _k : PUnit, (res e (pullU f _ (M.g (j PUnit.unit) (j' PUnit.unit)))) ^ (1 : ℤ) :
    Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem pull_inf_le (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι) :
    (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :=
  fun _ h => ⟨pull_le M f j h.1, pull_le M f j' h.2⟩

def secPull (M : LB X) (f : Y ⟶ X) (s : M.Sec) : (M.pull f).Sec where
  f j := (f.appLE _ _ (pull_le M f j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h := congrArg (f.appLE _ _ (pull_inf_le M f j j')).hom (s.compat (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul] at h
    erw [← pull_g M f j j'] at h
    erw [appLE_r, appLE_r] at h
    erw [r_appLE, r_appLE]
    exact h

theorem isGen_val {L : LB X} (t : L.Gen) : t.IsGen ↔ ∀ i j, resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i).val =
    (L.g i j).val * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j).val :=
  forall₂_congr fun _ _ => Units.ext_iff

theorem le₁ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J : PUnit → PUnit → M.ι) :
    ((M.pull π).pull x).U J ≤ (M.pull (x ≫ π)).U (J PUnit.unit) :=
  fun _ h => le_pull M (x ≫ π) _ (pull_le M π _ (pull_le (M.pull π) x J h))

theorem le₂ (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (j : PUnit → M.ι) :
    (M.pull (x ≫ π)).U j ≤ ((M.pull π).pull x).U (fun _ => j) :=
  fun _ h => le_pull (M.pull π) x (fun _ => j) (le_pull M π _ (pull_le M (x ≫ π) j h))

theorem pullpull_g (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J J' : PUnit → PUnit → M.ι)
    (e : ((M.pull π).pull x).U J ⊓ ((M.pull π).pull x).U J' ≤
      (x ≫ π) ⁻¹ᵁ (M.U (J PUnit.unit PUnit.unit) ⊓ M.U (J' PUnit.unit PUnit.unit))) :
    (((M.pull π).pull x).g J J').val =
      ((x ≫ π).appLE _ _ e).hom (M.g (J PUnit.unit PUnit.unit) (J' PUnit.unit PUnit.unit)).val := by
  rw [pull_g (M.pull π) x J J' (pull_inf_le _ _ _ _), pull_g M π _ _ (pull_inf_le _ _ _ _)]
  exact appLE_appLE x π _ _ e _

theorem secCoord_pull {σ : Type} (M : LB X) (th : σ → M.Sec) (π : Y ⟶ X) {T : Type} [CommRing T] (x : Sp T ⟶ Y)
    (v : σ → T) : SecCoord (M.pull π) (fun i => secPull M π (th i)) x v ↔ SecCoord M th (x ≫ π) v := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun j => res (le₂ M π x j) (τ.s fun _ => j)⟩, (isGen_val _).2 fun j j' => ?_, fun i j e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₂ M π x j) (le₂ M π x j')))
        ((isGen_val τ).1 hτ (fun _ => j) (fun _ => j'))
      rw [map_mul] at h0
      erw [pullpull_g M π x (fun _ => j) (fun _ => j') ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _)),
        rr, r_appLE] at h0
      erw [pull_g M (x ≫ π) j j' (pull_inf_le _ _ _ _)]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₂ M π x j') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₂ M π x j)) (h i (fun _ => j) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ _ e _).symm.trans h0
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun J => res (le₁ M π x J) (τ.s (J PUnit.unit))⟩, (isGen_val _).2 fun J J' => ?_, fun i J e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₁ M π x J) (le₁ M π x J')))
        ((isGen_val τ).1 hτ (J PUnit.unit) (J' PUnit.unit))
      rw [map_mul] at h0
      erw [pull_g M (x ≫ π) (J PUnit.unit) (J' PUnit.unit) (pull_inf_le _ _ _ _), rr, r_appLE] at h0
      erw [pullpull_g M π x J J' ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _))]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₁ M π x J') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₁ M π x J)) (h i (J PUnit.unit) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ e _ _).trans h0

theorem projRep_baseChange : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := by
  intro R R' σ _ _ φ I Z Z' s s' π M th ⟨hM, hloc, hpts⟩ hp
  refine ⟨fun i => secPull M π (th i), ⟨pull_isLB hM π, fun T _ β x v hx hv => ?_, fun T _ β v hu hF => ?_⟩,
    fun T _ x v => secCoord_pull M th π x v⟩
  · have hs : (x ≫ π) ≫ s = spMap (β.comp φ) := by
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    obtain ⟨h1, h2⟩ := hloc T (β.comp φ) (x ≫ π) v hs ((secCoord_pull M th π x v).1 hv)
    refine ⟨h1, fun F hF => ?_⟩
    have : I.map (MvPolynomial.map φ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      rw [Ideal.map_le_iff_le_comap]
      intro G hG
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact h2 G hG
    exact this hF
  · obtain ⟨y, ⟨hy, hv⟩, huniq⟩ := hpts T (β.comp φ) v hu fun G hG => by
      rw [← MvPolynomial.eval₂_map]
      exact hF _ (Ideal.mem_map_of_mem _ hG)
    have hw : y ≫ s = spMap β ≫ spMap φ := by rw [hy, spMap_comp]
    refine ⟨hp.lift y (spMap β) hw, ⟨hp.lift_snd _ _ _, (secCoord_pull M th π _ v).2 (by rw [hp.lift_fst]; exact hv)⟩, ?_⟩
    rintro x ⟨hx, hxv⟩
    apply hp.hom_ext
    · rw [hp.lift_fst]
      refine huniq _ ⟨?_, (secCoord_pull M th π x v).1 hxv⟩
      rw [Category.assoc, hp.w, ← Category.assoc, hx, spMap_comp]
    · rw [hp.lift_snd, hx]

end GlobalTheory.ZM.RepBC
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

open Topology Filter

theorem t2Space_ptsOver_of_isSeparated {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p] (s : Sp ℂ ⟶ S) :
    T2Space (Points.PtsOver p s) := by
  rw [t2_iff_isClosed_diagonal]
  let h := Points.PtsOver.prodHomeomorph (IsPullback.of_hasPullback p p) s
  have hd : pullback.diagonal p ≫ pullback.fst p p ≫ p = p := by simp
  have hc := (h.isClosedEmbedding.comp
    (Points.PtsOver.isClosedEmbedding_map (pullback.diagonal p) hd s)).isClosed_range
  convert hc using 1
  have key : ∀ x, h (Points.PtsOver.map (pullback.diagonal p) hd s x) = (x, x) := fun x =>
    Prod.ext (Subtype.ext (by simp [h, Points.PtsOver.prodHomeomorph, Points.PtsOver.map, Category.assoc]))
      (Subtype.ext (by simp [h, Points.PtsOver.prodHomeomorph, Points.PtsOver.map, Category.assoc]))
  ext ⟨a, b⟩
  constructor
  · intro hab
    obtain rfl : a = b := hab
    exact ⟨a, key a⟩
  · rintro ⟨x, hx⟩
    rw [Function.comp_apply, key] at hx
    rw [← hx]
    rfl

theorem exists_realLinear_lift {V W Q T : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Group Q] [TopologicalSpace T] [T2Space T] (j : Q → T)
    (hj : Function.Injective j) (e : W → Q) (e₀ : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (he₀ : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e) (Λ : Submodule ℤ W) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ) (hc : Continuous (j ∘ e)) (hc₀ : Continuous (j ∘ e₀)) :
    ∃ L : V →L[ℝ] W, ∀ z, e (L z) = e₀ z := by
  have heq : ∀ z w, e z = e w ↔ z - w ∈ Λ := fun z w => by
    rw [← hk, ← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]
  have : CompactSpace (W ⧸ Λ) := by
    refine ⟨?_⟩
    rw [← (Submodule.mkQ_surjective Λ).range_eq]
    refine IsZLattice.isCompact_range_of_periodic Λ _ Λ.isOpenQuotientMap_mkQ.continuous fun z w hw => ?_
    rw [map_add (f := _), Submodule.mkQ_apply _ w, (Submodule.Quotient.mk_eq_zero Λ).2 hw, add_zero]
  let ē : W ⧸ Λ → T := Quotient.lift (j ∘ e) fun a b hab =>
    congrArg j ((heq a b).2 ((Submodule.quotientRel_def Λ).1 hab))
  have hē : ∀ w, ē (Λ.mkQ w) = j (e w) := fun _ => rfl
  have hemb : IsClosedEmbedding ē := by
    refine (hc.quotient_lift _).isClosedEmbedding fun a b hab => ?_
    obtain ⟨a, rfl⟩ := Λ.mkQ_surjective a
    obtain ⟨b, rfl⟩ := Λ.mkQ_surjective b
    exact (Submodule.Quotient.eq Λ).2 ((heq a b).1 (hj hab))
  choose σ hσ using hs
  let φ : V →+ W ⧸ Λ := AddMonoidHom.mk' (fun z => Λ.mkQ (σ (e₀ z))) fun a b => by
    rw [← map_add (f := _)]
    exact (Submodule.Quotient.eq Λ).2 ((heq _ _).1 (by rw [he, hσ, hσ, hσ, he₀]))
  have hφ : Continuous φ := hemb.isEmbedding.continuous_iff.2 (hc₀.congr fun z => by
    show j (e₀ z) = j (e (σ (e₀ z)))
    rw [hσ])
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_lift (ex := φ) (isDiscrete_ker_mkQ Λ)
    (Λ.isOpenMap_mkQ.nhds_le 0) hφ.continuousAt
  exact ⟨L, fun z => ((heq _ _).2 ((Submodule.Quotient.eq Λ).1 (hL z))).trans (hσ _)⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

def IsExp {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)

theorem continuous_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) : Continuous a :=
  Points.continuous_of_differentiableOn fun U f => by simpa using h U f

theorem differentiableAt_of_isHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ a) (U : X.Opens) (f : Γ(X, U)) {z : V} (hz : ⊤ ≤ a z ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (a b) U f) z :=
  (h U f).2.differentiableAt ((h U f).1.mem_nhds ⟨trivial, hz⟩)

theorem IsExp.eq_of_fderiv {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e) {w w' : Fin g → ℂ}
    (h : ∀ (U : G.left.Opens) (f : Γ(G.left, U)), ⊤ ≤ (e 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e z).left U f) 0 w') : w = w' := by
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  refine (he.2.2.2.2 v hv.1).unique hv ⟨hv.1, fun U hU f => (hv.2 U hU f).trans (h U f ?_)⟩
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := hv.1
  rw [← h1]
  exact Points.le_preimage_comp _ _ hU (Points.le_preimage_top _)

theorem map_zero_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 := by
  have := he 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem eq_iff_sub_of_add {V Q : Type*} [AddGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  rw [← mul_left_inj (e w) (b := e (z - w)), ← he, sub_add_cancel, _root_.one_mul]

theorem IsExp.exists_linearEquiv [IsSeparated G.hom] {g g₀ : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : IsExp e)
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ G)} (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t2Space_ptsOver_of_isSeparated G.hom y
  obtain ⟨L, hL⟩ := exists_realLinear_lift (T := Points.PtsOver G.hom y) (fun x : Over.mk y ⟶ G => ⟨x.left, Over.w x⟩)
    (fun a b hab => Over.OverMorphism.ext (congrArg Subtype.val hab)) e e₀ he.1 ha he.2.1 Λ hk
    ((continuous_of_isHolTo he.2.2.1).subtype_mk _) ((continuous_of_isHolTo hh).subtype_mk _)
  have hsm : ∀ (c : ℂ) z, L (c • z) = c • L z := fun c z => he.eq_of_fderiv fun U f hU => by
    have h0 : (e₀ 0).left = (e 0).left := by rw [map_zero_of_add ha, map_zero_of_add he.1]
    have d := (differentiableAt_of_isHolTo he.2.2.1 U f hU).hasFDerivAt.restrictScalars ℝ
    have d₀ := (differentiableAt_of_isHolTo hh U f (z := 0) (by simpa only [h0] using hU)).hasFDerivAt.restrictScalars ℝ
    rw [← L.map_zero] at d
    have d₁ := d.comp 0 L.hasFDerivAt
    rw [L.map_zero] at d₁
    have e₁ : (fun b => valAt' (e b).left U f) ∘ L = fun b => valAt' (e₀ b).left U f := by
      funext b
      simp only [Function.comp_apply, hL]
    rw [e₁] at d₁
    have k := fun x => DFunLike.congr_fun (d₁.unique d₀) x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at k
    rw [k, map_smul, map_smul, k]
  have hi : Function.Injective L := realLinear_injective_of_countable_ker L.toLinearMap
    (hc.mono fun x (hx : L x = 0) => by
      show e₀ x = 1
      rw [← hL, hx, map_zero_of_add he.1])
  have hsu : Function.Surjective L := realLinear_surjective_of_mod_countable L.toLinearMap (Γ := Λ)
    (Set.countable_coe_iff.1 (inferInstanceAs (Countable Λ))) fun w => by
      obtain ⟨x, hx⟩ := hs (e w)
      exact ⟨x, (hk _).1 ((eq_iff_sub_of_add he.1 _ _).1 (hx.symm.trans (hL x).symm))⟩
  exact ⟨LinearEquiv.ofBijective ⟨⟨L, L.map_add⟩, hsm⟩ ⟨hi, hsu⟩, hL⟩

end GlobalTheory.UnifPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.FiniteClasses

open GlobalTheory.Points

theorem preconnectedSpace_pts (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : PreconnectedSpace (Pts (spMap (algebraMap ℂ A))) := by
  have hc := isConnected_basicOpen_complexPoints_of_dense
    (exists_isConnected_principalOpen noetherNormalization_primitive
      (isConnected_unramified_cover_of_irreducible isConnected_and_dense_compl_hypersurface
        exists_mvPolynomial_of_poly_bound_off_hypersurface))
    (principalOpen_dense_complexPoints noetherNormalization_primitive
      isConnected_and_dense_compl_hypersurface) A 1 one_ne_zero
  have he := isEmbedding_ptsOverEquivAlgHom (C := ℂ) A (id_eq_spMap_algebraMap ℂ)
  refine ⟨he.isInducing.isPreconnected_image.1 ?_⟩
  convert hc.isPreconnected using 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨_, rfl, by simp⟩
  · rintro ⟨φ, rfl, -⟩
    exact ⟨(ptsOverEquivAlgHom A (id_eq_spMap_algebraMap ℂ)).symm φ, trivial, by simp⟩

theorem finite_range_affine (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] {I : Type*}
    (c : Pts (spMap (algebraMap ℂ A)) → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcomp : ∀ P : Ideal A, spMap (Ideal.Quotient.mk P) ≫ spMap (algebraMap ℂ A) =
      spMap (algebraMap ℂ (A ⧸ P)) := fun P => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfin : (⋃ P ∈ minimalPrimes A,
      Set.range (c ∘ PtsOver.map (spMap (Ideal.Quotient.mk P)) (hcomp P) (𝟙 _))).Finite := by
    refine (minimalPrimes.finite_of_isNoetherianRing A).biUnion fun P hP => ?_
    have : P.IsPrime := hP.1.1
    have := preconnectedSpace_pts (A ⧸ P)
    exact Set.Subsingleton.finite (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hc.comp_continuous (PtsOver.continuous_map _ _ _)).apply_eq_of_preconnectedSpace a b)
  refine hfin.subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, rfl⟩ := (ptsEquivAlgHom A).symm.surjective x
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := RingHom.ker φ.toRingHom) bot_le
  refine Set.mem_biUnion (x := P) hP ⟨(ptsEquivAlgHom (A ⧸ P)).symm
    (Ideal.Quotient.liftₐ P φ fun a ha => hle ha), congrArg c (Subtype.ext ?_)⟩
  simp only [PtsOver.map_val, ptsOverEquivAlgHom_symm_val]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem finite_range {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [QuasiCompact p] {I : Type*}
    (c : Pts p → I) (hc : IsLocallyConstant c) : (Set.range c).Finite := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let 𝒰 := Y.affineOpenCover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (X := Y)
    (fun i => ((𝒰.f i).opensRange : Set Y)) (fun i => (𝒰.f i).opensRange.isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨𝒰.idx y, 𝒰.covers y⟩)
  have key : ∀ {R : CommRingCat.{0}} (j : Spec R ⟶ Y) [IsOpenImmersion j],
      (Set.range (c ∘ PtsOver.map j rfl (𝟙 _))).Finite := by
    intro R j _
    have hl : IsLocallyConstant (c ∘ PtsOver.map j rfl (𝟙 _)) :=
      hc.comp_continuous (PtsOver.continuous_map _ _ _)
    have hft : LocallyOfFiniteType (j ≫ p) := inferInstance
    generalize c ∘ PtsOver.map j rfl (𝟙 _) = c' at hl
    generalize j ≫ p = q at c' hl hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact finite_range_affine R c' hl
  refine (t.finite_toSet.biUnion fun i _ => key (𝒰.f i)).subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (x.1 (IsLocalRing.closedPoint ℂ))))
  have hx' : x ∈ Set.range (PtsOver.map (𝒰.f i) rfl (𝟙 _)) := by
    rw [PtsOver.range_map, range_comp_of_isOpenImmersion]
    exact (le_preimage_iff x.1 _).2 hx
  obtain ⟨z, rfl⟩ := hx'
  exact Set.mem_biUnion hi ⟨z, rfl⟩

theorem isLocallyConstant_of_hol {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) (d : ℕ)
    (hp : SmoothOfRelativeDimension d p) {I : Type*} (c : Pts p → I)
    (H : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → Pts p), IsOpen B → IsHolTo B (fun b => (y b).1) →
      ∀ b₀ ∈ B, ∀ᶠ b in 𝓝 b₀, c (y b) = c (y b₀)) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let h := overHomeomorph (C := ℂ) (Over.mk p)
  obtain ⟨W, σ, U, t, hW, h0, hσ, -, hhol, hco, hop, -⟩ := HolChart.exists_holomorphic_chart valAt'_rules
    existsUnique_point_of_ringHom exists_holomorphic_section_of_etale (Over.mk p) d hp (h.symm x)
  have hop' : IsOpen (σ '' W) := by
    refine TopologicalSpace.le_def.1 (le_generateFrom ?_) _ hop
    rintro _ ⟨V, f, O, hO, rfl⟩
    exact (isOpen_basicSet (C := ℂ) V f hO).preimage (isEmbedding_left (Over.mk p)).continuous
  have hx : h (σ 0) = x := by rw [hσ, Homeomorph.apply_symm_apply]
  have hev := H W (fun b => h (σ b)) hW hhol 0 h0
  have hxU : ⊤ ≤ x.1 ⁻¹ᵁ U := by rw [← hx]; exact (hco 0 h0).1
  have hT : Tendsto (fun (z : Pts p) (i : Fin d) => valR z.1 U (t i)) (𝓝 x) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    have h1 := ((continuousAt_valR (t i) hxU).comp continuous_subtype_val.continuousAt).tendsto
    have h2 : valR x.1 U (t i) = (0 : Fin d → ℂ) i := by rw [← hx]; exact (hco 0 h0).2 i
    rw [← h2]
    exact h1
  have hN : h '' (σ '' W) ∈ 𝓝 x := (h.isOpenMap _ hop').mem_nhds ⟨_, ⟨0, h0, rfl⟩, hx⟩
  filter_upwards [hN, hT.eventually hev] with z hz hz'
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
  have : (fun i => valR (h (σ w)).1 U (t i)) = w := funext (hco w hw).2
  rw [this, hx] at hz'
  exact hz'

theorem finite_image_of_locally_constant_on_holomorphic_families :
    (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B) → ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (I : Type 1) (cls : (Sp ℂ ⟶ X) → I), SmoothOfRelativeDimension d s → QuasiCompact s → (∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B, ∀ᶠ b in nhds b₀, cls (y b) = cls (y b₀)) → (cls '' {x | x ≫ s = spMap σ}).Finite := by
  intro _ k _ σ X s d I cls hs hq H
  let p := pullback.snd s (spMap σ)
  let q := pullback.fst s (spMap σ)
  have hp : SmoothOfRelativeDimension d p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback s (spMap σ)) hs
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hover : ∀ z : Pts p, (z.1 ≫ q) ≫ s = spMap σ := fun z => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, Category.id_comp]
  have hl : IsLocallyConstant fun z : Pts p => cls (z.1 ≫ q) := by
    refine isLocallyConstant_of_hol p d hp _ fun B y hB hy => ?_
    refine H B (fun b => (y b).1 ≫ q) hB (fun b _ => hover _) fun U f => ?_
    simp only [valAt'_eq_valR, valR_comp]
    exact hy (q ⁻¹ᵁ U) ((q.app U).hom f)
  refine (finite_range p _ hl).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx), pullback.lift_snd _ _ _⟩, ?_⟩
  exact congrArg cls (pullback.lift_fst _ _ _)

end GlobalTheory.FiniteClasses
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.smooth_genericFibre_of_independent_and_tangent_bound : ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by
  first | exact @GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le | exact GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le | (intros; apply GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le <;> assumption)
end
