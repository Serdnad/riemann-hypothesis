module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle678
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtalePull

theorem range_pt {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : Sp Ω ⟶ X) (t : Sp Ω) : Set.range p = {p t} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    have : s = t := Subsingleton.elim (α := PrimeSpectrum Ω) s t
    simp [this]
  · rintro rfl
    exact ⟨t, rfl⟩

theorem range_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) : Set.range (f ≫ g) = g '' Set.range f := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun t => Scheme.Hom.comp_apply f g t)

theorem exists_isIso_restrict {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [Etale f] [UniversallyClosed f]
    [UniversallyClosed q] (x : U)
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  have hΔ : IsOpenImmersion (pullback.diagonal f) := inferInstance
  let r : pullback f f ⟶ U := pullback.fst f f ≫ f ≫ q
  have h1 : IsClosed (r '' (Set.range (pullback.diagonal f))ᶜ) :=
    r.isClosedMap _ (pullback.diagonal f).isOpenEmbedding.isOpen_range.isClosed_compl
  have h2 : IsClosed (q '' (Set.range f)ᶜ) :=
    q.isClosedMap _ f.isOpenMap.isOpen_range.isClosed_compl
  let W : U.Opens := ⟨(r '' (Set.range (pullback.diagonal f))ᶜ)ᶜ ∩ (q '' (Set.range f)ᶜ)ᶜ,
    h1.isOpen_compl.inter h2.isOpen_compl⟩
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨z, hz, hzx⟩
    apply hz
    let w := (pullback f f).fromSpecResidueField z
    have hw : w ≫ pullback.fst f f = w ≫ pullback.snd f f := by
      refine hinj ((pullback f f).residueField z) _ _ ?_ ?_
      · have : Set.range (w ≫ r) = {x} := by
          rw [range_comp', Scheme.range_fromSpecResidueField, Set.image_singleton, hzx]
        have e : (w ≫ pullback.fst f f) ≫ f ≫ q = w ≫ r := Category.assoc _ _ _
        exact (congrArg (fun k : Spec ((pullback f f).residueField z) ⟶ U => Set.range k) e).trans this
      · simp [pullback.condition]
    have hw2 : w = (w ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp
      · simp [hw]
    have : z ∈ Set.range w := by rw [Scheme.range_fromSpecResidueField]; rfl
    obtain ⟨t, ht⟩ := this
    refine ⟨(w ≫ pullback.fst f f) t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hw2, ht]
  · rintro ⟨y, hy, hyx⟩
    exact hy (hsurj y hyx)
  · have hm : Mono (f ∣_ (q ⁻¹ᵁ W)) := by
      refine ⟨fun {T} u v huv => ?_⟩
      have e : (u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f = (v ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f := by
        simp only [Category.assoc, ← morphismRestrict_ι]
        rw [← Category.assoc, huv, Category.assoc]
      let w : T ⟶ pullback f f := pullback.lift _ _ e
      have hr : Set.range w ⊆ Set.range (pullback.diagonal f) := by
        rintro _ ⟨t, rfl⟩
        by_contra hn
        have hW : q (f ((f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι (u t))) ∈ W := (u t).2
        refine hW.1 ⟨w t, hn, ?_⟩
        have e3 : w ≫ r = u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι ≫ f ≫ q := by
          simp only [w, r, pullback.lift_fst_assoc, Category.assoc]
        rw [← Scheme.Hom.comp_apply, e3]
        simp only [Scheme.Hom.comp_apply]
      have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) w hr
      have e1 := congrArg (· ≫ pullback.fst f f) hl
      have e2 := congrArg (· ≫ pullback.snd f f) hl
      simp only [w, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
        pullback.lift_fst, pullback.lift_snd] at e1 e2
      rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι, ← e1, e2]
    have ho : IsOpenImmersion (f ∣_ (q ⁻¹ᵁ W)) := IsOpenImmersion.of_flat_of_mono _
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨ho, ⟨fun y => ?_⟩⟩
    have hW : q y.1 ∈ W := y.2
    have : y.1 ∈ Set.range f := by
      by_contra hn
      exact hW.2 ⟨y.1, hn, rfl⟩
    obtain ⟨s, hs⟩ := this
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ W
      rw [hs]; exact hW
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs

theorem exists_isIso_restrict' {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [UniversallyClosed f]
    [UniversallyClosed q] (x : U) (V : U.Opens) (hx : x ∈ V) [Etale (f ∣_ (q ⁻¹ᵁ V))]
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ W ≤ V ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  obtain ⟨W, hW, hiso⟩ := exists_isIso_restrict (f ∣_ (q ⁻¹ᵁ V)) (q ∣_ V) ⟨x, hx⟩ (by
    intro Ω _ p p' h1 h2
    rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι]
    apply hinj
    · have e : (p ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι) ≫ f ≫ q = (p ≫ f ∣_ (q ⁻¹ᵁ V) ≫ q ∣_ V) ≫ V.ι := by
        simp
      rw [e, range_comp', h1]
      exact Set.image_singleton
    · simp only [Category.assoc, ← morphismRestrict_ι]
      rw [← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    have h1 : q y.1 = x := (morphismRestrict_base_coe q V y).symm.trans (congrArg Subtype.val hy)
    obtain ⟨s, hs⟩ := hsurj y.1 h1
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ V
      rw [hs, h1]; exact hx
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs)
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hW, rfl⟩, V.ι_image_le W, ?_⟩
  rw [← image_morphismRestrict_preimage]
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme)
    (morphismRestrictRestrict f (q ⁻¹ᵁ V) ((q ∣_ V) ⁻¹ᵁ W))).1 hiso

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ V : U.left.Opens, x ∈ V → Etale (V.ι ≫ τ) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ _ S X π U a b g τ c hπ _ _ _ hU ha _ hτ hc1 hc2 hc x _ _ hinj hsurj V hxV hV
  have hcomm : a ≫ U.hom = b ≫ π := by
    rw [← hτ, ← Category.assoc, ← hc1, ← hc2, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨f, hf1, hf2⟩ : ∃ f : X ⟶ pullback U.hom π, f ≫ pullback.fst _ _ = a ∧ f ≫ pullback.snd _ _ = b :=
    ⟨pullback.lift a b hcomm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  subst hf1
  have hfp : IsProper f := IsProper.of_comp f (pullback.fst U.hom π)
  let G : pullback U.hom π ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π :=
    pullback.lift (pullback.fst _ _ ≫ τ) (pullback.snd _ _) (by rw [Category.assoc, hτ, pullback.condition])
  have hG1 : G ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ := pullback.lift_fst _ _ _
  have hG2 : G ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hG : IsPullback G (pullback.fst U.hom π) (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) τ := by
    refine IsPullback.of_right ?_ hG1 (IsPullback.of_hasPullback _ π).flip
    rw [hG2, hτ]
    exact (IsPullback.of_hasPullback _ π).flip
  have hfG : f ≫ G = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hG1, hc1, Category.assoc]
    · rw [Category.assoc, hG2, hc2, hf2]
  have hG' := (isPullback_morphismRestrict (pullback.fst U.hom π) V).flip.paste_horiz hG
  have hGe : Etale ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) :=
    MorphismProperty.of_isPullback (P := @Etale) hG'.flip hV
  have hfe : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V)) := by
    have : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V) ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) := by
      rw [morphismRestrict_ι_assoc, hfG]; infer_instance
    exact Etale.of_comp _ ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G)
  obtain ⟨W, hxW, hWV, hiso⟩ := exists_isIso_restrict' f (pullback.fst U.hom π) x V hxV (by
    intro Ω _ p p' h1 h2
    refine hinj Ω p p' h1 ?_ ?_
    · rw [← Category.assoc, h2, Category.assoc]
    · rw [← hf2, ← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    let K := (pullback U.hom π).residueField y
    let w : Sp (AlgebraicClosure K) ⟶ pullback U.hom π :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ (pullback U.hom π).fromSpecResidueField y
    let t : Sp (AlgebraicClosure K) := closedPoint (AlgebraicClosure K)
    have hw : w t = y := by
      have : w t ∈ Set.range ((pullback U.hom π).fromSpecResidueField y) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    obtain ⟨p, hp1, hp2⟩ := hsurj (AlgebraicClosure K) (w ≫ pullback.fst _ _) (w ≫ pullback.snd _ _)
      (by rw [range_pt _ t, Scheme.Hom.comp_apply, hw, hy]) (by simp [pullback.condition])
    have : p ≫ f = w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hp1]
      · rw [Category.assoc, hf2, hp2]
    exact ⟨p t, by rw [← Scheme.Hom.comp_apply, this, hw]⟩)
  refine ⟨W, hxW, ?_, ?_⟩
  · rw [← U.left.homOfLE_ι hWV, Category.assoc]
    infer_instance
  · have P1 := (isPullback_morphismRestrict (pullback.fst U.hom π) W).paste_vert (IsPullback.of_hasPullback U.hom π)
    have P0 : IsPullback (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ pullback.fst U.hom π ∣_ W)
        (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ (pullback.fst U.hom π ⁻¹ᵁ W).ι ≫ pullback.snd U.hom π)
        (W.ι ≫ U.hom) π :=
      P1.of_iso (asIso (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W))).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp only [Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id])
        (by simp) (by simp)
    rw [morphismRestrict_ι_assoc, hf2, ← morphismRestrict_comp] at P0
    exact P0

end GlobalTheory.Mum.EtalePull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DivSpread

theorem dvd_of_specializes {X : Scheme.{0}} {V : Type} [CommRing V] (p : X ⟶ Spec (CommRingCat.of V)) {L : LB X}
    (hL : L.IsLB) (s : LB.Sec L) (a : V) {x y : X} (hyx : y ⤳ x)
    (h : ∀ j, x ∈ L.U j → cst p x a ∣ gs (𝟙 X) x (L.U j) (s.f j)) :
    ∀ j, y ∈ L.U j → cst p y a ∣ gs (𝟙 X) y (L.U j) (s.f j) := by
  intro i hyi
  obtain ⟨k, hxk⟩ : ∃ k, x ∈ L.U k := by
    have : x ∈ (⨆ k, L.U k) := hL.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hyk : y ∈ L.U k := hyx.mem_open (L.U k).isOpen hxk
  have sp : ∀ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
      gs (𝟙 X) y U b = (X.presheaf.stalkSpecializes hyx).hom (gs (𝟙 X) x U b) := by
    intro U hx b
    rw [gs_eq _ y U (hyx.mem_open U.isOpen hx), gs_eq _ x U hx]
    exact (congrArg (fun φ => φ.hom ((Scheme.Hom.app (𝟙 X) U).hom b))
      (X.presheaf.germ_stalkSpecializes _ hyx)).symm
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z a := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨t, ht⟩ := h k hxk
  have hk : cst p y a ∣ gs (𝟙 X) y (L.U k) (s.f k) := by
    refine ⟨(X.presheaf.stalkSpecializes hyx).hom t, ?_⟩
    rw [sp _ hxk, ht, map_mul, ← hc, ← hc, ← sp (p ⁻¹ᵁ ⊤) (show p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) from trivial)]
  have hm : y ∈ L.U i ⊓ L.U k := ⟨hyi, hyk⟩
  have e := congrArg (gs (𝟙 X) y (L.U i ⊓ L.U k)) (s.compat i k)
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm] at e
  rw [e]
  exact Dvd.dvd.mul_left hk _

theorem exists_specializes_not_dvd {X : Scheme.{0}} {U W : X.Opens} (c : Γ(X, W)) (f : Γ(X, U)) {x : X}
    (hxU : x ∈ U) (hxW : x ∈ W) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] (h : ¬ gs (𝟙 X) x W c ∣ gs (𝟙 X) x U f) :
    ∃ y, y ⤳ x ∧ Order.coheight y ≤ 1 ∧ ¬ gs (𝟙 X) y W c ∣ gs (𝟙 X) y U f := by
  by_contra H
  push Not at H
  apply h
  obtain ⟨V, hV, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U ⊓ W) (x := x) ⟨hxU, hxW⟩
  have hVU : V ≤ U := fun z hz => (hVle hz).1
  have hVW : V ≤ W := fun z hz => (hVle hz).2
  let fV : Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom f
  let cV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom c
  have hgf : ∀ z (hz : z ∈ V), gs (𝟙 X) z U f = (X.presheaf.germ V z hz).hom fV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVU hz, gs_eq _ z V hz]; rfl
  have hgc : ∀ z (hz : z ∈ V), gs (𝟙 X) z W c = (X.presheaf.germ V z hz).hom cV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVW hz, gs_eq _ z V hz]; rfl
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hlocx := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [← Ideal.mem_span_singleton]
  refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one _ _ fun Q hQ hQ1 => ?_
  let P : Ideal Γ(X, V) := Q.comap (algebraMap Γ(X, V) (X.presheaf.stalk x))
  have hPp : P.IsPrime := Ideal.comap_isPrime _ Q
  let Pt : PrimeSpectrum Γ(X, V) := ⟨P, hPp⟩
  have hyV : hV.fromSpec Pt ∈ V := by
    have : hV.fromSpec Pt ∈ Set.range hV.fromSpec := ⟨Pt, rfl⟩
    rwa [hV.range_fromSpec] at this
  let yV : V := ⟨hV.fromSpec Pt, hyV⟩
  have hPt : hV.primeIdealOf yV = Pt := hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf yV)
  have hsp : yV.1 ⤳ x := by
    have hle : Pt ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
      show P ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  let : Algebra Γ(X, V) (X.presheaf.stalk yV.1) := X.presheaf.algebra_section_stalk yV
  have hlocy := hV.isLocalization_stalk yV
  rw [hPt] at hlocy
  have hdim : Order.coheight yV.1 ≤ 1 := by
    rw [← GlobalTheory.ringKrullDim_stalk_le_one_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk yV.1)]
    have := IsLocalization.height_under (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl Q
    change (P.height : WithBot ℕ∞) ≤ 1
    rw [show P = Ideal.under Γ(X, V) Q from rfl, this]
    exact_mod_cast hQ1
  obtain ⟨t, ht⟩ := H yV.1 hsp hdim
  rw [hgf _ hyV, hgc _ hyV] at ht
  change algebraMap Γ(X, V) _ fV = algebraMap Γ(X, V) _ cV * t at ht
  obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl t
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq, ← map_mul] at ht
  obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) ht
  refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * w), ?_, ?_⟩
  · exact (P.primeCompl.mul_mem m.2 w.2 : (m : Γ(X, V)) * w ∉ P)
  · rw [Ideal.mem_span_singleton, hgf x hxV, hgc x hxV]
    change algebraMap Γ(X, V) _ cV ∣ algebraMap Γ(X, V) _ (m * w) * algebraMap Γ(X, V) _ fV
    refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * a), ?_⟩
    rw [← map_mul, ← map_mul, show (m : Γ(X, V)) * w * fV = m * (fV * w) by ring, hm,
      show (m : Γ(X, V)) * (cV * a) = cV * (m * a) by ring]

theorem eq_of_specializes_of_coheight_le_one {X S : Scheme.{0}} (p : X ⟶ S) [Flat p] {y w : X}
    (hy : Order.coheight y ≤ 1) {P' : S} (hP' : P' ⤳ p y) (hne : P' ≠ p y) (hw : w ⤳ y) (he : p w = p y) :
    w = y := by
  by_contra hne'
  have hlt : y < w := lt_of_le_not_ge (show y ≤ w from hw) (fun h => hne' (hw.antisymm h).eq)
  have hmaxw : IsMax w := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hy w hlt
  obtain ⟨z, hz, hpz⟩ := Flat.generalizingMap p (show P' ⤳ p w from he ▸ hP')
  have h1 : w ≤ z := hz
  have h2 : z = w := (hz.antisymm (hmaxw h1)).eq
  exact hne (hpz.symm.trans (h2 ▸ he))

theorem mem_of_not_isUnit_cst {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (y : X)
    (a : R) (h : ¬ IsUnit (cst p y a)) : a ∈ (p y).asIdeal := by
  by_contra ha
  apply h
  have hy : y ∈ p ⁻¹ᵁ ⊤ := show p y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial
  rw [cst, gs_eq p y ⊤ hy]
  refine (X.mem_basicOpen _ y hy).1 ?_
  rw [← Scheme.preimage_basicOpen]
  show p y ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [basicOpen_eq_of_affine]
  exact ha

theorem specializes_of_mem_fibre {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIrreducible p] {y : X}
    (hmax : ∀ w, w ⤳ y → p w = p y → w = y) {z : X} (hz : p z = p y) : y ⤳ z := by
  obtain ⟨y', hy'⟩ : y ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨z', hz'⟩ : z ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; exact hz
  have hg : ∀ t, genericPoint (p.fiber (p y)) ⤳ t := fun t => (genericPoint_spec _).specializes trivial
  have hgm : p (p.fiberι (p y) (genericPoint (p.fiber (p y)))) = p y := by
    have : p.fiberι (p y) (genericPoint (p.fiber (p y))) ∈ Set.range (p.fiberι (p y)) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have h1 : p.fiberι (p y) (genericPoint (p.fiber (p y))) = y :=
    hmax _ (by have := (hg y').map (p.fiberι (p y)).continuous; rwa [hy'] at this) hgm
  rw [← h1, ← hz']
  exact (hg z').map (p.fiberι (p y)).continuous

end GlobalTheory.DivSpread

open GlobalTheory.DivSpread in
theorem GlobalTheory.DivSpread.dvd_everywhere : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Smooth p → GeometricallyConnected p → ∀ (e : Spec (CommRingCat.of R) ⟶ X), e ≫ p = 𝟙 _ → ∀ (L : LB X), L.IsLB → ∀ (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X), p x = closedPoint R → ∀ j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t := by
  intro R _ _ _ _ _ X p hsm hgc e he L hL s q hq hcl x j hxj
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hnot
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom q)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z q := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨y, hyx, hy1, hyn⟩ := exists_specializes_not_dvd c (s.f j) hxj trivial (by rw [hc]; exact hnot)
  rw [hc] at hyn
  have hyj : y ∈ L.U j := hyx.mem_open (L.U j).isOpen hxj
  have hqP : q ∈ (p y).asIdeal := mem_of_not_isUnit_cst p y q fun hu =>
    hyn ⟨hu.unit⁻¹ * gs (𝟙 X) y (L.U j) (s.f j), by rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]⟩
  let P0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hP0 : P0 ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have hP0' : P0 ≠ p y := fun h => hq (by
    have : q ∈ P0.asIdeal := h ▸ hqP
    exact this)
  have hmax : ∀ w, w ⤳ y → p w = p y → w = y := fun w hw hpe =>
    eq_of_specializes_of_coheight_le_one p hy1 hP0 hP0' hw hpe
  have hey : p (e (p y)) = p y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have h1 : y ⤳ e (p y) := specializes_of_mem_fibre p hmax hey
  have h2 : e (p y) ⤳ e (closedPoint R) := (IsLocalRing.specializes_closedPoint (p y)).map e.continuous
  have hcm : p (e (closedPoint R)) = closedPoint R := by
    show (e ≫ p) (closedPoint R) = _
    rw [he]; rfl
  exact hyn (dvd_of_specializes p hL s q (h1.trans h2) (fun k hk => hcl _ hcm k hk) j hyj)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GlueCopies

theorem desc_of_compat (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i :=
  ⟨Multicoequalizer.desc D.toGlueData.diagram S p (by rintro ⟨i, j⟩; exact h i j),
    fun i => Multicoequalizer.π_desc _ _ _ _ _⟩

theorem exists_glue_copies : ∀ (Y : Scheme.{0}) (J : Type) (V : J → J → Y.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ Y), (∀ i, V i i = ⊤) → (∀ i, τ i i = (V i i).ι) → (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) → (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) → ∃ (G : Scheme.{0}) (ψ : J → (Y ⟶ G)), (∀ j, IsOpenImmersion (ψ j)) ∧ (∀ g : G, ∃ j, g ∈ Set.range (ψ j)) ∧ (∀ i j, IsPullback (V i j).ι (τ i j) (ψ i) (ψ j)) ∧ ∀ (Z : Scheme.{0}) (g : J → (Y ⟶ Z)), (∀ i j, (V i j).ι ≫ g i = τ i j ≫ g j) → ∃ F : G ⟶ Z, ∀ j, ψ j ≫ F = g j := by
  intro Y J V τ hV hτ hr hc
  have mem_of : ∀ (U : Y.Opens) {T : Scheme.{0}} (f : T ⟶ U.toScheme) (p : T), (f ≫ U.ι) p ∈ U :=
    fun U T f p => by
      have h := Set.mem_range_self (f := ⇑U.ι) (f p)
      rw [Scheme.Opens.range_ι] at h
      rw [Scheme.Hom.comp_apply]; exact h
  have hs : ∀ i, ∃ s : Y ⟶ (V i i).toScheme, s ≫ (V i i).ι = 𝟙 _ := fun i =>
    ⟨IsOpenImmersion.lift (V i i).ι (𝟙 _) (by
      rw [Scheme.Opens.range_ι, hV]; intro x _; simp), IsOpenImmersion.lift_fac _ _ _⟩
  choose s hs using hs
  have ht : ∀ i j, ∃ t : (V i j).toScheme ⟶ (V j i).toScheme, t ≫ (V j i).ι = τ i j := fun i j =>
    ⟨IsOpenImmersion.lift (V j i).ι (τ i j) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hr i j i x (by rw [hV]; simp)), IsOpenImmersion.lift_fac _ _ _⟩
  choose t ht using ht
  have htb : ∀ i j, t i j ≫ τ j i = (V i j).ι := fun i j => by
    have h1 := hc i j i _ (𝟙 _) ((V i j).ι ≫ s i) (t i j) (by simp [hs]) (by simp [ht])
    rw [h1, hτ, Category.assoc, hs, Category.comp_id]
  have hu : ∀ i j k, ∃ u : pullback (V i j).ι (V i k).ι ⟶ (V j k).toScheme,
      u ≫ (V j k).ι = pullback.fst _ _ ≫ τ i j := fun i j k =>
    ⟨IsOpenImmersion.lift (V j k).ι (pullback.fst _ _ ≫ τ i j) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      apply hr i j k
      rw [← Scheme.Hom.comp_apply, pullback.condition]
      exact mem_of _ _ _), IsOpenImmersion.lift_fac _ _ _⟩
  choose u hu using hu
  have hub : ∀ i j k, u i j k ≫ τ j k = pullback.snd _ _ ≫ τ i k := fun i j k =>
    hc i j k _ (pullback.fst _ _) (pullback.snd _ _) (u i j k) pullback.condition (hu i j k).symm
  let D : Scheme.GlueData.{0} :=
    { J := J
      U := fun _ => Y
      V := fun p => (V p.1 p.2).toScheme
      f := fun i j => (V i j).ι
      f_mono := fun i j => inferInstance
      f_id := fun i => ⟨s i, by rw [← cancel_mono (V i i).ι, Category.assoc, hs]; simp, hs i⟩
      t := t
      t_id := fun i => by rw [← cancel_mono (V i i).ι, ht, hτ, Category.id_comp]
      t' := fun i j k => pullback.lift (u i j k) (pullback.fst _ _ ≫ t i j) (by simp [hu, ht])
      t_fac := fun i j k => pullback.lift_snd _ _ _
      cocycle := fun i j k => by
        rw [← cancel_mono (pullback.fst (V i j).ι (V i k).ι), ← cancel_mono (V i j).ι]
        simp only [Category.assoc, pullback.lift_fst_assoc, hu, hub, pullback.lift_snd_assoc, htb,
          Category.id_comp]
      f_open := fun i j => inferInstance }
  have hP : ∀ i j, IsPullback (V i j).ι (τ i j) (D.ι i) (D.ι j) := fun i j => by
    rw [← ht]
    exact IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
  refine ⟨D.glued, D.ι, fun j => D.ι_isOpenImmersion j, fun g => ?_, hP, fun Z g hg => ?_⟩
  · obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective g
    exact ⟨j, y, rfl⟩
  · refine desc_of_compat D g fun i j => ?_
    change (V i j).ι ≫ g i = (t i j ≫ (V j i).ι) ≫ g j
    rw [ht, hg]

end GlobalTheory.GlueCopies
end
