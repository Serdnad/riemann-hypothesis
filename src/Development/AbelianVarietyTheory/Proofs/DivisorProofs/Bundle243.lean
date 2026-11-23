module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue


open Limits in
theorem glue_away : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  intro S _ ι s hs Y e he
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ e i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ e j := by
    intro i j
    refine Scheme.Cover.hom_ext (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.openCover _ _ fun k => ?_
    let a : Spec ((pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k) ⟶ pullback (𝒰.f i) (𝒰.f j) :=
      (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.f k
    let T := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k
    let A : CommRingCat.of (Localization.Away (s i)) ⟶ T := Spec.preimage (a ≫ pullback.fst (𝒰.f i) (𝒰.f j))
    let B : CommRingCat.of (Localization.Away (s j)) ⟶ T := Spec.preimage (a ≫ pullback.snd (𝒰.f i) (𝒰.f j))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s i))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s j))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have key : A.hom.comp (algebraMap S (Localization.Away (s i))) =
        B.hom.comp (algebraMap S (Localization.Away (s j))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hu : IsUnit ((A.hom.comp (algebraMap S (Localization.Away (s i)))) (s i * s j)) := by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact (IsLocalization.Away.algebraMap_isUnit (s i)).map A.hom
      · rw [key]; exact (IsLocalization.Away.algebraMap_isUnit (s j)).map B.hom
    let L : Localization.Away (s i * s j) →+* T := IsLocalization.Away.lift (s i * s j) hu
    have hL : L.comp (algebraMap S (Localization.Away (s i * s j))) =
        A.hom.comp (algebraMap S (Localization.Away (s i))) := IsLocalization.Away.lift_comp _ _
    have hLA : L.comp (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) = A.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s i)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) hL
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayRight_eq, this]
    have hLB : L.comp (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) = B.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s j)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) (hL.trans key)
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayLeft_eq, this]
    have hA : Spec.map A = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLA]; rfl
    have hB : Spec.map B = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLB]; rfl
    have h2 : Spec.map A ≫ e i = Spec.map B ≫ e j := by
      rw [hA, hB, Category.assoc, Category.assoc, he i j]
    rw [ea, eb] at h2
    exact (Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))
  exact ⟨𝒰.glueMorphisms e hf, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 e hf i⟩

end GlobalTheory.SecGlue
end
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.factor_closedImmersion_of_affine_points :
    ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X),
      (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) →
      ∃ z : T ⟶ Z, z ≫ i = g := by
  intro X Z T i hi g h
  let 𝒰 := T.affineCover
  have hj : ∀ j, ∃ y : 𝒰.X j ⟶ Z, y ≫ i = 𝒰.f j ≫ g := fun j => h _ (𝒰.f j)
  choose y hy using hj
  have hc : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ y a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ y b := by
    intro a b
    rw [← cancel_mono i, Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms y hc, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hy]
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem hom_ext_of_span_eq_top (S : Type) [CommRing S] (ι : Type) (s : ι → S)
    (hs : Ideal.span (Set.range s) = ⊤) (Y : Scheme.{0}) (a b : Sp S ⟶ Y)
    (h : ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a =
      spMap (algebraMap S (Localization.Away (s i))) ≫ b) :
    a = b :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
    a b h

end GlobalTheory.SecGlue
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
end

section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory

theorem irreducibleSpace_of_open_cover_meeting {P : Type} [TopologicalSpace P] [Nonempty P]
    (S : Set (Set P)) (hopen : ∀ W ∈ S, IsOpen W) (hirr : ∀ W ∈ S, IsPreirreducible W)
    (hcov : ∀ p : P, ∃ W ∈ S, p ∈ W) (hmeet : ∀ W ∈ S, ∀ W' ∈ S, (W ∩ W').Nonempty) :
    IrreducibleSpace P := by
  refine { isPreirreducible_univ := ?_, toNonempty := inferInstance }
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨Wx, hWx, hxW⟩ := hcov x
  obtain ⟨Wy, hWy, hyW⟩ := hcov y
  obtain ⟨w, hwx, hwu, hwy⟩ :=
    hirr Wx hWx u Wy hu (hopen Wy hWy) ⟨x, hxW, hxu⟩ (hmeet Wx hWx Wy hWy)
  obtain ⟨z, hzW, hz⟩ := hirr Wy hWy u v hu hv ⟨w, hwy, hwu⟩ ⟨y, hyW, hyv⟩
  exact ⟨z, trivial, hz⟩

theorem scheme_homOfLE_apply_mk {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (x : X) (hx : x ∈ V) :
    (X.homOfLE e) ⟨x, hx⟩ = ⟨x, e hx⟩ := by
  apply Subtype.ext
  have h1 : (X.homOfLE e ≫ U.ι) ⟨x, hx⟩ = V.ι ⟨x, hx⟩ := by rw [X.homOfLE_ι]
  simpa using h1

theorem surjective_spMap_of_field {F k : Type} [Field F] [Field k] (f : F →+* k) :
    Surjective (spMap f) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (Sp k) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

theorem irreducibleSpace_pullback_of_cover : ∀ {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F) (k : Type)
    [Field k] (f : F →+* k) (U : X.Opens),
    IsIrreducible (U : Set X) →
    (∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) →
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) := by
  intro F _ X h k _ f U hU hV
  haveI := surjective_spMap_of_field f
  set q := pullback.fst (U.ι ≫ h) (spMap f) with hq
  have hqs : Function.Surjective q := q.surjective

  have key : ∀ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) →
      IsOpen (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      IsPreirreducible (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      ∀ p, U.ι (q p) ∈ V → p ∈ Set.range (pullback.snd (X.homOfLE hVU) q) := by
    intro V hVU hirrV
    refine ⟨(pullback.snd (X.homOfLE hVU) q).isOpenEmbedding.isOpen_range, ?_, ?_⟩
    · let e : pullback (V.ι ≫ h) (spMap f) ≅ pullback (X.homOfLE hVU) q :=
        pullback.congrHom (by rw [← X.homOfLE_ι hVU, Category.assoc]) rfl ≪≫
          (pullbackRightPullbackFstIso (U.ι ≫ h) (spMap f) (X.homOfLE hVU)).symm
      haveI : IrreducibleSpace ↑(pullback (X.homOfLE hVU) q) :=
        (Scheme.homeoOfIso e).surjective.irreducibleSpace (Scheme.homeoOfIso e).continuous
      rw [← Set.image_univ]
      exact (PreirreducibleSpace.isPreirreducible_univ (X := ↑(pullback (X.homOfLE hVU) q))).image _
        (pullback.snd (X.homOfLE hVU) q).continuous.continuousOn
    · intro p hp
      rw [Scheme.Pullback.range_snd]
      refine ⟨⟨U.ι (q p), hp⟩, ?_⟩
      show (X.homOfLE hVU) ⟨U.ι (q p), hp⟩ = q p
      rw [scheme_homOfLE_apply_mk]
      rfl
  have hUne : (U : Set X).Nonempty := hU.nonempty
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨p₀, -⟩ := hqs ⟨y₀, hy₀⟩
  haveI : Nonempty ↑(pullback (U.ι ≫ h) (spMap f)) := ⟨p₀⟩
  let S : Set (Set ↑(pullback (U.ι ≫ h) (spMap f))) :=
    {W | ∃ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) ∧
      (V : Set X).Nonempty ∧ W = Set.range (pullback.snd (X.homOfLE hVU) q)}
  refine irreducibleSpace_of_open_cover_meeting S ?_ ?_ ?_ ?_
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).1
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).2.1
  · intro p
    have hyU : U.ι (q p) ∈ U := (q p).2
    obtain ⟨V, hVU, hyV, hi⟩ := hV _ hyU
    exact ⟨_, ⟨V, hVU, hi, ⟨_, hyV⟩, rfl⟩, (key V hVU hi).2.2 p hyV⟩
  · rintro W ⟨V, hVU, hi, ⟨a, ha⟩, rfl⟩ W' ⟨V', hVU', hi', ⟨b, hb⟩, rfl⟩
    obtain ⟨z, hzU, hzV, hzV'⟩ :=
      hU.2 (V : Set X) (V' : Set X) V.isOpen V'.isOpen ⟨a, hVU ha, ha⟩ ⟨b, hVU' hb, hb⟩
    obtain ⟨p, hp⟩ := hqs ⟨z, hzU⟩
    have hpz : U.ι (q p) = z := by rw [hp]; rfl
    exact ⟨p, (key V hVU hi).2.2 p (hpz ▸ hzV), (key V' hVU' hi').2.2 p (hpz ▸ hzV')⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GeomFibre

theorem finite_of_finite_sections {K : Type} [Field K] [IsAlgClosed K] {P : Scheme.{0}}
    (g : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (h : Finite {p : Spec (CommRingCat.of K) ⟶ P // p ≫ g = 𝟙 _}) : Finite P := by
  have := LocallyOfFiniteType.jacobsonSpace g
  have h1 : (closedPoints P).Finite :=
    Set.finite_coe_iff.mp ((pointEquivClosedPoint g).finite_iff.mp h)
  have hc : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact h1.isClosed_biUnion fun x hx ↦ hx
  have h2 := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := P))
  rw [Set.univ_inter, hc.closure_eq] at h2
  exact Set.finite_univ_iff.mp (h2 ▸ h1)

theorem locallyQuasiFinite_of_finite_geometric_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
        Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}) → LocallyQuasiFinite f := by
  intro X Y f _ H
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  rcases (f ⁻¹' {y}).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]; exact Set.finite_empty
  obtain rfl : f x₀ = y := hx₀
  let K := AlgebraicClosure (X.residueField x₀)
  let x : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have hx : ∀ z, x z = x₀ := fun z ↦ by
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hfin : Finite ↥(pullback f (x ≫ f)) := by
    refine finite_of_finite_sections (pullback.snd f (x ≫ f)) ?_
    have := (H K x).to_subtype
    refine Finite.of_injective (β := {y : Sp K ⟶ X | y ≫ f = x ≫ f})
      (fun p ↦ ⟨p.1 ≫ pullback.fst f (x ≫ f), ?_⟩) fun a b hab ↦ ?_
    · change (p.1 ≫ _) ≫ f = x ≫ f
      rw [Category.assoc, pullback.condition, reassoc_of% p.2]
    · exact Subtype.ext (pullback.hom_ext (congrArg Subtype.val hab) (a.2.trans b.2.symm))
  refine (Set.finite_range (pullback.fst f (x ≫ f))).subset fun z hz ↦ ?_
  rw [Scheme.Pullback.range_fst]
  exact ⟨IsLocalRing.closedPoint K,
    ((Scheme.Hom.comp_apply x f _).trans (congrArg f (hx _))).trans hz.symm⟩

end GlobalTheory.GeomFibre
end

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SmoothNormal

theorem isNormalScheme_of_smoothOfRelativeDimension :
    ∀ (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro B Y _ π n _ hB
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth π hB

end GlobalTheory.SmoothNormal
end

section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GeomIrr

set_option backward.isDefEq.respectTransparency false

theorem irreducibleSpace_pullback_of_isDomain_tensor : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    (letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f))) := by
  intro F _ X g V hV k _ f
  letI : Algebra F Γ(X, V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  letI : Algebra F k := f.toAlgebra
  intro hdom
  have hφ : hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
  have e1 : V.ι ≫ g = hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← hφ, IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  let m := pullback.map (V.ι ≫ g) (spMap f) (Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))))
    (Spec.map (CommRingCat.ofHom (algebraMap F k))) hV.isoSpec.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, e1]) (by simp; rfl)
  let E : pullback (V.ι ≫ g) (spMap f) ≅ Spec (CommRingCat.of (Γ(X, V) ⊗[F] k)) :=
    asIso m ≪≫ pullbackSpecIso F Γ(X, V) k
  haveI : IsDomain (Γ(X, V) ⊗[F] k) :=
    MulEquiv.isDomain (k ⊗[F] Γ(X, V)) (Algebra.TensorProduct.comm F Γ(X, V) k).toRingEquiv.toMulEquiv
  haveI : IrreducibleSpace (Spec (CommRingCat.of (Γ(X, V) ⊗[F] k))) :=
    PrimeSpectrum.irreducibleSpace (R := Γ(X, V) ⊗[F] k)
  exact Function.Surjective.irreducibleSpace E.inv.homeomorph.continuous E.inv.homeomorph.surjective

end GlobalTheory.GeomIrr
end
end

section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct


set_option backward.isDefEq.respectTransparency false in

theorem _root_.GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    (letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f))) := by
  intro F _ X g V hV k _ f
  let : Algebra F Γ(X, V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
  let : Algebra F k := f.toAlgebra
  intro hdom
  have hSpec : hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hComp : V.ι ≫ g = hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))) := by
    rw [← hSpec, IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  let m := pullback.map (V.ι ≫ g) (spMap f) (Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, V))))
    (Spec.map (CommRingCat.ofHom (algebraMap F k))) hV.isoSpec.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hComp]) (by simp only [Category.comp_id, Category.id_comp]; rfl)
  let e : pullback (V.ι ≫ g) (spMap f) ≅ Spec (CommRingCat.of (Γ(X, V) ⊗[F] k)) :=
    asIso m ≪≫ pullbackSpecIso F Γ(X, V) k
  have : IsDomain (Γ(X, V) ⊗[F] k) :=
    MulEquiv.isDomain (k ⊗[F] Γ(X, V)) (Algebra.TensorProduct.comm F Γ(X, V) k).toRingEquiv.toMulEquiv
  have : IrreducibleSpace (Spec (CommRingCat.of (Γ(X, V) ⊗[F] k))) :=
    PrimeSpectrum.irreducibleSpace (R := Γ(X, V) ⊗[F] k)
  exact Function.Surjective.irreducibleSpace e.inv.homeomorph.continuous e.inv.homeomorph.surjective
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SectionLattice

def IntegralAtSection {W K' : Type} [CommRing W] [Field K'] [Algebra W K'] {G : Scheme.{0}}
    (p : G ⟶ Sp W) {P M : LB G} {N : LB (pullback p (spMap (algebraMap W K')))}
    (w : LB.Iso (M.pull (pullback.fst p (spMap (algebraMap W K')))) N)
    (w₁ : LB.Iso (P.pull (pullback.fst p (spMap (algebraMap W K')))) N) : Prop :=
  ∃ (e₀ : Sp W ⟶ G) (_ : e₀ ≫ p = 𝟙 _) (x : Sp K' ⟶ pullback p (spMap (algebraMap W K')))
    (_ : x ≫ pullback.fst p (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀)
    (_ : x ≫ pullback.snd p (spMap (algebraMap W K')) = 𝟙 _)
    (i : P.ι) (m : M.ι) (n : N.ι) (_ : ⊤ ≤ e₀ ⁻¹ᵁ P.U i) (_ : ⊤ ≤ e₀ ⁻¹ᵁ M.U m)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => i)))
    (h₂ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => m)))
    (a : W),
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h₁).hom (w₁.s (n, fun _ => i)).val) =
      algebraMap W K' a * (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
        ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)

end GlobalTheory.SectionLattice
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Pinch

def IsSecFam {X : Scheme.{0}} (L : LB X) {J : Type} (D : J → X.Opens) (k : J → L.ι)
    (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)) : Prop :=
  ∀ (j j' : J) (z : X) (hz : z ∈ D j) (hz' : z ∈ D j'),
    (X.presheaf.germ (D j) z hz).hom (e j) =
      (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hD j hz, hD j' hz'⟩).hom (L.g (k j) (k j')).val *
        (X.presheaf.germ (D j') z hz').hom (e j')

end GlobalTheory.Pinch
end
end
