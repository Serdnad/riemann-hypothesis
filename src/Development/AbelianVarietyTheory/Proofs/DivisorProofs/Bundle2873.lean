module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem glue_overlap_cocycle : ∀ (B S X : Scheme.{0}) (π : S ⟶ B), Surjective π → ∀ (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) := by
  intro B S X π hπ U J e he V τ hV hτ
  have hp : Function.Surjective (pullback.fst U.hom π) := (inferInstance : Surjective (pullback.fst U.hom π)).surj
  refine ⟨fun i => ?_, fun i j k x hx => ?_⟩
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨a, rfl⟩ := hp y
    exact (hV i i a).mpr ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := hp ((V i j).ι x)
    have hij : e i a ∈ Set.range (e j) := (hV i j a).mp (by
      rw [ha]
      have hx' : (V i j).ι x ∈ Set.range (V i j).ι := ⟨x, rfl⟩
      rwa [Scheme.Opens.range_ι] at hx')
    obtain ⟨b, hb⟩ := hij
    have hik : e i a ∈ Set.range (e k) := (hV i k a).mp (by rw [ha]; exact hx)
    obtain ⟨t, ht1, ht2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (e i) (e j)) a b hb.symm
    have hrange : Set.range (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) ⊆ Set.range (V i j).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (pullback.fst U.hom π) (pullback.fst (e i) (e j) z) ∈ V i j
      rw [hV i j]
      refine ⟨pullback.snd (e i) (e j) z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    let v := IsOpenImmersion.lift (V i j).ι (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) hrange
    have hv : v ≫ (V i j).ι = pullback.fst (e i) (e j) ≫ pullback.fst U.hom π := IsOpenImmersion.lift_fac _ _ _
    have key := hτ i j _ (pullback.fst (e i) (e j)) (pullback.snd (e i) (e j)) v pullback.condition hv
    have hvt : v t = x := by
      apply (V i j).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, ht1, ha]
    have : τ i j x = pullback.fst U.hom π b := by
      rw [← hvt, ← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, ht2]
    rw [this, hV j k, hb]
    exact hik

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SepDescent

def closedRange : MorphismProperty Scheme.{0} := fun _ _ f => IsClosed (Set.range f.base)

lemma range_iso_comp {X Y Z : Scheme.{0}} (e : X ≅ Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ f).base = Set.range f.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom.base x, by simp⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]

instance : closedRange.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    change IsClosed _
    rw [range_iso_comp]
    exact hf
  · intro X Y Z e f hf
    change IsClosed _
    have : Set.range (f ≫ e.hom).base = e.hom.base '' Set.range f.base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [this]
    exact e.hom.isClosedMap _ hf

instance : closedRange.DescendsAlong (@UniversallyClosed ⊓ @Surjective) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  haveI : UniversallyClosed f := hf.1
  have hs : Function.Surjective f.base := hf.2.surj
  have e : Set.range g.base = f.base '' Set.range (pullback.fst f g).base := by
    rw [Scheme.Pullback.range_fst, Set.image_preimage_eq _ hs]
  change IsClosed _
  rw [e]
  exact f.isClosedMap _ hfst

instance : (@UniversallyClosed ⊓ @Surjective : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
  @MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance

instance : (MorphismProperty.diagonal closedRange).DescendsAlong
    (@UniversallyClosed ⊓ @Surjective : MorphismProperty Scheme.{0}) :=
  inferInstance

end GlobalTheory.SepDescent


open GlobalTheory.SepDescent in
theorem GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), UniversallyClosed π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left),
    IsPullback β G'.hom G.hom π → IsSeparated G'.hom → IsSeparated G.hom := by
  intro R _ S π h1 h2 G' G β hp hs
  have hd : (MorphismProperty.diagonal closedRange) G.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal closedRange)
      (Q := @UniversallyClosed ⊓ @Surjective) hp.flip ⟨h1, h2⟩
      (pullback.diagonal G'.hom).isClosedMap.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hd⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isPullback_of_openCover_target : ∀ (X G S B : Scheme.{0}) (β : X ⟶ G) (f : X ⟶ S) (g : G ⟶ B) (π : S ⟶ B), β ≫ g = f ≫ π → ∀ (J : Type) (Y P : J → Scheme.{0}) (ψ : ∀ j, Y j ⟶ G) (e : ∀ j, P j ⟶ X) (p : ∀ j, P j ⟶ Y j) (q : ∀ j, P j ⟶ S), (∀ j, IsOpenImmersion (ψ j)) → (∀ y : G, ∃ j, y ∈ Set.range (ψ j)) → (∀ j, IsOpenImmersion (e j)) → (∀ j, IsPullback (p j) (q j) (ψ j ≫ g) π) → (∀ j, e j ≫ β = p j ≫ ψ j) → (∀ j, e j ≫ f = q j) → (∀ (j : J) (x : X), β x ∈ Set.range (ψ j) → x ∈ Set.range (e j)) → IsPullback β f g π := by
  intro X G S B β f g π w J Y P ψ e p q hψ hcov he hP hβ hf hr
  let ψ' : ∀ j, P j ⟶ pullback g π := fun j =>
    pullback.lift (p j ≫ ψ j) (q j) (by rw [Category.assoc]; exact (hP j).w)
  have hψ'f : ∀ j, ψ' j ≫ pullback.fst g π = p j ≫ ψ j := fun j => pullback.lift_fst _ _ _
  have hψ's : ∀ j, ψ' j ≫ pullback.snd g π = q j := fun j => pullback.lift_snd _ _ _
  have sq : ∀ j, IsPullback (ψ' j) (p j) (pullback.fst g π) (ψ j) := fun j =>
    (IsPullback.of_bot (v₁₁ := ψ' j) (v₂₁ := pullback.snd g π) (by rw [hψ's]; exact hP j)
      (hψ'f j).symm (IsPullback.of_hasPullback g π)).flip
  haveI : ∀ j, IsOpenImmersion (ψ' j) := fun j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq j).flip (hψ j)
  have hc : ∀ z : (pullback g π : Scheme), ∃ j y, ψ' j y = z := by
    intro z
    obtain ⟨j, y, hy⟩ := hcov (pullback.fst g π z)
    obtain ⟨t, ht, -⟩ := Scheme.exists_preimage_of_isPullback (sq j) z y hy.symm
    exact ⟨j, t, ht⟩
  let c : X ⟶ pullback g π := pullback.lift β f w
  have hcf : c ≫ pullback.fst g π = β := pullback.lift_fst _ _ _
  have hce : ∀ j, e j ≫ c = ψ' j := fun j => by
    apply pullback.hom_ext
    · rw [Category.assoc, hcf, hβ, hψ'f]
    · rw [Category.assoc, pullback.lift_snd, hf, hψ's]
  have loc : ∀ j, IsPullback (e j) (𝟙 (P j)) c (ψ' j) := fun j => by
    haveI := he j
    refine (IsOpenImmersion.isPullback (𝟙 (P j)) (e j) (ψ' j) c
      (by rw [hce, Category.id_comp]) ?_).flip
    ext x
    change c x ∈ Set.range (ψ' j) ↔ x ∈ Set.range (e j)
    constructor
    · rintro ⟨y, hy⟩
      apply hr j x
      refine ⟨p j y, ?_⟩
      rw [← hcf, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ'f]
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, hce]⟩
  have key : ∀ j : J, (MorphismProperty.isomorphisms Scheme) (pullback.snd c (ψ' j)) := fun j => by
    rw [← (loc j).isoPullback_inv_snd,
      MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)]
    exact MorphismProperty.isomorphisms.infer_property _
  have hiso : (MorphismProperty.isomorphisms Scheme) c :=
    IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers J P ψ' hc) fun j => key j
  haveI : IsIso c := hiso
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eighthPower_inj_exists : ∀ {S : Scheme.{0}} (P C : Over S) [GrpObj P] [IsCommMonObj P] [GrpObj C] (pr : Fin 8 → (P ⟶ C)) (hpr : ∀ a, IsMonHom (pr a)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ P, ∀ a, x ≫ pr a = y a), ∃ inj : Fin 8 → (C ⟶ P), (∀ a, IsMonHom (inj a)) ∧ (∀ a b, inj a ≫ pr b = if a = b then 𝟙 C else 1) ∧ ∏ a, (pr a ≫ inj a) = 𝟙 P := by
  intro S P C _ _ _ pr hpr huniv
  have hext : ∀ {T : Over S} (f g : T ⟶ P), (∀ b, f ≫ pr b = g ≫ pr b) → f = g :=
    fun f g h => (huniv _ (fun b => g ≫ pr b)).unique h (fun _ => rfl)
  choose inj hinj using fun a => (huniv C (fun b => if a = b then 𝟙 C else 1)).exists
  have hmon : ∀ a, IsMonHom (inj a) := by
    intro a
    constructor
    · apply hext
      intro b
      haveI := hpr b
      rw [Category.assoc, hinj a b, IsMonHom.one_hom (pr b)]
      split_ifs
      · simp
      · rw [MonObj.comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    · apply hext
      intro b
      haveI := hpr b
      simp only [Category.assoc]
      rw [hinj a b, IsMonHom.mul_hom (pr b), tensorHom_comp_tensorHom_assoc, hinj a b]
      split_ifs
      · simp
      · rw [MonObj.comp_one, ← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_one, MonObj.comp_one, _root_.one_mul]
  refine ⟨inj, hmon, hinj, ?_⟩
  apply hext
  intro b
  haveI := hpr b
  rw [Fin.prod_univ_eight]
  simp only [MonObj.mul_comp, Category.assoc, hinj, MonObj.comp_one, Category.id_comp, Category.comp_id]
  fin_cases b <;> simp

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace MatUnitIdem

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod' {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp' {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

end MatUnitIdem


open MatUnitIdem in
theorem matUnits_univ_of_idem : ∀ {S : Scheme.{0}} (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] (E : Fin 8 → Fin 8 → (G ⟶ G)) (hE : ∀ a b, IsMonHom (E a b)) (hrel : ∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) (hsum : ∏ a, E a a = 𝟙 G) (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = E 0 0), ∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ (E a 0 ≫ r) = y a := by
  intro S G H _ _ _ E hE hrel hsum i r hi hr hir hri T y
  have key : ∀ b, E b b = (E b 0 ≫ r) ≫ i ≫ E 0 b := by
    intro b
    have h1 : E b 0 ≫ E 0 b = E b b := by rw [hrel]; simp
    have h2 : E b 0 ≫ E 0 0 = E b 0 := by rw [hrel]; simp
    calc E b b = E b 0 ≫ E 0 b := h1.symm
      _ = (E b 0 ≫ E 0 0) ≫ E 0 b := by rw [h2]
      _ = (E b 0 ≫ r) ≫ i ≫ E 0 b := by rw [← hri]; simp only [Category.assoc]
  refine ⟨∏ a, y a ≫ i ≫ E 0 a, ?_, ?_⟩
  · intro b
    haveI := hE b 0
    haveI := hr
    have hx : (∏ a, y a ≫ i ≫ E 0 a) ≫ E b 0 = y b ≫ i ≫ E 0 0 := by
      rw [prod_comp', Finset.prod_eq_single b]
      · have h3 : E 0 b ≫ E b 0 = E 0 0 := by rw [hrel]; simp
        simp only [Category.assoc, h3]
      · intro a _ hab
        have h3 : E 0 a ≫ E b 0 = 1 := by rw [hrel]; simp [hab]
        simp only [Category.assoc, h3, MonObj.comp_one]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [← Category.assoc, hx, ← hri]
    simp only [Category.assoc]
    simp only [reassoc_of% hir, hir, Category.comp_id]
  · intro z hz
    calc z = z ≫ ∏ b, E b b := by rw [hsum, Category.comp_id]
      _ = ∏ b, z ≫ E b b := comp_prod' _ _ _
      _ = ∏ b, y b ≫ i ≫ E 0 b := by
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [key, ← Category.assoc, hz]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem baseChange_eighthPower_product_monHom : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (G H : Over S) [GrpObj G] [GrpObj H] (pr : Fin 8 → (G ⟶ H)), (∀ a, IsMonHom (pr a)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ pr a = y a) → (∀ a, IsMonHom ((Over.pullback t).map (pr a))) ∧ ∀ (T : Over S') (y : Fin 8 → (T ⟶ (Over.pullback t).obj H)), ∃! x : T ⟶ (Over.pullback t).obj G, ∀ a, x ≫ (Over.pullback t).map (pr a) = y a := by
  intro S S' t G H _ _ pr hmon hlim
  refine ⟨fun a => by haveI := hmon a; infer_instance, ?_⟩
  let c : Fan (fun _ : Fin 8 => H) := Fan.mk G pr
  have hc : IsLimit c := by
    refine Fan.IsLimit.mk c (fun s => (hlim s.pt s.proj).choose) (fun s j => ?_) (fun s m hm => ?_)
    · exact (hlim s.pt s.proj).choose_spec.1 j
    · exact (hlim s.pt s.proj).choose_spec.2 m hm
  intro T y
  let s : Fan (fun _ : Fin 8 => (Over.pullback t).obj H) := Fan.mk T y
  have hs : IsLimit (Fan.mk ((Over.pullback t).obj G) (fun a => (Over.pullback t).map (pr a))) :=
    isLimitFanMkObjOfIsLimit (Over.pullback t) (fun _ : Fin 8 => H) pr hc
  refine ⟨hs.lift s, fun a => hs.fac s ⟨a⟩, fun x hx => ?_⟩
  exact hs.uniq s x (by rintro ⟨a⟩; exact hx a)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum

theorem over_pullback_map_left_comp_pullbackFst_scheme {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.descent_eqn_of_chart_projection : ∀ (B S X G : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)) (ψ : J → (U.left ⟶ G)) (β : X ⟶ G), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ j, e j ≫ β = pullback.fst _ _ ≫ ψ j) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  intro B S X G π f Φ U J e ψ β he hcov hf hβ hch
  let 𝒰 : (pullback f (pullback.fst π π)).OpenCover :=
    Scheme.Cover.mkOfCovers J (fun j => pullback (e j) (pullback.fst f (pullback.fst π π)))
      (fun j => pullback.snd _ _) (by
        intro q
        obtain ⟨j, y, hy⟩ := (by simpa [Set.mem_range] using hcov (pullback.fst f (pullback.fst π π) q) :
          ∃ j, ∃ y, (e j) y = pullback.fst f (pullback.fst π π) q)
        obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback
          (IsPullback.of_hasPullback (e j) (pullback.fst f (pullback.fst π π))) y q hy
        exact ⟨j, p, hp⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ (fun (j : J) => ?_)
  change pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _ =
    pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _
  have hc := pullback.condition (f := e j) (g := pullback.fst f (pullback.fst π π))
  generalize pullback.snd (e j) (pullback.fst f (pullback.fst π π)) = z at hc ⊢
  generalize pullback.fst (e j) (pullback.fst f (pullback.fst π π)) = y₁ at hc
  have h1 : y₁ ≫ pullback.snd U.hom π = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π := by
    calc y₁ ≫ pullback.snd U.hom π = y₁ ≫ e j ≫ f := by rw [hf]
      _ = z ≫ pullback.fst f (pullback.fst π π) ≫ f := by rw [reassoc_of% hc]
      _ = z ≫ pullback.snd f (pullback.fst π π) ≫ pullback.fst π π := by rw [pullback.condition]
      _ = _ := (Category.assoc _ _ _).symm
  have h2 : (y₁ ≫ pullback.fst U.hom π) ≫ U.hom =
      ((z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.snd π π) ≫ π := by
    calc (y₁ ≫ pullback.fst U.hom π) ≫ U.hom = y₁ ≫ pullback.snd U.hom π ≫ π := by
          rw [Category.assoc, pullback.condition]
      _ = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by rw [reassoc_of% h1]; simp only [Category.assoc]
      _ = _ := by rw [pullback.condition]; simp only [Category.assoc]
  have hΦ := hch j _ y₁ (pullback.lift _ _ h2) _ (pullback.lift_fst _ _ _).symm h1
    (pullback.lift_snd _ _ _) z hc.symm rfl
  calc z ≫ pullback.fst f (pullback.fst π π) ≫ β = y₁ ≫ e j ≫ β := by
        rw [reassoc_of% hc]
    _ = pullback.lift _ _ h2 ≫ e j ≫ β := by
        rw [hβ, pullback.lift_fst_assoc, Category.assoc]
    _ = z ≫ Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
        have h3 := congrArg (· ≫ β) hΦ
        simpa only [Category.assoc] using h3.symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.isPullback_of_open_baseChange_eq_preimage : ∀ (S S₁ P G : Scheme.{0}) (p : P ⟶ S) (s : S₁ ⟶ S) (e : G ⟶ P) (c : G ⟶ S₁) (hw : e ≫ p = c ≫ s), IsOpenImmersion (Limits.pullback.lift e c hw) → ∀ V : P.Opens, (∀ w : ↥(Limits.pullback p s), Limits.pullback.fst p s w ∈ V ↔ w ∈ Set.range (Limits.pullback.lift e c hw)) → ∃ e' : G ⟶ V.toScheme, e' ≫ V.ι = e ∧ IsPullback e' c (V.ι ≫ p) s := by
  first | exact @GlobalTheory.Desc.isPullback_of_open_part_eq_preimage | exact GlobalTheory.Desc.isPullback_of_open_part_eq_preimage | (intros; apply GlobalTheory.Desc.isPullback_of_open_part_eq_preimage <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_section_translate_baseChange_of_point : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R') (G : Over (Sp R)) [GrpObj G] (c : Sp R' ⟶ G.left), c ≫ G.hom = spMap ρ → ∃ (a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G) (Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left), IsPullback Φ (pullback.snd G.hom (spMap ρ)) (snd G G).left c ∧ Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * snd G G).left ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * (snd G G)⁻¹).left := by
  first | exact @GlobalTheory.TransBaseChange.exists_section_translate | exact GlobalTheory.TransBaseChange.exists_section_translate | (intros; apply GlobalTheory.TransBaseChange.exists_section_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp : ∀ (R' : Type) [CommRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSeparated G'.hom → ∀ (a : 𝟙_ (Over (Sp R')) ⟶ G') (W : G'.left.Opens), IsAffineOpen W → IsAffineOpen ((𝟙 G' * (toUnit G' ≫ a)).left ⁻¹ᵁ W ⊓ (𝟙 G' * (toUnit G' ≫ a⁻¹)).left ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.TransAff.isAffineOpen_translates | exact GlobalTheory.TransAff.isAffineOpen_translates | (intros; apply GlobalTheory.TransAff.isAffineOpen_translates <;> assumption)
end
