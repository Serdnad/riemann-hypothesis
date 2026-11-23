module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle626
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
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

namespace GlobalTheory.AffInj

theorem inr_injective_of_isPushout {R A K P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : Function.Injective φ.hom)
    (hψ : ψ.hom.Flat) : Function.Injective inr.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  have h1 : inr = _ ≫ e.hom :=
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A K) H).symm
  rw [h1, CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback e.hom).comp ?_
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := K)
    (Algebra.linearMap R A) hφ
  intro a b hab
  apply (TensorProduct.lid R K).symm.injective
  apply hinj
  simpa using hab

end GlobalTheory.AffInj

namespace GlobalTheory.AffInj

theorem app_injective_of_isPullback (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R)
    (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S) (hπ : IsProper π) (hy : Flat y)
    (H : IsPullback p q y π) (hinj : Function.Injective π.appTop.hom) (V : Y.Opens)
    (hV : IsAffineOpen V) : Function.Injective (p.app V).hom := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have hUY : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hST : V ≤ y ⁻¹ᵁ ⊤ := le_top
  have hSX : (⊤ : S.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  let σ := pushoutSection H.flip hST hSX hUY
  have hm : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H.flip hST hSX hUY
    (isAffineOpen_top _) hV (by simpa using isCompact_univ)
  have hσ : Function.Injective σ.hom := (ConcreteCategory.mono_iff_injective_of_preservesPullback σ).mp hm
  have h1 : pushout.inr _ _ ≫ σ = p.appLE V (p ⁻¹ᵁ V) le_rfl := pushout.inr_desc _ _ _
  have hφ : Function.Injective (π.appLE ⊤ ⊤ hSX).hom := by
    have e : π.appLE ⊤ ⊤ hSX = π.appTop := (Scheme.Hom.app_eq_appLE π (U := ⊤)).symm
    rw [e]; exact hinj
  have hinr := inr_injective_of_isPushout (IsPushout.of_hasPushout (π.appLE ⊤ ⊤ hSX)
    (y.appLE ⊤ V hST)) hφ (y.flat_appLE (isAffineOpen_top _) hV _)
  have h2 : p.app V = p.appLE V (p ⁻¹ᵁ V) le_rfl := Scheme.Hom.app_eq_appLE p
  rw [h2, ← h1, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hσ.comp hinr

end GlobalTheory.AffInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem restrict_proper_sections_bijective_to_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  intro Y₀ H X'' P'' H' i a'' b'' hY hi ha hs hV hb
  haveI := hY; haveI := hi; haveI := ha; haveI := hs; haveI := hb
  have hP : IsNoetherian P'' := by
    haveI : IsLocallyNoetherian P'' := LocallyOfFiniteType.isLocallyNoetherian b''
    haveI : CompactSpace P'' := QuasiCompact.compactSpace_of_compactSpace b''
    exact {}
  let U0 : P''.Opens := ⟨(a'' '' (Set.range i)ᶜ)ᶜ,
    (a''.isClosedMap _ i.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩
  have hsub : ∀ w : X'', a'' w ∈ U0 → w ∈ Set.range i := by
    intro w hw
    by_contra h
    exact hw ⟨w, h, rfl⟩
  let W : H'.toScheme.Opens := i ⁻¹ᵁ (a'' ⁻¹ᵁ U0)
  let X : H.Opens := H'.ι ''ᵁ W
  have hXr : Set.range X.ι ⊆ Set.range H'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  let k : X.toScheme ⟶ H'.toScheme := IsOpenImmersion.lift H'.ι X.ι hXr
  have hk : k ≫ H'.ι = X.ι := IsOpenImmersion.lift_fac _ _ _
  have hrk : Set.range k = (W : Set H'.toScheme) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : H'.ι (k y) ∈ X := by
        rw [← Scheme.Hom.comp_apply, hk]
        have : X.ι y ∈ Set.range X.ι := ⟨y, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      obtain ⟨w, hw, he⟩ := h1
      rwa [← H'.ι.isOpenEmbedding.injective he]
    · intro hz
      have : H'.ι z ∈ Set.range X.ι := by
        rw [Scheme.Opens.range_ι]; exact ⟨z, hz, rfl⟩
      obtain ⟨y, hy⟩ := this
      refine ⟨y, H'.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hk, hy]
  have hrki : Set.range (k ≫ i) = (a'' ⁻¹ᵁ U0 : Set X'') := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrk]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hw
      obtain ⟨z, rfl⟩ := hsub w hw
      exact ⟨z, hw, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq (k ≫ i) (a'' ⁻¹ᵁ U0).ι (by rw [Scheme.Opens.range_ι]; exact hrki)
  let a : X.toScheme ⟶ U0.toScheme := e.hom ≫ (a'' ∣_ U0)
  have hfac : a ≫ U0.ι = k ≫ i ≫ a'' := by
    simp only [a, e, Category.assoc, morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  refine ⟨U0.toScheme, U0.ι, X, k, a, inferInstance, ?_, inferInstance, ?_, ?_, hk, hfac, ?_, ?_⟩
  · haveI := hP
    haveI : CompactSpace U0.toScheme := QuasiCompact.compactSpace_of_compactSpace U0.ι
    exact {}
  · refine ⟨fun x => ?_⟩
    obtain ⟨w, hw⟩ := a''.surjective x.1
    have hw' : w ∈ Set.range (k ≫ i) := by
      rw [hrki]; show a'' w ∈ U0; rw [hw]; exact x.2
    obtain ⟨y, rfl⟩ := hw'
    refine ⟨y, U0.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac]
    simp only [Scheme.Hom.comp_apply] at hw ⊢
    rw [hw]; rfl
  · intro V
    show Function.Bijective ((e.hom ≫ (a'' ∣_ U0)).app V).hom
    rw [Scheme.Hom.comp_app]
    have h1 : Function.Bijective ((a'' ∣_ U0).app V).hom := by
      rw [morphismRestrict_app]
      have h3 := hV (U0.ι ''ᵁ V)
      have h4 : Function.Bijective (X''.presheaf.map (eqToHom (image_morphismRestrict_preimage a'' U0 V)).op).hom :=
        ConcreteCategory.bijective_of_isIso _
      exact h4.comp h3
    have h2 : Function.Bijective (e.hom.app ((a'' ∣_ U0) ⁻¹ᵁ V)).hom := ConcreteCategory.bijective_of_isIso _
    exact h2.comp h1
  · intro z hz
    have : z ∈ W := by
      show a'' (i z) ∈ U0
      rintro ⟨w, hw, he⟩
      exact hw (hz w he)
    exact ⟨z, this, rfl⟩
  · intro w hw
    rw [hrki]
    rw [Scheme.Opens.range_ι] at hw
    exact hw

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Div.DescendOpens

theorem overlap_preimage_open : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), IsProper π → Surjective π → (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ i j : J, ∃ V : U.left.Opens, ∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j) := by
  intro B S X π U J e hP _ hO key i j
  haveI := hP
  haveI : UniversallyClosed (pullback.fst U.hom π) := inferInstance
  set p := pullback.fst U.hom π with hp
  let W : Set ↥(pullback U.hom π) := (e i) ⁻¹' Set.range (e j)
  have hWo : IsOpen W := by
    haveI := hO j
    exact (e i).continuous.isOpen_preimage _ (e j).isOpenEmbedding.isOpen_range
  have sat : ∀ a c : ↥(pullback U.hom π), p a = p c → a ∈ W → c ∈ W := by
    intro a c hac ha
    obtain ⟨b, hb⟩ := ha
    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) a c hac
    have h1 : (pullback.fst p p ≫ e i) t = e j b := by
      simp only [Scheme.Hom.comp_apply, ht1]; exact hb.symm
    obtain ⟨t', ht'1, ht'2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.fst p p ≫ e i) (g := e j) t b h1
    obtain ⟨h₂, hh₂, -⟩ := key i j _
      (pullback.fst (pullback.fst p p ≫ e i) (e j) ≫ pullback.fst p p)
      (pullback.fst (pullback.fst p p ≫ e i) (e j) ≫ pullback.snd p p)
      (pullback.snd (pullback.fst p p ≫ e i) (e j))
      (by simp only [Category.assoc]; rw [pullback.condition])
      (by rw [← pullback.condition, Category.assoc])
    refine ⟨h₂ t', ?_⟩
    have := congrArg (fun f => f t') hh₂
    simp only [Scheme.Hom.comp_apply, ht'1, ht2] at this
    exact this
  refine ⟨⟨(p '' Wᶜ)ᶜ, ?_⟩, ?_⟩
  · exact (p.isClosedMap _ hWo.isClosed_compl).isOpen_compl
  · intro a
    change p a ∈ (p '' Wᶜ)ᶜ ↔ a ∈ W
    constructor
    · intro h
      by_contra ha
      exact h ⟨a, ha, rfl⟩
    · rintro ha ⟨c, hc, hca⟩
      exact hc (sat a c hca.symm ha)

end GlobalTheory.Div.DescendOpens
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZmtNbhd

theorem quasiFiniteAt_of_isolated : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), LocallyOfFiniteType φ →
    ∀ (z : H) (O : H.Opens), z ∈ O → (∀ w ∈ O, φ w = φ z → w = z) → φ.QuasiFiniteAt z := by
  intro H X φ _ z O hzO hO
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (φ.fiberHomeo (φ z)).isOpen_image]
  simp only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  rw [isOpen_induced_iff]
  refine ⟨O, O.isOpen, ?_⟩
  ext ⟨w, hw⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (hO w h hw)
  · intro h
    have : w = z := congrArg Subtype.val h
    exact this ▸ hzO

theorem exists_image_of_isOpenImmersion : ∀ (U T X : Scheme.{0}) (j : U ⟶ T) (q : T ⟶ X),
    IsOpenImmersion j → QuasiCompact j → IsFinite q →
    ∃ (X' : Scheme.{0}) (ν : X' ⟶ X) (i : U ⟶ X'), IsFinite ν ∧ IsOpenImmersion i ∧
      i ≫ ν = j ≫ q ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro U T X j q _ _ _
  refine ⟨j.image, j.imageι ≫ q, j.toImage, inferInstance, inferInstance, by simp, inferInstance, ?_⟩
  intro V
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (C := CommRingCat)
    (F := j.image.sheaf) j.toImage.c V (fun x _ => j.stalkFunctor_toImage_injective x)

theorem exists_finite_openImmersion_nbhd : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), IsNoetherian X → IsSeparated φ → LocallyOfFiniteType φ → QuasiCompact φ → ∀ Z : Set H, (∀ z ∈ Z, ∃ O : H.Opens, z ∈ O ∧ ∀ w ∈ O, φ w = φ z → w = z) → ∃ (H' : H.Opens) (X' : Scheme.{0}) (ν : X' ⟶ X) (i : H'.toScheme ⟶ X'), Z ⊆ H' ∧ IsFinite ν ∧ IsOpenImmersion i ∧ i ≫ ν = H'.ι ≫ φ ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  intro H X φ hX hsep hloft hqc Z hZ
  let H' := φ.quasiFiniteLocus
  have hZH : Z ⊆ (H' : Set H) := fun z hz => by
    obtain ⟨O, hzO, hO⟩ := hZ z hz
    exact quasiFiniteAt_of_isolated H X φ hloft z O hzO hO
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian φ
  have : QuasiCompact H'.ι := inferInstance
  obtain ⟨T, q, j, hq, hj, hjq⟩ := GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite H'.toScheme X (H'.ι ≫ φ) hX inferInstance
    inferInstance inferInstance inferInstance
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ q) := by rw [hjq]; infer_instance
    exact QuasiCompact.of_comp j q
  obtain ⟨X', ν, i, hν, hi, hiν, hdom, hinj⟩ := exists_image_of_isOpenImmersion H'.toScheme T X j q hj this hq
  exact ⟨H', X', ν, i, hZH, hν, hi, by rw [hiν, hjq], hdom, hinj⟩

end GlobalTheory.ZmtNbhd
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem section_eq_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (q q' : Sp k ⟶ X)
    (hq : q ≫ p = 𝟙 _) (hq' : q' ≫ p = 𝟙 _) (h : q (closedPoint k) = q' (closedPoint k)) : q = q' := by
  obtain ⟨⟨y, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q
  obtain ⟨⟨y', a'⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hq hq' h ⊢
  obtain rfl : y = y' := by
    have k₁ : ∀ (y : X) (p : Spec (X.residueField y)), X.fromSpecResidueField y p = y := fun y p =>
      Set.mem_singleton_iff.1 (X.range_fromSpecResidueField y ▸ Set.mem_range_self p)
    exact (k₁ y _).symm.trans (h.trans (k₁ y' _))
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ p)
  have key : ∀ b : X.residueField y ⟶ CommRingCat.of k, (Spec.map b ≫ X.fromSpecResidueField y) ≫ p = 𝟙 _ →
      ∀ o, b.hom (c.hom o) = o := fun b hb o => by
    rw [Category.assoc, ← hc, ← Spec.map_comp] at hb
    have := Spec.map_injective (hb.trans (Spec.map_id _).symm)
    simpa using RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) o
  obtain rfl : a = a' := by
    ext u
    have hu : c.hom (a.hom u) = u := a.hom.injective (key a hq _)
    rw [← hu, key a hq, key a' hq']
  rfl

theorem eq_of_comp_eq_of_connectedSpace_pullback : ∀ (P Q : Scheme.{0}) (b : P ⟶ Q), LocallyQuasiFinite b → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (ξ₁ ξ₂ : Sp Ω ⟶ P), ξ₁ ≫ b = ν → ξ₂ ≫ b = ν → ConnectedSpace (pullback b ν : Scheme.{0}) → ξ₁ = ξ₂ := by
  intro P Q b hb Ω _ _ ν ξ₁ ξ₂ h₁ h₂ hc
  haveI := hb
  have hsub : ∀ x y : (pullback b ν : Scheme.{0}), x = y := by
    intro x y
    have hopen : ∀ z : (pullback b ν : Scheme.{0}), IsOpen ({z} : Set (pullback b ν : Scheme.{0})) := by
      intro z
      have hd := (pullback.snd b ν).isDiscrete_preimage_singleton (pullback.snd b ν z)
      obtain ⟨U, hU, hUz⟩ := isDiscrete_iff_forall_exists_isOpen.mp hd z rfl
      have hU' : U ∩ (pullback.snd b ν) ⁻¹' {pullback.snd b ν z} = U :=
        Set.inter_eq_left.mpr fun w _ => Subsingleton.elim _ _
      rw [hU'] at hUz
      exact hUz ▸ hU
    have hcl : IsClopen ({x} : Set (pullback b ν : Scheme.{0})) := by
      refine ⟨?_, hopen x⟩
      rw [← isOpen_compl_iff, ← Set.biUnion_of_singleton ({x}ᶜ : Set (pullback b ν : Scheme.{0}))]
      exact isOpen_biUnion fun z _ => hopen z
    rcases isClopen_iff.mp hcl with h | h
    · exact absurd h (Set.singleton_ne_empty x)
    · have : y ∈ ({x} : Set (pullback b ν : Scheme.{0})) := h ▸ Set.mem_univ y
      exact (Set.mem_singleton_iff.mp this).symm
  have e₁ : ξ₁ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₁, Category.id_comp]
  have e₂ : ξ₂ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₂, Category.id_comp]
  have hσ := section_eq_of_apply_eq (pullback.snd b ν) (pullback.lift ξ₁ (𝟙 _) e₁) (pullback.lift ξ₂ (𝟙 _) e₂)
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (hsub _ _)
  have := congrArg (fun σ => σ ≫ pullback.fst b ν) hσ
  simp only [pullback.lift_fst] at this
  exact this

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.smooth_iSup_comp (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  set U := ⨆ i, V i with hUdef
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth.{0}) (fun i => U.ι ⁻¹ᵁ V i) ?_ ?_
  · apply top_unique
    intro x _
    have hx : (U.ι x : P') ∈ (⨆ i, V i : P'.Opens) := x.2
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have hrange : Set.range ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) = Set.range (V i).ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      ext y
      simp only [Set.mem_image, SetLike.mem_coe, Scheme.Hom.mem_preimage]
      exact ⟨by rintro ⟨x, hx, rfl⟩; exact hx, fun hy => ⟨⟨y, hle i hy⟩, hy, rfl⟩⟩
    rw [← Category.assoc, ← IsOpenImmersion.isoOfRangeEq_hom_fac ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) (V i).ι hrange,
      Category.assoc]
    haveI := h i
    infer_instance
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem affineChart_smooth : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)), Smooth Y.hom → ∀ (W : Y.left.Opens), IsAffineOpen W → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (k : Sp O ⟶ Y.left) (_ : IsOpenImmersion k), k.opensRange = W ∧ k ≫ Y.hom = spMap (algebraMap R O) ∧ Algebra.Smooth R O := by
  intro R _ Y hY W hW
  let alg : R →+* Γ(Y.left, W) :=
    (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI : Algebra R Γ(Y.left, W) := alg.toAlgebra
  have s₀ : hW.fromSpec ≫ Y.hom = spMap alg := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom (isAffineOpen_top _) hW (fun _ _ => trivial),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
  have h1 : RingHom.Smooth (Y.hom.appLE ⊤ W (fun _ _ => trivial)).hom :=
    HasRingHomProperty.appLE @Smooth Y.hom hY ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  have h2 : RingHom.Smooth alg :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact ⟨Γ(Y.left, W), inferInstance, inferInstance, hW.fromSpec, inferInstance, hW.opensRange_fromSpec, s₀, h2⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.NearSurj

theorem surjective_of_open_closedFibre : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  intro R _ _ U hs hsu V hV
  have : Smooth (U ⊗ U).hom := inferInstanceAs (Smooth (pullback.fst U.hom U.hom ≫ U.hom))
  obtain ⟨u, hu⟩ := U.hom.surjective (closedPoint R)
  let d : U.left ⟶ (U ⊗ U).left := pullback.lift (𝟙 _) (𝟙 _) rfl
  have hd : (U ⊗ U).hom (d u) = closedPoint R := by
    rw [← hu, ← Scheme.Hom.comp_apply]
    change (pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom ≫ U.hom) u = _
    rw [pullback.lift_fst_assoc, Category.id_comp]
  have hmem : d u ∈ V := hV _ hd
  have ho : IsOpenMap (V.ι ≫ (U ⊗ U).hom) := (V.ι ≫ (U ⊗ U).hom).isOpenMap
  refine ⟨fun r => ?_⟩
  obtain ⟨y, hy⟩ : d u ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hmem
  have h₂ : (V.ι ≫ (U ⊗ U).hom) y = closedPoint R := by
    rw [Scheme.Hom.comp_apply, hy]; exact hd
  exact (IsLocalRing.specializes_closedPoint r).mem_open ho.isOpen_range ⟨_, h₂⟩

end GlobalTheory.Mum.NearSurj
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → Function.Injective π.appTop.hom → ∀ V : Y.Opens, IsAffineOpen V → Function.Injective (p.app V).hom := by
  first | exact @GlobalTheory.AffInj.app_injective_of_isPullback | exact GlobalTheory.AffInj.app_injective_of_isPullback | (intros; apply GlobalTheory.AffInj.app_injective_of_isPullback <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_proper_surjective_sections_bijective_over_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  first | exact @GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | exact GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | (intros; apply GlobalTheory.restrict_proper_sections_bijective_to_fibre_open <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.chartOverlap_eq_preimage_open_of_fibre_stable : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), IsProper π → Surjective π → (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ i j : J, ∃ V : U.left.Opens, ∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j) := by
  first | exact @GlobalTheory.Div.DescendOpens.overlap_preimage_open | exact GlobalTheory.Div.DescendOpens.overlap_preimage_open | (intros; apply GlobalTheory.Div.DescendOpens.overlap_preimage_open <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.eq_of_comp_eq_of_connectedSpace_pullback' : ∀ (P Q : Scheme.{0}) (b : P ⟶ Q), LocallyQuasiFinite b → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (ξ₁ ξ₂ : Sp Ω ⟶ P), ξ₁ ≫ b = ν → ξ₂ ≫ b = ν → ConnectedSpace (pullback b ν : Scheme.{0}) → ξ₁ = ξ₂ := by
  first | exact @GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback | exact GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback | (intros; apply GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback <;> assumption)

end
end
