module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle010
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem restrict_isPullback {R : Type} [CommRing R] {S Y Z Y' : Scheme.{0}} {π : S ⟶ Sp R} {y : Y ⟶ Sp R}
    {p : Z ⟶ Y} {q : Z ⟶ S} (hpb : IsPullback p q y π) (f : Y' ⟶ Y) :
    IsPullback (pullback.snd p f) (pullback.fst p f ≫ q) (f ≫ y) π :=
  IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb

theorem uniq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) (g₁ g₂ : Y ⟶ W), p ≫ g₁ = p ≫ g₂ → g₁ = g₂ := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W g₁ g₂ he
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have heqz := GlobalTheory.T.flat_descent_sections_injective_equalizer R S Y Z π y p q hprop hsurj hint hflat hpb
  have hbase : g₁.base = g₂.base := by
    ext x
    obtain ⟨z, rfl⟩ := p.surjective x
    have := congrArg (fun k : Z ⟶ W => k z) he
    simpa only [Scheme.Hom.comp_apply] using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (p.app (g₂ ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (heqz _).1
  rw [← cancel_mono (p.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm,
    Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]
  rfl

theorem exAff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) [IsAffine W] (h : Z ⟶ W), pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃ h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W _ h hh
  obtain ⟨hinj, hdesc⟩ := GlobalTheory.T.flat_descent_sections_injective_equalizer R S Y Z π y p q hprop hsurj hint hflat hpb ⊤
  have hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ (p.app ⊤).hom.range := by
    intro x
    refine hdesc (h.appTop x) fun e => ?_
    have := congrArg (fun k : pullback p p ⟶ W => k.appTop.hom x) hh
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.trans ?_
    change _ = (CommRingCat.Hom.hom ((pullback p p).presheaf.map (𝟙 (Opposite.op (⊤ : (pullback p p).Opens)))))
      ((pullback.snd p p).appTop.hom (h.appTop.hom x))
    rw [CategoryTheory.Functor.map_id]
    rfl
  let φ : Γ(W, ⊤) →+* Γ(Y, ⊤) :=
    (RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (h.appTop.hom.codRestrict _ hmem)
  have hφ : CommRingCat.ofHom φ ≫ p.appTop = h.appTop := by
    ext x
    exact congrArg Subtype.val ((RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply
      (h.appTop.hom.codRestrict _ hmem x))
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = Z.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  rw [h1, ← Category.assoc p, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ h : Z ⟶ W, pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃! h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z W π y p q hprop hsurj hint hflat hpb h hh
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have hpC : UniversallyClosed p := MorphismProperty.of_isPullback (P := @UniversallyClosed) hpb.flip inferInstance
  have hfib : Function.FactorsThrough h.base.hom p.base.hom := by
    intro a b hab
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) a b hab
    have := congrArg (fun k : pullback p p ⟶ W => k z) hh
    simp only [Scheme.Hom.comp_apply, hz1, hz2] at this
    exact this
  have hq : Topology.IsQuotientMap p.base.hom :=
    IsClosedMap.isQuotientMap p.isClosedMap p.base.hom.continuous p.surjective
  let b : Y.carrier ⟶ W.carrier := TopCat.ofHom (hq.lift h.base.hom hfib)
  have hb : ∀ z, b (p z) = h z := fun z => congrArg (fun k : C(Z, W) => k z) (hq.lift_comp h.base.hom hfib)
  let V : W.affineOpens → Y.Opens := fun i => TopologicalSpace.Opens.comap b.hom i.1
  have hV : TopologicalSpace.IsOpenCover V := W.isBasis_affineOpens.isOpenCover.comap b.hom
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd p (V i).ι ≫ u = pullback.fst p (V i).ι ≫ h := by
    intro i
    have hr : Set.range (pullback.fst p (V i).ι ≫ h) ⊆ Set.range i.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ((pullback.snd p (V i).ι) w).2
    let hi := IsOpenImmersion.lift i.1.ι _ hr
    have : IsAffine i.1.toScheme := i.2
    have heq : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi =
        pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi := by
      rw [← cancel_mono i.1.ι]
      simp only [Category.assoc, hi, IsOpenImmersion.lift_fac]
      let m : pullback (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ⟶ pullback p p :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
          (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])
      have e1 : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
      have e2 : pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
      rw [reassoc_of% e1, reassoc_of% e2, hh]
    obtain ⟨u, hu⟩ := exAff R S (V i).toScheme (pullback p (V i).ι) π ((V i).ι ≫ y) (pullback.snd p (V i).ι)
      (pullback.fst p (V i).ι ≫ q) hprop hsurj hint inferInstance (restrict_isPullback hpb _) i.1.toScheme hi heq
    exact ⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩
  choose u hu using hloc
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j := by
    intro i j
    let f := pullback.fst (V i).ι (V j).ι ≫ (V i).ι
    apply uniq R S _ (pullback p f) π (f ≫ y) (pullback.snd p f) (pullback.fst p f ≫ q) hprop hsurj hint
      inferInstance (restrict_isPullback hpb f) W
    let mi : pullback p f ⟶ pullback p (V i).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])
    let mj : pullback p f ⟶ pullback p (V j).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.snd _ _) (by
        rw [pullback.condition]
        show pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _
        rw [pullback.condition, Category.assoc])
    have ei : pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd p (V i).ι :=
      (pullback.lift_snd _ _ _).symm
    have ej : pullback.snd p f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd p (V j).ι :=
      (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have hglue : p ≫ 𝒰.glueMorphisms u hc = h := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ p) _ _ fun i => ?_
    change pullback.fst p (V i).ι ≫ _ = pullback.fst p (V i).ι ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd p (V i).ι ≫ 𝒰.f i ≫ _ = _
    exact (congrArg (pullback.snd p (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)
  refine ⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩
  exact uniq R S Y Z π y p q hprop hsurj hint hflat hpb W g _ (hg.trans hglue.symm)

end GlobalTheory.MorDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory

theorem eq_of_specializes_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {x x' : X}, x ⤳ x' → f x = f x' → x = x' := by
  intro X Y f _ x x' hxx' hf
  obtain ⟨_, ⟨V, hV0, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have hV : IsAffineOpen V := hV0
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hx' : x' ∈ f ⁻¹ᵁ V := hxV
  have hx : x ∈ f ⁻¹ᵁ V := hxx'.mem_open (f ⁻¹ᵁ V).isOpen hx'
  set P := hU.primeIdealOf ⟨x, hx⟩ with hPdef
  set P' := hU.primeIdealOf ⟨x', hx'⟩ with hP'def
  have eP : hU.fromSpec P = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have eP' : hU.fromSpec P' = x' := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have hsp : P ⤳ P' := by
    exact hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 (by rw [eP, eP']; exact hxx')
  have hle : P.asIdeal ≤ P'.asIdeal := (PrimeSpectrum.le_iff_specializes P P').mpr hsp
  have sq : Spec.map (f.app V) ≫ hV.fromSpec = hU.fromSpec ≫ f := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
  have img : ∀ Q : Spec Γ(X, f ⁻¹ᵁ V), hV.fromSpec (Spec.map (f.app V) Q) = f (hU.fromSpec Q) :=
    fun Q => (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => m Q) sq).trans (Scheme.Hom.comp_apply _ _ _))
  have hc : Spec.map (f.app V) P = Spec.map (f.app V) P' := by
    apply hV.fromSpec.isOpenEmbedding.injective
    exact (img P).trans ((congrArg f eP).trans (hf.trans ((congrArg f eP').symm.trans (img P').symm)))
  have hc' : P.asIdeal.comap (f.app V).hom = P'.asIdeal.comap (f.app V).hom :=
    congrArg PrimeSpectrum.asIdeal hc
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩
  have heq : P.asIdeal = P'.asIdeal := by
    by_contra hne
    have hlt := Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) (lt_of_le_of_ne hle hne)
    exact (ne_of_lt hlt) hc'
  have : P = P' := PrimeSpectrum.ext heq
  rw [← eP, ← eP', this]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_ext_of_apply_eq {T : Scheme.{0}} (K Ω : Type) [Field K] [Field Ω]
    (a : Sp K ⟶ T) (b : Sp Ω ⟶ T)
    (u : Sp K) (v : Sp Ω) (e : a u = b v) :
    ∃ (L : Type) (_ : Field L) (j₁ : K →+* L) (j₂ : Ω →+* L), spMap j₁ ≫ a = spMap j₂ ≫ b := by
  obtain ⟨⟨s₁, φ₁⟩, e₁⟩ := (Scheme.SpecToEquivOfField K T).symm.surjective a
  obtain ⟨⟨s₂, φ₂⟩, e₂⟩ := (Scheme.SpecToEquivOfField Ω T).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at e₁ e₂
  have hs : s₁ = s₂ := by
    rw [← e₁, ← e₂] at e
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
      Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hs
  obtain ⟨L, _, j₁, j₂, hj⟩ := GlobalTheory.exists_common_field_extension (T.residueField s₁) K Ω φ₁.hom φ₂.hom
  refine ⟨L, inferInstance, j₁, j₂, ?_⟩
  rw [← e₁, ← e₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext1
  exact hj

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem universallyInjective_of_fieldPoints' {G P : Scheme.{0}} (h : G ⟶ P)
    (H : ∀ (K : Type) [Field K] (z z' : Sp K ⟶ G), z ≫ h = z' ≫ h → z = z') :
    UniversallyInjective h := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro x
  let w := (Limits.pullback h h).fromSpecResidueField x
  have e : w ≫ Limits.pullback.fst h h = w ≫ Limits.pullback.snd h h :=
    H ((Limits.pullback h h).residueField x) _ _ (by
      simp only [Category.assoc, Limits.pullback.condition])
  have e2 : (w ≫ Limits.pullback.fst h h) ≫ Limits.pullback.diagonal h = w := by
    apply Limits.pullback.hom_ext
    · simp
    · simp [e]
  let pt : Spec ((Limits.pullback h h).residueField x) := IsLocalRing.closedPoint _
  refine ⟨(w ≫ Limits.pullback.fst h h) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, e2, Scheme.fromSpecResidueField_apply]

theorem isIso_of_isIso_fibres : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → (∀ s : T, ∃ (Ω : Type) (_ : Field Ω) (x : Sp Ω ⟶ T), s ∈ Set.range x ∧ IsIso (pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp))) → IsIso h := by
  intro T X Z p q h hh hp hq H
  apply GlobalTheory.T.isIso_of_etale_of_surjective_of_universallyInjective' X Z h
  ·
    have hloc : ∀ z : X, ∃ V : X.Opens, z ∈ V ∧ Etale (V.ι ≫ h) := by
      intro z
      obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H (p z)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z t ht.symm
      have hE : Etale ((⊤ : (pullback p x).Opens).ι ≫
          pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) := inferInstance
      obtain ⟨V, hV, hVe⟩ := GlobalTheory.T.etale_near_point_of_etale_on_fibre_smooth T X Z p q h hh hp hq Ω x ⊤ w trivial hE
      exact ⟨V, hw ▸ hV, hVe⟩
    choose V hV hVe using hloc
    have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) V ?_ hVe
    exact top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hV z⟩
  ·
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H (q y)
    obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := x) y t ht.symm
    let m := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)
    refine ⟨pullback.fst p x (inv m v), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.lift_fst (f := q) (g := x) (pullback.fst p x ≫ h)
      (pullback.snd p x ≫ 𝟙 _) (by simp [hh, pullback.condition]), Scheme.Hom.comp_apply]
    change pullback.fst q x (m (inv m v)) = y
    rw [← Scheme.Hom.comp_apply m, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
    exact hv
  ·
    refine universallyInjective_of_fieldPoints' h fun K _ z z' hz => ?_
    let u : Sp K := IsLocalRing.closedPoint K
    obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H ((z ≫ p) u)
    obtain ⟨L, _, j₁, j₂, hj⟩ := exists_common_ext_of_apply_eq K Ω (z ≫ p) x u t ht.symm
    have hj' : spMap j₁ ≫ z' ≫ p = spMap j₂ ≫ x := by
      rw [← hh, ← Category.assoc z', ← hz, Category.assoc, hh, hj]
    let m := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)
    let a := pullback.lift (f := p) (g := x) (spMap j₁ ≫ z) (spMap j₂) (by rw [Category.assoc, hj])
    let a' := pullback.lift (f := p) (g := x) (spMap j₁ ≫ z') (spMap j₂) (by rw [Category.assoc, hj'])
    have haa : a ≫ m = a' ≫ m := by
      apply pullback.hom_ext
      · simp only [m, a, a', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hz]
      · simp only [m, a, a', pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id]
    have haa' : a = a' := (cancel_mono m).1 haa
    have := congrArg (· ≫ pullback.fst p x) haa'
    simp only [a, a', pullback.lift_fst] at this
    exact GlobalTheory.Mum.spMap_field_cancel K L j₁ X z z' this

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamTorsion

theorem one_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_of_isGrpPullback h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

end GlobalTheory.FamTorsion
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem mem_subfield_of_forall_ringEquiv_fixed_of_isAlgClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ x : K,
      (∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ x = x) → x ∈ k₀ := by
  intro K _ _ k₀ hk₀ x hfix
  by_contra hx
  have htr : Transcendental k₀ x := by
    intro halg
    have hint : IsIntegral k₀ x := halg.isIntegral
    have hdeg : (minpoly k₀ x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint)
    obtain ⟨r, hr⟩ := minpoly.mem_range_of_degree_eq_one k₀ x hdeg
    apply hx
    rw [← hr]
    exact r.2
  obtain ⟨σ, hσk, hσx⟩ := GlobalTheory.FixedRoots.exists_ringEquiv_add_one k₀ x htr
  have h := hfix σ hσk
  rw [hσx] at h
  simp at h

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteClosedDvr

theorem exists_complete_dvr_isAlgClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  intro V _ _ _ _ _ _
  obtain ⟨D, _, _, _, φ, hac, hinj, hc⟩ := GlobalTheory.UnifProperChar.exists_dvr_centre V (maximalIdeal V)
  have : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 5).mpr hc
  have hb := AdicCompletion.residueField_map_bijective_of_fg (R := D)
    (maximalIdeal D).fg_of_isNoetherianRing
  refine ⟨AdicCompletion (maximalIdeal D) D, inferInstance, inferInstance, inferInstance,
    (algebraMap D _).comp φ, inferInstance, ?_,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).1,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).2⟩
  exact IsAlgClosed.of_ringEquiv (ResidueField D) _ (RingEquiv.ofBijective _ hb)

end GlobalTheory.CompleteClosedDvr
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.finite_maximal_ideals_containing_natCast' : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite := by
  first | exact @GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast | exact GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast | (intros; apply GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast <;> assumption)
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  first | exact @GlobalTheory.sep_one_mod_maximal_mem_others | exact GlobalTheory.sep_one_mod_maximal_mem_others | (intros; apply GlobalTheory.sep_one_mod_maximal_mem_others <;> assumption)
end
end
