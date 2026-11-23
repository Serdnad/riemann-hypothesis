module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.FinrankComp

theorem finrank_eq_mul_of_rankAtStalk (K S T : Type*) [Field K] [CommRing S] [AddCommGroup T]
    [Algebra K S] [Module S T] [Module K T] [IsScalarTower K S T] [Module.Finite K S]
    [Module.Finite S T] [Module.Flat S T] (d : ℕ)
    (h : ∀ p : PrimeSpectrum S, Module.rankAtStalk T p = d) :
    Module.finrank K T = d * Module.finrank K S := by
  have : IsArtinianRing S := IsArtinianRing.of_finite K S
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq S T d
    (fun P => by
      have := P.isMaximal
      letI := Ideal.Quotient.field P.asIdeal
      have h1 := Module.rankAtStalk_baseChange (R := S) (M := T) (S := S ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, h] at h1
      exact h1)
  rw [(b.equivFun.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_comp_field {X Y : Scheme.{0}} (K : CommRingCat.{0}) (hK : IsField K)
    (φ : X ⟶ Y) (ψ : Y ⟶ Spec K) [IsFinite φ] [Flat φ] [IsFinite ψ] [Flat ψ] (d : ℕ)
    (h : ∀ y, φ.finrank y = d) (z : Spec K) : (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  wlog hY : ∃ S, Y = Spec S generalizing X Y
  · have _ : IsAffine Y := isAffine_of_isAffineHom ψ
    have := this (φ ≫ Y.isoSpec.hom) (Y.isoSpec.inv ≫ ψ) (fun y => by
      rw [← h (Y.isoSpec.inv y)]
      exact Scheme.Hom.finrank_of_isPullback (𝟙 X) _ φ Y.isoSpec.inv
        (IsPullback.of_horiz_isIso ⟨by simp⟩) y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨S, rfl⟩ := hY
  wlog hX : ∃ T, X = Spec T generalizing X
  · have _ : IsAffine X := isAffine_of_isAffineHom φ
    have := this (X.isoSpec.inv ≫ φ) (fun y => by simpa using h y) ⟨_, rfl⟩
    simpa using this
  obtain ⟨T, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective ψ
  obtain ⟨g, rfl⟩ := Spec.map_surjective φ
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  rename_i hf1 hf2 hg1 hg2
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank (f := f ≫ g) (hg1.comp hf1) (hf2.comp hg2),
    Scheme.Hom.finrank_SpecMap_eq_finrank hf1 hf2]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank hg1 hg2] at h
  letI := hK.toField
  algebraize [f.hom, g.hom, (f ≫ g).hom]
  rw [← RingHom.algebraMap_toAlgebra g.hom, RingHom.finrank_algebraMap] at h
  rw [← RingHom.algebraMap_toAlgebra f.hom, ← RingHom.algebraMap_toAlgebra (f ≫ g).hom,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap]
  have : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq' rfl
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  exact finrank_eq_mul_of_rankAtStalk K S T d h

theorem finrank_comp_of_const {X Y Z : Scheme.{0}} (φ : X ⟶ Y) (ψ : Y ⟶ Z) [IsFinite φ] [Flat φ]
    [IsFinite ψ] [Flat ψ] (d : ℕ) (h : ∀ y, φ.finrank y = d) (z : Z) :
    (φ ≫ ψ).finrank z = d * ψ.finrank z := by
  let i := Z.fromSpecResidueField z
  let pt : Spec (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  have hz : i pt = z := Scheme.fromSpecResidueField_apply z pt
  have hp := (IsPullback.of_hasPullback φ (pullback.fst ψ i)).paste_vert
    (IsPullback.of_hasPullback ψ i)
  rw [← hz, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp pt,
    ← Scheme.Hom.finrank_pullback_snd ψ i pt]
  exact finrank_comp_field _ (Field.toIsField _) _ _ d
    (fun y => by rw [Scheme.Hom.finrank_pullback_snd, h]) pt

end GlobalTheory.FinrankComp
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem universallyClosed_of_closed_cover_in_universallyClosed :
    ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y),
      UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) →
        π '' T = Set.univ → UniversallyClosed f := by
  intro S X Y P f π q s T hs hq hcomm hT hqT hπT
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)
  have hrange : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hcl : IsClosedImmersion (I.subschemeι ≫ q) := by
    refine .of_isPreimmersion _ ?_
    have : Set.range (I.subschemeι ≫ q) = q '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [this]; exact hqT
  have : UniversallyClosed ((I.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc]
    infer_instance
  have : Surjective (I.subschemeι ≫ π) := by
    constructor
    have : Set.range (I.subschemeι ≫ π) = π '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [← Set.range_eq_univ, this]; exact hπT
  exact UniversallyClosed.of_comp_surjective (I.subschemeι ≫ π) f

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

theorem normalization_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra;
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V ''
        (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by
  classical
  set B := f.normalizationDiagram.obj (Opposite.op V.1) with hB
  set ι := f.normalizationOpenCover.f V with hι
  set j := f.toNormalization with hj
  have key : ∀ b : B, (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j →
      letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
      Algebra.FiniteType Γ(X, V.1) (Localization.Away b) := by
    intro b hb
    letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
    let g : Spec (.of (Localization.Away b)) ⟶ Spec B :=
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away b)))
    have hg : Set.range (g ≫ ι) ⊆ Set.range j := by
      rintro _ ⟨z, rfl⟩
      apply hb
      have : g z ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this
    let h := IsOpenImmersion.lift j (g ≫ ι) hg
    have hh : h ≫ j = g ≫ ι := IsOpenImmersion.lift_fac _ _ _
    haveI : LocallyOfFiniteType (h ≫ j) := by rw [hh]; infer_instance
    haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h j
    have e : h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away b))) ≫
        V.2.fromSpec := by
      rw [← f.toNormalization_fromNormalization, reassoc_of% hh, hι, f.ι_fromNormalization,
        ← Spec.map_comp_assoc]
      congr 2
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b))) ≫ V.2.fromSpec) := by
      rw [← e]; infer_instance
    haveI := locallyOfFiniteType_of_comp (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V.1) (Localization.Away b)))) V.2.fromSpec
    have := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
    exact RingHom.finiteType_algebraMap.mp this
  have hcov : ∀ x : U, f x ∈ V.1 → ∃ b : B,
      (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j ∧
        j x ∈ ι '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
    intro x hx
    have hx' : j x ∈ Set.range ι := by
      have h1 : j x ∈ f.fromNormalization ⁻¹ᵁ V.1 := by
        show f.fromNormalization (j x) ∈ V.1
        rw [← Scheme.Hom.comp_apply, hj, f.toNormalization_fromNormalization]
        exact hx
      rw [f.fromNormalization_preimage V] at h1
      exact h1
    obtain ⟨y, hy⟩ := hx'
    have hO : IsOpen (ι ⁻¹' Set.range j) := j.isOpenEmbedding.isOpen_range.preimage ι.continuous
    obtain ⟨_, ⟨b, rfl⟩, hyb, hbO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show y ∈ ι ⁻¹' Set.range j from ⟨x, hy.symm⟩) hO
    exact ⟨b, hbO, y, hyb, hy⟩
  have hK : IsCompact (f ⁻¹' (V.1 : Set X)) := f.isCompact_preimage V.2.isCompact
  let T := {b : B // (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ ι ⁻¹' Set.range j}
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun b : T => j ⁻¹' (ι '' (PrimeSpectrum.basicOpen b.1 : Set (PrimeSpectrum B))))
    (fun b => (ι.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen b.1).2).preimage
      j.continuous)
    (by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := hcov x hx
      exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hb
    exact key b'.1 b'.2
  · intro x hx
    obtain ⟨b, hbt, hxb⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact ⟨b.1, Finset.mem_image_of_mem _ hbt, hxb⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine
    (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens)
    (h : ∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) :
    IsSchemeTheoreticallyDominant W.ι := by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := X.isBasis_affineOpens.isOpenCover_mem_and_le
    (T.isBasis_affineOpens.isOpenCover.comap p.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U ↦ ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨U, ⟨V, hV⟩⟩, hU, hUV : U ≤ p ⁻¹ᵁ V⟩
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
  intro b hb
  have hb' : W.ι.app U b = 0 := W.ι.ideal_ker_le ⟨U, hU⟩ hb
  refine h U V hU hV hUV b fun x hx hxW ↦ ?_
  have h1 := Scheme.Hom.germ_stalkMap_apply W.ι U ⟨x, hxW⟩ hx b
  rw [hb', map_zero] at h1
  let y : W.toScheme := ⟨x, hxW⟩
  have hiso : IsIso (W.ι.stalkMap y) := inferInstance
  have hinj : Function.Injective (W.ι.stalkMap y) :=
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap y)).1
  exact hinj (h1.trans (map_zero _).symm)

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

namespace GlobalTheory.SepAffInf

theorem isAffineOpen_inf_of_le_preimage {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h]
    (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens)
    (h₁ : Ω₁.1 ≤ h ⁻¹ᵁ U.1) (h₂ : Ω₂.1 ≤ h ⁻¹ᵁ U.1) : IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by
  haveI : IsAffine U.1 := U.2
  haveI : (h ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from (h ∣_ U.1)]
    infer_instance
  have key : ∀ Ω : Z.Opens, Ω ≤ h ⁻¹ᵁ U.1 →
      (h ⁻¹ᵁ U.1).ι ''ᵁ ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω) = Ω := by
    intro Ω hΩ
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hΩ
  have a₁ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₁.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₁]
    exact Ω₁.2
  have a₂ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₂.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₂]
    exact Ω₂.2
  have a : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ (Ω₁.1 ⊓ Ω₂.1)) := a₁.inf a₂
  rw [← key _ (inf_le_left.trans h₁)]
  exact a.image_of_isOpenImmersion _

end GlobalTheory.SepAffInf
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_prime_comap_bot_lies_over_genericPoint :
    ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V →
      ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime),
        P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  intro X Y _ π V hV hW P hP h
  have e := IsAffineOpen.SpecMap_appLE_fromSpec π hV hW le_rfl
  have e2 : π (hW.fromSpec ⟨P, hP⟩) =
      hV.fromSpec (Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩) := by
    have := congrArg (fun f : Spec Γ(Y, π ⁻¹ᵁ V) ⟶ X => f (⟨P, hP⟩ : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V))) e
    exact this.symm
  set q : Spec Γ(X, V) := Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩ with hqdef
  have hq : q.asIdeal = ⊥ := by
    rw [← h, Scheme.Hom.app_eq_appLE]
    rfl
  have hne : Nonempty V := ⟨⟨hV.fromSpec q, hV.range_fromSpec.subset ⟨q, rfl⟩⟩⟩
  have hgen : q = genericPoint (Spec Γ(X, V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  rw [e2, hgen, genericPoint_eq_of_isOpenImmersion]

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry
namespace GlobalTheory

theorem appLE_injective_of_genericPoint_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) (hπ : π (genericPoint Y) = genericPoint X) {U : X.Opens} {V : Y.Opens}
    (hV : (V : Set Y).Nonempty) (h : V ≤ π ⁻¹ᵁ U) :
    Function.Injective (π.appLE U V h).hom := by
  have hy : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hxU : π (genericPoint Y) ∈ U := h hy
  have hF : IsField (X.presheaf.stalk (π (genericPoint Y))) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by rw [hπ]; simp [irreducibleComponents_eq_singleton])
  letI := hF.toField
  have key : ∀ s, (π.stalkMap (genericPoint Y)).hom (X.presheaf.germ U _ hxU s) =
      Y.presheaf.germ V (genericPoint Y) hy ((π.appLE U V h).hom s) := by
    intro s
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp [Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]
  intro s t hst
  apply germ_injective_of_isIntegral X _ hxU
  apply (π.stalkMap (genericPoint Y)).hom.injective
  rw [key, key, hst]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem inv_mem_connectedComponentIn_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] (y : G.left)
    (hy : y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) :
    (ι[G]).left y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hw : ∀ z : G.left, G.hom ((ι[G]).left z) = G.hom z := by
    intro z
    have h := Over.w (ι[G])
    rw [← Scheme.Hom.comp_apply, h]
  have hη : ∀ s : S, (ι[G]).left ((η[G]).left s) = (η[G]).left s := by
    intro s
    have h : (η[G] ≫ ι[G]).left = (η[G]).left := by rw [GrpObj.one_inv]
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
  rw [hw]
  set F := G.hom ⁻¹' {G.hom y}
  set e := (η[G]).left (G.hom y)
  have heF : e ∈ F := (connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩)
  have hsub : (ι[G]).left '' connectedComponentIn F e ⊆ connectedComponentIn F e := by
    refine (isPreconnected_connectedComponentIn.image _ (ι[G]).left.continuous.continuousOn).subset_connectedComponentIn
      ⟨e, mem_connectedComponentIn heF, hη _⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzF : z ∈ F := connectedComponentIn_subset _ _ hz
    simp only [F, Set.mem_preimage, Set.mem_singleton_iff] at hzF ⊢
    rw [hw, hzF]
  exact hsub ⟨y, hy, rfl⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isPullback_comp_mono_right_of_isPullback {𝒞 : Type*} [Category 𝒞] {P X Y Z Z' : 𝒞} {fst : P ⟶ X} {snd : P ⟶ Y}
    {a : X ⟶ Z} {b : Y ⟶ Z} (m : Z ⟶ Z') [Mono m] (h : IsPullback fst snd a b) :
    IsPullback fst snd (a ≫ m) (b ≫ m) :=
  ⟨⟨by rw [← Category.assoc, h.w, Category.assoc]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift c.fst c.snd (by rw [← cancel_mono m]; simpa using c.condition))
    (fun c ↦ h.lift_fst _ _ _) (fun c ↦ h.lift_snd _ _ _)
    (fun c n h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

theorem preirreducibleSpace_tensor_of_pullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
      (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k]
      [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom →
      PreirreducibleSpace ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  intro X S f V W h hV hW k _ _ _ hA hP
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, V) k Γ(X, W))).flip
  have sq2 := sq.of_iso (fst' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      hW.isoSpec.inv) (snd' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (f' := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)))
    (Iso.refl _) hW.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
  have sq3 := isPullback_comp_mono_right_of_isPullback hV.fromSpec sq2
  have e : (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W)))) ≫
      hV.fromSpec = W.ι ≫ f := by
    rw [hA, CommRingCat.ofHom_hom, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hW h,
      ← hW.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [e] at sq3
  let φ := sq3.isoPullback
  have hsurj : Function.Surjective (Scheme.homeoOfIso φ.symm) := (Scheme.homeoOfIso φ.symm).surjective
  refine ⟨?_⟩
  have := (PreirreducibleSpace.isPreirreducible_univ (X := ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)))).image
    (Scheme.homeoOfIso φ.symm) (Scheme.homeoOfIso φ.symm).continuous.continuousOn
  rw [Set.image_univ_of_surjective hsurj] at this
  exact this

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_left_isPullback_snd (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T) :
    IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  have hw : (U ◁ f).left ≫ (snd U T).left = (snd U T').left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  refine IsPullback.of_right (h₁₂ := (fst U T).left) (h₂₂ := T.hom) (v₁₃ := U.hom) ?_ hw ?_
  · have h1 : (U ◁ f).left ≫ (fst U T).left = (fst U T').left := by
      rw [← Over.comp_left, whiskerLeft_fst]
    have h2 : f.left ≫ T.hom = T'.hom := Over.w f
    rw [h1, h2, Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T'.hom
  · rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback U.hom T.hom

end GlobalTheory
end
