module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle125
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.DualNumber
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace QuotModel

theorem isProjOver_comp_spMap {O O' : Type} [CommRing O] [CommRing O'] (b : O' →+* O) {X : Scheme.{0}}
    (s : X ⟶ Sp O) (hb : IsFinite (spMap b)) (hs : IsProjOver s) : IsProjOver (s ≫ spMap b) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N b
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N b) := MorphismProperty.of_isPullback P.flip hb
  have := GlobalTheory.T.isProjOver_comp_finite O' (PSpace O' N) X (i ≫ GlobalTheory.ProjSpace.baseChange N b) (PSpace.str O' N) inferInstance
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  rwa [Category.assoc, P.w, ← Category.assoc] at this

theorem isPullback_fractionField {O O' F F' : Type} [CommRing O] [CommRing O'] [Field F] [Field F'] [IsDomain O]
    [Algebra O F] [IsFractionRing O F] [Algebra O' F'] [IsFractionRing O' F'] (b : O' →+* O) (k : F' →+* F)
    (h : (algebraMap O F).comp b = k.comp (algebraMap O' F')) (hb : IsFinite (spMap b)) :
    Function.Injective b ∧
      IsPullback (spMap (algebraMap O F)) (spMap k) (spMap b) (spMap (algebraMap O' F')) := by
  have hinj : Function.Injective b := by
    have : Function.Injective ((algebraMap O F).comp b) := by
      rw [h]; exact k.injective.comp (IsFractionRing.injective O' F')
    exact Function.Injective.of_comp (f := algebraMap O F) this
  refine ⟨hinj, ?_⟩
  have hfin : b.Finite := (IsFinite.SpecMap_iff _).mp hb
  letI := b.toAlgebra
  letI := ((algebraMap O F).comp b).toAlgebra
  have : IsScalarTower O' O F := .of_algebraMap_eq' rfl
  have : Module.Finite O' O := hfin
  have : FaithfulSMul O' O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Nontrivial O' := b.domain_nontrivial
  have : Algebra.IsAlgebraic O' O := inferInstance
  have h1 : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors O')) F := inferInstance
  have h2 : IsLocalization ((nonZeroDivisors O').map b) F := h1
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization b k h.symm (nonZeroDivisors O'))

theorem exists_isOpenImmersion_quotient (Γ : Type) [Group Γ] [Finite Γ] (Y Y' U U' : Scheme.{0}) (τ : Γ →* Aut Y)
    (ρ₀ : Γ →* Aut U) (φ : Y ⟶ Y') (r : U ⟶ U') (j : U ⟶ Y) [IsOpenImmersion j]
    (hφ : (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom))
    (hr : (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom))
    (hj : ∀ g, j ≫ (τ g).asIso.hom = (ρ₀ g).asIso.hom ≫ j) :
    ∃ j' : U' ⟶ Y', IsOpenImmersion j' ∧ r ≫ j' = j ≫ φ ∧ φ ⁻¹' Set.range j' = Set.range j := by
  have hst : ∀ g (y : Y), y ∈ j.opensRange → (τ g).asIso.hom y ∈ j.opensRange := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨(ρ₀ g).asIso.hom u, by rw [← Scheme.Hom.comp_apply, ← hj, Scheme.Hom.comp_apply]⟩
  obtain ⟨V, hV⟩ := (quotient_isIntegral_surjective_orbits Γ Y Y' τ φ hφ).2.2.2.2 j.opensRange (by
    intro g
    ext y
    refine ⟨fun h => ?_, hst g y⟩
    have h1 := hst g⁻¹ _ h
    have e : (τ g).asIso.hom ≫ (τ g⁻¹).asIso.hom = 𝟙 Y := by
      rw [map_inv]; exact (τ g).asIso.hom_inv_id
    rwa [← Scheme.Hom.comp_apply, e] at h1)
  let φ' : U ⟶ V := IsOpenImmersion.lift V.ι (j ≫ φ) (by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : j u ∈ φ ⁻¹ᵁ V := by rw [hV]; exact ⟨u, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact this)
  have e : φ' ≫ V.ι = j ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback φ' j V.ι φ := IsOpenImmersion.isPullback _ _ _ _ e.symm (by
    rw [Scheme.Opens.opensRange_ι, hV])
  have hφ' := (quotient_flat_baseChange Γ Y Y' U V τ φ φ' j V.ι hφ P inferInstance).2 ρ₀ fun g =>
    ⟨by rw [← cancel_mono V.ι, Category.assoc, e, ← Category.assoc, ← hj, Category.assoc, hφ.2.1], (hj g).symm⟩
  obtain ⟨a, ha, -⟩ := quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr V φ' hφ'.2.1
  obtain ⟨a', ha', -⟩ := quotient_existsUnique_comp_eq Γ U V ρ₀ φ' hφ' U' r hr.2.1
  have : IsIso a := ⟨a', (quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr U' r hr.2.1).unique
    (by rw [← Category.assoc, ha, ha']) (Category.comp_id _),
    (quotient_existsUnique_comp_eq Γ U V ρ₀ φ' hφ' V φ' hφ'.2.1).unique
    (by rw [← Category.assoc, ha', ha]) (Category.comp_id _)⟩
  refine ⟨a ≫ V.ι, inferInstance, by rw [← Category.assoc, ha, e], ?_⟩
  have hr' : Set.range (a ≫ V.ι) = V := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, a.surjective.range_comp, Scheme.Opens.range_ι]
  rw [hr']
  exact congrArg SetLike.coe hV

end QuotModel

theorem exists_quotient_model_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (β' : O' →+* F') (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ρ₀ : Γ →* Aut U) (ρ : Γ →* Aut C.X), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → (∀ g, C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j) → ∃ (X' : Scheme.{0}) (π : C.X ⟶ X') (s' : X' ⟶ Sp O') (jQ : U' ⟶ pullback s' (spMap β')), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(C.X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) ∧ IsFinite π ∧ π ≫ s' = C.s ≫ spMap b ∧ Geo.Tor.IsNormalScheme X' ∧ IsProjOver s' ∧ Flat s' ∧ jQ ≫ pullback.snd _ _ = c' ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ r ≫ jQ ≫ pullback.fst _ _ = C.j ≫ π ∧ ∀ x : C.X, π x ∈ Set.range (jQ ≫ pullback.fst s' (spMap β')) ↔ x ∈ Set.range C.j := by
  intro E _ _ _ H U F O _ _ c t β Γ _ _ C U' F' O' _ _ c' β' b k r ρ₀ ρ hβ hβ' hbk hb hrc hr hρ
  obtain ⟨⟨_, _⟩, -, hF⟩ := hβ
  obtain ⟨⟨_, _⟩, -, hF'⟩ := hβ'
  letI := β.toAlgebra
  letI := β'.toAlgebra
  obtain ⟨hN, hC, hS, hpre, hfl, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hdom' : IsDominant C.j := hdom
  obtain ⟨hinj, Pb⟩ := QuotModel.isPullback_fractionField (F := F) (F' := F') b k hbk hb
  replace Pb : IsPullback (spMap β) (spMap k) (spMap b) (spMap β') := Pb
  have hred : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s ≫ spMap b = r ≫ c' ≫ spMap β' := by
    rw [Cpt.j, Category.assoc, pullback.condition_assoc, ← Category.assoc, C.jQ_over, Pb.w, reassoc_of% hrc]
  have hinv : ∀ g, (ρ g).asIso.hom ≫ C.s ≫ spMap b = C.s ≫ spMap b := fun g =>
    ext_of_isDominant C.j (by rw [← Category.assoc, hρ, Category.assoc, hjs, ← Category.assoc, hr.2.1])
  have hproj := QuotModel.isProjOver_comp_spMap b C.s hb C.proj
  have hq : IsQProjOver C.s := by
    obtain ⟨N, i, hi, e⟩ := C.proj
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨X', π, hπ⟩ := exists_quotient_of_finite_group Γ C.X ρ fun x => by
    obtain ⟨V, hV, h, -⟩ := exists_isAffineOpen_le_of_isQProjOver O C.X C.s hq
      (Set.range fun g => (ρ g).asIso.hom x) ⊤ (Set.finite_range _) (Set.subset_univ _)
    exact ⟨V, hV, fun g => h ⟨g, rfl⟩⟩
  obtain ⟨s', hs', -⟩ := quotient_existsUnique_comp_eq Γ C.X X' ρ π hπ _ _ hinv
  have hprop : IsProper (π ≫ s') := by
    obtain ⟨N, i, hi, e⟩ := hproj
    have := isProper_str O' N
    rw [hs', ← e]; infer_instance
  have hfin := (GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties Γ C.X X' ρ π hπ _ s' inferInstance).1
  obtain ⟨-, hnorm, hflat⟩ := GlobalTheory.T.quotient_isReduced_isNormal_flat_of_invariant_sections Γ C.X X' ρ π hπ
  have hbf : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    letI := b.toAlgebra
    have : FaithfulSMul O' O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat O' O)
  have hs'f : Flat s' := hflat O' s' (by rw [hs']; have := C.flat; infer_instance)
  have hβf : Flat (spMap β') := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F' (nonZeroDivisors O'))
  have hβm : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  let p := pullback.fst C.s (spMap β)
  let p' := pullback.fst s' (spMap β')
  have hpm : IsPreimmersion p :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβm
  let φ : pullback C.s (spMap β) ⟶ pullback s' (spMap β') :=
    pullback.lift (p ≫ π) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, hs', pullback.condition_assoc, Pb.w, Category.assoc])
  have e1 : φ ≫ p' = p ≫ π := pullback.lift_fst _ _ _
  have e2 : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have P : IsPullback φ p p' π := by
    refine IsPullback.of_right ?_ e1 (IsPullback.of_hasPullback s' (spMap β')).flip
    rw [e2, hs']
    exact ((IsPullback.of_hasPullback C.s (spMap β)).paste_vert Pb).flip
  obtain ⟨⟨τ, hτ⟩, hφ⟩ := quotient_flat_baseChange Γ C.X X' _ _ ρ π φ p p' hπ P inferInstance
  replace hφ := hφ τ hτ
  have := C.jQ_open
  obtain ⟨j', hj', e3, e4⟩ := QuotModel.exists_isOpenImmersion_quotient Γ _ _ U U' τ ρ₀ φ r C.jQ hφ hr fun g => by
    rw [← cancel_mono p, Category.assoc, (hτ g).2, ← Category.assoc, Category.assoc (ρ₀ g).asIso.hom]
    exact hρ g
  have e5 : r ≫ j' ≫ p' = C.j ≫ π := by
    rw [reassoc_of% e3, e1, Cpt.j, Category.assoc]
  refine ⟨X', π, s', j', hπ, hfin, hs', hnorm hN C.normal, GlobalTheory.T.isProjOver_finite_group_quotient Γ C.X X' ρ π hπ O' s' (hs' ▸ hproj), hs'f,
    ?_, hj', ?_, e5, fun x => ⟨?_, ?_⟩⟩
  · refine (quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr _ (r ≫ c') fun g => ?_).unique ?_ rfl
    · rw [← Category.assoc, hr.2.1]
    · rw [reassoc_of% e3, e2, ← Category.assoc, C.jQ_over, hrc]
  · have hsurj := (quotient_isIntegral_surjective_orbits Γ _ _ τ φ hφ).2.1
    have hd : Dense (φ '' Set.range C.jQ) := φ.surjective.denseRange.dense_image φ.continuous C.jQ_dense
    exact hd.mono (by rw [← e4]; exact Set.image_preimage_subset _ _)
  · rintro ⟨u, hu⟩
    obtain ⟨y, hy, rfl⟩ := Scheme.exists_preimage_of_isPullback P (j' u) x
      (by rw [← hu, Scheme.Hom.comp_apply])
    have : y ∈ Set.range C.jQ := by rw [← e4]; exact ⟨u, hy.symm⟩
    obtain ⟨v, rfl⟩ := this
    exact ⟨v, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, rfl⟩
    exact ⟨r u, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e5]⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.SymRigid

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem sym_iff_cls {L : LB A.left} (hL : L.IsLB) : Out.Sym A L ↔ ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) = pull (A.hom ⁻¹ᵁ U).ι (cls L hL) := by
  refine forall_congr' fun s => exists_congr fun U => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two]
  change (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
    (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = 0 ↔ _
  rw [one_zsmul, neg_one_zsmul, add_neg_eq_zero]

theorem pull_restrict {U V : S.Opens} (h : V ≤ U) {c : Pic A.left}
    (e : pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ U).ι c) :
    pull ((A.hom ⁻¹ᵁ V).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ V).ι c := by
  have hle : A.hom ⁻¹ᵁ V ≤ A.hom ⁻¹ᵁ U := fun _ hx => h hx
  rw [← Scheme.homOfLE_ι A.left hle, Category.assoc, pull_comp, e, ← pull_comp]

theorem sym_of_cls_eq_sub {L M Q : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (hQ : Q.IsLB)
    (e : cls Q hQ = cls L hL - cls M hM) (sL : Out.Sym A L) (sM : Out.Sym A M) : Out.Sym A Q := by
  refine (sym_iff_cls hQ).2 fun s => ?_
  obtain ⟨U, hU, eU⟩ := (sym_iff_cls hL).1 sL s
  obtain ⟨V, hV, eV⟩ := (sym_iff_cls hM).1 sM s
  refine ⟨U ⊓ V, ⟨hU, hV⟩, ?_⟩
  rw [e, map_sub, map_sub, pull_restrict inf_le_left eU, pull_restrict inf_le_right eV]

theorem lbIso_pull_of_isConst : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ M : LB A'.left, M.IsLB → Out.Sym A' M → LBIso P₀.L (M.pull j) → LBIso M (P₀.L.pull ρ) := by
  intro laws P₀ u Hm χ hu A' _ ρ j hc M hM sM H
  have hL := pull_isLB P₀.isLB ρ
  have hQ : (LB.div (P₀.L.pull ρ) M).IsLB := LB.isLB_div hL hM
  have e₀ : cls _ P₀.isLB = pull j (cls M hM) := (cls_eq_iff _ (pull_isLB hM j)).2 H
  have triv : ∃ t : ((LB.div (P₀.L.pull ρ) M).pull j).Gen, t.IsGen := by
    rw [← cls_eq_zero_iff (pull_isLB hQ j), cls_pull hQ, cls_div hL hM, map_sub, cls_pull P₀.isLB, ← pull_comp,
      hc.2.2, pull_id, e₀, sub_self]
  obtain ⟨Q, k, hQ', iso, hk⟩ := GlobalTheory.T.exists_lineBundle_cocycle_one_add_eps _ _ P₀.A.hom A'.hom ρ j hc.1.1 hc.2.2 hc.2.1.1.w _ hQ triv
  have e : cls Q hQ' = cls _ hL - cls M hM := ((cls_eq_iff hQ hQ').2 iso).symm.trans (cls_div hL hM hQ)
  have z := (cls_eq_zero_iff hQ').2 (GlobalTheory.T.symmetric_bundle_trivial_constant_family_dualNumber laws P₀ u Hm χ hu A' ρ j hc Q k hQ' hk
    (sym_of_cls_eq_sub hL hM hQ' e (PolBaseChange.sym_pull hc.1 P₀.sym) sM))
  exact (cls_eq_iff hM hL).1 (sub_eq_zero.1 (e.symm.trans z)).symm

end GlobalTheory.SymRigid
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory

theorem exists_locDer_top_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hpb D s hD hs
  have key : ∀ (W : X.Opens) (f : Γ(X, W)), ∃! a : Γ(P₀.A.left, m ⁻¹ᵁ W),
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
    intro W f
    refine existsUnique_section_of_locally_regular P₀ u Hm χ hu (m ⁻¹ᵁ W) (fun z => s z W f) fun z hz => ?_
    have hz' : ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ) ∈ W := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW₀, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hz' W.isOpen
    have hle' : W₀ ≤ W := hle
    obtain ⟨a, ha⟩ := GlobalTheory.T.holomorphic_lift_regular_of_periods_zero hL P₀ u Hm χ hu R x₀ X p m hp hpb D s hD hs W₀ hW₀ W₀ le_rfl (resG X hle' f)
    refine ⟨m ⁻¹ᵁ W₀, a, fun _ hy => hle' hy, (top_le_preimage_iff_mem ((u.ex z).left ≫ m) W₀).2 hzW₀, fun z' hz' => ?_⟩
    exact (ha z' hz').trans ((hs.der z').res W W₀ hle' hz' f)
  choose d hd hu' using key
  have ext : ∀ (W : X.Opens) (f : Γ(X, W)) (a : Γ(P₀.A.left, m ⁻¹ᵁ W)),
      (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f) → d W f = a :=
    fun W f a h => (hu' W f a h).symm
  refine ⟨d, ⟨fun W _ f f' => ext W _ _ fun z hz => ?_, fun W _ f f' => ext W _ _ fun z hz => ?_,
    fun W W' i _ f => ext W' _ _ fun z hz => ?_, fun W _ r => ext W _ _ fun z hz => ?_⟩⟩
  · rw [valAt'_add, hd W f z hz, hd W f' z hz, (hs.der z).add W hz]
  · rw [valAt'_add, valAt'_mul, valAt'_mul, valAt'_comp, valAt'_comp, hd W f z hz, hd W f' z hz,
      (hs.der z).mul W hz]
  · rw [(hs.der z).res W W' i hz, ← hd W f z fun _ hy => i (hz hy)]
    exact valAt'_res _ _ _ hz
  · have e : constFn p W r = resG X le_top (constFn p ⊤ r) := by
      unfold constFn
      exact (congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (V' := W) le_top (homOfLE le_top).op)).symm
    rw [e, (hs.der z).res ⊤ W le_top hz, hs.base]
    exact valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FibreEmbed

theorem mono_of_geom_points {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h₁ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y')
    (h₂ : ∀ (k : Type) [Field k] [IsAlgClosed k] (w : Sp (DualNumber k) ⟶ X),
      w ≫ f = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w ≫ f →
        w = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w) : Mono f := by
  have hu : FormallyUnramified f := TangentCrit.formallyUnramified_of_tangent f h₂
  have hs : Surjective (pullback.diagonal f) := by
    refine ((tfae_universallyInjective f).out 2 4).1 fun (k : Type) [Field k] y y' e => ?_
    let x : Sp (AlgebraicClosure k) ⟶ Sp k := spMap (algebraMap k (AlgebraicClosure k))
    have : Surjective x :=
      ⟨fun z => ⟨(default : PrimeSpectrum (AlgebraicClosure k)), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Epi x := Flat.epi_of_flat_of_surjective x
    refine (cancel_epi x).1 (h₁ _ _ _ ?_)
    rw [Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]; rfl

theorem sp_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem projRep_of_fibres : ∀ (R σ : Type) [CommRing R] [Finite σ] (X : Scheme.{0}) (s : X ⟶ Sp R) (M : LB X) (th : σ → M.Sec), M.IsLB → IsProper s → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K), ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (s' : X' ⟶ Sp K) (M' : LB X') (th' : σ → M'.Sec) (I : Ideal (MvPolynomial σ K)), IsPullback π s' s (spMap x) ∧ ProjRep I s' M' th' ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X') (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ π) w) → ProjRep (idealOf s M th (𝟙 X)) s M th := by
  intro R σ _ _ X s M th hM hs H
  obtain ⟨P, sP, MP, thP, -, hP, -⟩ := GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat R σ ⊥ 0 (by
    intro F hF e
    rw [Ideal.mem_bot] at hF
    simp [hF])
  have hPp : IsProper sP := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R σ ⊥ (Over.mk sP) MP thP hP).2.1
  obtain ⟨f, hf, -, hfc, -⟩ := GlobalTheory.T.exists_scheme_map_of_projective_coordinates R σ ⊥ P X sP s MP M thP th hP hM (by
    intro R' _ β y v hy hv
    refine ⟨?_, fun F hF => by rw [Ideal.mem_bot] at hF; simp [hF]⟩
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field m
    let K := AlgebraicClosure (R' ⧸ m)
    let φ : R' →+* K := (algebraMap (R' ⧸ m) K).comp (Ideal.Quotient.mk m)
    obtain ⟨X', π, s', M', th', I, hpb, hrep, hc⟩ := H K (φ.comp β)
    have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ hM hv).1 K φ
    have e : (spMap φ ≫ y) ≫ s = 𝟙 _ ≫ spMap (φ.comp β) := by
      rw [Category.assoc, hy, sp_comp, Category.id_comp]
    have h2 := (hrep.2.1 K (RingHom.id K) (hpb.lift _ _ e) _ (by rw [hpb.lift_snd, sp_id])
      ((hc K _ _).2 (by rw [hpb.lift_fst]; exact h1))).1
    have h3 : Ideal.span (Set.range fun i => φ (v i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      have : Ideal.Quotient.mk m (v i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span ⟨i, rfl⟩))
      simp [φ, this]
    exact bot_ne_top (h3.symm.trans h2))
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (T : Type) [CommRing T] [IsLocalRing T] (c : K →+* T)
      (x : Sp K ⟶ Sp R) (y y' : Sp T ⟶ X), y ≫ s = spMap c ≫ x → y ≫ f = y' ≫ f → y = y' := by
    intro K _ _ T _ _ c x y y' hy e
    obtain ⟨x, rfl⟩ : ∃ g : R →+* K, spMap g = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
    have hy' : y' ≫ s = spMap c ≫ spMap x := by
      rw [← hy, ← hf, ← Category.assoc, ← e, Category.assoc]
    obtain ⟨X', π, s', M', th', I, hpb, hrep, hc⟩ := H K x
    obtain ⟨v, hv⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally X M σ th hM).1 T y
    have hv' : SecCoord M th y' v := (hfc T y' v).2 (e ▸ (hfc T y v).1 hv)
    have a1 : SecCoord M' th' (hpb.lift _ _ hy) v := (hc T _ _).2 (by rw [hpb.lift_fst]; exact hv)
    have a2 : SecCoord M' th' (hpb.lift _ _ hy') v := (hc T _ _).2 (by rw [hpb.lift_fst]; exact hv')
    obtain ⟨u1, u2⟩ := hrep.2.1 T c _ v (hpb.lift_snd _ _ hy) a1
    have := (hrep.2.2 T c v u1 u2).unique ⟨hpb.lift_snd _ _ hy, a1⟩ ⟨hpb.lift_snd _ _ hy', a2⟩
    rw [← hpb.lift_fst _ _ hy, this, hpb.lift_fst]
  have : IsProper (f ≫ sP) := hf ▸ hs
  have : IsProper f := IsProper.of_comp f sP
  have hm : Mono f := by
    refine mono_of_geom_points f (fun k _ _ y y' e => key k k (RingHom.id k) (y ≫ s) y y' ?_ e)
      fun k _ _ w hw => key k (DualNumber k) (algebraMap _ _) (TangentCrit.dualPt k ≫ w ≫ s) _ _ ?_ ?_
    · rw [sp_id, Category.id_comp]
    · have := congrArg (· ≫ sP) hw
      simpa only [Category.assoc, hf] using this
    · simpa only [Category.assoc] using hw
  have hci : IsClosedImmersion f := (IsClosedImmersion.iff_isProper_and_mono f).2 ⟨‹_›, hm⟩
  have := GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme R σ ⊥ P X sP MP thP f M th hP hci hM hfc
  rwa [hf] at this

end GlobalTheory.FibreEmbed
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem level_eq_of_gLies_of_hasTh : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (S S₁ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g ((n ^ j) ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ S₁) (w : Ix g ((n ^ j) ^ 2) → K), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ c = y' ≫ c → y ≫ s₁ = y' ≫ s₁ → t₁.HasTh y w → t₁.HasTh y' w → ∀ i, y ≫ (t₁.pt i).left ≫ ψ₁ = y' ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro hL hL2 g n j J hn hodd hj o _ b S S₁ A _ L act Q c s₁ t₁ ψ₁ K _ _ y y' w hLB hG hI hc hs T T'
  obtain ⟨u, ψ, m, ⟨a₁, -, a₃⟩, l, p⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y (y ≫ s₁) hLB hG hI rfl
  obtain ⟨u', ψ', m', ⟨a₁', -, a₃'⟩, l', p'⟩ :=
    gLies_pull o g (n ^ j) J b S S₁ _ A L act Q c s₁ t₁ ψ₁ y' (y ≫ s₁) hLB hG hI hs.symm
  rw [← hc] at a₁' a₃'
  have U : u.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u _ K _ _ m).2 (by rwa [Category.id_comp])
  have U' : u'.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ u' _ K _ _ m').2 (by rwa [Category.id_comp])
  have hp := a₁.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom a₁'.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  have c₁ : IsGrpPullback u'.A u.A (𝟙 _) χ :=
    a₁.cancel (a₁'.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id])
  have c₀ : LBIso (u.L.pull χ) (L.pull ψ') :=
    l.chartPull (Geo.Tor.chartPullPull u.L χ χ rfl)
      (chartPullSame L (fun _ : PUnit => ψ') (fun _ : PUnit => ψ) (fun _ => 1) χ (fun _ => e₁.symm))
  have c₂ : LBIso u'.L (u.L.pull χ) :=
    LBIso.trans u'.isLB (pull_isLB hLB _) (pull_isLB u.isLB _) l' c₀.symm
  have c₃ : ∀ i, (u'.pt i ^ n ^ j).left ≫ χ = (u.pt i ^ n ^ j).left := fun i => by
    apply hp.hom_ext
    · rw [Category.assoc, e₁, a₃', a₃]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ U U'
  intro i
  rw [← p, ← p', ← c₅, Category.assoc, e₁]

end GlobalTheory.ZM.NearBuild
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.normalised_polarisation' : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) → ∀ M : LB P.A.left, M = cubeLB P.A ![𝟙 P.A, w] P.L → M.IsLB ∧ Out.Rigidified P.A M ∧ Out.Sym P.A M ∧ Out.RelAmple P.A M ∧ Out.KTriv P.A M ∧ LBIso (abelian₂ P.A M) (abelian₂ P.A P.L) ∧ LBIso M (cubeLB P.A ![𝟙 P.A, w] M) ∧ LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] M) := by
  first | exact @GlobalTheory.PrimNormPol.normalised_polarisation | exact GlobalTheory.PrimNormPol.normalised_polarisation | (intros; apply GlobalTheory.PrimNormPol.normalised_polarisation <;> assumption)
end
