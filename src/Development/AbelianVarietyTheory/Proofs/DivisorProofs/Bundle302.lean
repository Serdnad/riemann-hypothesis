module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle193
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.LocalStructure
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.PushoutSquare

theorem isPullback_of_forall_isPushout_app :
    ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  intro X Y S S' j p y q hS hS' hj w H
  let φ : X ⟶ pullback y q := pullback.lift j p w
  have hφ1 : φ ≫ pullback.fst y q = j := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd y q = p := pullback.lift_snd _ _ _
  suffices hiso : IsIso φ by
    exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2
  have hPb : IsPullback (pullback.fst y q) (pullback.snd y q) y q := IsPullback.of_hasPullback y q
  haveI : IsAffineHom q := inferInstance
  haveI : IsAffineHom (pullback.fst y q) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback hPb.flip inferInstance
  let U : Y.affineOpens → (pullback y q).Opens := fun V => pullback.fst y q ⁻¹ᵁ V.1
  have hU : ⨆ V, U V = ⊤ := by
    show ⨆ V : Y.affineOpens, pullback.fst y q ⁻¹ᵁ (V : Y.Opens) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  show MorphismProperty.isomorphisms Scheme φ
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro V
  have hpre : φ ⁻¹ᵁ U V = j ⁻¹ᵁ V.1 := by
    show φ ⁻¹ᵁ (pullback.fst y q ⁻¹ᵁ V.1) = j ⁻¹ᵁ V.1
    rw [← Scheme.Hom.comp_preimage, hφ1]
  have hUa : IsAffineOpen (U V) := V.2.preimage _
  have hSa : IsAffineOpen (φ ⁻¹ᵁ U V) := by rw [hpre]; exact V.2.preimage j
  haveI : IsAffine (U V).toScheme := hUa
  haveI : IsAffine (φ ⁻¹ᵁ U V).toScheme := hSa

  have P1 := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y (pullback y q) S S'
    (pullback.fst y q) (pullback.snd y q) y q hPb hS hS' V.1 V.2
  have P2 := H V.1 V.2
  let c : Γ(pullback y q, U V) ⟶ Γ(X, j ⁻¹ᵁ V.1) := φ.appLE (U V) (j ⁻¹ᵁ V.1) hpre.ge
  have key : ∀ {T : Scheme.{0}} (g j' : X ⟶ T) (hg : g = j') (A : T.Opens) (e : j' ⁻¹ᵁ A ≤ g ⁻¹ᵁ A),
      g.appLE A (j' ⁻¹ᵁ A) e = j'.appLE A (j' ⁻¹ᵁ A) le_rfl := by
    intro T g j' hg A e; subst hg; rfl
  have hc1 : (pullback.fst y q).app V.1 ≫ c = j.app V.1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
    exact key _ _ hφ1 _ _
  have hc2 : (pullback.snd y q).appLE ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (fun _ _ => trivial) ≫ c =
      p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
    refine (Scheme.Hom.appLE_comp_appLE φ (pullback.snd y q) ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (j ⁻¹ᵁ V.1)
      (fun _ _ => trivial) hpre.ge).trans ?_
    have e2 : ∀ (e : j ⁻¹ᵁ V.1 ≤ (φ ≫ pullback.snd y q) ⁻¹ᵁ ⊤),
        (φ ≫ pullback.snd y q).appLE ⊤ (j ⁻¹ᵁ V.1) e = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
      intro e
      have gen : ∀ (g : X ⟶ S') (hg : g = p) (e' : j ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ ⊤),
          g.appLE ⊤ (j ⁻¹ᵁ V.1) e' = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
        intro g hg e'; subst hg; rfl
      exact gen _ hφ2 e
    exact e2 _
  have hcE : c = (P1.isoIsPushout _ _ P2).hom := by
    apply P1.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]; exact hc1
    · rw [IsPushout.inr_isoIsPushout_hom]; exact hc2
  have hcI : IsIso c := by rw [hcE]; infer_instance
  have hTop : IsIso (φ ∣_ U V).appTop := by
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    refine (Scheme.Hom.appLE_congr φ _ (Scheme.Opens.ι_image_top (U V))
      ((Scheme.Opens.ι_image_top (φ ⁻¹ᵁ U V)).trans hpre) (fun f => IsIso f)).mpr ?_
    exact hcI
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine (φ ∣_ U V))).mpr (inferInstanceAs (IsIso (Spec.map _)))

end GlobalTheory.PushoutSquare
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support : ∀ {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced T] (g : T ⟶ Y), (∀ t, g t ∈ i.ker.support) → ∃ h : T ⟶ X, h ≫ i = g := by
  first | exact @GlobalTheory.lift_of_reduced_of_support | exact GlobalTheory.lift_of_reduced_of_support | (intros; apply GlobalTheory.lift_of_reduced_of_support <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem exists_affine_etale_surjective :
    ∀ (W : Scheme.{0}) [CompactSpace W], ∃ (V : Scheme.{0}) (f : V ⟶ W), IsAffine V ∧ Etale f ∧ Surjective f := by
  intro W _
  let 𝒰 := W.affineCover.finiteSubcover
  refine ⟨∐ 𝒰.X, Sigma.desc 𝒰.f, inferInstance, ?_, inferInstance⟩
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory


open Polynomial in
theorem exists_etale_subset_range_of_isPrime {A : Type} [CommRing A] (q : Ideal A) [q.IsPrime]
    {K : Type} [Field K] [Algebra A K] [Algebra q.ResidueField K]
    [IsScalarTower A q.ResidueField K] [Algebra.IsSeparable q.ResidueField K]
    {ι : Type} [Finite ι] (b : ι → K) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra A E) (_ : Algebra.Etale A E) (ε : E →ₐ[A] K),
      ∀ i, b i ∈ Set.range ε := by
  classical
  let k := q.ResidueField
  let L := IntermediateField.adjoin k (Set.range b)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  have hr : ∀ i, ∃ r : k[X], aeval θ r = (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) := by
    intro i
    have h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁
    obtain ⟨g, hg⟩ := h₁
    exact ⟨g, hg⟩
  choose r hr using hr
  have := Fintype.ofFinite ι
  let T : Finset k := (minpoly k θ).coeffs ∪ Finset.univ.biUnion fun i => (r i).coeffs
  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (A ⧸ q)) T
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hs : algebraMap A k s ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)
  let As := Localization.Away s
  let ρ : As →+* k := IsLocalization.Away.lift s (Ne.isUnit hs)
  have hρ : ∀ a : A, ρ (algebraMap A As a) = algebraMap A k a := IsLocalization.Away.lift_eq s _
  letI : Algebra As k := ρ.toAlgebra
  letI : Algebra As K := ((algebraMap k K).comp ρ).toAlgebra
  have : IsScalarTower As k K := .of_algebraMap_eq' rfl
  have : IsScalarTower A As K := .of_algebraMap_eq fun a => by
    change algebraMap A K a = algebraMap k K (ρ (algebraMap A As a))
    rw [hρ, ← IsScalarTower.algebraMap_apply]
  have hT : ∀ c ∈ T, c ∈ Set.range ρ := by
    intro c hc
    obtain ⟨a, ha⟩ := hdT c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s), ?_⟩
    have e1 : ρ (IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s)) * algebraMap A k s =
        algebraMap A k a := by
      rw [← hρ, ← hρ, ← map_mul, IsLocalization.mk'_spec]
    have e2 : c * algebraMap A k s = algebraMap A k a := by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k s, IsScalarTower.algebraMap_apply A (A ⧸ q) k a]
      erw [ha]
      rw [Algebra.smul_def, mul_comm]
      rfl
    exact mul_right_cancel₀ hs (e1.trans e2.symm)
  have hlift : ∀ g : k[X], (∀ c ∈ g.coeffs, c ∈ Set.range ρ) → ∃ g' : As[X], g'.map ρ = g := by
    intro g hg
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h : g.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact hg _ (Polynomial.coeff_mem_coeffs h)
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap As k)
    (p := minpoly k θ) (Polynomial.mem_lifts _ |>.mpr
      (hlift _ fun c hc => hT c (Finset.mem_union_left _ hc))) (minpoly.monic hi)
  let P : StandardEtalePair As := ⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩
  have key : ∀ g : As[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap As k)) : L) := fun g => by
    rw [← aeval_map_algebraMap k]
    exact aeval_algHom_apply L.val θ _
  have hP : P.HasMap (θ : K) := by
    refine ⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩
    rw [key, ← derivative_map, hμ]
    exact fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero
      (minpoly.aeval k θ) (Subtype.ext h)
  let ε₀ : P.Ring →ₐ[As] K := P.lift _ hP
  letI : Algebra A P.Ring := ((algebraMap As P.Ring).comp (algebraMap A As)).toAlgebra
  have : IsScalarTower A As P.Ring := .of_algebraMap_eq' rfl
  refine ⟨P.Ring, inferInstance, inferInstance, Algebra.Etale.comp A As P.Ring,
    ε₀.restrictScalars A, fun i => ?_⟩
  obtain ⟨g, hg⟩ := hlift (r i) fun c hc =>
    hT c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩))
  refine ⟨aeval P.X g, ?_⟩
  change ε₀ (aeval P.X g) = b i
  rw [← aeval_algHom_apply, StandardEtalePair.lift_X, key]
  change ((aeval θ (g.map ρ) : L) : K) = b i
  rw [hg, hr i]

theorem exists_etale_prime_of_smooth {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Smooth A C] (p : Ideal C) [p.IsPrime] :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (_ : C →ₐ[A] W)
      (P : Ideal W), P.IsPrime ∧ P.comap (algebraMap A W) = p.comap (algebraMap A C) := by
  set q := p.comap (algebraMap A C) with hq
  let K := SeparableClosure q.ResidueField
  letI : Algebra A K := ((algebraMap q.ResidueField K).comp (algebraMap A q.ResidueField)).toAlgebra
  have : IsScalarTower A q.ResidueField K := .of_algebraMap_eq' rfl
  have hker : RingHom.ker (algebraMap A K) = q := by
    rw [IsScalarTower.algebraMap_eq A q.ResidueField K, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap q.ResidueField K).injective]
    exact Ideal.ker_algebraMap_residueField q
  obtain ⟨φ⟩ := nonempty_algHom_of_smooth_of_isSepClosed (R := A) (K := K) p hker.symm
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A)
    (p := RingHom.ker φ)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) A
  let φ' : S →ₐ[A] K := IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)
  obtain ⟨E, _, _, _, ε, hε⟩ := exists_etale_subset_range_of_isPrime q
    fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))
  choose c hc using hε
  let χ : P →ₐ[A] K := φ'.comp (IsScalarTower.toAlgHom A _ _)
  have hχ : ε.comp (MvPolynomial.aeval c) = χ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    exact (congrArg ε (MvPolynomial.aeval_X (R := A) c i)).trans (hc i)
  letI := (MvPolynomial.aeval (R := A) c).toAlgebra
  have : IsScalarTower A P E := .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := A) c).commutes r).symm
  letI := χ.toAlgebra
  letI := ε.toAlgebra
  have : IsScalarTower A E K := .of_algebraMap_eq fun r => (ε.commutes r).symm
  have : IsScalarTower P E K := .of_algebraMap_eq fun r => congr($hχ r).symm
  let φ'' : S →ₐ[P] K := ⟨φ', fun r => rfl⟩
  let W := E ⊗[P] S
  let ε' : W →ₐ[E] K := Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _
  have hcomm : ∀ r : A, (1 : E) ⊗ₜ[P] algebraMap A S r = algebraMap A W r := fun r => by
    change (1 : E) ⊗ₜ[P] algebraMap A S r = (algebraMap A E r) ⊗ₜ[P] (1 : S)
    rw [IsScalarTower.algebraMap_apply A P S, IsScalarTower.algebraMap_apply A P E]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  refine ⟨W, inferInstance, inferInstance, Algebra.Etale.comp A E W,
    ⟨(Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp
      (algebraMap C S), fun r => ?_⟩, RingHom.ker ε', RingHom.ker_isPrime _, ?_⟩
  · change (1 : E) ⊗ₜ[P] algebraMap C S (algebraMap A C r) = algebraMap A W r
    rw [← IsScalarTower.algebraMap_apply]
    exact hcomm r
  · ext r
    rw [Ideal.mem_comap, RingHom.mem_ker,
      show ε' (algebraMap A W r) = algebraMap A K r from (ε'.restrictScalars A).commutes r,
      ← RingHom.mem_ker, hker]

theorem exists_etale_quasiSection_of_smooth : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (x : X),
    x ∈ Set.range f → ∃ (V : Scheme.{0}) (s : V ⟶ Y), Etale (s ≫ f) ∧ x ∈ Set.range (s ≫ f) := by
  intro Y X f _ x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨U, V, hU, hV, hVU, -, hyV⟩ := exists_isAffineOpen_pair f y (O := ⊤) trivial
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have := f.smooth_appLE hU hV hVU
  have := p.isPrime
  algebraize [(f.appLE U V hVU).hom]
  obtain ⟨W, _, _, _, ψ, P, hP, hPq⟩ :=
    exists_etale_prime_of_smooth (A := Γ(X, U)) (C := Γ(Y, V)) p.asIdeal
  have hs : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ≫ hU.fromSpec := by
    rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  refine ⟨Spec (.of W), Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ⟨⟨P, hP⟩, ?_⟩⟩
  · rw [hs]
    infer_instance
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ⟨P, hP⟩ =
      Spec.map (f.appLE U V hVU) p := PrimeSpectrum.ext hPq
  rw [hs]
  exact (congrArg hU.fromSpec e).trans congr($(hU.SpecMap_appLE_fromSpec f hV hVU) p)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.LfpDescent

theorem exists_linear_retraction (B C : Type*) [CommRing B] [CommRing C] [Algebra B C]
    [Module.Finite B C] [Module.Projective B C] (hinj : Function.Injective (algebraMap B C)) :
    ∃ l : C →ₗ[B] B, l 1 = 1 := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' B C
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hsum : ∀ x : C, ∑ i, s x i • π (Pi.single i 1) = x := by
    intro x
    have h1 : π (s x) = x := LinearMap.congr_fun hs x
    conv_rhs => rw [← h1]
    rw [LinearMap.pi_apply_eq_sum_univ π (s x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  let T : Ideal B := LinearMap.range (LinearMap.applyₗ (R := B) (M₂ := B) (1 : C))
  have hT : ∀ x i, s x i ∈ T := fun x i =>
    ⟨(LinearMap.proj i) ∘ₗ s ∘ₗ (LinearMap.mulRight B x), by simp⟩
  have hle : (⊤ : Submodule B C) ≤ T • (⊤ : Submodule B C) := by
    intro x _
    rw [← hsum x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hT x i) trivial
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul T ⊤
    Module.Finite.fg_top hle
  have hr1 : r = 0 := by
    apply hinj
    have := hr0 1 trivial
    rw [Algebra.smul_def, mul_one] at this
    simpa using this
  have h1 : (1 : B) ∈ T := by
    have := T.neg_mem hr
    simpa [hr1] using this
  obtain ⟨l, hl⟩ := h1
  exact ⟨l, hl⟩

theorem finitePresentation_of_retract (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Module.Finite A B]
    [Module.Finite A C] [Algebra.FinitePresentation A C] [Module.Finite B C]
    [Module.Projective B C] (hinj : Function.Injective (algebraMap B C)) :
    Algebra.FinitePresentation A B := by
  obtain ⟨l, hl⟩ := exists_linear_retraction B C hinj
  have : Module.FinitePresentation A C :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := A) (S := C)).2 inferInstance
  let l' : C →ₗ[A] B := l.restrictScalars A
  let i : B →ₗ[A] C := (Algebra.linearMap B C).restrictScalars A
  have hli : ∀ b, l' (i b) = b := by
    intro b
    change l (algebraMap B C b) = b
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one]
  have hsurj : Function.Surjective l' := fun b => ⟨i b, hli b⟩
  have hker : LinearMap.ker l' = LinearMap.range (LinearMap.id - i ∘ₗ l') := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    constructor
    · intro hx
      exact ⟨x, by rw [hx, map_zero, sub_zero]⟩
    · rintro ⟨y, rfl⟩
      rw [map_sub, hli, sub_self]
  have hfg : (LinearMap.ker l').FG := by
    rw [hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have : Module.FinitePresentation A B := Module.finitePresentation_of_surjective l' hsurj hfg
  exact (Module.FinitePresentation.iff_finitePresentation_of_finite (R := A) (S := B)).1 this

theorem ringHom_finitePresentation {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : f.Finite) (hgf : (g.comp f).Finite)
    (hgfp : (g.comp f).FinitePresentation) (hg : g.FaithfullyFlat) : f.FinitePresentation := by
  have hgfin : g.Finite := RingHom.Finite.of_comp_finite hgf
  have hgp : g.FinitePresentation :=
    RingHom.FinitePresentation.of_comp_finiteType f hgfp hf.finiteType
  algebraize [f, g, g.comp f]
  have : Module.FinitePresentation B C :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := B) (S := C)).2 inferInstance
  have : Module.Projective B C := Module.Flat.projective_of_finitePresentation
  exact finitePresentation_of_retract A B C hg.injective

end GlobalTheory.LfpDescent

namespace GlobalTheory.LfpDescent

theorem affine_case {X Y Z : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine Z] (h : X ⟶ Y)
    (f : Y ⟶ Z) [Flat h] [Surjective h] [IsFinite f] [IsFinite (h ≫ f)]
    [LocallyOfFinitePresentation (h ≫ f)] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have hff : h.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine h).1 ⟨inferInstance, inferInstance⟩
  have hfp : (h ≫ f).appTop.hom.FinitePresentation :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ inferInstance
  have hfin1 : f.appTop.hom.Finite := f.finite_appTop
  have hfin2 : (h ≫ f).appTop.hom.Finite := (h ≫ f).finite_appTop
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hfp hfin2
  exact ringHom_finitePresentation _ _ hfin1 hfin2 hfp hff

end GlobalTheory.LfpDescent

namespace GlobalTheory


open LfpDescent in
set_option backward.isDefEq.respectTransparency.types false in
theorem locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale :
    ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) →
      IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f →
      LocallyOfFinitePresentation f := by
  intro X Y Z h f _ _ _ _ _ _
  have : IsFinite f := GlobalTheory.isFinite_of_comp_surjective h f
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) (f := f) _
    (iSup_affineOpens_eq_top Z)]
  intro U
  have hU : IsAffine U := U.2
  have e := morphismRestrict_comp h f U
  have h1 : IsFinite ((h ≫ f) ∣_ U) := IsZariskiLocalAtTarget.restrict ‹_› _
  have h2 : LocallyOfFinitePresentation ((h ≫ f) ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @LocallyOfFinitePresentation) inferInstance _
  have : IsAffine (f ⁻¹ᵁ (U : Z.Opens)) := isAffine_of_isAffineHom (f ∣_ U)
  have : IsAffine ((h ≫ f) ⁻¹ᵁ (U : Z.Opens)) := isAffine_of_isAffineHom ((h ≫ f) ∣_ U)
  have : IsAffine (h ⁻¹ᵁ f ⁻¹ᵁ (U : Z.Opens)) := this
  have : Surjective (h ∣_ f ⁻¹ᵁ (U : Z.Opens)) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
  have : Flat (h ∣_ f ⁻¹ᵁ (U : Z.Opens)) := IsZariskiLocalAtTarget.restrict (P := @Flat) inferInstance _
  have : IsFinite (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹_› _
  have h1' : IsFinite (h ∣_ f ⁻¹ᵁ (U : Z.Opens) ≫ f ∣_ U) := e ▸ h1
  have h2' : LocallyOfFinitePresentation (h ∣_ f ⁻¹ᵁ (U : Z.Opens) ≫ f ∣_ U) := e ▸ h2
  exact affine_case (h ∣_ f ⁻¹ᵁ U) (f ∣_ U)

end GlobalTheory
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.gluedQuotientMap_finite_flat_surjective : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) →
    (∀ j, IsFinite (q j).left) → (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) →
    IsFinite Q.left ∧ Flat Q.left ∧ Surjective Q.left := by
  first | (exact @GlobalTheory.QuotGlue.finite_flat_surjective) | (exact GlobalTheory.QuotGlue.finite_flat_surjective) | (intros; apply GlobalTheory.QuotGlue.finite_flat_surjective  <;> assumption)
end
