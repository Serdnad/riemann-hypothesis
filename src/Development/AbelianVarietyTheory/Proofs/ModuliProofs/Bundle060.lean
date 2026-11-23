module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle056
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem exists_oAct_descend_of_etale_isogeny :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (a : OAct O A), IsAbelianScheme A → IsAbelianScheme B → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A) (c : O), x ≫ ψ = 1 → (x ≫ a.act c) ≫ ψ = 1) → ∃ b : OAct O B, ∀ c, a.act c ≫ ψ = ψ ≫ b.act c := by
  intro O _ S _ A B _ _ _ _ ψ a hA hB hψ hf he hs hker
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have key : ∀ c : O, ∃ g' : B ⟶ B, IsMonHom g' ∧ ψ ≫ g' = a.act c ≫ ψ ∧
      ∀ g'' : B ⟶ B, ψ ≫ g'' = a.act c ≫ ψ → g'' = g' := by
    intro c
    have := a.hom c
    refine GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S A B B ψ (a.act c ≫ ψ) hA hB hsep hψ hf he hs inferInstance ?_
    intro k _ _ t x hx
    rw [← Category.assoc]
    exact hker k t x c hx
  choose f hf1 hf2 hf3 using key
  refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, fun c => (hf2 c).symm⟩
  · refine (hf3 1 _ ?_).symm
    rw [a.one, Category.id_comp, Category.comp_id]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [← Category.assoc, hf2, Category.assoc, hf2, a.mul, Category.assoc]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [MonObj.comp_mul, hf2, hf2, a.add]
    exact (map_mul (IsMonHom.monoidHom ψ A) _ _).symm

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GenTorsMap

theorem exists_factor {K : Type} [Field K] (X : Over (Sp K)) (hX : IsFinite X.hom) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra K F] (x : Sp F ⟶ X.left) (hx : x ≫ X.hom = spMap (algebraMap K F)) :
    ∃ (σ : AlgebraicClosure K →ₐ[K] F) (x' : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X),
      x = spMap σ.toRingHom ≫ x'.left := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ X.left.isoSpec.hom)
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have hfin : c.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hc]; infer_instance
  have e : c ≫ φ = CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hc, Category.assoc, Iso.hom_inv_id_assoc, hx]
  let σ : AlgebraicClosure K →ₐ[K] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hr : ∀ b, φ.hom b ∈ σ.range := fun b => by
    have hi : IsIntegral K (φ.hom b) := by
      obtain ⟨p, hp, h0⟩ := hfin.to_isIntegral b
      refine ⟨p, hp, ?_⟩
      have := congrArg φ.hom h0
      rw [Polynomial.hom_eval₂, map_zero] at this
      have e' : φ.hom.comp c.hom = algebraMap K F := congrArg CommRingCat.Hom.hom e
      rwa [e'] at this
    exact hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) σ
  have hσ : Function.Injective σ := σ.toRingHom.injective
  let φ' : Γ(X.left, ⊤) →+* AlgebraicClosure K :=
    (AlgEquiv.ofInjective σ hσ).symm.toRingEquiv.toRingHom.comp (φ.hom.codRestrict σ.range hr)
  have h1 : ∀ b, σ (φ' b) = φ.hom b := fun b =>
    congrArg Subtype.val ((AlgEquiv.ofInjective σ hσ).apply_symm_apply ⟨φ.hom b, hr b⟩)
  refine ⟨σ, Over.homMk (Spec.map (CommRingCat.ofHom φ') ≫ X.left.isoSpec.inv) ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    erw [← hc]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    apply hσ
    refine (h1 _).trans ?_
    refine Eq.trans ?_ (σ.commutes a).symm
    exact congrArg (fun g => CommRingCat.Hom.hom g a) e
  · show x = _ ≫ _ ≫ _
    rw [← Category.assoc, Iso.eq_comp_inv, ← hφ, ← Spec.map_comp]
    congr 1
    ext b
    exact (h1 b).symm

theorem hom_ext_points {K : Type} [Field K] {X Y : Over (Sp K)} (hX : IsFinite X.hom) (hE : Etale X.hom)
    (hY : IsSeparated Y.hom) (u v : X ⟶ Y)
    (h : ∀ x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X, x ≫ u = x ≫ v) : u = v := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  haveI : IsReduced X.left := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
    have he : c.hom.Etale := by
      rw [← HasRingHomProperty.Spec_iff (P := @Etale), hc]; infer_instance
    letI := c.hom.toAlgebra
    haveI : Algebra.Etale K Γ(X.left, ⊤) := he
    haveI : _root_.IsReduced Γ(X.left, ⊤) := Algebra.FormallyUnramified.isReduced_of_field K _
    exact isReduced_of_isAffine_isReduced _
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq _ _ Y.hom Set.univ dense_univ (fun z _ => ?_) (by simp)
  let F := AlgebraicClosure (X.left.residueField z)
  let i := spMap (algebraMap (X.left.residueField z) F)
  obtain ⟨c, hc⟩ := Spec.map_surjective ((i ≫ X.left.fromSpecResidueField z) ≫ X.hom)
  letI : Algebra K F := c.hom.toAlgebra
  obtain ⟨σ, x', e⟩ := exists_factor X hX F _ hc.symm
  have : Epi i := by
    have : Flat i := inferInstance
    have : Surjective i :=
      ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (X.left.residueField z)) _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi i, ← Category.assoc, ← Category.assoc]
  erw [e]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun g => _ ≫ g.left) (h x')

variable {R : Type} [CommRing R] [IsDomain R]

end GlobalTheory.GenTorsMap
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.GenericSmooth

theorem le_ringKrullDim_of_mem_minimalPrimes (o k R S : Type) [CommRing o] [IsDomain o] [Field k]
    [CommRing R] [CommRing S] [Algebra o k] [IsFractionRing o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    [IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S]
    [Algebra.FiniteType k S] (d : ℕ)
    (h : ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R →
      (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) : (d : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  let K := FractionRing (S ⧸ q)
  let ψ : S →ₐ[o] K := (IsScalarTower.toAlgHom o (S ⧸ q) K).comp (Ideal.Quotient.mkₐ o q)
  let φ : R →ₐ[o] K := ψ.comp (IsScalarTower.toAlgHom o R S)
  have hψ : ∀ s, ψ s = 0 ↔ s ∈ q := fun s ↦ by
    change algebraMap (S ⧸ q) K (Ideal.Quotient.mk q s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker φ = q.under R := by
    ext r
    exact hψ (algebraMap R S r)
  have hmin : RingHom.ker φ ∈ minimalPrimes R := by
    have h' := IsLocalization.minimalPrimes_map
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S ⊥
    rw [Ideal.map_bot] at h'
    rw [hker]
    exact h'.le hq
  have hs : ∀ s : S, ∃ a b, φ b ≠ 0 ∧ ψ s = φ a / φ b := fun s ↦ by
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) s
    have hb : φ b ≠ 0 := ((IsLocalization.map_units S b).map ψ).ne_zero
    refine ⟨a, b, hb, ?_⟩
    rw [eq_div_iff hb]
    have := congrArg ψ hab
    rw [map_mul] at this
    exact this
  have hsurj : ∀ z : K, ∃ a b, z = φ a / φ b := fun z ↦ by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ q) z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, b, hb, h₁⟩ := hs x
    obtain ⟨a', b', hb', h₂⟩ := hs y
    refine ⟨a * b', b * a', ?_⟩
    change ψ x / ψ y = _
    rw [h₁, h₂, map_mul, map_mul, div_div_div_eq]
  obtain ⟨y, hy⟩ := h K φ hmin hsurj
  obtain ⟨n, h₁, h₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k (S ⧸ q)
  have hk : AlgebraicIndependent k y := by
    have : Algebra.IsAlgebraic o k := IsLocalization.isAlgebraic k (nonZeroDivisors o)
    exact hy.extendScalars k
  have h₃ := hk.cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic (S ⧸ q) K := IsLocalization.isAlgebraic K (nonZeroDivisors (S ⧸ q))
  have : FaithfulSMul k (S ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k (S ⧸ q)).injective
  rw [← trdeg_add_eq k (S ⧸ q) (A := K), trdeg_eq_zero (R := S ⧸ q) (A := K), add_zero, h₂,
    Cardinal.mk_fin] at h₃
  rw [h₁]
  exact_mod_cast h₃

theorem finrank_derivation_le (o k R S C : Type) [CommRing o] [CommRing k]
    [CommRing R] [CommRing S] [Field C] [Algebra o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    (M : Submonoid R) [IsLocalization M S] [Algebra.FiniteType o R]
    [Algebra k C] [Algebra S C] [IsScalarTower k S C] [Algebra o C] [Algebra R C]
    [IsScalarTower o R C] [IsScalarTower R S C] [IsScalarTower o S C] [IsScalarTower o k C] :
    Module.finrank C (Derivation k S C) ≤ Module.finrank C (Derivation o R C) := by
  have : Module.Finite C (Derivation o R C) :=
    Module.Finite.equiv (GlobalTheory.SmoothTangent.derivationEquivDual o R C).symm
  let f : Derivation k S C →ₗ[C] Derivation o R C :=
    { toFun := fun D ↦ (D.restrictScalars o).compAlgebraMap R
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro D hD
  have h0 : ∀ r, D (algebraMap R S r) = 0 := fun r ↦ congr($hD r)
  ext s
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M s
  have := congrArg D hab
  rw [D.leibniz, h0, h0, smul_zero, zero_add, Algebra.smul_def] at this
  exact (mul_eq_zero.mp this).resolve_left
    ((IsLocalization.map_units S b).map (algebraMap S C)).ne_zero

end GlobalTheory.GenericSmooth

namespace GlobalTheory


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le :
    ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by
  intro o _ _ em R _ _ d hem hft hind htan
  let e : FractionRing o →+* ℂ := IsFractionRing.lift hem
  have : CharZero (FractionRing o) := e.charZero
  have := IsLocalization.tensorRight (S := R) (FractionRing o) (nonZeroDivisors o)
  refine smoothOfRelativeDimension_of_dim_of_finrank_derivation_le (FractionRing o) e _ d
    inferInstance
    (GenericSmooth.le_ringKrullDim_of_mem_minimalPrimes o (FractionRing o) R _ d hind) ?_
  intro _ _ _ he
  let : Algebra o ℂ := em.toAlgebra
  let : Algebra R ℂ :=
    ((algebraMap (FractionRing o ⊗[o] R) ℂ).comp (algebraMap R _)).toAlgebra
  have h₁ : IsScalarTower o (FractionRing o) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [he]
    exact (IsFractionRing.lift_algebraMap hem x).symm
  have h₂ : IsScalarTower o (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply o (FractionRing o) ℂ,
      IsScalarTower.algebraMap_apply (FractionRing o) (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o (FractionRing o) (FractionRing o ⊗[o] R)]
  have h₃ : IsScalarTower R (FractionRing o ⊗[o] R) ℂ := .of_algebraMap_eq fun _ ↦ rfl
  have h₄ : IsScalarTower o R ℂ := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R (FractionRing o ⊗[o] R) ℂ,
      ← IsScalarTower.algebraMap_apply o R (FractionRing o ⊗[o] R),
      ← IsScalarTower.algebraMap_apply o (FractionRing o ⊗[o] R) ℂ]
  exact (GenericSmooth.finrank_derivation_le o (FractionRing o) R _ ℂ
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))).trans (htan rfl)

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnifDvrCompare
open GlobalTheory.UU GlobalTheory.LN

theorem exists_point_of_fixed {F F' : Type} [Field F] [Field F'] [Algebra F F'] [IsGalois F F'] {X : Scheme.{0}}
    (x' : Sp F' ⟶ X) (h : ∀ σ : Gal(F'/F), spMap (σ : F' →+* F') ≫ x' = x') :
    ∃ x : Sp F ⟶ X, spMap (algebraMap F F') ≫ x = x' := by
  obtain ⟨⟨y, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField F' X).symm.surjective x'
  have e : (Scheme.SpecToEquivOfField F' X).symm ⟨y, f⟩ = Spec.map f ≫ X.fromSpecResidueField y := rfl
  rw [e] at h ⊢
  have hf : ∀ a, f.hom a ∈ (algebraMap F F').range := fun a => by
    refine IntermediateField.mem_bot.1 ((InfiniteGalois.mem_bot_iff_fixed _).2 fun σ => ?_)
    have := h σ
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp] at this
    exact congrArg (fun q => q.hom a) (Spec.map_injective this)
  choose g hg using hf
  have inj := (algebraMap F F').injective
  let g' : X.residueField y →+* F :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }
  refine ⟨Spec.map (CommRingCat.ofHom g') ≫ X.fromSpecResidueField y, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hg)

section Totality

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

end Totality

section HidaSetting

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

end HidaSetting

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Triples

end GlobalTheory.UnifDvrCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_isTypeFn_of_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ), Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) → ∃ ty : Fin g → (E →+* ℂ), IsTypeFn H D.p D.q ty := by
  intro E _ _ _ H D g ⟨e⟩
  obtain ⟨g', ty, h, -, P, -, hinj, hdisc, hspan, -⟩ := GlobalTheory.PeriodExists.exists_typeFn_period H D
  let L : Submodule ℤ (Fin g' → ℂ) := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology L := hdisc
  have : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g' → ℂ)) = Set.range P := by ext; simp [L]
    rw [this]; exact hspan⟩
  have h1 := ZLattice.rank ℝ L
  have h2 : Module.finrank ℤ L = 2 * g := by
    rw [← (e.trans (LinearEquiv.ofInjective P.toIntLinearMap hinj)).finrank_eq]
    simp
  have h3 : Module.finrank ℝ (Fin g' → ℂ) = 2 * g' := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  obtain rfl : g' = g := by omega
  exact ⟨ty, h⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  first | exact @GlobalTheory.exists_finset_isProjOver_descends | exact GlobalTheory.exists_finset_isProjOver_descends | (intros; apply GlobalTheory.exists_finset_isProjOver_descends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem pmaps_self_of_tautological {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    PMaps w φ φ ε t t (𝟙 Y) := by
  subst hF
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id, gen_trans ht r z (j := p) (j' := q) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq), trF]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hw Z (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]

end GlobalTheory.TorsionFormCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors.TorsMapExists

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ]
  simp only [Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

end GlobalTheory.FlatTors.TorsMapExists
end
