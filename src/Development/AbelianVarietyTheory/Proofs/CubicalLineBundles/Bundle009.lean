module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_numberField_factor (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    {k₀ A : Type} [Field k₀] [CommRing A] (j : k₀ →+* k) (α : k₀ →+* A) (hα : α.FiniteType)
    (ψ : A →+* ℂ) (hψ : ∀ a, ψ (α a) = (j a : ℂ)) (halg : ∀ c, IsAlgebraic k (ψ c)) :
    ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (ψ₁ : A →+* K₁), FiniteDimensional ℚ K₁ ∧
      ψ₁.comp α = (IntermediateField.inclusion hk).toRingHom.comp j ∧
      (algebraMap K₁ ℂ).comp ψ₁ = ψ := by
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hα)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (ψ '' (t : Set A))) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨x, -, rfl⟩
    exact ((halg x).restrictScalars ℚ).isIntegral
  let K₁ : IntermediateField ℚ ℂ := k ⊔ IntermediateField.adjoin ℚ (ψ '' (t : Set A))
  have hk : k ≤ K₁ := le_sup_left
  have hmem : ∀ x, ψ x ∈ K₁ := by
    intro x
    have hx : x ∈ Algebra.adjoin k₀ (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K₁) (IntermediateField.subset_adjoin ℚ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change ψ (α r) ∈ K₁
      rw [hψ]; exact hk (j r).2
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K₁, hk, ψ.codRestrict K₁ hmem, IntermediateField.finiteDimensional_sup _ _, ?_, ?_⟩
  · ext a
    exact hψ a
  · rfl

theorem exists_fg_le_range_subset {k : Type} [Field k] [Algebra k ℂ] (R : Subalgebra k ℂ) (hR : R.FG)
    {X : Scheme.{0}} (y : Sp R ⟶ X) (U : X.Opens)
    (hU : (spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ) ∈ U) :
    ∃ (R' : Subalgebra k ℂ) (h : R ≤ R'), R'.FG ∧
      Set.range (spMap (Subalgebra.inclusion h).toRingHom ≫ y) ⊆ (U : Set X) := by
  classical
  let p : PrimeSpectrum R := PrimeSpectrum.comap R.val.toRingHom (IsLocalRing.closedPoint ℂ)
  have hp : p ∈ ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := hU
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R))) hp (y ⁻¹ᵁ U).2
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have : r = 0 := Subtype.ext h
    subst this
    exact hr (Ideal.zero_mem _)
  obtain ⟨t, ht⟩ := hR
  have hle : R ≤ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) := by
    conv_lhs => rw [← ht]
    exact Algebra.adjoin_mono (by simp)
  refine ⟨_, hle, ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hq : PrimeSpectrum.comap (Subalgebra.inclusion hle).toRingHom q ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    intro h
    have h' : Subalgebra.inclusion hle r ∈ q.asIdeal := h
    have hu : (r : ℂ)⁻¹ ∈ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) :=
      Algebra.subset_adjoin (by simp)
    have h1 : Subalgebra.inclusion hle r * ⟨_, hu⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hr0)
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.mul_mem_right _ _ h'))
  exact hsub hq

theorem exists_numberField_point_of_countable :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG → ∀ (k₀ : Type) [Field k₀] (j : k₀ →+* k) (X : Scheme.{0}) (s : X ⟶ Sp k₀) [LocallyOfFiniteType s] (y : Sp R ⟶ X), y ≫ s = spMap ((algebraMap k R).comp j) → Set.Countable (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y) →
  ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (y₁ : Sp K₁ ⟶ X), FiniteDimensional ℚ K₁ ∧ y₁ ≫ s = spMap ((IntermediateField.inclusion hk).toRingHom.comp j) ∧ spMap (algebraMap K₁ ℂ) ≫ y₁ = spMap R.val.toRingHom ≫ y := by
  intro k _ R hR k₀ _ j X s _ y hy hc
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp _ _).symm
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}, spMap f = spMap g → f = g :=
    fun h => congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ))) isOpen_univ
  obtain ⟨R', hle, hR', hsub⟩ := exists_fg_le_range_subset R hR y U hxU
  have hU' : IsAffineOpen U := hU
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU'.fromSpec
  haveI : IsOpenImmersion i := hU'.isOpenImmersion_fromSpec
  have hsub' : Set.range (spMap (Subalgebra.inclusion hle).toRingHom ≫ y) ⊆ Set.range i :=
    hsub.trans hU'.range_fromSpec.ge
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* R', spMap φ ≫ i = spMap (Subalgebra.inclusion hle).toRingHom ≫ y := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i _ hsub')
    exact ⟨φ.hom, (congrArg (· ≫ i) hφ).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨α, hα⟩ : ∃ α : k₀ →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφα : φ.comp α = (Subalgebra.inclusion hle).toRingHom.comp ((algebraMap k R).comp j) := by
    apply hinj
    rw [← hcomp, hα, ← Category.assoc, hφ, Category.assoc, hy, hcomp]
  have hcnt : Set.Countable ((fun ψ : A →+* ℂ => spMap ψ ≫ i) ⁻¹'
      (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y)) :=
    hc.preimage_of_injOn fun a _ b _ h => hinj ((cancel_mono i).1 h)
  have halg : ∀ c, IsAlgebraic k ((R'.val.toRingHom.comp φ) c) := by
    intro c
    refine IsAlgebraic.algHom R'.val (a := φ c) ?_
    refine (specialisation_numberField_and_countable_values k R' hR' (φ c) 1 one_ne_zero).2
      _ (hcnt.image fun ψ => ψ c) fun ρ => ⟨ρ.toRingHom.comp φ, ⟨ρ.comp (Subalgebra.inclusion hle), ?_⟩, rfl⟩
    change spMap (ρ.toRingHom.comp (Subalgebra.inclusion hle).toRingHom) ≫ y = spMap (ρ.toRingHom.comp φ) ≫ i
    rw [← hcomp, ← hcomp, Category.assoc, Category.assoc, hφ]
  obtain ⟨K₁, hk, ψ₁, hfd, h1, h2⟩ := exists_numberField_factor k j α hft (R'.val.toRingHom.comp φ)
    (fun a => congrArg Subtype.val (RingHom.congr_fun hφα a)) halg
  refine ⟨K₁, hk, spMap ψ₁ ≫ i, hfd, ?_, ?_⟩
  · rw [Category.assoc, ← hα, hcomp, h1]
  · rw [← Category.assoc, hcomp, h2, ← hcomp, Category.assoc, hφ, ← Category.assoc, hcomp]
    rfl

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.abelianScheme_surjective_of_onto_complex_points : ∀ (R : Type) [CommRing R] [IsDomain R] (σ : R →+* ℂ), Function.Injective σ → ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (Φ : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → (∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Over.mk (spMap σ) ⟶ B, y = x ≫ Φ) → Surjective Φ.left ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ A), ∃ x : Over.mk t ⟶ B, y = x ≫ Φ := by
  first | exact @GlobalTheory.OntoSurj.surjective_of_onto_complex_points | exact GlobalTheory.OntoSurj.surjective_of_onto_complex_points | (intros; apply GlobalTheory.OntoSurj.surjective_of_onto_complex_points <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SymOfZeroDivisor

theorem appLE_mem_nonZeroDivisors {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (a : Γ(X, W))
    (ha : ∀ (V : X.Opens) (h : V ≤ W), resG X h a ∈ nonZeroDivisors Γ(X, V))
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) : (f.appLE W V h).hom a ∈ nonZeroDivisors Γ(Y, V) := by
  have h' : f ''ᵁ V ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact h hy
  have e : (f.appLE W V h).hom a = (f.appIso V).hom.hom (resG X h' a) := by
    rw [Scheme.Hom.appIso_hom']
    change _ = (X.presheaf.map (homOfLE h').op ≫ f.appLE _ _ _).hom a
    rw [Scheme.Hom.map_appLE]
  rw [e]
  rw [← MulEquivClass.map_nonZeroDivisors (f.appIso V).commRingCatIsoToRingEquiv]
  exact Submonoid.mem_map_of_mem _ (ha _ h')

theorem inv_eq_zero_iff {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Scheme.{0}} (t : T ⟶ A.left) :
    t ≫ (GrpObj.inv : A ⟶ A).left = (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A ↔
      t = t ≫ A.hom ≫ eSec A := by
  have h1 : (GrpObj.inv : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  have h2 : eSec A ≫ (GrpObj.inv : A ⟶ A).left = eSec A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have h3 : (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A =
      (t ≫ A.hom ≫ eSec A) ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [Category.assoc, reassoc_of% h1]
    simp only [Category.assoc]
    exact congrArg (fun u => t ≫ A.hom ≫ u) h2.symm
  rw [h3]
  exact cancel_mono _

theorem sym_of_regular_section : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (i : L.ι) (V : Scheme.Opens A.left) (h : V ≤ L.U i), resG A.left h (θ.f i) ∈ nonZeroDivisors Γ(A.left, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → Out.Sym A L := by
  intro S A _ L θ hL hreg hz s
  refine ⟨⊤, trivial, ?_⟩
  haveI : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (GrpObj.inv : A ⟶ A)))
  refine GlobalTheory.T.isoLineBundle_of_regularPullbacks_sameZeroScheme A.left _ L θ _ _ hL
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) ?_
  intro T t i j h h'
  rw [hz, hz, ← Category.assoc t]
  exact inv_eq_zero_iff A _

end GlobalTheory.SymOfZeroDivisor
end
