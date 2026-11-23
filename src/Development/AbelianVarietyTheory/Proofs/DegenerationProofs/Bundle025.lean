module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem residue_embedding_unique {X : Scheme.{0}} {Ω : CommRingCat.{0}} [Nonempty (Spec Ω)]
    {p q : X} (φ : X.residueField p ⟶ Ω) (ψ : X.residueField q ⟶ Ω)
    (h : Spec.map φ ≫ X.fromSpecResidueField p = Spec.map ψ ≫ X.fromSpecResidueField q) :
    ∃ e : p = q, φ = (X.residueFieldCongr e).hom ≫ ψ := by
  obtain ⟨t⟩ := ‹Nonempty (Spec Ω)›
  have e : p = q := by
    have := congrArg (fun f => f t) h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this
  subst e
  refine ⟨rfl, ?_⟩
  rw [cancel_mono, Spec.map_inj] at h
  simpa using h

theorem essFiniteType_residueField_of_locallyOfFiniteType {X : Scheme.{0}} {R : CommRingCat.{0}}
    (s : X ⟶ Spec R) [LocallyOfFiniteType s] (p : X) (ψ : R ⟶ X.residueField p)
    (h : Spec.map ψ = X.fromSpecResidueField p ≫ s) : ψ.hom.EssFiniteType := by
  haveI : (s p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have e : ψ = CommRingCat.ofHom (algebraMap R (s p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (s p)).inv ≫ s.residueFieldMap p := by
    rw [← Spec.map_inj, h, Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [e]
  refine .comp (RingHom.essFiniteType_algebraMap.mpr inferInstance) (.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.Spec.residueFieldIso R (s p)).inv).2).essFiniteType
    (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap s p)))

theorem exists_fieldOfValues : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  intro X Ω _ x
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  subst hx
  let f : X.residueField p →+* Ω := φ.hom
  refine ⟨f.fieldRange, fun τ τ' => ?_, fun K' _ j => ⟨fun h => ?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
      Spec.map_inj]
    constructor
    · rintro h _ ⟨c, rfl⟩
      exact congrArg (fun g => g.hom c) h
    · intro h
      ext c
      exact h _ ⟨c, rfl⟩
  · let e : K' ≃+* j.fieldRange := j.rangeRestrictFieldEquiv
    let g : X.residueField p →+* K' :=
      e.symm.toRingHom.comp (f.codRestrict j.fieldRange fun c => h ⟨c, rfl⟩)
    refine ⟨Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecResidueField p, ?_⟩
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f c, h ⟨c, rfl⟩⟩)
  · rintro ⟨y, hy⟩
    obtain ⟨⟨q, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K' X).symm.surjective y
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hy
    rw [← Category.assoc, ← Spec.map_comp] at hy
    obtain ⟨e, he⟩ := residue_embedding_unique _ _ hy.symm
    rintro _ ⟨c, rfl⟩
    exact ⟨ψ.hom ((X.residueFieldCongr e).hom.hom c), (congrArg (fun g => g.hom c) he).symm⟩
  · intro K _ _ s hs hxs halg
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ s)
    have hess := essFiniteType_residueField_of_locallyOfFiniteType s p ψ hψ
    rw [Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
    letI : Algebra K (X.residueField p) := ψ.hom.toAlgebra
    let fa : X.residueField p →ₐ[K] Ω :=
      { f with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
    haveI : Algebra.EssFiniteType K (X.residueField p) := hess
    haveI : Algebra.IsAlgebraic K (X.residueField p) :=
      Algebra.IsAlgebraic.of_injective fa f.injective
    haveI : Module.Finite K (X.residueField p) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    refine ⟨fa.fieldRange, ?_, rfl⟩
    exact Module.Finite.equiv (AlgEquiv.ofInjectiveField fa).toLinearEquiv

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.ArcInf

section General
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

theorem algOverHom_left (ψ : A →ₐ[k] B) : (algOverHom ψ).left = spMap (ψ : A →+* B) := rfl

theorem algOverHom_comp (ψ : A →ₐ[k] B) (χ : B →ₐ[k] C) :
    algOverHom (χ.comp ψ) = algOverHom χ ≫ algOverHom ψ := by
  ext1
  rw [Over.comp_left, algOverHom_left, algOverHom_left, algOverHom_left]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem algOverHom_id : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  ext1
  rw [algOverHom_left]
  exact Spec.map_id _

theorem algOverHom_injective : Function.Injective (algOverHom : (A →ₐ[k] B) → _) := by
  intro a b h
  have h1 : spMap (a : A →+* B) = spMap (b : A →+* B) := congrArg (fun x => x.left) h
  have h2 := Spec.map_injective h1
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h2)

theorem algOverHom_surjective : Function.Surjective (algOverHom : (A →ₐ[k] B) → _) := by
  intro φ
  obtain ⟨g, hg⟩ := Spec.map_surjective φ.left
  have hw : φ.left ≫ spMap (algebraMap k A) = spMap (algebraMap k B) := Over.w φ
  rw [← hg, ← Spec.map_comp] at hw
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  refine ⟨⟨g.hom, fun c => congrArg (fun f : k →+* B => f c) h2⟩, ?_⟩
  ext1
  exact hg

theorem eq_of_comp_eq {G : Over (Sp k)} {j : algOver k A ⟶ G} (hj : IsOpenImmersion j.left) {a b : A →ₐ[k] B}
    (h : algOverHom a ≫ j = algOverHom b ≫ j) : a = b := by
  apply algOverHom_injective
  ext1
  have := congrArg (fun x => x.left) h
  simp only [Over.comp_left] at this
  exact (cancel_mono j.left).1 this

end General

variable {k : Type} [Field k]

theorem exists_lift {F : Type} [CommRing F] [Algebra k F] (ρ : PowerSeries k →ₐ[k] F)
    (h : IsUnit (ρ PowerSeries.X)) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] F, ∀ x, σ (algebraMap (PowerSeries k) _ x) = ρ x := by
  have hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (ρ y) := by
    rintro ⟨y, hy⟩
    have h0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    obtain ⟨u, hu⟩ := hn.symm
    show IsUnit (ρ y)
    rw [← hu, map_mul, map_pow]
    exact (h.pow n).mul (u.isUnit.map ρ)
  exact ⟨IsLocalization.liftAlgHom (S := FractionRing (PowerSeries k)) hu, fun x => by simp⟩

def IsChart (G : Over (Sp k)) [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    (ε : A →ₐ[k] k) {r : ℕ} (f : Fin r → A) : Prop :=
  IsOpenImmersion j.left ∧ algOverHom ε ≫ j = 1 ∧ Algebra.adjoin k (Set.range f) = ⊤ ∧ ∀ i, ε (f i) = 0

def TwoVar {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    {r : ℕ} (f : Fin r → A) (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ (F : Type) [Field F] [Algebra k F] (τ : MvPowerSeries (Fin 2) k →ₐ[k] F)
    (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] F), τ d ≠ 0 →
    (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) →
    (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) →
    ∃ χ : A →ₐ[k] F, (∀ i, χ (f i) * τ d = τ (h i)) ∧
      algOverHom σ₁ ≫ a = (algOverHom χ ≫ j) * (algOverHom σ₀ ≫ a)

theorem IsChart.hom_ext {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A} (hc : IsChart G j ε f) {B : Type} [CommRing B] [Algebra k B]
    {a b : A →ₐ[k] B} (h : ∀ i, a (f i) = b (f i)) : a = b :=
  AlgHom.ext_of_adjoin_eq_top hc.2.2.1 (by rintro _ ⟨i, rfl⟩; exact h i)

end GlobalTheory.SS.ArcInf
end
end
