module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MilFlat

open TensorProduct

theorem isPullback_iff_elem {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (w : f ≫ h = g ≫ i) :
    IsPullback f g h i ↔ (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  constructor
  · intro H
    have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
    exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩
  · rintro ⟨h₁, h₂⟩
    refine IsPullback.of_map (forget CommRingCat) w ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
    · ext x
      simpa using congrArg (fun φ : A ⟶ D ↦ φ.hom x) w
    · exact fun x y hxy ↦ h₁ x y hxy.1 hxy.2
    · exact fun b c hbc ↦ h₂ b c hbc

theorem isoIsPushout_tmul {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {X : CommRingCat.{0}} {f : CommRingCat.of A ⟶ X} {f' : CommRingCat.of B ⟶ X}
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) f f') (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R A B).isoIsPushout _ _ h).hom.hom (a ⊗ₜ b) = f.hom a * f'.hom b := by
  have e₁ := congrArg (fun φ ↦ φ.hom a)
    (IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A B) h)
  have e₂ := congrArg (fun φ ↦ φ.hom b)
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A B) h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂
  have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by simp
  rw [this, map_mul]
  simp only [Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply] at e₁ e₂
  exact congrArg₂ (· * ·) e₁ e₂

theorem isPullback_of_flat (P C₁ C₂ C₀ E E₁ E₂ E₀ : CommRingCat.{0}) (p₁ : P ⟶ C₁) (p₂ : P ⟶ C₂) (q₁ : C₁ ⟶ C₀)
    (q₂ : C₂ ⟶ C₀) (hP : IsPullback p₁ p₂ q₁ q₂) (hq : Function.Surjective q₂.hom) (g : P ⟶ E) (g₁ : C₁ ⟶ E₁)
    (g₂ : C₂ ⟶ E₂) (g₀ : C₀ ⟶ E₀) (i₁ : E ⟶ E₁) (i₂ : E ⟶ E₂) (r₁ : E₁ ⟶ E₀) (r₂ : E₂ ⟶ E₀) (hg : g.hom.Flat)
    (h₁ : IsPushout g p₁ i₁ g₁) (h₂ : IsPushout g p₂ i₂ g₂) (h₀ : IsPushout g₂ q₂ r₂ g₀)
    (w₁ : i₁ ≫ r₁ = i₂ ≫ r₂) (w₂ : g₁ ≫ r₁ = q₁ ≫ g₀) : IsPullback i₁ i₂ r₁ r₂ := by
  letI : Algebra P E := g.hom.toAlgebra
  letI : Algebra P C₁ := p₁.hom.toAlgebra
  letI : Algebra P C₂ := p₂.hom.toAlgebra
  letI : Algebra P C₀ := (p₂ ≫ q₂).hom.toAlgebra
  haveI : Module.Flat P E := hg
  have hw : ∀ a, q₁.hom (p₁.hom a) = q₂.hom (p₂.hom a) := fun a ↦ by
    simpa using congrArg (fun φ ↦ φ.hom a) hP.w
  have hw₁ : ∀ x, r₁.hom (i₁.hom x) = r₂.hom (i₂.hom x) := fun x ↦ by
    simpa using congrArg (fun φ ↦ φ.hom x) w₁
  have hw₂ : ∀ c, r₁.hom (g₁.hom c) = g₀.hom (q₁.hom c) := fun c ↦ by
    simpa using congrArg (fun φ ↦ φ.hom c) w₂
  have hw₀ : ∀ c, r₂.hom (g₂.hom c) = g₀.hom (q₂.hom c) := fun c ↦ by
    simpa using congrArg (fun φ ↦ φ.hom c) h₀.w
  obtain ⟨hinj, hex⟩ := (isPullback_iff_elem p₁ p₂ q₁ q₂ hP.w).1 hP

  let f : P →ₗ[P] C₁ × C₂ := (Algebra.linearMap P C₁).prod (Algebra.linearMap P C₂)
  let Q₁ : C₁ →ₗ[P] C₀ :=
    { toFun := q₁.hom, map_add' := map_add _
      map_smul' := fun a c ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hw] }
  let Q₂ : C₂ →ₗ[P] C₀ :=
    { toFun := q₂.hom, map_add' := map_add _
      map_smul' := fun a c ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  let h : C₁ × C₂ →ₗ[P] C₀ := Q₁ ∘ₗ LinearMap.fst P C₁ C₂ - Q₂ ∘ₗ LinearMap.snd P C₁ C₂
  have hh : ∀ x y, h (x, y) = q₁.hom x - q₂.hom y := fun _ _ ↦ rfl
  have hf : ∀ a, f a = (p₁.hom a, p₂.hom a) := fun _ ↦ rfl
  have hfinj : Function.Injective f := fun a b hab ↦ by
    rw [hf, hf, Prod.ext_iff] at hab
    exact hinj a b hab.1 hab.2
  have hexact : Function.Exact f h := by
    rintro ⟨x, y⟩
    rw [hh, sub_eq_zero]
    constructor
    · intro hxy
      obtain ⟨a, ha₁, ha₂⟩ := hex x y hxy
      exact ⟨a, by rw [hf, ha₁, ha₂]⟩
    · rintro ⟨a, ha⟩
      rw [hf, Prod.mk.injEq] at ha
      rw [← ha.1, ← ha.2]
      exact hw a
  have hsurj : Function.Surjective h := fun z ↦ by
    obtain ⟨y, hy⟩ := hq (-z)
    exact ⟨(0, y), by rw [hh, hy]; simp⟩
  have hex' := lTensor_exact E hexact hsurj
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := E) f hfinj

  have h₀' : IsPushout g (p₂ ≫ q₂) (i₂ ≫ r₂) g₀ := (h₂.flip.paste_horiz h₀.flip).flip
  let k₁ := (CommRingCat.isPushout_tensorProduct P E C₁).isoIsPushout _ _ h₁
  let k₂ := (CommRingCat.isPushout_tensorProduct P E C₂).isoIsPushout _ _ h₂
  let k₀ := (CommRingCat.isPushout_tensorProduct P E C₀).isoIsPushout _ _ h₀'
  have k₁t : ∀ (e : E) (c : C₁), k₁.hom.hom (e ⊗ₜ c) = i₁.hom e * g₁.hom c := isoIsPushout_tmul h₁
  have k₂t : ∀ (e : E) (c : C₂), k₂.hom.hom (e ⊗ₜ c) = i₂.hom e * g₂.hom c := isoIsPushout_tmul h₂
  have k₀t : ∀ (e : E) (c : C₀), k₀.hom.hom (e ⊗ₜ c) = r₂.hom (i₂.hom e) * g₀.hom c := isoIsPushout_tmul h₀'
  have kinv : ∀ {X Y : CommRingCat.{0}} (k : X ≅ Y) (y : Y), k.hom.hom (k.inv.hom y) = y := fun k y ↦ by simp
  have kinj : ∀ {X Y : CommRingCat.{0}} (k : X ≅ Y), Function.Injective k.hom.hom := fun k x y hxy ↦ by
    simpa using congrArg k.inv.hom hxy
  let pr := TensorProduct.prodRight P P E C₁ C₂
  have key : ∀ x, k₀.hom.hom (h.lTensor E x) =
      r₁.hom (k₁.hom.hom (pr x).1) - r₂.hom (k₂.hom.hom (pr x).2) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e c =>
      obtain ⟨c₁, c₂⟩ := c
      rw [LinearMap.lTensor_tmul, hh, TensorProduct.prodRight_tmul, k₀t, k₁t, k₂t, map_mul, map_mul, hw₁, hw₂,
        hw₀, map_sub]
      ring
    | add x y hx hy =>
      simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, hx, hy]
      ring
  have keyone : ∀ e : E, pr (f.lTensor E (e ⊗ₜ 1)) = (e ⊗ₜ 1, e ⊗ₜ 1) := fun e ↦ by
    rw [LinearMap.lTensor_tmul, hf, map_one, map_one, TensorProduct.prodRight_tmul]
  have k₁one : ∀ e, k₁.hom.hom (e ⊗ₜ 1) = i₁.hom e := fun e ↦ by rw [k₁t, map_one, _root_.mul_one]
  have k₂one : ∀ e, k₂.hom.hom (e ⊗ₜ 1) = i₂.hom e := fun e ↦ by rw [k₂t, map_one, _root_.mul_one]
  refine (isPullback_iff_elem i₁ i₂ r₁ r₂ w₁).2 ⟨fun x y hx hy ↦ ?_, fun a b hab ↦ ?_⟩
  · have : f.lTensor E (x ⊗ₜ 1) = f.lTensor E (y ⊗ₜ 1) := by
      apply pr.injective
      rw [keyone, keyone, Prod.mk.injEq]
      exact ⟨kinj k₁ (by rw [k₁one, k₁one, hx]), kinj k₂ (by rw [k₂one, k₂one, hy])⟩
    simpa using congrArg (TensorProduct.rid P E) (hinj' this)
  · obtain ⟨x, hxd⟩ : ∃ x, pr x = (k₁.inv.hom a, k₂.inv.hom b) := ⟨pr.symm _, pr.apply_symm_apply _⟩
    have hx0 : h.lTensor E x = 0 := by
      apply kinj k₀
      rw [key, map_zero, hxd, kinv, kinv, hab, sub_self]
    obtain ⟨y, hy⟩ := (hex' x).1 hx0
    have hy' : y = (TensorProduct.rid P E y) ⊗ₜ 1 := by
      rw [← TensorProduct.rid_symm_apply, LinearEquiv.symm_apply_apply]
    rw [hy'] at hy
    have e₁ := congrArg (fun z ↦ k₁.hom.hom (pr z).1) hy
    have e₂ := congrArg (fun z ↦ k₂.hom.hom (pr z).2) hy
    simp only [keyone, k₁one, k₂one, hxd, kinv] at e₁ e₂
    exact ⟨_, e₁, e₂⟩

end GlobalTheory.MilFlat
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension g A B →
    Algebra.IsStandardSmoothOfRelativeDimension g A C →
    Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  intro A B C _ _ _ _ _ _ _ g hB hC hU
  have : Algebra.IsStandardSmooth A B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Algebra.IsStandardSmooth A C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange A B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map A B C x).mp (Subsingleton.elim _ _)
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A B C) := by
    rcases subsingleton_or_nontrivial C with hC0 | hC0
    · intro x y _
      exact Subsingleton.elim (α := TensorProduct B C Ω[B⁄A]) x y
    · have : Nontrivial B := (algebraMap B C).domain_nontrivial
      have : Module.Free B Ω[B⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have : Module.Free C Ω[C⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have hr : Module.rank C Ω[C⁄A] = Module.rank C (TensorProduct B C Ω[B⁄A]) := by
        rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g, Module.rank_baseChange,
          Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g]
        simp
      obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq hr
      have h2 : Function.Surjective (e.toLinearMap ∘ₗ KaehlerDifferential.mapBaseChange A B C) :=
        e.surjective.comp hs
      have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
      exact fun x y hxy => h3 (by simp [hxy])
  have : Algebra.FormallySmooth B C := by
    rw [Algebra.formallySmooth_iff]
    constructor
    · exact Module.Projective.of_free
    · refine subsingleton_of_forall_eq 0 fun x => ?_
      have h₁ : Algebra.H1Cotangent.δ A B C x = 0 := by
        apply hinj
        rw [map_zero]
        exact (Algebra.H1Cotangent.exact_δ_mapBaseChange A B C).apply_apply_eq_zero x
      obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ A B C x).mp h₁
      rw [Subsingleton.elim y 0, map_zero]
  have : Algebra.FormallyEtale B C := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  have : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.LinearCodimTwo

open GlobalTheory.ProjSpace GlobalTheory.Adelic

theorem exists_linear_closedImmersion_two_le_ringKrullDim_stalk :
    ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧
      ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧
      ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  intro F _ N
  have h1 : Function.Injective (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := Fin.castSucc_injective _
  have h2 : Function.Injective (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := Fin.castSucc_injective _
  let ℓ₁ : PSpace F N ⟶ PSpace F (N + 1) := linearι F h1
  let ℓ₂ : PSpace F (N + 1) ⟶ PSpace F (N + 2) := linearι F h2
  have linear_str (A B : ℕ) {e : Fin (A + 1) → Fin (B + 1)}
      (he : Function.Injective e) : linearι F he ≫ PSpace.str F B = PSpace.str F A := by
    refine (Proj.mapAffineOpenCover (killHom F he)
      (irrelevant_le_map_of_surjective _ (killHom_surjective F he))).openCover.hom_ext _ _ fun s => ?_
    have key : ∀ (d : ℕ) (hd : 0 < d) (s : MvPolynomial (Fin (B + 1)) F) (hs : s ∈ grading F B d),
        Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ linearι F he ≫ PSpace.str F B =
          Proj.awayι (grading F A) (killHom F he s) ((killHom F he).2 hs) hd ≫ PSpace.str F A := by
      intro d hd s hs
      rw [linearι, Proj.awayι_comp_map_assoc _ _ hd s hs, PSpace.str, PSpace.str, Proj.awayι_toSpecZero_assoc,
        Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      refine RingHom.ext fun r => HomogeneousLocalization.val_injective _ ?_
      refine (congrArg HomogeneousLocalization.val (HomogeneousLocalization.Away.map_mk (killHom F he) s hs 0 (MvPolynomial.C r)
        ((zero_smul ℕ d).symm ▸ MvPolynomial.isHomogeneous_C _ r))).trans ?_
      rw [HomogeneousLocalization.Away.val_mk]
      exact congrArg (Localization.mk · _) (MvPolynomial.killCompl_C he r)
    exact key _ s.1.2 _ s.2.2
  refine ⟨ℓ₁ ≫ ℓ₂, inferInstance, by rw [Category.assoc, linear_str _ _ h2, linear_str _ _ h1], fun y => ?_⟩
  have last1 : Fin.last (N + 1) ∉ Set.range (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have last2 : Fin.last (N + 2) ∉ Set.range (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have n1 : ℓ₁ y ∉ chart F (N + 1) (Fin.last (N + 1)) := fun h => by
    have : y ∈ ℓ₁ ⁻¹ᵁ chart F (N + 1) (Fin.last (N + 1)) := h
    rw [linearι_preimage_chart_of_notMem F h1 last1] at this
    exact this
  have n2 (z : PSpace F (N + 1)) : ℓ₂ z ∉ chart F (N + 2) (Fin.last (N + 2)) := fun h => by
    have : z ∈ ℓ₂ ⁻¹ᵁ chart F (N + 2) (Fin.last (N + 2)) := h
    rw [linearι_preimage_chart_of_notMem F h2 last2] at this
    exact this
  have s1 : projSys.gen F (N + 1) ⤳ ℓ₁ y :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₁ y).asHomogeneousIdeal from bot_le))
  have s2 : projSys.gen F (N + 2) ⤳ ℓ₂ (projSys.gen F (N + 1)) :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₂ (projSys.gen F (N + 1))).asHomogeneousIdeal from bot_le))
  have lt1 : ℓ₂ (ℓ₁ y) < ℓ₂ (projSys.gen F (N + 1)) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 (s1.map ℓ₂.continuous)) fun h => ?_
    have := ℓ₂.isClosedEmbedding.injective ((Scheme.le_iff_specializes.1 h).antisymm (s1.map ℓ₂.continuous)).eq
    exact n1 (this ▸ projSys.gen_mem F (N + 1) (Fin.last (N + 1)))
  have lt2 : ℓ₂ (projSys.gen F (N + 1)) < projSys.gen F (N + 2) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 s2) fun h => ?_
    have e : ℓ₂ (projSys.gen F (N + 1)) = projSys.gen F (N + 2) := ((Scheme.le_iff_specializes.1 h).antisymm s2).eq
    exact n2 _ (by rw [e]; exact projSys.gen_mem F (N + 2) (Fin.last (N + 2)))
  have hc : (2 : ℕ∞) ≤ Order.coheight (ℓ₂ (ℓ₁ y)) := by
    have a := Order.coheight_add_one_le lt1
    have b := Order.coheight_add_one_le lt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (projSys.gen F (N + 2)) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight (ℓ₂ (projSys.gen F (N + 1))) + 1 := by gcongr
      _ ≤ _ := a
  rw [Scheme.Hom.comp_apply, ringKrullDim_stalk_eq_coheight]
  have := WithBot.coe_le_coe.2 hc
  simpa using this

end GlobalTheory.LinearCodimTwo
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom : ∀ {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R') (A : Over (Sp R)) (W : A.left.Opens), IsAffineOpen W → (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) → ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧ ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  first | exact @GlobalTheory.affine_preimage_pullback_meets_fibres | exact GlobalTheory.affine_preimage_pullback_meets_fibres | (intros; apply GlobalTheory.affine_preimage_pullback_meets_fibres <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_basicOpen_affineOpen_meeting_fibres_grpScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R), ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens, IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))), ∃ x ∈ W, A.hom x = t := by
  first | exact @GlobalTheory.chartAroundUnit | exact GlobalTheory.chartAroundUnit | (intros; apply GlobalTheory.chartAroundUnit <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.residue_degree_generic_ne_zero_equidimensional : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) (n : ℕ), LocallyOfFiniteType p → LocallyOfFiniteType f → Surjective f → topologicalKrullDim M = n → topologicalKrullDim W = n → f.residueDegree (genericPoint M) ≠ 0 := by
  first | exact @GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero | (intros; apply GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DominantProjDegree

theorem residueDegree_ne_zero_of_map_genericPoint : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  intro k _ X Y _ _ p q D hp hq hX hY π hπ hη
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨M, j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str k N) := isProper_str k N
  haveI : IsProper (PSpace.str k M) := isProper_str k M
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (π ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper π := IsProper.of_comp π p
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  have hsurj : Surjective π := ⟨fun x => by
    have : genericPoint X ∈ Set.range π := ⟨_, hη⟩
    exact (genericPoint_specializes x).mem_closed hcl this⟩
  exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero k Y X p π D inferInstance inferInstance
    hsurj hY hX

end GlobalTheory.DominantProjDegree
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FunctionFieldTrdeg

theorem trdeg_functionField_eq : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (s : G ⟶ Sp F) (d : ℕ), IsProjOver s → topologicalKrullDim G = d → ∀ (φ : F →+* G.functionField), G.fromSpecStalk (genericPoint G) ≫ s = spMap φ → (letI := φ.toAlgebra; Algebra.trdeg F G.functionField = d) := by
  intro F _ G _ s d hs hd φ hφ
  obtain ⟨N, i, hi, hcomp⟩ := hs
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType s := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ s)
  have hψ : Spec.map ψ = hU.fromSpec ≫ s := Spec.map_preimage _
  letI : Algebra F Γ(G, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(G, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(G, U) = d :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F s hU ⟨_, hxU⟩ d hd
  letI : Algebra F G.functionField := φ.toAlgebra
  have key : CommRingCat.ofHom φ = ψ ≫ G.germToFunctionField U := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ = _
    rw [← hφ, hψ, ← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc]
  haveI : IsScalarTower F Γ(G, U) G.functionField :=
    IsScalarTower.of_algebraMap_eq' congr($(key).hom)
  haveI := functionField_isFractionRing_of_isAffineOpen G U hU
  haveI : FaithfulSMul F Γ(G, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(G, U)).injective
  haveI : FaithfulSMul Γ(G, U) G.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective Γ(G, U) G.functionField)
  haveI : Algebra.IsAlgebraic Γ(G, U) G.functionField := IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(G, U))
  show Algebra.trdeg F G.functionField = d
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top F Γ(G, U) G.functionField, hA]

end GlobalTheory.FunctionFieldTrdeg
end
end
