module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

section

open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.ExpChart.DualElements

theorem exists_det_ne_zero {X : Type} {g : ℕ} (w : X → Fin g → ℂ)
    (h : ∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * w x a = 0) → c = 0) :
    ∃ a : Fin g → X, (Matrix.of fun i j => w (a i) j).det ≠ 0 := by
  have hspan : Submodule.span ℂ (Set.range w) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hfx : ∀ y : Fin g → ℂ, f y = ∑ a, f (fun j => if a = j then 1 else 0) * y a := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul, mul_comm]
    have hc := h (fun a => f (fun j => if a = j then 1 else 0)) (fun x => by
      rw [← hfx]
      exact hf (Submodule.subset_span ⟨x, rfl⟩))
    refine LinearMap.ext fun y => ?_
    rw [hfx y, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun a _ => by
      rw [show f (fun j => if a = j then 1 else 0) = 0 from congrFun hc a, zero_mul]
  obtain ⟨b, hb, hbs, hli⟩ := exists_linearIndependent ℂ (Set.range w)
  let B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbs, hspan])
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = g := by
    rw [← Module.finrank_eq_card_basis B]
    simp
  let e : Fin g ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hex : ∀ i, ∃ x, w x = (e i : Fin g → ℂ) := fun i => hb (e i).2
  choose a ha using hex
  refine ⟨a, ?_⟩
  have hrow : LinearIndependent ℂ (Matrix.of fun i j => w (a i) j).row := by
    have hEq : (Matrix.of fun i j => w (a i) j).row = Subtype.val ∘ e := by
      ext i j
      simp [Matrix.row, ha]
    rw [hEq]
    exact hli.comp _ e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem exists_dual_elements :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (r : R) (g : ℕ)
      (E : A →+* Localization.Away r) (v : Fin g → (A →+* DualNumber (Localization.Away r)))
      (φ : Localization.Away r →+* ℂ),
      (∀ x : R, E (algebraMap R A x) = algebraMap R (Localization.Away r) x) →
      (∀ a (x : R), TrivSqZeroExt.snd (v a (algebraMap R A x)) = 0) →
      (∀ a x, TrivSqZeroExt.fst (v a x) = E x) →
      (∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * φ (TrivSqZeroExt.snd (v a x)) = 0) → c = 0) →
      ∃ (ρ : R) (t : Fin g → A), φ (algebraMap R (Localization.Away r) ρ) ≠ 0 ∧
        (∀ c, E (t c) = 0) ∧
        ∀ a c, TrivSqZeroExt.snd (v a (t c)) =
          if a = c then algebraMap R (Localization.Away r) ρ else 0 := by
  intro R A _ _ _ r g E v φ h1 h2 h3 h4
  let D : Fin g → A →+ Localization.Away r := fun a =>
    AddMonoidHom.mk' (fun x => TrivSqZeroExt.snd (v a x)) (fun x y => by
      rw [map_add (f := _), TrivSqZeroExt.snd_add])
  have hD : ∀ a x, D a x = TrivSqZeroExt.snd (v a x) := fun _ _ => rfl
  have hDmul : ∀ a x y, D a (x * y) = E x * D a y + E y * D a x := by
    intro a x y
    rw [hD, hD, hD, map_mul, TrivSqZeroExt.snd_mul, h3, h3, smul_eq_mul, op_smul_eq_mul, mul_comm (TrivSqZeroExt.snd (v a x))]
  have hDalg : ∀ a (s : R), D a (algebraMap R A s) = 0 := fun a s => h2 a s
  have hDs : ∀ a (s : R) x, D a (algebraMap R A s * x) =
      algebraMap R (Localization.Away r) s * D a x := by
    intro a s x
    rw [hDmul, hDalg, h1, mul_zero, add_zero]
  obtain ⟨a, ha⟩ := exists_det_ne_zero (X := A) (fun x i => φ (D i x)) h4
  obtain ⟨⟨b, hbm⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r) (fun c => E (a c))
  have hbu : IsUnit (algebraMap R (Localization.Away r) b) :=
    IsLocalization.map_units _ (⟨b, hbm⟩ : Submonoid.powers r)
  have hb' : ∀ c, ∃ s, algebraMap R (Localization.Away r) s =
      algebraMap R (Localization.Away r) b * E (a c) := fun c => by
    obtain ⟨s, hs⟩ := hb c
    exact ⟨s, by rw [hs, Algebra.smul_def]⟩
  choose s hs using hb'
  let t' : Fin g → A := fun c => algebraMap R A b * a c - algebraMap R A (s c)
  have hEt' : ∀ c, E (t' c) = 0 := by
    intro c
    simp only [t', map_sub, map_mul, h1, hs, sub_self]
  have hDt' : ∀ i c, D i (t' c) = algebraMap R (Localization.Away r) b * D i (a c) := by
    intro i c
    simp only [t', map_sub, hDs, hDalg, sub_zero]
  let N : Matrix (Fin g) (Fin g) (Localization.Away r) := Matrix.of fun c i => D i (t' c)
  have hN : φ N.det ≠ 0 := by
    have hN0 : N = algebraMap R (Localization.Away r) b •
        Matrix.of (fun c i => D i (a c)) := by
      ext c i
      simp [N, hDt']
    rw [hN0, Matrix.det_smul, map_mul, map_pow, RingHom.map_det]
    refine mul_ne_zero (pow_ne_zero _ (hbu.map φ).ne_zero) ?_
    have hM : φ.mapMatrix (Matrix.of fun c i => D i (a c)) =
        Matrix.of fun i j => φ (D j (a i)) := by
      ext i j
      simp
    rw [hM]
    exact ha
  obtain ⟨⟨b2, hb2m⟩, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r)
    (fun o : Option (Fin g × Fin g) => o.elim N.det (fun p => N.adjugate p.1 p.2))
  have hb2u : IsUnit (algebraMap R (Localization.Away r) b2) :=
    IsLocalization.map_units _ (⟨b2, hb2m⟩ : Submonoid.powers r)
  have hρ : ∃ ρ, algebraMap R (Localization.Away r) ρ =
      algebraMap R (Localization.Away r) b2 * N.det := by
    obtain ⟨s, hs⟩ := hb2 none
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  have hn : ∀ c c', ∃ n, algebraMap R (Localization.Away r) n =
      algebraMap R (Localization.Away r) b2 * N.adjugate c c' := fun c c' => by
    obtain ⟨s, hs⟩ := hb2 (some (c, c'))
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  obtain ⟨ρ, hρ⟩ := hρ
  choose n hn using hn
  refine ⟨ρ, fun c => ∑ c', algebraMap R A (n c c') * t' c', ?_, ?_, ?_⟩
  · rw [hρ, map_mul]
    exact mul_ne_zero (hb2u.map φ).ne_zero hN
  · intro c

    rw [map_sum]
    exact Finset.sum_eq_zero fun c' _ => by rw [map_mul, hEt', mul_zero]
  · intro i c

    rw [← hD, map_sum]
    have hsum : ∑ c', D i (algebraMap R A (n c c') * t' c') =
        algebraMap R (Localization.Away r) b2 * (N.adjugate * N) c i := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [hDs, hn, mul_assoc]
      rfl
    rw [hsum, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hic : i = c
    · subst hic
      simp [hρ]
    · simp [hic, Ne.symm hic]

end GlobalTheory.CompanionTheory.ExpChart.DualElements
end

section

namespace GlobalTheory.CompanionTheory.LocHom

variable {R : Type*} [CommRing R]

theorem isLocalizedModule_of_retract {M M' N N' : Type*} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [AddCommGroup N'] [Module R M] [Module R M'] [Module R N] [Module R N']
    (S : Submonoid R) (g : M →ₗ[R] M') (h : N →ₗ[R] N') [IsLocalizedModule S h]
    (i : M →ₗ[R] N) (j : N →ₗ[R] M) (i' : M' →ₗ[R] N') (j' : N' →ₗ[R] M')
    (hji : ∀ x, j (i x) = x) (hji' : ∀ x, j' (i' x) = x)
    (hi : ∀ x, h (i x) = i' (g x)) (hj : ∀ y, g (j y) = j' (h y)) :
    IsLocalizedModule S g := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [Module.End.isUnit_iff]
    have hu := IsLocalizedModule.map_units h s
    rw [Module.End.isUnit_iff] at hu
    constructor
    · intro x y hxy
      apply (show Function.Injective i' from fun a b e => by rw [← hji' a, ← hji' b, e])
      apply hu.1
      simp only [Module.algebraMap_end_apply] at hxy ⊢
      rw [← map_smul, ← map_smul, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hu.2 (i' y)
      refine ⟨j' z, ?_⟩
      simp only [Module.algebraMap_end_apply] at hz ⊢
      rw [← map_smul, hz, hji']
  · intro y
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj S h (i' y)
    refine ⟨⟨j x, s⟩, ?_⟩
    simp only at hx ⊢
    rw [hj, ← hx, Submonoid.smul_def, Submonoid.smul_def, map_smul, hji']
  · intro x₁ x₂ e
    have h0 : h (i x₁) = h (i x₂) := by rw [hi, hi, e]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) h0
    refine ⟨c, ?_⟩
    have h1 := congrArg j hc
    simpa only [Submonoid.smul_def, map_smul, hji] using h1

theorem map_away_smul {f : R} {P D : Type*} [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
    [CommRing D] [Algebra R D] (ρ : Localization.Away f →ₐ[R] D) (φ : P →ₗ[R] D)
    (a : Localization.Away f) (p : P) : φ (a • p) = ρ a * φ p := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers f) a
  simp only at hrs
  have hs : IsUnit (algebraMap R D s) := by
    have := (IsLocalization.map_units (Localization.Away f) s).map ρ
    rwa [AlgHom.commutes] at this
  have h1 : (s : R) • (a • p) = r • p := by
    rw [← algebraMap_smul (Localization.Away f) (s : R), ← algebraMap_smul (Localization.Away f) r,
      ← hrs, smul_smul, mul_comm]
  have h2 : (s : R) • φ (a • p) = r • φ p := by rw [← map_smul, h1, map_smul]
  rw [Algebra.smul_def, Algebra.smul_def] at h2
  have h3 := congrArg ρ hrs
  rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h3
  apply hs.mul_right_injective
  show algebraMap R D s * _ = algebraMap R D s * _
  linear_combination h2 - φ p * h3

section retraction

variable {A P D : Type*} [CommRing A] [Algebra R A] [AddCommGroup P] [Module R P]
  [CommRing D] [Algebra R D] {n : ℕ}

noncomputable def coord (s : P →ₗ[R] (Fin n → A)) (ρ : A →ₐ[R] D) (k : Fin n) : P →ₗ[R] D :=
  ρ.toLinearMap ∘ₗ LinearMap.proj k ∘ₗ s

noncomputable def assemble (s : P →ₗ[R] (Fin n → A)) (ρ : A →ₐ[R] D) :
    (Fin n → D) →ₗ[R] (P →ₗ[R] D) where
  toFun v := ∑ k, v k • coord s ρ k
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum, smul_assoc]

def evalAt (D : Type*) [CommRing D] [Algebra R D] (b : Fin n → P) :
    (P →ₗ[R] D) →ₗ[R] (Fin n → D) where
  toFun φ k := φ (b k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end retraction

theorem isLocalizedModule_compRight_away :
    ∀ (R P C C' : Type) [CommRing R] [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (f t : R) [AddCommGroup P] [Module R P]
      [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
      [Module.Finite (Localization.Away f) P]
      [Module.Projective (Localization.Away f) P], IsUnit (algebraMap R C f) →
      ∀ c : C →ₐ[R] C',
      IsLocalizedModule (Submonoid.powers t) c.toLinearMap →
      IsLocalizedModule (Submonoid.powers t)
        (LinearMap.compRight R c.toLinearMap : (P →ₗ[R] C) →ₗ[R] (P →ₗ[R] C')) := by
  intro R P C C' _ _ _ _ _ f t _ _ _ _ _ _ hf c hc
  have hunit : ∀ y : Submonoid.powers f, IsUnit ((Algebra.ofId R C) (y : R)) := by
    rintro ⟨_, k, rfl⟩
    simpa [Algebra.ofId_apply] using hf.pow k
  let ρ : Localization.Away f →ₐ[R] C := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ρ' : Localization.Away f →ₐ[R] C' := c.comp ρ
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (Localization.Away f) P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let s₀ : P →ₗ[R] (Fin n → Localization.Away f) := s.restrictScalars R
  let b : Fin n → P := fun k => π (fun j => if k = j then 1 else 0)
  have hexp : ∀ p : P, ∑ k, s p k • b k = p := by
    intro p
    have h1 := LinearMap.congr_fun hs p
    have h2 := LinearMap.pi_apply_eq_sum_univ π (s p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1] at h2
    exact h2.symm
  have hret : ∀ {D : Type} [CommRing D] [Algebra R D] (σ : Localization.Away f →ₐ[R] D)
      (φ : P →ₗ[R] D), assemble s₀ σ (evalAt D b φ) = φ := by
    intro D _ _ σ φ
    ext p
    conv_rhs => rw [← hexp p]

    simp [assemble, evalAt, coord, s₀, map_sum, map_away_smul σ, mul_comm]
  haveI : IsLocalizedModule (Submonoid.powers t)
      (LinearMap.pi fun k : Fin n => c.toLinearMap ∘ₗ LinearMap.proj k) :=
    IsLocalizedModule.pi (Submonoid.powers t) (fun _ : Fin n => c.toLinearMap)
  refine isLocalizedModule_of_retract (Submonoid.powers t) _
    (LinearMap.pi fun k : Fin n => c.toLinearMap ∘ₗ LinearMap.proj k)
    (evalAt C b) (assemble s₀ ρ) (evalAt C' b) (assemble s₀ ρ')
    (hret ρ) (hret ρ') ?_ ?_
  · intro φ
    rfl
  · intro v
    ext p

    simp [assemble, coord, ρ', map_sum]

end GlobalTheory.CompanionTheory.LocHom
end

section

namespace GlobalTheory.CompanionTheory.Ggeo

theorem finite_projective_of_isLocalizedModule_cover :
    ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : J → Type) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module (Localization.Away (f i)) (F i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (F i)] [∀ i, Module.Finite (Localization.Away (f i)) (F i)]
    [∀ i, Module.Projective (Localization.Away (f i)) (F i)] (φ : ∀ i, E →ₗ[R] F i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (φ i)) → Module.Finite R E ∧ Module.Projective R E := by
  intro R E _ _ _ J _ f hf F _ _ _ _ _ _ φ hφ
  have hex : ∀ g : Set.range f, ∃ i, f i = g.1 := fun g => g.2
  choose idx hidx using hex
  have hA : ∀ g : Set.range f, IsLocalization.Away g.1 (Localization.Away (f (idx g))) := by
    intro g
    rw [← hidx g]
    infer_instance
  have hL : ∀ g : Set.range f, IsLocalizedModule (Submonoid.powers g.1) (φ (idx g)) := by
    intro g
    rw [← hidx g]
    exact hφ _
  have hfp : Module.FinitePresentation R E :=
    Module.FinitePresentation.of_localizationSpan' (Set.range f) hf
      (Mₚ := fun g => F (idx g)) (Rₚ := fun g => Localization.Away (f (idx g)))
      (fun g => φ (idx g)) (fun g => Module.finitePresentation_of_projective _ _)
  have hflat : Module.Flat R E := by
    refine Module.flat_of_isLocalized_span (R := R) R E (Set.range f) hf (fun g => F (idx g))
      (fun g => φ (idx g)) (fun g => ?_)
    have : Module.Flat R (Localization.Away (f (idx g))) :=
      IsLocalization.flat _ (Submonoid.powers (f (idx g)))
    exact Module.Flat.trans R (Localization.Away (f (idx g))) (F (idx g))
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.CompanionTheory.Ggeo
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_pow_mul_unit_add_eq_zero_of_integral {K A : Type*} [Field K] [CommRing A]
    (φ : K →+* A) (a : A) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (u b : A), IsUnit u ∧ a ^ m * (u + a * b) = 0 := by
  obtain ⟨p, hp, hpa⟩ := ha
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hq0).map φ, ?_⟩
  have hsplit : p.eval₂ φ a = a ^ p.rootMultiplicity 0 * q.eval₂ φ a := by
    conv_lhs => rw [hpq]
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hq' : q.eval₂ φ a = φ (q.coeff 0) + a * q.divX.eval₂ φ a := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      add_comm]
  rw [← hq', ← hsplit, hpa]

theorem isUnit_of_pow_mul_unit_add_eq_zero (X : Scheme.{0}) [ConnectedSpace X]
    (a u b : Γ(X, ⊤)) (m : ℕ) (hu : IsUnit u) (h : a ^ m * (u + a * b) = 0)
    (hne : ((X.basicOpen a : X.Opens) : Set X).Nonempty) : IsUnit a := by
  have hcover : ∀ x : X, x ∈ X.basicOpen a ∨ x ∈ X.basicOpen (u + a * b) := by
    intro x
    rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
    by_cases hxa : IsUnit (X.presheaf.germ ⊤ x trivial a)
    · exact Or.inl hxa
    · right
      have hU : IsUnit (X.presheaf.germ ⊤ x trivial u) := hu.map _
      have hsum : X.presheaf.germ ⊤ x trivial u =
          X.presheaf.germ ⊤ x trivial (u + a * b) +
            -(X.presheaf.germ ⊤ x trivial a * X.presheaf.germ ⊤ x trivial b) := by
        rw [map_add (f := _), map_mul]; ring
      rw [hsum] at hU
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h1 | h1
      · exact h1
      · exact absurd (isUnit_of_mul_isUnit_left (IsUnit.neg_iff _ |>.1 h1)) hxa
  have hdisj : ∀ x : X, x ∈ X.basicOpen a → x ∈ X.basicOpen (u + a * b) → False := by
    intro x hxa hxg
    rw [Scheme.mem_basicOpen_top] at hxa hxg
    have hx : x ∈ X.basicOpen (a ^ m * (u + a * b)) := by
      rw [Scheme.mem_basicOpen_top, map_mul, map_pow]
      exact (hxa.pow m).mul hxg
    rw [h, Scheme.basicOpen_zero] at hx
    exact hx
  have hall : ∀ x : X, x ∈ X.basicOpen a := by
    intro x
    by_contra hx
    have hxg := (hcover x).resolve_left hx
    obtain ⟨y, -, hy1, hy2⟩ := isPreconnected_univ
      ((X.basicOpen a : X.Opens) : Set X) ((X.basicOpen (u + a * b) : X.Opens) : Set X)
      (X.basicOpen a).isOpen (X.basicOpen (u + a * b)).isOpen
      (fun z _ => hcover z) (by simpa using hne) ⟨x, Set.mem_univ _, hxg⟩
    exact hdisj y hy1 hy2
  exact X.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
    (fun x _ => (X.mem_basicOpen_top a x).1 (hall x))

theorem isUnit_of_basicOpen_nonempty_of_universallyClosed :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      [UniversallyClosed f] [ConnectedSpace X] (a : Γ(X, ⊤)),
      ((X.basicOpen a : X.Opens) : Set X).Nonempty → IsUnit a := by
  intro k _ X f _ _ a hne
  let F := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  obtain ⟨m, u, b, hu, h⟩ := exists_pow_mul_unit_add_eq_zero_of_integral F.hom a (hF a)
  exact isUnit_of_pow_mul_unit_add_eq_zero X a u b m hu h hne

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

def gapN {Ψ : Type} {N : ℕ} (ν : Ψ × Fin N → ℤ) : Option (Ψ × Fin N) → ℤ
  | none => 0
  | some p => ν p - if h : (p.2 : ℕ) + 1 < N then ν (p.1, ⟨p.2 + 1, h⟩) else 0

end GlobalTheory.CompanionTheory.Ar.ExRefEff
end
