module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle089
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle118
public import Mathlib.RingTheory.Ideal.Cotangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle144
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOfDimOne
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem quotient_base_change_invariant_derivations :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  intro O A _ _ _ I d l hl
  set S := O ⧸ I
  set B := S ⊗[O] A
  let ε := Bialgebra.counitAlgHom S B
  let Δ := Bialgebra.comulAlgHom S B
  have hεt : ∀ (s : S) (a : A), ε (s ⊗ₜ a) = Coalgebra.counit (R := O) a • s := by
    intro s a
    show Coalgebra.counit (R := S) (s ⊗ₜ[O] a) = _
    rw [TensorProduct.counit_tmul]
    rfl
  have hε : (∀ b : B, TensorProduct.lid S B (LinearMap.rTensor B ε.toLinearMap (Δ b)) = b) ∧
      (∀ b : B, TensorProduct.rid S B (LinearMap.lTensor B ε.toLinearMap (Δ b)) = b) := by
    constructor
    · intro b
      have := Coalgebra.rTensor_counit_comul (R := S) b
      show TensorProduct.lid S B (LinearMap.rTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
    · intro b
      have := Coalgebra.lTensor_counit_comul (R := S) b
      show TensorProduct.rid S B (LinearMap.lTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
  have key : ∀ i, ∃ D : Derivation S B B, ∀ b, ε (D b) = LinearMap.liftBaseChange S (l i) b := by
    intro i
    refine invariant_derivation_exists S B ε Δ hε (LinearMap.liftBaseChange S (l i)) ?_
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hεt, hεt]
        rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.liftBaseChange_tmul, hl]
        simp only [smul_eq_mul, smul_add, Algebra.smul_def]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
      ring
  choose D hD using key
  refine ⟨D, fun i a => ?_⟩
  rw [hD, LinearMap.liftBaseChange_tmul, one_smul]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.dedekind_power_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (exact GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (intros; apply GlobalTheory.dedekind_pow_maximal_mul_mem_span <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_surjective_pi_quotient_pow_ker_eq : ∀ {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A), P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d → ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧ ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  first | (exact @GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (exact GlobalTheory.exists_surj_pi_quot_pow_ker_eq) | (intros; apply GlobalTheory.exists_surj_pi_quot_pow_ker_eq  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_card_torsion_quot_smul_top_le_pow_finrank : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] (I J : Ideal R), I.IsMaximal → Finite (R ⧸ I) → J ≠ ⊥ → Finite {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ∧ Nat.card {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ≤ Nat.card (R ⧸ I) ^ Module.finrank R M := by
  first | exact @GlobalTheory.TorsionCount.torsion_card | exact GlobalTheory.TorsionCount.torsion_card | (intros; apply GlobalTheory.TorsionCount.torsion_card <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_pow_apply_mem_smul_univ_of_torsion : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M] (I J : Ideal R) (f : M →ₗ[R] M) (m : ℕ), I.IsMaximal → J ≠ ⊥ → (∀ x, (f ^ m) x ∈ I • (⊤ : Submodule R M)) → ∃ j : ℕ, ∀ y : M, (∀ a ∈ I, a • y ∈ J • (⊤ : Submodule R M)) → (f ^ j) y ∈ J • (⊤ : Submodule R M) := by
  first | exact @GlobalTheory.pow_maps_torsion_into_smul_top | exact GlobalTheory.pow_maps_torsion_into_smul_top | (intros; apply GlobalTheory.pow_maps_torsion_into_smul_top <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isolate_maximal_among_primes_containing_etale : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (Q : Ideal D), Q.IsMaximal → ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q := by
  first | (exact @GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (exact GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (intros; apply GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing  <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_derivation_extending_cotangent_form : ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  first | exact @GlobalTheory.ConormalDer.exists_derivation_extending | exact GlobalTheory.ConormalDer.exists_derivation_extending | (intros; apply GlobalTheory.ConormalDer.exists_derivation_extending <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.derivation_normalise_family | exact GlobalTheory.derivation_normalise_family | (intros; apply GlobalTheory.derivation_normalise_family <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FormalOrigin

def iterOp {A : Type} {n : ℕ} (ds : Fin n → A → A) (α : Fin n →₀ ℕ) (f : A) : A :=
  (List.finRange n).foldr (fun i g => (ds i)^[α i] g) f

def taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B) (ds : Fin n → A → A)
    (f : A) : MvPowerSeries (Fin n) B :=
  fun α => (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f)

section Origin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

def origin : G.left := (η[G]).left (IsLocalRing.closedPoint R)

def evO : G.left.presheaf.stalk (origin G) →+* R :=
  (Scheme.stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left).hom

def constO : R →+* G.left.presheaf.stalk (origin G) :=
  (G.left.presheaf.germ ⊤ (origin G) trivial).hom.comp
    ((G.hom.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
end Origin

def intDer {S A : Type} [CommRing S] [CommRing A] [Algebra S A] (δ : Derivation S A A) : Derivation ℤ A A where
  toFun := δ
  map_add' := map_add δ
  map_smul' m x := by simpa using map_zsmul δ m x
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

theorem iterOp_zero {A : Type} {n : ℕ} (ds : Fin n → A → A) (f : A) : iterOp ds 0 f = f := by
  unfold iterOp
  induction (List.finRange n) with
  | nil => rfl
  | cons i l ih => simpa using ih
end GlobalTheory.FormalOrigin
end
end

section


theorem _root_.GlobalTheory.T.dvr_exists_unit_pow_eq_mul_uniformizer : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V], Function.Injective (algebraMap T V) →
    ∀ (α : V) (ϖ u : T) (m k : ℕ), Irreducible ϖ → IsUnit u → 0 < k →
    α ^ (m * k) = algebraMap T V (u * ϖ ^ k) →
    ∃ γ : V, IsUnit γ ∧ α ^ m = γ * algebraMap T V ϖ ∧ γ ^ k = algebraMap T V u := by
  first | (exact @GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif) | (exact GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif) | (intros; apply GlobalTheory.dvr_pow_mul_eq_unit_mul_pow_unif  <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.subring_eq_univ_of_uniformizer_generates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (S : Subring V) (π : V), π ∈ S → π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V → (∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1) → (∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) → (∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) → S = ⊤ := by
  first | exact @GlobalTheory.dvrSubring_eq_top | exact GlobalTheory.dvrSubring_eq_top | (intros; apply GlobalTheory.dvrSubring_eq_top <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.PropDvr

theorem exists_cdvr_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (I : Type) [Finite I] (a : I → R) (k : I → ℕ), (∀ i, Associated (ψ (a i)) (ϖ ^ k i)) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W) (ψ' : R →+* W) (m m' : ℕ) (k' : I → ℕ), IsAdicComplete (maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧ IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧ ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  first
  | exact @_root_.GlobalTheory.CompleteDiscreteValuationRing.main
  | exact _root_.GlobalTheory.CompleteDiscreteValuationRing.main
  | (apply _root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompleteDiscreteValuationRing.main ..)

end GlobalTheory.PropDvr
end
