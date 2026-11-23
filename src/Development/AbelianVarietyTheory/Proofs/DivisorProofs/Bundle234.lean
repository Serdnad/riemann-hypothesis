module

public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle127
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle128
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle131
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle132
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open IsDedekindDomain

theorem _root_.GlobalTheory.T.henselian_norm_lift : ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (τ : A →+* A), (∀ a, τ (τ a) = a) → IsUnit (2 : A) → (∀ a ∈ I, τ a ∈ I) → ∀ a t₀ : A, IsUnit a → τ a = a → IsUnit t₀ → t₀ * τ t₀ - a ∈ I → ∃ t : A, IsUnit t ∧ t * τ t = a := by
  first | (exact @GlobalTheory.hensel_norm_lift_of_involution) | (exact GlobalTheory.hensel_norm_lift_of_involution) | (intros; apply GlobalTheory.hensel_norm_lift_of_involution <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk : ∀ (A : Type) [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A), P * P = P →
    ∀ (k : Type) [Field k] (g : A →+* k),
      Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
        Module.rankAtStalk (LinearMap.range P.mulVecLin) (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  first | (exact @GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (exact GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (intros; apply GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.basis_quotient_tensor_base_change : ∀ (A B C R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J : Ideal (C ⊗[A] B)) (ψ : C →ₐ[A] R), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k))) = ⊤ := by
  first | (exact @GlobalTheory.quotient_basis_baseChange) | (exact GlobalTheory.quotient_basis_baseChange) | (intros; apply GlobalTheory.quotient_basis_baseChange  <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  first | (exact @GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (exact GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (intros; apply GlobalTheory.tensor_isLocalRing_of_unique_prime_over  <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.pushout_residue_linearIndependent' : ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by
  first | exact @GlobalTheory.pushout_residue_linearIndependent | exact GlobalTheory.pushout_residue_linearIndependent | (intros; apply GlobalTheory.pushout_residue_linearIndependent <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_unit_approximation_adic_completion : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M] [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N] (φ : M →ₐ[A] N), (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) → (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) → ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧ ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  first | exact @GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | exact GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal | (intros; apply GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_prime_le_comap_of_goingDown_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  first | exact @GlobalTheory.fibre_going_down_tensor | exact GlobalTheory.fibre_going_down_tensor | (intros; apply GlobalTheory.fibre_going_down_tensor <;> assumption)
end

section


theorem _root_.GlobalTheory.T.conj_dual_parts_killed_of_perfect_pairing : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  first | (exact @GlobalTheory.DualParts.conj_dual_parts) | (exact GlobalTheory.DualParts.conj_dual_parts) | (intros; apply GlobalTheory.DualParts.conj_dual_parts <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ideals_eq_of_span_independent : ∀ (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)), J₁ ≤ J₂ → Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k)) → J₁ = J₂ := by
  first | (exact @GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (exact GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (intros; apply GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent  <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isReduced_quot_tensor_of_reduced_mod_p : ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 → IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) → IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  first | exact @GlobalTheory.reduced_quot_tensor_of_reduced_modp | exact GlobalTheory.reduced_quot_tensor_of_reduced_modp | (intros; apply GlobalTheory.reduced_quot_tensor_of_reduced_modp <;> assumption)
end

section


theorem _root_.GlobalTheory.T.tensor_quotient_onto_and_injective_mod_ideal_pow : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  first | exact @GlobalTheory.quot_tensor_level | exact GlobalTheory.quot_tensor_level | (intros; apply GlobalTheory.quot_tensor_level <;> assumption)
end

section

universe u

theorem _root_.GlobalTheory.T.exists_eigen_idempotents_of_comaximal : ∀ {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
  (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∃ e : Fin a → Module.End C W,
    (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
    (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
    (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  first | exact @GlobalTheory.eigenIdempotents_of_comaximal | exact GlobalTheory.eigenIdempotents_of_comaximal | (intros; apply GlobalTheory.eigenIdempotents_of_comaximal <;> assumption)
end
