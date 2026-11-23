module

public import Mathlib.Analysis.Matrix.Spectrum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle059
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypes
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle004
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle005
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle003
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle006
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

section

open NumberField GlobalTheory.LKTrip
open scoped TensorProduct Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

def extZero (s : Fin n → Prop) [DecidablePred s] : ({i // s i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun w i := if hi : s i then w ⟨i, hi⟩ else 0
  map_add' a b := by funext i; by_cases hi : s i <;> simp [hi]
  map_smul' r a := by funext i; by_cases hi : s i <;> simp [hi]

theorem extZero_apply_mem (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) (i : {i // s i}) :
    extZero s w i = w i := by simp [extZero, i.2]

theorem extZero_apply_not (s : Fin n → Prop) [DecidablePred s] (w : {i // s i} → ℂ) {i : Fin n} (hi : ¬ s i) :
    extZero s w i = 0 := by simp [extZero, hi]

theorem quad_mulVec (h X : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    star (X *ᵥ u) ⬝ᵥ h *ᵥ (X *ᵥ u) = star u ⬝ᵥ (Xᴴ * h * X) *ᵥ u := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem re_quad_ext (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (s : Fin n → Prop) [DecidablePred s]
    (w : {i // s i} → ℂ) :
    (star ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w) ⬝ᵥ
        h *ᵥ ((hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ extZero s w)).re =
      ∑ i, hh.eigenvalues i * Complex.normSq (extZero s w i) := by
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh, Matrix.mulVec_mulVec,
    Matrix.mem_unitaryGroup_iff'.mp hh.eigenvectorUnitary.2, Matrix.one_mulVec]

theorem finrank_le_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (S : Submodule ℂ (Fin n → ℂ))
    (hS : ∀ u ∈ S, u ≠ 0 → 0 < (star u ⬝ᵥ h *ᵥ u).re) :
    Module.finrank ℂ S ≤ Fintype.card {i : Fin n // 0 < hh.eigenvalues i} := by
  refine GlobalTheory.SylvesterInertia.finrank_le_card_of_vanish
    (star (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) S _ fun u hu hv => ?_
  by_contra hne
  have hpos := hS u hu hne
  rw [GlobalTheory.SylvesterInertia.re_quad_eq_sum h hh u] at hpos
  refine absurd hpos (not_lt.mpr (Finset.sum_nonpos fun i _ => ?_))
  by_cases hi : 0 < hh.eigenvalues i
  · rw [hv i hi, map_zero, mul_zero]
  · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hi) (Complex.normSq_nonneg _)

end GlobalTheory.SimSign

namespace GlobalTheory.SimSign

open Matrix

variable {n : ℕ}

theorem sum_pos (h : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (w : {i // 0 < hh.eigenvalues i} → ℂ)
    (hw : w ≠ 0) : 0 < ∑ i, hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i ≤ hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    intro i _
    by_cases hi : 0 < hh.eigenvalues i
    · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
    · rw [extZero_apply_not _ w hi]; simp
  have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      (0 : Fin n → ℝ) i < hh.eigenvalues i * Complex.normSq (extZero (fun i => 0 < hh.eigenvalues i) w i) := by
    refine ⟨j.1, Finset.mem_univ _, ?_⟩
    rw [extZero_apply_mem]
    exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
  simpa using Finset.sum_lt_sum hle hlt

end GlobalTheory.SimSign

namespace GlobalTheory.HTBetti

end GlobalTheory.HTBetti

end
end

section

open NumberField Filter Topology

noncomputable section

namespace GlobalTheory.Proof.IdempotentLatticeSequence

theorem norm_int_le {p : ℕ} [Fact p.Prime] {M : Type} [Field M] (φ : M →+* ℂ_[p]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  obtain ⟨P, hmon, hev⟩ := RingOfIntegers.isIntegral_coe a
  have key : ∀ f : ℤ →+* ℂ_[p], Polynomial.eval₂ f (φ (a : M)) P = 0 := fun f => by
    rw [RingHom.ext_int f (φ.comp (algebraMap ℤ M)), ← Polynomial.hom_eval₂, hev, map_zero]
  exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral ⟨P, hmon, key _⟩

theorem flat_system {A B : Type} [CommRing A] [AddCommGroup B] [Module A B] [Module.Flat A B] {κ J : Type}
    [Fintype κ] [Fintype J] (b : κ → J → A) (r : κ → B) (h : ∀ j, ∑ k, b k j • r k = 0) :
    ∃ (n : ℕ) (a : κ → Fin n → A) (y : Fin n → B), (∀ k, r k = ∑ l, a k l • y l) ∧ ∀ l j, ∑ k, b k j * a k l = 0 := by
  classical
  let f : (J → A) →ₗ[A] (κ → A) := Matrix.mulVecLin (Matrix.of fun k j => b k j)
  let x : (κ → A) →ₗ[A] B := Fintype.linearCombination A r
  have hxf : x ∘ₗ f = 0 := by
    refine LinearMap.ext fun c => ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, x, f, Fintype.linearCombination_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp_rw [mul_comm (b _ j) (c j), mul_smul]
    rw [← Finset.smul_sum, h j, smul_zero]
  obtain ⟨n, a', y', hxa, haf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  refine ⟨n, fun k l => a' (Pi.single k 1) l, fun l => y' (Finsupp.single l 1), fun k => ?_, fun l j => ?_⟩
  · have hr : r k = x (Pi.single k 1) := by
      simp [x, Fintype.linearCombination_apply, Pi.single_apply]
    rw [hr, hxa, LinearMap.comp_apply]
    conv_lhs => rw [← Finsupp.univ_sum_single (a' (Pi.single k 1))]

    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finsupp.smul_single_one, map_smul]
  · have h1 := congrArg (fun v => v l) (LinearMap.congr_fun haf (Pi.single j 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
    have hf : f (Pi.single j 1) = ∑ k, b k j • Pi.single k 1 := by
      ext k'
      simp [f, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]

    rw [hf, map_sum] at h1
    simpa [Finsupp.finsetSum_apply, map_smul] using h1

def primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : Ideal (𝓞 E) where
  carrier := {a | ‖φ (a : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    rw [map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  smul_mem' := fun c a ha => by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le φ c)).trans_lt ha

theorem mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) (a : 𝓞 E) :
    a ∈ primeOf φ ↔ ‖φ (algebraMap (𝓞 E) E a)‖ < 1 := by
  exact Iff.rfl

theorem natCast_mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) :
    (p : 𝓞 E) ∈ primeOf φ := by
  rw [mem_primeOf]
  have h1 : ‖((p : ℚ_[p]) : ℂ_[p])‖ < 1 := by
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  simpa using h1

theorem primeOf_isPrime {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : (primeOf φ).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one, mem_primeOf]
    simp
  · rw [mem_primeOf, map_mul, map_mul, norm_mul] at hab
    rw [mem_primeOf, mem_primeOf]
    have ha : ‖φ (algebraMap (𝓞 E) E a)‖ ≤ 1 := norm_int_le φ a
    have hb : ‖φ (algebraMap (𝓞 E) E b)‖ ≤ 1 := norm_int_le φ b
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    nlinarith [h.1, h.2, norm_nonneg (φ (algebraMap (𝓞 E) E a))]

theorem primeOf_isMaximal {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) :
    (primeOf φ).IsMaximal := by
  refine (primeOf_isPrime φ).isMaximal ?_
  intro h
  have hp := natCast_mem_primeOf φ
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

end GlobalTheory.Proof.IdempotentLatticeSequence
end
end

section


theorem _root_.GlobalTheory.T.isCompl_orthogonal_of_no_common_irreducible_types : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by
  first | exact @GlobalTheory.IsotypicOrth.orth_isCompl | exact GlobalTheory.IsotypicOrth.orth_isCompl | (intros; apply GlobalTheory.IsotypicOrth.orth_isCompl <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_complement_without_common_irreducible_types : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  first | exact @GlobalTheory.TypeComplement.exists_typeComplement | exact GlobalTheory.TypeComplement.exists_typeComplement | (intros; apply GlobalTheory.TypeComplement.exists_typeComplement <;> assumption)
end

section


theorem _root_.GlobalTheory.T.gl_hom_nnreal_trivial_of_scalar_trivial : ∀ (k : Type) [Field k], (∃ x : k, x ≠ 0 ∧ x ≠ 1) → ∀ (N : ℕ) (φ : GL (Fin N) k →* NNReal), (∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) → ∀ g, φ g = 1 := by
  first | exact @GlobalTheory.gl_hom_nnreal_trivial_of_scalar | exact GlobalTheory.gl_hom_nnreal_trivial_of_scalar | (intros; apply GlobalTheory.gl_hom_nnreal_trivial_of_scalar <;> assumption)
end

section


theorem _root_.GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Injective EF → ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  first | (exact @GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (exact GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (intros; apply GlobalTheory.bilinForm_injective_exists_mul_mem_range  <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.GL_inv_mul_congr_one_mod_uniformizer : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K), π ≠ 0 → Valued.v π < 1 →
  ∀ (a a₁ : GL (Fin N) K), (∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    (∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 := by
  first | exact @GlobalTheory.GL_inv_mul_congr_one | exact GlobalTheory.GL_inv_mul_congr_one | (intros; apply GlobalTheory.GL_inv_mul_congr_one <;> assumption)
end

section

namespace GlobalTheory.UnipNormalTrace

open Module

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem isNilpotent_of_trace_pow_eq_zero {K : Type} [Field K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (h : ∀ k, 1 ≤ k → LinearMap.trace K V (f ^ k) = 0) : IsNilpotent f := by
  first
  | exact @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow
  | (apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentOfTracePowers.isNilpotent_of_trace_pow ..)

end GlobalTheory.UnipNormalTrace
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | exact GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | (intros; apply GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_finset_sum_lt_of_forall_lt {K : Type*} [NormedField K] [IsUltrametricDist K]
    (s : Finset ℕ) (f : ℕ → K) {r : ℝ} (hr : 0 < r) (h : ∀ i ∈ s, ‖f i‖ < r) :
    ‖∑ i ∈ s, f i‖ < r := by
  first
  | exact @_root_.GlobalTheory.NormSumLt.main
  | exact _root_.GlobalTheory.NormSumLt.main
  | (apply _root_.GlobalTheory.NormSumLt.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormSumLt.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormSumLt.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormSumLt.main ..)

theorem norm_le_one_of_isIntegral_int {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z : K} (hz : IsIntegral ℤ z) : ‖z‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hz
  by_contra hlt
  push_neg at hlt
  set n := p.natDegree
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree,
    hm.leadingCoeff, map_one, one_mul] at hp
  set S := ∑ i ∈ Finset.range n, (algebraMap ℤ K) (p.coeff i) * z ^ i
  have hS : ‖S‖ < ‖z‖ ^ n := by
    refine norm_finset_sum_lt_of_forall_lt _ _ (pow_pos (by linarith) n) ?_
    intro i hi
    rw [norm_mul, norm_pow]
    have h1 : ‖(algebraMap ℤ K) (p.coeff i)‖ ≤ 1 := by
      rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one K _
    calc ‖(algebraMap ℤ K) (p.coeff i)‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) _)
      _ = ‖z‖ ^ i := one_mul _
      _ < ‖z‖ ^ n := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  have h2 : z ^ n = -S := by linear_combination hp
  have h3 : ‖z‖ ^ n = ‖S‖ := by rw [← norm_pow, h2, norm_neg]
  linarith

theorem exists_embedding_padicAlgCl_place (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] : ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)),
      ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  let τ : E →+* PadicAlgCl l := (IsAlgClosed.lift : E →ₐ[ℚ] PadicAlgCl l).toRingHom
  have hle : ∀ x : 𝓞 E, ‖τ (x : E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral_int ((x.isIntegral_coe).map τ.toIntAlgHom)
  let I : Ideal (𝓞 E) :=
    { carrier := {x | ‖τ (x : E)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        push_cast
        rw [map_mul, norm_mul]
        calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
              mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hx }
  have hmem : ∀ x : 𝓞 E, x ∈ I ↔ ‖τ (x : E)‖ < 1 := fun x => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro x y hxy
      rw [hmem] at hxy
      rw [hmem, hmem]
      by_contra h
      push_neg at h
      have : 1 ≤ ‖τ ((x * y : 𝓞 E) : E)‖ := by
        push_cast
        rw [map_mul, norm_mul]
        exact one_le_mul_of_one_le_of_one_le h.1 h.2
      linarith
  have hne : I ≠ ⊥ := by
    intro hbot
    have hl : ((l : 𝓞 E)) ∈ I := by
      rw [hmem]
      have h1 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
      rw [h1, map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l,
        PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    rw [hbot, Ideal.mem_bot] at hl
    have h2 : ((l : 𝓞 E) : E) = 0 := by rw [hl]; rfl
    have h3 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
    rw [h3] at h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  exact ⟨τ, ⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 → ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N → v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_pow_valuation_div_sub_one_le | exact GlobalTheory.exists_pow_valuation_div_sub_one_le | (intros; apply GlobalTheory.exists_pow_valuation_div_sub_one_le <;> assumption)
end

section

open NumberField IsDedekindDomain WithZero

theorem _root_.GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ), ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by
  first | exact @GlobalTheory.ordIdeal_of_embedding | exact GlobalTheory.ordIdeal_of_embedding | (intros; apply GlobalTheory.ordIdeal_of_embedding <;> assumption)
end
