module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle038
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle007
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle008
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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

@[expose] public section

section

open NumberField

theorem _root_.GlobalTheory.T.exists_integral_generator_common_denom_of_isQuadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧ ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_exists_integral_generator_common_denominator | exact GlobalTheory.quadratic_exists_integral_generator_common_denominator | (intros; apply GlobalTheory.quadratic_exists_integral_generator_common_denominator <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegRam

theorem not_isUnramifiedAt_of_sq_eq_neg :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime →
      ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  intro E K _ _ _ _ _ p hp hd δ hδ w hpw hunr
  have hmax := w.isMaximal
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E)) := by
    refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hpw
  have h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hunr
  have h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hv
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]
  have hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 h3
  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    have : (-(p : K)) = algebraMap ℤ K (-(p : ℤ)) := by simp
    rw [this]
    exact isIntegral_algebraMap
  set y : 𝓞 K := ⟨δ, hint⟩ with hy
  have hy2 : y ^ 2 = (p : 𝓞 K) * (-1) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))
    rw [map_pow, map_mul, map_neg, map_one, map_natCast]
    change δ ^ 2 = _
    rw [hδ]; ring
  have hu : (-1 : 𝓞 K) ∉ w.asIdeal := by
    intro h
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))
  exact GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2

end GlobalTheory.SqrtNegRam
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_residueClass_near_real_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (m : Ideal (𝓞 F)) (a₀ : 𝓞 F), m ≠ ⊥ → ∃ C : ℝ, ∀ y : (F →+* ℝ) → ℝ, ∃ a : 𝓞 F, a - a₀ ∈ m ∧ ∀ τ : F →+* ℝ, |τ (a : F) - y τ| ≤ C := by
  first | exact @GlobalTheory.residueClass_relativelyDense | exact GlobalTheory.residueClass_relativelyDense | (intros; apply GlobalTheory.residueClass_relativelyDense <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 := by
  first | exact @GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | exact GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | (intros; apply GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.infinitePlace_eq_of_embedding_comp_algebraMap_eq' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E), w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E) → w₁ = w₂ := by
  first | exact @GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | exact GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | (intros; apply GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective : ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) → ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  first | exact @GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | exact GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective | (intros; apply GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective <;> assumption)
end

section


theorem _root_.GlobalTheory.T.residue_degree_one_of_linear_mem' : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  first | exact @GlobalTheory.residue_degree_one_of_linear_mem | exact GlobalTheory.residue_degree_one_of_linear_mem | (intros; apply GlobalTheory.residue_degree_one_of_linear_mem <;> assumption)
end

section

open Pointwise

theorem _root_.GlobalTheory.T.length_le_of_forall_fg_submodule_length_le : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞), (∀ N : Submodule O M, N.FG → Module.length O N ≤ b) → Module.length O M ≤ b := by
  first | exact @GlobalTheory.length_le_of_forall_fg_length_le | exact GlobalTheory.length_le_of_forall_fg_length_le | (intros; apply GlobalTheory.length_le_of_forall_fg_length_le <;> assumption)
end

section

open Pointwise

theorem _root_.GlobalTheory.T.length_quotient_smul_sup_le_intermediate : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (Z B B' : Submodule O A) (a : O), B ≤ B' → Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤ Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id : (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) + Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  first | exact @GlobalTheory.length_quotient_smul_sup_le | exact GlobalTheory.length_quotient_smul_sup_le | (intros; apply GlobalTheory.length_quotient_smul_sup_le <;> assumption)
end

section

open Pointwise

theorem _root_.GlobalTheory.T.length_quotient_span_pow_le_mul_length : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ), Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  first | exact @GlobalTheory.main | exact GlobalTheory.main | (intros; apply GlobalTheory.main <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent : ∀ {B A : Type} [inst : CommRing B] [IsDomain B] [inst_2 : CommRing A] [inst_3 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ}, Module.finrank B A = d → ∀ (y : Fin d → A), LinearIndependent B y → ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | exact GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero : ∀ {k B A : Type} [inst : Field k] [Infinite k] [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra k B] [inst_5 : CommRing A] [inst_6 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ} (y : Fin d → A), (∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) → ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_field_combination_norm_ne_zero | exact GlobalTheory.exists_field_combination_norm_ne_zero | (intros; apply GlobalTheory.exists_field_combination_norm_ne_zero <;> assumption)
end
