module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle012
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle015
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle016
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle017
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibMdisc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.exists_descended_ringHom_on_quotient : ∀ (O : Type) [Ring O] (g g' : ℕ) (B : O →+* Module.End ℂ (Fin g → ℂ)) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q → (∀ (a : O) z, q z = 0 → q (B a z) = 0) → ∃ B' : O →+* Module.End ℂ (Fin g' → ℂ), ∀ a z, B' a (q z) = q (B a z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection | exact GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUniv.ringAction_descends_along_surjection <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.holomorphic_local_quotient_map : ∀ (g' k g n : ℕ) (U : Set (Fin n → ℂ)) (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen U → t₀ ∈ U → k + g' = g → (∀ i, DifferentiableOn ℂ (e i) U) → LinearIndependent ℂ (fun i => e i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧ ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧ ∀ t ∈ V, Function.Surjective (q t) ∧ LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient | exact GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient | (intros; apply GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.linearIndependent_complex_of_real_hermitian : ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℝ u → (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → LinearIndependent ℂ u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RealFormIndep.linearIndependent_complex_of_real_form | exact GlobalTheory.CompanionTheory.Ar.RealFormIndep.linearIndependent_complex_of_real_form | (intros; apply GlobalTheory.CompanionTheory.Ar.RealFormIndep.linearIndependent_complex_of_real_form <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.mem_span_of_real_combination_periods : ∀ (g k n : ℕ) (Λ : Type) [AddCommGroup Λ] (P : Λ →+ (Fin g → ℂ)) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n), LinearIndependent ℝ (fun j => P (b j)) → Function.Injective f → ∀ (x : Λ) (c : Fin k → ℝ), P x = ∑ i, (c i : ℂ) • P (b (f i)) → x ∈ Submodule.span ℤ (Set.range fun i => b (f i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb | exact GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.mem_span_part_of_period_real_comb <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.monge_ampere_density_diagonal_levi : ∀ (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ), ContDiffAt ℝ 2 φ z → (∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) → maDens (fun _ => φ) z = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | exact GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MaDiag.maDens_diag_levi <;> assumption)
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.levi_flat_separately_harmonic : ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O → (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i, InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | exact GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.exists_real_orthogonal_projection_of_real_gram : ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u → (∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ, ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0) → (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → ∀ z : Fin g → ℂ, (∀ j, (z ⬝ᵥ Hm *ᵥ star (u j)).im = 0) → ∃ c : Fin k → ℝ, ∀ j, (z - ∑ i, (c i : ℂ) • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ProjReal.orthogonal_projection_real_coefficients | exact GlobalTheory.CompanionTheory.Ar.ProjReal.orthogonal_projection_real_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.ProjReal.orthogonal_projection_real_coefficients <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.exists_hermitian_orthogonal_projection : ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u → ∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ, ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients | exact GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.PosFormProjection.exists_orthogonal_coefficients <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.exists_posDef_form_on_quotient : ∀ (g g' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ (S : Submodule ℂ (Fin g → ℂ)) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q → LinearMap.ker q = S → (∀ z : Fin g → ℂ, ∃ s ∈ S, ∀ v ∈ S, (z - s) ⬝ᵥ Hm *ᵥ star v = 0) → ∃ Hm' : Matrix (Fin g') (Fin g') ℂ, Hm'.IsHermitian ∧ (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) ∧ ∀ x y : Fin g → ℂ, (∀ v ∈ S, x ⬝ᵥ Hm *ᵥ star v = 0) → q y ⬝ᵥ Hm' *ᵥ star (q x) = y ⬝ᵥ Hm *ᵥ star x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUniv.hermitian_transport_along_orthogonal_complement | exact GlobalTheory.CompanionTheory.Ar.QuotUniv.hermitian_transport_along_orthogonal_complement | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUniv.hermitian_transport_along_orthogonal_complement <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.QuadFin

theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add (f := _)]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add (f := _), map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

theorem not_sq_eq_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (b : ℚ)
    (h : (p : ℚ) = q * b ^ 2) : False := by
  haveI := Fact.mk hq
  have hb : b ≠ 0 := by
    rintro rfl
    have h0 : (p : ℚ) = 0 := by rw [h]; ring
    exact hp.ne_zero (by exact_mod_cast h0)
  have h1 := congrArg (padicValRat q) h
  rw [padicValRat.mul (by exact_mod_cast hq.ne_zero) (pow_ne_zero 2 hb), padicValRat.pow b,
    padicValRat.self hq.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd] at h1
  · push_cast at h1
    omega
  · intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm

theorem false_of_sq_eq {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (x : E) (hx : x ^ 2 = -(q : E)) (a b : ℚ)
    (h : (algebraMap ℚ E a + algebraMap ℚ E b * x) ^ 2 = -(p : E)) : False := by
  have hφ : Function.Injective (algebraMap ℚ E) := (algebraMap ℚ E).injective
  have key : algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) + algebraMap ℚ E (2 * a * b) * x = 0 := by
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    linear_combination h - algebraMap ℚ E b ^ 2 * hx
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases hab : 2 * a * b = 0
  · rw [hab, map_zero, zero_mul, add_zero, map_eq_zero_iff _ hφ] at key
    rcases mul_eq_zero.mp hab with h2a | hb
    · have ha : a = 0 := by linarith
      subst ha
      exact not_sq_eq_of_prime hp hq hpq b (by linear_combination key)
    · subst hb
      nlinarith [sq_nonneg a]
  · have hne : algebraMap ℚ E (2 * a * b) ≠ 0 := (map_ne_zero _).mpr hab
    have hx' : x = -algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) / algebraMap ℚ E (2 * a * b) :=
      eq_div_of_mul_eq hne (by linear_combination key)
    rw [← map_neg, ← map_div₀] at hx'
    rw [hx', ← map_pow, show -(q : E) = algebraMap ℚ E (-(q : ℚ)) by rw [map_neg, map_natCast]] at hx
    have h2 := hφ hx
    nlinarith [sq_nonneg (-(a ^ 2 - q * b ^ 2 + p) / (2 * a * b))]

theorem finite_primes_of_finiteDimensional (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)}.Finite := by
  classical
  haveI : Finite (IntermediateField ℚ E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField ℚ E).mp
      ⟨inferInstance, Field.exists_primitive_element ℚ E⟩
  have key : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : E, x ^ 2 = -(p : E) → y ^ 2 = -(q : E) →
      IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {y} → p = q := by
    intro p q hp hq x y hx hy he
    by_contra hpq
    have hmem : x ∈ IntermediateField.adjoin ℚ {y} := by
      rw [← he]
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    obtain ⟨a, b, hab⟩ :=
      exists_eq_add_mul_of_mem_adjoin y (-(q : ℚ)) (by rw [hy, map_neg, map_natCast]) hmem
    exact false_of_sq_eq hp hq hpq y hy a b (by rw [← hab]; exact hx)
  have hinj : Function.Injective (fun p : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)} =>
      IntermediateField.adjoin ℚ {Classical.choose p.2.2}) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ he
    exact Subtype.ext (key p q hp.1 hq.1 _ _ (Classical.choose_spec hp.2) (Classical.choose_spec hq.2) he)
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

theorem finite_primes_field (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [Algebra.EssFiniteType ℚ F] : {p : ℕ | p.Prime ∧ ∃ x : F, x ^ 2 = -(p : F)}.Finite := by
  have hfd := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType ℚ F
  refine (@finite_primes_of_finiteDimensional (algebraicClosure ℚ F) _ _ (algebraicClosure ℚ F).algebra' hfd).subset ?_
  rintro p ⟨hp, x, hx⟩
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C (-(p : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hx]⟩
  have hmem : x ∈ algebraicClosure ℚ F := mem_algebraicClosure_iff'.mpr hint
  exact ⟨hp, ⟨x, hmem⟩, Subtype.ext (by simp [hx])⟩

theorem finite_primes_of_isFractionRing (A F : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] [Field F] [Algebra A F] [IsFractionRing A F] :
    {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)
  haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ A F
  haveI : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F
  refine (finite_primes_field F).subset ?_
  rintro p ⟨hp, a, b, hb, hab⟩
  have hb' : algebraMap A F b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A F (by rw [h0, map_zero]))
  refine ⟨hp, algebraMap A F a / algebraMap A F b, ?_⟩
  have e := congrArg (algebraMap A F) hab
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_zero] at e
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hb')]
  linear_combination e

theorem finite_primes_neg_sq : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  intro σ _ A _ _ _ f hf
  haveI : Algebra.FiniteType ℤ A := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
    refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr
      ⟨n, MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i))), ?_⟩
    have hcomp : ((MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i)))).toRingHom).comp
        (MvPolynomial.rename (R := ℤ) e).toRingHom = f := by
      apply MvPolynomial.ringHom_ext'
      · exact RingHom.ext_int _ _
      · intro s
        simp
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨MvPolynomial.rename (R := ℤ) e p, RingHom.congr_fun hcomp p⟩
  exact finite_primes_of_isFractionRing A (FractionRing A)

end GlobalTheory.CompanionTheory.QuadFin
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullPsh

variable {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

theorem comp_chart_eventuallyEq {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (g ∘ h ∘ (A'.chart j).symm) =ᶠ[𝓝 t]
      (g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm) := by
  have hc : ContinuousAt (h ∘ (A'.chart j).symm) t :=
    hh.1.continuousAt.comp ((A'.chart j).continuousAt_symm ht)
  have hmem : ∀ᶠ s in 𝓝 t, h ((A'.chart j).symm s) ∈ (A.chart k).source :=
    hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hmem] with s hs
  simp only [Function.comp_apply, (A.chart k).left_inv hs]

theorem levi_pull_nonneg {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t))
    (hn : ∀ v, 0 ≤ levi (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) v)
    (w : Fin e' → ℂ) : 0 ≤ levi (g ∘ h ∘ (A'.chart j).symm) t w := by
  rw [ReciprocityTheory.AnForm.levi_congr (comp_chart_eventuallyEq hh g j k ht hk) w,
    ReciprocityTheory.AnForm.levi_comp w (hh.2 j k t ⟨ht, hk⟩) hg]
  exact hn _

theorem chart_image_mem {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (A.chart k ∘ h ∘ (A'.chart j).symm) t ∈ (A.chart k).target ∧
      (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) = h ((A'.chart j).symm t) := by
  exact ⟨(A.chart k).map_source hk, (A.chart k).left_inv hk⟩

theorem contDiffAt_of_smoothOn {A : FinHolAtlas e X} {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) (k : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ (A.chart k).target)
    (hzU : (A.chart k).symm z ∈ U) : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) z := by
  have ho : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target hU
  exact (hf k).contDiffAt (ho.mem_nhds ⟨hz, hzU⟩)

theorem smoothOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    A'.SmoothOn (h ⁻¹' U) (f ∘ h) := by
  intro j
  have key : ∀ t ∈ (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (h ⁻¹' U),
      ContDiffAt ℝ ∞ ((f ∘ h) ∘ (A'.chart j).symm) t := by
    rintro t ⟨ht, htU⟩
    obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm t))
    have hF : AnalyticAt ℂ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hh.2 j k t ⟨ht, hk⟩
    have hF' : ContDiffAt ℂ ∞ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hF.contDiffAt
    have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
    have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) ∈ U := by
      rw [hci.2]; exact htU
    have hfk : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) :=
      contDiffAt_of_smoothOn hU hf k hci.1 hzU
    have hcomp : ContDiffAt ℝ ∞ ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm)) t :=
      hfk.comp t (hF'.restrict_scalars ℝ)
    exact hcomp.congr_of_eventuallyEq (comp_chart_eventuallyEq hh f j k ht hk)
  intro t ht
  exact (key t ht).contDiffWithinAt

theorem isPsh_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} (hP : IsPotential A P) (hpsh : IsPsh A P) :
    IsPsh A' (P.pullback h hh.1) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 (P.φ (h x) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    (contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzU).of_le h2
  exact levi_pull_nonneg hh (P.φ (h x)) j k hy.1 hk hg (fun v => hpsh (h x) k _ ⟨hci.1, hzU⟩ v) w

theorem isPshOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} {U : Set X} {f : X → ℝ} (hU : IsOpen U)
    (hP : IsPotential A P) (hf : A.SmoothOn U f) (hpsh : IsPshOn A U (P + LocPot.ofFun f)) :
    IsPshOn A' (h ⁻¹' U) (P.pullback h hh.1 + LocPot.ofFun (f ∘ h)) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2.1.1
  have hyU : h ((A'.chart j).symm y) ∈ U := hy.2.2
  have hzP : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ U := by
    rw [hci.2]; exact hyU
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 ((fun z => P.φ (h x) z + f z) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    ((contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzP).add
      (contDiffAt_of_smoothOn hU hf k hci.1 hzU)).of_le h2
  have hmem : (A.chart k ∘ h ∘ (A'.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((P + LocPot.ofFun f).U (h x) ∩ U) :=
    ⟨hci.1, ⟨hzP, Set.mem_univ _⟩, hzU⟩
  exact levi_pull_nonneg hh (fun z => P.φ (h x) z + f z) j k hy.1 hk hg
    (fun v => hpsh (h x) k _ hmem v) w

theorem pullPsh : PullPshStatement := by
  intro e e' X X' _ _ A A' h hh P U f hU hP
  exact ⟨fun hf => smoothOn_pull hh hU hf, fun hpsh => isPsh_pull hh hP hpsh,
    fun hf hpsh => isPshOn_pull hh hU hP hf hpsh⟩

end PullPsh

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem mdisc_split_fibre_direction : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap (RingHom.id ℂ) (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm :=
  PositivityTheory.Xgp.t_fib_mdisc

end GlobalTheory.CompanionTheory.Ar.PB
end
