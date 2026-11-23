module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle018
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsQuasiFinitePolynomialMap
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle020
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle019
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

@[expose] public section

section

open NumberField

theorem _root_.GlobalTheory.T.exists_finBasis_coeffs_embeddings_eval : ∀ (L : Type) [Field L] [NumberField L] (K : Type) [Field K] [CharZero K] (z : (L →+* K) → K), ∃ y : Fin (Module.finrank ℚ L) → K, ∀ σ : L →+* K, ∑ i, σ (Module.finBasis ℚ L i) * y i = z σ := by
  first | exact @GlobalTheory.embeddings_eval_onto | exact GlobalTheory.embeddings_eval_onto | (intros; apply GlobalTheory.embeddings_eval_onto <;> assumption)
end

section

open NumberField Matrix

theorem _root_.GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), ∃ a : L, a * (IsCMField.complexConj L : L →+* L) a = 1 ∧ ∀ σ : L →+* ℂ, (1 + σ a • X σ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_normOne_det_one_add_ne_zero | exact GlobalTheory.exists_normOne_det_one_add_ne_zero | (intros; apply GlobalTheory.exists_normOne_det_one_add_ne_zero <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero_charZero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K] [CharZero K] (n : ℕ) (M : (L →+* K) → Matrix (Fin n) (Fin n) K), ∃ u : L, u * (IsCMField.complexConj L : L →+* L) u = 1 ∧ ∀ σ : L →+* K, (1 + σ u • M σ).det ≠ 0 := by
  first | exact @GlobalTheory.CMScalar.exists_unit_norm_one_det_ne_zero | exact GlobalTheory.CMScalar.exists_unit_norm_one_det_ne_zero | (intros; apply GlobalTheory.CMScalar.exists_unit_norm_one_det_ne_zero <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_injective_adicCompletion_map_of_finite : ∀ (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N] [Module.Finite D N], Function.Injective (algebraMap D N) → ∀ J : Ideal D, ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N, Function.Injective f := by
  first | exact @GlobalTheory.adicCompletion_injective_ringHom_of_finite | exact GlobalTheory.adicCompletion_injective_ringHom_of_finite | (intros; apply GlobalTheory.adicCompletion_injective_ringHom_of_finite <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_quasi_finite_polynomial_map : ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by
  first | exact @GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | exact GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | (intros; apply GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_approx_finite_places_numberField : ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)), Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 → ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤ Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  first | exact @GlobalTheory.exists_approx_finite_places | exact GlobalTheory.exists_approx_finite_places | (intros; apply GlobalTheory.exists_approx_finite_places <;> assumption)
end

section

namespace GlobalTheory

theorem localizationAtPrime_isDiscreteValuationRing_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  intro A _ _ _ _ q _ hq
  exact isDiscreteValuationRing_of_height_eq_one q hq (Localization.AtPrime q)

end GlobalTheory
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int : ∀ (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D], ringKrullDim D < ⊤ := by
  first | exact @GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | exact GlobalTheory.ringKrullDim_lt_top_of_essFiniteType | (intros; apply GlobalTheory.ringKrullDim_lt_top_of_essFiniteType <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ (ω : L ⊗[F] K) (p : Polynomial (U ⊗[T] C)), p.Monic → p.eval₂ φ ω = 0 → IsIntegral U ω := by
  first | exact @GlobalTheory.integral_of_finite_base_change_image | exact GlobalTheory.integral_of_finite_base_change_image | (intros; apply GlobalTheory.integral_of_finite_base_change_image <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.isUnit_map_of_mem_nonZeroDivisors_tensor' : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), Function.Injective φ → (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  first | exact @GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | exact GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | (intros; apply GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_map_comap_of_one_tmul_mem_map : ∀ {B C R : Type} [CommRing B] [CommRing C] [CommRing R] [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R), (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) → r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  first | exact @GlobalTheory.flat_comap_map_of_one_tmul_mem | exact GlobalTheory.flat_comap_map_of_one_tmul_mem | (intros; apply GlobalTheory.flat_comap_map_of_one_tmul_mem <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.iInf_map_le_map_iInf_of_flat : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R] [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B), ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by
  first | exact @GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf | exact GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf | (intros; apply GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf <;> assumption)
end
