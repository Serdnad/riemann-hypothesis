module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.SemistableReduction.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ), (∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) → IsIntegral ℤ ((M : ℤ) • x) := by
  first | (exact @GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (exact GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (intros; apply GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int  <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.span_basis_det_integral_eq_one : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V), Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ Submodule.span (𝓞 F) (Set.range β)) ∧ y = β.det w} = 1 := by
  first | exact @GlobalTheory.basis_det_integral_span_eq_one | exact GlobalTheory.basis_det_integral_span_eq_one | (intros; apply GlobalTheory.basis_det_integral_span_eq_one <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.coeff_det_mem_span_det_integral_polynomial_vectors : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V) (τ : Type) (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F)), (∀ k m, ∑ i, AddMonoidAlgebra.coeff (P i k) m • b i ∈ M) → ∀ m, AddMonoidAlgebra.coeff P.det m ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
  first | exact @GlobalTheory.DetCoeff.coeff_det_mem_span_det | exact GlobalTheory.DetCoeff.coeff_det_mem_span_det | (intros; apply GlobalTheory.DetCoeff.coeff_det_mem_span_det <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.exists_common_denominator_span_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (M : Submodule (𝓞 F) V), M.FG → ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ M) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F) := by
  first | exact @GlobalTheory.det_span_common_denominator | exact GlobalTheory.det_span_common_denominator | (intros; apply GlobalTheory.det_span_common_denominator <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.exists_maximalIdeal_smul_mem_of_lt_of_relIndex_ne_zero : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (N₀ N : Submodule (𝓞 F) V), N₀ < N → N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 → ∃ (u : V) (p : Ideal (𝓞 F)), p.IsMaximal ∧ u ∈ N ∧ u ∉ N₀ ∧ ∀ π ∈ p, π • u ∈ N₀ := by
  first | exact @GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero | exact GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero | (intros; apply GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.smul_detSpan_sup_le_detSpan_lattice : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (b : Module.Basis (Fin d) F V) (N : Submodule (𝓞 F) V) (u : V) (π : 𝓞 F), π • u ∈ N → ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N ⊔ Submodule.span (𝓞 F) {u}) ∧ y = b.det v}, π • y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N) ∧ y = b.det v} := by
  first | exact @GlobalTheory.DetColon.smul_detSpan_sup_le | exact GlobalTheory.DetColon.smul_detSpan_sup_le | (intros; apply GlobalTheory.DetColon.smul_detSpan_sup_le <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.IntAwayP

theorem norm_self_padicAlgCl (p : ℕ) [Fact p.Prime] : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends p (p : ℚ_[p])
  rw [map_natCast] at this
  rw [this, Padic.norm_p]

theorem norm_prime_padicAlgCl_of_ne (ℓ p : ℕ) [hℓ : Fact ℓ.Prime] (hp : p.Prime) (h : ℓ ≠ p) :
    ‖(p : PadicAlgCl ℓ)‖ = 1 := by
  have h1 := PadicAlgCl.norm_extends ℓ (p : ℚ_[ℓ])
  rw [map_natCast] at h1
  rw [h1]
  have h2 : ‖(p : ℤ_[ℓ])‖ = 1 := (PadicInt.norm_natCast_eq_one_iff).2 ((Nat.coprime_primes hℓ.out hp).2 h)
  rw [← h2, PadicInt.norm_def]
  simp

theorem isIntegral_of_pow_mul (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (z : K) (N : ℕ) (hN : IsIntegral ℤ ((p : K) ^ N * z))
    (h : ∀ φ : K →+* PadicAlgCl p, ‖φ z‖ ≤ 1) : IsIntegral ℤ z := by
  refine GlobalTheory.isIntegral_of_forall_padicAlgCl_norm_le_one K z fun q _ τ => ?_
  by_cases hq : q = p
  · subst hq; exact h τ
  · have h1 : ‖τ ((p : K) ^ N * z)‖ ≤ 1 :=
      GlobalTheory.norm_le_one_of_isIntegral_int (hN.map τ.toIntAlgHom)
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      norm_prime_padicAlgCl_of_ne q p hp.out hq, one_pow, one_mul] at h1
    exact h1

theorem exists_pow_mul_isIntegral : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (B : ℝ), ∃ m₀ : ℕ, ∀ (c : K) (D : ℕ), (∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * D * c)) → (∀ φ : K →+* PadicAlgCl p, ‖φ c‖ ≤ B) → IsIntegral ℤ ((p : K) ^ m₀ * D * c) := by
  intro K _ _ p _ B
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt B hp1
  refine ⟨m₀, fun c D ⟨m, hm⟩ hB => ?_⟩
  apply isIntegral_of_pow_mul K p _ m
  · have e : (p : K) ^ m * ((p : K) ^ m₀ * D * c) = (p : K) ^ m₀ * ((p : K) ^ m * D * c) := by ring
    rw [e]
    have hpi : IsIntegral ℤ ((p : K) ^ m₀) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (p : ℤ))).pow m₀
    exact hpi.mul hm
  · intro φ
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast, norm_mul, norm_mul, norm_pow,
      norm_self_padicAlgCl]
    have hD := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) D
    have h2 : ‖(D : PadicAlgCl p)‖ * ‖φ c‖ ≤ (p : ℝ) ^ m₀ :=
      (mul_le_of_le_one_left (norm_nonneg _) hD).trans ((hB φ).trans hm₀.le)
    rw [mul_assoc, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact h2

end GlobalTheory.IntAwayP
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.relIndex_ideal_smul_fractionalIdeal_eq_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Submodule (𝓞 F) F) (p : Ideal (𝓞 F)), p ≠ ⊥ → I ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (p • I).toAddSubgroup.relIndex I.toAddSubgroup = Ideal.absNorm p := by
  first | exact @GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm | exact GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm | (intros; apply GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.relIndex_sup_span_singleton_eq_absNorm_of_isMaximal : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (N₀ : Submodule (𝓞 F) V) (u : V) (p : Ideal (𝓞 F)), p.IsMaximal → u ∉ N₀ → (∀ π ∈ p, π • u ∈ N₀) → N₀.toAddSubgroup.relIndex (N₀ ⊔ Submodule.span (𝓞 F) {u}).toAddSubgroup = Ideal.absNorm p := by
  first | exact @GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | exact GlobalTheory.relIndex_sup_span_singleton_eq_absNorm | (intros; apply GlobalTheory.relIndex_sup_span_singleton_eq_absNorm <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.cmField_conj_extends_of_adjoin_absSq : ∀ (F M : Type) [Field F] [NumberField F] [IsCMField F] [Field M] [NumberField M] [Algebra F M] (π : M) (c : ℚ), Algebra.adjoin F {π} = ⊤ → c ≠ 0 → (∀ φ : M →+* ℂ, ‖φ π‖ ^ 2 = (c : ℝ)) → ∃ σ : M →+* M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)) ∧ σ π * π = (c : M) ∧ ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x) := by
  first | (exact @GlobalTheory.cm_conj_extends_of_adjoin) | (exact GlobalTheory.cm_conj_extends_of_adjoin) | (intros; apply GlobalTheory.cm_conj_extends_of_adjoin  <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.finsum_log_finitePlace_eq_neg_log_abs_norm' : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∑ᶠ q : FinitePlace F, Real.log (q δ) = -Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm | exact GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm | (intros; apply GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.QuadSigns

section Field

variable {L : Type} [Field L] [NumberField L]

theorem conj_involutive (σ : L →+* L)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (x : L) : σ (σ x) = x := by
  let φ := (Classical.arbitrary (InfinitePlace L)).embedding
  apply φ.injective
  rw [hc, hc, Complex.conj_conj]

theorem isTotallyComplex_of_conj (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) : IsTotallyComplex L := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hr => hσ ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hr
  refine RingHom.ext fun x => w.embedding.injective ?_
  rw [hc, RingHom.id_apply, ← ComplexEmbedding.conjugate_coe_eq, hr]

end Field

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isReal_comp (σ : L →+* L) (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : L →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) := by
  rw [ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun x => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, hK]

theorem isTotallyReal_of_conj [Algebra.IsAlgebraic K L] (σ : L →+* L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) : IsTotallyReal K := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) w
  show (W.comap (algebraMap K L)).IsReal
  rw [← W.mk_embedding, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
  exact isReal_comp σ hK hc _

theorem eq_or_eq_conjugate (hd : Module.finrank K L = 2) (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ ε : L →+* ℂ)
    (h : φ.comp (algebraMap K L) = ε.comp (algebraMap K L)) :
    φ = ε ∨ φ = ComplexEmbedding.conjugate ε := by
  have hss := conj_involutive σ hc
  obtain ⟨s, hs⟩ : ∃ s, σ s ≠ s := by
    by_contra hne
    push_neg at hne
    exact hσ (RingHom.ext hne)
  set t := s - σ s with ht
  have hσt : σ t = -t := by rw [ht, map_sub, hss]; ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have hli : LinearIndependent K ![(1 : L), t] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h2 := congrArg σ hab
    simp only [Algebra.smul_def, map_add (f := _), map_mul, hK, hσt, map_one, map_zero, mul_one] at h2 hab
    have hb2 : (2 : L) * (algebraMap K L b * t) = 0 := by linear_combination hab - h2
    have hb : b = 0 := by simpa [ht0] using hb2
    subst hb
    simp only [map_zero, zero_mul, add_zero, FaithfulSMul.algebraMap_eq_zero_iff] at hab
    exact ⟨hab, rfl⟩
  have hdec : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * t := by
    intro x
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hd])
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    simp [B, Fin.sum_univ_two, Algebra.smul_def]
  have hφK : ∀ a : K, φ (algebraMap K L a) = ε (algebraMap K L a) := fun a => RingHom.congr_fun h a
  obtain ⟨a, b, hab⟩ := hdec (t * t)
  have hb : b = 0 := by
    have h2 : σ (t * t) = t * t := by rw [map_mul, hσt, neg_mul_neg]
    rw [hab] at h2
    simp only [map_add (f := _), map_mul, hK, hσt] at h2
    have hb2 : (2 : L) * (algebraMap K L b * t) = 0 := by linear_combination -h2
    simpa [ht0] using hb2
  subst hb
  simp only [map_zero, zero_mul, add_zero] at hab
  have hsq : φ t * φ t = ε t * ε t := by rw [← map_mul, ← map_mul, hab, hφK]
  have hfac : (φ t - ε t) * (φ t + ε t) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hfac with h1 | h1
  · left
    have hφt : φ t = ε t := sub_eq_zero.1 h1
    refine RingHom.ext fun x => ?_
    obtain ⟨a', b', rfl⟩ := hdec x
    simp only [map_add (f := _), map_mul, hφK, hφt]
  · right
    have hφt : φ t = -ε t := eq_neg_of_add_eq_zero_left h1
    refine RingHom.ext fun x => ?_
    obtain ⟨a', b', rfl⟩ := hdec x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc]
    simp only [map_add (f := _), map_mul, hφK, hφt, hK, hσt, map_neg]

end GlobalTheory.QuadSigns

namespace GlobalTheory.QuadSigns

open scoped TensorProduct

theorem exists_signs (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hd : Module.finrank K L = 2) (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (ε ε' : L →+* ℂ)
    (h1 : ε ≠ ε') (h2 : ε ≠ ComplexEmbedding.conjugate ε') :
    ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧
      (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' →
        φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L,
        Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  classical
  haveI : Algebra.IsQuadraticExtension K L := ⟨hd⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hKr : IsTotallyReal K := isTotallyReal_of_conj σ hK hc
  have hLc : IsTotallyComplex L := isTotallyComplex_of_conj σ hσ hc
  have hover : ∀ φ ψ : L →+* ℂ, InfinitePlace.mk (φ.comp (algebraMap K L)) =
      InfinitePlace.mk (ψ.comp (algebraMap K L)) → φ = ψ ∨ φ = ComplexEmbedding.conjugate ψ := by
    intro φ ψ hm
    apply eq_or_eq_conjugate hd σ hσ hK hc
    rcases InfinitePlace.mk_eq_iff.1 hm with hh | hh
    · exact hh
    · rwa [ComplexEmbedding.isReal_iff.1 (isReal_comp σ hK hc φ)] at hh
  set w₁ := InfinitePlace.mk (ε.comp (algebraMap K L)) with hw₁
  set w₂ := InfinitePlace.mk (ε'.comp (algebraMap K L)) with hw₂
  have hw : w₁ ≠ w₂ := by
    intro he
    rcases hover ε ε' he with hh | hh
    · exact h1 hh
    · exact h2 hh
  obtain ⟨h, hneg, hpos, hfin⟩ := GlobalTheory.QuadRecip.exists_signs_of_even K L hKr hLc {w₁, w₂}
    (by rw [Finset.card_pair hw]; decide)
  have hsign : ∀ φ : L →+* ℂ, (φ (algebraMap K L (h : K))).re =
      InfinitePlace.embedding_of_isReal (hKr.isReal (InfinitePlace.mk (φ.comp (algebraMap K L))))
        (h : K) := by
    intro φ
    have := InfinitePlace.embedding_of_isReal_apply
      (hKr.isReal (InfinitePlace.mk (φ.comp (algebraMap K L)))) (h : K)
    rw [InfinitePlace.embedding_mk_eq_of_isReal (isReal_comp σ hK hc φ), RingHom.comp_apply] at this
    rw [← this, Complex.ofReal_re]
  refine ⟨h, h.ne_zero, ?_, ?_, ?_, ?_⟩
  · rw [hsign]
    exact hneg _ (by simp [w₁])
  · rw [hsign]
    exact hneg _ (by simp [w₂])
  · intro φ n1 n2 n3 n4
    rw [hsign]
    refine hpos _ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro he
      rcases hover φ ε he with hh | hh
      · exact n1 hh
      · exact n2 hh
    · intro he
      rcases hover φ ε' he with hh | hh
      · exact n3 hh
      · exact n4 hh
  · intro v
    obtain ⟨z, hz⟩ := GlobalTheory.QuadSymbol.mem_normGroup_iff.1 (hfin v)
    exact ⟨z, hz⟩

end GlobalTheory.QuadSigns
end
end
