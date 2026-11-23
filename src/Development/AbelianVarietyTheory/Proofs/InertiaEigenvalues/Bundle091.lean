module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle012
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle048
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle049
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.SimpleModule.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle018
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.WittVector.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle052
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
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

section

open Polynomial

namespace GlobalTheory.FilCoeff

theorem poly_eq_zero_of_eval_nat {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) :
    ∀ (n : ℕ) (F : R[X]), F.natDegree ≤ n → ∀ m : ℕ,
      (∀ k : ℕ, F.eval ((m + k : ℕ) : R) = 0) → F = 0 := by
  first
  | exact @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | (apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add ..)

noncomputable def binPoly {R : Type} [CommRing R] (y : R) (s : ℕ) : R[X] :=
  ∑ j ∈ Finset.range s, C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j

theorem eval_binPoly {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (k : ℕ) :
    (binPoly y s).eval ((k : ℕ) : R) = (1 + y) ^ k := by
  have hterm : ∀ j ∈ Finset.range s,
      eval ((k : ℕ) : R) (C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j)
        = y ^ j * ((k.choose j : ℕ) : R) := by
    intro j _
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc, ← mul_assoc (Ring.inverse _),
      Ring.inverse_mul_cancel _ (hR _ (Nat.factorial_ne_zero j)), one_mul]
  rw [binPoly, eval_finsetSum, Finset.sum_congr rfl hterm, add_comm, add_pow]
  simp only [one_pow, mul_one]
  have h1 : ∑ j ∈ Finset.range s, y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [pow_eq_zero_of_le hj hy, zero_mul]
  have h2 : ∑ j ∈ Finset.range (k + 1), y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  rw [h1, h2]

theorem smul_coeff_one_eq_zero {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (c : ℕ → R)
    (h : ∀ k : ℕ, ∑ i ∈ Finset.range s, ((1 + y) ^ k - 1) ^ i * c i = 0) :
    y * c 1 = 0 := by
  rcases s with _ | _ | t
  · have h1 : (1 : R) = 0 := by simpa using hy
    calc y * c 1 = y * c 1 * 1 := (mul_one _).symm
      _ = 0 := by rw [h1, mul_zero]
  · rw [zero_add, pow_one] at hy; rw [hy, zero_mul]
  set P : R[X] := binPoly y (t + 2) - 1 with hPdef
  have hP : ∀ k : ℕ, P.eval ((k : ℕ) : R) = (1 + y) ^ k - 1 := by
    intro k; rw [hPdef, eval_sub, eval_one, eval_binPoly hR y _ hy k]
  set F : R[X] := ∑ i ∈ Finset.range (t + 2), P ^ i * C (c i) with hFdef
  have hF : F = 0 := by
    apply poly_eq_zero_of_eval_nat hR F.natDegree F le_rfl 0
    intro k
    rw [zero_add, hFdef, eval_finsetSum]
    simp only [eval_mul, eval_pow, eval_C, hP]
    exact h k
  have h0 : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]; simpa using hP 0
  obtain ⟨Q, hQ⟩ := X_dvd_iff.2 h0
  have hF1 : F.coeff 1 = Q.coeff 0 * c 1 := by
    rw [hFdef, finsetSum_coeff]
    simp only [coeff_mul_C, hQ, mul_pow, coeff_X_pow_mul']
    rw [Finset.sum_eq_single 1]
    · simp
    · intro i _ hi
      rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · have : i = 0 := by omega
        subst this; simp [coeff_one]
      · rw [if_neg (by omega), zero_mul]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hL : P.coeff 1 = Q.coeff 0 := by rw [hQ, coeff_X_mul]
  have hL2 : P.coeff 1 = y * (1 + (∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
    rw [hPdef, coeff_sub, coeff_one, if_neg one_ne_zero, sub_zero, binPoly, finsetSum_coeff]
    simp only [coeff_C_mul]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      Ring.inverse_one, descPochhammer_one, descPochhammer_zero, coeff_X_one, coeff_one,
      if_neg one_ne_zero, mul_zero, add_zero, mul_one, one_mul]
    have e : ∀ j ∈ Finset.range t, y ^ (j + 1 + 1) * Ring.inverse (((j + 1 + 1).factorial : ℕ) : R)
        * (descPochhammer R (j + 1 + 1)).coeff 1
        = y * ((y ^ j * Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
      intro j _; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hnil : IsNilpotent ((∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) :=
    (Commute.all _ y).isNilpotent_mul_left ⟨_, hy⟩
  have hc := congrArg (fun G : R[X] => G.coeff 1) hF
  simp only [hF1, coeff_zero] at hc
  rw [← hL, hL2, mul_comm, ← mul_assoc, mul_comm (c 1), mul_comm _ (1 + _)] at hc
  have := (hnil.isUnit_one_add).mul_right_eq_zero.1 hc
  rw [mul_comm] at this ⊢; exact (mul_comm (c 1) y) ▸ this

theorem d_mul_x_one_mem_span_pow :
    ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u →
      q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B),
      (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i
        ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  intro B _ hB d q u hu hq s x hx
  set I : Ideal B := Ideal.span {d ^ s} with hI
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B ⧸ I) := fun n hn => by
    simpa using (hB n hn).map (Ideal.Quotient.mk I)
  have hy : (Ideal.Quotient.mk I q - 1) ^ s = 0 := by
    rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      mul_pow]
    exact I.mul_mem_right _ (Ideal.subset_span rfl)
  have key := smul_coeff_one_eq_zero hR (Ideal.Quotient.mk I q - 1) s hy
    (fun i => Ideal.Quotient.mk I (Ring.inverse (i.factorial : B) * x i)) (by
      intro k
      rw [add_sub_cancel]
      have := (Ideal.Quotient.eq_zero_iff_mem).2 (hx k)

      rw [map_sum] at this
      simpa only [map_mul, map_pow, map_sub, map_one, mul_assoc] using this)
  simp only [Nat.factorial_one, Nat.cast_one, Ring.inverse_one, one_mul] at key
  rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at key
  obtain ⟨v, rfl⟩ := hu
  have : d * x 1 = d * ↑v * x 1 * ↑v⁻¹ := by
    rw [mul_right_comm d, mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact I.mul_mem_right _ key

end GlobalTheory.FilCoeff
end

section


theorem _root_.GlobalTheory.T.exists_generators_of_card_hom_residueField_le : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)] (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ),
  Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ a →
  ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  first | exact @GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | exact GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | (intros; apply GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le <;> assumption)
end

section

open NumberField IsDedekindDomain TensorProduct

theorem _root_.GlobalTheory.T.norm_eq_mul_norm_idempotent_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  first | exact @GlobalTheory.norm_eq_mul_norm_idem_corner | exact GlobalTheory.norm_eq_mul_norm_idem_corner | (intros; apply GlobalTheory.norm_eq_mul_norm_idem_corner <;> assumption)
end

section


theorem _root_.GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det : ∀ {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ} (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E'), (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  first | exact @GlobalTheory.det_traceGram_blockMatrix | exact GlobalTheory.det_traceGram_blockMatrix | (intros; apply GlobalTheory.det_traceGram_blockMatrix <;> assumption)
end

section

open scoped PowerSeries Pointwise

theorem _root_.GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  first | exact @GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | exact GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | (intros; apply GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main <;> assumption)
end

section

open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem flat_quotientMap_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    (I : Ideal R) : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Flat := by
  algebraize [φ]
  have h1 : (algebraMap (R ⧸ I) (TensorProduct R (R ⧸ I) S)).Flat :=
    RingHom.flat_algebraMap_iff.2 inferInstance
  let e : TensorProduct R (R ⧸ I) S ≃+* S ⧸ I.map φ :=
    (Algebra.TensorProduct.comm R (R ⧸ I) S).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toRingEquiv
  have h2 : (e : TensorProduct R (R ⧸ I) S →+* S ⧸ I.map φ).Flat := RingHom.Flat.of_bijective e.bijective
  have h3 := h1.comp h2
  convert h3 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have : (Ideal.Quotient.mk I r) ⊗ₜ[R] (1 : S) = (1 : R ⧸ I) ⊗ₜ[R] (φ r) := by
    have := TensorProduct.smul_tmul (R := R) r (1 : R ⧸ I) (1 : S)
    simp only [Algebra.smul_def, mul_one] at this
    exact this
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_coe]
  rw [this]
  apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).injective
  simp [e]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S I (φ r)

end GlobalTheory.Pat
end

section

open Polynomial

namespace GlobalTheory.SimpleCharIndep

theorem exists_smul_eq_ite {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (h : ∀ i j, i ≠ j → ∀ f : M i →ₗ[R] M j, f = 0) (i₀ : ι) (s : ∀ i, Finset (M i)) :
    ∃ r : R, ∀ i, ∀ m ∈ s i, r • m = if i = i₀ then m else 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionOnto.main
  | exact _root_.GlobalTheory.OrthogonalProjectionOnto.main
  | (apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionOnto.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionOnto.main ..)

end GlobalTheory.SimpleCharIndep
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_pi_fin_self {F : Type} [Field F] (r : ℕ) (x : Fin r → F) :
    Algebra.trace F (Fin r → F) x = ∑ i, x i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun F (Fin r)), Matrix.trace]
  congr 1
  ext i
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_apply]

theorem trace_eq_sum_coords_of_algEquiv {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ)
    (e : K ≃ₐ[F] (Fin r → F)) (k : K) : Algebra.trace F K k = ∑ i, e k i := by
  rw [← Algebra.trace_eq_of_algEquiv e k, trace_pi_fin_self]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.eq_of_roots_congr_of_derivative_unit : ∀ {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Polynomial ℤ) (β β' : Ω),
    A.valuation β ≤ 1 → A.valuation β' ≤ 1 → Polynomial.aeval β f = 0 → Polynomial.aeval β' f = 0 →
    ¬ A.valuation (Polynomial.aeval β (Polynomial.derivative f)) < 1 → A.valuation (β - β') < 1 → β = β' := by
  first | exact @GlobalTheory.eq_of_root_congr_of_deriv_unit | exact GlobalTheory.eq_of_root_congr_of_deriv_unit | (intros; apply GlobalTheory.eq_of_root_congr_of_deriv_unit <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A, ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  first | exact @GlobalTheory.DworkGhost.exists_witt_ghost_iterate | exact GlobalTheory.DworkGhost.exists_witt_ghost_iterate | (intros; apply GlobalTheory.DworkGhost.exists_witt_ghost_iterate <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  first | exact @GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | exact GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | (intros; apply GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J → (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) → ∀ a ∈ J, μ ∣ a := by
  first | exact @GlobalTheory.wittVector_dvd_of_saturated_ideal | exact GlobalTheory.wittVector_dvd_of_saturated_ideal | (intros; apply GlobalTheory.wittVector_dvd_of_saturated_ideal <;> assumption)
end
