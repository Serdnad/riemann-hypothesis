module

public import Formalism.JumpKernelCokernel.Bundle001
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle002
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncZero
public import Mathlib.RingTheory.PowerSeries.Trunc
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem add_pow_mem_span_pow_pow (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ) :
    (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := by
  have hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := Ideal.subset_span (Set.mem_insert _ _)
  have hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [add_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ A + r - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hA : A ≤ i
  · have e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A) := by rw [← pow_add, Nat.add_sub_cancel' hA]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))
  · have hr : r ≤ A + r - 1 - i := by omega
    have e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))

end Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem Formalism.KernelCokernelLengths.ideal_power_sum_mem : Formalism.KernelCokernelLengths.QPow := by
  intro R _ π₀ ℓ A r
  exact Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r
end

section

noncomputable section

namespace Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial

variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module O V]

theorem decomp (d : Module.End O V) (P : O[X]) (v : V) :
    aeval d P v = P.eval 0 • v + aeval d P.divX (d v) := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add P]
  rw [map_add (f := _), map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, ← Polynomial.coeff_zero_eq_eval_zero, add_comm]

theorem aeval_mem (d : Module.End O V) (M : Submodule O V) (hM : M.map d ≤ M) :
    ∀ (Q : O[X]) (v : V), v ∈ M → aeval d Q v ∈ M := by
  have hd : ∀ v ∈ M, d v ∈ M := fun v hv => hM (Submodule.mem_map_of_mem hv)
  have hpow : ∀ (n : ℕ) (v : V), v ∈ M → (d ^ n) v ∈ M := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hd v hv)
  intro Q
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add (f := _), LinearMap.add_apply]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial n a =>
    intro v hv
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact M.smul_mem a (hpow n v hv)

end Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial Formalism.KernelCokernelLengths.PolynomialDegreeLemmas in
theorem Formalism.KernelCokernelLengths.polynomial_degree_facts : Formalism.KernelCokernelLengths.PdFacts := by
  intro O _ V _ _ d P M hM
  refine ⟨fun h0 => ?_, fun h0 u hu => ?_⟩
  · have ha : ∀ v : V, d (aeval d P v) = 0 := by
      intro v
      have h1 := congrArg (fun f : Module.End O V => f v) h0
      simpa [map_mul, aeval_X] using h1
    refine ⟨ha, fun v hv => ?_, fun w hw u hu => ?_⟩
    · rw [decomp d P v, hv, map_zero, add_zero]
    · have h1 := decomp d P u
      have h2 : P.eval 0 • w = d (-(aeval d P.divX w)) := by
        have h3 : P.eval 0 • u = aeval d P u - aeval d P.divX (d u) := eq_sub_of_add_eq h1.symm
        rw [← hu, ← map_smul, h3, map_sub, ha, zero_sub, map_neg]
      rw [h2]
      exact Submodule.mem_map_of_mem (M.neg_mem (aeval_mem d M hM _ w hw))
  · have h1 := decomp d P u
    rw [h0, LinearMap.zero_apply] at h1
    have h3 : P.eval 0 • u = -(aeval d P.divX (d u)) := eq_neg_of_add_eq_zero_left h1.symm
    rw [h3]
    exact M.neg_mem (aeval_mem d M hM _ _ hu)
end
end

section

namespace Formalism.KernelCokernelLengths

theorem row_degree_bound : RowD := by
  unfold RowD
  intro h h1 η hη
  have key : 32 * (h1 + η) ≤ 50 * h1 := by omega
  gcongr ?_ / _
  exact_mod_cast key

end Formalism.KernelCokernelLengths
end

section

namespace Formalism.KernelCokernelLengths

theorem row_degree_exponent : ExpRowD := by
  intro ℓ hℓ h η S b a s₁ E e₂ hη hb ha hs hE he
  have key := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.expBound_statement ℓ hℓ h η S b a s₁ E e₂ hb ha hs hE he
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ2 : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by positivity
  have hη' : (2 * (η : ℝ)) ≤ h := by exact_mod_cast hη
  have hc : 32 * ((h + η : ℕ) : ℝ) / (ℓ : ℝ) ^ 2 ≤ 50 * (h : ℝ) / (ℓ : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hℓ2.le
    push_cast
    nlinarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  linarith

end Formalism.KernelCokernelLengths
end

section

noncomputable section

namespace Formalism.KernelCokernelLengths

theorem column_theorem_C : ColThmC := by
  intro O _ _ _ M _ _ _ _ ℓ P k F gen n r m e e' S cD hn hrk hgen hk hF0 hF hsub hG hN hE
  have h := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_assembly_bound O M ℓ P k F gen m e e' (r * S + 2 * m * cD) hF0 hF hsub hG hN hE
  refine h.trans ?_
  have hAB : Module.finrank O M * e + gen.card * m * e' + (k - gen.card) * (r * S + 2 * m * cD) ≤
      (n + 1) * r * e + 4 * n * m * e' + (3 * n / 2) * (r * S + 2 * m * cD) := by
    gcongr
  gcongr

end Formalism.KernelCokernelLengths
end
end

section

namespace Formalism.KernelCokernelLengths

theorem relation_vanishes : RelZero := by
  intro R _ u π₀ q ℓ h η y hℓ hη hy
  apply Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul R u π₀ q ℓ (h / (ℓ - 1) + 1) η y hy
  have hpos : 0 < ℓ - 1 := by omega
  have h1 : h < (ℓ - 1) * (h / (ℓ - 1) + 1) := Nat.lt_mul_div_succ h hpos
  have h2 : (ℓ - 1) * (h / (ℓ - 1) + 1) ≤ (ℓ - 1) * y := Nat.mul_le_mul_left _ hy
  omega

end Formalism.KernelCokernelLengths
end

section

noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open PowerSeries

theorem len_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (v : ℕ) :
    Module.length O (O ⧸ Ideal.span {(u : O) * ϖ ^ v}) = v := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) v

theorem ker_eq_coker {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) :
    Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f) := by
  have h1 : Module.length O M =
      Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
      (Submodule.subtype_injective _) f.surjective_rangeRestrict
      (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length O M =
      Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hR : Module.length O (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective _ (Submodule.subtype_injective (LinearMap.range f)))
  have h5 : Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) =
      Module.length O (M ⧸ LinearMap.range f) + Module.length O (LinearMap.range f) := by
    rw [← h1, h2, add_comm]
  exact WithTop.add_right_cancel hR h5

variable {O : Type} [CommRing O] (ℓ : O) (n k : ℕ)

abbrev J : Ideal (PowerSeries O) := Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

noncomputable abbrev ψ : Polynomial O →+* (PowerSeries O ⧸ J ℓ n k) :=
  Polynomial.eval₂RingHom (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X)

theorem psi_apply (P : Polynomial O) :
    ψ ℓ n k P = P.eval₂ (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X) := rfl

theorem alg_eq (a : O) :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) a = Ideal.Quotient.mk (J ℓ n k) (C a) := rfl

theorem psi_eq (P : Polynomial O) : ψ ℓ n k P = Ideal.Quotient.mk (J ℓ n k) (P : PowerSeries O) := by
  have h : ψ ℓ n k = (Ideal.Quotient.mk (J ℓ n k)).comp (Polynomial.coeToPowerSeries.ringHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [alg_eq]
    · simp
  rw [h]
  rfl

theorem mk_eq_psi (p : PowerSeries O) :
    Ideal.Quotient.mk (J ℓ n k) p = ψ ℓ n k (trunc n p) := by
  rw [psi_eq, Ideal.Quotient.eq]
  obtain ⟨q, hq⟩ : (X : PowerSeries O) ^ n ∣ p - (trunc n p : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hm]
  rw [hq]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem algebraMap_pow_k :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) (ℓ ^ k) = 0 := by
  rw [alg_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

theorem smul_pow_k (b : PowerSeries O ⧸ J ℓ n k) : ℓ ^ k • b = 0 := by
  rw [Algebra.smul_def, algebraMap_pow_k, zero_mul]

theorem len_B_le :
    Module.length O (PowerSeries O ⧸ J ℓ n k) ≤
      Module.length O (Fin n → O ⧸ Ideal.span {ℓ ^ k}) := by
  let e : Fin n → (PowerSeries O ⧸ J ℓ n k) := fun j => (Ideal.Quotient.mk (J ℓ n k) X) ^ (j : ℕ)
  have hker : ∀ j, Ideal.span {ℓ ^ k} ≤ LinearMap.ker (LinearMap.toSpanSingleton O _ (e j)) := by
    intro j
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact smul_pow_k ℓ n k _
  let Φ : (Fin n → O ⧸ Ideal.span {ℓ ^ k}) →ₗ[O] (PowerSeries O ⧸ J ℓ n k) :=
    ∑ j : Fin n, (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j)).comp
      (LinearMap.proj j)
  have hΦ : Function.Surjective Φ := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨fun j => Ideal.Quotient.mk _ (coeff (j : ℕ) p), ?_⟩
    rw [mk_eq_psi, psi_apply, eval₂_trunc_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range]
    simp only [Φ]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j))
      (Submodule.Quotient.mk (coeff (j : ℕ) p)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  exact Module.length_le_of_surjective Φ hΦ

theorem len_coker_le :
    Module.length O ((PowerSeries O ⧸ J ℓ n k) ⧸ LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))) ≤
      Module.length O (O ⧸ Ideal.span {ℓ ^ k}) := by
  set R := LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ))) with hR
  have hker : Ideal.span {ℓ ^ k} ≤
      LinearMap.ker (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k))) := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← LinearMap.map_smul, smul_pow_k, map_zero]
  let Ψ := Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k)))
    hker
  have hΨ : Function.Surjective Ψ := by
    intro z
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective R z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := ℓ) (p := trunc n p)
    refine ⟨Submodule.Quotient.mk ((trunc n p).eval ℓ), ?_⟩
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul,
      Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-ψ ℓ n k Q, ?_⟩
    have hX : Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ) =
        ψ ℓ n k (Polynomial.X - Polynomial.C ℓ) := by
      rw [psi_eq, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
    rw [map_neg, LinearMap.mulLeft_apply, hX, ← map_mul, ← hQ, map_sub, mk_eq_psi ℓ n k p,
      psi_apply ℓ n k (Polynomial.C _), Polynomial.eval₂_C,
      Algebra.algebraMap_eq_smul_one, neg_sub]
  exact Module.length_le_of_surjective Ψ hΨ

end Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas in
theorem Formalism.KernelCokernelLengths.torsion_kernel_length : Formalism.KernelCokernelLengths.TorsKer := by
  intro O _ _ _ ℓ hℓ n k
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ hϖ
  have hl1 : Module.length O (O ⧸ Ideal.span {ℓ}) = v := by
    rw [hu]; exact len_quot_pow hϖ u v
  have hlk : Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = ((v * k : ℕ) : ℕ∞) := by
    rw [hu, mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val]
    exact len_quot_pow hϖ (u ^ k) (v * k)
  have hB : Module.length O (PowerSeries O ⧸ J ℓ n k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (len_B_le ℓ n k)
    rw [Module.length_pi, hlk, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  rw [ker_eq_coker hB, hl1]
  refine (len_coker_le ℓ n k).trans ?_
  rw [hlk]
  push_cast
  rw [mul_comm]
end
end
