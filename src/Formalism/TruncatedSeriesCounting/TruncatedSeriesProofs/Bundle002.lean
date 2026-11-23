module

public import Formalism.TruncatedSeriesCounting.Bundle002
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.Bundle001
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma lam_ge_one (ℓ H : ℕ) (hℓ : 2 ≤ ℓ) : 1 ≤ lam ℓ H := by
  unfold lam
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  · have h2 : (1 : ℝ) ≤ 2 * (H : ℝ) := by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have := Real.logb_nonneg h1 h2
    linarith

private lemma hcoef_le (x : ℝ) (hx : 11 ≤ x) :
    8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)) ≤ 32 / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd0 : (0 : ℝ) < x - 1 := by linarith
  have ht : (0 : ℝ) ≤ x - 11 := by linarith
  have ha : 8 * (2 * x - 1) / (x - 1) ^ 3 ≤ (41 / 2) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 3, pow_nonneg ht 2]
  have hb : 8 / (x - 1) ^ 2 ≤ 10 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hc : 1 / (x * (x - 1)) ≤ (11 / 10) / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_nonneg ht 2]
  have hx2 : (0 : ℝ) ≤ 1 / x ^ 2 := by positivity
  have e1 : (41 / 2) / x ^ 2 + 10 / x ^ 2 + (11 / 10) / x ^ 2 = (316 / 10) * (1 / x ^ 2) := by ring
  have e2 : 32 / x ^ 2 = 32 * (1 / x ^ 2) := by ring
  linarith

theorem expBound_statement : ExpBound := by
  intro ℓ hℓ h η S b a s₁ E e₂ hbh ha hs1 hE he2
  have hx : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hd : (10 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hd0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hx0 : (0 : ℝ) < ℓ := by linarith
  have hL := lam_ge_one ℓ (h + η) (by omega)
  have hc := hcoef_le (ℓ : ℝ) hx
  have hsig : sig ℓ h η = (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) + 1 := by
    unfold sig
    push_cast
    ring
  have hfl : ((h / (ℓ - 1) : ℕ) : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) := by
    have h1 := Nat.cast_div_le (m := h) (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h1
  rw [hsig]
  unfold sig₂ at he2 ⊢
  unfold aR at ha
  set L := lam ℓ (h + η) with hLdef
  set H : ℝ := ((h + η : ℕ) : ℝ) with hHdef
  have hhH : (h : ℝ) ≤ H := by
    rw [hHdef]
    push_cast
    linarith [(Nat.cast_nonneg η : (0 : ℝ) ≤ η)]
  have hbH : (b : ℝ) ≤ H := le_trans (by exact_mod_cast hbh) hhH
  have hH0 : 0 ≤ H := by positivity
  have hfl2 : ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ≤ H / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [sq, ← div_div]
    apply div_le_div_of_nonneg_right _ hd0.le
    exact hfl.trans (div_le_div_of_nonneg_right hhH hd0.le)
  have hA : (a : ℝ) / ((ℓ : ℝ) - 1) ≤
      (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) :=
    div_le_div_of_nonneg_right ha hd0.le
  have hB : (b : ℝ) / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) ≤ H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hbH (by positivity)
  have hHc := mul_le_mul_of_nonneg_left hc hH0
  have e3 : H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) =
      H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3) := by
    rw [div_div, ← pow_succ, mul_div_assoc]
  have hv : 1 / ((ℓ : ℝ) - 1) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ hd0 (by norm_num)]
    linarith
  have hLv : L / ((ℓ : ℝ) - 1) ≤ L / 10 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hd
  have hSv : (S : ℝ) / ((ℓ : ℝ) - 1) ≤ S / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
  have hηv : 0 ≤ (η : ℝ) / ((ℓ : ℝ) - 1) := by positivity
  have k1 : (2 * (a : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((ℓ : ℝ) - 1) =
      2 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k2 : (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) =
      3 * ((a : ℝ) / ((ℓ : ℝ) - 1)) + (S : ℝ) / ((ℓ : ℝ) - 1) + 2 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by
    ring
  have k3 : (H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 + 3 + L + 1) / ((ℓ : ℝ) - 1) =
      H * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 / ((ℓ : ℝ) - 1) + 4 * (1 / ((ℓ : ℝ) - 1)) +
        L / ((ℓ : ℝ) - 1) := by
    ring
  have k4 : (((h / (ℓ - 1) : ℕ) : ℝ) + 1 + η) / ((ℓ : ℝ) - 1) =
      ((h / (ℓ - 1) : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 1 / ((ℓ : ℝ) - 1) + (η : ℝ) / ((ℓ : ℝ) - 1) := by
    ring
  have k5 : H * (8 * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3 + 8 / ((ℓ : ℝ) - 1) ^ 2 +
      1 / ((ℓ : ℝ) * ((ℓ : ℝ) - 1))) =
      8 * (H * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 3)) + 8 * (H / ((ℓ : ℝ) - 1) ^ 2) +
        H / ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) := by
    ring
  have k6 : 2 * H / ((ℓ : ℝ) - 1) ^ 2 = 2 * (H / ((ℓ : ℝ) - 1) ^ 2) := by ring
  have k7 : 32 * H / (ℓ : ℝ) ^ 2 = H * (32 / (ℓ : ℝ) ^ 2) := by ring
  have k8 : 10 * (η : ℝ) / ((ℓ : ℝ) - 1) = 10 * ((η : ℝ) / ((ℓ : ℝ) - 1)) := by ring
  rw [k1] at hs1
  rw [k2] at hE
  rw [k3] at hA
  rw [k5] at hHc
  rw [k6] at he2
  rw [k4, k6, k7, k8]
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Formalism.WachCohomologyFacts.PLenBound in
theorem submodule_generator_count : SubGen := by
  intro O _ _ _ M _ _ _ _ ℓ e F P h
  classical

  have hA : ∀ n : ℕ, Module.length O (O ⧸ Ideal.span {ℓ ^ n}) ≤
      (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
    intro n
    induction n with
    | zero =>
      have : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0}) := by
        rw [pow_zero, Ideal.span_singleton_one]
        infer_instance
      simp [Module.length_eq_zero]
    | succ n ih =>
      have hle : Ideal.span {ℓ ^ (n + 1)} ≤ Ideal.span {ℓ ^ n} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ (Nat.le_succ n))
      let g : (O ⧸ Ideal.span {ℓ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ n}) :=
        Submodule.mapQ _ _ LinearMap.id (fun x hx => hle hx)
      have hg : Function.Surjective g := by
        intro y
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact ⟨Submodule.Quotient.mk a, rfl⟩

      let f0 : (O ⧸ Ideal.span {ℓ}) →ₗ[O] (O ⧸ Ideal.span {ℓ ^ (n + 1)}) :=
        (Ideal.span {ℓ}).liftQ (ℓ ^ n • (Ideal.span {ℓ ^ (n + 1)}).mkQ) (by
          intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
          rw [LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
          exact ⟨c, by rw [smul_eq_mul]; ring⟩)
      have hf0 : ∀ x, f0 x ∈ LinearMap.ker g := by
        intro x
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [LinearMap.mem_ker]
        simp only [f0, g, Submodule.liftQ_apply, LinearMap.smul_apply, Submodule.mkQ_apply,
          map_smul, Submodule.mapQ_apply, LinearMap.id_apply]
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
        exact ⟨a, by rw [smul_eq_mul, mul_comm]⟩
      have hf1 : Function.Surjective (f0.codRestrict (LinearMap.ker g) hf0) := by
        rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [LinearMap.mem_ker] at hy
        have ha : a ∈ Ideal.span {ℓ ^ n} := (Submodule.Quotient.mk_eq_zero _).mp hy
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        refine ⟨Submodule.Quotient.mk c, ?_⟩
        apply Subtype.ext
        simp only [LinearMap.codRestrict_apply, f0, Submodule.liftQ_apply, LinearMap.smul_apply,
          Submodule.mkQ_apply]
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]
      have hker : Module.length O (LinearMap.ker g) ≤ Module.length O (O ⧸ Ideal.span {ℓ}) :=
        Module.length_le_of_surjective _ hf1
      rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
        (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)]
      calc Module.length O (LinearMap.ker g) + Module.length O (O ⧸ Ideal.span {ℓ ^ n})
          ≤ Module.length O (O ⧸ Ideal.span {ℓ}) +
              (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := add_le_add hker ih
        _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
          push_cast
          ring

  obtain ⟨k, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  have hk : k ≤ Module.finrank O M := by
    have h1 := Submodule.finrank_le F
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin] at h1
    exact h1
  set Q := P.comap F.subtype with hQ
  have hPF : ∀ y : F, ℓ ^ e • y ∈ Q := by
    intro y
    rw [hQ, Submodule.mem_comap, map_smul]
    exact h _ y.2

  let φ : Fin k → (O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := fun i =>
    (Ideal.span {ℓ ^ e}).liftQ (LinearMap.toSpanSingleton O (↥F ⧸ Q) (Q.mkQ (bF i))) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, mul_smul]
      exact Q.smul_mem c (hPF _))
  let ψ : (Fin k → O ⧸ Ideal.span {ℓ ^ e}) →ₗ[O] (↥F ⧸ Q) := ∑ i, (φ i).comp (LinearMap.proj i)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨fun i => Submodule.Quotient.mk (bF.repr x i), ?_⟩
    have hx : (Submodule.Quotient.mk x : ↥F ⧸ Q) =
        ∑ i, bF.repr x i • Submodule.Quotient.mk (bF i) := by
      conv_lhs => rw [← bF.sum_repr x]

      rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
    rw [hx]
    simp only [ψ, φ, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      Submodule.mkQ_apply]
  have hB : Module.length O (↥F ⧸ Q) ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := by
    calc Module.length O (↥F ⧸ Q) ≤ Module.length O (Fin k → O ⧸ Ideal.span {ℓ ^ e}) :=
          Module.length_le_of_surjective ψ hψ
      _ = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := by
          rw [Module.length_pi_of_fintype]
          simp
  calc Module.length O (↥F ⧸ Q)
      ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := hB
    _ ≤ (k : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})) := by
        gcongr
        exact hA e
    _ ≤ ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
        push_cast
        rw [mul_assoc]
        gcongr

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end
end
