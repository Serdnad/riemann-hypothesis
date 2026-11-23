module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle267
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedBasisIntegralConjEntriesBounded
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatrices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

section

namespace GlobalTheory.NormPowerTwoUnity

lemma norm_sq_sub_one_ge (w : ℂ) (h : ‖w - 1‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w + 1) * (w - 1) := by ring
  have h2 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    rw [this]
    exact norm_sub_le _ _
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith

theorem eq_one_of_norm_pow_two_pow_sub_one_lt (z : ℂ)
    (h : ∀ (m : ℕ), ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ < (1 / 2 : ℝ)) : z = (1 : ℂ) := by
  apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.eq_one_of_pow_two_pow_near <;> assumption

end GlobalTheory.NormPowerTwoUnity
end

section

open Matrix GlobalTheory.ClassFin

namespace GlobalTheory.RedBound

lemma entry_bound {N : ℕ} (P Z Q : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (c : ℝ)
    (h : ∀ p q, |P i p * Z p q * Q q j| ≤ c) : |(P * Z * Q) i j| ≤ N * N * c := by
  have e : (P * Z * Q) i j = ∑ q, ∑ p, P i p * Z p q * Q q j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [e]
  calc |∑ q, ∑ p, P i p * Z p q * Q q j| ≤ ∑ q, |∑ p, P i p * Z p q * Q q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : Fin N, ∑ _p : Fin N, c := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => h p q)
    _ = N * N * c := by simp [Finset.sum_const, Finset.card_fin]; ring

lemma orth_entry_le {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (p q : Fin N) :
    |k p q| ≤ 1 := by
  have h1 : ∑ r, k r q * k r q = 1 := by
    have := congrFun (congrFun h q) q
    simpa [Matrix.mul_apply] using this
  have h2 : k p q * k p q ≤ ∑ r, k r q * k r q :=
    Finset.single_le_sum (f := fun r => k r q * k r q) (fun r _ => mul_self_nonneg _)
      (Finset.mem_univ p)
  rw [h1] at h2
  have h3 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact h2
  nlinarith [abs_nonneg (k p q)]

lemma le_of_le_idx {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {i p : Fin N} (h : i ≤ p) : a i ≤ Cm * a p := by
  rcases h.lt_or_eq with h | h
  · exact (hS.le i p h).trans (mul_le_mul_of_nonneg_right hC (hS.pos p).le)
  · subst h; exact le_mul_of_one_le_left (hS.pos i).le h1

lemma prod_le {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {p q r s : Fin N} (hr : p ≤ r) (hs : q ≤ s) : a p * a q ≤ Cm ^ 2 * (a r * a s) := by
  have har := le_of_le_idx hS h1 hC hr
  have has := le_of_le_idx hS h1 hC hs
  have h0 : 0 ≤ Cm * a r := mul_nonneg (by linarith) (hS.pos r).le
  calc a p * a q ≤ (Cm * a r) * (Cm * a s) := mul_le_mul har has (hS.pos q).le h0
    _ = Cm ^ 2 * (a r * a s) := by ring

end GlobalTheory.RedBound

namespace GlobalTheory.RedBound

theorem reduced_bound : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) →
    B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) →
    (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X →
    ∀ i j, |(B i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨M, hM⟩ := GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded N C
  obtain ⟨Cm, hCm1, hCC⟩ : ∃ Cm : ℝ, 1 ≤ Cm ∧ C ≤ Cm := ⟨max C 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨M₀, hM₀, hMM⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ M ≤ M₀ := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R₀, hR₀, hRR⟩ : ∃ R₀ : ℝ, 0 ≤ R₀ ∧ R ≤ R₀ := ⟨max R 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = N * N * (1 * R₀ * 1) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = N * N * K₁ + 1 := ⟨_, rfl⟩
  have hCm0 : 0 < Cm := lt_of_lt_of_le one_pos hCm1
  have hR'0 : 0 ≤ R' := by rw [hR']; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨N * N * (Cm * (Cm ^ 2 * T * R') * Cm), ?_⟩
  intro k a n hS X B B' μ hμ hμR hX hB hB' i j
  obtain ⟨m, hmn, _hnm, hmlow, hmb⟩ := hM n hS.diag hS.lower hS.bdd
  have hmb' : ∀ p q, |m p q| ≤ M₀ := fun p q => (hmb p q).trans hMM
  have hnb : ∀ p q, |n p q| ≤ Cm := fun p q => (hS.bdd p q).trans hCC
  have hμ₀ : |μ| ≤ R₀ := hμR.trans hRR
  have hk : ∀ p q, |k p q| ≤ 1 := orth_entry_le k hS.orth
  obtain ⟨X', hX'def⟩ : ∃ X', X' = kᵀ * X * k := ⟨_, rfl⟩
  have hX' : ∀ p q, |X' p q| ≤ R' := by
    intro p q
    rw [hX'def, hR']
    apply entry_bound
    intro r s
    rw [abs_mul, abs_mul, Matrix.transpose_apply]
    exact mul_le_mul (mul_le_mul (hk r p) ((hX r s).trans hRR) (abs_nonneg _) zero_le_one)
      (hk s q) (abs_nonneg _) (by positivity)
  obtain ⟨Br', hBr'⟩ : ∃ Br', Br' = B'.map (Int.cast : ℤ → ℝ) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = n * Br' * nᵀ := ⟨_, rfl⟩
  have hWeq : diagonal a * W * diagonal a = μ • X' := by
    have h1 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k = μ • X' := by
      rw [hBr', hB', hX'def, Matrix.mul_smul, Matrix.smul_mul]
    rw [← h1, hWdef]
    have h2 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k =
        (kᵀ * k) * (diagonal a * (n * Br' * nᵀ) * diagonal a) * (kᵀ * k) := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [h2, hS.orth, Matrix.one_mul, Matrix.mul_one]
  have hWent : ∀ p q, a p * W p q * a q = μ * X' p q := by
    intro p q
    have := congrFun (congrFun hWeq p) q
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hBm : Br' = m * W * mᵀ := by
    rw [hWdef]
    calc Br' = (m * n) * Br' * (m * n)ᵀ := by rw [hmn]; simp
      _ = m * (n * Br' * nᵀ) * mᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hZ : B.map (Int.cast : ℤ → ℝ) = nᵀ * (diagonal a * X' * diagonal a) * n := by
    rw [hB, hX'def]
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hA : ∀ p q, T ≤ a p * a q → B' p q = 0 := by
    intro p q hpq
    have hpos : 0 < a p * a q := mul_pos (hS.pos p) (hS.pos q)
    have hb : |Br' p q| ≤ N * N * (K₁ / (a p * a q)) := by
      rw [hBm]
      apply entry_bound
      intro r s
      rw [le_div_iff₀ hpos, Matrix.transpose_apply]
      by_cases hr : r < p
      · rw [hmlow p r hr]; simp; positivity
      by_cases hs : s < q
      · rw [hmlow q s hs]; simp; positivity
      push_neg at hr hs
      have hWb : |W r s| * (a r * a s) ≤ R₀ * R' := by
        calc |W r s| * (a r * a s) = |a r * W r s * a s| := by
              rw [abs_mul, abs_mul, abs_of_pos (hS.pos r), abs_of_pos (hS.pos s)]; ring
          _ = |μ| * |X' r s| := by rw [hWent r s, abs_mul]
          _ ≤ R₀ * R' := mul_le_mul hμ₀ (hX' r s) (abs_nonneg _) hR₀
      have hapq := prod_le hS hCm1 hCC hr hs
      rw [abs_mul, abs_mul, hK₁]
      calc |m p r| * |W r s| * |m q s| * (a p * a q)
          ≤ |m p r| * |W r s| * |m q s| * (Cm ^ 2 * (a r * a s)) :=
            mul_le_mul_of_nonneg_left hapq (by positivity)
        _ = |m p r| * (Cm ^ 2 * (|W r s| * (a r * a s))) * |m q s| := by ring
        _ ≤ M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ :=
            mul_le_mul (mul_le_mul (hmb' p r) (mul_le_mul_of_nonneg_left hWb (by positivity))
              (mul_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (mul_pos (hS.pos r) (hS.pos s)).le)) hM₀) (hmb' q s) (abs_nonneg _) (by positivity)
    have hlt : |Br' p q| < 1 := by
      have e : (N : ℝ) * N * (K₁ / (a p * a q)) = (N * N * K₁) / (a p * a q) := by ring
      rw [e] at hb
      exact hb.trans_lt ((div_lt_one hpos).mpr (by linarith))
    have h3 : |((B' p q : ℤ) : ℝ)| < 1 := by rw [hBr'] at hlt; simpa using hlt
    have h4 : |B' p q| < 1 := by exact_mod_cast h3
    exact Int.abs_lt_one_iff.mp h4
  have hBz : ∀ p q, Cm ^ 2 * T ≤ a p * a q → W p q = 0 := by
    intro p q h
    rw [hWdef]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_eq_zero
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r < p
    · rw [hS.lower p r hr]; ring
    by_cases hs : s < q
    · rw [hS.lower q s hs]; ring
    push_neg at hr hs
    have hapq := prod_le hS hCm1 hCC hr hs
    have hT' : T ≤ a r * a s := by
      have : Cm ^ 2 * T ≤ Cm ^ 2 * (a r * a s) := h.trans hapq
      exact le_of_mul_le_mul_left this (by positivity)
    have h0 := hA r s hT'
    simp [hBr', h0]
  have hZb : ∀ p q, |a p * X' p q * a q| ≤ Cm ^ 2 * T * R' := by
    intro p q
    by_cases h : Cm ^ 2 * T ≤ a p * a q
    · have e := hWent p q
      rw [hBz p q h] at e
      have h0 : μ * X' p q = 0 := by rw [← e]; ring
      have hx : X' p q = 0 := (mul_eq_zero.mp h0).resolve_left hμ
      rw [hx]; simp; positivity
    · push_neg at h
      calc |a p * X' p q * a q| = (a p * a q) * |X' p q| := by
            rw [abs_mul, abs_mul, abs_of_pos (hS.pos p), abs_of_pos (hS.pos q)]; ring
        _ ≤ (Cm ^ 2 * T) * R' := mul_le_mul h.le (hX' p q) (abs_nonneg _) (by positivity)
  have hBe : (B i j : ℝ) = (nᵀ * (diagonal a * X' * diagonal a) * n) i j := by
    rw [← hZ]; simp
  rw [hBe]
  apply entry_bound
  intro r s
  have hZe : (diagonal a * X' * diagonal a) r s = a r * X' r s * a s := by
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transpose_apply, hZe, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hnb r i) (hZb r s) (abs_nonneg _) hCm0.le) (hnb s j)
    (abs_nonneg _) (by positivity)

end GlobalTheory.RedBound
end

section

open Matrix GlobalTheory.ClassFin

theorem _root_.GlobalTheory.T.reducedBasis_integral_conj_entries_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) → (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) → (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) → ∀ i j, |(M i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.ReducedBasisBound.integral_conj_bounded | exact GlobalTheory.ReducedBasisBound.integral_conj_bounded | (intros; apply GlobalTheory.ReducedBasisBound.integral_conj_bounded <;> assumption)
end

section

open ValuativeRel GlobalTheory.SplitWeil Matrix

theorem _root_.GlobalTheory.T.exists_schrodinger_intertwiner_integralMatrices : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z : Type) [AddCommGroup Z] (χ : Matrix Y Y' k → Z → ℂ), (∀ a b z, χ (a + b) z = χ a z * χ b z) → (∀ a z z', χ a (z + z') = χ a z * χ a z') → (∀ z, χ 0 z = 1) → (∀ a, χ a 0 = 1) → (∀ n : ℕ, 0 < n → ∀ z : Z, ∃ z' : Z, n • z' = z) → (∀ n : ℕ, 0 < n → Function.Injective fun z : Z => n • z) → (∀ x : Matrix Y Y' k, (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → χ x z = 1) → ∀ r q, x r q ∈ 𝒪[k]) → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Matrix Y Y' k → M →ₗ[ℂ] M) (μ : Z → M →ₗ[ℂ] M), (∀ x x' f, τ x (τ x' f) = τ (x + x') f) → (∀ z z' f, μ z (μ z' f) = μ (z + z') f) → (∀ x z f, τ x (μ z f) = χ x z • μ z (τ x f)) → (∀ f, τ 0 f = f) → (∀ f, μ 0 f = f) → ∀ f₀ : M, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → τ u f₀ = f₀) → (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → μ z f₀ = f₀) → ∃ Tm : SB (Matrix Y Y' k) →ₗ[ℂ] M, (∀ (x : Matrix Y Y' k) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = Φ.1 (t + x)) → Tm Φ' = τ x (Tm Φ)) ∧ (∀ (z : Z) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = χ t z * Φ.1 t) → Tm Φ' = μ z (Tm Φ)) ∧ (∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → Tm Φ = f₀) ∧ ∀ Φ, Tm Φ ∈ Submodule.span ℂ (Set.range fun w : Matrix Y Y' k × Z => τ w.1 (μ w.2 f₀)) := by
  first | exact @GlobalTheory.SchrodExist.exists_intertwiner_matrix | exact GlobalTheory.SchrodExist.exists_intertwiner_matrix | (intros; apply GlobalTheory.SchrodExist.exists_intertwiner_matrix <;> assumption)
end

section

open ValuativeRel GlobalTheory.SplitWeil Matrix

theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_translation_modulation_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ W : Submodule ℂ (Matrix Y Y' k → ℂ), W ≤ SB (Matrix Y Y' k) → (∀ Φ ∈ W, ∀ x : Matrix Y Y' k, (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) → (fun t => Φ (t + x)) ∈ W) → (∀ Φ ∈ W, ∀ b : Matrix Y Y' k, (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ SB (Matrix Y Y' k) → (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ W) → ∀ Φ₀ ∈ W, Φ₀ ≠ 0 → W = SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.IrredSB.sb_irreducible | exact GlobalTheory.IrredSB.sb_irreducible | (intros; apply GlobalTheory.IrredSB.sb_irreducible <;> assumption)
end

section

open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

theorem _root_.GlobalTheory.T.exists_linear_of_bilinear_schwartzBruhatProduct : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  first | exact @GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | exact GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | (intros; apply GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB <;> assumption)
end

section

open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

theorem _root_.GlobalTheory.T.span_schwartzBruhatProduct_eq_top : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y], Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  first | exact @GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | exact GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top | (intros; apply GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top <;> assumption)
end

section

open ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.TAdicInt

def intEquiv (T : ℕ) [Fact T.Prime] : 𝒪[ℚ_[T]] ≃+* ℤ_[T] where
  toFun x := ⟨x.1, by
    have h := (Valuation.mem_integer_iff _ _).1 x.2
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.1 (by rw [map_one]; exact not_lt.2 h)
    rwa [norm_one, not_lt] at this⟩
  invFun x := ⟨x.1, (Valuation.mem_integer_iff _ _).2 (by
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.2 (by rw [norm_one]; exact not_lt.2 x.2)
    rwa [map_one, not_lt] at this)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem card_residueField (T : ℕ) [Fact T.Prime] : Nat.card (ResidueField 𝒪[ℚ_[T]]) = T := by
  rw [Nat.card_congr ((ResidueField.mapEquiv (intEquiv T)).trans PadicInt.residueField).toEquiv, Nat.card_zmod]

theorem irreducible_natCast (T : ℕ) [Fact T.Prime] : Irreducible (T : 𝒪[ℚ_[T]]) := by
  have := (PadicInt.irreducible_p (p := T)).map (intEquiv T).symm.toMulEquiv
  rwa [show (intEquiv T).symm.toMulEquiv (T : ℤ_[T]) = (T : 𝒪[ℚ_[T]]) from
    map_natCast (intEquiv T).symm T] at this

theorem card_residueField_and_irreducible :
    ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧
      Irreducible ((T : 𝒪[ℚ_[T]])) :=
  fun T _ => ⟨card_residueField T, irreducible_natCast T⟩

end GlobalTheory.TAdicInt
end
end
