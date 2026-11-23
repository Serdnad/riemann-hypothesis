module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle003
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
public import Mathlib.Analysis.CStarAlgebra.Basic

@[expose] public section

section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_step {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]
    [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ C : ℝ) (hC : 0 ≤ C)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    (hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    dist ((2 : ℂ) ^ k • iter h k (b, s)) ((2 : ℂ) ^ (k + 1) • iter h (k + 1) (b, s))
      ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
  rw [dist_eq_norm, iter_succ, pow_succ, mul_smul, ← smul_sub, norm_smul, norm_sub_rev]
  have hx := iter_mem_ball b₀ h ρ hcontr hb hs k
  have hxn := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : ‖(2 : ℂ) ^ k‖ = (2 : ℝ) ^ k := by simp
  rw [h2]
  calc (2 : ℝ) ^ k * ‖(2 : ℂ) • h (b, iter h k (b, s)) - iter h k (b, s)‖
      ≤ (2 : ℝ) ^ k * (C * ‖iter h k (b, s)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hquad b hb _ hx) (by positivity)
    _ ≤ (2 : ℝ) ^ k * (C * ((3 / 5) ^ k * ‖s‖) ^ 2) := by gcongr
    _ = C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
        have e : (18 / 25 : ℝ) ^ k = 2 ^ k * ((3 / 5) ^ k) ^ 2 := by
          rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
          norm_num
        rw [e]
        ring

theorem koenigs_limit : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V)
    (ρ C : ℝ), 0 < ρ → 0 ≤ C →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) →
    ∃ L : B × V → V,
      TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • iter h k p) L atTop
        (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧
      ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  intro B V _ _ _ _ _ b₀ h ρ C hρ hC hcontr hquad
  set F : ℕ → B × V → V := fun k p => (2 : ℂ) ^ k • iter h k p with hF
  have hstep : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ k : ℕ,
      dist (F k p) (F (k + 1) p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ k := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩ k
    exact koenigs_step b₀ h ρ C hC hcontr hquad hb hs k
  have hr : (18 / 25 : ℝ) < 1 := by norm_num
  have hcauchy : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, CauchySeq (fun k => F k p) :=
    fun p hp => cauchySeq_of_le_geometric _ _ hr (hstep p hp)
  let L : B × V → V := fun p => limUnder atTop (fun k => F k p)
  have hlim : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, Tendsto (fun k => F k p) atTop (𝓝 (L p)) :=
    fun p hp => (hcauchy p hp).tendsto_limUnder
  have hdist : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ n : ℕ,
      dist (F n p) (L p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ n / (7 / 25) := by
    intro p hp n
    have h1 := dist_le_of_le_geometric_of_tendsto _ _ hr (hstep p hp) (hlim p hp) n
    rwa [show (1 - 18 / 25 : ℝ) = 7 / 25 by norm_num] at h1
  refine ⟨L, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hg : Tendsto (fun n : ℕ => C * ρ ^ 2 * (18 / 25 : ℝ) ^ n / (7 / 25)) atTop (𝓝 0) := by
      have h1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25) hr).const_mul
        (C * ρ ^ 2)).div_const (7 / 25 : ℝ)
      simpa using h1
    filter_upwards [hg.eventually (gt_mem_nhds hε)] with n hn
    rintro ⟨b, s⟩ hp
    rw [dist_comm]
    refine lt_of_le_of_lt ((hdist _ hp n).trans ?_) hn
    have hs : ‖s‖ < ρ := by simpa using hp.2
    have hsle : ‖s‖ ≤ ρ := hs.le
    have hsq : ‖s‖ ^ 2 ≤ ρ ^ 2 := by gcongr
    show C * ‖s‖ ^ 2 * (18 / 25) ^ n / (7 / 25) ≤ C * ρ ^ 2 * (18 / 25) ^ n / (7 / 25)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq hC
  · intro b hb s hs
    have h0 := hdist (b, s) ⟨hb, hs⟩ 0
    have e0 : F 0 (b, s) = s := by simp [hF]
    rw [e0, dist_comm, dist_eq_norm] at h0
    calc ‖L (b, s) - s‖ ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ 0 / (7 / 25) := h0
      _ ≤ 4 * C * ‖s‖ ^ 2 := by
        rw [pow_zero, mul_one, div_le_iff₀ (by norm_num)]
        nlinarith [mul_nonneg hC (sq_nonneg ‖s‖)]

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_limit_additive_for_law : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  intro B V _ _ _ _ b₀ h μ L ρ C _hρ hC hcontr happrox hhom hlim b hb s hs t ht hm
  have hsk := fun k => iter_mem_ball b₀ h ρ hcontr hb hs k
  have htk := fun k => iter_mem_ball b₀ h ρ hcontr hb ht k
  have hiter : ∀ k : ℕ, iter h k (b, μ (b, s, t)) = μ (b, iter h k (b, s), iter h k (b, t)) := by
    intro k
    induction k with
    | zero => rw [iter_zero, iter_zero, iter_zero]
    | succ k ih =>
      rw [iter_succ, iter_succ, iter_succ, ih]
      exact hhom b hb _ (hsk k) _ (htk k)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have herr : Tendsto (fun k : ℕ => (2 : ℂ) ^ k •
      (μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t))) atTop (𝓝 0) := by
    have hg : Tendsto (fun k : ℕ => C * ‖s‖ * ‖t‖ * (18 / 25 : ℝ) ^ k) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25)
        (by norm_num : (18 / 25 : ℝ) < 1)
      simpa using this.const_mul (C * ‖s‖ * ‖t‖)
    refine squeeze_zero_norm (fun k => ?_) hg
    rw [norm_smul, norm_pow, hn2]
    have h1 := happrox b hb _ (hsk k) _ (htk k)
    have h2 := norm_iter_le b₀ h ρ hcontr hb hs k
    have h3 := norm_iter_le b₀ h ρ hcontr hb ht k
    calc (2 : ℝ) ^ k * ‖μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t)‖
        ≤ 2 ^ k * (C * ‖iter h k (b, s)‖ * ‖iter h k (b, t)‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 ^ k * (C * ((3 / 5) ^ k * ‖s‖) * ((3 / 5) ^ k * ‖t‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (norm_nonneg _)
            (mul_nonneg hC (by positivity))
      _ = C * ‖s‖ * ‖t‖ * (18 / 25) ^ k := by
          rw [show (18 / 25 : ℝ) = 2 * (3 / 5) * (3 / 5) by norm_num, mul_pow, mul_pow]
          ring
  have hsum : Tendsto (fun k : ℕ => (2 : ℂ) ^ k • iter h k (b, μ (b, s, t))) atTop
      (𝓝 (L (b, s) + L (b, t) + 0)) := by
    refine (((hlim b hb s hs).add (hlim b hb t ht)).add herr).congr (fun k => ?_)
    rw [hiter k, smul_sub, smul_sub]
    abel
  rw [add_zero] at hsum
  exact tendsto_nhds_unique (hlim b hb _ hm) hsum

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial GroundTheory.Heights₂.Heights

theorem mem_antisymSpace_of_pointwise :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : MvPolynomial (Ψ × Fin N) ℝ),
      R.IsHomogeneous (antisymDegree Ψ N + 1) →
      (∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) →
        ∀ lam : Ψ × Fin N → ℝ, eval lam R + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) R = 0) →
      R ∈ antisymSpace Ψ N j := by
  intro Ψ _ _ N j R hR h
  refine ⟨(mem_homogeneousSubmodule _ _).2 hR, ?_⟩
  rintro σ ⟨τ, a, b, hab, hblock, rfl⟩
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_rename, map_neg]
  exact eq_neg_of_add_eq_zero_right (h τ a b hab hblock lam)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open Set Filter Topology Metric

theorem _root_.GlobalTheory.T.analytic_group_law_bounded_commutator : ∀ {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (b₀ : B) (G : B × V × V → W) (R : ℝ), 0 < R → DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R) → (∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1) → (∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) → ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | exact GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | (intros; apply GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcNorm_norm_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hz
  have h3 : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [← h2]
  rw [h3, Complex.norm_real]
  simp only [Complex.ofReal_re, Real.norm_eq_abs]
  exact abs_of_pos (by simpa using h1)

theorem fcNorm_arith {ne nw ns h₁ h₂ t u : ℝ} (hh₂ : 0 < h₂) (ht : 0 < t)
    (hnw : nw * h₂ = t) (hmain : ne * ne * h₂ * h₁ = t * u * ns) :
    (ne / nw) ^ 2 * h₁ = u * t⁻¹ * ns * h₂ := by
  have hnw' : nw = t / h₂ := by field_simp; exact hnw
  have e : (ne / (t / h₂)) ^ 2 * h₁ = (ne * ne * h₂ * h₁) * h₂ / t ^ 2 := by
    field_simp
  rw [hnw', e, hmain]
  field_simp

theorem fcNorm : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (A' : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (S : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (H₁ : Matrix (Fin p) (Fin p) ℂ) (H₂ : Matrix (Fin q) (Fin q) ℂ), H₁.PosDef → H₂.PosDef → S.det ≠ 0 → Aᵀ * H₁ * A.map star - (A'ᵀ * H₂ * A'.map star)ᵀ = (2 * Complex.I) • S → A * ((Sᵀ)⁻¹ * A'ᵀ) = 0 ∧ A.rank = p ∧ ((Sᵀ)⁻¹ * A'ᵀ).rank = q ∧ ‖(fromRows ((Sᵀ)⁻¹ * A'ᵀ)ᴴ A).det / (((Sᵀ)⁻¹ * A'ᵀ)ᴴ * ((Sᵀ)⁻¹ * A'ᵀ)).det‖ ^ 2 * H₁.det.re = 2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by
  intro p q A A' S H₁ H₂ hH₁ hH₂ hS h
  have hd₁ : 0 < H₁.det := hH₁.det_pos
  have hd₂ : 0 < H₂.det := hH₂.det_pos
  have hn₁ := fcNorm_norm_of_pos hd₁
  have hn₂ := fcNorm_norm_of_pos hd₂
  have hr₂ : 0 < H₂.det.re := (Complex.lt_def.mp hd₂).1
  have hc : (2 * Complex.I : ℂ) ≠ 0 := by simp
  have hnc : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  have hAstar : (A.map star)ᵀ = Aᴴ := by ext i j; simp [conjTranspose_apply]
  have hB'H : (A'.map star)ᴴ = A'ᵀ := by ext i j; simp [conjTranspose_apply]
  have hT : Aᴴ * H₁ᵀ * A - A'ᵀ * H₂ * A'.map star = (2 * Complex.I) • Sᵀ := by
    have := congrArg Matrix.transpose h
    rw [transpose_sub, transpose_transpose, transpose_smul, transpose_mul, transpose_mul,
      transpose_transpose, hAstar, ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨B', hB'⟩ : ∃ B', B' = A'.map star := ⟨_, rfl⟩
  rw [← hB'] at hT hB'H
  obtain ⟨E, hE⟩ : ∃ E, E = fromRows B' A := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = fromCols (-(A'ᵀ * H₂)) (Aᴴ * H₁ᵀ) := ⟨_, rfl⟩
  have hME : M * E = (2 * Complex.I) • Sᵀ := by
    rw [hM, hE, fromCols_mul_fromRows, ← hT, Matrix.neg_mul]
    abel
  have hMD : M = Eᴴ * fromBlocks (-H₂) 0 0 H₁ᵀ := by
    rw [hM, hE, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, hB'H]
    simp
  have hdetME : M.det * E.det = (2 * Complex.I) ^ (q + p) * S.det := by
    rw [← det_mul, hME, det_smul, det_transpose]
    simp
  have hne : (2 * Complex.I) ^ (q + p) * S.det ≠ 0 := mul_ne_zero (pow_ne_zero _ hc) hS
  have hMu : IsUnit M := (isUnit_iff_isUnit_det M).mpr
    (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul (hdetME ▸ hne)))
  have hEdet : E.det ≠ 0 := right_ne_zero_of_mul (hdetME ▸ hne)
  have hEu : IsUnit E := (isUnit_iff_isUnit_det E).mpr (isUnit_iff_ne_zero.mpr hEdet)
  have hmain : ‖E.det‖ * ‖E.det‖ * H₂.det.re * H₁.det.re
      = (2 : ℝ) ^ q * 2 ^ p * ‖S.det‖ := by
    have h1 := congrArg norm hdetME
    rw [hMD, det_mul, det_conjTranspose, det_fromBlocks_zero₂₁, det_neg, det_transpose] at h1
    simp only [norm_mul, norm_pow, hnc, norm_star, norm_neg, norm_one, one_pow, one_mul, hn₁, hn₂,
      Fintype.card_fin] at h1
    rw [pow_add] at h1
    linarith
  have hSu : IsUnit (Sᵀ).det := by
    rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hS
  have hSinv : Sᵀ * (Sᵀ)⁻¹ = 1 := mul_nonsing_inv _ hSu
  have hH₂u : IsUnit H₂.det := isUnit_iff_ne_zero.mpr hd₂.ne'
  have hH₂inv : H₂ * H₂⁻¹ = 1 := mul_nonsing_inv _ hH₂u
  have hH₂inv' : H₂⁻¹ * H₂ = 1 := nonsing_inv_mul _ hH₂u
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = (Sᵀ)⁻¹ * A'ᵀ := ⟨_, rfl⟩
  rw [← hΦ]
  have hEΦ : E * Φ = fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
    have hMi : M⁻¹ * M = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).mp hMu)
    have hkey : M * (E * Φ)
        = M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ) := by
      rw [← Matrix.mul_assoc, hME, hΦ, Matrix.smul_mul, ← Matrix.mul_assoc, hSinv, Matrix.one_mul]
      rw [hM, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.mul_smul, Matrix.neg_mul,
        Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hH₂inv, Matrix.mul_one]
    calc E * Φ = M⁻¹ * (M * (E * Φ)) := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
      _ = M⁻¹ * (M * fromRows ((2 * Complex.I) • (-H₂⁻¹)) (0 : Matrix (Fin p) (Fin q) ℂ)) := by
        rw [hkey]
      _ = _ := by rw [← Matrix.mul_assoc, hMi, Matrix.one_mul]
  rw [hE, fromRows_mul] at hEΦ
  obtain ⟨hBΦ, hAΦ⟩ := fromRows_inj hEΦ
  have hrA : A.rank = p := by
    obtain ⟨X, hXd⟩ : ∃ X, X = E⁻¹ * fromRows (0 : Matrix (Fin q) (Fin p) ℂ)
        (1 : Matrix (Fin p) (Fin p) ℂ) := ⟨_, rfl⟩
    have hX : E * X = fromRows 0 1 := by
      rw [hXd, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hEdet), Matrix.one_mul]
    rw [hE, fromRows_mul] at hX
    obtain ⟨-, hX2⟩ := fromRows_inj hX
    have h1 := rank_mul_le_left A X
    rw [hX2, rank_one, Fintype.card_fin] at h1
    have h2 := rank_le_card_height A
    rw [Fintype.card_fin] at h2
    omega
  have hw : (B' * Φ).det * H₂.det = (-(2 * Complex.I)) ^ q := by
    have e : (2 * Complex.I) • (-1 : Matrix (Fin q) (Fin q) ℂ) = (-(2 * Complex.I)) • 1 := by simp
    rw [← det_mul, hBΦ, Matrix.smul_mul, Matrix.neg_mul, hH₂inv', e, det_smul, det_one,
      Fintype.card_fin, mul_one]
  have hwne : (B' * Φ).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hw
    exact pow_ne_zero _ (neg_ne_zero.mpr hc) hw.symm
  have hrΦ : Φ.rank = q := by
    have h1 := rank_mul_le_right B' Φ
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hwne)),
      Fintype.card_fin] at h1
    have h2 := rank_le_card_width Φ
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨hy, -, hN⟩ := fcIndep p q A Φ hAΦ hrA hrΦ
  have hN' := hN B'
  rw [← hE] at hN'
  refine ⟨hAΦ, hrA, hrΦ, ?_⟩
  have hq : (fromRows Φᴴ A).det / (Φᴴ * Φ).det = E.det / (B' * Φ).det := by
    field_simp
    linear_combination -hN'
  have hnw : ‖(B' * Φ).det‖ * H₂.det.re = (2 : ℝ) ^ q := by
    have := congrArg norm hw
    simpa [hn₂, hnc] using this
  rw [hq, norm_div, inv_pow]
  have hfin := fcNorm_arith (ne := ‖E.det‖) (ns := ‖S.det‖) (h₁ := H₁.det.re) (u := (2:ℝ)^p) hr₂
    (by positivity) hnw hmain
  exact hfin

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.dominated_convergence_exhaustion : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ) (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ), (∀ n, MeasurableSet (E n)) → Monotone E → (∀ n, μ (E n) < ⊤) → (∀ᵐ y ∂μ, ∃ n, y ∈ E n) → (∀ᵐ y ∂μ, 0 ≤ L y) → 0 ≤ a → Tendsto b atTop (𝓝 0) → (∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) → (∀ n, TendstoUniformlyOn Γ Γ0 l (E n)) → (∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M) → (∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧ (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧ ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) → Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧ Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | exact GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | (intros; apply GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion <;> assumption)
end
