module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermCOrthonormalCoordinates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscrMulHermitianIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace IsotropicThreshold

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem c_pos (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  positivity

theorem iso_threshold (X : Data E r) : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ x ∈ X.dom, ∀ v ∈ X.Λ,
    ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 → herm X.Gm v v = 0 := by
  classical
  have hcpos := c_pos X
  obtain ⟨D, hD, hDb⟩ : ∃ D : ℝ, 0 < D ∧ ∀ σ : E →+* ℂ, ‖σ (X.den : E)‖ ≤ D := by
    refine ⟨∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ + 1, by positivity, fun σ => ?_⟩
    have := Finset.single_le_sum (f := fun σ : E →+* ℂ => ‖σ (X.den : E)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
    linarith
  set S := ∑ τ : X.Ψ, (X.c τ)⁻¹ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => (inv_pos.2 (hcpos τ)).le
  have hcl : ∀ τ, (S + 1)⁻¹ ≤ X.c τ := fun τ => by
    have h1 : (X.c τ)⁻¹ ≤ S := Finset.single_le_sum (f := fun τ => (X.c τ)⁻¹)
      (fun τ _ => (inv_pos.2 (hcpos τ)).le) (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  refine ⟨(S + 1)⁻¹ / D, div_pos (inv_pos.2 (by linarith)) hD, ?_⟩
  intro x hx v hv hsum
  have hmaj0 : ∀ τ : X.Ψ, 0 ≤ X.maj x τ (Data.emb τ.1 v) := fun τ =>
    (norm_nonneg _).trans (UnipotentCoefficientShift.norm_hermC_le_maj hx τ _)
  have hterm : ∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) < (S + 1)⁻¹ / D := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v))
      (fun τ _ => mul_nonneg (hcpos τ).le (hmaj0 τ)) (Finset.mem_univ τ)) hsum
  have hmaj : ∀ τ : X.Ψ, D * X.maj x τ (Data.emb τ.1 v) < 1 := fun τ => by
    have h3 := hcpos τ
    have h5 : X.c τ * X.maj x τ (Data.emb τ.1 v) < X.c τ / D :=
      lt_of_lt_of_le (hterm τ) (div_le_div_of_nonneg_right (hcl τ) hD.le)
    rw [lt_div_iff₀ hD] at h5
    nlinarith
  have hemb : ∀ τ : E →+* ℂ,
      hermC τ X.Gm (Data.emb τ v) (Data.emb τ v) = τ (herm X.Gm v v) := by
    intro τ

    simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]
  have ha : IsIntegral ℤ ((X.den : E) * herm X.Gm v v) := X.Λ_int v hv v hv
  have hzero := UnipotentCoefficientShift.eq_zero_of_conj_lt_one ha (fun σ => by
    obtain ⟨τ, h1, h2⟩ : ∃ τ : X.Ψ, ‖σ (herm X.Gm v v)‖ = ‖τ.1 (herm X.Gm v v)‖ ∧
        ‖σ (X.den : E)‖ = ‖τ.1 (X.den : E)‖ := by
      by_cases hσ : σ ∈ X.Ψ
      · exact ⟨⟨σ, hσ⟩, rfl, rfl⟩
      · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ X.Ψ := by
          by_contra h
          exact hσ ((X.cmType σ).2 h)
        refine ⟨⟨_, hc⟩, ?_, ?_⟩ <;> simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [map_mul, norm_mul, h1]
    have hb := UnipotentCoefficientShift.norm_hermC_le_maj hx τ (Data.emb τ.1 v)
    rw [hemb] at hb
    calc ‖σ (X.den : E)‖ * ‖τ.1 (herm X.Gm v v)‖ ≤ D * X.maj x τ (Data.emb τ.1 v) :=
          mul_le_mul (hDb σ) hb (norm_nonneg _) hD.le
      _ < 1 := hmaj τ)
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd h (NumberField.RingOfIntegers.coe_ne_zero_iff.2 X.den_ne)
  · exact h

end IsotropicThreshold

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

lemma real_upper {ρ α β Q : ℝ} (hρ1 : ρ < 1) (hρ0 : 0 ≤ ρ)
    (hQ : Q * (1 - ρ ^ 2) ≤ (α + ρ * β) ^ 2) :
    2 * Q - (α ^ 2 - β ^ 2) ≤ (1 + ρ) / (1 - ρ) * (α ^ 2 + β ^ 2) := by
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 + ρ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith [mul_nonneg hρ0 (sq_nonneg (α - β)), mul_le_mul_of_nonneg_left hQ h2.le]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma mj_xZ_zero (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show (mat x τ * X.lowBlock 0 τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [h1, Matrix.mul_one]
  rfl

private lemma nsq_add_fundamental_domains {n : ℕ} (p q : Fin n → ℂ) :
    nsq (p + q) = nsq p + 2 * (mjip p q).re + nsq q := by
  rw [show p + q = p - ((-1 : ℝ) : ℂ) • q by simp, mjnsq_sub_smul]
  ring

private lemma re_mjip_comm {n : ℕ} (p q : Fin n → ℂ) : (mjip q p).re = (mjip p q).re := by
  simp only [mjip, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

private lemma mjip_sub_left {n : ℕ} (p q δ : Fin n → ℂ) :
    mjip (p - q) δ = mjip p δ - mjip q δ := by
  simp [mjip, sub_mul, Finset.sum_sub_distrib]

private lemma re_mjip_le_sqrt_nsq_mul {n : ℕ} (p q : Fin n → ℂ) :
    (mjip p q).re ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) :=
  (Complex.re_le_norm _).trans (mjip_norm_le p q)

private lemma neg_re_mjip_le_sqrt_nsq_mul {n : ℕ} (p q : Fin n → ℂ) :
    -(mjip p q).re ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) :=
  (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (mjip_norm_le p q))

private lemma sqrt_nsq_mulVec_le_opN_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    Real.sqrt (nsq (A *ᵥ v)) ≤ Data.opN A * Real.sqrt (nsq v) := by
  rw [← Real.sqrt_sq (opN_nonneg A), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (nsq_mulVec_le_opN A v)



theorem mj_bounds {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1 / 10) {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (hy : X.xZ x Z ∈ X.dom) (τ : X.Ψ)
    (v : Fin r → ℂ) :
    (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
      X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v := by
  obtain ⟨w, rfl⟩ : ∃ w, v = mat x τ *ᵥ w := ⟨(mat x τ)⁻¹ *ᵥ v, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr ((X.mem_dom_iff x).1 hx τ).1), Matrix.one_mulVec]⟩
  have hx0 : X.xZ x 0 ∈ X.dom := by rw [mj_xZ_zero]; exact hx
  obtain ⟨γ0, h0maj, h0id⟩ := mj_coord X ho 0 hx0 τ w
  rw [mj_xZ_zero] at h0maj
  have hZ0 : Matrix.of ((0 : X.Coord) τ) = 0 := by ext; rfl
  have hγ0 : γ0 = mjpa X w := by
    funext d
    have := h0id (Pi.single d 1)
    simp only [hZ0, Matrix.zero_mulVec, mjip_zero_right, sub_zero, mjip_single] at this
    exact this.symm
  have hmx : X.maj x τ (mat x τ *ᵥ w) = nsq (mjpa X w) + nsq (mjpb X w) := by
    rw [h0maj, hZ0, Matrix.zero_mulVec, nsq_zero', hγ0]
    ring
  obtain ⟨γ, hmaj, hid⟩ := mj_coord X ho Z hy τ w
  rw [hmx, hmaj]
  have hk0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := opN_nonneg _
  have hkρ : Data.opN (Matrix.of (Z τ)) ≤ ρ := (opN_le_zN X Z τ).trans hZ
  have hs2 : nsq (Matrix.of (Z τ) *ᵥ γ) ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq γ :=
    nsq_mulVec_le_opN _ _
  have hS : Real.sqrt (nsq (Matrix.of (Z τ) *ᵥ γ)) ≤ Data.opN (Matrix.of (Z τ)) * Real.sqrt (nsq γ) :=
    sqrt_nsq_mulVec_le_opN_mul _ _
  have hdid : ∀ δ, mjip (mjpa X w - γ) δ =
      mjip (mjpb X w - Matrix.of (Z τ) *ᵥ γ) (Matrix.of (Z τ) *ᵥ δ) := by
    intro δ
    rw [mjip_sub_left, mjip_sub_left]
    linear_combination hid δ
  set Zm := Matrix.of (Z τ) with hZm
  set k := Data.opN Zm with hkdef
  set d := mjpa X w - γ with hd
  set t := mjpb X w - Zm *ᵥ γ with ht
  have hG0 := Real.sqrt_nonneg (nsq γ)
  have hT0 := Real.sqrt_nonneg (nsq t)
  have hD0 := Real.sqrt_nonneg (nsq d)
  have hG2 := Real.sq_sqrt (nsq_nonneg γ)
  have hT2 := Real.sq_sqrt (nsq_nonneg t)
  have hD2 := Real.sq_sqrt (nsq_nonneg d)
  have hDs : Real.sqrt (nsq d) ≤ k * Real.sqrt (nsq t) := by
    have h1 : nsq d = (mjip t (Zm *ᵥ d)).re := by rw [← hdid, mjip_self, Complex.ofReal_re]
    have h2 := re_mjip_le_sqrt_nsq_mul t (Zm *ᵥ d)
    have h4 : Real.sqrt (nsq (Zm *ᵥ d)) ≤ k * Real.sqrt (nsq d) := sqrt_nsq_mulVec_le_opN_mul Zm d
    have h5 : Real.sqrt (nsq d) ^ 2 ≤ Real.sqrt (nsq t) * (k * Real.sqrt (nsq d)) := by
      calc Real.sqrt (nsq d) ^ 2 = nsq d := hD2
        _ = (mjip t (Zm *ᵥ d)).re := h1
        _ ≤ _ := h2.trans (mul_le_mul_of_nonneg_left h4 hT0)
    rcases eq_or_lt_of_le hD0 with h | h
    · rw [← h]
      positivity
    · nlinarith
  have hdd : nsq d ≤ k ^ 2 * nsq t := by
    calc nsq d = Real.sqrt (nsq d) ^ 2 := hD2.symm
      _ ≤ (k * Real.sqrt (nsq t)) ^ 2 := pow_le_pow_left₀ hD0 hDs 2
      _ = k ^ 2 * nsq t := by rw [mul_pow, hT2]
  have hAe : nsq (mjpa X w) = nsq γ + 2 * (mjip γ d).re + nsq d := by
    rw [show mjpa X w = γ + d by rw [hd]; abel, nsq_add_fundamental_domains]
  have hBe : nsq (mjpb X w) = nsq (Zm *ᵥ γ) + 2 * (mjip (Zm *ᵥ γ) t).re + nsq t := by
    rw [show mjpb X w = Zm *ᵥ γ + t by rw [ht]; abel, nsq_add_fundamental_domains]
  have hcross : (mjip γ d).re = (mjip (Zm *ᵥ γ) t).re := by
    rw [re_mjip_comm d γ, hdid γ, re_mjip_comm (Zm *ᵥ γ) t]
  have hs2' : nsq (Zm *ᵥ γ) ≤ k ^ 2 * nsq γ := hs2
  have hS' : Real.sqrt (nsq (Zm *ᵥ γ)) ≤ k * Real.sqrt (nsq γ) := hS
  have hk1 : k < 1 := by linarith
  refine ⟨?_, ?_⟩
  · have hlow : (1 - k ^ 2) * (nsq γ + nsq t) ≤
        2 * (nsq γ - nsq (Zm *ᵥ γ)) - (nsq (mjpa X w) - nsq (mjpb X w)) := by
      rw [hAe, hBe, hcross]
      nlinarith [hs2', hdd]
    have r1 : (mjip γ d).re ≤ Real.sqrt (nsq γ) * (k * Real.sqrt (nsq t)) :=
      (re_mjip_le_sqrt_nsq_mul γ d).trans (mul_le_mul_of_nonneg_left hDs hG0)
    have r2 : (mjip (Zm *ᵥ γ) t).re ≤ (k * Real.sqrt (nsq γ)) * Real.sqrt (nsq t) :=
      (re_mjip_le_sqrt_nsq_mul (Zm *ᵥ γ) t).trans (mul_le_mul_of_nonneg_right hS' hT0)
    have hAB : nsq (mjpa X w) + nsq (mjpb X w) ≤ (1 + k) ^ 2 * (nsq γ + nsq t) := by
      rw [hAe, hBe]
      nlinarith [mul_nonneg hk0 (sq_nonneg (Real.sqrt (nsq γ) - Real.sqrt (nsq t)))]
    have hc : (1 - ρ) / (1 + ρ) ≤ (1 - k) / (1 + k) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hAB0 : 0 ≤ nsq (mjpa X w) + nsq (mjpb X w) := add_nonneg (nsq_nonneg _) (nsq_nonneg _)
    calc (1 - ρ) / (1 + ρ) * (nsq (mjpa X w) + nsq (mjpb X w))
        ≤ (1 - k) / (1 + k) * (nsq (mjpa X w) + nsq (mjpb X w)) := mul_le_mul_of_nonneg_right hc hAB0
      _ ≤ (1 - k) / (1 + k) * ((1 + k) ^ 2 * (nsq γ + nsq t)) :=
          mul_le_mul_of_nonneg_left hAB (div_nonneg (by linarith) (by linarith))
      _ = (1 - k ^ 2) * (nsq γ + nsq t) := by
          field_simp
          ring
      _ ≤ _ := hlow
  · have hQid : nsq γ - nsq (Zm *ᵥ γ) = (mjip (mjpa X w) γ).re - (mjip (mjpb X w) (Zm *ᵥ γ)).re := by
      have := congrArg Complex.re (hid γ)
      simp only [Complex.sub_re, mjip_self, Complex.ofReal_re] at this
      linarith
    have r3 := re_mjip_le_sqrt_nsq_mul (mjpa X w) γ
    have r4 := neg_re_mjip_le_sqrt_nsq_mul (mjpb X w) (Zm *ᵥ γ)
    have hβ0 := Real.sqrt_nonneg (nsq (mjpb X w))
    have hα0 := Real.sqrt_nonneg (nsq (mjpa X w))
    have r5 : Real.sqrt (nsq (mjpb X w)) * Real.sqrt (nsq (Zm *ᵥ γ)) ≤
        Real.sqrt (nsq (mjpb X w)) * (ρ * Real.sqrt (nsq γ)) :=
      mul_le_mul_of_nonneg_left (hS'.trans (mul_le_mul_of_nonneg_right hkρ hG0)) hβ0
    have hQle : nsq γ - nsq (Zm *ᵥ γ) ≤
        (Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w))) * Real.sqrt (nsq γ) := by
      rw [hQid]
      linarith [r3, r4, r5]
    have hkk : k ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hk0 hkρ 2
    have hQge : (1 - ρ ^ 2) * nsq γ ≤ nsq γ - nsq (Zm *ᵥ γ) := by
      linarith [hs2', mul_le_mul_of_nonneg_right hkk (nsq_nonneg γ)]
    have hρ2 : 0 ≤ 1 - ρ ^ 2 := by
      have : ρ ^ 2 ≤ ρ := by
        rw [sq]
        exact mul_le_of_le_one_left hρ0.le (by linarith)
      linarith
    have hQ0 : 0 ≤ nsq γ - nsq (Zm *ᵥ γ) := le_trans (mul_nonneg hρ2 (nsq_nonneg γ)) hQge
    have hup : (nsq γ - nsq (Zm *ᵥ γ)) * (1 - ρ ^ 2) ≤
        (Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w))) ^ 2 := by
      set s := Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w)) with hs
      set Q := nsq γ - nsq (Zm *ᵥ γ) with hQ
      rcases eq_or_lt_of_le hQ0 with hq | hq
      · rw [← hq, zero_mul]
        positivity
      · have hsq : Q ^ 2 ≤ (s * Real.sqrt (nsq γ)) ^ 2 := pow_le_pow_left₀ hQ0 hQle 2
        rw [mul_pow, hG2] at hsq
        nlinarith [mul_le_mul_of_nonneg_left hQge (sq_nonneg s), mul_le_mul_of_nonneg_right hsq hρ2]
    have := real_upper (ρ := ρ) (α := Real.sqrt (nsq (mjpa X w))) (β := Real.sqrt (nsq (mjpb X w)))
      (Q := nsq γ - nsq (Zm *ᵥ γ)) (by linarith) hρ0.le hup
    rwa [Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at this

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem unipotent_lattice_lift : UnipotentLatticeLift (E := E) := by
  intro r X u hu hmem
  exact ⟨fun b hb => X.exists_gamma u hu hmem b hb,
    fun la P hP hχ b hb x hx => X.LZ_periodic u hu hmem la P hP hχ b hb x hx,
    fun χ hχ hf => X.freq_to_beta χ hχ hf⟩

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

lemma opN_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ v, OrthonormalChartBounds.nsq (A *ᵥ v) ≤ δ ^ 2 * OrthonormalChartBounds.nsq v) : Data.opN A ≤ δ := by
  unfold Data.opN
  apply Real.sSup_le _ hδ
  rintro t ⟨v, hv, rfl⟩
  have hpos : 0 < ∑ j, ‖v j‖ ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hj) 2)
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖v i‖) (Finset.mem_univ j))
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)]
  calc Real.sqrt (∑ i, ‖(A *ᵥ v) i‖ ^ 2) ≤ Real.sqrt (δ ^ 2 * ∑ j, ‖v j‖ ^ 2) := Real.sqrt_le_sqrt (h v)
    _ = δ * Real.sqrt (∑ j, ‖v j‖ ^ 2) := by rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma exists_Z (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (y : Fin r → Fin r → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, X.p0 ≤ (j : ℕ) → w j = 0) →
      ReciprocityTheory.MultiplicativeHeights.negSq X.p0 ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j) ≤
        δ ^ 2 * ReciprocityTheory.MultiplicativeHeights.posSq X.p0 ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j) ∧
      (w ≠ 0 → 0 < (ReciprocityTheory.MultiplicativeHeights.jForm X.p0 ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j)
        ((mat x τ)⁻¹ *ᵥ ∑ j, w j • y j)).re)) :
    ∃ Zτ : Fin (r - X.p0) → Fin X.p0 → ℂ, Data.opN (Matrix.of Zτ) ≤ δ ∧
      ∀ Z : X.Coord, Z τ = Zτ →
        Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le a)) =
          Submodule.span ℂ (Set.range fun a : Fin X.p0 => y (Fin.castLE X.p0_le a)) := by
  classical
  set Q := (mat x τ)⁻¹ with hQ
  have hinv : ∀ u : Fin r → ℂ, mat x τ *ᵥ (Q *ᵥ u) = u := fun u => by
    rw [hQ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hx τ).1), Matrix.one_mulVec]
  set c : Fin X.p0 → Fin r → ℂ := fun a => Q *ᵥ y (Fin.castLE X.p0_le a) with hc
  set A : Matrix (Fin X.p0) (Fin X.p0) ℂ := Matrix.of fun i a => c a (Fin.castLE X.p0_le i) with hA
  set B : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ := Matrix.of fun m a => c a (OrthonormalChartBounds.nI X m) with hB
  have hcomb : ∀ w' : Fin X.p0 → ℂ, ∃ w : Fin r → ℂ, (∀ j : Fin r, X.p0 ≤ (j : ℕ) → w j = 0) ∧
      (w' ≠ 0 → w ≠ 0) ∧ Q *ᵥ ∑ j, w j • y j = ∑ a, w' a • c a := by
    intro w'
    refine ⟨fun j => if h : (j : ℕ) < X.p0 then w' ⟨j, h⟩ else 0, fun j hj => dif_neg (by omega), ?_, ?_⟩
    · intro hw' hw
      apply hw'
      funext a
      have := congrFun hw (Fin.castLE X.p0_le a)
      simpa [Fin.val_castLE, a.isLt] using this
    · simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
      rw [PositiveSpanMatrices.sum_split X.p0_le]
      simp [PositiveSpanMatrices.kap, Fin.val_castLE, hc]
  have hpa : ∀ w' : Fin X.p0 → ℂ, OrthonormalChartBounds.mjpa X (∑ a, w' a • c a) = A *ᵥ w' := fun w' => by
    funext i
    simp [OrthonormalChartBounds.mjpa, hA, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hpb : ∀ w' : Fin X.p0 → ℂ, OrthonormalChartBounds.mjpb X (∑ a, w' a • c a) = B *ᵥ w' := fun w' => by
    funext m
    simp [OrthonormalChartBounds.mjpb, hB, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hpos : ∀ u : Fin r → ℂ, ReciprocityTheory.MultiplicativeHeights.posSq X.p0 u = OrthonormalChartBounds.nsq (OrthonormalChartBounds.mjpa X u) := fun u => by
    unfold ReciprocityTheory.MultiplicativeHeights.posSq OrthonormalChartBounds.nsq OrthonormalChartBounds.mjpa
    rw [PositiveSpanMatrices.sum_split X.p0_le]
    simp [PositiveSpanMatrices.kap, Fin.val_castLE]
  have hneg : ∀ u : Fin r → ℂ, ReciprocityTheory.MultiplicativeHeights.negSq X.p0 u = OrthonormalChartBounds.nsq (OrthonormalChartBounds.mjpb X u) := fun u => by
    unfold ReciprocityTheory.MultiplicativeHeights.negSq OrthonormalChartBounds.nsq OrthonormalChartBounds.mjpb
    rw [PositiveSpanMatrices.sum_split X.p0_le]
    simp [PositiveSpanMatrices.kap, OrthonormalChartBounds.nI, Fin.val_castLE]
  have hjre : ∀ u : Fin r → ℂ, (ReciprocityTheory.MultiplicativeHeights.jForm X.p0 u u).re =
      ReciprocityTheory.MultiplicativeHeights.posSq X.p0 u - ReciprocityTheory.MultiplicativeHeights.negSq X.p0 u := fun u => by
    unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.posSq ReciprocityTheory.MultiplicativeHeights.negSq ReciprocityTheory.MultiplicativeHeights.sgn
    rw [Complex.re_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.conj_mul']
    split_ifs <;> simp [← Complex.ofReal_pow]
  have hkey : ∀ w' : Fin X.p0 → ℂ, OrthonormalChartBounds.nsq (B *ᵥ w') ≤ δ ^ 2 * OrthonormalChartBounds.nsq (A *ᵥ w') ∧
      (w' ≠ 0 → OrthonormalChartBounds.nsq (B *ᵥ w') < OrthonormalChartBounds.nsq (A *ᵥ w')) := fun w' => by
    obtain ⟨w, hw0, hne, hw⟩ := hcomb w'
    obtain ⟨h1, h2⟩ := hg w hw0
    rw [hw, hneg, hpos, hpb, hpa] at h1
    refine ⟨h1, fun h => ?_⟩
    have := h2 (hne h)
    rw [hw, hjre, hneg, hpos, hpb, hpa] at this
    linarith
  have hAdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := (hkey v).2 hv
    rw [hAv, OrthonormalChartBounds.nsq_zero'] at this
    linarith [OrthonormalChartBounds.nsq_nonneg (B *ᵥ v)]
  have hext : ∀ u u' : Fin r → ℂ, OrthonormalChartBounds.mjpa X u = OrthonormalChartBounds.mjpa X u' → OrthonormalChartBounds.mjpb X u = OrthonormalChartBounds.mjpb X u' →
      u = u' := by
    intro u u' ha hb
    funext k
    rcases PositiveSpanMatrices.fin_cases_split X.p0_le k with ⟨b, rfl⟩ | ⟨m, rfl⟩
    · exact congrFun ha b
    · exact congrFun hb m
  refine ⟨B * A⁻¹, ?_, fun Z hZ => ?_⟩
  · apply opN_le _ hδ
    intro v
    have hAv : A *ᵥ (A⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hAdet), Matrix.one_mulVec]
    have := (hkey (A⁻¹ *ᵥ v)).1
    rw [hAv, Matrix.mulVec_mulVec] at this
    exact this
  · have hsgl : ∀ b : Fin X.p0, (fun a => A a b) = A *ᵥ Pi.single b 1 := fun b => by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have e2 : ∀ b : Fin X.p0, OrthonormalChartBounds.mjg X Z τ (fun a => A a b) = c b := fun b => by
      apply hext
      · rw [OrthonormalChartBounds.mjg_pa]
        rfl
      · rw [OrthonormalChartBounds.mjg_pb, hZ, hsgl b]
        change (B * A⁻¹) *ᵥ (A *ᵥ Pi.single b 1) = _
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hAdet),
          Matrix.mul_one]
        funext m
        simp [OrthonormalChartBounds.mjpb, hB, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hcol : ∀ b : Fin X.p0, y (Fin.castLE X.p0_le b) =
        ∑ a, A a b • col (mat (X.xZ x Z) τ) (Fin.castLE X.p0_le a) := fun b =>
      calc y (Fin.castLE X.p0_le b) = mat x τ *ᵥ c b := (hinv _).symm
        _ = mat x τ *ᵥ OrthonormalChartBounds.mjg X Z τ (fun a => A a b) := by rw [e2]
        _ = ∑ a, (fun a => A a b) a • X.colP (X.xZ x Z) τ a := (OrthonormalChartBounds.mj_sum_colP X x Z τ _).symm
        _ = _ := rfl
    exact (PositiveSpanMatrices.span_eq_of_mat _ _ A hAdet hcol).symm

end

end ReciprocityTheory.ChartRestriction.G.FD.SmallOperatorExistence
end
