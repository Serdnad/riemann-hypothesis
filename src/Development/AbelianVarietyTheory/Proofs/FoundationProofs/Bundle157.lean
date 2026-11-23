module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
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
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eis_norm_le (j : ℕ) (c : ℂ) (a b : ℤ → ℂ) (Ca Cb : ℝ) (ha : ∀ x, ‖a x‖ ≤ Ca)
    (hb : ∀ x, ‖b x‖ ≤ Cb) (n : ℕ) (hn : n ≠ 0) :
    ‖eis j c a b n‖ ≤ Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1) := by
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  simp only [eis, if_neg hn]
  refine (norm_sum_le _ _).trans ?_
  have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have key : ∀ p ∈ n.divisorsAntidiagonal,
      ‖a p.1 * (p.1 : ℂ) ^ (j - 1) * b p.2‖ ≤ Ca * Cb * (n : ℝ) ^ (j - 1) := by
    intro p hp
    have hle : p.1 ≤ n := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 : (p.1 : ℝ) ^ (j - 1) ≤ (n : ℝ) ^ (j - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) _
    calc ‖a p.1‖ * (p.1 : ℝ) ^ (j - 1) * ‖b p.2‖ ≤ Ca * (n : ℝ) ^ (j - 1) * Cb :=
          mul_le_mul (mul_le_mul (ha _) h1 (by positivity) hCa) (hb _) (norm_nonneg _) (by positivity)
      _ = Ca * Cb * (n : ℝ) ^ (j - 1) := by ring
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  ring

theorem eis_qseries : ∀ (j : ℕ) (c : ℂ) (a b : ℤ → ℂ), (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → PolyB (eis j c a b) ∧ (∃ C : ℝ, ∀ n, n ≠ 0 → ‖eis j c a b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (j - 1)) ∧ ∀ τ : ℍ, HasSum (fun y : ℕ => b (y + 1 : ℕ) * ∑' x : ℕ, ((x + 1 : ℕ) : ℂ) ^ (j - 1) * a (x + 1 : ℕ) * cexp (2 * π * Complex.I * (x + 1 : ℕ) * ((y + 1 : ℕ) * τ))) (qs (eis j c a b) τ - c) := by
  intro j c a b ⟨Ca, ha⟩ ⟨Cb, hb⟩
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  have hB := eis_norm_le j c a b Ca Cb ha hb
  refine ⟨?_, ⟨Ca * Cb, hB⟩, ?_⟩
  · refine ⟨max ‖c‖ (Ca * Cb), j + 1, fun n => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [eis]
    · refine (hB n hn).trans ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : (n.divisors.card : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.card_divisors_le_self n
        have : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast this
        linarith
      have h2 : (n : ℝ) ^ (j - 1) ≤ ((n : ℝ) + 1) ^ j :=
        (pow_le_pow_left₀ hn0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (Nat.sub_le j 1))
      have h3 : Ca * Cb ≤ max ‖c‖ (Ca * Cb) := le_max_right _ _
      have h4 : 0 ≤ Ca * Cb := mul_nonneg hCa hCb
      calc Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1)
          ≤ max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ j := by
            apply mul_le_mul (mul_le_mul h3 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)
        _ = max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) ^ (j + 1) := by ring
  · intro τ
    set q : ℂ := cexp (2 * π * Complex.I * τ) with hqdef
    have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
    have hE : ∀ m : ℕ, cexp (2 * π * Complex.I * m * τ) = q ^ m := fun m => by
      rw [hqdef, ← Complex.exp_nat_mul]; ring_nf
    have hE2 : ∀ m l : ℕ, cexp (2 * π * Complex.I * (m : ℂ) * ((l : ℂ) * τ)) = q ^ (m * l) := fun m l => by
      rw [hqdef, ← Complex.exp_nat_mul]; push_cast; ring_nf
    set H : ℕ+ × ℕ+ → ℂ := fun d => a ((d.1 : ℕ) : ℤ) * (((d.1 : ℕ) : ℂ)) ^ (j - 1) * b ((d.2 : ℕ) : ℤ) *
      q ^ ((d.1 : ℕ) * (d.2 : ℕ)) with hHdef
    have hHs : Summable H := by
      refine Summable.of_norm_bounded ((summable_prod_mul_pow (j - 1) hq).prod_symm.norm.mul_left (Ca * Cb)) fun d => ?_
      simp only [hHdef, norm_mul, norm_pow, Complex.norm_natCast, Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm ((d.2 : ℕ)) (d.1 : ℕ)]
      refine (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (ha _) (by positivity)) (hb _)
        (norm_nonneg _) (by positivity)) le_rfl (by positivity) (by positivity)).trans (le_of_eq ?_)
      ring
    have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hHs.hasSum
    have h3 : HasSum (fun n : ℕ+ => eis j c a b n * q ^ (n : ℕ)) (∑' d, H d) := by
      refine h2.sigma fun n => ?_
      refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
      simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
        Equiv.coe_fn_mk, Finset.univ_eq_attach, hHdef]
      rw [(n : ℕ).divisorsAntidiagonal.sum_attach (fun y : ℕ × ℕ => a (y.1 : ℤ) * ((y.1 : ℕ) : ℂ) ^ (j - 1) * b (y.2 : ℤ) * q ^ (y.1 * y.2))]
      simp only [eis, if_neg n.ne_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]
    have h4 : HasSum (fun n : ℕ => eis j c a b n * q ^ n) (c + ∑' d, H d) := by
      have h5 := (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => eis j c a b n * q ^ n)).1 h3
      have h6 := HasSum.zero_add (f := fun n : ℕ => eis j c a b n * q ^ n) h5
      have h7 : eis j c a b 0 * q ^ 0 = c := by simp [eis]
      rw [h7] at h6
      exact h6
    have hqs : qs (eis j c a b) τ = c + ∑' d, H d := by
      unfold qs
      rw [← h4.tsum_eq]
      exact tsum_congr fun n => by rw [hE]
    rw [hqs, add_sub_cancel_left]
    let e : ℕ × ℕ ≃ ℕ+ × ℕ+ := (Equiv.prodComm ℕ ℕ).trans (Equiv.pnatEquivNat.symm.prodCongr Equiv.pnatEquivNat.symm)
    set F : ℕ × ℕ → ℂ := fun p => b (p.1 + 1 : ℕ) * (((p.2 + 1 : ℕ) : ℂ) ^ (j - 1) * a (p.2 + 1 : ℕ) *
      cexp (2 * π * Complex.I * (p.2 + 1 : ℕ) * ((p.1 + 1 : ℕ) * τ))) with hFdef
    have hFe : F = H ∘ e := by
      funext p
      simp only [hFdef, hHdef, Function.comp, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
        Prod.snd_swap, Equiv.prodCongr_apply, Prod.map, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one]
      rw [hE2, mul_comm (p.2 + 1) (p.1 + 1)]
      ring
    have hFs : Summable F := by rw [hFe]; exact e.summable_iff.2 hHs
    have hF : HasSum F (∑' d, H d) := by rw [hFe]; exact e.hasSum_iff.2 hHs.hasSum
    refine hF.prod_fiberwise fun y => ?_
    rw [← tsum_mul_left]
    exact (hFs.prod_factor y).hasSum

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.CotQExp

theorem hasSum_pi_cot (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun m : ℕ => -2 * π * Complex.I * cexp (2 * π * Complex.I * w) ^ (m + 1))
      (π * Complex.cot (π * w) + π * Complex.I) := by
  have h : (π : ℂ) * Complex.cot (π * w) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ n :=
    pi_mul_cot_pi_q_exp (⟨w, hw⟩ : ℍ)
  have hq : ‖cexp (2 * π * Complex.I * w)‖ < 1 :=
    UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨w, hw⟩ : ℍ)
  have hs : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ n :=
    summable_geometric_of_norm_lt_one hq
  have hs1 : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have h2 := hs1.hasSum.mul_left (-2 * π * Complex.I)
  have e : (π : ℂ) * Complex.cot (π * w) + π * Complex.I =
      -2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ (n + 1) := by
    rw [h, hs.tsum_eq_zero_add]
    ring
  rw [e]
  exact h2

theorem sum_cot_eq_qexp : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 →
    ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      -2 * π * Complex.I / L *
        ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
  intro L φ z hL hz h0
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by
    simpa [hat] using h0
  have him : ∀ r : ℕ, 0 < ((z + r) / L : ℂ).im := by
    intro r
    rw [Complex.div_natCast_im]
    simpa using div_pos hz hLr
  have hs := hasSum_sum (s := Finset.range L)
    (fun r _ => (hasSum_pi_cot _ (him r)).mul_left (φ r / L))
  rw [← tsum_mul_left]
  have e1 : ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I) := by
    have : ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I)
        = ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L)))
          + (∑ r ∈ Finset.range L, φ r) * (π * Complex.I / L) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [this, hsum0, zero_mul, add_zero]
  rw [e1, ← hs.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [hat, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul, mul_assoc (φ r), ← Complex.exp_add]
  have e2 : ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * ((z + r) / L)) =
      2 * π * Complex.I * (r * (((m + 1 : ℕ) : ℤ) : ℂ)) / L
        + 2 * π * Complex.I * (m + 1 : ℕ) * z / L := by
    push_cast
    ring
  rw [e2]
  ring

end GlobalTheory.CotQExp
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma pow_succ_le_factorial_mul_choose (n A : ℕ) :
    ((n : ℝ) + 1) ^ A ≤ (A.factorial : ℝ) * ((n + A).choose A : ℕ) := by
  have h := Nat.pow_succ_le_ascFactorial (n + 1) A
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact_mod_cast h

lemma norm_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma one_sub_exp_inv_le (y : ℝ) (hy : 0 < y) :
    (1 - Real.exp (-2 * π * y))⁻¹ ≤ 1 + y⁻¹ := by
  set t := 2 * π * y with ht
  have htpos : 0 < t := by positivity
  have hty : y ≤ t := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith
  have h1 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
  have h2 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp; ring
    linarith
  have h3 : (1 - Real.exp (-t))⁻¹ ≤ (t / (1 + t))⁻¹ := inv_anti₀ (by positivity) h2
  have h4 : (t / (1 + t))⁻¹ = 1 + t⁻¹ := by field_simp; ring
  have h5 : t⁻¹ ≤ y⁻¹ := inv_anti₀ hy hty
  have : -2 * π * y = -t := by rw [ht]; ring
  rw [this]
  linarith

lemma one_add_inv_pow_le (y : ℝ) (hy : 0 < y) (B : ℕ) :
    (1 + y⁻¹) ^ B ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
  rcases le_or_gt 1 y with h | h
  · have : 1 + y⁻¹ ≤ 2 * y := by
      have : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * y ^ B := mul_pow _ _ _
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ (y ^ B)⁻¹ := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]
  · have : 1 + y⁻¹ ≤ 2 * y⁻¹ := by
      have : 1 ≤ y⁻¹ := one_le_inv₀ hy |>.mpr h.le
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y⁻¹) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * (y ^ B)⁻¹ := by rw [mul_pow, inv_pow]
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ y ^ B := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]

theorem mod_qs_of_polyB : ∀ a : ℕ → ℂ, PolyB a → Mod (qs a) := by
  intro a ⟨C, A, hC⟩
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * A.factorial * 2 ^ (A + 1), A + 1, fun τ => ?_⟩
  set y := τ.im
  have hy : 0 < y := τ.im_pos
  set r := Real.exp (-2 * π * y) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    have := Real.pi_pos
    calc r < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have hS := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) A hrn
  have hbound : ∀ n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by
    intro n
    rw [norm_mul, norm_qterm]
    have h1 := hC n
    have h2 := pow_succ_le_factorial_mul_choose n A
    calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ C * ((A.factorial : ℝ) * ((n + A).choose A : ℕ)) * r ^ n := by
          gcongr
      _ = (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by ring
  have hsum2 : HasSum (fun n : ℕ => (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n))
      ((C * A.factorial) * (1 / (1 - r) ^ (A + 1))) := hS.mul_left _
  have hsumm : Summable (fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum2.summable
  have key : ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := by
    unfold qs
    calc ‖∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)‖
        ≤ ∑' n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' n : ℕ, (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) :=
          hsumm.tsum_le_tsum hbound hsum2.summable
      _ = _ := hsum2.tsum_eq
  have hinv : 1 / (1 - r) ^ (A + 1) ≤ 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by
    rw [one_div, ← inv_pow]
    calc ((1 - r)⁻¹) ^ (A + 1) ≤ (1 + y⁻¹) ^ (A + 1) :=
          pow_le_pow_left₀ (by have : 0 < 1 - r := by linarith
                               positivity) (one_sub_exp_inv_le y hy) _
      _ ≤ _ := one_add_inv_pow_le y hy _
  calc ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := key
    _ ≤ (C * A.factorial) * (2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = C * A.factorial * 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by ring

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qExpansionFunction_coeffHeckeVOperator_eq_tsum (l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (τ : ℍ) :
    qs (Vo l a) τ = ∑' m : ℕ, a m * cexp (2 * π * Complex.I * m * ((l : ℂ) * τ)) := by
  unfold qs Vo
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun x y h => by
    simpa [hl.ne'] using h
  rw [← hinj.tsum_eq]
  · congr 1; ext m
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl]
    congr 2; push_cast; ring
  · intro n hn
    by_cases h : l ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · simp [Function.mem_support, h] at hn

theorem adjU_sum (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (hk : 1 ≤ k) (hl : 0 < l)
    (hf : MF k N (ch ε) h) (τ : ℍ) :
    ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  have hlC : (0 : ℝ) < l := by exact_mod_cast hl
  let τ' : ℍ := ⟨(l : ℂ) * τ, by simpa using mul_pos hlC τ.im_pos⟩
  have hτ' : (τ' : ℂ) = (l : ℂ) * τ := rfl
  have key : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ (k - 1) * qs h τ' := by
    intro j
    let γ : SL(2, ℤ) := ⟨!![1, 0; (N * (j : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
    have hγ := hf.2 γ (by simp [γ]) τ'
    have hpt : ((γ • τ' : ℍ) : ℂ) = ((l : ℂ) * τ) / (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [coe_specialLinearGroup_apply]; simp [γ, hτ']; ring
    have hden : ((((N * (j : ℕ) : ℤ)) : ℂ) * (τ' : ℂ) + 1) = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [hτ']; push_cast; ring
    have hne : (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      rcases this with h1 | h1
      · have h2 : N * l * (j : ℕ) = 0 := by rcases h1 with (h1 | h1) | h1 <;> simp [h1]
        simp [h2] at h0
      · exact (τ.im_pos.ne' h1)
    have hγ' : qs h (γ • τ') = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ^ k * qs h τ' := by
      rw [← hden, hγ]; simp [γ, ch]
    have harg : ((l : ℂ) * τ / ((N : ℂ) * l * ((j : ℕ) : ℂ) * τ + 1)) = ((γ • τ' : ℍ) : ℂ) := by
      rw [hpt]; push_cast; ring
    unfold slz repL
    simp [Matrix.det_fin_two]
    rw [harg, ofComplex_apply, hγ']
    push_cast at hne ⊢
    field_simp
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [qExpansionFunction_coeffHeckeVOperator_eq_tsum l hl h τ]
  have hp : (l : ℂ) * (l : ℂ) ^ (k - 1) = (l : ℂ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [← mul_assoc, hp]
  rfl
end GlobalTheory.EisM

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem map_mem_aug_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (A B : Set G) (z : G) (h : ∀ y ∈ B, z * y * z⁻¹ ∈ A) (u : V) (hu : u ∈ aug π B (fun _ => 1)) :
    π z u ∈ aug π A (fun _ => 1) := by
  have hle : aug π B (fun _ => 1) ≤ (aug π A (fun _ => 1)).comap (π z) := by
    unfold aug
    refine Submodule.span_le.2 ?_
    rintro x ⟨y, hy, w, rfl⟩
    refine Submodule.subset_span ⟨z * y * z⁻¹, h y hy, π z w, ?_⟩
    have e : π (z * y * z⁻¹) (π z w) = π z (π y w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [e, map_sub, map_smul]
  exact hle hu

theorem aug_mono_set {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    {A B : Set G} (θ : G → ℂ) (h : A ⊆ B) : aug π A θ ≤ aug π B θ := by
  unfold aug
  refine Submodule.span_mono ?_
  rintro x ⟨y, hy, w, rfl⟩
  exact ⟨y, h hy, w, rfl⟩

theorem eig_eq_zero_of_mem_aug_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ z hJ hN hmono h0 hconj h1 hz m
  induction m with
  | zero =>
    intro u hu heig
    refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 0) (fun _ => 1) (hN 0)).1 u hu ?_
    intro y hy
    rw [heig y (h0 y hy).1, (h0 y hy).2]
  | succ m ih =>
    intro u hu heig
    obtain ⟨u', hu'eig, hsub⟩ := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 1) (fun _ => 1) (hN 1)).2 u
    have hsub' : u - u' ∈ aug π (N (m + 1)) (fun _ => 1) :=
      aug_mono_set π _ (hmono (Nat.succ_le_succ (Nat.zero_le m))) hsub
    have hu' : u' ∈ aug π (N (m + 1)) (fun _ => 1) := by
      have := Submodule.sub_mem _ hu hsub'
      simpa using this
    have hzu : π z u' ∈ aug π (N m) (fun _ => 1) :=
      map_mem_aug_of_conj π (N m) (N (m + 1)) z (fun y hy => (hconj m y).1 hy) u' hu'
    have hzeig : IsEig π J θ (π z u') :=
      GlobalTheory.T.isEig_apply_of_sub_mem_aug G V π hπ J (N 0) (N 1) θ z hJ (hN 0) h0 (hconj 0) hz u u' heig hu'eig hsub
    have hz0 : π z u' = 0 := ih _ hzu hzeig
    have hu0 : u' = 0 := by
      have e : π z⁻¹ (π z u') = u' := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      rw [← e, hz0, map_zero]
    rw [hu0, sub_zero] at hsub
    exact GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine G V π hπ J (N 1) θ hJ (hN 1) h1 u hsub heig

end GlobalTheory.PsType
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.isLogDerivQExpansion_finset_prod_zpow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (ι : Type) (I : Finset ι) (f : ι → X.K) (φ : ι → HahnSeries ℚ Ω) (m : ι → ℤ), (∀ i ∈ I, IsDl X A l n s (f i) (φ i)) → IsDl X A l n s (∏ i ∈ I, f i ^ m i) (∑ i ∈ I, m i • φ i) := by
  first | exact @GlobalTheory.isDl_finset_prod_zpow | exact GlobalTheory.isDl_finset_prod_zpow | (intros; apply GlobalTheory.isDl_finset_prod_zpow <;> assumption)
end
