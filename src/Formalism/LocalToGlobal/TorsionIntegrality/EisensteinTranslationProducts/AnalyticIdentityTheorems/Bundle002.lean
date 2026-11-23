module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.Connected
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

section

noncomputable section
open scoped Topology

namespace Formalism.L2.Th1.F

namespace PDeriv

lemma hasDerivAt_P (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd := (L.differentiableOn_weierstrassP.differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  rwa [L.deriv_weierstrassP] at hd

lemma eventually_notMem (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz

lemma notMem_of_rat (L : PeriodPair) (α β : ℚ) {x : ℂ} (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬ (α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by
  intro hmem
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hmem
  rw [hx] at hmn
  have key := (LinearIndependent.pair_iff.mp L.indep) ((α : ℝ) - m) ((β : ℝ) - n) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination -hmn)
  have ha : α = m := by exact_mod_cast sub_eq_zero.mp key.1
  have hb : β = n := by exact_mod_cast sub_eq_zero.mp key.2
  exact h ⟨by rw [ha]; simp, by rw [hb]; simp⟩

lemma disc_alg (g2 g3 e1 e2 e3 : ℂ) (h1 : 4 * e1 ^ 3 - g2 * e1 - g3 = 0)
    (h2 : 4 * e2 ^ 3 - g2 * e2 - g3 = 0) (h3 : 4 * e3 ^ 3 - g2 * e3 - g3 = 0)
    (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3) : g2 ^ 3 - 27 * g3 ^ 2 ≠ 0 := by
  have hA : g2 = 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) := by
    have h0 : (e1 - e2) * (4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) - g2) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h12
    · linear_combination -h
  have hB : g2 = 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) := by
    have h0 : (e1 - e3) * (4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) - g2) = 0 := by
      linear_combination h1 - h3
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h13
    · linear_combination -h
  have hS : e1 + e2 + e3 = 0 := by
    have h0 : (e2 - e3) * (e1 + e2 + e3) = 0 := by linear_combination (hB - hA) / 4
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h23
    · exact h
  have hD : g2 ^ 3 - 27 * g3 ^ 2 = 16 * ((e1 - e2) * (e1 - e3) * (e2 - e3)) ^ 2 := by
    have h3' : e3 = -e1 - e2 := by linear_combination hS
    have hg3 : g3 = 4 * e1 ^ 3 - g2 * e1 := by linear_combination -h1
    rw [hg3, hA, h3']
    ring
  rw [hD]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h23)))

end PDeriv

open PDeriv

theorem sigmaDouble_of (h : SigmaAdd) (he : SigmaEntire) (hs : SigmaSimple) : SigmaDouble := by
  intro L z hz
  have h0 : wSigma L 0 = 0 := by simp only [wSigma, zero_mul]
  have hd : ∀ x, HasDerivAt (wSigma L) (deriv (wSigma L) x) x := fun x => (he L x).hasDerivAt
  have hF := (HasDerivAt.comp z (hd (z + z)) ((hasDerivAt_id' z).const_add z)).mul
    (HasDerivAt.comp z (hd (z - z)) ((hasDerivAt_id' z).const_sub z))
  have hG := ((((hd z).mul (hd z)).const_mul (wSigma L z ^ 2)).mul
    ((hasDerivAt_P L hz).const_sub (L.weierstrassP z))).neg
  have hG' : HasDerivAt (fun w => wSigma L (z + w) * wSigma L (z - w)) _ z :=
    hG.congr_of_eventuallyEq ((eventually_notMem L hz).mono fun w hw => by
      simp only [Pi.neg_apply, Pi.mul_apply]
      rw [h L z w hz hw]
      ring)
  have key := hF.unique hG'
  simp only [Function.comp_apply, Pi.mul_apply, sub_self, h0, (hs L).1] at key
  rw [two_mul]
  linear_combination -key

theorem pDerivZero_of (h : SigmaDouble) (hz : SigmaZero) : PDerivZero := by
  intro L z hz'
  have hσ : wSigma L z ≠ 0 := fun h0 => hz' ((hz L z).mp h0)
  rw [← hz L (2 * z), h L z hz']
  simp [hσ]

theorem discNeZero_of (hp : PDerivZero) (hi : PInjective) : DiscNeZero := by
  intro L
  have root : ∀ x, x ∉ L.lattice → 2 * x ∈ L.lattice →
      4 * L.weierstrassP x ^ 3 - L.g₂ * L.weierstrassP x - L.g₃ = 0 := by
    intro x hx h2
    have hsq := L.derivWeierstrassP_sq x hx
    rw [(hp L x hx).mpr h2] at hsq
    linear_combination -hsq
  have ne : ∀ x y, x ∉ L.lattice → y ∉ L.lattice → x - y ∉ L.lattice → x + y ∉ L.lattice →
      L.weierstrassP x ≠ L.weierstrassP y := fun x y hx hy h1 h2 he =>
    ((hi L x y hx hy).mp he).elim h1 h2
  have hw1 : L.ω₁ ∈ L.lattice := L.ω₁_mem_lattice
  have hw2 : L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨0, 1, by push_cast; ring⟩
  have n1 : L.ω₁ / 2 ∉ L.lattice :=
    notMem_of_rat L 2⁻¹ 0 (by push_cast; ring) (by first | decide | norm_num | simp)
  have n2 : L.ω₂ / 2 ∉ L.lattice :=
    notMem_of_rat L 0 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)
  have n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice :=
    notMem_of_rat L 2⁻¹ 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)
  have d1 : 2 * (L.ω₁ / 2) ∈ L.lattice := by
    rw [show 2 * (L.ω₁ / 2) = L.ω₁ by ring]
    exact hw1
  have d2 : 2 * (L.ω₂ / 2) ∈ L.lattice := by
    rw [show 2 * (L.ω₂ / 2) = L.ω₂ by ring]
    exact hw2
  have d3 : 2 * ((L.ω₁ + L.ω₂) / 2) ∈ L.lattice := by
    rw [show 2 * ((L.ω₁ + L.ω₂) / 2) = L.ω₁ + L.ω₂ by ring]
    exact add_mem hw1 hw2
  exact disc_alg _ _ _ _ _ (root _ n1 d1) (root _ n2 d2) (root _ n3 d3)
    (ne _ _ n1 n2 (notMem_of_rat L 2⁻¹ (-2⁻¹) (by push_cast; ring) (by first | decide | norm_num | simp))
      (notMem_of_rat L 2⁻¹ 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)))
    (ne _ _ n1 n3 (notMem_of_rat L 0 (-2⁻¹) (by push_cast; ring) (by first | decide | norm_num | simp))
      (notMem_of_rat L 1 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)))
    (ne _ _ n2 n3 (notMem_of_rat L (-2⁻¹) 0 (by push_cast; ring) (by first | decide | norm_num | simp))
      (notMem_of_rat L 2⁻¹ 1 (by push_cast; ring) (by first | decide | norm_num | simp)))

theorem zetaAdd_of (h : SigmaAdd) (hl : SigmaLogDeriv) (hz : SigmaZero) : ZetaAdd := by
  intro L a b ha hb hab hamb
  have hσ : ∀ x, x ∉ L.lattice → wSigma L x ≠ 0 := fun x hx h0 => hx ((hz L x).mp h0)
  have hadd := h L a b ha hb
  have hK : wSigma L a ^ 2 * wSigma L b ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (hσ a ha)) (pow_ne_zero _ (hσ b hb))
  have hD : L.weierstrassP a - L.weierstrassP b ≠ 0 := by
    intro h0
    rw [h0, mul_zero, neg_zero] at hadd
    exact mul_ne_zero (hσ _ hab) (hσ _ hamb) hadd

  have hF1 := (HasDerivAt.comp a (hl L (a + b) hab) ((hasDerivAt_id' a).add_const b)).mul
    (HasDerivAt.comp a (hl L (a - b) hamb) ((hasDerivAt_id' a).sub_const b))
  have hG1 := ((((hl L a ha).mul (hl L a ha)).mul_const (wSigma L b ^ 2)).mul
    ((hasDerivAt_P L ha).sub_const (L.weierstrassP b))).neg
  have hG1' : HasDerivAt (fun x => wSigma L (x + b) * wSigma L (x - b)) _ a :=
    hG1.congr_of_eventuallyEq ((eventually_notMem L ha).mono fun x hx => by
      simp only [Pi.neg_apply, Pi.mul_apply]
      rw [h L x b hx hb]
      ring)
  have k1 := hF1.unique hG1'
  simp only [Function.comp_apply, Pi.mul_apply] at k1

  have hF2 := (HasDerivAt.comp b (hl L (a + b) hab) ((hasDerivAt_id' b).const_add a)).mul
    (HasDerivAt.comp b (hl L (a - b) hamb) ((hasDerivAt_id' b).const_sub a))
  have hG2 := ((((hl L b hb).mul (hl L b hb)).const_mul (wSigma L a ^ 2)).mul
    ((hasDerivAt_P L hb).const_sub (L.weierstrassP a))).neg
  have hG2' : HasDerivAt (fun y => wSigma L (a + y) * wSigma L (a - y)) _ b :=
    hG2.congr_of_eventuallyEq ((eventually_notMem L hb).mono fun y hy => by
      simp only [Pi.neg_apply, Pi.mul_apply]
      rw [h L a y ha hy]
      ring)
  have k2 := hF2.unique hG2'
  simp only [Function.comp_apply, Pi.mul_apply] at k2
  have e1 : (wSigma L a ^ 2 * wSigma L b ^ 2) *
      ((L.weierstrassP a - L.weierstrassP b) * (wZeta L (a + b) + wZeta L (a - b))
        - 2 * wZeta L a * (L.weierstrassP a - L.weierstrassP b) - L.derivWeierstrassP a) = 0 := by
    linear_combination (wZeta L (a + b) + wZeta L (a - b)) * hadd - k1
  have e2 : (wSigma L a ^ 2 * wSigma L b ^ 2) *
      ((L.weierstrassP a - L.weierstrassP b) * (wZeta L (a + b) - wZeta L (a - b))
        - 2 * wZeta L b * (L.weierstrassP a - L.weierstrassP b) + L.derivWeierstrassP b) = 0 := by
    linear_combination (wZeta L (a + b) - wZeta L (a - b)) * hadd - k2
  have f1 := (mul_eq_zero.mp e1).resolve_left hK
  have f2 := (mul_eq_zero.mp e2).resolve_left hK
  have hq : wZeta L (a + b) - (wZeta L a + wZeta L b)
      = (L.derivWeierstrassP a - L.derivWeierstrassP b) /
        (2 * (L.weierstrassP a - L.weierstrassP b)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hD)]
    linear_combination f1 + f2
  linear_combination hq

end Formalism.L2.Th1.F
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace ThetaZeroHermitianLemmas

lemma herm_add_left (L : PeriodPair) (x y w : ℂ) : herm L (x + y) w = herm L x w + herm L y w := by
  simp only [herm]; ring

lemma herm_add_right (L : PeriodPair) (x y w : ℂ) : herm L w (x + y) = herm L w x + herm L w y := by
  simp only [herm, map_add (f := _)]; ring

lemma herm_zero_left (L : PeriodPair) (w : ℂ) : herm L 0 w = 0 := by
  simp [herm]

lemma herm_conj (L : PeriodPair) (x y : ℂ) : herm L x y = conj (herm L y x) := by
  simp only [herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]; ring

lemma herm_sub_swap (L : PeriodPair) (x y : ℂ) :
    herm L x y - herm L y x = -(2 * Complex.I * (altE L y x : ℂ)) := by
  rw [herm_conj L x y]
  apply Complex.ext <;> simp [altE]
  all_goals ring

lemma thetaZero_periodLattice_eq (L : PeriodPair) (t z : ℂ) :
    th0 L t z = sgStar L (z + t) * Complex.exp (-(Real.pi : ℂ) * herm L z t) / sgStar L t := by
  have h1 : Complex.exp (-(Real.pi : ℂ) * herm L z t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-(Real.pi : ℂ) * herm L z t) * Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [← Complex.exp_add]; congr 1
  have h2 : Complex.exp (-(Real.pi : ℂ) * herm L 0 t - (Real.pi : ℂ) * herm L t t / 2)
      = Complex.exp (-((Real.pi : ℂ) * herm L t t / 2)) := by
    rw [herm_zero_left]; congr 1; ring
  simp only [th0, opU, zero_add, h1, h2]
  rw [← mul_assoc, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]

lemma exp_pi_int (k : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (k : ℂ))) = Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) := by
  have h : Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_int_mul_two_pi_mul_I k using 2
    ring
  rw [Complex.exp_neg]
  exact inv_eq_of_mul_eq_one_right h

end ThetaZeroHermitianLemmas

open ThetaZeroHermitianLemmas

theorem th0Const_of (hb : SgStarBasic) : ThetaZeroConstant := by
  intro L t
  have h : opU L t (sgStar L) 0 = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2) := by
    simp only [opU, zero_add, herm_zero_left]; congr 2; ring
  refine ⟨h, fun ht => ?_⟩
  rw [h]
  exact mul_ne_zero (fun h0 => ht (((hb L).2.2.1 t).1 h0)) (Complex.exp_ne_zero _)

theorem th0Class_of (hb : SgStarBasic) (hq : SgStarQuasi) : ThetaZeroClass := by
  intro L t ω z hω ht
  have hs : sgStar L t ≠ 0 := fun h0 => ht (((hb L).2.2.1 t).1 h0)
  have hc : semiChar L ω ≠ 0 := by unfold semiChar; split_ifs <;> norm_num
  have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * herm L z (t + ω))
      = Complex.exp (-(Real.pi : ℂ) * herm L z t)
        * Complex.exp ((Real.pi : ℂ) * herm L t ω + (Real.pi : ℂ) * herm L ω ω / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    rw [herm_add_left, herm_add_right]; ring
  rw [thetaZero_periodLattice_eq L (t + ω) z, thetaZero_periodLattice_eq L t z, ← add_assoc, hq L ω (z + t) hω, hq L ω t hω,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) hs) hs]
  linear_combination (semiChar L ω * sgStar L (z + t) * sgStar L t) * key

theorem th0Basic_of (hb : SgStarBasic) (hq : SgStarQuasi) (hi : AltEInt) : ThetaZeroBasic := by
  intro L ω₀ hω hn
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn ⊢
  have hs : sgStar L t ≠ 0 := fun h0 => hn (((hb L).2.2.1 t).1 h0)
  have hχ : semiChar L (t + t) = -1 := by
    rw [semiChar, if_neg (by rw [h2]; exact hn)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hd := (hb L).1
    show Differentiable ℂ (fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0)
    simp only [opU, herm]
    fun_prop
  · simp only [th0]
    exact div_self ((th0Const_of hb L t).2 hn)
  · intro z
    rw [thetaZero_periodLattice_eq L t (-z), thetaZero_periodLattice_eq L t z]
    have h1 : sgStar L (-z + t) = -sgStar L (z - t) := by
      rw [show -z + t = -(z - t) by ring]; exact (hb L).2.1 _
    have h3 := hq L (t + t) (z - t) hω
    rw [show z - t + (t + t) = z + t by ring, hχ] at h3
    have key : Complex.exp (-(Real.pi : ℂ) * herm L (-z) t)
        = Complex.exp ((Real.pi : ℂ) * herm L (z - t) (t + t) + (Real.pi : ℂ) * herm L (t + t) (t + t) / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [← Complex.exp_add]; congr 1
      simp only [herm, map_add (f := _), map_neg, map_sub]; ring
    rw [h1, h3]
    linear_combination (-sgStar L (z - t) / sgStar L t) * key
  · intro z
    rw [thetaZero_periodLattice_eq, div_eq_zero_iff, mul_eq_zero, (hb L).2.2.1]
    simp [Complex.exp_ne_zero, hs]
  · intro ω hω' z
    obtain ⟨k, hk⟩ := hi L ω (t + t) hω' hω
    have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
        = Complex.exp (-((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))) := by
      rw [hk]; push_cast; exact (exp_pi_int k).symm
    have hsw := herm_sub_swap L (t + t) ω
    have key : Complex.exp ((Real.pi : ℂ) * herm L (z + t) ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L (z + ω) t)
        = Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω (t + t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2)
          * Complex.exp (-(Real.pi : ℂ) * herm L z t) := by
      rw [he]; simp only [← Complex.exp_add]; congr 1
      simp only [herm, map_add (f := _)] at hsw ⊢
      linear_combination ((Real.pi : ℂ) / 2) * hsw
    rw [thetaZero_periodLattice_eq L t (z + ω), thetaZero_periodLattice_eq L t z, show z + ω + t = (z + t) + ω by ring, hq L ω (z + t) hω']
    linear_combination (semiChar L ω * sgStar L (z + t) / sgStar L t) * key

theorem th0LogDeriv_of (hl : SigmaLogDeriv) (he : EtaSplit) (hzq : ZetaQuasi)
    (hzo : ZetaOdd) : ThetaZeroLogDerivative := by
  intro L ω₀ z hω hn hzt
  obtain ⟨t, rfl⟩ : ∃ t, ω₀ = t + t := ⟨ω₀ / 2, by ring⟩
  have h2 : (t + t) / 2 = t := by ring
  rw [h2] at hn hzt ⊢
  have hζ : wZeta L t = s2 L * t + ((Real.pi : ℂ) / (area L : ℂ)) * conj t := by
    have h1 := hzq L (t + t) (-t) hω (by rwa [neg_mem_iff])
    rw [show -t + (t + t) = t by ring, hzo, he] at h1
    simp only [map_add (f := _)] at h1
    linear_combination h1 / 2
  have hd1 : HasDerivAt (fun w => wSigma L (w + t)) (wZeta L (z + t) * wSigma L (z + t)) z := by
    have := (hl L (z + t) hzt).comp z ((hasDerivAt_id' z).add_const t)
    rw [mul_one] at this
    exact this
  have hg : HasDerivAt (fun w : ℂ => -(s2 L) * (w + t) ^ 2 / 2
        + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2))
      (-(s2 L) * (z + t) - (Real.pi : ℂ) * (conj t / (area L : ℂ))) z := by
    have e1 := ((((hasDerivAt_id' z).add_const t).mul ((hasDerivAt_id' z).add_const t)).const_mul
      (-(s2 L))).div_const 2
    have e2 := (((hasDerivAt_id' z).mul_const (conj t / (area L : ℂ))).const_mul
      (-(Real.pi : ℂ))).sub_const ((Real.pi : ℂ) * herm L t t / 2)
    refine ((e1.add e2).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, herm]; ring
  have hfull := (hd1.mul hg.cexp).div_const (opU L t (sgStar L) 0)
  have hfun : th0 L t = fun w => wSigma L (w + t) * Complex.exp (-(s2 L) * (w + t) ^ 2 / 2
      + (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) / opU L t (sgStar L) 0 := by
    funext w
    simp only [th0]
    congr 1
    simp only [opU, sgStar]
    rw [Complex.exp_add]; ring
  rw [hfun]
  refine hfull.congr_deriv ?_
  beta_reduce
  rw [hζ]; ring

end Formalism.L2.Th1.F
end
end

section

noncomputable section

namespace Formalism.L2.Th1.F

namespace WeierstrassZetaQuasiPeriod

lemma isOpen_compl (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) :=
  L.isClosed_lattice.isOpen_compl

lemma isPreconnected_compl (L : PeriodPair) : IsPreconnected ((L.lattice : Set ℂ)ᶜ) :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (countable_of_Lindelof_of_discrete (X := L.lattice))).2

lemma add_notMem {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := fun h => hz (by simpa using sub_mem h hω)

lemma diff_const (hd : ZetaHasDeriv) (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) {x y : ℂ}
    (hx : x ∉ L.lattice) (hy : y ∉ L.lattice) :
    wZeta L (x + ω) - wZeta L x = wZeta L (y + ω) - wZeta L y := by
  have hD : ∀ z, z ∉ L.lattice → HasDerivAt (fun z => wZeta L (z + ω) - wZeta L z) 0 z := by
    intro z hz
    have h1 := (hd L (z + ω) (add_notMem hω hz)).comp_add_const z ω
    have h2 := h1.sub (hd L z hz)
    have h3 : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    have e : -L.weierstrassP (z + ω) - -L.weierstrassP z = 0 := by rw [h3]; ring
    rw [e] at h2
    exact h2
  exact (isOpen_compl L).is_const_of_deriv_eq_zero (f := fun z => wZeta L (z + ω) - wZeta L z)
    (isPreconnected_compl L)
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv) hx hy

lemma diff_eq (hd : ZetaHasDeriv) (ho : ZetaOdd) (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice)
    (hω2 : ω / 2 ∉ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    wZeta L (z + ω) = wZeta L z + 2 * wZeta L (ω / 2) := by
  have hm : -(ω / 2) ∉ L.lattice := fun h => hω2 (by simpa using neg_mem h)
  have h := diff_const hd L hω hz hm
  have e : -(ω / 2) + ω = ω / 2 := by ring
  rw [e, ho L (ω / 2)] at h
  linear_combination h

lemma wEta_ω₁ (L : PeriodPair) : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
  simpa [wEta] using this

lemma wEta_ω₂ (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
  have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  simpa [wEta] using this

end WeierstrassZetaQuasiPeriod


open WeierstrassZetaQuasiPeriod in
theorem zetaQuasi_of (hd : ZetaHasDeriv) (ho : ZetaOdd) : ZetaQuasi := by
  intro L ω z hω hz
  let G : AddSubgroup ℂ :=
    { carrier := { w | w ∈ L.lattice ∧
        ∀ x, x ∉ L.lattice → wZeta L (x + w) = wZeta L x + wEta L w }
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun x hx => ?_⟩
        calc
          wZeta L (x + (a + b)) = wZeta L (x + a + b) := by congr 1; abel
          _ = wZeta L (x + a) + wEta L b :=
            hb' (x + a) (WeierstrassZetaQuasiPeriod.add_notMem ha hx)
          _ = (wZeta L x + wEta L a) + wEta L b := by rw [ha' x hx]
          _ = wZeta L x + wEta L (a + b) := by rw [map_add]; abel
      zero_mem' := ⟨zero_mem _, fun x _ => by simp⟩
      neg_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨neg_mem ha, fun x hx => ?_⟩
        have h := ha' (x + -a) (WeierstrassZetaQuasiPeriod.add_notMem (neg_mem ha) hx)
        rw [neg_add_cancel_right] at h
        rw [map_neg, h]; ring }
  have hG : L.lattice ≤ G.toIntSubmodule := by
    rw [PeriodPair.lattice, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ⟨L.ω₁_mem_lattice, fun x hx => by
        rw [WeierstrassZetaQuasiPeriod.wEta_ω₁]; exact WeierstrassZetaQuasiPeriod.diff_eq hd ho L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice hx⟩
    · exact ⟨L.ω₂_mem_lattice, fun x hx => by
        rw [WeierstrassZetaQuasiPeriod.wEta_ω₂]; exact WeierstrassZetaQuasiPeriod.diff_eq hd ho L L.ω₂_mem_lattice L.ω₂_div_two_notMem_lattice hx⟩
  exact (hG hω).2 z hz

end Formalism.L2.Th1.F
end
end
