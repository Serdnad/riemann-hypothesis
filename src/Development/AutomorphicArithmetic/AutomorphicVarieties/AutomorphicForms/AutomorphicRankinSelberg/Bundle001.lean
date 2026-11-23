module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private theorem half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private theorem norm_G_cls_mul_ker_le_of_mem_fd {L : ℕ} (G : (Fin 2 → ZMod L) → ℍ → ℂ) (C s : ℝ)
    (hC : ∀ (v : Fin 2 → ZMod L) (z : ℍ), 1 / 2 ≤ z.im → ‖G v z‖ * z.im ^ 3 ≤ C)
    (hk : ∀ (x : Fin 2 → ℤ), ∀ z ∈ ModularGroup.fd, ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)))
    (h0 : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ ker s x z) (x : Fin 2 → ℤ) (z : ℍ)
    (hz : z ∈ ModularGroup.fd) :
    ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) := by
  have him := half_le_im hz
  have hw : 0 ≤ ‖x‖ ^ (-(2 * s)) := Real.rpow_nonneg (norm_nonneg _) _
  have hG := hC (cls L x) z him
  have hn : 0 ≤ ‖G (cls L x) z‖ := norm_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x z)]
  have h2 : ‖G (cls L x) z‖ * z.im ^ 2 ≤ 2 * C := by
    nlinarith [mul_nonneg (mul_nonneg hn (sq_nonneg z.im)) (sub_nonneg.2 him)]
  calc ‖G (cls L x) z‖ * ker s x z
      ≤ ‖G (cls L x) z‖ * (4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s))) :=
        mul_le_mul_of_nonneg_left (hk x z hz) hn
    _ = 4 * (‖G (cls L x) z‖ * z.im ^ 2) * ‖x‖ ^ (-(2 * s)) := by ring
    _ ≤ 4 * (2 * C) * ‖x‖ ^ (-(2 * s)) := by gcongr
    _ = 8 * C * ‖x‖ ^ (-(2 * s)) := by ring

private theorem sum_cls (L : ℕ) [NeZero L] (g : (Fin 2 → ZMod L) → ℂ) (s : ℝ) (z : ℍ)
    (hs : Summable fun x => ker s x z) :
    ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ) = ∑ v, g v * (Zc L v s z : ℂ) := by
  have hc : ∀ v, Summable fun x : Fin 2 → ℤ => if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
    intro v
    have := ((Complex.ofRealCLM.summable hs).mul_left (g v)).indicator {x | cls L x = v}
    refine this.congr (fun x => ?_)
    simp [Set.indicator_apply]
  calc ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ)
      = ∑' x : Fin 2 → ℤ, ∑ v, if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
        refine tsum_congr (fun x => ?_)
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ v, ∑' x : Fin 2 → ℤ, if cls L x = v then g v * (ker s x z : ℂ) else 0 :=
        Summable.tsum_finsetSum (fun v _ => hc v)
    _ = ∑ v, g v * (Zc L v s z : ℂ) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Zc, Complex.ofReal_tsum, ← tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        split_ifs <;> simp

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.swap :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.Swap := by
  intro hfd hkb hw L _ G hG s hs
  obtain ⟨hGc, C, hC⟩ := hG
  have hs' : s ∈ Icc (1:ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, -, -, -, hkb'⟩ := hkb s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hw.1 (2 * s) (by linarith [hs.1])
  have hbd : ∀ x : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
      ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) :=
    fun x z hz => norm_G_cls_mul_ker_le_of_mem_fd G C s hC hkb' hk0 x z hz
  have hint : ∀ x : Fin 2 → ℤ,
      IntegrableOn (fun z => G (cls L x) z * (ker s x z : ℂ)) ModularGroup.fd volume := by
    intro x
    exact Measure.integrableOn_of_bounded hfd.2.ne
      ((hGc _).mul (Complex.continuous_ofReal.comp (hkc x))).aestronglyMeasurable
      ((ae_restrict_iff' hfd.1).2 (Filter.Eventually.of_forall (hbd x)))
  refine ⟨hint, ?_⟩
  have hnorm : Summable fun x : Fin 2 → ℤ =>
      ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun x => integral_nonneg (fun _ => norm_nonneg _))
      (fun x => ?_) ((hsum.mul_left (8 * C)).mul_right (volume.real ModularGroup.fd))
    calc ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖
        ≤ ∫ z in ModularGroup.fd, 8 * C * ‖x‖ ^ (-(2 * s)) :=
          setIntegral_mono_on (hint x).norm (integrableOn_const hfd.2.ne) hfd.1 (hbd x)
      _ = 8 * C * ‖x‖ ^ (-(2 * s)) * volume.real ModularGroup.fd := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
  have h := hasSum_integral_of_summable_integral_norm hint hnorm
  have e : TT L G s = ∫ z in ModularGroup.fd, ∑' x : Fin 2 → ℤ, G (cls L x) z * (ker s x z : ℂ) := by
    unfold TT
    refine setIntegral_congr_fun hfd.1 (fun z hz => ?_)
    have hsz : Summable fun x : Fin 2 → ℤ => ker s x z :=
      Summable.of_nonneg_of_le (fun x => hk0 x z) (fun x => hkb' x z hz) (hsum.mul_left _)
    exact (sum_cls L (fun v => G v z) s z hsz).symm
  rw [e]
  exact h
end

section

open UpperTheory.V.Af.Rs in
private theorem arFact_agree (e e' a b : ℕ → ℂ) (ha : Rec e a) (hb : Rec e' b)
    (hp : ∀ p : ℕ, p.Prime → b p = a p) :
    ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → e p = e' p) → b n = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hdiv
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    rw [ha.1, hb.1]
  · obtain ⟨p, hpp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨n', rfl⟩ := hpn
    have hn' : 1 ≤ n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hlt : n' < p * n' := by have := hpp.two_le; nlinarith
    have hep : e p = e' p := hdiv p hpp (dvd_mul_right p n')
    have hsub : ∀ q : ℕ, q.Prime → q ∣ n' → e q = e' q :=
      fun q hq hqd => hdiv q hq (dvd_mul_of_dvd_right hqd p)
    have h1 := ha.2 p hpp n' hn'
    have h2 := hb.2 p hpp n' hn'
    have hb' := ih n' hlt hn' hsub
    by_cases hpd : p ∣ n'
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have hlt' : t < p * t := by have := hpp.two_le; nlinarith
      have hbt := ih t (by nlinarith) ht
        (fun q hq hqd => hsub q hq (dvd_mul_of_dvd_right hqd p))
      rw [if_pos (dvd_mul_right p t), hdt] at h1 h2
      rw [hbt, hb', hp p hpp, ← hep] at h2
      linear_combination h2 - h1
    · rw [if_neg hpd, mul_zero, add_zero] at h1 h2
      rw [hb', hp p hpp] at h2
      rw [h2, h1]

theorem UpperTheory.V.Af.Rs.arFact :
    UpperTheory.V.Af.Rs.ArFact := by
  intro r e e' a b ha hb hp hbad hbd
  refine ⟨{n | b n = a n}, fun n hn => hn, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn han
  by_cases hgood : ∀ p : ℕ, p.Prime → p ∣ n → e p = e' p
  · have hag := arFact_agree e e' a b ha hb hp n hn hgood
    exact ⟨n, hag, 1, by ring, by simp, by simp [hag]⟩
  · push_neg at hgood
    obtain ⟨p, hpp, hpn, hne⟩ := hgood
    have hap : a p = 0 := hbad p hpp hne
    have hbp : b p = 0 := by rw [hp p hpp, hap]
    obtain ⟨n'', rfl⟩ := hpn
    have hn'' : 1 ≤ n'' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have h1 := ha.2 p hpp n'' hn''
    by_cases hpd : p ∣ n''
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn'')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have h2 := hb.2 p hpp (p * t) hn''
      rw [if_pos (dvd_mul_right p t), hdt, hap, zero_mul] at h1
      rw [if_pos (dvd_mul_right p t), hdt, hbp, zero_mul] at h2
      have hA : a (p * (p * t)) = -(e p * a t) := by linear_combination h1
      have hB : b (p * (p * t)) = -(e' p * b t) := by linear_combination h2
      have hat : a t ≠ 0 := by
        intro h0
        apply han
        rw [hA, h0, mul_zero, neg_zero]
      have hlt : t < p * (p * t) := by have := hpp.two_le; nlinarith
      obtain ⟨n₁, hn₁, m, hnm, hA1, hB1⟩ := ih t hlt ht hat
      refine ⟨n₁, hn₁, p * m, by rw [hnm]; ring, ?_, ?_⟩
      · rw [hA, norm_neg, norm_mul]
        calc ‖e p‖ * ‖a t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).1 hA1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
      · rw [hB, norm_neg, norm_mul]
        calc ‖e' p‖ * ‖b t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).2 hB1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
    · exfalso
      apply han
      rw [if_neg hpd, mul_zero, add_zero, hap, zero_mul] at h1
      exact h1
end

section

open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped ENNReal

private lemma fd_meas : MeasurableSet ModularGroup.fd := by
  apply IsClosed.measurableSet
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const
  exact h1.inter h2

private lemma tail_fin :
    ∫⁻ y in Ioi (1 / 2 : ℝ), ENNReal.ofReal (1 / y ^ 2) < ∞ := by
  have h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi (1 / 2 : ℝ)) := by
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two, one_div]
  exact h'.lintegral_lt_top

theorem UpperTheory.V.Af.Rs.fdFin :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdFin := by
  rintro - ⟨hm, hv⟩
  refine ⟨fd_meas, ?_⟩
  rw [hv, Measure.map_apply hm fd_meas]
  have hsub : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' ModularGroup.fd ⊆
      (Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Ioi (1 / 2 : ℝ)) ∪ ((univ : Set ℝ) ×ˢ Iic (0 : ℝ)) := by
    rintro ⟨x, y⟩ hp
    rcases le_or_gt y 0 with hy | hy
    · exact Or.inr ⟨mem_univ _, hy⟩
    · left
      have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
      have hp' : UpperTheory.V.Af.Rs.pt x y ∈ ModularGroup.fd := hp
      have e : UpperTheory.V.Af.Rs.pt x y = ⟨_, him⟩ := ofComplex_apply_of_im_pos him
      have hre : (UpperTheory.V.Af.Rs.pt x y).re = x := by rw [e]; simp [UpperHalfPlane.re]
      have hi : (UpperTheory.V.Af.Rs.pt x y).im = y := by rw [e]; simp [UpperHalfPlane.im]
      have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hp'
      have h2 := hp'.2
      rw [hre] at h2
      rw [hi] at h3
      refine ⟨abs_le.1 h2, ?_⟩
      show (1 / 2 : ℝ) < y
      nlinarith
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [ENNReal.add_lt_top]
  constructor
  · rw [withDensity_apply _ (measurableSet_Icc.prod measurableSet_Ioi), ← Measure.prod_restrict,
      lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const]
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi (by norm_num))]
    exact ENNReal.mul_lt_top tail_fin (by simp)
  · rw [withDensity_absolutelyContinuous _ _ (by simp [Measure.prod_prod, Iic_inter_Ioi])]
    exact ENNReal.zero_lt_top
end

section

open Set

namespace UpperTheory.V.Af.Rs

private lemma one_le_norm {x : Fin 2 → ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ ‖x i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (norm_le_pi_norm x i)

private lemma ker_le (hB : KerBd) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) {z : UpperHalfPlane}
    (hz : z ∈ ModularGroup.fd) (x : Fin 2 → ℤ) :
    ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
  obtain ⟨-, -, h3, -, -, h6⟩ := hB s hs
  have him0 : 0 < z.im := z.im_pos
  have him : 1 / 2 < z.im := by
    have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    nlinarith
  by_cases hx : x = 0
  · subst hx
    rw [h3]
    simp
  · have hn := one_le_norm hx
    have hpos : 0 < ‖x‖ := by linarith
    have e1 : ‖x‖ ^ (-(2 * s)) ≤ ‖x‖ ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith [hs.1])
    have e2 : ‖x‖ * ‖x‖ ^ (-3 : ℝ) = ‖x‖ ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = 1 + (-3) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have hp : 0 ≤ ‖x‖ ^ (-2 : ℝ) := Real.rpow_nonneg hpos.le _
    have hq : 4 * z.im ^ 2 ≤ 8 * z.im ^ 3 := by
      nlinarith [mul_pos (pow_pos him0 2) (by linarith : (0 : ℝ) < 2 * z.im - 1)]
    calc ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) := h6 x z hz
      _ ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-2 : ℝ) := by gcongr
      _ ≤ 8 * z.im ^ 3 * ‖x‖ ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right hq hp
      _ = 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by rw [← e2]; ring

private lemma diff_le (hB : KerBd) (hD : KerDiff) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (1 : ℝ) 2,
    ∀ x x' : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
    |ker s x z - ker s x' z| ≤ C * ‖x - x'‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := hD
  refine ⟨max C 8, hC0.trans (le_max_left _ _), ?_⟩
  intro s hs x x' z hz
  obtain ⟨-, h2, h3, -⟩ := hB s hs
  have h0 : ‖(0 : Fin 2 → ℤ)‖ ^ (-3 : ℝ) = 0 := by
    rw [norm_zero]
    exact Real.zero_rpow (by norm_num)
  by_cases hx : x = 0
  · by_cases hx' : x' = 0
    · subst hx hx'
      rw [h3, sub_self, abs_zero]
      positivity
    · subst hx
      rw [h3, zero_sub, abs_neg, abs_of_nonneg (h2 _ _), zero_sub, norm_neg, h0, zero_add]
      calc ker s x' z ≤ 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := ker_le hB hs hz x'
        _ ≤ max C 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
  · by_cases hx' : x' = 0
    · subst hx'
      rw [h3, sub_zero, abs_of_nonneg (h2 _ _), sub_zero, h0, add_zero]
      calc ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := ker_le hB hs hz x
        _ ≤ max C 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
    · refine (hC s hs x x' hx hx' z hz).trans ?_
      gcongr
      exact le_max_left _ _

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.zDiff :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerDiff → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff := by
  intro hB hD hW L _
  obtain ⟨C, hC0, hC⟩ := diff_le hB hD
  have hS : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-3 : ℝ) := hW.1 3 (by norm_num)
  set S := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-3 : ℝ) with hSdef
  refine ⟨C * L * (2 * S), ?_⟩
  intro v v' s hs z hz
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h2, -, -, -, h6⟩ := hB s hs'
  have him : 0 < z.im := z.im_pos
  let a : Fin 2 → ℤ := fun i => ((v' i - v i : ZMod L).val : ℤ)
  have hcls : ∀ x, cls L (x + a) = v' ↔ cls L x = v := by
    intro x
    have e : cls L (x + a) = cls L x + (v' - v) := by
      funext i
      simp [cls, a, ZMod.natCast_zmod_val]
    rw [e]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  have ha : ‖a‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [a, Int.norm_eq_abs]
    rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    exact_mod_cast (ZMod.val_lt _).le
  have hker : Summable fun x : Fin 2 → ℤ => ker s x z := by
    refine Summable.of_nonneg_of_le (fun x => h2 x z) (fun x => h6 x z hz) ?_
    exact (hW.1 (2 * s) (by linarith [hs.1])).mul_left _
  have hker' : Summable fun x : Fin 2 → ℤ => ker s (x + a) z :=
    (Equiv.addRight a).summable_iff.mpr hker
  have hS' : Summable fun x : Fin 2 → ℤ => ‖x + a‖ ^ (-3 : ℝ) :=
    (Equiv.addRight a).summable_iff.mpr hS
  set g : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s x z else 0 with hg
  set g' : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s (x + a) z else 0 with hg'
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker
    · simp only [hg]
      split_ifs
      exacts [h2 x z, le_rfl]
    · simp only [hg]
      split_ifs
      exacts [le_rfl, h2 x z]
  have hgs' : Summable g' := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker'
    · simp only [hg']
      split_ifs
      exacts [h2 _ z, le_rfl]
    · simp only [hg']
      split_ifs
      exacts [le_rfl, h2 _ z]
  have hZ : Zc L v s z = ∑' x, g x := rfl
  have hZ' : Zc L v' s z = ∑' x, g' x := by
    show (∑' x, if cls L x = v' then ker s x z else 0) = _
    rw [← (Equiv.addRight a).tsum_eq (fun x => if cls L x = v' then ker s x z else 0)]
    congr 1
    funext x
    change (if cls L (x + a) = v' then ker s (x + a) z else 0) = g' x
    simp only [hg', hcls]
  have hd : ∀ x, |g x - g' x| ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
    intro x
    have hnn : 0 ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by positivity
    simp only [hg, hg']
    split_ifs
    · have e : ‖x - (x + a)‖ = ‖a‖ := by simp
      calc |ker s x z - ker s (x + a) z|
          ≤ C * ‖x - (x + a)‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
            hC s hs' x (x + a) z hz
        _ ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
            rw [e]
            gcongr
    · simpa using hnn
  have hh : Summable fun x : Fin 2 → ℤ =>
      C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
    (hS.add hS').mul_left _
  have hshift : ∑' x : Fin 2 → ℤ, ‖x + a‖ ^ (-3 : ℝ) = S :=
    (Equiv.addRight a).tsum_eq (fun x => ‖x‖ ^ (-3 : ℝ))
  have hsum : ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ))
      = C * L * z.im ^ 3 * (2 * S) := by
    rw [tsum_mul_left, hS.tsum_add hS', hshift]
    ring
  rw [hZ, hZ', ← hgs.tsum_sub hgs']
  calc |∑' x, (g x - g' x)|
      ≤ ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
        rw [abs_le]
        constructor
        · rw [← tsum_neg]
          exact Summable.tsum_le_tsum (fun x => neg_le_of_abs_le (hd x)) hh.neg (hgs.sub hgs')
        · exact Summable.tsum_le_tsum (fun x => le_of_abs_le (hd x)) (hgs.sub hgs') hh
    _ = C * L * z.im ^ 3 * (2 * S) := hsum
    _ = C * L * (2 * S) * z.im ^ 3 := by ring
end

section

open MeasureTheory in
theorem UpperTheory.V.Af.Rs.tBdd :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TBdd := by
  intro hF hD _ L _ G hG h0
  obtain ⟨C, hC⟩ := hD L
  obtain ⟨-, D, hD⟩ := hG
  refine ⟨(∑ _v : Fin 2 → ZMod L, |C| * D) * (volume : Measure UpperHalfPlane).real ModularGroup.fd, fun s hs => ?_⟩
  unfold UpperTheory.V.Af.Rs.TT
  refine norm_setIntegral_le_of_norm_le_const hF.2 fun z hz => ?_
  have hy : 0 < z.im := z.im_pos
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy2 : 1 / 2 ≤ z.im := by nlinarith
  have he : ∑ v, G v z * (UpperTheory.V.Af.Rs.Zc L v s z : ℂ) =
      ∑ v, G v z * ((UpperTheory.V.Af.Rs.Zc L v s z - UpperTheory.V.Af.Rs.Zc L 0 s z : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h0 z, zero_mul, sub_zero]
  rw [he]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hC v 0 s hs z hz
  have h2 := hD v z hy2
  have h4 : C * z.im ^ 3 ≤ |C| * z.im ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  calc _ ≤ ‖G v z‖ * (|C| * z.im ^ 3) := mul_le_mul_of_nonneg_left (h1.trans h4) (norm_nonneg _)
    _ = |C| * (‖G v z‖ * z.im ^ 3) := by ring
    _ ≤ |C| * D := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
end
