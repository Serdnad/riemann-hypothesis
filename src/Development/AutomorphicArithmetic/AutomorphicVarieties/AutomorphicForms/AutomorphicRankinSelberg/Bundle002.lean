module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open MeasureTheory Set UpperHalfPlane

private lemma half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private lemma intOn_of_bdd (hF : UpperTheory.V.Af.Rs.FdFin) (φ : ℍ → ℝ) (hc : Continuous φ) (B : ℝ)
    (hB : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ B) : IntegrableOn φ ModularGroup.fd :=
  Measure.integrableOn_of_bounded hF.2.ne hc.aestronglyMeasurable
    ((ae_restrict_iff' hF.1).2 (Filter.Eventually.of_forall hB))

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.tTop :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdPos → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZLow → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TTop := by
  intro hfd hpos hw hzd hzl hzi L _ G hG hre hex M
  obtain ⟨hGc, C', hC'⟩ := hG
  obtain ⟨C, hC⟩ := hzd L
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (Fintype.card (Fin 2 → ZMod L) : ℝ) := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hNpos : 0 < N := by linarith
  have hcard : ∀ x : ℝ, (Finset.univ : Finset (Fin 2 → ZMod L)).card • x = N * x := by
    intro x
    rw [Finset.card_univ, nsmul_eq_mul, hN]
  obtain ⟨φ, hφ⟩ : ∃ φ : ℍ → ℝ,
      φ = fun z => (∑ v, (G v z).re) / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℍ → ℝ, ψ = fun z => ∑ v, (G v z).re * z.im ^ 3 := ⟨_, rfl⟩
  have hreC : ∀ v, Continuous fun z => (G v z).re := fun v => Complex.continuous_re.comp (hGc v)
  have himC : Continuous fun z : ℍ => z.im := UpperHalfPlane.continuous_im
  have hnC : Continuous fun z : ℍ => ‖(z : ℂ)‖ := continuous_norm.comp UpperHalfPlane.continuous_coe
  have hden : ∀ z : ℍ, 0 < 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := fun z => by positivity
  have hφC : Continuous φ := by
    rw [hφ]
    exact (continuous_finsetSum _ (fun v _ => hreC v)).div
      (continuous_const.mul ((hnC.add continuous_const).pow 4)) (fun z => (hden z).ne')
  have hψC : Continuous ψ := by
    rw [hψ]
    exact continuous_finsetSum _ (fun v _ => (hreC v).mul (himC.pow 3))
  have hGb : ∀ v, ∀ z ∈ ModularGroup.fd,
      0 ≤ (G v z).re * z.im ^ 3 ∧ (G v z).re * z.im ^ 3 ≤ C' := by
    intro v z hz
    have hp : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    refine ⟨mul_nonneg (hre v z) hp, ?_⟩
    exact (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hp).trans (hC' v z (half_le_im hz))
  have hψb : ∀ z ∈ ModularGroup.fd, ‖ψ z‖ ≤ N * C' := by
    intro z hz
    rw [hψ, Real.norm_of_nonneg (Finset.sum_nonneg (fun v _ => (hGb v z hz).1))]
    exact (Finset.sum_le_card_nsmul _ _ _ (fun v _ => (hGb v z hz).2)).trans_eq (hcard _)
  have hφb : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ N * (8 * C') := by
    intro z hz
    have hs0 : 0 ≤ ∑ v, (G v z).re := Finset.sum_nonneg (fun v _ => hre v z)
    have h1 : 1 ≤ 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := by
      have : 1 ≤ (‖(z : ℂ)‖ + 1) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg (z : ℂ)])
      nlinarith
    rw [hφ, Real.norm_of_nonneg (div_nonneg hs0 (hden z).le)]
    refine (div_le_self hs0 h1).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ (fun v _ => ?_)).trans_eq (hcard _)
    have h8 := (hGb v z hz).2
    have h3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) (half_le_im hz) 3) (hre v z)
    norm_num at h3
    linarith
  have hφI := intOn_of_bdd hfd φ hφC _ hφb
  have hψI := intOn_of_bdd hfd ψ hψC _ hψb
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    rw [hφ]
    exact div_nonneg (Finset.sum_nonneg (fun v _ => hre v z)) (hden z).le
  obtain ⟨v0, z0, hz0, hv0⟩ := hex
  have hc : 0 < ∫ z in ModularGroup.fd, φ z := by
    refine hpos φ hφC hφ0 hφI z0 hz0 ?_
    rw [hφ]
    refine div_pos ?_ (hden z0)
    exact lt_of_lt_of_le hv0
      (Finset.single_le_sum (f := fun v => (G v z0).re) (fun v _ => hre v z0) (Finset.mem_univ v0))
  obtain ⟨c, hcd⟩ : ∃ c, c = ∫ z in ModularGroup.fd, φ z := ⟨_, rfl⟩
  rw [← hcd] at hc
  have hψint : ∫ z in ModularGroup.fd, ψ z ≤ N * C' * volume.real ModularGroup.fd :=
    (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hfd.2 hψb)
  obtain ⟨s, hs, hWs⟩ := hw.2 ((M + |C| * (N * C' * volume.real ModularGroup.fd)) / c)
  refine ⟨s, hs, ?_⟩
  have hpt : ∀ z ∈ ModularGroup.fd,
      Wsum s * φ z - |C| * ψ z ≤ (∑ v, G v z * (Zc L v s z : ℂ)).re := by
    intro z hz
    have hlow := hzl L s hs z hz
    have hp3 : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    have hZ : ∀ v, Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3 ≤ Zc L v s z := by
      intro v
      have hsum : ∑ v', Zc L v' s z ≤ N * (Zc L v s z + |C| * z.im ^ 3) := by
        refine (Finset.sum_le_card_nsmul _ _ _ (fun v' _ => ?_)).trans_eq (hcard _)
        have h1 := hC v v' s hs z hz
        have h2 := mul_le_mul_of_nonneg_right (le_abs_self C) hp3
        have h3 := neg_abs_le (Zc L v s z - Zc L v' s z)
        linarith
      have hq : 1 / 2 / (‖(z : ℂ)‖ + 1) ^ 4 * Wsum s =
          N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) := by
        have := hden z
        field_simp
      have h4 : N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) ≤ N * (Zc L v s z + |C| * z.im ^ 3) :=
        hq ▸ hlow.trans hsum
      have h5 := le_of_mul_le_mul_left h4 hNpos
      linarith
    rw [Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hφ, hψ]
    simp only
    rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have h6 := mul_le_mul_of_nonneg_left (hZ v) (hre v z)
    calc Wsum s * ((G v z).re / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) - |C| * ((G v z).re * z.im ^ 3)
        = (G v z).re * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3) := by ring
      _ ≤ (G v z).re * Zc L v s z := h6
  have hfI : IntegrableOn (fun z => ∑ v, G v z * (Zc L v s z : ℂ)) ModularGroup.fd :=
    integrable_finsetSum _ (fun v _ => hzi L G ⟨hGc, C', hC'⟩ s hs v v)
  have hre_eq : (∫ z in ModularGroup.fd, ∑ v, G v z * (Zc L v s z : ℂ)).re =
      ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re := (integral_re hfI).symm
  unfold TT
  rw [hre_eq]
  calc M ≤ Wsum s * c - |C| * (N * C' * volume.real ModularGroup.fd) := by
        have := (div_le_iff₀ hc).1 hWs
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (Wsum s * φ z - |C| * ψ z) := by
        rw [integral_sub (hφI.const_mul _) (hψI.const_mul _), integral_const_mul,
          integral_const_mul, ← hcd]
        have := mul_le_mul_of_nonneg_left hψint (abs_nonneg C)
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re :=
        setIntegral_mono_on ((hφI.const_mul _).sub (hψI.const_mul _)) hfI.re hfd.1 hpt
end

section

open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private lemma nsq_eq (x : Fin 2 → ℤ) (z : ℍ) :
    Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) =
      ((x 0 : ℝ) * z.re + x 1) ^ 2 + ((x 0 : ℝ) * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

private lemma nsq_pos (x : Fin 2 → ℤ) (hx : x ≠ 0) (z : ℍ) :
    0 < Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have : (x 1 : ℝ) ≠ 0 := by exact_mod_cast h1
    simp only [h0, Int.cast_zero, zero_mul, zero_add]
    positivity
  · have : (x 0 : ℝ) ≠ 0 := by exact_mod_cast h0
    have := z.im_pos.ne'
    positivity

private lemma nsq_low (x : Fin 2 → ℤ) (z : ℍ) (hz : z ∈ ModularGroup.fd) :
    ‖x‖ ^ 2 ≤ 2 * Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  obtain ⟨hz1, hzre⟩ := hz
  have hN : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have := hz1
    rw [Complex.normSq_apply] at this
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    nlinarith
  set a : ℝ := (x 0 : ℝ)
  set b : ℝ := (x 1 : ℝ)
  have hnorm : ‖x‖ ≤ max |a| |b| := by
    refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).mpr fun i => ?_
    fin_cases i
    · simp [Int.norm_eq_abs, a]
    · simp [Int.norm_eq_abs, b]
  have hM : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_nonneg a]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_nonneg b]
  have hx2 : ‖x‖ ^ 2 ≤ (max |a| |b|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hab : -(|a| * |b|) ≤ 2 * a * b * z.re := by
    have h1 : |2 * a * b * z.re| ≤ |a| * |b| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have := abs_nonneg a
      have := abs_nonneg b
      nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b)]
    exact (abs_le.mp h1).1
  have hsq : a ^ 2 + b ^ 2 ≤ 2 * (a ^ 2 - |a| * |b| + b ^ 2) := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hexp : (a * z.re + b) ^ 2 + (a * z.im) ^ 2
      = a ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * a * b * z.re + b ^ 2 := by ring
  rw [hexp]
  have : a ^ 2 ≤ a ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
    nlinarith [sq_nonneg a]
  linarith

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.kerBd :
    UpperTheory.V.Af.Rs.KerBd := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 < s := by linarith
  have hzero : ∀ z, ker s 0 z = 0 := by
    intro z
    simp [ker, Real.zero_rpow hs0.ne']
  have hnn : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) :=
    fun x z => div_nonneg z.im_pos.le (Complex.normSq_nonneg _)
  refine ⟨?_, ?_, hzero, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      have : ker s 0 = fun _ => 0 := funext hzero
      rw [this]; exact continuous_const
    · unfold ker
      refine Continuous.rpow_const ?_ (fun _ => Or.inr hs0.le)
      refine Continuous.div UpperHalfPlane.continuous_im ?_ (fun z => (nsq_pos x hx z).ne')
      exact Complex.continuous_normSq.comp
        ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const)
  · intro x z
    exact Real.rpow_nonneg (hnn x z) _
  · intro γ z
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
    rfl
  · intro n x z
    have h : Complex.normSq (((((n : ℤ) • x) 0 : ℤ) : ℂ) * z + ((((n : ℤ) • x) 1 : ℤ) : ℂ)) =
        Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) * (n : ℝ) ^ (2 : ℝ) := by
      rw [nsq_eq, nsq_eq]
      simp
      ring
    unfold ker
    rw [h, ← div_div, Real.div_rpow (hnn x z) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg n)]
  · intro x z hz
    by_cases hx : x = 0
    · subst hx
      rw [hzero]
      positivity
    · have hp := nsq_pos x hx z
      have hl := nsq_low x z hz
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy := z.im_pos
      have hy1 : 1 ≤ 2 * z.im := by
        have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
        nlinarith
      have h1 : z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) ≤ 2 * z.im / ‖x‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two, div_le_div_iff₀ hp (by positivity)]
        nlinarith
      calc ker s x z ≤ (2 * z.im / ‖x‖ ^ (2 : ℝ)) ^ s := Real.rpow_le_rpow (hnn x z) h1 hs0.le
        _ = (2 * z.im) ^ s * ‖x‖ ^ (-(2 * s)) := by
          rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn.le,
            Real.rpow_neg hn.le, div_eq_mul_inv]
        _ ≤ (2 * z.im) ^ (2 : ℝ) * ‖x‖ ^ (-(2 * s)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hy1 hs2) (by positivity)
        _ = _ := by rw [Real.rpow_two]; ring
end

section

noncomputable section

open MeasureTheory Set

namespace UpperTheory.V.Af.Rs

private lemma melSum_int {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    IntegrableOn (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := t - 1) (p := 1) (b := r) (by linarith) one_pos hr).const_mul a
  refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring

private lemma melSum_val {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    ∫ y in Ioi (0 : ℝ), a * Real.exp (-r * y) * y ^ (t - 1) = a * ((1 / r) ^ t * Real.Gamma t) := by
  have e : (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) =
      fun y => a * (y ^ (t - 1) * Real.exp (-(r * y))) := by
    funext y
    rw [neg_mul]
    ring
  rw [e, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ht hr]

theorem melSum : MelSum := by
  intro c P t ht hc hP hI
  have hΓ : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
  have h4 : 0 < 4 * Real.pi := by positivity
  have hCpos : 0 < (4 * Real.pi) ^ t / Real.Gamma t := div_pos (Real.rpow_pos_of_pos h4 t) hΓ
  have hr : ∀ n : ℕ, 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hval : ∀ n : ℕ, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t =
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ),
        c (n + 1) * Real.exp (-(4 * Real.pi * ((n + 1 : ℕ) : ℝ)) * y) * y ^ (t - 1) := by
    intro n
    rw [melSum_val ht (hr n)]
    have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Real.div_rpow zero_le_one (hr n).le, Real.one_rpow, Real.mul_rpow h4.le hm.le]
    have h5 : 0 < ((n + 1 : ℕ) : ℝ) ^ t := Real.rpow_pos_of_pos hm t
    have h6 : 0 < (4 * Real.pi) ^ t := Real.rpow_pos_of_pos h4 t
    field_simp
  have hbound : ∀ N, ∑ n ∈ Finset.range N, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t ≤
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ), P y * y ^ (t - 1) := by
    intro N
    simp_rw [hval]
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun n _ => melSum_int ht (hr n) _)]
    apply mul_le_mul_of_nonneg_left _ hCpos.le
    apply setIntegral_mono_on
    · exact integrable_finsetSum _ (fun n _ => melSum_int ht (hr n) _)
    · exact hI
    · exact measurableSet_Ioi
    · intro y hy
      have hy' : 0 < y := hy
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy'.le _)
      have h1 : ∑ n ∈ Finset.range (N + 1), c n * Real.exp (-(4 * Real.pi * n) * y) ≤ P y :=
        sum_le_hasSum _ (fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le) (hP y hy')
      rw [Finset.sum_range_succ'] at h1
      have h0 : 0 ≤ c 0 * Real.exp (-(4 * Real.pi * ((0 : ℕ) : ℝ)) * y) :=
        mul_nonneg (hc 0) (Real.exp_pos _).le
      linarith
  have hs : Summable (fun n : ℕ => c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t) :=
    summable_of_sum_range_le
      (fun n => div_nonneg (hc _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hbound
  exact (summable_nat_add_iff 1 (f := fun n : ℕ => c n / (n : ℝ) ^ t)).mp hs

end UpperTheory.V.Af.Rs
end
end

section

open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private theorem pt_im (x y : ℝ) (hy : 0 < y) : (pt x y).im = y := by
  simp [pt, UpperHalfPlane.ofComplex_apply_of_im_pos, hy]

private theorem coef_zero (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) : coef f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (by simp)

private theorem integrableOn_rpow_mul_exp_neg_Ioi (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y ^ (A - 1) * Real.exp (-r * y)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A - 1) (b := r)
    (by linarith) one_pos hr
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

private theorem integral_rpow_mul_exp_neg_Ioi_eq_gamma_div (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    ∫ y in Ioi (0:ℝ), y ^ (A - 1) * Real.exp (-r * y) = Real.Gamma A / r ^ A := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hA hr
  simp only [neg_mul] at h ⊢
  rw [h, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
  ring

private theorem gamma_div_four_pi_mul_rpow_eq (A : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.Gamma A / (4 * Real.pi * n) ^ A = Real.Gamma A / (4 * Real.pi) ^ A / (n : ℝ) ^ A := by
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (0:ℝ) < (4 * Real.pi) ^ A := by positivity
  have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
  field_simp

theorem UpperTheory.V.Af.Rs.rankin :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin := by
  intro hFub hInt hNice hPars hSum k L _ f g s hs
  have hs1 : 1 < s := hs.1
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  set A : ℝ := (k:ℝ) + s - 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith
  set a : ℕ → ℂ := fun n => starRingEnd ℂ (coef g n) * coef f n with ha
  have ha0 : a 0 = 0 := by simp [ha, coef_zero k L f]
  set G : ℕ → ℝ → ℂ := fun n y =>
    a n * ((y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ) with hG
  have hpt : ∀ y : ℝ, 0 < y →
      (∫ x in (0:ℝ)..1, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ))
        / ((y ^ 2 : ℝ) : ℂ) = ∑' n, G n y := by
    intro y hy
    have h1 : ∀ x : ℝ, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ)
        = (starRingEnd ℂ (g (pt x y)) * f (pt x y)) * ((y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ)) := by
      intro x
      simp only [UpperHalfPlane.petersson, pt_im x y hy, zpow_natCast]
      ring
    have hyA : ((y ^ (A - 1) : ℝ) : ℂ) = (y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ) / ((y ^ 2 : ℝ) : ℂ) := by
      have hr : y ^ (A - 1) = y ^ k * y ^ s / y ^ 2 := by
        rw [show A - 1 = ((k:ℝ) + s) - 2 by rw [hAdef]; ring, Real.rpow_sub hy, Real.rpow_add hy,
          Real.rpow_natCast, Real.rpow_two]
      rw [hr]
      push_cast
      ring
    simp_rw [h1]
    rw [intervalIntegral.integral_mul_const, ← (hPars k L f g y hy).tsum_eq, ← tsum_mul_right,
      ← tsum_div_const]
    congr 1
    ext n
    simp only [hG, ha]
    rw [Complex.ofReal_mul, hyA]
    ring
  have hr : ∀ n : ℕ, 0 < n → (0:ℝ) < 4 * Real.pi * n := fun n hn => by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hGi : ∀ n, Integrable (G n) (volume.restrict (Ioi (0:ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : G 0 = fun _ => 0 := by funext y; simp [hG, ha0]
      rw [this]
      exact integrable_zero _ _ _
    · exact ((integrableOn_rpow_mul_exp_neg_Ioi A _ hA (hr n hn)).ofReal).const_mul (a n)
  have hsum : Summable (fun n : ℕ => ‖a n‖ / (n:ℝ) ^ A) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((hSum k L f s hs).add (hSum k L g s hs)).div_const 2)
    have key : ‖coef g n‖ * ‖coef f n‖ ≤ (‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖coef f n‖ - ‖coef g n‖)]
    have hn : (0:ℝ) ≤ (n:ℝ) ^ A := by positivity
    calc ‖a n‖ / (n:ℝ) ^ A = (‖coef g n‖ * ‖coef f n‖) / (n:ℝ) ^ A := by
          simp [ha, norm_mul]
      _ ≤ ((‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2) / (n:ℝ) ^ A := by gcongr
      _ = _ := by ring
  have hGs : Summable (fun n => ∫ y in Ioi (0:ℝ), ‖G n y‖) := by
    refine (hsum.mul_left (Real.Gamma A / (4 * Real.pi) ^ A)).congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hG, ha0]
    · have hc : ∫ y in Ioi (0:ℝ), ‖G n y‖
          = ∫ y in Ioi (0:ℝ), ‖a n‖ * (y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
        have hy' : (0:ℝ) < y := hy
        simp only [hG, norm_mul, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [hc, integral_const_mul, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn]
      ring
  have hI := hInt _ (hNice k L f g) s hs
  obtain ⟨-, heq⟩ := hFub _ hI
  show (∫ z in strip, _) = _
  rw [heq, setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpt y hy),
    ← integral_tsum_of_summable_integral_norm hGi hGs, ← tsum_mul_left]
  congr 1
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hG, ha0, coef_zero k L f]
  · simp only [hG]
    rw [integral_const_mul, integral_complex_ofReal, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn, gam]
    have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
    push_cast
    field_simp
    simp only [ha]
    ring
end
