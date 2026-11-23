module

public import GroundTheory.PAdicHodge.BCrisNewtonNorm
public import GroundTheory.PAdicHodge.Bundle007
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector Laurent Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝔸" => Localization.Away (p : AInf K p)

theorem norm_coeffB_toB_le_one (z : 𝔸) (n : ℤ) : ‖(teichLift K p).coeffB (toB K p z) n‖ ≤ 1 := by
  obtain ⟨M, x, h⟩ := exists_toB_mul z
  rw [TeichLift.coeffB_eq _ h]
  exact norm_zcoeff_incl_le_one x _

theorem exists_gn_eq_monomial {z : 𝔸} (hz : z ≠ 0) {r₀ : ℝ} (hr0 : 0 < r₀) (hr1 : r₀ < 1) :
    ∃ (β : ℝ) (i : ℤ) (ρ₃ : ℝ), 0 < β ∧ r₀ < ρ₃ ∧ ρ₃ < 1 ∧
      ∀ ρ ∈ Set.Icc r₀ ρ₃, gn K p ρ z = β * ρ ^ i := by
  set a := (teichLift K p).coeffB (toB K p z) with ha_def
  have hconv : ∀ ρ, 0 < ρ → ρ < 1 → ConvergesAt a ρ := fun ρ h0 h1 => convergesAt_toB z h0 h1
  have ha0 : a ≠ 0 := by
    intro h
    have := gn_pos (K := K) hr0 hr1 hz
    unfold gn at this
    rw [← ha_def, h] at this
    simp [gaussNorm] at this
  set i := highIndex a r₀
  have hi := highIndex_mem hr0 (hconv r₀ hr0 hr1) ha0
  set β := ‖a i‖ with hβ_def
  have hβ : 0 < β := norm_pos_iff.2 (ne_zero_of_mem_domSet hr0 (hconv r₀ hr0 hr1) ha0 hi)
  have hG : gaussNorm a r₀ = β * r₀ ^ i := hi.symm
  set ρt := (r₀ + 1) / 2 with hρt
  have hρt0 : 0 < ρt := by linarith
  have hρt1 : ρt < 1 := by linarith
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hβ hρt1
  have hev : ∀ᶠ ρ in 𝓝 r₀, ∀ n ∈ Finset.Ioc i (i + L), ‖a n‖ * ρ ^ n < β * ρ ^ i := by
    rw [Filter.eventually_all_finset]
    intro n hn
    have hlt : ‖a n‖ * r₀ ^ n < β * r₀ ^ i := by
      rw [← hG]
      exact weight_lt_of_highIndex_lt hr0 (hconv r₀ hr0 hr1) ha0 (Finset.mem_Ioc.1 hn).1
    have hc : ContinuousAt (fun ρ : ℝ => β * ρ ^ i - ‖a n‖ * ρ ^ n) r₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ r₀ i (Or.inl hr0.ne'))).sub
        (continuousAt_const.mul (continuousAt_zpow₀ r₀ n (Or.inl hr0.ne')))
    filter_upwards [hc.eventually (lt_mem_nhds (sub_pos.2 hlt))] with ρ hρ
    exact sub_pos.1 hρ
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨β, i, min (r₀ + δ / 2) ρt, hβ, lt_min (by linarith) (by linarith),
    (min_le_right _ _).trans_lt hρt1, fun ρ hρ => ?_⟩
  have hρ0 : 0 < ρ := hr0.trans_le hρ.1
  have hρ1 : ρ < 1 := hρ.2.trans_lt ((min_le_right _ _).trans_lt hρt1)
  have hρt' : ρ ≤ ρt := hρ.2.trans (min_le_right _ _)
  have hd : dist ρ r₀ < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hρ.1])]
    linarith [hρ.2, min_le_left (r₀ + δ / 2) ρt]
  have hnear := hδf hd
  unfold gn
  rw [← ha_def]
  refine le_antisymm (gaussNorm_le fun n => ?_) ((hconv ρ hρ0 hρ1).le_gaussNorm i)
  rcases le_or_gt n i with hni | hni
  ·
    have h1 : ‖a n‖ * r₀ ^ n ≤ β * r₀ ^ i := hG ▸ (hconv r₀ hr0 hr1).le_gaussNorm n
    have hq : 1 ≤ ρ / r₀ := (one_le_div hr0).2 hρ.1
    have h2 : (ρ / r₀) ^ n ≤ (ρ / r₀) ^ i := zpow_le_zpow_right₀ hq hni
    have e1 : ‖a n‖ * ρ ^ n = (‖a n‖ * r₀ ^ n) * (ρ / r₀) ^ n := by
      rw [div_zpow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (zpow_ne_zero n hr0.ne')]
    have e2 : β * ρ ^ i = (β * r₀ ^ i) * (ρ / r₀) ^ i := by
      rw [div_zpow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (zpow_ne_zero i hr0.ne')]
    rw [e1, e2]
    exact mul_le_mul h1 h2 (zpow_nonneg (div_nonneg hρ0.le hr0.le) n)
      (mul_nonneg hβ.le (zpow_nonneg hr0.le i))
  · rcases le_or_gt n (i + L) with hnL | hnL
    · exact (hnear n (Finset.mem_Ioc.2 ⟨hni, hnL⟩)).le
    ·
      have h1 : ‖a n‖ * ρ ^ n ≤ ρ ^ n :=
        mul_le_of_le_one_left (zpow_nonneg hρ0.le n) (norm_coeffB_toB_le_one z n)
      have h2 : ρ ^ n = ρ ^ i * ρ ^ (n - i) := by rw [← zpow_add₀ hρ0.ne']; ring_nf
      have h3 : ρ ^ (n - i) ≤ ρ ^ (L : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le (by omega)
      have h4 : ρ ^ (L : ℤ) ≤ ρt ^ L := by
        rw [zpow_natCast]; exact pow_le_pow_left₀ hρ0.le hρt' L
      have h5 : ρ ^ (n - i) ≤ β := (h3.trans h4).trans hL.le
      calc ‖a n‖ * ρ ^ n ≤ ρ ^ i * ρ ^ (n - i) := h1.trans h2.le
        _ ≤ ρ ^ i * β := mul_le_mul_of_nonneg_left h5 (zpow_nonneg hρ0.le i)
        _ = β * ρ ^ i := mul_comm _ _

end WittTilt

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open _root_.WittVector Laurent Polynomial WittTilt

variable {p : ℕ} [hp : Fact p.Prime]


variable (p) in
def sig (ρ : ℝ) : ℝ := Real.log ρ / Real.log (p : ℝ)⁻¹

theorem inv_p_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt)

theorem log_inv_p_neg : Real.log (p : ℝ)⁻¹ < 0 := Real.log_neg inv_p_pos inv_p_lt_one

theorem rpow_sig {ρ : ℝ} (hρ : 0 < ρ) : ((p : ℝ)⁻¹) ^ sig p ρ = ρ := by
  rw [Real.rpow_def_of_pos inv_p_pos]
  have : Real.log (p : ℝ)⁻¹ * sig p ρ = Real.log ρ := by
    unfold sig
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ log_inv_p_neg.ne
  rw [this, Real.exp_log hρ]

theorem sig_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < sig p ρ :=
  div_pos_of_neg_of_neg (Real.log_neg hρ0 hρ1) log_inv_p_neg

theorem sig_inv_p : sig p (p : ℝ)⁻¹ = 1 := div_self log_inv_p_neg.ne

theorem norm_p_Cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_p_algCl : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem pow_rpow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (s : ℝ) : (x ^ n) ^ s = (x ^ s) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

theorem gn_padicInt {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : ℤ_[p]) :
    gn ℂ_[p] p ρ (algebraMap (AInf ℂ_[p] p) (Localization.Away (p : AInf ℂ_[p] p))
      (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p c)) =
      ‖c‖ ^ sig p ρ := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, map_zero, gn_zero, norm_zero, Real.zero_rpow (sig_pos hρ0 hρ1).ne']
  · have hn : ‖c‖ = ((p : ℝ)⁻¹) ^ c.valuation := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [norm_mul, PadicInt.norm_units, one_mul, norm_pow, PadicInt.norm_p]
    conv_lhs => rw [PadicInt.unitCoeff_spec hc]
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, gn_mul hρ0 hρ1,
      gn_unit hρ0 hρ1 ((PadicInt.unitCoeff hc).isUnit.map _), one_mul, gn_pow hρ0 hρ1,
      gn_natCast_p hρ0, hn, pow_rpow_comm inv_p_pos.le, rpow_sig hρ0]

theorem natDegree_minpoly_pos (y : PadicAlgCl p) : 0 < (minpoly ℚ_[p] y).natDegree :=
  minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)

theorem norm_minpoly_coeff_le (y : PadicAlgCl p) {i : ℕ} (hi : i ≤ (minpoly ℚ_[p] y).natDegree) :
    ‖(minpoly ℚ_[p] y).coeff i‖ ≤ ‖y‖ ^ ((minpoly ℚ_[p] y).natDegree - i) := by
  set q := minpoly ℚ_[p] y with hq
  rcases hi.lt_or_eq with hi | hi
  · have h1 : ‖q.coeff i‖ ^ (1 / (q.natDegree - i : ℝ)) ≤ ‖y‖ := by
      have e : ‖y‖ = spectralValue q := rfl
      rw [e, ← spectralValueTerms_of_lt_natDegree _ hi]
      exact le_ciSup (spectralValueTerms_bddAbove _) i
    have hpos : (0 : ℝ) < (q.natDegree - i : ℝ) := by
      have : (i : ℝ) < q.natDegree := by exact_mod_cast hi
      linarith
    have hcast : ((q.natDegree - i : ℕ) : ℝ) = (q.natDegree - i : ℝ) := by
      rw [Nat.cast_sub hi.le]
    calc ‖q.coeff i‖ = (‖q.coeff i‖ ^ (1 / (q.natDegree - i : ℝ))) ^ ((q.natDegree - i : ℕ) : ℝ) := by
          rw [← Real.rpow_mul (norm_nonneg _), hcast, one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one]
      _ ≤ ‖y‖ ^ ((q.natDegree - i : ℕ) : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (Nat.cast_nonneg _)
      _ = ‖y‖ ^ (q.natDegree - i) := Real.rpow_natCast _ _
  · rw [hi, Nat.sub_self, pow_zero, (minpoly.monic (Algebra.IsIntegral.isIntegral y)).coeff_natDegree,
      norm_one]

theorem norm_minpoly_coeff_zero (y : PadicAlgCl p) :
    ‖(minpoly ℚ_[p] y).coeff 0‖ = ‖y‖ ^ (minpoly ℚ_[p] y).natDegree := by
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := PadicAlgCl p) y
  rw [PadicAlgCl.spectralNorm_eq] at h
  have hd : (0 : ℝ) < (minpoly ℚ_[p] y).natDegree := by exact_mod_cast natDegree_minpoly_pos y
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hd.ne',
    Real.rpow_one]

theorem eq_of_no_dominant {d : ℕ} (hd : 1 ≤ d) {Fa Fb μ ρk : ℝ} (hFa : 0 < Fa) (hFb : 0 < Fb)
    (hμ : 0 < μ) (hρk : 0 < ρk) (G : ℕ → ℝ) (hG : ∀ i ≤ d, 0 ≤ G i ∧ G i ≤ ρk * μ ^ (d - i))
    (hG0 : G 0 = ρk * μ ^ d) (hGd : G d = ρk)
    (hnd : ∀ j ∈ Finset.range (d + 1), 0 < G j * Fa ^ j * Fb ^ (d - j) →
      ¬ ∀ i ∈ Finset.range (d + 1), i ≠ j →
        G i * Fa ^ i * Fb ^ (d - i) < G j * Fa ^ j * Fb ^ (d - j)) :
    Fa = μ * Fb := by
  rcases lt_trichotomy Fa (μ * Fb) with hlt | heq | hgt
  · exfalso
    refine hnd 0 (Finset.mem_range.2 (by omega)) ?_ fun i hi hi0 => ?_
    · rw [hG0]; positivity
    · have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      obtain ⟨hG1, hG2⟩ := hG i hid
      have hpow : Fa ^ i < (μ * Fb) ^ i := pow_lt_pow_left₀ hlt hFa.le hi0
      have e1 : ρk * μ ^ (d - i) * (μ * Fb) ^ i * Fb ^ (d - i) = ρk * μ ^ d * Fb ^ d := by
        rw [mul_pow]
        have h1 : μ ^ (d - i) * μ ^ i = μ ^ d := by rw [← pow_add, Nat.sub_add_cancel hid]
        have h2 : Fb ^ i * Fb ^ (d - i) = Fb ^ d := by rw [← pow_add, Nat.add_sub_cancel' hid]
        calc ρk * μ ^ (d - i) * (μ ^ i * Fb ^ i) * Fb ^ (d - i)
            = ρk * (μ ^ (d - i) * μ ^ i) * (Fb ^ i * Fb ^ (d - i)) := by ring
          _ = _ := by rw [h1, h2]
      rw [hG0, Nat.sub_zero, pow_zero, mul_one, ← e1]
      calc G i * Fa ^ i * Fb ^ (d - i) ≤ ρk * μ ^ (d - i) * Fa ^ i * Fb ^ (d - i) := by
            gcongr
        _ < ρk * μ ^ (d - i) * (μ * Fb) ^ i * Fb ^ (d - i) := by
            have : 0 < ρk * μ ^ (d - i) := by positivity
            have : 0 < Fb ^ (d - i) := by positivity
            gcongr
  · exact heq
  · exfalso
    refine hnd d (Finset.mem_range.2 (by omega)) ?_ fun i hi hid' => ?_
    · rw [hGd, Nat.sub_self, pow_zero, mul_one]; positivity
    · have hid : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hid'
      obtain ⟨hG1, hG2⟩ := hG i hid.le
      have hpow : (μ * Fb) ^ (d - i) < Fa ^ (d - i) := pow_lt_pow_left₀ hgt (by positivity) (by omega)
      have e1 : ρk * Fa ^ i * Fa ^ (d - i) = ρk * Fa ^ d := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hid.le]
      rw [hGd, Nat.sub_self, pow_zero, mul_one, ← e1]
      calc G i * Fa ^ i * Fb ^ (d - i) ≤ ρk * μ ^ (d - i) * Fa ^ i * Fb ^ (d - i) := by gcongr
        _ = ρk * Fa ^ i * (μ * Fb) ^ (d - i) := by rw [mul_pow]; ring
        _ < ρk * Fa ^ i * Fa ^ (d - i) := by
            have : 0 < ρk * Fa ^ i := by positivity
            gcongr

end ACris

end GroundTheory.PAdicHodge
end
end
