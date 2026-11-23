module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle497
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle515
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle506
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.ProperSpace
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022

@[expose] public section

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

namespace RatioProp

variable {l : ℕ} [Fact l.Prime]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

theorem inv_l_pos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith [(one_lt_l : (1 : ℝ) < l)])

theorem inv_l_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_l

theorem rho_pos {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) : 0 < ρ := lt_of_lt_of_le inv_l_pos h0

theorem gauss {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : IsGauss l ρ (gC l ρ) :=
  isGauss_gC_target l ρ h0 h1

theorem phi_zc (c : ℤ_[l]) : φc l (zc l c) = zc l c :=
  (GlobalTheory.MemLoc.PhiFix.phiA_alg l _).trans (congrArg _ (GlobalTheory.MemLoc.PhiFix.φA_zA l c))

theorem iter_lpow (m j : ℕ) (x : Formalism.Per.Acris l) :
    (φc l)^[m] ((l : Formalism.Per.Acris l) ^ j * x) = (l : Formalism.Per.Acris l) ^ j * (φc l)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem gC_zero {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hm := (gauss h0 h1).2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1] at hm
  have e : gC l ρ 0 * (1 - ρ) = 0 := by linear_combination hm
  rcases mul_eq_zero.1 e with h | h
  · exact h
  · exact absurd h (by linarith)

theorem gC_lpow {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (m : ℕ) (x : Formalism.Per.Acris l) :
    gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
  induction m with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ m ih =>
    rw [pow_succ', mul_assoc, (gauss h0 h1).2.2.2.1, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1, ih, pow_succ']
    ring

theorem lpow_ne_zero {x : Formalism.Per.Acris l} (hx : x ≠ 0) (m : ℕ) : (l : Formalism.Per.Acris l) ^ m * x ≠ 0 := by
  intro e
  have h := gC_lpow le_rfl inv_l_lt_one m x
  rw [e, gC_zero le_rfl inv_l_lt_one] at h
  have hp := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ le_rfl inv_l_lt_one
  have : (0 : ℝ) < (l : ℝ)⁻¹ ^ m * gC l (l : ℝ)⁻¹ x := mul_pos (pow_pos inv_l_pos m) hp
  linarith

theorem pert {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (W W' : Formalism.Per.Acris l) (c y : ℤ_[l]) (k : ℕ) :
    gC l ρ (W - zc l (c + (l : ℤ_[l]) ^ k * y) * W') ≤ max (gC l ρ (W - zc l c * W')) (ρ ^ k * gC l ρ W') := by
  have e : W - zc l (c + (l : ℤ_[l]) ^ k * y) * W' =
      (W - zc l c * W') + -((l : Formalism.Per.Acris l) ^ k * (zc l y * W')) := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine ((gauss h0 h1).2.1 _ _).trans (max_le_max le_rfl ?_)
  rw [(gauss h0 h1).2.2.1, gC_lpow h0 h1, (gauss h0 h1).2.2.2.1]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left ((gauss h0 h1).1 _).1 ((gauss h0 h1).1 _).2) (pow_nonneg (rho_pos h0).le _)

def digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : Set ℤ_[l] :=
  {c | ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') ≤ ρ ^ k * gC l ρ W'}

theorem isClosed_digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : IsClosed (digitSet W W' k) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro c hc
  simp only [digitSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hc
  obtain ⟨ρ, h0, h1, hlt⟩ := hc
  refine ⟨(l : ℝ) ^ (-(k : ℤ)), zpow_pos (by linarith [(one_lt_l : (1 : ℝ) < l)]) _, fun c' hc' hT => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hc'
  have hmem : c - c' ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, norm_sub_rev]
    exact hc'.le
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  have hp := pert h0 h1 W W' c' y k
  have e : c' + (l : ℤ_[l]) ^ k * y = c := by rw [mul_comm, hy]; ring
  rw [e] at hp
  exact absurd (hp.trans (max_le (hT ρ h0 h1) le_rfl)) (not_le.2 hlt)

theorem gC_eq_of_vr {V W' : Formalism.Per.Acris l} (hV : V ≠ 0) (hW' : W' ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r V - vr l r W' = n * r) {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ V = ρ ^ n * gC l ρ W' := by
  apply GlobalTheory.PMon.Gauss.gC_eq_zpow_mul_of_vr <;> assumption

theorem digit_step {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W') (k : ℕ) (c : ℤ_[l]) (hc : c ∈ digitSet W W' k) :
    (digitSet W W' (k + 1)).Nonempty := by
  have hrV : φc l (W - zc l c * W') * W' = (W - zc l c * W') * φc l W' := by
    rw [map_sub, map_mul, phi_zc]
    linear_combination hr
  by_cases hV0 : W - zc l c * W' = 0
  · refine ⟨c, fun ρ h0 h1 => ?_⟩
    rw [hV0, gC_zero h0 h1]
    exact mul_nonneg (pow_nonneg (rho_pos h0).le _) ((gauss h0 h1).1 _).1
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs _ W' he hV0 hW' hrV
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') = ρ ^ n * gC l ρ W' :=
    fun ρ h0 h1 => gC_eq_of_vr hV0 hW' n hn h0 h1
  have hW0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' _ le_rfl inv_l_lt_one
  have hk : (k : ℤ) ≤ n := by
    have a := hc _ le_rfl inv_l_lt_one
    rw [hg _ le_rfl inv_l_lt_one] at a
    have b := le_of_mul_le_mul_right a hW0
    rw [← zpow_natCast] at b
    exact (zpow_le_zpow_iff_right_of_lt_one₀ inv_l_pos inv_l_lt_one).1 b
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hkm : k ≤ m := by exact_mod_cast hk
  obtain ⟨u, -, hu⟩ := GlobalTheory.T.gaussNormAcris_sub_unit_le_digit l h s hs (W - zc l c * W') ((l : Formalism.Per.Acris l) ^ m * W')
    (by rw [iter_lpow, he]; ring) (lpow_ne_zero hW' m)
    (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hrV)
    (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
  refine ⟨c + u * (l : ℤ_[l]) ^ m, fun ρ h0 h1 => ?_⟩
  have e : W - zc l (c + u * (l : ℤ_[l]) ^ m) * W' =
      (W - zc l c * W') - zc l u * ((l : Formalism.Per.Acris l) ^ m * W') := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine (hu ρ h0 h1).trans ?_
  rw [gC_lpow h0 h1, ← mul_assoc, ← pow_succ']
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (rho_pos h0).le h1.le (by omega))
    ((gauss h0 h1).1 _).1

theorem eq_zc_mul {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W')
    (hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ W = gC l ρ W') :
    ∃ c : ℤ_[l], W = zc l c * W' := by
  have hmono : ∀ i, digitSet W W' (i + 1) ⊆ digitSet W W' i := fun i c hc ρ h0 h1 =>
    (hc ρ h0 h1).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (rho_pos h0).le h1.le (Nat.le_succ i)) ((gauss h0 h1).1 _).1)
  have hne : ∀ i, (digitSet W W' i).Nonempty := by
    intro i
    induction i with
    | zero => exact ⟨0, fun ρ h0 h1 => by rw [map_zero, zero_mul, sub_zero, pow_zero, one_mul, hg ρ h0 h1]⟩
    | succ i ih =>
      obtain ⟨c, hc⟩ := ih
      exact digit_step hs he hW' hr i c hc
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hmono hne
    (isCompact_univ.of_isClosed_subset (isClosed_digitSet W W' 0) (Set.subset_univ _))
    (isClosed_digitSet W W')
  rw [Set.mem_iInter] at hc
  refine ⟨c, ?_⟩
  by_contra hne'
  have hpos := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l (W - zc l c * W') (sub_ne_zero.2 hne') _ le_rfl inv_l_lt_one
  have hlim : Filter.Tendsto (fun i : ℕ => (l : ℝ)⁻¹ ^ i * gC l (l : ℝ)⁻¹ W') Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one inv_l_pos.le inv_l_lt_one).mul_const
      (gC l (l : ℝ)⁻¹ W')
  have := ge_of_tendsto' hlim (fun i => hc i _ le_rfl inv_l_lt_one)
  linarith

end RatioProp


open RatioProp in
theorem ratio_proportional_target : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w = (l : Formalism.Per.Acris l) ^ s * w → (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ c d : ℤ_[l], c ≠ 0 ∧ zc l c * w = zc l d * w' := by
  intro l _ h s hs w w' _ he' hw' hr
  by_cases hw : w = 0
  · exact ⟨1, 0, one_ne_zero, by rw [hw, mul_zero, map_zero, zero_mul]⟩
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs w w' he' hw hw' hr
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = ρ ^ n * gC l ρ w' :=
    fun ρ h0 h1 => gC_eq_of_vr hw hw' n hn h0 h1
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := w) (W' := (l : Formalism.Per.Acris l) ^ m * w')
      (by rw [iter_lpow, he']; ring) (lpow_ne_zero hw' m)
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
    refine ⟨1, c * (l : ℤ_[l]) ^ m, one_ne_zero, ?_⟩
    rw [map_one, one_mul, hc, map_mul, map_pow, map_natCast]
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -n := ⟨(-n).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := (l : Formalism.Per.Acris l) ^ m * w) (W' := w') he' hw'
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by
        rw [gC_lpow h0 h1, hg ρ h0 h1, ← mul_assoc, ← zpow_natCast, hm,
          ← zpow_add₀ (ne_of_gt (rho_pos h0)), neg_add_cancel, zpow_zero, one_mul])
    refine ⟨(l : ℤ_[l]) ^ m, c, pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), ?_⟩
    rw [map_pow, map_natCast, hc]

end GlobalTheory.PMon.Gauss
end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEulLocal

theorem wtS_eq_sum (n : ℕ) (a : Fin n → ℤ) :
    GlobalTheory.CellDec.wtS n a = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * a i := by
  apply GlobalTheory.WeightSumSplit.wtS_eq <;> assumption


open GlobalTheory.JSW in
theorem localTerm_eq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  intro q hq n α β x v h0 hv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (fun i => (v i).toNat) := fun i j hij => Int.toNat_le_toNat (hv hij)
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℝ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
    simp
  set cR : ℝ := ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℕ)) * (v i : ℝ) with hcR
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (((v i).toNat : ℕ) : ℂ))) = (cR : ℂ) := by
    rw [hcR]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcast i, Complex.ofReal_intCast]
  set A : ℝ := (q : ℝ) ^ (-cR / 2) with hA'
  have hA : (q : ℂ) ^ (-(cR : ℂ) / 2) = (A : ℂ) := by
    rw [hA', Complex.ofReal_cpow hqR.le]
    push_cast
    rfl
  have hW : (GlobalTheory.CellDec.wtS n v : ℝ) = cR := by
    rw [GlobalTheory.ZEulLocal.wtS_eq_sum, hcR]
    push_cast
    rfl
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) = 1 := by
    rw [hA', ← Real.rpow_add hqR, ← Real.rpow_intCast, ← Real.rpow_add hqR, hW]
    rw [show cR + (-cR / 2 + -cR / 2) = 0 by ring, Real.rpow_zero]
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW, sphW, if_pos hl, if_pos hl, hc, hA, GlobalTheory.ZEul.rsTerm, if_pos ⟨h0, hv⟩, key2, map_mul,
    Complex.conj_ofReal]
  calc _ = (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) : ℝ) : ℂ) *
        (schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
          ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)) := by push_cast; ring
    _ = _ := by rw [key]; simp

end GlobalTheory.ZEulLocal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CharLabTransport

theorem teich_inv {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (c : (ZMod g)ˣ) :
    L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((c⁻¹ : (ZMod g)ˣ) : ZMod g)) =
      (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (c : ZMod g)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem charLab_of_value {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ)
    (t : (ZMod g)ˣ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = ((θ u : ℂˣ) : ℂ) ∨
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = (((θ u)⁻¹ : ℂˣ) : ℂ)) :
    ∃ c : ZMod g, GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp θ) c ∧
      (c = (t : ZMod g) ∨ c = ((t⁻¹ : (ZMod g)ˣ) : ZMod g)) := by
  by_cases hex : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1
  · obtain ⟨u₀, hu₀⟩ := hex
    have huniq : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 → u = u₀ := by
      intro u hu
      apply Units.ext
      exact (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hu.trans hu₀.symm)
    rcases hε with rfl | rfl <;> rcases h u₀ hu₀ with hv | hv
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
  · exact ⟨_, ⟨t.ne_zero, fun u hu => (hex ⟨u, hu⟩).elim⟩, Or.inl rfl⟩

theorem charLab_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hg k v i PP hdiv iso ε hε
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, -, hser, hchi⟩ := hg k
  refine ⟨L, hser, ?_⟩
  apply charLab_of_value L _ _ ε hε
  intro u hu
  have h1 : (((u : ZMod (D.host.g k)).val : ℕ) : ZMod (D.host.g k)) = u := ZMod.natCast_zmod_val _
  refine hchi v i PP hdiv (u : ZMod (D.host.g k)).val
    (Units.map (iso : ZMod (D.host.g k) →* kP PP) u) ?_ ?_
  · rw [← hu, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), h1]
  · rw [← map_natCast iso, h1]; rfl

end GlobalTheory.CharLabTransport
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.LowerHarm

open MvPolynomial

theorem deg_pderiv_succ {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (k : ℕ) (h : f.totalDegree ≤ k + 1) :
    (pderiv i f).totalDegree ≤ k := by
  classical

  rw [f.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega
    have e2 := congrArg Finsupp.degree e
    rw [map_add (f := _), Finsupp.degree_single] at e2
    have h3 := (le_totalDegree hs).trans h
    change s.degree ≤ k + 1 at h3
    change (s - Finsupp.single i 1).degree ≤ k
    omega

theorem pderiv_of_deg_zero {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (h : f.totalDegree ≤ 0) : pderiv i f = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 h), pderiv_C]

theorem fockT_lower {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = - ∑ j : Fin n, pderiv (τ, i, j) (pderiv (τ, l, j) P) := by
  classical
  have hil : i ≠ l := by intro h; subst h; omega
  have h1 : decide ((i : ℕ) < p τ) = false := decide_eq_false (by omega)
  have h2 : decide ((l : ℕ) < p τ) = true := decide_eq_true hl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, h1, h2, hil, LinearMap.sum_apply]
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem lower_deg {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (k : ℕ) (h : P.totalDegree ≤ k + 2) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P).totalDegree ≤ k := by
  rw [fockT_lower τ p i l hi hl, totalDegree_neg]
  exact totalDegree_finsetSum_le fun j _ => deg_pderiv_succ _ _ _ (deg_pderiv_succ _ _ (k + 1) h)

theorem lower_zero {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (h : P.totalDegree ≤ 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = 0 := by
  rw [fockT_lower τ p i l hi hl]
  simp [pderiv_of_deg_zero _ _ (deg_pderiv_succ _ _ 0 h)]

theorem lower_to_harmonic : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (M : Submodule ℂ (W →ₗ[ℂ] PolF D m n)), (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (i l : Fin m), p τ ≤ (i : ℕ) → (l : ℕ) < p τ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0 := by
  intro D n m p W _ _ _ M hM hne
  classical
  have hex : ∃ d, ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w, (ψ w).totalDegree ≤ d := by
    obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let b := Module.finBasis ℂ W
    refine ⟨Finset.univ.sup fun j => (ψ (b j)).totalDegree, ψ, hψ, hψ0, fun w => ?_⟩

    rw [← b.sum_repr w, map_sum]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rw [map_smul]
    exact (totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun j => (ψ (b j)).totalDegree) (Finset.mem_univ j))
  obtain ⟨ψ, hψ, hψ0, hdeg⟩ := Nat.find_spec hex
  refine ⟨ψ, hψ, hψ0, fun w τ i l hi hl => ?_⟩
  by_contra hne'
  have hL := hM ψ hψ τ i l hi hl
  have hL0 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ≠ 0 := fun h => hne' (by simpa using LinearMap.congr_fun h w)
  rcases Nat.lt_or_ge (Nat.find hex) 2 with h2 | h2
  · exact hne' (lower_zero τ p i l hi hl _ (by have := hdeg w; omega))
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 2 := ⟨Nat.find hex - 2, by omega⟩
    have := Nat.find_min' hex ⟨_, hL, hL0, fun w' => lower_deg τ p i l hi hl _ k (hk ▸ hdeg w')⟩
    omega

end GlobalTheory.LowerHarm
end
end
