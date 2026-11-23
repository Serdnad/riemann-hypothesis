module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle039
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
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.CoeffMulMem
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.DecTransport

open Matrix Finset
open scoped InnerProductSpace
open Formalism.QuantumDeterminants (UH Hpk IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open GlobalTheory.Count (dOp rkR)
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp dimV DecGap DecKFin DecSmooth)

lemma hs_le_op {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, Complex.normSq (x i j) ≤ n * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := by
  rw [Finset.sum_comm]
  have h : ∀ j, ∑ i, Complex.normSq (x i j) ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := by
    intro j
    have h1 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x).le_opNorm (EuclideanSpace.single j (1 : ℂ))
    rw [PiLp.norm_single, norm_one, mul_one] at h1
    refine le_trans (le_of_eq ?_) (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]
    congr 2
    have := GlobalTheory.Dec.stdRep_apply x (EuclideanSpace.single j (1 : ℂ)) i
    simp only [GlobalTheory.Dec.stdRep] at this
    rw [this]
    simp
  calc _ ≤ ∑ _j : Fin n, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ ^ 2 := Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp

lemma op_conj {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (P * x * star P)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) x‖ := by
  have hu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P ∈ unitary _ := by
    rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, Unitary.star_mul_self_of_mem hP,
      Unitary.mul_star_self_of_mem hP, map_one]
    exact ⟨rfl, rfl⟩
  rw [map_mul, map_mul, map_star, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hu),
    CStarRing.norm_mem_unitary_mul _ hu]

lemma rkR_eq {k r : ℕ} (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) : rkR ε = r + 1 := by
  have h1 := (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff k r ε).1 ⟨P, hP⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * r + k + 1))))
    (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h2
  unfold rkR
  omega

lemma exp_le_rpow {a b c N G : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c) (hN : 0 ≤ Real.log N) (hG : 0 < G)
    (hGN : G ≤ c * N) : Real.exp (-b * Real.log N) ≤ c ^ a * G ^ (-a) := by
  have hN0 : 0 < N := by
    by_contra h
    nlinarith [mul_nonneg hc.le (neg_nonneg.2 (not_lt.1 h))]
  have hl := Real.log_le_log hG hGN
  rw [Real.log_mul hc.ne' hN0.ne'] at hl
  rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hG, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left hl ha, mul_le_mul_of_nonneg_right hab hN]

lemma gN_pos {k r : ℕ} {x : Mat k r} (hx : x ∈ UH (Hpk k r)) : 0 < gN x := by
  refine lt_of_le_of_ne (Real.sqrt_nonneg _) fun h => ?_
  have h0 : ∑ i, ∑ j, Complex.normSq (x i j) = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).1 h.symm
  have hx0 : x = 0 := by
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (x i j)).1 h0 i (mem_univ _)
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (x i j)).1 h1 j (mem_univ _))
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 : xᴴ * Hpk k r * x = Hpk k r := hx
  rw [hx0, Matrix.mul_zero] at h3
  rw [← h3, Matrix.mul_zero] at h2
  exact zero_ne_one h2

end GlobalTheory.DecTransport
end
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.DiscRoot

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_span_pow (p x : ball K) (n : ℕ) :
    x ∈ Ideal.span {p} ^ n ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : ‖(a : K)‖ ≤ 1 := a.2
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ha
  · intro h
    by_cases hp : (p : K) ^ n = 0
    · rw [← norm_pow, hp, norm_zero, norm_le_zero_iff] at h
      exact ⟨0, Subtype.ext (by simp [h])⟩
    · refine ⟨⟨x / p ^ n, ?_⟩, Subtype.ext ?_⟩
      · change ‖(x : K) / p ^ n‖ ≤ 1
        rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ h (by positivity)
      · simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
        exact div_mul_cancel₀ _ hp

theorem smod_iff (p x y : ball K) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule (ball K) (ball K))] ↔
      ‖(x : K) - y‖ ≤ ‖(p : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow]
  rfl

theorem adicComplete [CompleteSpace K] (p : ball K) (hp : ‖(p : K)‖ < 1) :
    IsAdicComplete (Ideal.span {p}) (ball K) := by
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : K)‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp
  have hH : IsHausdorff (Ideal.span {p}) (ball K) := ⟨fun x hx => by
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      simpa using (smod_iff p x 0 n).1 (hx n)
    exact Subtype.ext (by simpa using this)⟩
  have hP : IsPrecomplete (Ideal.span {p}) (ball K) := ⟨fun f hf => by
    have hc : CauchySeq fun n => (f n : K) := by
      refine cauchySeq_of_le_tendsto_0' (fun n => ‖(p : K)‖ ^ n) (fun n m hnm => ?_) ht
      rw [dist_eq_norm]
      exact (smod_iff p _ _ n).1 (hf hnm)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => (f n).2
    refine ⟨⟨L, hL1⟩, fun n => (smod_iff p _ _ n).2 ?_⟩
    refine le_of_tendsto ((tendsto_const_nhds (x := (f n : K))).sub hL).norm ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact (smod_iff p _ _ n).1 (hf hm)⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem division [CompleteSpace K] (h : PowerSeries K) (d : ℕ) (hd : 0 < d)
    (hi : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff d h‖ = 1)
    (hl : ∀ k < d, ‖PowerSeries.coeff k h‖ < 1) :
    ∃ (q : PowerSeries K) (r : Polynomial K), (∀ n, ‖PowerSeries.coeff n q‖ ≤ 1) ∧
      ‖PowerSeries.coeff 0 q‖ = 1 ∧ r.degree < d ∧ (∀ n, ‖r.coeff n‖ < 1) ∧
      PowerSeries.X ^ d = h * q + (r : PowerSeries K) := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range d)
    (fun k => ‖PowerSeries.coeff k h‖) ⟨0, Finset.mem_range.2 hd⟩
  let g : PowerSeries (ball K) := PowerSeries.mk fun n => ⟨PowerSeries.coeff n h, hi n⟩
  have hg : ∀ n, ((PowerSeries.coeff n g : ball K) : K) = PowerSeries.coeff n h := fun n => by
    simp [g]
  let p : ball K := PowerSeries.coeff k g
  have hp : ‖(p : K)‖ < 1 := by rw [hg]; exact hl k (Finset.mem_range.1 hk)
  set I : Ideal (ball K) := Ideal.span {p} with hI
  have hmem : ∀ x : ball K, x ∈ I ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ := fun x => by
    simpa using mem_span_pow p x 1
  have hlow : ∀ j < d, PowerSeries.coeff j g ∈ I := fun j hj => by
    rw [hmem, hg, hg]; exact hmax j (Finset.mem_range.2 hj)
  have hord : (g.map (Ideal.Quotient.mk I)).order = d := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem, hmem, hg, h1]
      exact not_le.2 hp
    · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
      exact hlow i hi
  have hord' : (g.map (Ideal.Quotient.mk I)).order.toNat = d := by rw [hord]; rfl
  have H : g.IsWeierstrassDivisorAt I := by
    rw [PowerSeries.IsWeierstrassDivisorAt, hord']
    have h0 : PowerSeries.coeff d h ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff d h)⁻¹, ?_⟩ (Subtype.ext ?_)
    · change ‖(PowerSeries.coeff d h)⁻¹‖ ≤ 1
      rw [norm_inv, h1, inv_one]
    · rw [Subring.coe_mul, hg]
      exact mul_inv_cancel₀ h0
  haveI := adicComplete p hp
  have HD := H.isWeierstrassDivisionAt_div_mod (PowerSeries.X ^ d)
  set q := H.div (PowerSeries.X ^ d)
  set r := H.mod (PowerSeries.X ^ d)
  have hdeg : r.degree < d := hord' ▸ HD.degree_lt
  have hgh : g.map (ball K).subtype = h := by
    ext n; simp [hg]
  refine ⟨q.map (ball K).subtype, r.map (ball K).subtype, fun n => ?_, ?_,
    lt_of_le_of_lt (Polynomial.degree_map_le) hdeg, fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff n q).2
  · have e := congrArg (PowerSeries.coeff d) HD.eq_mul_add
    rw [g.eq_X_pow_mul_shift_add_trunc d, add_mul, mul_assoc, map_add (f := _), map_add (f := _),
      PowerSeries.coeff_X_pow_self, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_degree_lt hdeg, add_zero, PowerSeries.coeff_X_pow_mul',
      if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_mul] at e
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at e
    have e2 : PowerSeries.coeff d (((g.trunc d : Polynomial (ball K)) : PowerSeries (ball K)) * q) ∈ I := by
      refine PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) d
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hh
      · exact hlow i hh
      · exact zero_mem _
    have e3 := ((hmem _).1 e2).trans_lt hp
    have e4 := congrArg (fun z : ball K => (z : K)) e
    simp only [PowerSeries.coeff_mk, zero_add, Subring.coe_add, Subring.coe_mul, hg, OneMemClass.coe_one] at e4
    rw [PowerSeries.coeff_map]
    refine le_antisymm (PowerSeries.coeff 0 q).2 (not_lt.1 fun hlt => ?_)
    have e5 := congrArg norm e4
    rw [norm_one] at e5
    refine absurd (e5.le.trans (IsUltrametricDist.norm_add_le_max _ _)) (not_le.2 (max_lt ?_ e3))
    rw [norm_mul, h1, one_mul]
    exact hlt
  · rw [Polynomial.coeff_map]
    by_cases hn : n < d
    · have := HD.coeff_f_sub_r_mem (i := n) (hord'.symm ▸ hn)
      rw [map_sub, PowerSeries.coeff_X_pow, if_neg hn.ne, zero_sub, neg_mem_iff,
        Polynomial.coeff_coe] at this
      exact ((hmem _).1 this).trans_lt hp
    · rw [Polynomial.coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast not_lt.1 hn))]
      simp
  · have := congrArg (PowerSeries.map (ball K).subtype) HD.eq_mul_add
    rw [map_pow, PowerSeries.map_X, map_add (f := _), map_mul, hgh] at this
    rw [this, Polynomial.polynomial_map_coe]

theorem root_small [IsAlgClosed K] (r : Polynomial K) (d : ℕ) (hd : 0 < d) (hr : r.degree < d)
    (hc : ∀ n, ‖r.coeff n‖ < 1) : ∃ x : K, ‖x‖ < 1 ∧ (Polynomial.X ^ d - r).eval x = 0 := by
  have hdeg : (Polynomial.X ^ d - r).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.X ^ d - r)
    (by rw [hdeg]; exact_mod_cast hd.ne')
  refine ⟨x, not_le.1 fun h1 => ?_, hx⟩
  have e : x ^ d = ∑ i ∈ Finset.range d, r.coeff i * x ^ i := by
    have := hx.eq_zero
    rw [Polynomial.eval_sub, sub_eq_zero, Polynomial.eval_pow, Polynomial.eval_X] at this
    rw [this]
    by_cases h0 : r = 0
    · simp [h0]
    exact Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt h0).2 hr) x
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := Finset.range d) ⟨0, Finset.mem_range.2 hd⟩ (fun i => r.coeff i * x ^ i)
  rw [← e, norm_mul, norm_pow, norm_pow] at hle
  have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ d := pow_le_pow_right₀ h1 (Finset.mem_range.1 hi).le
  have h3 : 0 < ‖x‖ ^ i := by positivity
  have h4 := hc i
  nlinarith

end GlobalTheory.ConvSer.DiscRoot

theorem GlobalTheory.ConvSer.exists_root_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  intro K _ _ _ _ h d hd hi h1 hl
  obtain ⟨-, -, hA, -, -, -, -, -, -, hB⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨q, r, hq, hq0, hr, hrc, e⟩ := DiscRoot.division h d hd ((hB h).1.1 hi) h1 hl
  obtain ⟨x, hx, hx0⟩ := DiscRoot.root_small r d hd hr hrc
  refine ⟨x, hx, ?_⟩
  obtain ⟨-, hmul, -, -, hP, -, hI, -⟩ := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hq' : Intg q := (hB q).1.2 hq
  have e2 : ((Polynomial.X ^ d - r : Polynomial K) : PowerSeries K) = h * q := by
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, e]; ring
  have e3 := (hP (Polynomial.X ^ d - r)).2
  rw [hx0, e2, (hmul h q ((hA h 0).2.2 hi) ((hA q 0).2.2 hq')).2.2] at e3
  refine (mul_eq_zero.1 e3).resolve_right fun h0 => ?_
  have := (hI q hq').2.1
  rw [h0, zero_sub, norm_neg, hq0] at this
  exact absurd hx (not_lt.2 this)
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

private theorem intg_of_norm_coeff_le_one {K : Type} [NormedField K] (f : PowerSeries K)
    (h : ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) : Intg f := by
  intro ν
  have h1 := h (ν ())
  have h2 : ν = Finsupp.single () (ν ()) := Finsupp.unique_single ν
  rw [h2]
  exact h1

theorem integralPowerSeries_eq_zero_of_vanish_on_points (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : ℕ → Finset K) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hG : ∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1)
    (hT : Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0))
    (h : PowerSeries K) (hh : Intg h) (m : ℕ)
    (hz : ∀ n, m ≤ n → ∀ x ∈ G n, ev1 h x = 0) : h = 0 := by
  ext k
  have key : ‖PowerSeries.coeff k h‖ * r ^ k ≤ 0 := by
    refine ge_of_tendsto hT ?_
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    exact (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K h (G n) hh (fun x hx => ⟨(hG n x hx).2, hz n hn x hx⟩)).1 r hr hr1
      (fun x hx => (hG n x hx).1) k
  have hp : 0 < r ^ k := pow_pos hr k
  have h0 : ‖PowerSeries.coeff k h‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hc hp
    linarith
  simpa using norm_le_zero_iff.mp h0

theorem eq_zero_of_ev_vanish : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  intro K _ _ _ G r hr hr1 hmono hG hT H hH hz
  have hS : ∀ (x y : K), ‖x‖ < 1 → ‖y‖ < 1 →
      Intg (shift1 H y) ∧ ev1 (shift1 H y) x = ev H ![x, y] := fun x y hx hy =>
    (GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx).2.2.2.2.2.2.2.2.2.1 H y hy hH
  have h1 : ∀ m, ∀ y ∈ G m, shift1 H y = 0 := by
    intro m y hy
    have hy1 := (hG m y hy).2
    refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (hS 0 y (by simp) hy1).1 m ?_
    intro n hn x hx
    rw [(hS x y (hG n x hx).2 hy1).2]
    exact hz n x hx y (hmono hn hy)
  have h2 : ∀ a b : ℕ,
      MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) H = 0 := by
    intro a b
    have h3 : (PowerSeries.mk fun b : ℕ =>
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) H) = 0 := by
      refine integralPowerSeries_eq_zero_of_vanish_on_points K G r hr hr1 hG hT _ (intg_of_norm_coeff_le_one _ ?_) 0 ?_
      · intro n
        rw [PowerSeries.coeff_mk]
        exact hH _
      · intro n _ y hy
        have h4 := congrArg (PowerSeries.coeff a) (h1 n y hy)
        rw [shift1, PowerSeries.coeff_mk, map_zero] at h4
        simpa [ev1, PowerSeries.coeff_mk] using h4
    have h5 := congrArg (PowerSeries.coeff b) h3
    rwa [PowerSeries.coeff_mk, map_zero] at h5
  ext ν
  have hν : ν = Finsupp.single 0 (ν 0) + Finsupp.single 1 (ν 1) := by
    ext i
    fin_cases i <;> simp
  rw [hν, h2]
  simp

end GlobalTheory.ConvSer
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_for_point {K : Type} [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  induction n with
  | zero =>
    rw [nMul_zero]
    exact GlobalTheory.BddAlg.intg_zero
  | succ n ih =>
    rw [nMul_succ]
    have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1
    refine GlobalTheory.BddAlg.Le.subst (c := 1) (fun j => ?_) (fun j => ?_) hF
    · fin_cases j
      · exact ih
      · exact hX
    · fin_cases j
      · exact nMul_constantCoeff F n
      · exact PowerSeries.constantCoeff_X

private lemma ev1_zero {K : Type} [NormedField K] (y : K) : ev1 (0 : PowerSeries K) y = 0 := by
  simp [ev1]

theorem nMul_point : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  intro K _ _ _ F hF
  have hI : ∀ n, Intg (nMul F n) := intg_nMul_for_point F hF
  have hB : Bdd F.toPowerSeries := GlobalTheory.BddAlg.bdd_of_intg hF
  have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1

  have hleft : MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_succ F 0
    rw [nMul_zero, nMul_one] at h
    exact h.symm
  have hright : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_add F 1 0
    rw [nMul_zero, nMul_one] at h
    simpa using h
  refine ⟨hI, fun x hx => ?_⟩
  obtain ⟨-, -, -, hevX, -, -, hnorm, hsub, hpair, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  refine ⟨by rw [nMul_zero]; exact ev1_zero x, by rw [nMul_one]; exact hevX, fun j => ?_,
    fun i j => ?_, fun i j => ?_, fun y hy => ?_⟩
  · obtain ⟨-, h1, h2⟩ := hnorm (nMul F j) (hI j)
    have h0 : PowerSeries.coeff 0 (nMul F j) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact nMul_constantCoeff F j
    rw [h0, sub_zero] at h1 h2
    rw [nMul_coeff_one] at h2
    refine ⟨h1, fun hj => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using h1
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hsq : ‖x‖ ^ 2 < ‖x‖ := by nlinarith
      have hjx : ‖(j : K) * x‖ = ‖x‖ := by rw [norm_mul, hj, one_mul]
      set v := ev1 (nMul F j) x
      have hlt : ‖v - (j : K) * x‖ < ‖(j : K) * x‖ := by rw [hjx]; exact lt_of_le_of_lt h2 hsq
      have hdecomp : v = (j : K) * x + (v - (j : K) * x) := by ring
      rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
        max_eq_left hlt.le, hjx]
  · rw [← hpair F.toPowerSeries (nMul F i) (nMul F j) hB (hI i) (hI j)
      (nMul_constantCoeff F i) (nMul_constantCoeff F j), nMul_add]
  · rw [← hsub (nMul F i) (nMul F j) (hI j) (nMul_constantCoeff F j)
      (GlobalTheory.BddAlg.bdd_of_intg (hI i)), nMul_subst_nMul]
  · obtain ⟨-, -, -, hevXy, -, -, -, -, hpairy, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K y hy
    have hz : Intg (0 : PowerSeries K) := GlobalTheory.BddAlg.intg_zero
    have hc0 : PowerSeries.constantCoeff (0 : PowerSeries K) = 0 := by simp
    have hcX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
    constructor
    · have h := hpairy F.toPowerSeries 0 PowerSeries.X hB hz hX hc0 hcX
      rw [hleft, hevXy, ev1_zero] at h
      exact h.symm
    · have h := hpairy F.toPowerSeries PowerSeries.X 0 hB hX hz hcX hc0
      rw [hright, hevXy, ev1_zero] at h
      exact h.symm

end GlobalTheory.ConvSer
end
