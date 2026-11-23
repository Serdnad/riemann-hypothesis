module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle013
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Aesop.Main
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open Set

namespace GlobalTheory.ZetaPartialSum
open GlobalTheory.ZetaHalfPlane

noncomputable def tailInt (s : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi a, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

lemma norm_tailInt_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖tailInt s a‖ ≤ a ^ (-s.re) / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖tailInt s a‖ ≤ ∫ t in Ioi a, t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h ha) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun t ht => ?_
        have ht0 : 0 < t := lt_trans ha ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)
    _ = a ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt h ha,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]

lemma piece {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    s * ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = (M : ℂ) ^ (1 - s) / (s - 1) - ((M : ℂ) + 1) ^ (1 - s) / (s - 1)
        - ((M : ℂ) + 1) ^ (-s) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hle : (M : ℝ) ≤ M + 1 := by linarith
  have hmem : (0 : ℝ) ∉ uIcc (M : ℝ) (M + 1) := by
    rw [uIcc_of_le hle]
    intro h
    linarith [h.1]
  have e : ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = ∫ t in (M : ℝ)..(M + 1), ((t : ℂ) ^ (-s) - (M : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := lt_trans hM0 ht.1
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    have e1 : (t : ℂ) ^ (-s) = t * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = 1 + -(s + 1) by ring, cpow_add _ _ htc, cpow_one]
    have e2 : ⌊t⌋ = (M : ℤ) := by
      rw [Int.floor_eq_iff]
      exact ⟨by simpa using ht.1.le, by simpa using ht.2⟩
    have e3 : Int.fract t = t - M := by
      rw [Int.fract, e2]; simp
    rw [e1, e3]
    push_cast
    ring
  have i1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have i2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have n1 : -s ≠ -1 := fun h => hs1 (neg_injective h)
  have n2 : -(s + 1) ≠ -1 := fun h => hs0 (by linear_combination -h)
  rw [e, intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨n1, hmem⟩), integral_cpow (Or.inr ⟨n2, hmem⟩)]
  push_cast
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hMc1 : (M : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
  have a1 : (M : ℂ) ^ (1 - s) = M * (M : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc, cpow_one]
  have a2 : ((M : ℂ) + 1) ^ (1 - s) = (M + 1) * ((M : ℂ) + 1) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc1, cpow_one]
  rw [show -s + 1 = 1 - s by ring, show -(s + 1) + 1 = -s by ring, a1, a2]
  have hs1'' : 1 - s ≠ 0 := sub_ne_zero.2 hs1.symm
  field_simp
  ring

theorem zeta_eq_sum {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) + (M : ℂ) ^ (1 - s) / (s - 1)
      - s * tailInt s M := by
  induction M, hM using Nat.le_induction with
  | base =>
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    rw [zeta_eq hs hs1]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow, tailInt, fractInt]
    field_simp
    ring
  | succ M hM ih =>
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hle : (M : ℝ) ≤ M + 1 := by linarith
    have hsplit : tailInt s M
        = (∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
          + tailInt s ((M : ℝ) + 1) := by
      unfold tailInt
      rw [← Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
      · exact (integrableOn_integrand hs).mono_set fun t ht => lt_of_le_of_lt hM1 ht.1
      · exact (integrableOn_integrand hs).mono_set fun t ht =>
          lt_of_le_of_lt (hM1.trans hle) ht
    rw [ih, Finset.sum_Icc_succ_top (by omega), hsplit, mul_add, piece hs hs1 hM]
    push_cast
    ring

theorem norm_zeta_sub_sum_le :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M →
      ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖
        ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  intro s hs hs1 M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have e : riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)
      = -(s * tailInt s M) := by
    rw [zeta_eq_sum hs hs1 hM]; ring
  rw [e, norm_neg, norm_mul, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_tailInt_le hs hM0) (norm_nonneg s)

end GlobalTheory.ZetaPartialSum
end

section

open Complex

noncomputable section

namespace GlobalTheory.SgStarOddTheta

open Formalism.L2.Th1.F

theorem jacobiTheta₂_add_int_lattice (z τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ (z + (m * τ + k)) τ =
      cexp (-(Real.pi : ℂ) * I * (m ^ 2 * τ + 2 * m * z)) * jacobiTheta₂ z τ := by
  rw [jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩
  simp only [Equiv.coe_addRight]
  push_cast
  ring

theorem oddTheta_add (τ : UpperHalfPlane) (z : ℂ) (m k : ℤ) :
    GlobalTheory.ThetaWeberRoad.oddTheta τ (z + (m * (τ : ℂ) + k)) =
      cexp ((Real.pi : ℂ) * I * (k - m - m ^ 2 * (τ : ℂ) - 2 * m * z)) *
        GlobalTheory.ThetaWeberRoad.oddTheta τ z := by
  unfold GlobalTheory.ThetaWeberRoad.oddTheta
  rw [show z + (m * (τ : ℂ) + k) + ((τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) + (m * (τ : ℂ) + k) by ring,
    jacobiTheta₂_add_int_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

theorem exp_pi_I_int (j : ℤ) : cexp ((Real.pi : ℂ) * I * j) = if Even j then 1 else -1 := by
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h).neg_one_zpow

theorem area_periodPairOfTau (τ : UpperHalfPlane) : area (GlobalTheory.periodPairOfTau τ) = τ.im := by
  simp [area, GlobalTheory.periodPairOfTau, abs_of_pos τ.im_pos]

theorem semiChar_periodPairOfTau (τ : UpperHalfPlane) (m k : ℤ) :
    semiChar (GlobalTheory.periodPairOfTau τ) (m * (τ : ℂ) + k) =
      cexp ((Real.pi : ℂ) * I * ((k - m + m * k : ℤ) : ℂ)) := by
  have hpar : Even (k - m + m * k) ↔ Even m ∧ Even k := by
    simp only [parity_simps]; tauto
  have hmem : (m * (τ : ℂ) + k) / 2 ∈ (GlobalTheory.periodPairOfTau τ).lattice ↔ Even m ∧ Even k := by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    constructor
    · rintro ⟨p, q, e⟩
      have e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ) := by
        push_cast
        linear_combination -2 * e
      have h1 := congrArg Complex.im e1
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1
      rw [h1, add_right_inj, Int.cast_inj] at e1
      exact ⟨⟨p, h1⟩, ⟨q, e1⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
      exact ⟨p, q, by push_cast; ring⟩
  rw [exp_pi_I_int, semiChar]
  by_cases h : Even m ∧ Even k
  · rw [if_pos (hmem.2 h), if_pos (hpar.2 h)]
  · rw [if_neg (fun h' => h (hmem.1 h')), if_neg (fun h' => h (hpar.1 h'))]

def expOddTheta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z

theorem differentiable_expOddTheta (τ : UpperHalfPlane) : Differentiable ℂ (expOddTheta τ) := by
  have := GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ
  unfold expOddTheta
  fun_prop

theorem expOddTheta_law (τ : UpperHalfPlane) : ∀ ω ∈ (GlobalTheory.periodPairOfTau τ).lattice, ∀ z,
    semiChar (GlobalTheory.periodPairOfTau τ) ω * opU (GlobalTheory.periodPairOfTau τ) ω (expOddTheta τ) z =
      expOddTheta τ z := by
  intro ω hω z
  obtain ⟨m, k, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ ω).1 hω
  simp only [one_mul]
  rw [semiChar_periodPairOfTau, opU, herm, herm, area_periodPairOfTau, expOddTheta, expOddTheta,
    oddTheta_add]
  have hE : ∀ A B C D w : ℂ, cexp A * (cexp B * (cexp C * w) * cexp D) = cexp (A + B + C + D) * w := by
    intros
    simp only [Complex.exp_add]
    ring
  rw [hE]
  congr 1
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨k - m + m * k, ?_⟩
  have hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * I := by
    apply Complex.ext <;> simp
    ring
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  simp only [map_add (f := _), map_mul, map_intCast, hc]
  field_simp
  push_cast
  ring

theorem exp_mul_oddTheta_eq_deriv_mul_sgStar :
    Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ),
      Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by
  intro hTL hSB τ z
  obtain ⟨c, hc⟩ := hTL _ (expOddTheta τ) (differentiable_expOddTheta τ) (expOddTheta_law τ)
  have hfun : expOddTheta τ = fun z => c * sgStar (GlobalTheory.periodPairOfTau τ) z := funext hc
  obtain ⟨hdiff, -, -, hd1, -⟩ := hSB (GlobalTheory.periodPairOfTau τ)
  have h1 : deriv (expOddTheta τ) 0 = c := by
    rw [hfun]
    have := ((hdiff 0).hasDerivAt.const_mul c).deriv
    rw [hd1, mul_one] at this
    exact this
  have he : HasDerivAt (fun z : ℂ => cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ)))) 0 0 := by
    have := (((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const
      (2 * ((τ.im : ℝ) : ℂ))).cexp
    simpa using this
  have h2 : deriv (expOddTheta τ) 0 = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 := by
    have := (he.mul (GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ 0).hasDerivAt).deriv
    simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div, Complex.exp_zero, one_mul] at this
    exact this
  have := hc z
  rw [expOddTheta] at this
  rw [this, ← h1, h2]

end GlobalTheory.SgStarOddTheta
end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem eq_zero_of_setIntegral_compact_eq_zero {K : Type} [MetricSpace K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] {B : Set K} (hB : IsOpen B) {h : K → ℂ} (hc : ContinuousOn h B)
    (hz : ∀ S : Set K, IsCompact S → S ⊆ B → ∫ b in S, h b ∂ν = 0) {t : K} (ht : t ∈ B) :
    h t = 0 := by
  by_contra hne
  have hpos : 0 < ‖h t‖ := norm_pos_iff.2 hne
  have hca : ContinuousAt h t := hc.continuousAt (hB.mem_nhds ht)
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hca (‖h t‖ / 2) (half_pos hpos)
  obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.1 hB t ht
  have hρ0 : 0 < min (ε / 2) (δ / 2) := lt_min (half_pos hε) (half_pos hδ)
  have hmemS : ∀ b ∈ Metric.closedBall t (min (ε / 2) (δ / 2)), dist b t < ε ∧ dist b t < δ := by
    intro b hb
    have hb' := Metric.mem_closedBall.1 hb
    constructor
    · linarith [min_le_left (ε / 2) (δ / 2)]
    · linarith [min_le_right (ε / 2) (δ / 2)]
  have hSc := isCompact_closedBall t (min (ε / 2) (δ / 2))
  have hSB : Metric.closedBall t (min (ε / 2) (δ / 2)) ⊆ B := fun b hb =>
    hδB (Metric.mem_ball.2 (hmemS b hb).2)
  have hνS : 0 < ν (Metric.closedBall t (min (ε / 2) (δ / 2))) :=
    Metric.measure_closedBall_pos ν t hρ0
  have hνSf : ν (Metric.closedBall t (min (ε / 2) (δ / 2))) < ⊤ := hSc.measure_lt_top
  have hIh : IntegrableOn h (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    (hc.mono hSB).integrableOn_compact hSc
  have hIc : IntegrableOn (fun _ => h t) (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    integrableOn_const hνSf.ne
  have key := integral_sub hIh hIc
  rw [hz _ hSc hSB, setIntegral_const, zero_sub] at key
  have hbound := norm_setIntegral_le_of_norm_le_const hνSf (f := fun b => h b - h t)
    (C := ‖h t‖ / 2) (fun b hb => by rw [← dist_eq_norm]; exact (hball (hmemS b hb).1).le)
  rw [key, norm_neg, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hbound
  have hreal : 0 < ν.real (Metric.closedBall t (min (ε / 2) (δ / 2))) := by
    rw [measureReal_def]; exact ENNReal.toReal_pos hνS.ne' hνSf.ne
  nlinarith [mul_pos hreal hpos]

theorem contDensityOn_eq_fibre_mass : ∀ (K V : Type) [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → ∀ (fib : K → Measure V), IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib → ∀ (L : Set V), IsCompact L → IsOpen L → ∀ g : K → ℂ, IsContDensityOn μ q id ν {t | t ≠ 0} (L.indicator 1) g → ∀ t : K, t ≠ 0 → g t = (((fib t L).toReal : ℝ) : ℂ) := by
  intro K V _ _ _ _ _ _ _ _ μ ν _ q hq fib hfib L hLc hLo g hg t ht
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  obtain ⟨hgc, hgS⟩ := hg
  have hLm : MeasurableSet L := hLo.measurableSet
  have hBo : IsOpen {t : K | t ≠ 0} := isOpen_ne
  have hφc : Continuous (L.indicator (1 : V → ℝ)) :=
    IsClopen.continuous_indicator ⟨hLc.isClosed, hLo⟩ continuous_const
  have hφs : HasCompactSupport (L.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨hint, hcont⟩ := hf3 _ hφc hφs (Set.subset_univ _)
  have hm_eq : (fun b => ∫ v, L.indicator (1 : V → ℝ) v ∂(fib b)) = fun b => (fib b L).toReal := by
    funext b; rw [integral_indicator_one hLm]; rfl
  have hmc : ContinuousOn (fun b => (fib b L).toReal) {t : K | t ≠ 0} := by
    rw [← hm_eq]; exact hcont
  have hfin : ∀ b ∈ {t : K | t ≠ 0}, fib b L < ⊤ := by
    intro b hb
    have hi := hint b hb
    rw [integrable_indicator_iff hLm] at hi
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 hi).resolve_left (by simp)
  have hmcC : ContinuousOn (fun b => (((fib b L).toReal : ℝ) : ℂ)) {t : K | t ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn hmc
  have key : ∀ S : Set K, IsCompact S → S ⊆ {t : K | t ≠ 0} →
      ∫ b in S, (g b - (((fib b L).toReal : ℝ) : ℂ)) ∂ν = 0 := by
    intro S hS hSB
    have hSm : MeasurableSet S := hS.measurableSet
    rw [integral_sub ((hgc.mono hSB).integrableOn_compact hS)
      ((hmcC.mono hSB).integrableOn_compact hS), sub_eq_zero, ← hgS S hS hSB, Set.image_id]
    have hind : L.indicator (1 : V → ℂ) = L.indicator (fun _ => (1 : ℂ)) := rfl
    rw [hind, integral_indicator_const _ hLm, integral_complex_ofReal, Complex.real_smul, mul_one]
    congr 1
    have haem : AEMeasurable (fun b => fib b L) (ν.restrict S) :=
      ((hmc.mono hSB).aemeasurable hSm).ennreal_ofReal.congr
        ((ae_restrict_mem hSm).mono fun b hb => ENNReal.ofReal_toReal (hfin b (hSB hb)).ne)
    rw [integral_toReal haem ((ae_restrict_mem hSm).mono fun b hb => hfin b (hSB hb)),
      measureReal_def, Measure.restrict_apply hLm]
    congr 1
    have hTm : MeasurableSet (L ∩ q ⁻¹' S) := hLm.inter (hq.measurable hSm)
    have h2 := hf2 ((L ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hTm)
    rw [Measure.restrict_univ, lintegral_indicator_one hTm] at h2
    rw [h2, ← lintegral_indicator hSm]
    refine lintegral_congr fun b => ?_
    rw [lintegral_indicator_one hTm]
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine measure_inter_conull (measure_mono_null (Set.compl_subset_compl.2 ?_) (hf1 b))
      intro v hv
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, id] at hv
      simp only [Set.mem_preimage, hv.1, hb]
    · rw [Set.indicator_of_notMem hb]
      refine measure_mono_null (fun v hv => ?_) (hf1 b)
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        id, Set.mem_univ, and_true]
      intro hqv
      exact hb (hqv ▸ hv.2)
  exact sub_eq_zero.1 (eq_zero_of_setIntegral_compact_eq_zero ν hBo (hgc.sub hmcC) key
    (show t ∈ {t : K | t ≠ 0} from ht))

end GlobalTheory
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem isFibreFamily_univ_of_null_cone (K V : Type) [NormedField K] [IsUltrametricDist K]
    [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (ν : Measure K) (q : V → K) (hq : Continuous q) (h0 : μ {x | q x = 0} = 0)
    (U : Set V) (B : Set K) (fib : K → Measure V) (hU : {x | q x ≠ 0} ⊆ U) (hB : {t | t ≠ 0} ⊆ B)
    (h : IsFibreFamily μ q id U ν B fib) :
    IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have hae : ∀ b, ∀ᵐ x ∂(fib b), q x = b := by
    intro b
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs _ => ?_⟩
  · refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx ⟨hx'.1, trivial⟩
  · have hμ : μ.restrict U = μ := by
      apply Measure.restrict_eq_self_of_ae_mem
      refine measure_mono_null ?_ h0
      intro x hx
      by_contra hx'
      exact hx (hU hx')
    rw [← h2 φ hφ, hμ, Measure.restrict_univ]
  · have key : ∀ b0 : K, b0 ≠ 0 → ∃ D : Set K, D ∈ nhds b0 ∧ b0 ∈ D ∧ D ⊆ B ∧
        (∀ b ∈ D, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) D := by
      intro b0 hb0
      have hr : 0 < ‖b0‖ := norm_pos_iff.mpr hb0
      have hD : IsClopen (Metric.ball b0 ‖b0‖) := IsUltrametricDist.isClopen_ball b0 _
      set D := Metric.ball b0 ‖b0‖ with hDdef
      have hD0 : ∀ t ∈ D, t ≠ 0 := by
        rintro t ht rfl
        simp [hDdef] at ht
      have hE : IsClopen (q ⁻¹' D) := hD.preimage hq
      let ψ : V → ℝ := (q ⁻¹' D).indicator φ
      have hψc : Continuous ψ := hE.continuous_indicator hc
      have hψs : HasCompactSupport ψ := by
        refine hcs.mono ?_
        intro x hx hx'
        apply hx
        simp [ψ, Set.indicator, hx']
      have hψt : tsupport ψ ⊆ U := by
        have : tsupport ψ ⊆ q ⁻¹' D :=
          closure_minimal Set.support_indicator_subset hE.isClosed
        intro x hx
        exact hU (hD0 _ (this hx))
      obtain ⟨hi, hco⟩ := h3 ψ hψc hψs hψt
      have hDB : D ⊆ B := fun t ht => hB (hD0 t ht)
      have heq : ∀ b ∈ D, ψ =ᵐ[fib b] φ := by
        intro b hb
        filter_upwards [hae b] with x hx
        have : x ∈ q ⁻¹' D := by
          show q x ∈ D
          rw [hx]; exact hb
        simp [ψ, Set.indicator_of_mem this]
      refine ⟨D, Metric.ball_mem_nhds _ hr, Metric.mem_ball_self hr, hDB, fun b hb => ?_, ?_⟩
      · exact (integrable_congr (heq b hb)).mp (hi b (hDB hb))
      · refine (hco.mono hDB).congr fun b hb => ?_
        exact (integral_congr_ae (heq b hb)).symm
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨D, -, hbD, -, hi, -⟩ := key b hb
      exact hi b hbD
    · obtain ⟨D, hD, -, -, -, hco⟩ := key b hb
      exact (hco.continuousAt hD).continuousWithinAt

end GlobalTheory
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.additive_char_conductor_exists : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first | exact @GlobalTheory.CharConductor.exists_conductor_exponent | exact GlobalTheory.CharConductor.exists_conductor_exponent | (intros; apply GlobalTheory.CharConductor.exists_conductor_exponent <;> assumption)
end
