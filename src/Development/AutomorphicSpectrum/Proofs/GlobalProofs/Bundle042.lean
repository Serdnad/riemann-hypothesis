module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.OneAddHsInvPowLintegralLtTop
public import Formalism.RealPlaceAnalysis.FinalF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

@[expose] public section

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord

theorem sum_abs_coord_le_mnorm {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hli : LinearIndependent ℝ b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  let L : (Fin d → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun r a c => ∑ i, r i • b i a c
      map_add' := fun r s => by
        funext a c
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t r => by
        funext a c
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hL : ∀ r a c, L r a c = (∑ i, r i • b i) a c := by
    intro r a c
    simp [L, Matrix.sum_apply, Matrix.smul_apply]
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun r hr => ?_
    have hsum : ∑ i, r i • b i = 0 := by
      ext a c
      have h := congrFun (congrFun hr a) c
      rw [hL] at h
      simpa using h
    funext i
    exact Fintype.linearIndependent_iff.mp hli r hsum i
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨(d : ℝ) * K, by positivity, fun r => ?_⟩
  have h1 : ‖r‖ ≤ K * ‖L r‖ := by
    have h := hK.le_mul_dist r 0
    simpa [dist_zero_right] using h
  have hN : 0 ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ‖L r‖ ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun c => ?_
    rw [hL]
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    calc ‖(∑ i, r i • b i) a c‖ ≤ ∑ c', ‖(∑ i, r i • b i) a c'‖ :=
          Finset.single_le_sum (f := fun c' => ‖(∑ i, r i • b i) a c'‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
      _ ≤ ∑ a', ∑ c', ‖(∑ i, r i • b i) a' c'‖ :=
          Finset.single_le_sum (f := fun a' => ∑ c', ‖(∑ i, r i • b i) a' c'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h3 : ∑ i, |r i| ≤ d * ‖r‖ := by
    calc ∑ i, |r i| ≤ ∑ _i : Fin d, ‖r‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm r i
      _ = d * ‖r‖ := by simp
  calc ∑ i, |r i| ≤ d * ‖r‖ := h3
    _ ≤ d * (K * ‖L r‖) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ ≤ d * (K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 K.coe_nonneg) (Nat.cast_nonneg _)
    _ = d * K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

open MeasureTheory

theorem wt_eq_hs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : wt M = Formalism.REAL.hs M := by
  have key : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    have h : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold wt Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, key]
  exact Finset.sum_comm

theorem one_le_hs_of_inUJ {n : ℕ} (hn : 0 < n) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.REAL.inUJ ε g) : 1 ≤ Formalism.REAL.hs g := by
  set a : Fin n := ⟨0, hn⟩ with ha
  have hs1 : ∀ k : Fin n, ‖(if ε k = true then (1 : ℂ) else -1)‖ = 1 := by
    intro k; split_ifs <;> simp
  have e : ∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a =
      (if ε a = true then (1 : ℂ) else -1) := by
    have h2 := congrFun (congrFun h a) a
    simpa [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply] using h2
  have h3 : (1 : ℝ) ≤ ∑ k, ‖g k a‖ ^ 2 := by
    calc (1 : ℝ) = ‖∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := by
          rw [e, hs1]
      _ ≤ ∑ k, ‖star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := norm_sum_le _ _
      _ = ∑ k, ‖g k a‖ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul, hs1, norm_star]; ring
  refine h3.trans ?_
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun k _ => ?_
  exact Finset.single_le_sum (f := fun j => ‖g k j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ a)

theorem rpow_neg_le_of_dichotomy {w b' : ℝ} {s : ℕ} (hw : w = 0 ∨ 1 ≤ w) (hb : (s : ℝ) ≤ b') :
    w ^ (-b') ≤ ((2 : ℝ) ^ b' + 1) * ((1 + w)⁻¹) ^ s := by
  have hb0 : 0 ≤ b' := (Nat.cast_nonneg s).trans hb
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b' := Real.rpow_pos_of_pos (by norm_num) _
  rcases hw with rfl | hw
  · have h1 : (0 : ℝ) ^ (-b') ≤ 1 := Real.zero_rpow_le_one _
    simp only [add_zero, inv_one, one_pow, mul_one]
    linarith
  · have hw0 : 0 < w := by linarith
    have hu0 : 0 < (1 + w)⁻¹ := by positivity
    have hu1 : (1 + w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hwi : w⁻¹ ≤ 2 * (1 + w)⁻¹ := by
      rw [inv_le_comm₀ hw0 (by positivity), mul_inv, inv_inv]
      linarith
    calc w ^ (-b') = (w⁻¹) ^ b' := by rw [Real.rpow_neg hw0.le, Real.inv_rpow hw0.le]
      _ ≤ (2 * (1 + w)⁻¹) ^ b' := Real.rpow_le_rpow (by positivity) hwi hb0
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ b' := Real.mul_rpow (by norm_num) hu0.le
      _ ≤ (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ (s : ℝ) := by
          gcongr ?_ * ?_
          exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hb
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ s := by rw [Real.rpow_natCast]
      _ ≤ _ := by
          have : 0 ≤ ((1 + w)⁻¹) ^ s := by positivity
          nlinarith

theorem integrable_wt_rpow_neg {n : ℕ} (ε : Fin n → Bool) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' →
      MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.HolPQ.one_add_hs_inv_pow_lintegral_lt_top n ε
  have hfin : ∫⁻ g : UJ ε, ENNReal.ofReal (((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) ∂(Formalism.REAL.muG ε) < ⊤ :=
    hs s le_rfl
  refine ⟨s, Nat.cast_nonneg s, fun b' hb' => ?_⟩
  have hinv : (Formalism.REAL.muG ε).inv = Formalism.REAL.muG ε := Formalism.REAL.invInvariant n ε
  rw [hinv]
  have hc : Continuous fun g : UJ ε => Formalism.REAL.hs (uMat g) := GlobalTheory.CompanionTheory.HolPQ.continuous_hs_umat ε
  have hnn : ∀ g : UJ ε, 0 ≤ Formalism.REAL.hs (uMat g) := fun g =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hI : Integrable (fun g : UJ ε => ((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) (Formalism.REAL.muG ε) := by
    refine ⟨((measurable_const.add hc.measurable).inv.pow_const s).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      have := hnn g
      positivity)]
    exact hfin
  have hw : ∀ g : UJ ε, wt (uMat g) = Formalism.REAL.hs (uMat g) := fun g => wt_eq_hs _
  have hmeas : Measurable fun g : UJ ε => wt (uMat g) ^ (-b') := by
    simp only [hw]
    exact hc.measurable.pow_const _
  refine (hI.const_mul ((2 : ℝ) ^ b' + 1)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  have hdich : Formalism.REAL.hs (uMat g) = 0 ∨ 1 ≤ Formalism.REAL.hs (uMat g) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [Formalism.REAL.hs]
    · right; exact one_le_hs_of_inUJ hn ε _ g.2
  rw [hw, Real.norm_of_nonneg (Real.rpow_nonneg (hnn g) _)]
  exact rpow_neg_le_of_dichotomy hdich hb'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

end
end
