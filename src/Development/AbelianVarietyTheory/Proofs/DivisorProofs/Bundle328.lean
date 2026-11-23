module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle246
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open NumberField
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latM_ne_zero (𝔞 : Frac F) : latM 𝔞 ≠ 0 := by
  rw [latM_eq_dual]
  exact FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero

theorem nrm_pos (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  unfold nrm
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

theorem eisTerm_eq [IsTotallyReal F] (k : ℕ) (z : Emb F → ℂ) (a b : F) :
    eisTerm k 0 z (a, b) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      lhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) a := by
  have hprod : ∏ τ, latPt z (a, b) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ (Module.finrank ℚ F) *
      ∏ τ : F →+* ℝ, (((τ b : ℝ) : ℂ) * z τ + ((τ a : ℝ) : ℂ)) := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [latPt]; ring
  unfold eisTerm lhsTerm
  rw [hprod]
  simp only [mul_zero, Complex.cpow_zero, mul_one, zpow_neg, zpow_natCast]
  ring

theorem rhsTerm_eq [IsTotallyReal F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (ν b : F) :
    rhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z (ν, b) := by
  have hN : ∏ τ : F →+* ℝ, τ ν = ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    have h := prod_emb ν
    rw [← Complex.ofReal_prod] at h
    exact_mod_cast h
  have hpos := nrm_pos 𝔞
  have hreal : |((Algebra.norm ℚ ν : ℚ) : ℝ)| ^ (k - 1) =
      nrm 𝔞 ^ (k - 1) * (|((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hpos.ne')]
  have hsum : ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * (((τ b : ℝ) : ℂ) * z τ) =
      ∑ τ : F →+* ℝ, ((τ (ν * b) : ℝ) : ℂ) * z τ := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, Complex.ofReal_mul, mul_assoc]
  unfold rhsTerm qTerm qPow
  rw [hN, hsum, hreal, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

end GlobalTheory.EisPerB


open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent in
theorem GlobalTheory.EisPerB.lattice_sum_eq_cone_sum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
    ∀ (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k → ∀ (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
      Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) ∧
      HasSum (fun a : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F) => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k 0 z ((a : F), b))
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) *
          ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) := by
  intro F _ _ _ hLip 𝔞 k hk2 hke b hb z hz
  have hz'im : ∀ τ, ((fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) τ).im ≠ 0 := by
    intro τ
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  obtain ⟨hL, hR, hEq⟩ := hLip F (latM 𝔞) (GlobalTheory.EisPerB.latM_ne_zero 𝔞) k hk2 hke _ hz'im
  let e : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ≃ GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b :=
    Equiv.subtypeEquivRight (fun ν => GlobalTheory.T.mem_traceDualSignedPositiveCone_iff_totallyPositive F 𝔞 b hb z hz ν)
  have hN : (nrm 𝔞 : ℂ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (GlobalTheory.EisPerB.nrm_pos 𝔞).ne')
  have hRq : ∀ ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z ((e ν).1, b) :=
    fun ν => GlobalTheory.EisPerB.rhsTerm_eq 𝔞 k z ν.1 b
  have hsumQ : Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b)) := by
    have h1 : Summable (fun ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) =>
        qTerm 𝔞 k z ((e ν).1, b)) := by
      refine (hR.mul_left ((nrm 𝔞 : ℂ) ^ (k - 1))⁻¹).congr fun ν => ?_
      rw [hRq, inv_mul_cancel_left₀ hN]
    exact e.summable_iff.1 h1
  have htsum : ∑' ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν =
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) := by
    rw [tsum_congr hRq, tsum_mul_left]
    congr 1
    exact e.tsum_eq (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b))
  refine ⟨hsumQ, ?_⟩
  have hE : (fun a : (latM 𝔞 : Set F) => eisTerm k 0 z ((a : F), b)) = fun a : (latM 𝔞 : Set F) =>
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
        lhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) a :=
    funext fun a => GlobalTheory.EisPerB.eisTerm_eq k z a b
  rw [hE]
  have h := hL.hasSum.mul_left ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹
  rw [hEq, htsum] at h
  rw [← GlobalTheory.T.lipschitzConstant_inverseDifferent_eisenstein F 𝔞 k (by omega)]
  have hv : ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * lipConst k (latM 𝔞) *
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      (lipConst k (latM 𝔞) * ((nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b))) := by
    ring
  rw [hv]
  exact h
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem _root_.GlobalTheory.T.adjoinRootProdLinearFactors_structure : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S] (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧ lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧ (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧ (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧ (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  first | exact @GlobalTheory.RingFacts.ring_facts | exact GlobalTheory.RingFacts.ring_facts | (intros; apply GlobalTheory.RingFacts.ring_facts <;> assumption)
end

section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section
namespace GlobalTheory.PoincareBounds

def pdiag {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : ℝ :=
  if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2

theorem poincareGram_eq {n : ℕ} (a : ℕ) (z : Fin n → ℂ) :
    poincareGram a z = diagonal fun k => ((pdiag a z k : ℝ) : ℂ) := rfl

theorem pdiag_nonneg {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : 0 ≤ pdiag a z k := by
  unfold pdiag; split_ifs <;> positivity

theorem gnorm_diag_sq {n : ℕ} (d : Fin n → ℝ) (hd : ∀ k, 0 ≤ d k) (ξ : Fin n → ℂ) :
    gnorm (diagonal fun k => ((d k : ℝ) : ℂ)) ξ ^ 2 = ∑ k, d k * ‖ξ k‖ ^ 2 := by
  have hP : (diagonal fun k => ((d k : ℝ) : ℂ)).PosSemidef := by
    rw [posSemidef_diagonal_iff]; intro k; exact_mod_cast hd k
  rw [gnorm_sq hP, form_eq_sum]
  simp only [diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm (ξ k), mul_assoc, mul_conj, ← ofReal_mul, ofReal_re, normSq_eq_norm_sq]

theorem norm_mul_tlog_lt {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) :
    0 < ‖w‖ * tlog w ∧ ‖w‖ * tlog w < 1 := by
  have hx : 0 < ‖w‖ := norm_pos_iff.2 h0
  refine ⟨mul_pos hx (tlog_pos h0 h1), ?_⟩
  have hl := Real.abs_log_mul_self_lt ‖w‖ hx h1.le
  have hpi : 1 < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have e : ‖w‖ * tlog w = -(Real.log ‖w‖ * ‖w‖) / (2 * Real.pi) := by
    unfold tlog; ring
  rw [e, div_lt_one (by linarith)]
  have := neg_le_abs (Real.log ‖w‖ * ‖w‖)
  linarith

theorem half_le_pdiag {n a : ℕ} (ha : a ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1) {z : Fin n → ℂ}
    (hz : z ∈ punctured ha ρ) (k : Fin n) : 1 / 2 ≤ pdiag a z k := by
  unfold pdiag
  split_ifs with hk
  · have h0 : z k ≠ 0 := hz.2 ⟨k, hk⟩
    obtain ⟨hp, hl⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have hs : ‖z k‖ ^ 2 * tlog (z k) ^ 2 = (‖z k‖ * tlog (z k)) ^ 2 := by ring
    rw [hs]
    have h2 : 0 < (‖z k‖ * tlog (z k)) ^ 2 := by positivity
    have h3 : (‖z k‖ * tlog (z k)) ^ 2 < 1 := by nlinarith
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  · exact le_rfl

theorem pdiag_term_le {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (ξ : Fin n → ℂ) (k : Fin n) :
    pdiag a z k * ‖ξ k‖ ^ 2 ≤ gnorm (poincareGram a z) ξ ^ 2 := by
  rw [poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg a z)]
  exact Finset.single_le_sum (f := fun k => pdiag a z k * ‖ξ k‖ ^ 2)
    (fun j _ => mul_nonneg (pdiag_nonneg a z j) (by positivity)) (Finset.mem_univ k)

theorem poincare_bounds : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 → ∀ z ∈ punctured ha ρ,
    (poincareGram a z).PosSemidef ∧ ∀ ξ : Fin n → ℂ, (∀ k, ‖ξ k‖ ≤ 2 * gnorm (poincareGram a z) ξ) ∧
      ∀ i : Fin a, ‖ξ (Fin.castLE ha i)‖ ≤
        2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) * gnorm (poincareGram a z) ξ := by
  intro n a ha ρ hρ z hz
  refine ⟨?_, fun ξ => ⟨fun k => ?_, fun i => ?_⟩⟩
  · rw [poincareGram_eq, posSemidef_diagonal_iff]
    intro k; exact_mod_cast pdiag_nonneg a z k
  · have h1 := pdiag_term_le a z ξ k
    have h2 := half_le_pdiag ha hρ hz k
    have hG := gnorm_nonneg (poincareGram a z) ξ
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * gnorm (poincareGram a z) ξ ^ 2 := by nlinarith
    nlinarith
  · set k := Fin.castLE ha i with hkdef
    have hk : k.val < a := i.2
    have h0 : z k ≠ 0 := hz.2 i
    obtain ⟨hp, -⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have h1 := pdiag_term_le a z ξ k
    have hd : pdiag a z k = 1 / (2 * (‖z k‖ * tlog (z k)) ^ 2) := by
      unfold pdiag; rw [if_pos hk]; ring
    rw [hd] at h1
    set s := ‖z k‖ * tlog (z k)
    set G := gnorm (poincareGram a z) ξ
    have hG : 0 ≤ G := gnorm_nonneg _ _
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * s ^ 2 * G ^ 2 := by
      have hs2 : 0 < 2 * s ^ 2 := by positivity
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs2] at h1
      linarith
    nlinarith [mul_nonneg hp.le hG]

end GlobalTheory.PoincareBounds
end
end

section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeGramLocal

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem del_im_of_differentiableAt {F : E → ℂ} {z : E} (hF : DifferentiableAt ℂ F z) (ξ : E) :
    del (fun x => ((F x).im : ℂ)) z ξ = (1 / (2 * I)) * fderiv ℂ F z ξ := by
  have hR : DifferentiableAt ℝ F z := hF.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun x => conj (F x)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z hR
  have e : (fun x => ((F x).im : ℂ)) = fun x => (1 / (2 * I)) • (F x - conj (F x)) := by
    funext x; rw [im_eq_sub_conj, smul_eq_mul]; ring
  rw [e, del_const_smul _ (hR.fun_sub hc), ContinuousLinearMap.smul_apply, del_sub hR hc,
    ContinuousLinearMap.sub_apply, del_conj, dbar_eq_zero hF, del_eq_fderiv hF]
  simp

theorem ddbar_im_of_contDiffAt {F : E → ℂ} {z : E} (hF : ContDiffAt ℂ 2 F z) :
    ddbar (fun x => ((F x).im : ℂ)) z = 0 := by
  have h := leviForm_re_eq_zero (f := fun x => -I * F x) (contDiffAt_const.mul hF)
  have e : (fun x => ((F x).im : ℂ)) = fun x => (((-I * F x).re : ℝ) : ℂ) := by
    funext x; simp
  rw [e]; exact h

theorem contDiffAt_im_of_analyticAt {F : E → ℂ} {z : E} (hF : AnalyticAt ℂ F z)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun x => ((F x).im : ℂ)) z :=
  (ofRealCLM.comp imCLM).contDiff.contDiffAt.comp z (hF.contDiffAt.restrict_scalars ℝ)

end General

def locLog (w₀ w : ℂ) : ℂ := Complex.log (w / w₀) + Complex.log w₀

theorem exp_locLog {w₀ w : ℂ} (h0 : w₀ ≠ 0) (h : w / w₀ ∈ slitPlane) :
    exp (locLog w₀ w) = w := by
  rw [locLog, exp_add, exp_log (slitPlane_ne_zero h), exp_log h0, div_mul_cancel₀ _ h0]

theorem hasDerivAt_locLog {w₀ w : ℂ} (h : w / w₀ ∈ slitPlane) :
    HasDerivAt (locLog w₀) (1 / w₀ / (w / w₀)) w :=
  (((hasDerivAt_id w).div_const w₀).clog h).add_const _

end GlobalTheory.HodgeGramLocal

namespace GlobalTheory.HodgeGramLocal

variable {n a g : ℕ}

def locEntry (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (j k : Fin g) (x : Fin n → ℂ) : ℂ :=
  τ₀ x j k + ∑ i, locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i)) / (2 * Real.pi * I) *
    ((B i j k : ℤ) : ℂ)

theorem isOpen_polydisc (n : ℕ) : IsOpen (polydisc n 1) := by
  rw [show polydisc n 1 = ⋂ k, {z : Fin n → ℂ | ‖z k‖ < 1} by ext; simp [polydisc]]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const

theorem hodgeGram_local (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (hP : IsPeriodChart rk τ₀ B) :
    ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧
      (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) •
        ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) +
          ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) •
            ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧
      ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  intro z hz
  let V : Set (Fin n → ℂ) := {x | x ∈ polydisc n 1 ∧
    ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane}
  have hVo : IsOpen V := by
    have h2 : IsOpen {x : Fin n → ℂ |
        ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_slitPlane.preimage (by fun_prop)
    exact (isOpen_polydisc n).inter h2
  have hzV : z ∈ V := ⟨hz.1, fun i => by rw [div_self (hz.2 i)]; exact one_mem_slitPlane⟩
  have hV : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

  have hterm : ∀ (j k : Fin g) (i : Fin a) (x : Fin n → ℂ), x ∈ V →
      HasFDerivAt (fun y : Fin n → ℂ => locLog (z (Fin.castLE ha i)) (y (Fin.castLE ha i)) /
        (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ))
        ((1 / z (Fin.castLE ha i) / (x (Fin.castLE ha i) / z (Fin.castLE ha i)) /
          (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k i x hx => by
      have h1 := ((hasDerivAt_locLog (hx.2 i)).div_const (2 * (Real.pi : ℂ) * I)).mul_const
        ((B i j k : ℤ) : ℂ)
      have h2 : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE ha i))
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
        hasFDerivAt_apply _ _
      exact h1.comp_hasFDerivAt x h2
  have hτ : ∀ j k, ∀ x ∈ V, HasFDerivAt (fun y => τ₀ y j k) (fderiv ℂ (fun y => τ₀ y j k) x) x :=
    fun j k x hx => ((hP.holo j k).differentiableAt ((isOpen_polydisc n).mem_nhds hx.1)).hasFDerivAt
  have hloc : ∀ j k, ∀ x ∈ V, HasFDerivAt (locEntry ha τ₀ B z j k)
      (fderiv ℂ (fun y => τ₀ y j k) x + ∑ i, (1 / z (Fin.castLE ha i) /
        (x (Fin.castLE ha i) / z (Fin.castLE ha i)) / (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k x hx => (hτ j k x hx).add (HasFDerivAt.fun_sum fun i _ => hterm j k i x hx)
  have hdiff : ∀ j k, DifferentiableOn ℂ (locEntry ha τ₀ B z j k) V := fun j k x hx =>
    (hloc j k x hx).differentiableAt.differentiableWithinAt
  have hF : ∀ j k, AnalyticAt ℂ (locEntry ha τ₀ B z j k) z := fun j k =>
    ReciprocityTheory.AnForm.Osgood.osgood n V _ hVo (hdiff j k) z hzV
  have heq : ∀ x ∈ V, hodgeGram ha τ₀ B x = of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) := by
    intro x hx
    have hL : ∀ i, exp ((fun i => locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i))) i) =
        x (Fin.castLE ha i) := fun i => exp_locLog (hz.2 i) (hx.2 i)
    rw [hodgeGram, ← im_period ha τ₀ B x _ hL]
    ext j k
    simp [period, locEntry, Matrix.sum_apply]
  have hev : hodgeGram ha τ₀ B =ᶠ[𝓝 z] fun x => of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) :=
    Filter.eventually_of_mem hV heq
  have hev' : ∀ j k, (fun x => hodgeGram ha τ₀ B x j k) =ᶠ[𝓝 z]
      fun x => ((locEntry ha τ₀ B z j k x).im : ℂ) := fun j k =>
    Filter.eventually_of_mem hV fun x hx => by
      show hodgeGram ha τ₀ B x j k = _
      rw [heq x hx]; rfl
  refine ⟨fun j k => (contDiffAt_im_of_analyticAt (hF j k)).congr_of_eventuallyEq (hev' j k),
    fun ξ => ?_, fun ξ η => ?_⟩
  · rw [mdel_congr hev]
    ext j k
    simp only [mdel_apply, of_apply]
    rw [del_im_of_differentiableAt (hF j k).differentiableAt, (hloc j k z hzV).fderiv]
    simp [Matrix.sum_apply, div_self (hz.2 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · ext j k
    rw [mddbar_apply, ddbar_congr (hev' j k),
      ddbar_im_of_contDiffAt ((hF j k).contDiffAt)]
    rfl

end GlobalTheory.HodgeGramLocal
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.UnitsDense

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem denseRange_embeddings' : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap E
  have hs : Function.Surjective
      (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) := by
    intro y
    choose x hx using fun w : InfinitePlace E =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex w) (y w)
    exact ⟨x, funext hx⟩
  have hc : Continuous (Pi.map fun w : InfinitePlace E => InfinitePlace.Completion.extensionEmbedding w) :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have := hs.denseRange.comp h1 hc
  convert this using 1
  funext x w
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  rw [InfiniteAdeleRing.algebraMap_apply]
  have := InfinitePlace.Completion.extensionEmbedding_coe (v := w) ((WithAbs.equiv w.1).symm x)
  simp only [RingEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

theorem exists_unit_mem_open :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty →
      ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  intro E _ _ _ V hV ⟨v, hv⟩
  have hU : IsOpen (Units.val '' V) := Units.isOpenEmbedding_val.isOpenMap V hV
  have hd : DenseRange fun x : E => pInf E (algebraMap E (Ad E) x) := by
    have : (fun x : E => pInf E (algebraMap E (Ad E) x)) = fun (x : E) (w : InfinitePlace E) => w.embedding x := by
      funext x w; exact pInf_algebraMap x w
    rw [this]; exact denseRange_embeddings'
  obtain ⟨x, u, hu, hxu⟩ := hd.exists_mem_open hU ⟨v.1, v, hv, rfl⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hxu
    haveI : Nonempty (InfinitePlace E) := inferInstance
    exact u.ne_zero hxu
  refine ⟨Units.mk0 x hx, ?_⟩
  convert hu using 1
  ext
  simp [hxu]

end GlobalTheory.UnitsDense
end

section

noncomputable section

open NumberField

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E]

def expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp X).unit

@[simp] theorem val_expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    (expGLi a X).val = NormedSpace.exp X := rfl

theorem expGLi_add_smul (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expGLi a ((s + t) • X) = expGLi a (s • X) * expGLi a (t • X) :=
  Units.ext (by
    rw [Units.val_mul, val_expGLi, val_expGLi, val_expGLi, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t))

@[simp] theorem expGLi_zero (a : ℕ) : expGLi a (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
  Units.ext (by rw [val_expGLi, NormedSpace.exp_zero, Units.val_one])

end GlobalTheory.CuspRep
end
end
