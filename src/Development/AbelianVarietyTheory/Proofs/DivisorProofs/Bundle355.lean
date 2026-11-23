module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSum
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle285
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open Complex GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y = if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | exact GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | (intros; apply GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors


theorem _root_.GlobalTheory.T.summable_heckeWeightTwoLatticeSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  first | exact @GlobalTheory.HeckeTwo.summable_latSum | exact GlobalTheory.HeckeTwo.summable_latSum | (intros; apply GlobalTheory.HeckeTwo.summable_latSum <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.contDiffOn_heckeEisensteinFourierTerm : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → ∀ σ ∈ halfPlane,
  ContDiffOn ℝ ∞ (fun z : Emb F → ℂ => fTerm σ z b ν) (upperHalf F) := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_contDiffOn | exact GlobalTheory.HeckeTwo.fTerm_contDiffOn | (intros; apply GlobalTheory.HeckeTwo.fTerm_contDiffOn <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.FactorBound

theorem iteratedDeriv_eChar (i : ℕ) :
    iteratedDeriv i (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) =
      fun x : ℝ => (2 * (Real.pi : ℂ) * I) ^ i * Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * z))
        (Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ)) * (2 * (Real.pi : ℂ) * I)) (x : ℂ) := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (2 * (Real.pi : ℂ) * I)).cexp
      simpa using this
    have h2 := (h1.comp_ofReal).const_mul ((2 * (Real.pi : ℂ) * I) ^ i)
    rw [h2.deriv]
    ring

theorem contDiff_eChar :
    ContDiff ℝ ω (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem norm_iteratedFDeriv_eChar (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) x‖ = (2 * Real.pi) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eChar]
  simp only [norm_mul, norm_pow]
  have : ‖Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [this, mul_one]
  congr 1
  simp [Complex.norm_real, abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_eRe (a : ℝ) (i : ℕ) (w : ℂ) :
    ‖iteratedFDeriv ℝ i (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) w‖ ≤
      (2 * Real.pi * |a|) ^ i := by
  set L : ℂ →L[ℝ] ℝ := a • Complex.reCLM
  have hf : (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) =
      (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) ∘ L := by
    funext w; simp [L]
  rw [hf, L.iteratedFDeriv_comp_right contDiff_eChar w le_top]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eChar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖L‖ ≤ |a| := by
    simp only [L]
    refine (norm_smul_le _ _).trans ?_
    simp [Complex.reCLM_norm]
  rw [mul_pow (2 * Real.pi) |a| i]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL i) (pow_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) _)

theorem norm_iteratedFDerivWithin_hIm (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (j : ℕ) (w : ℂ)
    (hw : β * w.im ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | β * w.im ≠ 0} w‖ ≤
      ‖iteratedDeriv j (hTrans σ ν) (β * w.im)‖ * |β| ^ j := by
  set L : ℂ →L[ℝ] ℝ := β • Complex.imCLM
  have hS : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
  have hpre : {w : ℂ | β * w.im ≠ 0} = L ⁻¹' {y : ℝ | y ≠ 0} := by ext w; simp [L]
  have hf : (fun w : ℂ => hTrans σ ν (β * w.im)) = hTrans σ ν ∘ L := by funext w; simp [L]
  have hLw : L w = β * w.im := by simp [L]
  have hLw' : L w ∈ {y : ℝ | y ≠ 0} := by rw [hLw]; exact hw
  rw [hf, hpre, L.iteratedFDerivWithin_comp_right (TermSmooth.contDiffOn_hTrans σ hσ ν) hS.uniqueDiffOn
    (hS.preimage L.continuous).uniqueDiffOn hLw' (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDerivWithin_of_isOpen j hS hLw',
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, hLw]
  have hL : ‖L‖ ≤ |β| := by
    simp only [L]
    refine (norm_smul_le _ _).trans ?_
    simp [Complex.imCLM_norm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL j) (norm_nonneg _)

theorem norm_iteratedFDeriv_le_sum (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) (k : ℕ) (w : ℂ)
    (hw : 0 < w.im) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi * |ν * β|) ^ i *
        (‖iteratedDeriv (k - i) (hTrans σ ν) (β * w.im)‖ * |β| ^ (k - i)) := by
  set V : Set ℂ := {w : ℂ | β * w.im ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun (continuous_const.mul Complex.continuous_im) continuous_const
  have hwV : w ∈ V := mul_ne_zero hβ hw.ne'
  have hu : ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) V :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul Complex.reCLM.contDiff))).cexp).contDiffOn
  have hv : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) V :=
    (TermSmooth.contDiffOn_hTrans σ hσ ν).comp (contDiff_const.mul Complex.imCLM.contDiff).contDiffOn
      fun z hz => hz
  rw [← iteratedFDerivWithin_of_isOpen k hV hwV]
  refine (norm_iteratedFDerivWithin_mul_le hu hv hV.uniqueDiffOn hwV (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [iteratedFDerivWithin_of_isOpen i hV hwV]
  refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_eRe (ν * β) i w) (Nat.cast_nonneg _))
    (norm_iteratedFDerivWithin_hIm σ hσ ν β (k - i) w hwV) (norm_nonneg _) ?_
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)

theorem norm_iteratedFDeriv_fourierFactor_le :
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ c c' : ℝ, 0 < c → ∀ k : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν β : ℝ, ν ≠ 0 → β ≠ 0 → ∀ w : ℂ, c ≤ w.im → w.im ≤ c' →
      ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤ C * (|β| + |β|⁻¹) ^ m / (1 + |ν * β|) ^ N := by
  intro H K hK hKH c c' hc k
  choose s hs using H K hK hKH
  refine ⟨k + ∑ j ∈ Finset.range (k + 1), s j, fun N => ?_⟩
  choose C hC using fun j => hs j (N + k)
  set M : ℝ := max c' c⁻¹ with hMdef
  set μ : ℝ := min 1 c with hμdef
  have hM : 0 < M := lt_of_lt_of_le (inv_pos.2 hc) (le_max_right _ _)
  have hμ : 0 < μ := lt_min one_pos hc
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi) ^ i *
      (|C (k - i)| * M ^ s (k - i) / μ ^ (N + k)), ?_⟩
  intro σ hσ ν β hν hβ w hw1 hw2
  have hσH : σ ∈ halfPlane := hKH hσ
  have ht : 0 < w.im := lt_of_lt_of_le hc hw1
  set t := w.im with htdef
  set B : ℝ := |β| + |β|⁻¹ with hBdef
  set A : ℝ := 1 + |ν * β| with hAdef
  have hβp : 0 < |β| := abs_pos.2 hβ
  have hB1 : 1 ≤ B := by
    rcases le_total 1 |β| with h | h
    · have := inv_nonneg.2 hβp.le; linarith
    · have := (one_le_inv₀ hβp).2 h; linarith
  have hA1 : 1 ≤ A := by have := abs_nonneg (ν * β); linarith
  have hApos : 0 < A := by linarith
  have hy : β * t ≠ 0 := mul_ne_zero hβ ht.ne'
  have hyB : |β * t| + |β * t|⁻¹ ≤ M * B := by
    rw [abs_mul, abs_of_pos ht, mul_inv, hBdef, mul_add]
    have h1 : |β| * t ≤ M * |β| := by
      rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hw2.trans (le_max_left _ _)) hβp.le
    have h2 : |β|⁻¹ * t⁻¹ ≤ M * |β|⁻¹ := by
      rw [mul_comm M]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hβp.le)
      exact (inv_anti₀ hc hw1).trans (le_max_right _ _)
    linarith
  have hyA : μ * A ≤ 1 + |ν * (β * t)| := by
    rw [← mul_assoc, abs_mul (ν * β), abs_of_pos ht, hAdef, mul_add, mul_one]
    have h1 : μ ≤ 1 := min_le_left _ _
    have h2 : μ ≤ t := (min_le_right _ _).trans hw1
    have h3 : μ * |ν * β| ≤ |ν * β| * t := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith
  have hh : ∀ j, ‖iteratedDeriv j (hTrans σ ν) (β * t)‖ ≤
      |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
    intro j
    refine (hC j σ hσ ν (β * t) hν hy).trans ?_
    have hX : 0 ≤ (|β * t| + |β * t|⁻¹) ^ s j := by positivity
    calc C j * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k)
        ≤ |C j| * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k) := by
          gcongr
          exact le_abs_self _
      _ ≤ |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
          gcongr
  refine (norm_iteratedFDeriv_le_sum σ hσH ν β hβ k w ht).trans ?_
  rw [mul_div_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  set j := k - i with hjdef
  have hjk : j ≤ k := Nat.sub_le _ _
  have hsj : s j ≤ ∑ j ∈ Finset.range (k + 1), s j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))
  have hd : (2 * Real.pi * |ν * β|) ^ i ≤ (2 * Real.pi) ^ i * A ^ k := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |ν * β| ^ i ≤ A ^ i := pow_le_pow_left₀ (abs_nonneg _) (by linarith) i
      _ ≤ A ^ k := pow_le_pow_right₀ hA1 hik
  have he : |β| ^ j ≤ B ^ k :=
    (pow_le_pow_left₀ hβp.le (by have := inv_nonneg.2 hβp.le; linarith) j).trans (pow_le_pow_right₀ hB1 hjk)
  calc (k.choose i : ℝ) * (2 * Real.pi * |ν * β|) ^ i * (‖iteratedDeriv j (hTrans σ ν) (β * t)‖ * |β| ^ j)
      ≤ (k.choose i : ℝ) * ((2 * Real.pi) ^ i * A ^ k) *
          ((|C j| * (M * B) ^ s j / (μ * A) ^ (N + k)) * B ^ k) := by
        gcongr
        exact hh j
    _ = (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) * (B ^ (k + s j) / A ^ N) := by
        have hA0 : A ≠ 0 := hApos.ne'
        have hμ0 : μ ≠ 0 := hμ.ne'
        rw [mul_pow, mul_pow, pow_add, pow_add]
        field_simp
        rw [mul_pow, mul_pow, pow_add]
        ring
    _ ≤ (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) *
          (B ^ (k + ∑ j ∈ Finset.range (k + 1), s j) / A ^ N) := by
        gcongr
        all_goals first | exact hB1 | omega

end GlobalTheory.HeckeTwo.FactorBound

end
end

section

open NumberField Complex MeasureTheory


theorem _root_.GlobalTheory.T.heckePhiFourierTransform_rapid_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ, ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_rapid_decay | exact GlobalTheory.HeckeTwo.hTrans_rapid_decay | (intros; apply GlobalTheory.HeckeTwo.hTrans_rapid_decay <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by
  first | exact @GlobalTheory.HeckeTwo.summable_balanced_latSum | exact GlobalTheory.HeckeTwo.summable_balanced_latSum | (intros; apply GlobalTheory.HeckeTwo.summable_balanced_latSum <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckeWeightTwo_constantTerm_eq_partialZeta_neg_one : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (C : ClassGroup (NumberField.RingOfIntegers F)) (D : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) (Za Za' : ℂ → ℂ), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) → C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Za → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Za' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Za s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Za' (1 - s)) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * GlobalTheory.HeckeTwo.aPart 𝔞 0 / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Za' (1 - ((2 : ℕ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeTwoConst.constant_term | exact GlobalTheory.HeckeTwoConst.constant_term | (intros; apply GlobalTheory.HeckeTwoConst.constant_term <;> assumption)
end

section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_equiv_fourierClasses_posCone_summand : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)) ≃ Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟),
      ∀ (k : ℕ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 (GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep β)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (e x) = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (x.2.1, GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  first | exact @GlobalTheory.Div.QFibre.qFibres | exact GlobalTheory.Div.QFibre.qFibres | (intros; apply GlobalTheory.Div.QFibre.qFibres <;> assumption)
end

section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_equiv_latticeClasses_fibre_summand : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    ∃ e : (Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)) ≃
      {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0},
      ∀ (k : ℕ), Even k → ∀ (σ : ℂ) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (x : Σ _β : GlobalTheory.SlopeTestRemainingChoices.EisFibre.NzCls 𝔟, (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F)),
        GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (e x).1 = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z ((x.2 : F), GlobalTheory.SlopeTestRemainingChoices.EisFibre.rep x.1) := by
  first | exact @GlobalTheory.LatFibre.exists_equiv | exact GlobalTheory.LatFibre.exists_equiv | (intros; apply GlobalTheory.LatFibre.exists_equiv <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial Matrix

theorem _root_.GlobalTheory.T.hermitianModel_charpoly_eq_and_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → γ.charpoly = B.P ∧ (B.g * B.σ B.g = 1 → (γ.map K.c)ᵀ * γ = 1) := by
  first | exact @GlobalTheory.ModelCharpoly.model_charpoly_unitary | exact GlobalTheory.ModelCharpoly.model_charpoly_unitary | (intros; apply GlobalTheory.ModelCharpoly.model_charpoly_unitary <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial Matrix

theorem _root_.GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' : Matrix (Fin n) (Fin n) K.E) (x x' v : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (x' : B.A) = x * (v * B.σ v) → ∃ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 ∧ γ * u = u * γ' := by
  first | exact @GlobalTheory.InertUnitOrb.conj_of_norm_class | exact GlobalTheory.InertUnitOrb.conj_of_norm_class | (intros; apply GlobalTheory.InertUnitOrb.conj_of_norm_class <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbertSections_finite_flat : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens), Module.Finite Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) ∧ Module.Flat Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) := by
  first | (exact @GlobalTheory.HilbAff.sec_finite_flat) | (exact GlobalTheory.HilbAff.sec_finite_flat) | (intros; apply GlobalTheory.HilbAff.sec_finite_flat  <;> assumption)
end
