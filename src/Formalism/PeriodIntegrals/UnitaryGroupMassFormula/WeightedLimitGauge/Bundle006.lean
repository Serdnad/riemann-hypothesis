module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Unimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
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

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

def boost (y : Fin k → ℂ) (c : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  Fin.lastCases (Fin.lastCases c (fun j' => ((‖c‖ : ℂ) / conj c) * conj (y j')) j)
    (fun i' => Fin.lastCases (y i')
      (fun j' => (if i' = j' then 1 else 0) + y i' * conj (y j') / (1 + (‖c‖ : ℂ))) j) i

theorem form_apply (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    (Aᴴ * Hb k * A) i j = ∑ l : Fin k, conj (A l.castSucc i) * A l.castSucc j -
      conj (A (Fin.last k) i) * A (Fin.last k) j := by
  rw [Hb, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def, Fin.castSucc_ne_last, if_false,
    if_true, mul_one]
  ring

theorem boost_mem (y : Fin k → ℂ) (c : ℂ)
    (hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1) (hc0 : c ≠ 0) :
    (boost y c)ᴴ * Hb k * boost y c = Hb k := by
  have hc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hD : (1 + ((‖c‖ : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [norm_nonneg c]
  have hcc : conj c ≠ 0 := by rwa [map_ne_zero]
  have hn0 : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hc0
  have hcb : conj c = ((‖c‖ : ℝ) : ℂ) ^ 2 / c := by
    rw [eq_div_iff hc0]; exact hc
  ext i j
  rw [form_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_eq, if_true]
      rw [hS, hc]; ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last j).symm]
      have h1 : ∀ l : Fin k, conj (y l) * ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = j then conj (y l) else 0) + (conj (y j) / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last i)]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) * y l =
          (if l = i then y l else 0) + (y i / (1 + (‖c‖ : ℂ))) * (conj (y l) * y l) := by
        intro l
        simp only [map_add (f := _), map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        split_ifs <;> simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      try simp only [hcb]
      field_simp
      ring
    | cast j =>
      simp only [boost, Fin.lastCases_last, Fin.lastCases_castSucc, Hb, Matrix.diagonal_apply, Fin.castSucc_inj,
        Fin.castSucc_ne_last, if_false]
      have h1 : ∀ l : Fin k, conj ((if l = i then 1 else 0) + y l * conj (y i) / (1 + (‖c‖ : ℂ))) *
          ((if l = j then 1 else 0) + y l * conj (y j) / (1 + (‖c‖ : ℂ))) =
          (if l = i then (if i = j then 1 else 0) else 0) + (if l = i then y i * conj (y j) / (1 + (‖c‖ : ℂ)) else 0) +
            (if l = j then conj (y l) * y i / (1 + (‖c‖ : ℂ)) else 0) +
            (y i * conj (y j) / (1 + (‖c‖ : ℂ)) ^ 2) * (conj (y l) * y l) := by
        intro l
        simp only [map_add (f := _), map_mul, map_div₀, map_one, Complex.conj_ofReal, Complex.conj_conj]
        by_cases hi : l = i <;> by_cases hj : l = j
        · subst hi; subst hj; simp <;> field_simp <;> ring
        · subst hi; simp [hj] <;> field_simp <;> ring
        · subst hj; simp [hi] <;> field_simp <;> ring
        · simp [hi, hj] <;> field_simp <;> ring
      rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum, hS]
      simp only [Finset.mem_univ, if_true, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      split_ifs with hij
      · subst hij; try simp only [hcb]; field_simp; ring
      · try simp only [hcb]; field_simp; ring

theorem hermHb_self (v : Fin (k + 1) → ℂ) :
    herm (Hb k) v v = ((∑ l : Fin k, Complex.normSq (v l.castSucc) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by
  unfold herm
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [Hb, Matrix.mulVec_diagonal, Fin.castSucc_ne_last, if_false, if_true, Pi.star_apply, Complex.star_def]
  push_cast [Complex.normSq_eq_conj_mul_self]
  ring

theorem emb_mulVec_out (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) : (embWb k r μ *ᵥ v) i = v i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · unfold embWb
    rw [dite_eq_right (by omega), if_pos ⟨rfl, by omega⟩, one_mul]
  · intro l _ hl
    unfold embWb
    rw [dite_eq_right (by omega), if_neg (fun h => hl h.1.symm), zero_mul]
  · simp

theorem wLast_inWb (s : ℂ) : inWb k r (s • wLast k r) := by
  intro i hi
  have : i ≠ wI k r (Fin.last k) := by
    intro h; have := congrArg Fin.val h; simp only [wI, Fin.val_last] at this; omega
  simp [wLast, bvec, Pi.single_apply, this]

theorem wbPart_wLast (s : ℂ) (m : Fin (k + 1)) :
    wbPart k r (s • wLast k r) m = if m = Fin.last k then s else 0 := by
  simp only [wbPart, wLast, bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : m = Fin.last k
  · subst h; simp
  · rw [if_neg (fun h' => h (wI_injective h')), if_neg h, mul_zero]

theorem transW : TransW := by
  intro k r z hz hT
  set T := Tz k r z with hTdef
  set s : ℝ := Real.sqrt T with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hss : s * s = T := Real.mul_self_sqrt hT.le
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  set u : Fin (k + 1) → ℂ := fun j => z (wI k r j) / s with hu
  set y : Fin k → ℂ := fun l => u l.castSucc with hy
  set c : ℂ := u (Fin.last k) with hcdef

  have hTform : T = Complex.normSq (z (wI k r (Fin.last k))) - ∑ l : Fin k, Complex.normSq (z (wI k r l.castSucc)) := by
    rw [hTdef, Tz, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]
    simp only [wbPart]; ring
  have hnq : ∀ a : ℂ, Complex.normSq (a / s) = Complex.normSq a / T := by
    intro a; rw [Complex.normSq_div, Complex.normSq_ofReal, hss]
  have hBA : Complex.normSq c - ∑ l : Fin k, Complex.normSq (y l) = 1 := by
    simp only [hcdef, hy, hu, hnq]
    rw [← Finset.sum_div, ← sub_div, ← hTform, div_self hT.ne']
  have hA0 : 0 ≤ ∑ l : Fin k, Complex.normSq (y l) := Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hBA; linarith
  have hS : ∑ l, conj (y l) * y l = ((‖c‖ : ℝ) : ℂ) ^ 2 - 1 := by
    have e1 : ∑ l, conj (y l) * y l = ((∑ l : Fin k, Complex.normSq (y l) : ℝ) : ℂ) := by
      push_cast [Complex.normSq_eq_conj_mul_self]; rfl
    have e2 : (‖c‖ : ℝ) ^ 2 = Complex.normSq c := (Complex.normSq_eq_norm_sq c).symm
    have hA : ∑ l : Fin k, Complex.normSq (y l) = Complex.normSq c - 1 := by linarith
    rw [e1, ← Complex.ofReal_pow, e2, hA]
    push_cast; ring
  refine ⟨embWb k r (boost y c), MB.emb_mem_UWb (boost_mem y c hS hc0), ?_⟩
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [emb_mulVec_out _ _ i hi, wLast_inWb _ i hi, hz i hi]
  · push Not at hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin (k + 1), wI k r j = i :=
      ⟨⟨i.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
    have e := congrFun (wbPart_emb (boost y c) _ (wLast_inWb (k := k) (r := r) (s : ℂ))) j
    simp only [wbPart] at e
    rw [e, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last k)]
    · have hb : boost y c j (Fin.last k) = u j := by
        induction j using Fin.lastCases with
        | last => simp [boost, hcdef]
        | cast j' => simp [boost, hy]
      have hw := wbPart_wLast (k := k) (r := r) (s : ℂ) (Fin.last k)
      rw [hb, hw, if_pos rfl]
      simp only [hu]
      field_simp
    · intro m _ hm
      have hw := wbPart_wLast (k := k) (r := r) (s : ℂ) m
      rw [hw, if_neg hm, mul_zero]
    · simp

end PI.RhsWLim.W
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim HU

variable {k r : ℕ}

def BallConj : Prop :=
  ∀ (k r : ℕ) (ρ : ℝ) (q : Mat k r), q ∈ UWb k r → qᴴ * q = 1 →
    rmulM q ⁻¹' bBall k r ρ ⊆ lmulM q ⁻¹' bBall k r ρ

def rmulE (p : Mat k r) (hp : IsUnit p.det) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulM p
  invFun := rmulM p⁻¹
  left_inv x := by
    show (Matrix.of x * p) * p⁻¹ = x
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hp, Matrix.mul_one]; rfl
  right_inv x := by
    show (Matrix.of x * p⁻¹) * p = x
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.mul_one]; rfl
  measurable_toFun := rmulM_meas p
  measurable_invFun := rmulM_meas p⁻¹

theorem lr_comm (s p : Mat k r) : lmulM s ∘ rmulM p = rmulM p ∘ lmulM s := by
  funext x
  show s * (Matrix.of x * p) = (s * Matrix.of x) * p
  rw [Matrix.mul_assoc]

theorem rmul_haar (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r) :
    IsHaarOn (UWb k r) (ν.map (rmulM p)) := by
  obtain ⟨hσ, h0, hc, hl⟩ := hH
  have hu := uwb_unit hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rmulE p hu).sigmaFinite_map
  · rw [Ne, Measure.map_eq_zero_iff (rmulM_meas p).aemeasurable]; exact h0
  · have hms : MeasurableSet {x : Mt k r | Matrix.of x ∉ UWb k r} := amb_closed.isOpen_compl.measurableSet
    rw [Measure.map_apply (rmulM_meas p) hms]
    refine measure_mono_null (fun x hx => ?_) hc
    intro hxm
    apply hx
    show Matrix.of x * p ∈ UWb k r
    exact uwb_mul hxm hp
  · intro s hs
    rw [Measure.map_map (lmulM_cont s).measurable (rmulM_meas p), lr_comm,
      ← Measure.map_map (rmulM_meas p) (lmulM_cont s).measurable, hl s hs]

theorem gauge_ball (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) :
    ∃ ρ : ℝ, 0 < ν (bBall k r ρ) ∧ ν (bBall k r ρ) < ⊤ := by
  have h := hG.2.eventually_const_lt (show (0 : ℝ) < 1 from one_pos)
  obtain ⟨ρ, hρ⟩ := h.exists
  refine ⟨ρ, ?_, ?_⟩
  · rcases eq_or_ne (ν (bBall k r ρ)) 0 with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact pos_iff_ne_zero.2 h0
  · rcases eq_or_ne (ν (bBall k r ρ)) ⊤ with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact lt_top_iff_ne_top.2 h0

theorem rmul_scale (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r)
    (s : Set (Mt k r)) (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) :
    ν.map (rmulM p) = (ν.map (rmulM p) s / ν s) • ν := by
  have h1 := rmul_haar ν hH p hp
  obtain ⟨hσ1, h01, hc1, hl1⟩ := h1
  obtain ⟨hσ2, h02, hc2, hl2⟩ := hH
  have i1 : SigmaFinite (pull (ν.map (rmulM p))) := pull_sigmaFinite _
  have i2 : SigmaFinite (pull ν) := pull_sigmaFinite ν
  have i3 : (pull (ν.map (rmulM p))).IsMulLeftInvariant := pull_left _ hl1
  have i4 : (pull ν).IsMulLeftInvariant := pull_left ν hl2
  have key := measure_eq_div_smul (pull (ν.map (rmulM p))) (pull ν) (s := inc ⁻¹' s)
    (by rw [pull_apply ν hc2]; exact h0) (by rw [pull_apply ν hc2]; exact ht)
  calc ν.map (rmulM p) = (pull (ν.map (rmulM p))).map inc := (map_pull _ hc1).symm
    _ = ((pull (ν.map (rmulM p)) (inc ⁻¹' s) / pull ν (inc ⁻¹' s)) • pull ν).map inc := by rw [← key]
    _ = _ := by rw [Measure.map_smul _ inc_cont.measurable.aemeasurable, map_pull ν hc2, pull_apply _ hc1, pull_apply ν hc2]

theorem one_of_le (c c' : ℝ≥0∞) (h : c * c' = 1) (hc : c ≤ 1) (hc' : c' ≤ 1) : c = 1 := by
  refine le_antisymm hc ?_
  calc 1 = c * c' := h.symm
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

theorem one_of_sq (c : ℝ≥0∞) (h : c * c = 1) : c = 1 := by
  rcases le_total c 1 with hc | hc
  · exact one_of_le c c h hc hc
  · refine le_antisymm ?_ hc
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * c := by gcongr
      _ = 1 := h

theorem map_rmul_one (ν : Measure (Mt k r)) : ν.map (rmulM (1 : Mat k r)) = ν := by
  have : (rmulM (1 : Mat k r) : Mt k r → Mt k r) = id := by
    funext x; unfold rmulM; rw [Matrix.mul_one]; rfl
  rw [this, Measure.map_id]

theorem scale_mul_one (ν : Measure (Mt k r)) (p p' : Mat k r) (hpp : p * p' = 1) (s : Set (Mt k r))
    (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) (c c' : ℝ≥0∞) (hc : ν.map (rmulM p) = c • ν)
    (hc' : ν.map (rmulM p') = c' • ν) : c * c' = 1 := by
  have e : ν = (c * c') • ν := by
    calc ν = ν.map (rmulM (p * p')) := by rw [hpp, map_rmul_one]
      _ = (ν.map (rmulM p)).map (rmulM p') := by
          rw [Measure.map_map (rmulM_meas p') (rmulM_meas p), rmulM_comp]
      _ = (c * c') • ν := by rw [hc, Measure.map_smul _ (rmulM_meas p').aemeasurable, hc', smul_smul]
  have e2 := congrArg (fun m : Measure (Mt k r) => m s) e
  simp only [Measure.smul_apply, smul_eq_mul] at e2
  exact (ENNReal.mul_left_inj h0 ht).1 (show (c * c') * ν s = 1 * ν s by rw [one_mul]; exact e2.symm)

theorem unitInv_of (hB : BallConj) : UnitInv := by
  intro k r ν hk hG q hq hqu
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  have hs : MeasurableSet (bBall k r ρ) := measurableSet_expBall k r (UWb k r) ρ
  have hu := uwb_unit hq
  have hqi : q⁻¹ = qᴴ := Matrix.inv_eq_left_inv hqu
  have hq' : qᴴ ∈ UWb k r := by rw [← hqi]; exact uwb_inv hq
  have hqu' : (qᴴ)ᴴ * qᴴ = 1 := by rw [conjTranspose_conjTranspose, ← hqi, Matrix.mul_nonsing_inv _ hu]
  have le1 : ∀ q : Mat k r, q ∈ UWb k r → qᴴ * q = 1 → ν.map (rmulM q) (bBall k r ρ) ≤ ν (bBall k r ρ) := by
    intro q hq hqu
    rw [Measure.map_apply (rmulM_meas q) hs]
    calc ν (rmulM q ⁻¹' bBall k r ρ) ≤ ν (lmulM q ⁻¹' bBall k r ρ) := measure_mono (hB k r ρ q hq hqu)
      _ = ν.map (lmulM q) (bBall k r ρ) := (Measure.map_apply (lmulM_cont q).measurable hs).symm
      _ = ν (bBall k r ρ) := by rw [hG.1.2.2.2 q hq]
  have hsc := rmul_scale ν hG.1 q hq _ h0.ne' ht.ne
  have hsc' := rmul_scale ν hG.1 qᴴ hq' _ h0.ne' ht.ne
  have hm := scale_mul_one ν q qᴴ (by rw [← hqi, Matrix.mul_nonsing_inv _ hu]) _ h0.ne' ht.ne _ _ hsc hsc'
  have hc1 : ν.map (rmulM q) (bBall k r ρ) / ν (bBall k r ρ) ≤ 1 :=
    (ENNReal.div_le_iff h0.ne' ht.ne).2 (by rw [one_mul]; exact le1 q hq hqu)
  have hc1' : ν.map (rmulM qᴴ) (bBall k r ρ) / ν (bBall k r ρ) ≤ 1 :=
    (ENNReal.div_le_iff h0.ne' ht.ne).2 (by rw [one_mul]; exact le1 qᴴ hq' hqu')
  rw [hsc, one_of_le _ _ hm hc1 hc1', one_smul]

theorem hb_sq (k : ℕ) : Hb k * Hb k = 1 := by
  rw [Hb, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> norm_num

theorem hermInv_of (hU : UnitInv) : HermInv := by
  intro k r ν hk hG B₀ hB hBh
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  have hE : embWb k r (Hb k) ∈ UWb k r := MB.emb_mem_UWb (by rw [hHbh, hb_sq, Matrix.one_mul])
  have hEu : (embWb k r (Hb k))ᴴ * embWb k r (Hb k) = 1 := by
    rw [MB.emb_conjT, hHbh, ← MB.emb_mul, hb_sq, MB.emb_one]
  have hBm : embWb k r B₀ ∈ UWb k r := MB.emb_mem_UWb hB
  have hinv : embWb k r B₀ * (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k)) = 1 := by
    rw [← MB.emb_mul, ← MB.emb_mul, ← MB.emb_mul]
    have : B₀ * (Hb k * B₀ * Hb k) = 1 := by
      calc B₀ * (Hb k * B₀ * Hb k) = (B₀ᴴ * Hb k * B₀) * Hb k := by rw [hBh]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hB, hb_sq]
    rw [this, MB.emb_one]
  have hEinv := hU k r ν hk hG _ hE hEu
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  have hsc := rmul_scale ν hG.1 _ hBm _ h0.ne' ht.ne
  set c := ν.map (rmulM (embWb k r B₀)) (bBall k r ρ) / ν (bBall k r ρ) with hc
  have h2 : ν.map (rmulM (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k))) = c • ν := by
    rw [← rmulM_comp, ← rmulM_comp, ← Measure.map_map (rmulM_meas _) ((rmulM_meas _).comp (rmulM_meas _)),
      ← Measure.map_map (rmulM_meas _) (rmulM_meas _), hEinv, hsc, Measure.map_smul _ (rmulM_meas _).aemeasurable, hEinv]
  have hcc := scale_mul_one ν _ _ hinv _ h0.ne' ht.ne c c hsc h2
  rw [hsc, one_of_sq c hcc, one_smul]

theorem unimodW_of_two (hB : BallConj) (hP : PolarDecW) : UnimodW :=
  unimodW_of (unitInv_of hB) (hermInv_of (unitInv_of hB)) hP

end PI.RhsWLim.W
end
end
