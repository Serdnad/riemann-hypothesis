module

public import Formalism.PeriodIntegrals.Bundle028
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.Development
public import Development.AutomorphicArithmetic.OrbitLabellings.SumLogMulMaxZeroLeOfOddAddOrderOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.PrimeWeightedRemainderBound
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Formalism.GaussJetBounds.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace UpperTheory.G2

open Formalism.BasicNotions Formalism.MainNotions.G PI.SzEatI.W

theorem szEatI_of_stepA (hA : StepA) : PI.SzEatI.SzEatI := by
  classical
  intro K ce eps Ct CGam Cc CT2 PK
  obtain ⟨x0, hx0⟩ := hA K eps
  obtain ⟨C, hC, x1, hx1⟩ := UpperTheory.sum_log_mul_max_zero_le_of_odd_addOrderOf ce eps Ct CGam Cc CT2 PK
  have hc1 : 0 ≤ c1 ce := by unfold c1; positivity
  refine ⟨c1 ce + 1 + C, by positivity, max x0 x1, ?_⟩
  intro D L P hU hx hSz j hj S hS
  obtain ⟨hbb, hR0, hYR, hY1, hlog⟩ := hx0 D L hU.1 (le_trans (le_max_left _ _) hx) hSz
  have hX := hx1 D L P hU (le_trans (le_max_right _ _) hx) hSz j hj (S.filter fun p => IsCs D p) (by
    intro p hp
    obtain ⟨hpS, hcs⟩ := Finset.mem_filter.1 hp
    exact ⟨(hS p hpS).1, hcs.1, hcs.2.1, (hS p hpS).2.2.2⟩)
  have hXs : ∑ p ∈ S, Real.log p * EatX L ce j p ≤
      C * (D.R.f : ℝ) * L.sc.b * Real.log (L.sc.X'' D.R.n) := by
    refine le_trans ?_ hX
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    unfold EatX
    split_ifs
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.log_natCast_nonneg p)
    · simp
  set Y := L.sc.X'' D.R.n with hYdef
  set f : ℝ := (D.R.f : ℝ) with hfdef
  have hf : 0 ≤ f := Nat.cast_nonneg _
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hpt : ∀ p ∈ S, Real.log p * (EatI L K ce j p -
      max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))) ≤
      c1 ce * f * L.sc.b * (Real.log p / p) + f * Rt L K + Real.log p * EatX L ce j p := by
    intro p hp
    obtain ⟨hpr, -, -, hpY⟩ := hS p hp
    have h := prime_weighted_remainder_bound K ce D L hSz hbb j hj p hpr hpY
    unfold rest at h
    rw [mul_sub] at h
    linarith
  have hM : ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y :=
    sum_log_p_over_p Y hY1 S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2.2⟩)
  have hcard : (S.card : ℝ) ≤ Y :=
    card_le_of_le S Y (by linarith) (fun p hp => ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2.2⟩)
  calc ∑ p ∈ S, Real.log p * (EatI L K ce j p -
        max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)))
      ≤ ∑ p ∈ S, (c1 ce * f * L.sc.b * (Real.log p / p) + f * Rt L K + Real.log p * EatX L ce j p) :=
        Finset.sum_le_sum hpt
    _ = c1 ce * f * L.sc.b * (∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ)) + (S.card : ℝ) * (f * Rt L K) +
          ∑ p ∈ S, Real.log p * EatX L ce j p := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ c1 ce * f * L.sc.b * Real.log Y + Y * (f * Rt L K) + C * f * L.sc.b * Real.log Y := by
        have h0 : 0 ≤ c1 ce * f * L.sc.b := mul_nonneg (mul_nonneg hc1 hf) hb
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hM h0)
          (mul_le_mul_of_nonneg_right hcard (mul_nonneg hf hR0))) hXs
    _ = c1 ce * f * L.sc.b * Real.log Y + f * (Y * Rt L K) + C * f * L.sc.b * Real.log Y := by ring
    _ ≤ c1 ce * f * L.sc.b * Real.log Y + f * (L.sc.b * Real.log Y) + C * f * L.sc.b * Real.log Y := by
        refine add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hf)) le_rfl
        calc Y * Rt L K ≤ L.sc.b := hYR
          _ = L.sc.b * 1 := by ring
          _ ≤ L.sc.b * Real.log Y := mul_le_mul_of_nonneg_left hlog hb
    _ = (c1 ce + 1 + C) * f * L.sc.b * Real.log Y := by ring

end UpperTheory.G2
end
end

section

open scoped BigOperators

namespace UpperTheory.ColumnLengthWeights

open Formalism.MainNotions.product_zeroth_first_parts

private theorem card_eq_sum_colLen (μ : YoungDiagram) :
    μ.cells.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.range (μ.rowLen 0))]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => (μ.cells.filter fun c => c.2 = j).card)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [YoungDiagram.colLen_eq_card]
    rfl
  · rintro ⟨i, j⟩ h
    rw [Finset.mem_coe, Finset.mem_range]
    have h0 : (0, j) ∈ μ := μ.up_left_mem (Nat.zero_le i) le_rfl (Finset.mem_coe.mp h)
    exact YoungDiagram.mem_iff_lt_rowLen.mp h0

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (a : Lt → ℕ)

private def wt : XZ Lt N0 N1 → ℕ := Sum.elim (fun _ => 0) (fun z => a z.1)

omit [Fintype Lt] [DecidableEq Lt] in
private theorem minorXZ_hom (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (minorXZ N0 N1 s p I) (p • a s) := by
  have hent : ∀ i k : Fin p, MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a)
      (∑ b : Fin N0, MvPolynomial.X (Sum.inl (s, (i : ℕ), b)) * MvPolynomial.X (Sum.inr (s, b, I k)) :
        MvPolynomial (XZ Lt N0 N1) ℤ) (a s) := by
    intro i k
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inl (s, (i : ℕ), b))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inr (s, b, I k)))
    simpa only [wt, Sum.elim_inl, Sum.elim_inr, zero_add] using this
  unfold minorXZ
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ (wt N0 N1 a) _)
  have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun _ => a s)
    (fun i _ => hent (σ i) i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

omit [DecidableEq Lt] in
private theorem Gxz_hom (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (Gxz N0 N1 nu I)
      (∑ s, (nu s).cells.card • a s) := by
  unfold Gxz
  have h := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun s => ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen (c : ℕ)) (I s c))
    (fun s => ∑ c : Fin ((nu s).rowLen 0), (nu s).colLen (c : ℕ) • a s)
    (fun s _ => MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _
      (fun c _ => minorXZ_hom N0 N1 a s _ (I s c)))
  convert h using 2 with s
  rw [← Finset.sum_smul, card_eq_sum_colLen]

private theorem deg_of_mem_support (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) (μ : XZ Lt N0 N1 →₀ ℕ)
    (hμ : μ ∈ (Gxz N0 N1 nu I).support) (t : Lt) :
    ∑ ab : Fin N0 × Fin N1, (Finsupp.sumFinsuppEquivProdFinsupp μ).2 (t, ab) = (nu t).cells.card := by
  classical
  set a : Lt → ℕ := fun z => if z = t then 1 else 0 with ha
  have hw := Gxz_hom N0 N1 a nu I (MvPolynomial.mem_support_iff.mp hμ)
  have hr : ∑ s, (nu s).cells.card • a s = (nu t).cells.card := by
    rw [Finset.sum_eq_single t]
    · simp [ha]
    · intro b _ hb
      simp [ha, hb]
    · simp
  set T : Finset (XZ Lt N0 N1) := Finset.univ.map
    ⟨fun ab : Fin N0 × Fin N1 => (Sum.inr (t, ab) : XZ Lt N0 N1), fun x y h => by simpa using h⟩ with hT
  have hwt : Finsupp.weight (wt N0 N1 a) μ = ∑ ab : Fin N0 × Fin N1, μ (Sum.inr (t, ab)) := by
    rw [Finsupp.weight_apply,
      Finsupp.sum_of_support_subset μ (Finset.subset_union_left (s₂ := T)) _ (by simp)]
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := μ.support) (s₂ := T))]
    · rw [hT, Finset.sum_map]
      refine Finset.sum_congr rfl fun ab _ => ?_
      change μ (Sum.inr (t, ab)) • wt N0 N1 a (Sum.inr (t, ab)) = μ (Sum.inr (t, ab))
      simp [wt, ha]
    · intro x _ hx
      cases x with
      | inl y => simp [wt]
      | inr z =>
        obtain ⟨t', ab⟩ := z
        have hne : t' ≠ t := by
          rintro rfl
          exact hx (Finset.mem_map.mpr ⟨ab, Finset.mem_univ _, rfl⟩)
        simp [wt, ha, hne]
  simp only [Finsupp.snd_sumFinsuppEquivProdFinsupp]
  rw [← hwt, hw, hr]

end UpperTheory.ColumnLengthWeights

open UpperTheory.ColumnLengthWeights in
theorem UpperTheory.kvalGe_of_norm_mfact_mul_coeff_le :
    ∀ (l : ℕ) [Fact l.Prime] (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ),
    (∀ κ : Lt × Fin N0 × Fin N1 →₀ ℕ, (∀ t, ∑ ab : Fin N0 × Fin N1, κ (t, ab) = (nu t).cells.card) →
      ‖((Formalism.DworkPowerSeriesWeights.mfact κ : ℕ) : ℂ_[l]) * MvPowerSeries.coeff κ Th‖ ≤ (l : ℝ) ^ (-B)) →
    Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B := by
  intro l _ Lt _ _ N0 N1 nu Th B h I m
  classical
  have hpos : (0 : ℝ) ≤ (l : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg l) _
  unfold Formalism.MainNotions.product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos fun μ hμ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs with hm
  · have h1 := h _ (deg_of_mem_support N0 N1 nu I μ hμ)
    have h2 : ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) =
        ((Formalism.DworkPowerSeriesWeights.mfact (Finsupp.sumFinsuppEquivProdFinsupp μ).2 : ℕ) : ℂ_[l]) := by
      unfold Formalism.DworkPowerSeriesWeights.mfact Finsupp.prod
      rw [Nat.cast_prod]
    rw [h2, mul_assoc, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)).trans h1
  · rw [norm_zero]; exact hpos
end
