module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HpkMulVecMulVec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
public import Formalism.HermitianCurvature.StatementB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Bundle001
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
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core

open Formalism.QuantumDeterminants

section hpk

variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  apply ReciprocityTheory.ChartRestriction.DS.Mult1.TopH.hpk_mulVec <;> assumption

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have h' : (2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := by omega
    rw [hpk_mulVec, if_pos h, hpk_mulVec, if_pos h']
    congr 1
    ext
    simp only
    omega
  · rw [hpk_mulVec, if_neg h, hpk_mulVec, if_neg h]
    split_ifs <;> simp

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

end hpk

theorem inv_mul_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r * Hpk k r := by rw [hg']
    _ = 1 := hpk_sq k r

theorem mul_inv_UH (k r : ℕ) {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h := inv_mul_UH k r hg
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h)

theorem mul_mem_UH (k r : ℕ) {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem inv_mem_UH (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have e := mul_inv_UH k r hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e]; simp

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Core
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.IntS

open Formalism.QuantumDeterminants

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN g = ‖g‖ := by
  rw [frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le' {k r : ℕ} (A B : Mat k r) :
    Formalism.FourierDecayAlt.B.gN (A * B) ≤ Formalism.FourierDecayAlt.B.gN A * Formalism.FourierDecayAlt.B.gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

theorem gN_pos_of_ne {k r : ℕ} {g : Mat k r} (hg : g ≠ 0) : 0 < Formalism.FourierDecayAlt.B.gN g := by
  rw [gN_eq_frob]; exact norm_pos_iff.mpr hg

end frob

theorem gN_nonneg' {k r : ℕ} (g : Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem gN_continuous (k r : ℕ) : Continuous (fun g : Mat k r => Formalism.FourierDecayAlt.B.gN g) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_out k r h j

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mid k r h j

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec k r v i

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec_mulVec k r v

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_sq k r

variable {k r}

theorem UH_left_inv {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : Hpk k r * gᴴ * Hpk k r * g = 1 :=
  ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_left_inv k r hg

theorem UH_mul_inv {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h1 : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (UH_left_inv hg)
  exact mul_eq_one_comm.mp (by rw [h1, UH_left_inv hg])

theorem UH_mul {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem ne_zero_of_mem_UH {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g ≠ 0 := by
  intro h
  have := UH_mul_inv hg
  rw [h, Matrix.zero_mul] at this
  exact zero_ne_one this

end hpk

theorem orbit_bound (k r : ℕ) (x₀ s x : Mat k r) (hx₀ : x₀ ∈ UH (Hpk k r)) (hs : s ∈ UH (Hpk k r))
    (hx : x ∈ UH (Hpk k r)) (b : ℝ) (hb : 0 ≤ b) :
    Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (s * x)) ^ (-b) ≤
      (Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b * Formalism.FourierDecayAlt.B.gN s ^ (-b) := by
  set y := x₀⁻¹ * (s * x) with hy
  have hsy : x₀ * y * x⁻¹ = s := by
    rw [hy, ← Matrix.mul_assoc x₀, UH_mul_inv hx₀, Matrix.one_mul, Matrix.mul_assoc, UH_mul_inv hx,
      Matrix.mul_one]
  have hs0 : 0 < Formalism.FourierDecayAlt.B.gN s := gN_pos_of_ne (ne_zero_of_mem_UH hs)
  have hyne : y ≠ 0 := by
    intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at hsy
    exact ne_zero_of_mem_UH hs hsy.symm
  have hy0 : 0 < Formalism.FourierDecayAlt.B.gN y := gN_pos_of_ne hyne
  set A := Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹ with hA
  have hle : Formalism.FourierDecayAlt.B.gN s ≤ A * Formalism.FourierDecayAlt.B.gN y := by
    rw [← hsy]
    calc Formalism.FourierDecayAlt.B.gN (x₀ * y * x⁻¹) ≤ Formalism.FourierDecayAlt.B.gN (x₀ * y) * Formalism.FourierDecayAlt.B.gN x⁻¹ := gN_mul_le' _ _
      _ ≤ Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN x⁻¹ :=
          mul_le_mul_of_nonneg_right (gN_mul_le' _ _) (gN_nonneg' _)
      _ = A * Formalism.FourierDecayAlt.B.gN y := by rw [hA]; ring
  have hA0 : 0 < A := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hy0.le]
  have hpow : Formalism.FourierDecayAlt.B.gN s ^ b ≤ A ^ b * Formalism.FourierDecayAlt.B.gN y ^ b := by
    rw [← Real.mul_rpow hA0.le hy0.le]
    exact Real.rpow_le_rpow hs0.le hle hb
  have hSb : 0 < Formalism.FourierDecayAlt.B.gN s ^ b := Real.rpow_pos_of_pos hs0 b
  have hYb : 0 < Formalism.FourierDecayAlt.B.gN y ^ b := Real.rpow_pos_of_pos hy0 b
  rw [Real.rpow_neg hy0.le, Real.rpow_neg hs0.le, ← div_eq_mul_inv, le_div_iff₀ hSb,
    inv_mul_le_iff₀ hYb]
  linarith [mul_comm (A ^ b) (Formalism.FourierDecayAlt.B.gN y ^ b)]

theorem bS_nonneg (k r : ℕ) : 0 ≤ bS k r := by
  unfold bS nS; positivity

theorem bS_le_bS (k r : ℕ) : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r ≤ bS k r :=
  le_of_le_of_eq (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS_le k r) (by unfold bS nS ReciprocityTheory.ChartRestriction.DS.Mult1.nR; rfl)

theorem intS_of_sIntFin (h : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.SIntFin) : IntSStatement := by
  intro k r z μW μN hz hT hW hN x₀ hx₀ x hx b hb
  have hb0 : 0 ≤ b := le_trans (bS_nonneg k r) hb.le
  have hb1 : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r < b := lt_of_le_of_lt (bS_le_bS k r) hb
  have hfin := (h k r z μW μN hz hT hW hN b hb1).1
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hcont : Continuous (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x))) :=
    (gN_continuous k r).comp (continuous_const.matrix_mul
      ((continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_const))
  have hmeas : Measurable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) :=
    hcont.measurable.pow_const _
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
        {y : Mt k r | Matrix.of y ∉ UWset k r z} ×ˢ (Set.univ : Set (Mt k r)) := by
      ext p; simp
    rw [e, Measure.prod_prod, hW.2.2.1, zero_mul]
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.2 ∈ Nset k r} =
        (Set.univ : Set (Mt k r)) ×ˢ {y : Mt k r | Matrix.of y ∉ Nset k r} := by
      ext p; simp
    rw [e, Measure.prod_prod, hN.2.2.1, mul_zero]
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (gN_nonneg' _) _)]
  calc ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) ∂(μW.prod μN)
      ≤ ∫⁻ p, ENNReal.ofReal ((Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b) *
          ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN) := by
        refine lintegral_mono_ae ((h1.and h2).mono fun p hp => ?_)
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (gN_nonneg' _) (gN_nonneg' _)) _)]
        exact ENNReal.ofReal_le_ofReal
          (orbit_bound k r x₀ _ x hx₀ (UH_mul hp.1.1 hp.2.1) hx b hb0)
    _ = ENNReal.ofReal ((Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b) *
          ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.IntS
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec

open Formalism.QuantumDeterminants

theorem one_le_gN (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : 1 ≤ Formalism.FourierDecayAlt.B.gN g :=
  DecA.one_le_gN' hg

theorem of_cont (k r : ℕ) : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) :=
  continuous_matrix fun i j => by
    simp only [Matrix.of_apply]; exact (continuous_apply j).comp (continuous_apply i)

theorem gN_cont (k r : ℕ) : Continuous (fun M : Mat k r => Formalism.FourierDecayAlt.B.gN M) := by
  unfold Formalism.FourierDecayAlt.B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

theorem UW_inv_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hinv : h⁻¹ * h = 1 := DecA.inv_mul hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨DecA.inv_mem hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem UH_closed (k r : ℕ) : IsClosed (UH (Hpk k r) : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem UW_closed (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have e : UWset k r z = UH (Hpk k r) ∩ ((⋂ a : Fin r, ({g : Mat k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
      {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ z = z}) := by
    ext g; simp only [UWset, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact (UH_closed k r).inter ((isClosed_iInter fun a =>
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)).inter
    (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const))

theorem psiGen_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (fun M : Mat k r => Formalism.MainNotions.S.psiGen k r z c M) := by
  have hell : ∀ a : Fin r, Continuous (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) := by
    intro a
    by_cases h : a.val + 1 < r
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) =
          fun M : Mat k r => M (eI k r a) (eI k r ⟨a.val + 1, h⟩) :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dite_eq_left h]
      rw [e]; exact continuous_id.matrix_elem _ _
    · have e : (fun M : Mat k r => Formalism.MainNotions.S.ellA k r z M a) = fun M : Mat k r => ∑ j, M (eI k r a) j * z j :=
        funext fun M => by unfold Formalism.MainNotions.S.ellA; rw [dite_eq_right h]; rfl
      rw [e]; exact continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const
  unfold Formalism.MainNotions.S.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (hell a)))))

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec
end
end
