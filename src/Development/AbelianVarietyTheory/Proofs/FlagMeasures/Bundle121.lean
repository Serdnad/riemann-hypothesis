module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle103
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis
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
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Formalism.REAL (Jm UJ inUJ hs muG Jm_mul_self Jm_conjTranspose)

noncomputable section

namespace GlobalTheory.LeviIso

def haarLoc (j : ℕ) : Measure (Fin j → Fin j → ℂ) :=
  (volume : Measure (Fin j → Fin j → ℂ)).withDensity
    fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)

instance (j : ℕ) : SigmaFinite (haarLoc j) := by
  unfold haarLoc
  infer_instance

instance sigmaFinite_ofReal_smul {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : ℝ) :
    SigmaFinite (ENNReal.ofReal c • μ) :=
  inferInstanceAs (SigmaFinite (c.toNNReal • μ))

def IsRadial {X : Type} [MeasurableSpace X] (μ : Measure X) (q : X → ℝ) (d : ℕ) : Prop :=
  Filter.Tendsto (fun r : ℝ => μ {x | Real.sqrt (q x) ≤ r} / ENNReal.ofReal (r ^ d))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

variable {n n₀ a : ℕ} {j : Fin a → ℕ}

def SpansFlag (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ k y, y ∈ W k ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧ y = ∑ i, B i *ᵥ u i

def IsFrame (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (B₀ : Matrix (Fin n) (Fin n₀) ℂ) : Prop :=
  (∀ i, (B i)ᴴ * B i = 1) ∧ (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) ∧ (∀ i k, (B i)ᴴ * Jm ε * B k = 0) ∧
    (∀ i, (B i)ᴴ * B₀ = 0) ∧ B₀ᴴ * B₀ = 1 ∧ Jm ε * B₀ = B₀ * Jm ε₀ ∧
    ∑ i, B i * (B i)ᴴ + ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε + B₀ * B₀ᴴ = 1

def lev (ε : Fin n → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ)
    (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Matrix (Fin n₀) (Fin n₀) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, B i * x i * (B i)ᴴ + ∑ i, Jm ε * B i * (x i)⁻¹ᴴ * (B i)ᴴ * Jm ε + B₀ * g * B₀ᴴ

variable {ε : Fin n → Bool} {ε₀ : Fin n₀ → Bool} {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ}
  {B₀ : Matrix (Fin n) (Fin n₀) ℂ}

theorem IsFrame.J_B₀ (h : IsFrame ε ε₀ B B₀) (i : Fin a) : (B i)ᴴ * Jm ε * B₀ = 0 := by
  rw [Matrix.mul_assoc, h.2.2.2.2.2.1, ← Matrix.mul_assoc, h.2.2.2.1 i, Matrix.zero_mul]

theorem IsFrame.B₀_B (h : IsFrame ε ε₀ B B₀) (i : Fin a) : B₀ᴴ * B i = 0 := by
  have e := congrArg Matrix.conjTranspose (h.2.2.2.1 i)
  simpa [Matrix.conjTranspose_mul] using e

theorem IsFrame.B₀_J (h : IsFrame ε ε₀ B B₀) (i : Fin a) : B₀ᴴ * Jm ε * B i = 0 := by
  have e := congrArg Matrix.conjTranspose (h.J_B₀ i)
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc] using e

theorem IsFrame.sum_mul (h : IsFrame ε ε₀ B B₀) {m : Type} (y : ∀ i, Matrix m (Fin (j i)) ℂ) (i : Fin a) :
    (∑ k, y k * (B k)ᴴ) * B i = y i := by
  rw [Matrix.sum_mul, Finset.sum_eq_single i]
  · rw [Matrix.mul_assoc, h.1 i, Matrix.mul_one]
  · intro k _ hk
    rw [Matrix.mul_assoc, h.2.1 k i hk, Matrix.mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable (x x' : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g g' : Matrix (Fin n₀) (Fin n₀) ℂ)

theorem IsFrame.lev_mul_B (h : IsFrame ε ε₀ B B₀) (i : Fin a) : lev ε B B₀ x g * B i = B i * x i := by
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B i) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.2.2.1 k i
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * B i = B i * x i := h.sum_mul (fun k => B k * x k) i
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * B i = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s3 : B₀ * g * B₀ᴴ * B i = 0 := by
    simp only [Matrix.mul_assoc, h.B₀_B i, Matrix.mul_zero]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, add_zero, add_zero]

theorem IsFrame.lev_mul_JB (h : IsFrame ε ε₀ B B₀) (i : Fin a) :
    lev ε B B₀ x g * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
  have hJJ : ∀ {m : Type} (M : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B i) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.2.2.1 k i
  have e₀ : B₀ᴴ * (Jm ε * B i) = 0 := by
    rw [← Matrix.mul_assoc]
    exact h.B₀_J i
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * (Jm ε * B i) = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
    rw [Matrix.sum_mul, Finset.sum_eq_single i]
    · simp only [Matrix.mul_assoc, hJJ, h.1 i, Matrix.mul_one]
    · intro k _ hk
      simp only [Matrix.mul_assoc, hJJ, h.2.1 k i hk, Matrix.mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have s3 : B₀ * g * B₀ᴴ * (Jm ε * B i) = 0 := by
    simp only [Matrix.mul_assoc, e₀, Matrix.mul_zero]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, zero_add, add_zero]

theorem IsFrame.lev_mul_B₀ (h : IsFrame ε ε₀ B B₀) : lev ε B B₀ x g * B₀ = B₀ * g := by
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B₀) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.J_B₀ k
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * B₀ = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by
      simp only [Matrix.mul_assoc, h.2.2.2.1 k, Matrix.mul_zero]
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * B₀ = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s3 : B₀ * g * B₀ᴴ * B₀ = B₀ * g := by
    simp only [Matrix.mul_assoc, h.2.2.2.2.1, Matrix.mul_one]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, zero_add, zero_add]

theorem IsFrame.ext (h : IsFrame ε ε₀ B B₀) {m : Type} {M N : Matrix m (Fin n) ℂ} (h1 : ∀ i, M * B i = N * B i)
    (h2 : ∀ i, M * (Jm ε * B i) = N * (Jm ε * B i)) (h3 : M * B₀ = N * B₀) : M = N := by
  have h2' : ∀ i, M * Jm ε * B i = N * Jm ε * B i := fun i => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h2 i]
  calc M = M * (1 : Matrix (Fin n) (Fin n) ℂ) := (Matrix.mul_one M).symm
    _ = N * (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← h.2.2.2.2.2.2]
      simp only [Matrix.mul_add, Matrix.mul_sum, ← Matrix.mul_assoc, h1, h2', h3]
    _ = N := Matrix.mul_one N

theorem IsFrame.lev_mul (h : IsFrame ε ε₀ B B₀) :
    lev ε B B₀ (fun i => x i * x' i) (g * g') = lev ε B B₀ x g * lev ε B B₀ x' g' := by
  refine h.ext (fun i => ?_) (fun i => ?_) ?_
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_B x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_B x g, h.lev_mul_B, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_JB x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_JB x g, h.lev_mul_JB]
    simp only [Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_B₀ x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_B₀ x g, h.lev_mul_B₀, Matrix.mul_assoc]

theorem lev_conjTranspose : (lev ε B B₀ x g)ᴴ = lev ε B B₀ (fun i => (x i)ᴴ) gᴴ := by
  unfold lev
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    Matrix.mul_assoc]

theorem IsFrame.inUJ_lev (h : IsFrame ε ε₀ B B₀) (hx : ∀ i, (x i).det ≠ 0) (hg : inUJ ε₀ g) :
    inUJ ε (lev ε B B₀ x g) := by
  have hl : ∀ i, (x i)⁻¹ * x i = 1 := fun i => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx i))
  have hr : ∀ i, (x i)ᴴ * ((x i)ᴴ)⁻¹ = 1 := fun i => by
    rw [← Matrix.conjTranspose_nonsing_inv, ← Matrix.conjTranspose_mul, hl i, Matrix.conjTranspose_one]
  have hJJ : ∀ {m : Type} (M : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hJ₀ : ∀ {m : Type} (M : Matrix (Fin n₀) m ℂ), Jm ε * (B₀ * M) = B₀ * (Jm ε₀ * M) := fun M => by
    rw [← Matrix.mul_assoc, h.2.2.2.2.2.1, Matrix.mul_assoc]
  have hg' : gᴴ * (Jm ε₀ * g) = Jm ε₀ := by
    rw [← Matrix.mul_assoc]
    exact hg
  have eB : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ) (i : Fin a)
      {m : Type} (M : Matrix (Fin (j i)) m ℂ), lev ε B B₀ y k * (B i * M) = B i * (y i * M) :=
    fun y k i {_} M => by rw [← Matrix.mul_assoc, h.lev_mul_B, Matrix.mul_assoc]
  have eJB : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ) (i : Fin a)
      {m : Type} (M : Matrix (Fin (j i)) m ℂ),
      lev ε B B₀ y k * (Jm ε * (B i * M)) = Jm ε * (B i * ((y i)⁻¹ᴴ * M)) :=
    fun y k i {_} M => by
      rw [← Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc, h.lev_mul_JB]
      simp only [Matrix.mul_assoc]
  have eB₀ : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ)
      {m : Type} (M : Matrix (Fin n₀) m ℂ), lev ε B B₀ y k * (B₀ * M) = B₀ * (k * M) :=
    fun y k {_} M => by rw [← Matrix.mul_assoc, h.lev_mul_B₀, Matrix.mul_assoc]
  show (lev ε B B₀ x g)ᴴ * Jm ε * lev ε B B₀ x g = Jm ε
  rw [lev_conjTranspose]
  refine h.ext (fun i => ?_) (fun i => ?_) ?_
  · simp only [Matrix.mul_assoc, h.lev_mul_B, eJB, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, hl, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, h.lev_mul_JB, hJJ, eB, Matrix.conjTranspose_nonsing_inv, hr,
      Matrix.mul_one]
  · simp only [Matrix.mul_assoc, h.lev_mul_B₀, hJ₀, eB₀, hg', h.2.2.2.2.2.1]

theorem IsFrame.lev_inj (h : IsFrame ε ε₀ B B₀) (e : lev ε B B₀ x g = lev ε B B₀ x' g') : x = x' ∧ g = g' := by
  have hB : ∀ i, B i * x i = B i * x' i := fun i => by
    rw [← h.lev_mul_B x g i, e, h.lev_mul_B]
  have hB₀ : B₀ * g = B₀ * g' := by
    rw [← h.lev_mul_B₀ x g, e, h.lev_mul_B₀]
  refine ⟨funext fun i => ?_, ?_⟩
  · have e' := congrArg ((B i)ᴴ * ·) (hB i)
    simpa [← Matrix.mul_assoc, h.1 i] using e'
  · have e' := congrArg (B₀ᴴ * ·) hB₀
    simpa [← Matrix.mul_assoc, h.2.2.2.2.1] using e'

def IsLeviChart (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ)
    (θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε) : Prop :=
  Measurable θ ∧
  (∀ m, m ∈ flagM ε W ↔ ∃ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) ∧ θ z = m) ∧
  (∀ z z' : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
    (∀ i, (Matrix.of (z'.1 i)).det ≠ 0) →
    θ z * θ z' = θ (fun i r s => (Matrix.of (z.1 i) * Matrix.of (z'.1 i)) r s, z.2 * z'.2) ∧
      (θ z = θ z' → z = z')) ∧
  (∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
    (∀ i, locSize j W (uMat (θ z)) i = ‖(Matrix.of (z.1 i)).det‖ ^ (-(1 : ℝ) / j i)) ∧
    ∀ g : UJ ε, (∀ i, uMat g * A i = A i * (Matrix.of (z.1 i)).map τ) → uMat g * A₀ = A₀ * (uMat z.2).map τ₀ →
      g * (θ z)⁻¹ ∈ flagN ε W) ∧
  ∀ (μ : Measure (UJ ε)) (c : ℝ), IsGaugeSub (flagM ε W) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) μ → IsGauge ε₀ c →
    μ = ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
      (ENNReal.ofReal c • muG ε₀)).map θ

end GlobalTheory.LeviIso
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SphereRatio

theorem sphV_succ (i : ℕ) : sphV (i + 1) = sphV i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) := by
  unfold sphV
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem sphV_pos (i : ℕ) : 0 < sphV i := by
  unfold sphV
  refine Finset.prod_pos fun l _ => ?_
  have := Real.pi_pos
  positivity

theorem le_exp : (32.5 : ℝ) ≤ Real.exp 3.49 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3.49 : ℝ)) (by norm_num) 10
  refine le_trans ?_ h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem sphV_add_le (m j : ℕ) : sphV (m + j) ≤ sphV m * Real.exp (3.49 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := GlobalTheory.zetaProd_sphereVolume_bounds.2.2 (m + j + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    have h2 := h.trans le_exp
    have hp := Real.pi_pos
    have hm := sphV_pos m
    rw [← add_assoc, sphV_succ]
    calc sphV (m + j) * (2 * Real.pi ^ (m + j + 1) / ((m + j).factorial : ℝ))
        ≤ (sphV m * Real.exp (3.49 * j)) * Real.exp 3.49 :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = sphV m * Real.exp (3.49 * ((j + 1 : ℕ) : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          push_cast
          ring_nf

theorem inv_sphV_le (J : ℕ) : (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  induction J with
  | zero => simp [sphV]
  | succ J ih =>
    have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi ^ (J + 1) := by
      have := one_le_pow₀ (n := J + 1) hp
      linarith
    have hf : (J.factorial : ℝ) ≤ (J : ℝ) ^ J := by exact_mod_cast Nat.factorial_le_pow J
    have h2 : (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹ ≤ (J : ℝ) ^ J := by
      rw [inv_div]
      exact (div_le_self (by positivity) h1).trans hf
    have he : (J + 1) * (J + 1 - 1) / 2 = J * (J - 1) / 2 + J := Nat.triangle_succ J
    have hJ := sphV_pos J
    rw [sphV_succ, mul_inv, he]
    calc (sphV J)⁻¹ * (2 * Real.pi ^ (J + 1) / (J.factorial : ℝ))⁻¹
        ≤ (J : ℝ) ^ (J * (J - 1) / 2) * (J : ℝ) ^ J :=
          mul_le_mul ih h2 (by positivity) (by positivity)
      _ = (J : ℝ) ^ (J * (J - 1) / 2 + J) := by rw [pow_add]
      _ ≤ ((J + 1 : ℕ) : ℝ) ^ (J * (J - 1) / 2 + J) :=
          pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _

end GlobalTheory.SphereRatio

theorem GlobalTheory.sphV_ratio_and_inv_bounds :
    (∀ q j : ℕ, j ≤ q → Real.log (sphV q / sphV (q - j)) ≤ 3.49 * j) ∧
      ∀ J : ℕ, 0 < sphV J ∧ (sphV J)⁻¹ ≤ (J : ℝ) ^ (J * (J - 1) / 2) := by
  refine ⟨fun q j h => ?_, fun J => ⟨GlobalTheory.SphereRatio.sphV_pos J, GlobalTheory.SphereRatio.inv_sphV_le J⟩⟩
  have h1 := GlobalTheory.SphereRatio.sphV_add_le (q - j) j
  rw [Nat.sub_add_cancel h] at h1
  have hq := GlobalTheory.SphereRatio.sphV_pos q
  have hm := GlobalTheory.SphereRatio.sphV_pos (q - j)
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hm, mul_comm]
  exact h1
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DensityIntegral

theorem integral_cube (a : ℕ) (c : Fin a → ℕ) (hc : ∀ i, 1 ≤ c i) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1), ∏ i, (c i : ℝ) * τ i ^ (c i - 1) = 1 := by
  rw [volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (i : Fin a) (t : ℝ) => (c i : ℝ) * t ^ (c i - 1))]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, integral_pow]
  obtain ⟨m, hm⟩ : ∃ m, c i = m + 1 := ⟨c i - 1, by have := hc i; omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel, one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, sub_zero]
  push_cast
  field_simp

theorem dens_le (n f a : ℕ) (j : Fin a → ℕ) (hf : 1 ≤ f) (hj : ∀ i, 1 ≤ j i) (hn : 2 * ∑ i, j i + 1 ≤ n)
    (τ : Fin a → ℝ) (hτ : τ ∈ simplexH a) :
    FlagMeas.dens n f j τ ≤ ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) := by
  have h2 := (GlobalTheory.Count.layerProd_count_mul_density_le_two n f (∑ i, j i) a j τ 0 le_rfl (by omega)
    hτ.1 hτ.2 le_rfl (by norm_num)).2
  have h3 : 0 ≤ ∏ i, 2 * (f : ℝ) * j i / τ i :=
    Finset.prod_nonneg fun i _ => by have := (hτ.2 i).1; positivity
  refine (mul_le_mul_of_nonneg_right h2 h3).trans ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => by have := (hτ.2 i).1; positivity) fun i _ => ?_
  obtain ⟨h0, h1⟩ := hτ.2 i
  have hc : 1 ≤ 2 * f * j i := Nat.mul_pos (by omega) (hj i)
  have he : 2 * f * j i ≤ 2 * j i * (n - 2 * ∑ l, j l) * f := by
    calc 2 * f * j i = 2 * j i * 1 * f := by ring
      _ ≤ _ := by gcongr; omega
  have h4 : τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) ≤ τ i ^ (2 * f * j i - 1) * τ i := by
    rw [← pow_succ]
    exact pow_le_pow_of_le_one h0.le (by linarith) (by omega)
  calc _ ≤ τ i ^ (2 * f * j i - 1) * τ i * (2 * (f : ℝ) * j i / τ i) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = _ := by push_cast; field_simp

theorem lintegral_dens_le_one : ∀ (n f a : ℕ) (j : Fin a → ℕ), 1 ≤ f → (∀ i, 1 ≤ j i) → 2 * ∑ i, j i + 1 ≤ n → ∫⁻ τ in simplexH a, ENNReal.ofReal (dens n f j τ) ≤ 1 := by
  intro n f a j hf hj hn
  set box : Set (Fin a → ℝ) := Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1) with hbox
  have hc : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : simplexH a ⊆ box := fun τ hτ i _ => ⟨(hτ.2 i).1.le, by linarith [(hτ.2 i).2]⟩
  have hm : MeasurableSet (simplexH a) := by
    have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
        ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
      ext τ
      simp [simplexH, StrictMono]
    rw [this]
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k))
      (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const))
  set g : (Fin a → ℝ) → ℝ := fun τ => ∏ i, ((2 * f * j i : ℕ) : ℝ) * τ i ^ (2 * f * j i - 1) with hg
  have hcont : Continuous g := by rw [hg]; fun_prop
  have hint : IntegrableOn g box := hcont.continuousOn.integrableOn_compact hc
  calc _ ≤ ∫⁻ τ in simplexH a, ENNReal.ofReal (g τ) :=
        setLIntegral_mono' hm fun τ hτ => ENNReal.ofReal_le_ofReal (dens_le n f a j hf hj hn τ hτ)
    _ ≤ ∫⁻ τ in box, ENNReal.ofReal (g τ) := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ τ in box, g τ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        refine (ae_restrict_iff' hc.measurableSet).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
        refine Finset.prod_nonneg fun i _ => ?_
        have := (hτ i trivial).1
        positivity
    _ = 1 := by
        rw [integral_cube a (fun i => 2 * f * j i) fun i => Nat.mul_pos (by omega) (hj i), ENNReal.ofReal_one]

end GlobalTheory.DensityIntegral
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeWhole

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hc
  push_neg at hc
  have hle : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have := le_of_tendsto h' hle
  linarith

theorem isGaugeSub_univ {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) :
    0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε) := by
  have hc := pos_of_isGauge' h
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨hc, ?_⟩
  unfold IsGaugeSub
  refine ⟨by simp, fun s _ => ?_, ?_⟩
  · rw [Measure.map_smul, map_mul_left_eq_self]
    exact (measurable_const_smul s).aemeasurable
  · rw [← ENNReal.ofReal_toReal hfin]
    refine (ENNReal.tendsto_ofReal h').congr' ?_
    filter_upwards [h'.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hμ : Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
      intro htop
      rw [htop] at hr
      simp at hr
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos (pow_pos hr0' _),
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hμ]

theorem gauge_whole : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ c : ℝ, IsGauge ε c → 0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε)) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ (Set.univ : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := by
  intro n ε
  refine ⟨fun c hc => isGaugeSub_univ hc, ?_⟩
  obtain ⟨E, hE, horth, hexp⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨⊤, E, fun _ _ _ _ => Submodule.mem_top, horth, fun X => ?_, ?_⟩
  · constructor
    · rintro ⟨-, hX⟩
      rw [hexp X hX]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hs : ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i = (((X * (E i)ᴴ).trace).re : ℝ) • E i := by
        ext a b
        simp [Complex.real_smul]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hX
      refine ⟨Submodule.mem_top, ?_⟩
      have hle : Submodule.span ℝ (Set.range E) ≤ GlobalTheory.GaugeConst.lieJ ε := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact GlobalTheory.GaugeConst.mem_lieJ.mpr (hE i).1
      exact GlobalTheory.GaugeConst.mem_lieJ.mp (hle hX)
  · ext g
    simp

end GlobalTheory.GaugeWhole
end
