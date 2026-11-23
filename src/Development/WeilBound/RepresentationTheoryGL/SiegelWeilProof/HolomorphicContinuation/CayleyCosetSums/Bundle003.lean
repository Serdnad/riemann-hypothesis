module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CRSecA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.TotallySplit
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle004
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle003
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem JJ_inv : (JJ n)⁻¹ = -JJ n := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.neg_mul, JJ_mul_JJ, neg_neg]

theorem JJ_conjT : (JJ n)ᴴ = -JJ n := by
  simp [JJ, fromBlocks_conjTranspose, fromBlocks_neg]

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  simp [sig, JJ_inv]

theorem sig_sig (X : M2 n) : sig (sig X) = X := by
  have h1 : ∀ B : M2 n, JJ n * (JJ n * B) = -B := by
    intro B
    rw [← Matrix.mul_assoc, JJ_mul_JJ, Matrix.neg_mul, Matrix.one_mul]
  rw [sig_eq, sig_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, JJ_conjT, Matrix.mul_assoc,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, h1, JJ_mul_JJ, Matrix.mul_one]

theorem sig_add (X Y : M2 n) : sig (X + Y) = sig X + sig Y := by
  simp [sig_eq, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem sig_smul (c : ℂ) (X : M2 n) : sig (c • X) = (starRingEnd ℂ c) • sig X := by
  simp only [sig_eq, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.star_def]

theorem sig_sub (X Y : M2 n) : sig (X - Y) = sig X - sig Y := by
  simp [sig_eq, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem conj_real_part_fixed (Z : M2 n) : sig (Z1 Z) = Z1 Z := by
  have hc : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  rw [Z1, sig_smul, sig_add, sig_sig, hc, add_comm]

theorem conj_imaginary_part_fixed (Z : M2 n) : sig (Z2 Z) = Z2 Z := by
  have hc : starRingEnd ℂ (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    field_simp
  rw [Z2, sig_smul, sig_sub, sig_sig, hc, neg_smul, ← smul_neg, neg_sub]

theorem real_add_imaginary_part (Z : M2 n) : Z1 Z + Complex.I • Z2 Z = Z := by
  have hc : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  simp only [Z1, Z2, smul_smul, hc]
  module

theorem inG_cE {A : M2 n} (hA : sig A = A) (s : ℝ) : InG (II.cE A s) := by
  have hJJ := JJ_mul_JJ (n := n)
  let U : (M2 n)ˣ := ⟨JJ n, -JJ n, by rw [Matrix.mul_neg, hJJ, neg_neg],
    by rw [Matrix.neg_mul, hJJ, neg_neg]⟩
  have hAh : Aᴴ = JJ n * A * JJ n := by
    have h := hA
    rw [sig_eq] at h
    calc Aᴴ = (JJ n * JJ n) * Aᴴ * (JJ n * JJ n) := by
          rw [hJJ, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
      _ = JJ n * (JJ n * Aᴴ * JJ n) * JJ n := by simp only [Matrix.mul_assoc]
      _ = JJ n * A * JJ n := by rw [h]
  have hB : (s • A)ᴴ = (U : M2 n) * (-(s • A)) * ((U⁻¹ : (M2 n)ˣ) : M2 n) := by
    show (s • A)ᴴ = JJ n * (-(s • A)) * (-JJ n)
    rw [conjTranspose_smul, star_trivial, hAh]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_smul, Matrix.smul_mul]
  unfold InG II.cE
  rw [← Matrix.exp_conjTranspose, hB, Matrix.exp_units_conj]
  show JJ n * NormedSpace.exp (-(s • A)) * (-JJ n) * JJ n * NormedSpace.exp (s • A) = JJ n
  rw [Matrix.mul_assoc (JJ n * _) (-JJ n) (JJ n), Matrix.neg_mul, hJJ, neg_neg, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute (-(s • A)) (s • A) ((Commute.refl (s • A)).neg_left),
    neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def v1 (b : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • b.toBlocks₁₁ + b.toBlocks₁₂

theorem fz_zero (e : ℤ) (x : M2 n) : fz m e 0 x = x.det ^ e * (u1 x).det ^ (-(m : ℤ)) := by
  simp [fz]

theorem blocks_mul (g b : M2 n) : (g * b).toBlocks₂₁ = g.toBlocks₂₁ * b.toBlocks₁₁ + g.toBlocks₂₂ * b.toBlocks₂₁ ∧
    (g * b).toBlocks₂₂ = g.toBlocks₂₁ * b.toBlocks₁₂ + g.toBlocks₂₂ * b.toBlocks₂₂ := by
  constructor <;> ext i j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.add_apply]

theorem second_coord_mul_inner (g b : M2 n) : u1 (g * b) = g.toBlocks₂₁ * v1 b + g.toBlocks₂₂ * u1 b := by
  obtain ⟨h1, h2⟩ := blocks_mul g b
  simp only [u1, v1, h1, h2, Matrix.mul_add, Matrix.mul_smul, smul_add]
  abel

theorem nU_blocks (y : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) :
    (y * nU S).toBlocks₂₁ = y.toBlocks₂₁ ∧ (y * nU S).toBlocks₂₂ = y.toBlocks₂₁ * S + y.toBlocks₂₂ := by
  obtain ⟨h1, h2⟩ := blocks_mul y (nU S)
  simp only [nU, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_one, Matrix.mul_zero,
    add_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem det_nU (S : Matrix (Fin n) (Fin n) ℂ) : (nU S).det = 1 := by
  simp [nU]

private theorem mul_JJ_mul_conjTranspose_eq_of_inG (y : M2 n) (hy : InG y) : y * JJ n * yᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := by
    ext (i|i) (j|j) <;> simp [JJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hy' : yᴴ * JJ n * y = JJ n := hy
  have h1 : (-(JJ n * yᴴ * JJ n)) * y = 1 := by
    calc (-(JJ n * yᴴ * JJ n)) * y = -(JJ n * (yᴴ * JJ n * y)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hy', hJ, neg_neg]
  have h2 : y * (-(JJ n * yᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc y * JJ n * yᴴ = y * JJ n * yᴴ * (-(JJ n * JJ n)) := by rw [hJ, neg_neg, Matrix.mul_one]
    _ = (y * (-(JJ n * yᴴ * JJ n))) * JJ n := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [h2, Matrix.one_mul]

theorem hermit_cd (y : M2 n) (hy : InG y) (hc : IsUnit y.toBlocks₂₁.det) :
    (y.toBlocks₂₁⁻¹ * y.toBlocks₂₂).IsHermitian := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_mul_conjTranspose_eq_of_inG y hy)
  rw [← Matrix.fromBlocks_toBlocks y] at h
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at h
  rw [neg_add_eq_zero] at h
  have hcH : IsUnit (y.toBlocks₂₁)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr hc
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc (y.toBlocks₂₂)ᴴ * (y.toBlocks₂₁)ᴴ⁻¹
      = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₁ * (y.toBlocks₂₂)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hc, Matrix.one_mul]
    _ = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₂ * (y.toBlocks₂₁)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by rw [← h]
    _ = (y.toBlocks₂₁)⁻¹ * y.toBlocks₂₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hcH, Matrix.mul_one]

theorem v_rel (b : M2 n) (hb : InG b) : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e := hb
  unfold InG at e
  rw [← Matrix.fromBlocks_toBlocks b] at e
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  have key : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b =
      -(-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₁)
      - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₂)
      + Complex.I • ((-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₂)
        - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₁)) := by
    simp only [u1, v1, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_I]
    match_scalars <;>
      first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
  rw [key, e1, e2, e3, e4]
  module

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def ub2 (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := -x⁻¹.toBlocks₁₁ + Complex.I • x⁻¹.toBlocks₂₁

def Om (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := ub2 x * (ub1 x)⁻¹

def eQ (m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n) : ℂ := fz m e z x * (Om x * Q).trace

def rhoP {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Kg) : ℂ :=
  star (fz m e 0 (ι k) * ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace)

def LoweringDerivativeVacuum : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n), InG x → rC (lowQ Q) (fz m e z) x = z * eQ m e z Q x

def MultiplicityOneTestOperators : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n),
    Continuous ψ → HasCompactSupport ψ → InG a → InG b →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (x : M2 n), InG x →
      tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x = eQ m e z (c z • Yᴴ) x

def SingularTestsKillVacuum : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ρ : Kg → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), Continuous ρ →
    IsSingTest ψ → InG a → InG b → InG x → tOp μ ι ρ ψ a b (fz m e 0) x = 0

def Crux : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n),
      IsSingTest ψ ∧ InG a ∧ InG b ∧ InG x ∧ deriv (fun z => tOp μ ι (rhoP ι m e P) ψ a b (fz m e z) x) 0 ≠ 0

def AsmLT : Prop := LoweringDerivativeVacuum → MultiplicityOneTestOperators → SingularTestsKillVacuum → Crux → LocTau

end PositivityTheory.Rg.Sw.HSt
end
end

section

noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reL : Mn n →L[ℝ] Mn n := (1 / 2 : ℂ) • (ContinuousLinearMap.id ℝ (Mn n) + cT)

def imL : Mn n →L[ℝ] Mn n := (-(Complex.I / 2)) • (ContinuousLinearMap.id ℝ (Mn n) - cT)

theorem reL_apply (V : Mn n) : reL V = reP V := rfl

theorem imL_apply (V : Mn n) : imL V = imaginary V := rfl

theorem contDiff_fM (a0 : Mn n) : ContDiff ℝ ⊤ (fM a0) := by
  have h1 : ContDiff ℝ ⊤ (fun V : Mn n => (1 : Mn n) + imaginary V) := contDiff_const.add imL.contDiff
  unfold fM
  refine reL.contDiff.add (ContDiff.const_smul _ ?_)
  exact contDiff_mul' (contDiff_mul' (contDiff_mul' contDiff_const h1) h1) contDiff_const

theorem fM_line (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) (t : ℝ) :
    fM a0 (V0 + t • dV) = (V0 + Complex.I • (a0 * a0ᴴ)) +
      t • (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) +
      (t ^ 2) • (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ)) := by
  have hr : reP (V0 + t • dV) = V0 + t • reP dV := by
    rw [← reL_apply, map_add (f := _), map_smul, reL_apply, reL_apply, reP_of_herm h0]
  have hi : imaginary (V0 + t • dV) = t • imaginary dV := by
    rw [← imL_apply, map_add (f := _), map_smul, imL_apply, imL_apply, imaginaryPart_of_isHermitian h0, zero_add]
  unfold fM
  rw [hr, hi]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    smul_add, smul_smul]
  module

theorem fderiv_fM (a0 V0 dV : Mn n) (h0 : V0ᴴ = V0) :
    fderiv ℝ (fM a0) V0 dV = reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ) := by
  have hd : DifferentiableAt ℝ (fM a0) V0 := ((contDiff_fM a0).differentiable (by simp)).differentiableAt
  have hl := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const dV).const_add V0
  rw [one_smul] at hl
  have hd' : HasFDerivAt (fM a0) (fderiv ℝ (fM a0) V0) (V0 + (0 : ℝ) • dV) := by
    rw [zero_smul, add_zero]; exact hd.hasFDerivAt
  have hc := hd'.comp_hasDerivAt (0 : ℝ) hl
  have h1 := (hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).smul_const (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ))
  have h2 := ((hasDerivAt_id' (𝕜 := ℝ) (x := (0 : ℝ))).pow 2).smul_const
    (Complex.I • (a0 * imaginary dV * imaginary dV * a0ᴴ))
  have h3 := ((hasDerivAt_const (0 : ℝ) (V0 + Complex.I • (a0 * a0ᴴ))).add h1).add h2
  simp only [one_smul, zero_add] at h3
  have h4 : HasDerivAt (fun t : ℝ => fM a0 (V0 + t • dV)) (reP dV + Complex.I • (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)) 0 := by
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp only [fM_line a0 V0 dV h0 t, Pi.add_apply, Pi.pow_apply]
    · norm_num
  exact hc.unique h4

theorem herm_zero_of (H1 H2 : Mn n) (h1 : H1ᴴ = H1) (h2 : H2ᴴ = H2) (h : H1 + Complex.I • H2 = 0) :
    H1 = 0 ∧ H2 = 0 := by
  have hc : H1 - Complex.I • H2 = 0 := by
    have := congrArg conjTranspose h
    rw [conjTranspose_add, conjTranspose_smul, h1, h2, conjTranspose_zero] at this
    rw [sub_eq_add_neg, ← neg_smul]
    simpa using this
  have h2H1 : H1 + H1 = 0 := by
    calc H1 + H1 = (H1 + Complex.I • H2) + (H1 - Complex.I • H2) := by abel
      _ = 0 := by rw [h, hc, add_zero]
  have hH1 : H1 = 0 := by
    have : (2 : ℂ) • H1 = 0 := by rw [two_smul]; exact h2H1
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  refine ⟨hH1, ?_⟩
  rw [hH1, zero_add] at h
  exact (smul_eq_zero.mp h).resolve_left Complex.I_ne_zero

theorem fderiv_fM_inj (a0 V0 : Mn n) (h0 : V0ᴴ = V0) (ha : a0.det ≠ 0) :
    Function.Injective (fderiv ℝ (fM a0) V0) := by
  refine (injective_iff_map_eq_zero (fderiv ℝ (fM a0) V0)).2 fun dV hdV => ?_
  rw [fderiv_fM a0 V0 dV h0] at hdV
  have hH2 : (a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ)ᴴ = a0 * ((2 : ℂ) • imaginary dV) * a0ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul, imaginaryPart_isHermitian,
      Matrix.mul_assoc]
    simp
  obtain ⟨hr, hi⟩ := herm_zero_of _ _ (reP_herm dV) hH2 hdV
  have hu : IsUnit a0.det := isUnit_iff_ne_zero.mpr ha
  have huH : IsUnit a0ᴴ.det := by rw [det_conjTranspose]; exact (isUnit_iff_ne_zero.mpr ha).star
  have hB : (2 : ℂ) • imaginary dV = 0 := by
    have := congrArg (fun M => a0⁻¹ * M * (a0ᴴ)⁻¹) hi
    simp only [Matrix.mul_zero, Matrix.zero_mul] at this
    rw [← this, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huH, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hB' : imaginary dV = 0 := (smul_eq_zero.mp hB).resolve_left two_ne_zero
  rw [← reP_add_imP dV, hr, hB', smul_zero, add_zero]

end PositivityTheory.Rg.Sw.HSt.CRSec
end
end
