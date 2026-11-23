module

public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle006
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
import Formalism.DoubleCosetMeasures.Statement
import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Formalism.HermitianCurvature.Bundle002
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Basic.Complex.Basic
import Formalism.HermitianCurvature.StatementLE
import Formalism.HermitianCurvature.Bundle001
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.S3x2

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]

variable {c : ι → ℕ} {x y : Matrix ι ι A}


end Generic

section Prod

variable {G : Type} [Group G]

end Prod

section Specific

variable {A : Type} [CommRing A] {r k : ℕ}




end Specific

section Local

variable (o : Type) [CommRing o] [IsLocalRing o]

variable {o} {r k : ℕ}

end Local

end Formalism.FourierDecayAlt.P.S3x2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.WordLiftInduction

open Finset Polynomial Formalism.FourierDecayAlt.F7

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

end

end Formalism.FourierDecayAlt.P.WordLiftInduction

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

open MvPolynomial

end Formalism.FourierDecayAlt.P.LEx2
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {n : ℕ}

def cols (x : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun p i => x i p

theorem cols_mulVec (x : Fin n → Fin n → ℂ) (c : Fin n → ℂ) : cols x *ᵥ c = ∑ i, c i • x i := by
  funext p
  simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem cols_mulVec_single (x : Fin n → Fin n → ℂ) (i : Fin n) : cols x *ᵥ Pi.single i 1 = x i := by
  rw [cols_mulVec, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem mul_cols (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    A * cols x = cols (fun i => A *ᵥ x i) := by
  ext p i
  simp [cols, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_cols (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    (cols x)ᴴ * H * cols x = Matrix.of fun j i => herm H (x i) (x j) := by
  ext j i
  rw [Matrix.mul_assoc, mul_cols]
  simp [cols, Matrix.mul_apply, herm, dotProduct, Matrix.conjTranspose_apply]

theorem gram_eq {H : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : (cols x)ᴴ * H * cols x = H := by
  rw [gram_cols]
  ext j i
  exact hx i j

theorem cols_unit {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsUnit H.det) {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : IsUnit (cols x).det := by
  have h := congrArg Matrix.det (gram_eq hx)
  rw [Matrix.det_mul] at h
  rw [← h] at hH
  exact isUnit_of_mul_isUnit_right hH

theorem wittGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x y : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (hy : ∀ i j, herm H (y i) (y j) = H j i) :
    ∃ g ∈ UH H, ∀ i, g *ᵥ x i = y i := by
  have hX := cols_unit hH hx
  have gx := gram_eq hx
  have gy := gram_eq hy
  have e1 : (cols x)⁻¹ * cols x = 1 := Matrix.nonsing_inv_mul _ hX
  have e2 : cols x * (cols x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hX
  refine ⟨cols y * (cols x)⁻¹, ?_, ?_⟩
  · show (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹) = H
    calc (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹)
        = ((cols x)⁻¹)ᴴ * ((cols y)ᴴ * H * cols y) * (cols x)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = ((cols x)⁻¹)ᴴ * ((cols x)ᴴ * H * cols x) * (cols x)⁻¹ := by rw [gy, gx]
      _ = (cols x * (cols x)⁻¹)ᴴ * H * (cols x * (cols x)⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [e2]; simp
  · intro i
    calc (cols y * (cols x)⁻¹) *ᵥ x i = (cols y * (cols x)⁻¹) *ᵥ (cols x *ᵥ Pi.single i 1) := by
          rw [cols_mulVec_single]
      _ = y i := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, e1, Matrix.mul_one, cols_mulVec_single]

theorem extGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i, A *ᵥ x i = B *ᵥ x i) : A = B := by
  have hX := cols_unit hH hx
  have e : A * cols x = B * cols x := by
    rw [mul_cols, mul_cols]
    congr 1
    funext i
    exact h i
  calc A = A * cols x * (cols x)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
    _ = B := by rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def fam (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ :=
  fun i => if h : r ≤ i.val ∧ i.val ≤ r + k then e ⟨i.val - r, by omega⟩ else bvec i

def ONb (k r : ℕ) (e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ a, inWb k r (e a)) ∧
    ∀ a b, herm (Hpk k r) (e a) (e b) = if a = b then (if a.val = k then -1 else 1) else 0

theorem hpk_out_in {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    Hpk k r i j = 0 ∧ Hpk k r j i = 0 := by
  constructor <;> simp only [Hpk] <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_bvec (i j : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec i) (bvec j) = Hpk k r j i := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]

theorem herm_bvec_w {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) (bvec i) w = 0 := by
  have hc : ∀ l, (Hpk k r *ᵥ bvec i) l = Hpk k r l i := fun l => by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [herm, dotProduct, hc]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).2, mul_zero]
  · rw [Pi.star_apply, hw l (by omega), star_zero, zero_mul]

theorem herm_w_bvec {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : herm (Hpk k r) w (bvec i) = 0 := by
  have hc : herm (Hpk k r) w (bvec i) = (Hpk k r *ᵥ w) i := by
    simp [herm, bvec, dotProduct, Pi.single_apply]
  rw [hc]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
  · rw [(hpk_out_in hi hl).1, zero_mul]
  · rw [hw l (by omega), mul_zero]

theorem fam_in {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : r ≤ i.val ∧ i.val ≤ r + k) :
    fam k r e i = e ⟨i.val - r, by omega⟩ := by
  simp only [fam]
  rw [dite_eq_left h]

theorem fam_out {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    fam k r e i = bvec i := by
  simp only [fam]
  rw [dite_eq_right]
  omega

theorem famGram {e : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ} (he : ONb k r e) (i j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (fam k r e i) (fam k r e j) = Hpk k r j i := by
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k <;> by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · rw [fam_in hi, fam_in hj, he.2]
    simp only [Hpk]
    split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)
  · rw [fam_in hi, fam_out (i := j) (by omega), herm_w_bvec (i := j) (by omega) (he.1 _),
      (hpk_out_in (i := j) (j := i) (by omega) hi).1]
  · rw [fam_out (i := i) (by omega), fam_in hj, herm_bvec_w (i := i) (by omega) (he.1 _),
      (hpk_out_in (i := i) (j := j) (by omega) hj).2]
  · rw [fam_out (i := i) (by omega), fam_out (i := j) (by omega), herm_bvec_bvec]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x1

theorem lamN_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (j : ℕ) (hj : j + 1 = n) : lamN R Z j = lamLin R Z := by
  unfold lamN lamTil lamLin rowN lastCoord
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  have : (a.val = j ↔ a.val + 1 = n) := by omega
  simp [this]

end Formalism.FourierDecayAlt.P.A5x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x1

theorem tripleForm : Formalism.FourierDecayAlt.A5.TripleForm := by
  intro K _ R ψ w w' k hw hw'
  unfold Kp intTT pairTerm
  apply finsum_congr
  intro q
  congr 2
  split_ifs with hI
  · congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro φ
    constructor
    · intro hφ
      refine ⟨hφ, ?_⟩
      intro j hkj hjn
      have hj : j = k := by omega
      subst hj
      refine ⟨0, ?_⟩
      intro v v' hv
      have h2 := hφ.2 v v' hv
      rw [lamN_last R _ j hw'.symm, lamN_last R _ j hw.symm, h2]
      simp
    · exact fun h => h.1
  · rfl

end Formalism.FourierDecayAlt.P
end

section

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def An (TT : ℝ) : Set ℂ := {ζ | TT < Complex.normSq ζ}

theorem isOpen_An (TT : ℝ) : IsOpen (An TT) :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exp_mem_An {w : ℂ} (hw : w ∈ Hh TT) : Complex.exp w ∈ An TT := by
  exact hw

theorem hasFDerivAt_exp_real (w : ℂ) :
    HasFDerivAt Complex.exp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w)) w := by
  have h : HasFDerivAt Complex.exp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp w)).restrictScalars ℝ) w :=
    (Complex.hasDerivAt_exp w).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (bet α)
      (α (Complex.exp w) • (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w) +
        Complex.exp w • (fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w := by
  have he := hasFDerivAt_exp_real w
  have hmem : Complex.exp w ∈ An TT := exp_mem_An hw
  have hdα : DifferentiableAt ℝ α (Complex.exp w) :=
    (hα.contDiffAt ((isOpen_An TT).mem_nhds hmem)).differentiableAt
      (by first | simp | exact le_top)
  have hc : HasFDerivAt (fun z => α (Complex.exp z))
      ((fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w :=
    hdα.hasFDerivAt.comp w he
  exact hc.mul he

theorem fderiv_bet_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (v : ℂ) :
    fderiv ℝ (bet α) w v = (α (Complex.exp w) * Complex.exp w + wZ α (Complex.exp w) * Complex.exp w ^ 2) * v +
      wZb α (Complex.exp w) * Complex.exp w * (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v := by
  rw [(hasFDerivAt_bet hα hw).fderiv]
  unfold wZ wZb
  obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ α (Complex.exp w) := ⟨_, rfl⟩
  rw [← hL]
  have hL' : ∀ u : ℂ, 2 * L u = (u + (starRingEnd ℂ) u) * L 1 + Complex.I * ((starRingEnd ℂ) u - u) * L Complex.I := by
    intro u
    have hre : L u = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
      have hu : u.re • (1 : ℂ) + u.im • Complex.I = u := by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      conv_lhs => rw [← hu]
      rw [map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have h1 := Complex.add_conj u
    have h2 := Complex.sub_conj u
    push_cast at h1 h2
    rw [hre]
    linear_combination (-(L 1)) * h1 + (Complex.I * L Complex.I) * h2 +
      (2 * (u.im : ℂ) * L Complex.I) * Complex.I_sq
  have key := hL' (Complex.exp w * v)
  have hcj : (starRingEnd ℂ) (Complex.exp w * v) = (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v :=
    map_mul (starRingEnd ℂ) _ _
  rw [hcj] at key
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  linear_combination (Complex.exp w / 2) * key

theorem sym_alg (A b ζ h k : ℂ) (hb : b.re = 0) :
    ((A * h + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) h) * k).im =
      ((A * k + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) k) * h).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.conj_re,
    Complex.conj_im, hb]
  ring

theorem contDiffOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bet α) (Hh TT) := by
  have he : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.exp (Hh TT) :=
    Complex.contDiff_exp.contDiffOn
  exact (hα.comp he (fun w hw => exp_mem_An hw)).mul he

theorem contDiffOn_om (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (om α) (Hh TT) :=
  omL.contDiff.comp_contDiffOn (contDiffOn_bet hα)

theorem fderiv_om_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (h k : ℂ) :
    fderiv ℝ (om α) w h k = 2 * (fderiv ℝ (bet α) w h * k).im := by
  have hb := hasFDerivAt_bet hα hw
  have hom : HasFDerivAt (om α) (omL.comp (fderiv ℝ (bet α) w)) w :=
    omL.hasFDerivAt.comp w hb.differentiableAt.hasFDerivAt
  rw [hom.fderiv]
  simp [omL, two_smul, two_mul]

theorem om_sym (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ∀ p ∈ Hh TT, ∀ h k : ℂ, fderiv ℝ (om α) p h k = fderiv ℝ (om α) p k h := by
  intro p hp h k
  rw [fderiv_om_apply hα hp, fderiv_om_apply hα hp, fderiv_bet_apply hα hp, fderiv_bet_apply hα hp,
    sym_alg _ _ _ h k (hcurv _ (exp_mem_An hp))]

def x0 (TT : ℝ) : ℂ := (Real.log (TT + 1) : ℂ)

theorem base_point_mem_half_plane (hTT : 0 ≤ TT) : x0 TT ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT))
  unfold x0
  rw [← Complex.ofReal_exp, Complex.normSq_ofReal, Real.exp_log (by linarith)]
  nlinarith

def th (TT : ℝ) (α : ℂ → ℂ) (w : ℂ) : ℝ := prim (om α) (x0 TT) w

theorem hasFDerivAt_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (th TT α) (om α w) w :=
  hasFDerivAt_prim (isOpen_Hh TT) (convex_Hh TT) (base_point_mem_half_plane hTT) ((contDiffOn_om hα).of_le (by simp))
    (om_sym hα hcurv) hw

theorem contDiffOn_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (Hh TT) := by
  have hHo : IsOpen (Hh TT) :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hHo]
  refine ⟨fun y hy => (hasFDerivAt_th hTT hα hcurv hy).differentiableAt.differentiableWithinAt, ?_⟩
  exact (contDiffOn_om hα).congr (fun y hy => (hasFDerivAt_th hTT hα hcurv hy).fderiv)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end
