module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle059
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNMulRpow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.Bundle005
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

def abelian₂ (e0 : Mx k r → ℂ) (γ : Mx k r) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (x y : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
    Matrix.of y)‖ₑ ∂μq ∂μp

def Lam1 (e0 : Mx k r → ℂ) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x y : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂μp

theorem meas_inv {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) :
    Measurable (fun t => (fun i j => ((Matrix.of (f t))⁻¹ : Mx k r) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  (B2x1.invM_meas (k := k) (r := r)).comp hf

theorem measurable_enorm_composition {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {f : α → Formalism.QuantumDeterminants.Mt k r} (hf : Measurable f) : Measurable (fun t => ‖e0 (Matrix.of (f t))‖ₑ) :=
  ((he0.comp mt_cont).measurable.comp hf).enorm

theorem meas_hn {α : Type*} [MeasurableSpace α] {f : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) :
    Measurable (fun t => (fun i j => (Matrix.of (f t).1 * Matrix.of (f t).2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_matmul hf.fst hf.snd

theorem meas_lam_int {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P Q : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) * γ *
      (Matrix.of (Q t).1 * Matrix.of (Q t).2)⁻¹ * Matrix.of (Y t))‖ₑ) := by
  have mγ : Measurable (fun _ : α => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
  have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) mγ)
    (meas_inv (meas_hn hQ))) hY
  exact measurable_enorm_composition he0 M

theorem measurable_lambda_integrand {e0 : Mx k r → ℂ} (he0 : Continuous e0) {α : Type*} [MeasurableSpace α]
    {X Y : α → Formalism.QuantumDeterminants.Mt k r} {P : α → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hX : Measurable X) (hY : Measurable Y) (hP : Measurable P) :
    Measurable (fun t => ‖e0 ((Matrix.of (X t))⁻¹ * (Matrix.of (P t).1 * Matrix.of (P t).2) *
      Matrix.of (Y t))‖ₑ) := by
  have M := meas_matmul (meas_matmul (meas_inv hX) (meas_hn hP)) hY
  exact measurable_enorm_composition he0 M

theorem meas_lam {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] [SFinite μq] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => abelian₂ e0 γ μp μq t.1 t.2) := by
  unfold abelian₂
  have m4 := meas_lam_int he0 γ (α := ((Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (measurable_fst.fst.fst) (measurable_fst.fst.snd) measurable_fst.snd measurable_snd
  have m3 := m4.lintegral_prod_right' (ν := μq)
  exact m3.lintegral_prod_right' (ν := μp)

theorem measurable_lambda_integral {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μp] :
    Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => Lam1 e0 μp t.1 t.2) := by
  unfold Lam1
  have m3 := measurable_lambda_integrand he0 (α := (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) × (Formalism.QuantumDeterminants.Mt k r ×
      Formalism.QuantumDeterminants.Mt k r)) (measurable_fst.fst) (measurable_fst.snd) measurable_snd
  exact m3.lintegral_prod_right' (ν := μp)

theorem meas_const_mt (c : Formalism.QuantumDeterminants.Mt k r) {α : Type*} [MeasurableSpace α] :
    Measurable (fun _ : α => c) := measurable_const

theorem lam_left {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μq]
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ (μW.prod μN) μq (fun i j => (h0 * n0 * Matrix.of x) i j) y = abelian₂ e0 γ (μW.prod μN) μq x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * γ *
    (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq with hF
  have hFm : Measurable F := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) := measurable_const
    have M := meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt x'))
      measurable_fst) mγ) (meas_inv (meas_hn measurable_snd))) (meas_const_mt y)
    exact (measurable_enorm_composition he0 M).lintegral_prod_right'
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold abelian₂
  calc ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y)‖ₑ ∂μq ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lam_right {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ μp (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = abelian₂ e0 γ μp (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, hSS, -⟩ := MatrixMultiplicationContinuity.uh_inv hS
  unfold abelian₂
  apply lintegral_congr
  intro p
  set y' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of y) i j with hy'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
    (Matrix.of m)⁻¹ * Matrix.of y')‖ₑ with hF
  have hFm : Measurable F := by
    have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ) i j : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    have M := meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt y')
    exact measurable_enorm_composition he0 M
  have hpl := param_left hW hN hz hh0 hn0 hFm
  calc ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
        (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of y')‖ₑ ∂(μW.prod μN)
      = ∫⁻ q, F (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ q, F (fun i j => (h0 * n0 * (Matrix.of q.1 * Matrix.of q.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hSS' := (MatrixMultiplicationContinuity.uh_inv hS).2.2
        have hmat : ∀ (Z Q : Mx k r), Z * (Matrix.of (fun i j => (h0 * n0 * Q) i j : Formalism.QuantumDeterminants.Mt k r))⁻¹ *
            Matrix.of y' = Z * Q⁻¹ * Matrix.of y := by
          intro Z Q
          show Z * (h0 * n0 * Q)⁻¹ * (h0 * n0 * Matrix.of y) = Z * Q⁻¹ * Matrix.of y
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS',
            Matrix.one_mul, ← Matrix.mul_assoc]
        simp only [hF, hmat]

theorem lambda_left_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) (fun i j => (h0 * n0 * Matrix.of x) i j) y = Lam1 e0 (μW.prod μN) x y := by
  have hS : h0 * n0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hh0.1 hn0.1
  obtain ⟨-, -, hSS⟩ := MatrixMultiplicationContinuity.uh_inv hS
  set x' : Formalism.QuantumDeterminants.Mt k r := fun i j => (h0 * n0 * Matrix.of x) i j with hx'
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x')⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x')) measurable_id) (meas_const_mt y))
  have hpl := param_left hW hN hz hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x')⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := rfl
    _ = ∫⁻ p, F (fun i j => (h0 * n0 * (Matrix.of p.1 * Matrix.of p.2)) i j) ∂(μW.prod μN) := hpl.symm
    _ = _ := by
        have hmat : ∀ P : Mx k r, (Matrix.of x')⁻¹ * Matrix.of (fun i j => (h0 * n0 * P) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * P := by
          intro P
          show (h0 * n0 * Matrix.of x)⁻¹ * (h0 * n0 * P) = (Matrix.of x)⁻¹ * P
          rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (h0 * n0)⁻¹, hSS, Matrix.one_mul]
        simp only [hF, hmat]

theorem lambda_right_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = Lam1 e0 (μW.prod μN) x y := by
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun m => ‖e0 ((Matrix.of x)⁻¹ * Matrix.of m * Matrix.of y)‖ₑ with hF
  have hFm : Measurable F :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt x)) measurable_id) (meas_const_mt y))
  have hpr := param_right hW hN hz hT hh0 hn0 hFm
  unfold Lam1
  calc ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) *
        Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r))‖ₑ ∂(μW.prod μN)
      = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2 * (h0 * n0)) i j) ∂(μW.prod μN) := by
        have hmat : ∀ P : Mx k r, (Matrix.of x)⁻¹ * P *
            Matrix.of (fun i j => (h0 * n0 * Matrix.of y) i j : Formalism.QuantumDeterminants.Mt k r) =
            (Matrix.of x)⁻¹ * Matrix.of (fun i j => (P * (h0 * n0)) i j : Formalism.QuantumDeterminants.Mt k r) * Matrix.of y := by
          intro P
          show (Matrix.of x)⁻¹ * P * (h0 * n0 * Matrix.of y) = (Matrix.of x)⁻¹ * (P * (h0 * n0)) * Matrix.of y
          simp only [Matrix.mul_assoc]
        simp only [hF, hmat]
    _ = ∫⁻ p, F (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) ∂(μW.prod μN) := hpr
    _ = _ := rfl

end Formalism.FourierDecayAlt.P.S3dx4
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section general

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jgq_continuousOn (D : B.RealPlaceData k r Wp Wq) {A : ℝ} {H : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hT : JF.TransportedAlt k r A 0) (hH : B.InCC A 0 H) :
    ContinuousOn (fun q => B.JF D H (B.gq D q)) (JF.QDom k r D.z D.z') := by
  exact (Formalism.FourierDecayAlt.Final.jf_jqSmooth k r Wp Wq D A 0 H hT hH).continuousOn

theorem aesm_weight_smul (D : B.RealPlaceData k r Wp Wq) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin r → ℂ) × ℂ → E} (hc : ContinuousOn g (JF.QDom k r D.z D.z')) :
    AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q) volume := by
  set s := JF.QDom k r D.z D.z' with hs_def
  have hs : MeasurableSet s := by
    have hseq : s = (⋂ a : Fin r, {q : (Fin r → ℂ) × ℂ | q.1 a ≠ 0}) ∩
        {q | Tz k r D.z * Tz k r D.z' < Complex.normSq q.2} := by
      ext q
      simp [hs_def, JF.QDom]
    rw [hseq]
    refine IsOpen.measurableSet (IsOpen.inter (isOpen_iInter_of_finite fun a => ?_) ?_)
    · exact isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
    · exact isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  have contW : Continuous (fun q : (Fin r → ℂ) × ℂ => (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) *
      (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') ^ (k - 1)) := by
    first | fun_prop | continuity
  have hw : ContinuousOn (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q) s := by
    refine contW.continuousOn.congr fun q hq => ?_
    unfold bcWeight
    rw [if_pos hq.2.le]
  have h1 : AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q)
      (volume.restrict s) := (hw.smul hc).aestronglyMeasurable hs
  have h2 := (aestronglyMeasurable_indicator_iff hs).mpr h1
  refine h2.congr ?_
  have hN1 : ∀ a : Fin r, volume {q : (Fin r → ℂ) × ℂ | q.1 a = 0} = 0 := by
    intro a
    have h0 : volume {x : Fin r → ℂ | x a = 0} = 0 := by
      have he : {x : Fin r → ℂ | x a = 0} = Function.eval a ⁻¹' {0} := rfl
      rw [he, MeasureTheory.volume_pi]
      first
        | exact MeasureTheory.Measure.pi_eval_preimage_null _ (measure_singleton 0)
        | exact MeasureTheory.Measure.pi_eval_preimage_null (measure_singleton 0)
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_fst h0
  have hN2 : volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = Tz k r D.z * Tz k r D.z'} = 0 := by
    have hsph : volume (Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r D.z * Tz k r D.z'))) = 0 := by
      first
        | exact MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) _
        | exact MeasureTheory.Measure.addHaar_sphere (0 : ℂ) _
    have h0 : volume {z : ℂ | Complex.normSq z = Tz k r D.z * Tz k r D.z'} = 0 := by
      refine measure_mono_null (fun z hz => ?_) hsph
      simp only [Set.mem_setOf_eq] at hz
      rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_snd h0
  have hA : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), ∀ a : Fin r, q.1 a ≠ 0 :=
    ae_all_iff.mpr fun a => ae_iff.mpr (by simpa using hN1 a)
  have hB : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), Complex.normSq q.2 ≠ Tz k r D.z * Tz k r D.z' :=
    ae_iff.mpr (by simpa using hN2)
  filter_upwards [hA, hB] with q hqa hqb
  classical
  by_cases hq : q ∈ s
  · simp [Set.indicator_apply, hq]
  · simp only [Set.indicator_apply, hq, if_false]
    have hlt : Complex.normSq q.2 < Tz k r D.z * Tz k r D.z' := by
      have hn : ¬ (Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) := fun h => hq ⟨hqa, h⟩
      exact lt_of_le_of_ne (not_lt.mp hn) hqb
    have hz : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := by
      unfold bcWeight
      rw [if_neg (not_le.mpr hlt)]
    rw [hz, zero_smul]

end general

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5.Rad

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_uEquiv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : Mx k r) {h h' : Mx k r} (hh : h ∈ UWset k r D.z)
    (hh' : h' ∈ UWset k r D.z') : B.JF D F (h * g * h') = (D.π h).comp ((B.JF D F g).comp (D.π' h')) := by
  have := P.B5.haar_sigmaFinite D.haarW
  have := P.B5.haar_sigmaFinite D.haarN
  have := P.B5.haar_sigmaFinite D.haarW'
  exact bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

theorem radJFExists : RadJFExists := by
  intro Wp Wq _ _ _ _ _ _ Pa z z' π π' D F _hP hz hz' hπ hπ' hF
  subst hz hz' hπ hπ'
  classical
  let Φf : Fn Pa.k Pa.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) c g else 0
  have hsm := sf_resG (jf_smoothLev D F hF.1)
  have hmem : Φf ∈ RadSp Pa.k Pa.r D.z D.z' D.π D.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = 0
      rw [if_neg (by simpa using hx)]
    · obtain ⟨U, Fe, hU, hxU, hFe, hΦ⟩ := hsm x₀
        ⟨hx₀.1, wCell_mem_omPlus D.z_mem D.z'_mem hx₀.1 hx₀.2.1 hx₀.2.2⟩ hx₀.2.1
      have hV : IsOpen {x : (Fin Pa.r → ℂ) × Mx Pa.k Pa.r | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2} :=
        ((P.Qx3.isOpen_OmX Pa.r).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((P.Qx5.GGl_continuous Pa.k Pa.r D.z D.z').comp continuous_snd))
      refine ⟨U ∩ {x | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2}, Fe, hU.inter hV,
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hFe.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
      rw [if_pos hxD]
      exact hΦ x hx.1 hxG
    · have hx' : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := by simpa using hx
      show (if (x.1, h * x.2 * h') ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 (h * x.2 * h') else 0) =
        (D.π h).comp ((if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0).comp (D.π' h'))
      rw [if_pos (domR_uw hx hh hh'), if_pos hx']
      unfold resG
      have e : wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * (h * x.2 * h') =
          h * (wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) * h' := by
        have hc := P.Qx3.wlist_comm (k := Pa.k) (Fin.last Pa.r) x.1
          ((List.finRange Pa.r).filter fun a => a.val < (Fin.last Pa.r).val)
          (fun a ha => by simpa using (List.mem_filter.1 ha).2) (P.Qx3.uw_glev (Fin.last Pa.r) hh)
        change wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * h = h * wCell Pa.k Pa.r (Fin.last Pa.r) x.1 at hc
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc h]
      rw [e, jf_uEquiv D F _ hh hh']
      ext v
      simp
  exact ⟨⟨Φf, hmem⟩, fun x hx => by
    show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
    rw [if_pos (by simpa using hx)]⟩

end Formalism.FourierDecayAlt.P5
end
end

section

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem self_adjoint_cover_holds : SACover := by
  intro k r z z' hz hz' g hg
  obtain ⟨hg0, hD, hG⟩ := hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, hgeq⟩ := Formalism.FourierDecayAlt.P.big_cell_decomposition k r z z' g hg0.1 hD
  have e : bigCell k r c μ = wCell k r (Fin.last r) c * B2.embWb k r μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  have hg1 : B2.embWb k r μ ∈ Glev k r (Fin.last r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mem_UWb hμ)
  have hninv : n⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn

  have hDinv : ∀ l, Dmin k r z z' g l = Dmin k r z z' (bigCell k r c μ) l := by
    intro l
    rw [hgeq]
    exact dInv k r z z' hz hz' _ (Formalism.FourierDecayAlt.P.BigCellDecomposition.n_inv_S hn) _ (Formalism.FourierDecayAlt.P.BigCellDecomposition.n_S hn') _ l
  have hGb : 0 < Gf k r z z' (bigCell k r c μ) := by
    have e2 : Gf k r z z' g = Gf k r z z' (bigCell k r c μ) := by
      unfold Gf; rw [hDinv, hDinv]
    rw [← e2]; exact hG
  have hGG : 0 < GGl k r z z' (B2.embWb k r μ) := by
    have hmin := big_cell_minors_holds k r z z' c μ hz hz'
    have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (B2.embWb k r μ) := by
      rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
        Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
    have hzeta := hmin.2.2 hc
    rw [hζ] at hzeta
    have hr := hmin.1 (Fin.last r)
    set Pd := Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ with hPd
    have hP0 : Pd ≠ 0 := by
      have : Pd = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1)) =
        zetaL k r z z' (Fin.last r) (B2.embWb k r μ) * Pd := by
      unfold Formalism.QuantumDeterminants.zeta at hzeta
      rw [← hPd] at hzeta
      have h2 := div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hzeta] at h2
      exact h2.symm
    have hGb' := hGb
    unfold Gf at hGb'
    rw [hlast, ← hPd, Complex.normSq_mul] at hGb'
    have h1 : 0 < Complex.normSq Pd := Complex.normSq_pos.2 hP0
    unfold GGl
    nlinarith
  refine ⟨n⁻¹, ⟨hninv, hninv.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, n', ⟨hn', hn'.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩,
    c, hc, B2.embWb k r μ, hg1, hGG, ?_⟩
  rw [hgeq, e]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end
