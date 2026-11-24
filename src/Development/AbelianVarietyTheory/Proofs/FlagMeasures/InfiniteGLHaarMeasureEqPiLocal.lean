module

import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FormHeightOneEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarPi

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  first | exact _root_.GlobalTheory.GaussMarginal.lintegral_pi_fin | exact @_root_.GlobalTheory.GaussMarginal.lintegral_pi_fin | apply _root_.GlobalTheory.GaussMarginal.lintegral_pi_fin <;> assumption

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hrw : ∀ y : Fin (Fintype.card ι) → E,
      ∏ i, f i (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e y i) = ∏ k, f (e k) (y k) := by
    intro y
    rw [← e.prod_comp]
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hrw]
  rw [lintegral_pi_fin _ μ (fun k => f (e k)) (fun k => hf (e k))]
  exact e.prod_comp (fun i => ∫⁻ t, f i t ∂μ)

theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  first | exact _root_.GlobalTheory.GaussMarginal.pi_withDensity_const | exact @_root_.GlobalTheory.GaussMarginal.pi_withDensity_const | apply _root_.GlobalTheory.GaussMarginal.pi_withDensity_const <;> assumption

theorem haarGL_eq_pi : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  intro E _ _ j
  set F : (Fin j → Fin j → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)
  have hF : Measurable F := by
    have hc : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := continuous_id.matrix_det
    exact ENNReal.measurable_ofReal.comp
      (((hc.norm.pow 2).measurable.inv).pow_const j)
  have : SigmaFinite ((volume : Measure (Fin j → Fin j → ℂ)).withDensity F) :=
    inferInstanceAs (SigmaFinite (haarLoc j))
  have hloc : haarLoc j = (volume : Measure (Fin j → Fin j → ℂ)).withDensity F := rfl
  simp only [hloc]
  rw [pi_withDensity (ι := InfinitePlace E) volume F hF, ← volume_pi, haarGL]
  congr 1
  funext x
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => by positivity]
  congr 1
  unfold MatInf at x
  unfold detNorm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]

end GlobalTheory.HaarPi
