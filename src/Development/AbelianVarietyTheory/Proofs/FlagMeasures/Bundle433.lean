module

public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle427
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle430
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_hsNorm_le_degreeBound_realPlace : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → ∀ (j : ℕ) (hj : j ≤ D.R.rS) (q : ℕ) (γ : Mat D.R.k D.R.rS) (s H₁ De : ℝ) (μR νR : Measure (Mt D.R.k D.R.rS)), 1 ≤ j → j + 2 ≤ D.R.k → 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ q → 0 < s → 1 ≤ H₁ → TailBd W.z W.νS A.Φ q H₁ → TailBd W.z' W.νS' A.Φ' q H₁ → DeOK D.R.k D.R.rS W.z W.z' γ De → IsNormalFormStabilizerMeasure D.R.k D.R.rS hj W.z W.z' γ s μR → IsQuotMeas W.μG μR νR → Real.sqrt (hsNormSq (A.J νR γ)) ≤ Real.sqrt (Module.finrank ℂ W.Wp) * (((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) / s * degBd D.R.k D.R.rS j q H₁ De (Dj D.R.k D.R.rS hj W.z W.z' γ) (sgV D.R.k D.R.rS W.z W.z' γ H₁)) := by
  first | exact @GlobalTheory.Amp.sqrt_hsNormSq_amplitude_le_degBd | exact GlobalTheory.Amp.sqrt_hsNormSq_amplitude_le_degBd | (intros; apply GlobalTheory.Amp.sqrt_hsNormSq_amplitude_le_degBd <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.pi_unipotentModel_measurable_full_measure : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.pi_nset_full | exact GlobalTheory.SnMass.VolN.pi_nset_full | (intros; apply GlobalTheory.SnMass.VolN.pi_nset_full <;> assumption)
end
