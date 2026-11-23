module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle027
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRayClassFamilyFOneGeOfRealCharacter
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle029
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle030
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryBlockEmbeddingOntoStabiliser
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧ ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧ ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 → IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  first | exact @GlobalTheory.Alc.rowE_rowWeight | exact GlobalTheory.Alc.rowE_rowWeight | (intros; apply GlobalTheory.Alc.rowE_rowWeight <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.traceEPowerHighestWeightValue_generating_series : ∀ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R), (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) = ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.Alc.hcVal_generating | exact GlobalTheory.Alc.hcVal_generating | (intros; apply GlobalTheory.Alc.hcVal_generating <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.norm_rayClassFamily_F_one_ge_of_real_character : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), χ * χ = 1 → c / 𝓕.B ^ A ≤ ‖𝓕.F χ 1‖ := by
  first | exact @GlobalTheory.Hk.RealChar.norm_F_one_ge | exact GlobalTheory.Hk.RealChar.norm_F_one_ge | (intros; apply GlobalTheory.Hk.RealChar.norm_F_one_ge <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 < s.re → LSeriesSummable (𝓕.lamChi χ) s ∧ ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries (𝓕.aChi χ) s‖ ∧ 𝓕.F χ s ≠ 0 ∧ -(deriv (𝓕.F χ) s / 𝓕.F χ s) + (if χ = 1 then 1 / (s - 1) else 0) = LSeries (𝓕.lamChi χ) s := by
  first | exact @GlobalTheory.Hk.LogDeriv.logDeriv_F | exact GlobalTheory.Hk.LogDeriv.logDeriv_F | (intros; apply GlobalTheory.Hk.LogDeriv.logDeriv_F <;> assumption)
end

section

open Complex
open scoped Real

theorem _root_.GlobalTheory.T.jacobiTriple_finite_product : ∀ (s x : ℂ), s ≠ 0 → ‖s‖ < 1 → x ≠ 0 → ∀ n : ℕ, ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  first | exact @GlobalTheory.JacobiTriple.finTriple | exact GlobalTheory.JacobiTriple.finTriple | (intros; apply GlobalTheory.JacobiTriple.finTriple <;> assumption)
end

section

open Complex
open scoped Real

theorem _root_.GlobalTheory.T.jacobi_triple_product_limit : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im → Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ) Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  first | exact @GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ | exact GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ | (intros; apply GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.quadricPointGauge_polarCoordinates_compare_tangentGauge : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanGauge u < t⁻¹ * r → ptGauge e (polarPt e u) < r) ∧ (ptGauge e (polarPt e u) < r → tanGauge u < t * r) := by
  first | exact @GlobalTheory.PolarCompare.polar_compare | exact GlobalTheory.PolarCompare.polar_compare | (intros; apply GlobalTheory.PolarCompare.polar_compare <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_isOrthogonalComplementIsometryEmbedding_translate : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ → ∀ g₀ : UpqT P Q, ∃ A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, IsPerpEmb (act g₀ (baseVec e)) A (fun g => g₀ * j₀ g * g₀⁻¹) := by
  first | exact @GlobalTheory.PerpFrameTranslate.exists_isPerpEmb | exact GlobalTheory.PerpFrameTranslate.exists_isPerpEmb | (intros; apply GlobalTheory.PerpFrameTranslate.exists_isPerpEmb <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.orthogonalComplement_unitary_embedding_conj_block : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ → ∀ (x₀ : Sp P Q) (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ) (j : UpqT P' Q' → UpqT P Q), qf x₀ = sg (e none) → IsPerpEmb x₀ A j → ∃ g₀ : UpqT P Q, act g₀ (baseVec e) = x₀ ∧ ∀ g, j g = g₀ * j₀ g * g₀⁻¹ := by
  first | exact @GlobalTheory.CompactDualQuot.PerpConj.perp_conj | exact GlobalTheory.CompactDualQuot.PerpConj.perp_conj | (intros; apply GlobalTheory.CompactDualQuot.PerpConj.perp_conj <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.unitaryExpLieBall_comparable_entryGauge : ∀ (P Q : ℕ) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), expBall P Q (t⁻¹ * r) ⊆ {g : UpqT P Q | gauge g < r} ∧ {g : UpqT P Q | gauge g < r} ⊆ expBall P Q (t * r) := by
  first | exact @GlobalTheory.ExpBallCompare.expBall_compare | exact GlobalTheory.ExpBallCompare.expBall_compare | (intros; apply GlobalTheory.ExpBallCompare.expBall_compare <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_tangent_borelSection_quadric : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), ∃ σ : Sp P Q → UpqT P Q, IsSection (sg (e none)) (baseVec e) σ ∧ ∀ y : Sp P Q, qf y = sg (e none) → y (e none) ≠ -1 → (∀ b, ‖UpqT.mat (σ y) (e none) (e (some b))‖ = ‖y (e (some b))‖) ∧ ∀ a b, ‖(UpqT.mat (σ y) - 1) (e (some a)) (e (some b))‖ = ‖y (e (some a))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖ := by
  first | exact @GlobalTheory.TangentSection.exists_tangent_section | exact GlobalTheory.TangentSection.exists_tangent_section | (intros; apply GlobalTheory.TangentSection.exists_tangent_section <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_unitaryBlockEmbedding_onto_stabiliser : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∃ j : UpqT P' Q' →* UpqT P Q, IsBlockEmb e j ∧ Topology.IsClosedEmbedding j ∧ Set.range j = {g | act g (baseVec e) = baseVec e} := by
  first | exact @GlobalTheory.BlockEmbedding.exists_blockEmb | exact GlobalTheory.BlockEmbedding.exists_blockEmb | (intros; apply GlobalTheory.BlockEmbedding.exists_blockEmb <;> assumption)
end
