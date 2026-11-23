module

import CompanionTheory.AutomorphicTheory.ThetaDilations.FstarDil
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGaussianFourierStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatumStatement
public import Development.WeilBound.CoreStatements.ThetaDilations.IntFou
import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
import Development.WeilBound.CoreStatements.ThetaDilations.ProdRho
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem cG_dil {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} {B : Matrix ι ι F}
    {ρ : InfinitePlace F → (F →+* ℝ)} {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P) {a : F} (ha : a ≠ 0)
    (τ : InfinitePlace F → ℂ) : cG B ρ P (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) =
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)|⁻¹ ^ M) ^ 2 : ℝ) * cG B ρ P τ := by
  apply _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.cG_dil <;> assumption

theorem fstar_dil {R : Type} [CommRing R] {ι : Type} [Fintype ι] [TopologicalSpace R] [MeasurableSpace R]
    {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)} (H : NAQuad ψ h B μ) (a : Rˣ) {m : ℝ}
    (hm : 0 ≤ m) (hμ : ∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal m * μ s)
    (φ : (ι → R) → ℂ) (b : R) : m * fstar ψ h B μ (opD 1 (a : R) φ) ((a : R) ^ 2 * b) = fstar ψ h B μ φ b := by
  apply _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.fstar_dil <;> assumption

theorem ei_inv : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ b : F, eis ψ lf B ρ P (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = eis ψ lf B ρ P φ τ) ∧ (∀ a : F, a ≠ 0 → eis ψ lf B ρ P (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = eis ψ lf B ρ P φ τ) ∧ (cG B ρ P τ * eis ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = eis ψ lf B ρ P φ τ) ∧ ∀ c : ℂ, eis ψ lf B ρ P (c • φ) τ = c * eis ψ lf B ρ P φ τ := by
  apply _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.ei_inv <;> assumption

end PositivityTheory.PlacePermOperatorBicommutantSpan
