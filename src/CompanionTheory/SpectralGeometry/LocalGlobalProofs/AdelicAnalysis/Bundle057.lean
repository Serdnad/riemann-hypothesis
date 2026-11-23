module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle056
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.adelic_haar_measure_linear_change : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | exact GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale | (intros; apply GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.theta_average_integral_formula : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main | exact GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main | (intros; apply GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.weil_operator_integral_invariance : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  first | exact @GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic | exact GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic | (intros; apply GlobalTheory.CompanionTheory.SW.FstarPer.fstar_periodic <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.global_unit_scaling_haar_product_formula : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | exact GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | (intros; apply GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.dual_lattice_membership_trace : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff | exact GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.adelic_lattice_measure_formula : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (N : ℕ), 0 < N → (muF B lf (latN F ι N : Set (ι → A F))).toReal = kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) ^ Fintype.card ι := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.muF_latN | exact GlobalTheory.CompanionTheory.SW.ThW.muF_latN | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.muF_latN <;> assumption)
end
