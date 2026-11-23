module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.RowMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momZero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, (∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0) → ∀ φ ∈ Fock D.δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    ∫ x : IdeleGroup F × G1 F, p (row (mD x.1 * x.2)) * T.indicator 1 (finPartPi (row (mD x.1 * x.2))) * iw (w1 W f.1 φ 1) x ∂M.ν = 0 := by
  intro F E _ _ _ _ _ _ _ D W M π f hf h0 φ hφ p hp T hc ho
  obtain ⟨φ', hφ', he⟩ := hatSurj F D.δ D.neg _
    ((fockMul F D.δ).1 _ (hatFock F D.δ _ (mem_fock.1 hφ)) p hp T hc ho)
  have hrow := rowMul F E D W (fun r => p r * T.indicator 1 (finPartPi r)) φ φ'
    (fun v => by rw [he])
  have hw : ∀ g : G1 F, w1 W f.1 φ' 1 g =
      p (row g) * T.indicator 1 (finPartPi (row g)) * w1 W f.1 φ 1 g := by
    intro g
    have hr : (![(0 : A F), 1] ᵥ* g.1) = row g := by
      ext i
      simp [row, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h1 := hrow g ![0, 1, 1, 0]
    have h2 : (![(![0, 1, 1, 0] : V4 F) 0, (![0, 1, 1, 0] : V4 F) 1] : Fin 2 → A F) = ![0, 1] := by
      ext i
      fin_cases i <;> rfl
    rw [h2, hr] at h1
    simp only [w1, map_one, Module.End.one_apply]
    rw [h1]
    ring
  have hz := h0 φ' hφ'
  rw [← hz]
  simp only [W1, Meas.I0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [iw, hw]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.uxCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2) (s : (A F)ˣ) (h : GL (Fin 2) (A E)), ∃ (h₁ : GL (Fin 2) (A E)) (c : ℂ), nu F h = s ^ 4 * nu F h₁ ∧
    ∀ f ∈ π.V, ∀ φ ξ g, ux W f.1 φ h ξ g = c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) := by
  intro F E _ _ _ _ _ _ _ D W π s h
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨z, hz⟩ : ∃ z : (A E)ˣ, ideleNorm F E z = s ^ 2 := ⟨ideleEmbedding F E s, D.ideleNorm_emb s⟩
  obtain ⟨hL, hnu⟩ := UpperTheory.ConvolutionTheory.R2.Ff.lCen F E D W z
  rw [hz] at hL hnu
  obtain ⟨h₁, rfl⟩ : ∃ h₁, h = Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁ :=
    ⟨_, (mul_inv_cancel_left _ _).symm⟩
  have hnh : nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) = s ^ 4 * nu F h₁ := by
    rw [nu_mul, hnu, ← pow_mul]
  refine ⟨h₁, ((ω (s ^ 2) : ℂˣ) : ℂ), hnh, fun f hf φ ξ g => ?_⟩
  have e0 : dM (s ^ 4) = gl (mD (s ^ 2)⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) := by
    rw [← gl_mD_mul_dM_sq (s ^ 2), mD_inv, gl_inv, inv_mul_cancel_left, ← pow_mul]
  have e1 : gl g * dM (s ^ 4 * nu F h₁) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) * (gl (g * mD (s ^ 2)⁻¹) * dM (nu F h₁)) := by
    rw [dM_mul, e0, mul_assoc (gl _) _ (dM _), UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (dM _),
      UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (gl _ * dM _), gl_mul]
    simp only [mul_assoc]
  have e2 : W.Om g (W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) φ) =
      W.Om (g * mD (s ^ 2)⁻¹) (W.L h₁ φ) := by
    rw [map_mul, hL, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [ux, ux, hnh, e1, hω f hf, e2, mul_assoc]
end
