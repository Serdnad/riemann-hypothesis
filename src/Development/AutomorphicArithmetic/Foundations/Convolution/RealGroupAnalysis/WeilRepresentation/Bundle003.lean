module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle010
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle016
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieZ
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle012
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle010
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.stable :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Stable W M π := by
  intro F E _ _ _ _ _ _ _ D W M π o Φ hΦ
  refine (Submodule.span_le.2 ?_ : span W M π ≤ (span W M π).comap (act o)) hΦ
  rintro Ψ ⟨f, hf, φ, hφ, e⟩
  cases o with
  | fin k =>
    obtain ⟨f', hf', φ', hφ', h⟩ := finLift F E D W M π f hf φ hφ k
    exact Submodule.subset_span ⟨f', hf', φ', hφ', funext fun g => (congrFun e _).trans (h g)⟩
  | cpt k => exact (kFin F E D W M π f hf φ hφ Ψ e).1 k
  | lie X =>
    obtain ⟨O⟩ := UpperTheory.ConvolutionTheory.R2.Fo.opsEx F
    obtain ⟨Y, s, hY, rfl, -⟩ := lieSplit X
    change lie E 2 (Y + zE s) Ψ ∈ span W M π
    rw [map_add (f := _), LinearMap.add_apply]
    exact add_mem (Submodule.subset_span ⟨f, hf, _, dLFock F E D O Y φ hφ, lieL F E D O W M π f hf φ hφ Y hY Ψ e⟩)
      (Submodule.subset_span ⟨_, π.stable (.lie _) f hf, φ, hφ, lieZ F E D W M π f hf φ hφ s Ψ e⟩)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.cusp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Cusp W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Φ hΦ
  have hG : Good D Φ.1 := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hφ, e⟩ := hx
      rw [e]
      exact G.goodLift F E D W M π h0 f hf φ hφ
    | zero => exact (G.goodSpan F E D).1
    | add x y _ _ hx hy => exact (G.goodSpan F E D).2.1 _ _ hx hy
    | smul c x _ hx => exact (G.goodSpan F E D).2.2 c _ hx
  refine ⟨G.cuspE F E D _ hG.left hG.zero, fun hW => Subtype.ext (funext fun h => ?_)⟩
  have hs := hG.sum h
  simp only [hW] at hs
  exact hs.unique hasSum_zero
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.ne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Ne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π
  obtain ⟨f, hf, a, k, hk, hW⟩ := G.exIw F M π
  obtain ⟨φ, hφ, hp⟩ := G.exPhi F E D W a k hk
  by_contra hn
  have h0 : ∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0 := fun φ hφ => by
    by_contra h1
    exact hn ⟨f, hf, φ, hφ, 1, h1⟩
  have h := G.zeroW F E D W M π f hf h0 φ hφ a k hk
  have e : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
  simp only [w1, e, dM_one, mul_one, map_one, Module.End.one_apply] at h
  exact mul_ne_zero hW hp h
end
