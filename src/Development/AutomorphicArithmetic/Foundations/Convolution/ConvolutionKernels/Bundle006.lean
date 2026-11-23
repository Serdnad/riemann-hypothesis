module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
public import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.kerId :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f a g : CC K n) (M : L2 μ →L[ℂ] L2 μ),
      Rop μ f = Rop μ a ∘L M ∘L Rop μ g → ∀ x y : G1 K n,
        ∑ᶠ γ : Gam K n, f (x⁻¹ * (γ : G1 K n) * y) = ⟪kv μ a x, M (kv μ (ccStar g) y)⟫_ℂ := by
  intro K _ _ n μ _ f a g M hf x y
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have ext : ∀ u w : RightCosetSpace (Gam K n) → ℂ, Continuous u → Continuous w →
      u =ᵐ[quotientMeasure (Gam K n) μ] w → ∀ z : G1 K n, u (mk _ z) = w (mk _ z) := by
    intro u w hu hw h z
    have h1 := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) h
    exact congrFun ((hu.comp (continuous_mk _)).ae_eq_iff_eq μ (hw.comp (continuous_mk _)) |>.1 h1) z
  have s1 : ∀ φ : L2 μ, rconv (Gam K n) μ f φ x = rconv (Gam K n) μ a (M (Rop μ g φ)) x := by
    intro φ
    have e : Rop μ f φ = Rop μ a (M (Rop μ g φ)) := by rw [hf]; rfl
    refine ext _ _ (continuous_rconvQ _ μ f φ) (continuous_rconvQ _ μ a _) ?_ x
    have a1 := integrated_ae_eq_rconvQ (Gam K n) μ f φ
    have a2 := integrated_ae_eq_rconvQ (Gam K n) μ a (M (Rop μ g φ))
    change (Rop μ f φ : _ → ℂ) =ᵐ[_] _ at a1
    change (Rop μ a (M (Rop μ g φ)) : _ → ℂ) =ᵐ[_] _ at a2
    rw [e] at a1
    exact a1.symm.trans a2
  have s2 : kv μ f x = Rop μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x)) := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, s1, ← ropAdj, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, inner_kv]
  have a3 := integrated_ae_eq_rconvQ (Gam K n) μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x))
  change (Rop μ (ccStar g) _ : _ → ℂ) =ᵐ[_] _ at a3
  rw [← s2] at a3
  have s3 := ext _ _ (Complex.continuous_conj.comp ((continuous_quotientKernel (Gam K n) f).comp (Continuous.prodMk_right (mk _ x))))
    (continuous_rconvQ _ μ (ccStar g) _) ((kvAe K n μ f x).symm.trans a3) y
  simp only [Function.comp_apply, quotientKernel_mk, rconvQ_mk] at s3
  rw [← inner_kv, ContinuousLinearMap.adjoint_inner_right] at s3
  rw [← inner_conj_symm, ← s3, starRingEnd_self_apply]
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.ropPc :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      Rop μ f ∘L Pc μ = Pc μ ∘L Rop μ f := by
  intro K _ _ n μ _ f
  have h : ∀ g : CC K n, ∀ v ∈ cuspidalL2 μ, Rop μ g v ∈ cuspidalL2 μ := by
    intro g v hv
    rw [← Submodule.orthogonal_orthogonal (cuspidalL2 μ), Submodule.mem_orthogonal]
    intro u hu
    rw [Rop, inner_integrated_ccToL1]
    have : ∀ x, ⟪u, rightRegularRep (Gam K n) μ x v⟫_ℂ = 0 := fun x =>
      (Submodule.mem_orthogonal' _ _).1 hu _ (isInvariant_cuspidalL2 μ x v hv)
    simp [this]
  exact commProj (cuspidalL2 μ) (Rop μ f) (h f) (fun v hv => by rw [ropAdj]; exact h _ v hv)
end

section

open MeasureTheory NumberField PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.K

theorem UpperTheory.ConvolutionTheory.K.g0 :
    G0 := by
  refine ⟨fun F E _ _ _ _ _ _ σ _ n _ μ _ => ?_, fun F _ _ n μ _ g => ?_⟩
  · obtain ⟨θ, h⟩ := galTwistEx E n μ σ.toRingEquiv
    exact ⟨θ, fun g => by rw [galAdEq]; exact h g⟩
  · rw [galAdEq]
    ext i j : 2
    exact ((adBasic F).2.1 _).symm
end
