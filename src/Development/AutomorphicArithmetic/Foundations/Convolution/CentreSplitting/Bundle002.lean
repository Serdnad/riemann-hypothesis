module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.V

namespace UpperTheory.ConvolutionTheory.Dp

def TwUnitary : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ), (∀ v, ‖θ.U v‖ = ‖v‖) ∧ Function.Surjective θ.U ∧
      ∀ g v, θ.U (rightRegularRep (rationalGLOne (K := K) (n := n)) μ g v) = rightRegularRep (rationalGLOne (K := K) (n := n)) μ (θ.e g) (θ.U v)

def TwCls : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ), ∀ φ ∈ centralCuspForms K n, ∀ ψ ∈ centralCuspForms K n,
      (θ.U (clsL μ ψ) = clsL μ φ ↔ ∀ x : normOneGL (K := K) (n := n), ψ.1 x = φ.1 (θ.e x : normOneGL (K := K) (n := n)))

def TwSummand : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (V : Submodule ℂ (LL μ)), IsSummand μ V ↔ IsSummand μ (V.map θ.U.toLinearMap)

def GalCentral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E),
    UpperTheory.CBC.IsGalAd σ s → (∀ s', UpperTheory.CBC.IsGalAd σ s' → s' = s) ∧
      ∀ t, Matrix.GeneralLinearGroup.map s.toRingHom (centralSection E n t) = centralSection E n t

def ConjCarries : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E), UpperTheory.CBC.IsGalAd σ s →
    (∀ g : normOneGL (K := E) (n := n), ((θ.e g : normOneGL (K := E) (n := n)) : GA E n) = Matrix.GeneralLinearGroup.map s.toRingHom (g : GA E n)) →
    ∀ (π π' : CuspSub E n) (V' : Submodule ℂ (LL μ)),
      (UpperTheory.CBC.Cusp.cx π').space =
        (fun f : GA E n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (UpperTheory.CBC.Cusp.cx π).space →
      (Carries μ π' V' ↔ Carries μ π (V'.map θ.U.toLinearMap))

def ConjIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E), UpperTheory.CBC.IsGalAd σ s →
    (∀ g : normOneGL (K := E) (n := n), ((θ.e g : normOneGL (K := E) (n := n)) : GA E n) = Matrix.GeneralLinearGroup.map s.toRingHom (g : GA E n)) →
    ∀ (π : CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V →
      ((UpperTheory.CBC.Cusp.cx π).ConjIso σ ↔ V.map θ.U.toLinearMap = V)

end UpperTheory.ConvolutionTheory.Dp
end
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.clsBasic :
    UpperTheory.ConvolutionTheory.Dp.ClsBasic := by
  intro K _ _ n μ _
  have hr : ∀ φ : cuspForms K n, IsContRep μ (clsL μ φ)
      (fun y => (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n)) := fun φ => isContRep_cuspToL2 μ φ
  refine ⟨fun φ hφ h => eq_zero_of_cuspVecL_eq_zero hφ (toLp_injective μ (h.trans (map_zero (toLp μ)).symm)),
    fun φ => (cuspToL2 μ φ).2, fun φ hφ ψ g h => ?_, fun φ _ => ?_⟩
  · have h1 := (hr φ).translate (retractOne g)
    have e : (fun y : normOneGL (K := K) (n := n) => (φ : AdelicGLn.AdelicGL K n → ℂ) ((y * retractOne g : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n)) =
        fun y : normOneGL (K := K) (n := n) => (ψ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n) := funext fun y => by
      have e1 : g = (retractOne g : AdelicGLn.AdelicGL K n) * centralSection K n (detModule K n g) := by
        rw [coe_retractOne, inv_mul_cancel_right]
      rw [h]
      conv_rhs => rw [e1, ← mul_assoc, apply_mul_centralSection_of_mem hφ]
      rfl
    have h2 : IsContRep μ (RG μ g (clsL μ φ)) fun y : normOneGL (K := K) (n := n) => (ψ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n) := by
      rw [← e]
      exact h1
    exact Lp.ext ((hr ψ).ae_eq_quotFun.trans h2.ae_eq_quotFun.symm)
  · refine (hr φ).ae_eq_quotFun.trans (Filter.Eventually.of_forall fun y => ?_)
    conv_lhs => rw [← Quotient.out_eq y]
    rfl
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.formsClosure :
    UpperTheory.ConvolutionTheory.Dp.FormsClosure := by
  intro K _ _ n μ _ U hU hs
  have hsup := sup_orthRel_centralCuspForms μ U hU hs.ρ hs.τ
  have hin : ∀ a b : cuspForms K n, inner ℂ (clsL μ a) (clsL μ b) = inner ℂ (cuspToL2 μ a) (cuspToL2 μ b) :=
    fun _ _ => rfl
  apply le_antisymm
  · rintro φ ⟨hφc, hφV⟩
    have hφc' := hφc
    rw [← hsup] at hφc'
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hφc'
    have huV : clsL μ u ∈ (U.map (clsL μ)).topologicalClosure :=
      Submodule.le_topologicalClosure _ ⟨u, hu, rfl⟩
    have hcV : clsL μ c ∈ (U.map (clsL μ)).topologicalClosure := by
      have h : clsL μ (u + c) ∈ (U.map (clsL μ)).topologicalClosure := hφV
      rw [map_add (f := _)] at h
      simpa only [add_sub_cancel_left] using Submodule.sub_mem _ h huV
    have hle : U.map (clsL μ) ≤ (ℂ ∙ clsL μ c)ᗮ := by
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hin]
      exact hc.2 v hv
    have h2 := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _) hcV
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hin, inner_self_eq_zero] at h2
    have h0 : c = 0 :=
      injOn_cuspToL2 μ (hc.1 : _) (fun _ _ => rfl) (h2.trans (map_zero (cuspToL2 μ)).symm)
    rw [h0, add_zero]
    exact hu
  · intro φ hφ
    exact ⟨hU hφ, Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩⟩
end
