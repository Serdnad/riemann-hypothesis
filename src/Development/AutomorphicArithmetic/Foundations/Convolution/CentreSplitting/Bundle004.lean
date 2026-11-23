module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle002
public import GroundTheory.AutomorphicForms.L2LocalComponents
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle001
public import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty
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

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.twUnitary :
    UpperTheory.ConvolutionTheory.Dp.TwUnitary := by
  intro K _ _ n μ _ θ
  obtain ⟨U, hU, hint, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary K n μ θ
  have h : ∀ v, θ.U v = U v := fun v => by rw [← hU]; rfl
  refine ⟨fun v => ?_, fun w => ?_, fun g v => ?_⟩
  · rw [h]; exact U.norm_map v
  · obtain ⟨v, hv⟩ := U.surjective w
    exact ⟨v, (h v).trans hv⟩
  · rw [h, h]; exact hint g v
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V


theorem UpperTheory.ConvolutionTheory.Dp.closureSummand :
    UpperTheory.ConvolutionTheory.Dp.ClosureSummand := by
  intro K _ _ n μ _ U hU hs h0 hirr
  have hcl : IsClosed (cuspidalL2 μ : Set (LL μ)) := (completeSpace_coe_iff_isComplete.1 (inferInstanceAs (CompleteSpace (CuspL2 μ)))).isClosed
  have hle : (U.map (clsL μ)).topologicalClosure ≤ cuspidalL2 μ :=
    Submodule.topologicalClosure_minimal _ (by rintro _ ⟨φ, -, rfl⟩; exact toLp_mem μ _) hcl
  have hI := isInvariant_topologicalClosure_map μ hU hs.ρ hs.σ hs.τ
  have hmap : ∀ y ∈ (U.map (cuspVecL μ)).topologicalClosure, toLp μ y ∈ (U.map (clsL μ)).topologicalClosure := fun y hy =>
    Submodule.topologicalClosure_minimal (U.map (cuspVecL μ))
      (t := (U.map (clsL μ)).topologicalClosure.comap (toLp μ).toLinearMap)
      (by rintro _ ⟨φ, hφ, rfl⟩; exact Submodule.le_topologicalClosure (U.map (clsL μ)) ⟨φ, hφ, rfl⟩)
      ((Submodule.isClosed_topologicalClosure _).preimage (toLp μ).continuous) hy
  refine ⟨hle, Submodule.isClosed_topologicalClosure _, fun g v hv => ?_, fun e => h0 ?_, fun V' hV' hc hi => ?_⟩
  · refine mem_of_mem_topologicalClosure (Submodule.isClosed_topologicalClosure _) (rightRegularRep (rationalGLOne (K := K) (n := n)) μ g) ?_ hv
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmap _ (hI g _ (Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩))
  · refine eq_bot_iff.2 fun φ hφ => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hU hφ) (toLp_injective μ ?_)
    have h1 : clsL μ φ ∈ (U.map (clsL μ)).topologicalClosure := Submodule.le_topologicalClosure _ ⟨φ, hφ, rfl⟩
    rw [e, Submodule.mem_bot] at h1
    exact h1.trans (map_zero (toLp μ)).symm
  · refine or_iff_not_imp_left.2 fun hne => le_antisymm hV' ?_
    set W := V'.comap (toLp μ).toLinearMap with hW
    have hWc : IsClosed (W : Set (CuspL2 μ)) := hc.preimage (toLp μ).continuous
    have hWi : (cuspRepT μ).IsInvariant W := fun g v hv => hi g _ hv
    have hW0 : W ≠ ⊥ := by
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact (Submodule.ne_bot_iff _).2 ⟨(⟨v, hle (hV' hv)⟩ : cuspidalL2 μ), hv, fun e => hv0 (congrArg Subtype.val e)⟩
    obtain ⟨φ, hφ, hφ0, hφW⟩ := exists_cuspForm_mem_of_ne_bot μ hWc hWi hW0
    have h1 : summandCuspForms W ≤ U := fun ψ hψ => by
      rw [← formsClosure K n μ U hU hs]
      exact ⟨hψ.1, hV' hψ.2⟩
    rcases hirr _ h1 ⟨summandCuspForms_stable_ρ hWc hWi, summandCuspForms_stable_σ hWi, summandCuspForms_stable_τ hWi⟩ with e | e
    · have h2 : φ ∈ summandCuspForms W := mem_summandCuspForms.2 ⟨hφ, hφW⟩
      rw [e, Submodule.mem_bot] at h2
      exact (hφ0 h2).elim
    · have hmin : U.map (clsL μ) ≤ V' := by
        rintro _ ⟨ψ, hψ, rfl⟩
        have h3 : ψ ∈ summandCuspForms W := e.ge hψ
        exact (mem_summandCuspForms.1 h3).2
      exact fun v hv => closure_minimal (show ((U.map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) ⊆ V' from hmin) hc hv
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.formsIrr :
    UpperTheory.ConvolutionTheory.Dp.FormsIrr := by
  intro K _ _ n μ _ V hV
  obtain ⟨hcs, hI, hirr⟩ := sumT K n μ V hV
  have hc : IsClosed ((V.comap (toLp μ).toLinearMap : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) :=
    hV.closed.preimage (toLp μ).continuous
  have e : formsIn μ V = summandCuspForms (V.comap (toLp μ).toLinearMap) := by
    rw [formsIn, clsL, Submodule.comap_comp, summandCuspForms]
  have hne := summandCuspForms_ne_bot μ _ hI hirr
  have hcl := topologicalClosure_map_summandCuspForms hc hI hirr hne
  have h1 := summandCuspForms_stable_ρ hc hI
  have h2 := summandCuspForms_stable_σ hI
  have h3 := summandCuspForms_stable_τ hI
  have h4 := fun W hW a b c d => eq_summandCuspForms (W := W) hc hI hirr hW a b c d
  rw [← e] at hne hcl h1 h2 h3 h4
  refine ⟨⟨h1, h2, h3⟩, hne, fun W hW hs => ?_, ?_⟩
  · exact (em (W = ⊥)).imp_right fun h0 => h4 W hW hs.ρ hs.σ hs.τ h0
  · refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_ hV.closed) fun v hv => ?_
    · exact Submodule.map_le_iff_le_comap.2 inf_le_right
    · obtain ⟨u, rfl⟩ : ∃ u : CuspL2 μ, toLp μ u = v := ⟨(⟨v, hV.le hv⟩ : cuspidalL2 μ), rfl⟩
      have hu : u ∈ closure (((formsIn μ V).map (cuspVecL μ) : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) := by
        rw [← Submodule.topologicalClosure_coe, hcl]
        exact hv
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      refine map_mem_closure (toLp μ).continuous hu fun x hx => ?_
      obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hx
      exact Submodule.mem_map_of_mem (f := clsL μ) hφ
end
