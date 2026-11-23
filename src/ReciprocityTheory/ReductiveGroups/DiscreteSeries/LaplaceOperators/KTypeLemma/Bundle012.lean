module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeLink
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeVectorExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.MemEigenTensorSpaceIff
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolPowerDetDiag
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.IndicatorRholMem
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RealSmulCj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.WeightVectorTensorEqDual
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.OfDInjective

@[expose] public section

section

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem k2V (n : ℕ) : EigenspaceWeightConeStandard n := by
  intro ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq
  obtain ⟨T, μ, ι, hμ, hιK, hcoef⟩ := k2vLink n ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq
  obtain ⟨hEM, hlow, hwt, hgen⟩ := k2vM lam μ hμ
  have hVst := hV.2.1
  have : FiniteDimensional ℂ V := hV.1
  have hw0 := lowestKType_vector_exists ε lam σ D E V hσ hD hV T ι hιK
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hU' : ∀ a b, ε a = ε b → ∀ x y : D, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ := by
    intro a b hab x y
    rw [hU a b x y, adjSign, if_pos hab, one_mul]
  have hℓ : ∀ (a : Fin n) (v w : V), (w : D) = E a a v →
      submoduleEvaluationFunctional V (ι.symm T.w) w = ((lowK ε lam a : ℝ) : ℂ) * submoduleEvaluationFunctional V (ι.symm T.w) v := by
    intro a v w hw
    change ⟪((ι.symm T.w : V) : D), (w : D)⟫_ℂ =
      ((lowK ε lam a : ℝ) : ℂ) * ⟪((ι.symm T.w : V) : D), (v : D)⟫_ℂ
    rw [hw, ← hU' a a rfl, hw0.1 a, inner_smul_left, Complex.conj_ofReal]
  refine lowestKType_tensor_lift ε lam s hanti E (genSub E V) (eMM μ) (phiMM μ) hEM hlow hwt hgen (sT E V)
    (sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w))) (sES V) (sA ε E V hVst)
    (sA_isKRel ε E V hVst hD.glRep) (sT_sES E V) (sθ_sES V _ _ _)
    (fun a b hab => sA_comm_sES ε E V hVst a b hab) ?_ ?_ ?_
  · intro a x
    exact sθ_sA ε E V hVst (eMM μ) hEM (phiMM μ) (lam + rho n) (lowK ε lam) hwt (submoduleEvaluationFunctional V (ι.symm T.w)) hℓ a x
  · intro W hW hθ
    exact lowestKType_trace ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq T μ ι hμ hιK hcoef W hW hθ
  · intro μ' f hf hk
    exact lift_highestWeightVector ε E V hVst hD.glRep hU' μ' f hf hk

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section

noncomputable section

open ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS DualRepresentationReversal

theorem dualKType_of_standardKType (n : ℕ) (hK : LowestKTypeEulerTensorStandard n) : LowestKTypeEulerTensorDual n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgl hp hq f hf
  have hint' : ∀ a, ∃ m : ℤ, lamd lam a - ((n : ℝ) - 1) / 2 = (m : ℝ) := fun a => by
    obtain ⟨m, hm⟩ := hint (Fin.rev a)
    refine ⟨-m - ((n : ℤ) - 1), ?_⟩
    change -lam (Fin.rev a) - ((n : ℝ) - 1) / 2 = ((-m - ((n : ℤ) - 1) : ℤ) : ℝ)
    push_cast
    linarith
  have hc' : ∀ v ∈ cjV V, casimir (Edd ε E) v = (casVal (lamd lam) : ℂ) • v := fun v hv => by
    rw [← ofD_toD v, casimir_Edd, hc _ ((mem_cjV v).1 hv), casVal_rev, ofD_smul, Complex.conj_ofReal]
  have hVK' : ∀ k ∈ Kset (ε ∘ Fin.rev), ∀ v ∈ cjV V, ∃ w ∈ cjV V, (w : Cj H) = sdd σ k v :=
    fun k hk v hv => by
      obtain ⟨w, hw, hweq⟩ := hVK (sub k) (K_sub hk) (toD v) ((mem_cjV v).1 hv)
      exact ⟨ofD w, (mem_cjV _).2 hw, hweq⟩
  have hgl' := gapLap_rev hgl
  have key := hK (ε ∘ Fin.rev) (lamd lam) h (Cj H) (sdd σ) (cjSub D) (Edd ε E) (cjV V) (urep_sdd hσ)
    (derived_sdd hD) (kirr_cjV hV) hc' hVK' hint' hgl'.1 hgl' (by rwa [pOf_rev]) (by rwa [qOf_rev])
    (Tf ε f) (fun c => mem_genSub_Edd ε E V (Submodule.smul_mem _ _ (hf _)))
  have hθ : thV (lamd lam) = fun t => thVd lam (Fin.rev t) := rfl
  rw [hθ, prodShift_rev] at key
  have hl := list_inter (Tfh ε) (Tf_smul ε) (eeV (Edd ε E)) (eeVd E) (fun g => (weightVector_tensor_eq_dual ε E g).symm)
    (List.ofFn (thVd lam)) f
  rw [← prodShift_eq, ← prodShift_eq] at hl
  have h2 : Tfh ε (prodShift (eeVd E) (thVd lam) f) = 0 := by rw [hl]; exact key
  exact Tf_inj ε h2

theorem k1Vd (n : ℕ) : LowestKTypeEulerTensorDual n :=
  dualKType_of_standardKType n (k1V n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
