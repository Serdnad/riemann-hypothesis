module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepSqInt
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IrredA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.Bundle002

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace CompanionTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hilbert_signature_holds : StepSig := by
  intro n ε lam T Ψ hP hst
  have hσ := rreg_isURepOn ε
  have hcoe : ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ T.w, ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x := by
    intro g hg x
    have hx : rreg ε g x ∈ Hlam ε Ψ T.w := hst g hg x x.2
    show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _
    exact congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  refine ⟨hcoe, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [hcoe 1 h1 x, hσ.1.1]
    rfl
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [ContinuousLinearMap.comp_apply, hcoe _ (mul_mem_unitaryJ ha hb) x,
      hcoe a ha, hcoe b hb, hσ.1.2 a ha b hb, ContinuousLinearMap.comp_apply]
  · intro g hg x
    have h := hσ.2.1 g hg (x : L2 ε)
    rw [← hcoe g hg x] at h
    simpa using h
  · intro v
    exact (Hlam ε Ψ T.w).orthogonalProjectionOnto.continuous.comp_continuousOn (hσ.2.2 (v : L2 ε))
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (datumV_ne_bot hP (HW.KType.w_ne_zero T))
    refine nontrivial_of_ne (⟨(x : L2 ε), UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) _ x hx⟩ : Hlam ε Ψ T.w) 0 ?_
    intro h
    apply hx0
    have h2 : (x : L2 ε) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2

end CompanionTheory.RgDs.Hilb
end
end

section

noncomputable section

open Finset Matrix MeasureTheory

namespace CompanionTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

def V1 {n : ℕ} (ε : Fin n → Bool) {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Submodule ℂ (L2 ε) :=
  (datumV ε Ψ T.w).map (smD ε (rreg ε)).subtype

def StepStable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      ∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w

def StepDatum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ)

def StepMoll : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W S : Submodule ℂ (L2 ε)), IsClosed (W : Set (L2 ε)) →
    (∀ g ∈ UJset ε, ∀ x ∈ W, rreg ε g x ∈ W) → FiniteDimensional ℂ S → S ≤ W →
      Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S →
      ∃ A : L2 ε →ₗ[ℂ] L2 ε, (∀ k ∈ Kset ε, ∀ x, A (rreg ε k x) = rreg ε k (A x)) ∧
        (∀ x ∈ S, A x = 0 → x = 0) ∧ S.map A ≤ smD ε (rreg ε) ∧ S.map A ≤ W

def StepWtSpan : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (S : Submodule ℂ (L2 ε)), FiniteDimensional ℂ S → S ≤ smD ε (rreg ε) →
    Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (e : S →ₗ[ℂ] N), e ≠ 0 →
      ∃ (ν : Fin n → ℝ) (x : S), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) ν (x : L2 ε) ∧ e x ≠ 0

def StepCone : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), S7.IsHCParam lam → IsPsiFor ε lam T Ψ →
      KeyFor ε lam T Ψ → ∀ (η : Fin n → ℝ) (S : Submodule ℂ (L2 ε)), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) η S → InCone (lowK ε lam) η

def StepLowEq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), S7.IsHCParam lam → IsPsiFor ε lam T Ψ →
      KeyFor ε lam T Ψ → ∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ

def StepIrred : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      (∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w) →
      (∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ) →
      ∀ W : Submodule ℂ (L2 ε), W ≤ Hlam ε Ψ T.w → IsClosed (W : Set (L2 ε)) →
        (∀ g ∈ UJset ε, ∀ x ∈ W, rreg ε g x ∈ W) → W = ⊥ ∨ W = Hlam ε Ψ T.w

def StepFormulaF : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
      (∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w) →
      (∀ S : Submodule ℂ (L2 ε), S ≤ Hlam ε Ψ T.w →
        Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) S → S = V1 ε Ψ) →
      ∀ g ∈ UJset ε, ∀ v v' : T.V,
        inner ℂ (uniformisationL2 ε Ψ T.w v') (rreg ε g (uniformisationL2 ε Ψ T.w v)) =
          ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v)

def StepVogan : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam η : Fin n → ℝ), S7.IsHCParam lam → InCone (lowK ε lam) η →
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε η

end CompanionTheory.RgDs.Hilb
end
end
