module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Polynomial.Coeff
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.CharpolyFrobDense

def CoeffCont {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] (F : Γ → K[X]) : Prop :=
  ∀ k, Continuous fun g => (F g).coeff k

theorem CoeffCont.mul {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {F F' : Γ → K[X]} (h : CoeffCont F) (h' : CoeffCont F') :
    CoeffCont (F * F') := by
  intro k
  simp only [Pi.mul_apply, coeff_mul]
  exact continuous_finsetSum _ fun x _ => (h x.1).mul (h' x.2)

theorem coeffCont_one {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] :
    CoeffCont (1 : Γ → K[X]) := fun _ => continuous_const

theorem coeffCont_X_sub_C {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {a : Γ → K} (ha : Continuous a) :
    CoeffCont fun g => (X - C (a g)) := by
  intro k
  rcases k with _ | _ | k
  · simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    exact ha.neg
  · simpa using continuous_const
  · simp only [coeff_sub, coeff_X, coeff_C]
    simpa using continuous_const

theorem coeffCont_prod {Γ K ι : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (s : Finset ι) (F : ι → Γ → K[X]) (h : ∀ c ∈ s, CoeffCont (F c)) :
    CoeffCont fun g => ∏ c ∈ s, F c g := by
  have : (fun g => ∏ c ∈ s, F c g) = ∏ c ∈ s, F c := by
    funext g; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (fun G => CoeffCont G) (fun _ _ ha hb => ha.mul hb) coeffCont_one h

end GlobalTheory.CharpolyFrobDense
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem GlobalTheory.padicAlgCl_finite_dense_eq_adjoin : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  intro l _ E _ _ c K hc hfin hdense
  have hle : IntermediateField.adjoin ℚ_[l] (Set.range c) ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩; exact hc x
  have hKfin : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hfin
  have hAfin : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule :=
    Submodule.finiteDimensional_of_le (S₂ := K.toSubalgebra.toSubmodule) hle
  have hclosed : IsClosed ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule
      : Set (PadicAlgCl l)) :=
    Submodule.closed_of_finiteDimensional _
  apply le_antisymm _ hle
  intro y hy
  have h1 : closure (Set.range c) ⊆
      ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
    apply closure_minimal _ hclosed
    rintro _ ⟨x, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  exact h1 (hdense hy)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.finrank_local_field_eq_card_decomposition_group : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) [IsGalois ℚ E] (v : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) → Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range c)) = Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) :=
  @_root_.UpperTheory.HF.LocStab.finrank_adjoin_range_eq_card_stabilizer
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  first | exact @GlobalTheory.padicAlgCl_finite_dense_eq_adjoin | exact GlobalTheory.padicAlgCl_finite_dense_eq_adjoin | (intros; apply GlobalTheory.padicAlgCl_finite_dense_eq_adjoin <;> assumption)

end
end
