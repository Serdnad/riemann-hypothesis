module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_linear_in_polynomial : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) := by
  intro O _ _ _ K _ _ ι _ σ Z cls Q
  classical
  set g : (σ →₀ ℕ) → ℝ := fun μ => (cycList Z (classList cls μ ++ Q) : ℝ) with hg
  have key : ∀ (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      cycNum Z cls H Q = ∑ μ ∈ s, AddMonoidAlgebra.coeff H μ * g μ := by
    intro H s hs
    show ∑ μ ∈ H.support, AddMonoidAlgebra.coeff H μ * g μ = _
    refine Finset.sum_subset hs (fun μ _ hμ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]
  have hadd : ∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q := by
    intro H H'
    rw [key (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
      key H (H.support ∪ H'.support) Finset.subset_union_left,
      key H' (H.support ∪ H'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : cycNum Z cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 ∅ (by simp)]
    simp
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c H
    have hs : (MvPolynomial.C c * H).support ⊆ H.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      rw [MvPolynomial.coeff_C_mul] at hμ
      exact right_ne_zero_of_mul hμ
    rw [key _ H.support hs, key H H.support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_C_mul, mul_assoc]
  · intro α s H
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  · intro μ c
    rw [key _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_linear_in_polynomial : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), genNum F V cls (C c * H) Q = c * genNum F V cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), genNum F V cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, genNum F V cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial μ c) Q = c * (intNumL F V (classList cls μ ++ Q) : ℝ) := by
  intro F _ K _ _ ι _ σ V cls Q
  classical
  set g : (σ →₀ ℕ) → ℝ := fun μ => (intNumL F V (classList cls μ ++ Q) : ℝ) with hg
  have key : ∀ (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      genNum F V cls H Q = ∑ μ ∈ s, AddMonoidAlgebra.coeff H μ * g μ := by
    intro H s hs
    show ∑ μ ∈ H.support, AddMonoidAlgebra.coeff H μ * g μ = _
    refine Finset.sum_subset hs (fun μ _ hμ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]
  have hadd : ∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q := by
    intro H H'
    rw [key (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
      key H (H.support ∪ H'.support) Finset.subset_union_left,
      key H' (H.support ∪ H'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : genNum F V cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 ∅ (by simp)]
    simp
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c H
    have hs : (MvPolynomial.C c * H).support ⊆ H.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      rw [MvPolynomial.coeff_C_mul] at hμ
      exact right_ne_zero_of_mul hμ
    rw [key _ H.support hs, key H H.support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_C_mul, mul_assoc]
  · intro α s H
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  · intro μ c
    rw [key _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

private theorem intNum_get_eq_of_perm {K : Type} [DecidableEq K] {ι : K → Type} (F : Type) [Field F]
    (P : Ideal (MRing ι F)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    intNum F P l.get = intNum F P l'.get := by
  unfold intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get]
  haveI : LeftCommutative (diffStep (K := K)) := ⟨fun a b f => by
    funext m
    simp only [diffStep]
    rw [show m - a - b = m - b - a by abel]
    ring⟩
  rw [h.foldr_eq]

theorem BaseChangeColon.intNumL_perm (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)) (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  unfold intNumL
  exact intNum_get_eq_of_perm F V h

theorem BaseChangeColon.intersection_numbers_perm_invariant : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  refine ⟨fun F _ K _ _ ι _ V l l' h => BaseChangeColon.intNumL_perm F K ι V l l' h, ?_⟩
  intro O _ _ _ K _ _ ι _ Z l l' h
  unfold cycList
  congr 1
  funext W
  unfold vNumL vNum
  exact intNum_get_eq_of_perm _ _ h
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_rename_variables : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) := by
  refine ⟨?_, ?_⟩
  · intro O _ _ _ K _ _ ι _ σ σ' e Z cls H Q
    unfold cycNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
  · intro F _ K _ _ ι _ σ σ' e V cls H Q
    unfold genNum classList
    rw [BaseChangeColon.evL_eq, BaseChangeColon.evL_eq, BaseChangeColon.evL_rename]
    simp only [BaseChangeColon.classes_mapDomain]
end
