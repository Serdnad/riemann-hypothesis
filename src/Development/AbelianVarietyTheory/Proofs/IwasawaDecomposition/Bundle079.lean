module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle071
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.CantorSet
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001

@[expose] public section

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.exists_ne_zero_intertwiner_of_map : ∀ {k L Γ : Type} [Field k] [Field L] (f : k →+* L) {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k) (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L), C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 → ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  first | exact @GlobalTheory.matrix_system_nonzero_solution_descends | exact GlobalTheory.matrix_system_nonzero_solution_descends | (intros; apply GlobalTheory.matrix_system_nonzero_solution_descends <;> assumption)
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense : ∀ {X A : Type} [TopologicalSpace X] [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Infinite A] {n : ℕ} (M N : X → Matrix (Fin n) (Fin n) A), Continuous M → Continuous N → ∀ U : Set X, Dense U → (∀ x ∈ U, (M x).charpoly = (N x).charpoly) → ∀ x, (M x).charpoly = (N x).charpoly := by
  first | exact @GlobalTheory.charpoly_eq_of_eqOn_dense | exact GlobalTheory.charpoly_eq_of_eqOn_dense | (intros; apply GlobalTheory.charpoly_eq_of_eqOn_dense <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.OrbitSection

theorem exists_section_real {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (C : Set ℝ) [CompactSpace C] (c₀ : C) (f : C → X) (hf : Continuous f) :
    ∃ τ : X → C, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  have h : ∀ y : X, ∃ c : C, (y ∈ Set.range f → f c = y ∧ ∀ c', f c' = y → (c : ℝ) ≤ c') ∧
      (y ∉ Set.range f → c = c₀) := by
    intro y
    by_cases hy : y ∈ Set.range f
    · have hc : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf).isCompact
      obtain ⟨c, hc1, hc2⟩ := hc.exists_isMinOn (f := fun c : C => (c : ℝ)) hy
        continuous_subtype_val.continuousOn
      exact ⟨c, fun _ => ⟨hc1, fun c' h' => hc2 h'⟩, fun h => absurd hy h⟩
    · exact ⟨c₀, fun h => absurd h hy, fun _ => rfl⟩
  choose τ h1 h2 using h
  refine ⟨τ, ?_, fun y hy => (h1 y hy).1⟩
  have hm : Measurable fun y => (τ y : ℝ) := by
    refine measurable_of_Iic fun a => ?_
    have he : (fun y => (τ y : ℝ)) ⁻¹' Set.Iic a =
        f '' {c : C | (c : ℝ) ≤ a} ∪ ((Set.range f)ᶜ ∩ {_y | (c₀ : ℝ) ≤ a}) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_setOf_eq]
      by_cases hy : y ∈ Set.range f
      · constructor
        · intro h
          exact Or.inl ⟨τ y, h, (h1 y hy).1⟩
        · rintro (⟨c, hc, hcy⟩ | h)
          · exact ((h1 y hy).2 c hcy).trans hc
          · exact absurd hy h.1
      · rw [h2 y hy]
        constructor
        · intro h
          exact Or.inr ⟨hy, h⟩
        · rintro (⟨c, -, hcy⟩ | h)
          · exact absurd ⟨c, hcy⟩ hy
          · exact h.2
    rw [he]
    refine MeasurableSet.union ?_ (MeasurableSet.inter ?_ (MeasurableSet.const _))
    · exact ((isClosed_le continuous_subtype_val continuous_const).isCompact.image
        hf).isClosed.measurableSet
    · exact (isCompact_range hf).isClosed.measurableSet.compl
  exact hm.subtype_mk (h := fun y => (τ y).2)

theorem exists_section_compact {K X : Type} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (f : K → X) (hf : Continuous f) :
    ∃ τ : X → K, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  letI := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨p, hp, hps⟩ := exists_nat_bool_continuous_surjective_of_compact K
  have : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  let q : cantorSet → K := p ∘ cantorSetHomeomorphNatToBool
  have hq : Continuous q := hp.comp cantorSetHomeomorphNatToBool.continuous
  have hqs : Function.Surjective q := hps.comp cantorSetHomeomorphNatToBool.surjective
  obtain ⟨τ, h1, h2⟩ := exists_section_real cantorSet ⟨0, zero_mem_cantorSet⟩ (f ∘ q)
    (hf.comp hq)
  refine ⟨q ∘ τ, hq.measurable.comp h1, fun y hy => h2 y ?_⟩
  rwa [hqs.range_comp]

theorem measurableSet_orbit_and_exists_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀
  classical
  have hπ : Continuous fun g : G => g • x₀ := by fun_prop
  let K : ℕ → Set G := fun n => insert 1 (compactCovering G n)
  have hK : ∀ n, IsCompact (K n) := fun n => (isCompact_compactCovering G n).insert 1
  have hKU : ∀ g : G, ∃ n, g ∈ K n := fun g => by
    obtain ⟨n, hn⟩ := exists_mem_compactCovering g
    exact ⟨n, Or.inr hn⟩
  let A : ℕ → Set X := fun n => (fun g : G => g • x₀) '' K n
  have hA : ∀ n, MeasurableSet (A n) := fun n => ((hK n).image hπ).isClosed.measurableSet
  have hO : MeasurableSet {y : X | ∃ g : G, g • x₀ = y} := by
    have : {y : X | ∃ g : G, g • x₀ = y} = ⋃ n, A n := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn⟩ := hKU g
        exact ⟨n, g, hn, hg⟩
      · rintro ⟨n, g, -, hg⟩
        exact ⟨g, hg⟩
    rw [this]
    exact MeasurableSet.iUnion hA
  have hs : ∀ n, ∃ s : X → G, Measurable s ∧ ∀ y ∈ A n, s y • x₀ = y := by
    intro n
    have : CompactSpace (K n) := isCompact_iff_compactSpace.1 (hK n)
    have : Nonempty (K n) := ⟨⟨1, Or.inl rfl⟩⟩
    obtain ⟨τ, h1, h2⟩ := exists_section_compact (fun g : K n => (g : G) • x₀)
      (hπ.comp continuous_subtype_val)
    refine ⟨fun y => τ y, measurable_subtype_coe.comp h1, ?_⟩
    rintro y ⟨g, hg, hgy⟩
    exact h2 y ⟨⟨g, hg⟩, hgy⟩
  choose s hs1 hs2 using hs
  have hex : ∀ y : X, ∃ n, (y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) := by
    intro y
    by_cases hy : ∃ g : G, g • x₀ = y
    · obtain ⟨g, hg⟩ := hy
      obtain ⟨n, hn⟩ := hKU g
      exact ⟨n, Or.inl ⟨g, hn, hg⟩⟩
    · exact ⟨0, Or.inr hy⟩
  refine ⟨hO, fun y => s (Nat.find (hex y)) y, ?_, fun y hy => ?_⟩
  · exact Measurable.find (p := fun n y => y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) hs1 (fun n => (hA n).union hO.compl) hex
  · exact hs2 _ y ((Nat.find_spec (hex y)).resolve_right (not_not.2 hy))

end GlobalTheory.OrbitSection
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.QuadricCount

lemma sum_dot {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (w : ι → k) :
    ∑ x : ι → k, ψ (x ⬝ᵥ w) = if w = 0 then ((Fintype.card k : ℂ) ^ Fintype.card ι) else 0 := by
  split_ifs with hw
  · subst hw; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hi' : w i ≠ 0 := hi
    have h1 : ∃ a : k, ψ (a * w i) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have := AddChar.sum_mulShift (w i) hψ
      simp [hcon, hi'] at this
    obtain ⟨a, ha⟩ := h1
    have h2 : ∑ x : ι → k, ψ (x ⬝ᵥ w) = ψ (a * w i) * ∑ x : ι → k, ψ (x ⬝ᵥ w) := by
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp (Equiv.addLeft (Pi.single i a : ι → k))]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [add_dotProduct, AddChar.map_add_eq_mul]
    have h3 : (1 - ψ (a * w i)) * ∑ x : ι → k, ψ (x ⬝ᵥ w) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h).symm ha
    · exact h

lemma gauss_normSq {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (S : Matrix ι ι k) (h2 : (2 : k) ≠ 0) (hS : S.IsSymm)
    (hd : S.det ≠ 0) (t : k) (ht : t ≠ 0) :
    ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))‖ ^ 2 = (Fintype.card k : ℝ) ^ Fintype.card ι := by
  have hsym : ∀ x z : ι → k, z ⬝ᵥ S.mulVec x = x ⬝ᵥ S.mulVec z := by
    intro x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq, dotProduct_comm]
  have key : (starRingEnd ℂ) (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)))
      = (Fintype.card k : ℂ) ^ Fintype.card ι := by

    rw [map_sum, Finset.sum_mul]
    have e1 : ∀ x : ι → k, (starRingEnd ℂ) (ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ y : ι → k, ψ (t * (y ⬝ᵥ S.mulVec y)))
        = ∑ z : ι → k, ψ (t * (z ⬝ᵥ S.mulVec z)) * ψ (x ⬝ᵥ ((2 * t) • S.mulVec z)) := by
      intro x
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft x)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [Equiv.coe_addLeft, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hsym x z]
      ring
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_dot ψ hψ]
    rw [Finset.sum_eq_single (0 : ι → k)]
    · simp
    · intro z _ hz
      rw [if_neg, mul_zero]
      intro h
      rcases smul_eq_zero.mp h with h | h
      · exact mul_ne_zero h2 ht h
      · exact hz (Matrix.eq_zero_of_mulVec_eq_zero hd h)
    · simp
  rw [Complex.conj_mul'] at key
  exact_mod_cast key

theorem card_quadric_sub_sq_le : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (S : Matrix ι ι k) (β : k), (2 : k) ≠ 0 → S.IsSymm → S.det ≠ 0 → (((Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card : ℝ) - (Fintype.card k : ℝ) ^ (Fintype.card ι - 1)) ^ 2 ≤ (Fintype.card k : ℝ) ^ Fintype.card ι := by
  intro k _ _ _ ι _ _ _ S β h2 hS hd
  set ψ := AddChar.FiniteField.primitiveChar_to_Complex k
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k
  set N := (Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card with hN
  set q := Fintype.card k with hq
  set m := Fintype.card ι with hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hm0 : m = (m - 1) + 1 := by have : 0 < m := Fintype.card_pos; omega
  have e1 : ∑ x : ι → k, ∑ t : k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) * N := by
    simp_rw [AddChar.sum_mulShift _ hψ, sub_eq_zero]
    push_cast
    rw [← Finset.sum_filter]
    simp [hN, hq, mul_comm]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))] at e1
  have e2 : ∑ x : ι → k, ψ (0 * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) ^ m := by
    simp [hq, hm]
  rw [e2] at e1
  set r : ℝ := Real.sqrt ((q : ℝ) ^ m) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (q : ℝ) ^ m := Real.sq_sqrt (by positivity)
  have e3 : ∀ t ∈ Finset.univ.erase (0 : k), ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β))‖ ≤ r := by
    intro t ht
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have : ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = ψ (-(t * β)) * ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this, norm_mul, AddChar.norm_apply, one_mul, hr, ← gauss_normSq ψ hψ S h2 hS hd t ht0, Real.sqrt_sq (norm_nonneg _)]
  have e4 : ‖(q : ℂ) * N - (q : ℂ) ^ m‖ ≤ q * r := by
    rw [← e1, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ e3).trans ?_)
    rw [nsmul_eq_mul]
    gcongr
    exact Finset.card_le_univ _
  have e5 : (q : ℂ) * N - (q : ℂ) ^ m = (((q : ℝ) * ((N : ℝ) - (q : ℝ) ^ (m - 1)) : ℝ) : ℂ) := by
    conv_lhs => rw [hm0]
    push_cast
    ring
  rw [e5, Complex.norm_real, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0] at e4
  have e6 := le_of_mul_le_mul_left e4 hq0
  rw [← hr2, ← sq_abs]
  gcongr

end GlobalTheory.QuadricCount
end

section

open IsLocalRing

namespace GlobalTheory.CompletionReduced

theorem map_le_jacobson_of_comap_isMaximal {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : ∀ M : Ideal B, M.IsMaximal → (M.comap f).IsMaximal) (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A)) : I.map f ≤ Ideal.jacobson (⊥ : Ideal B) := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro M ⟨-, hM⟩
  rw [Ideal.map_le_iff_le_comap]
  exact hI.trans (sInf_le ⟨bot_le, hf M hM⟩)

theorem exists_lt_of_add_one_le (e : WithBot ℕ∞) (n : ℕ) (h0 : 0 ≤ e) (h : e + 1 ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, m < n ∧ e ≤ (m : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h
      rw [WithBot.coe_le_coe, top_add] at h'
      exact absurd h' (by simp)
    | coe k =>
      refine ⟨k, ?_, le_rfl⟩
      have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      exact_mod_cast this

theorem isReduced_of_normal (n : ℕ)
    (ih : ∀ m < n, ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      ringKrullDim D ≤ (m : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
        IsReduced (AdicCompletion J D))
    (N : Type) [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra.EssFiniteType ℤ N]
    (hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞)) (I : Ideal N)
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal N)) : IsReduced (AdicCompletion I N) := by
  haveI : IsNoetherianRing N := Algebra.EssFiniteType.isNoetherianRing ℤ N
  by_cases hbot : I = ⊥
  · subst hbot
    exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.toRingEquiv.toRingHom
      (AdicCompletion.ofAlgEquiv (⊥ : Ideal N)).symm.injective
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let R := AdicCompletion I N
  haveI : IsNoetherianRing R := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian N I
  haveI : Module.Flat N R := AdicCompletion.flat_of_isNoetherian I
  have hxR : algebraMap N R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular N x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap N R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hxjac : algebraMap N R x ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have h1 : IsAdicComplete I R := AdicCompletion.isAdicComplete (IsNoetherian.noetherian I)
    have h2 : IsAdicComplete (I.map (algebraMap N R)) R := (IsAdicComplete.map_algebraMap_iff _ _).2 h1
    exact IsAdicComplete.le_jacobson_bot (I.map (algebraMap N R)) (Ideal.mem_map_of_mem _ hxI)
  have hredq : ∀ q : Ideal N, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap N R)) := by
    intro q hq hxq
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv N I q
    haveI : IsDomain (N ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType N (N ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (N ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (N ⧸ q)
      haveI : IsScalarTower ℤ N (N ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ N (N ⧸ q)
    have hj : I.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (N ⧸ q)) :=
      map_le_jacobson_of_comap_isMaximal _
        (fun M hM => Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) I hIjac
    have hd1 : ringKrullDim (N ⧸ q) + 1 ≤ (n : WithBot ℕ∞) := by
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
      have h2 : ringKrullDim (N ⧸ q) ≤ ringKrullDim (N ⧸ Ideal.span {x}) :=
        ringKrullDim_le_of_surjective _
          (Ideal.Quotient.factor_surjective (by rwa [Ideal.span_singleton_le_iff_mem]))
      exact ((add_le_add h2 le_rfl).trans h1).trans hdimN
    obtain ⟨m, hmn, hm⟩ := exists_lt_of_add_one_le _ n ringKrullDim_nonneg_of_nontrivial hd1
    haveI := ih m hmn (N ⧸ q) hm _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  refine GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes R (algebraMap N R x) hxR hxjac ?_
  intro P _ hP
  obtain ⟨h1, -⟩ := GlobalTheory.T.associated_prime_localization_dvr N R x hx0 hredq P hP
  exact h1

theorem isReduced_of_dim_le : ∀ (n : ℕ) (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    ringKrullDim D ≤ (n : WithBot ℕ∞) → ∀ (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) →
      IsReduced (AdicCompletion J D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ _ _ hdim J hJ
  haveI : IsNoetherianRing D := Algebra.EssFiniteType.isNoetherianRing ℤ D

  let N := integralClosure D (FractionRing D)
  haveI : Module.Finite D N := GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain D
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing D)
  have hinj : Function.Injective (algebraMap D N) := by
    intro a b hab
    have := congrArg (fun y : N => (y : FractionRing D)) hab
    exact IsFractionRing.injective D (FractionRing D) this
  have hdimN : ringKrullDim N ≤ (n : WithBot ℕ∞) := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]; exact hdim
  haveI : Algebra.EssFiniteType D N := inferInstance
  haveI hessN : @Algebra.EssFiniteType ℤ N _ _ (Ring.toIntAlgebra _) := by
    letI := Ring.toIntAlgebra N
    haveI : IsScalarTower ℤ D N := .of_algebraMap_eq fun z => by simp
    exact Algebra.EssFiniteType.comp ℤ D N
  have hIjac : J.map (algebraMap D N) ≤ Ideal.jacobson (⊥ : Ideal N) :=
    map_le_jacobson_of_comap_isMaximal _
      (fun M hM => Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) M) J hJ
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_injective_adicCompletion_map_of_finite D N hinj J
  haveI := isReduced_of_normal n ih N hdimN _ hIjac
  exact isReduced_of_injective f hf

theorem isReduced_adicCompletion : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D]
    (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  intro D _ _ _ J hJ
  have hlt := GlobalTheory.T.ringKrullDim_finite_of_essFiniteType_int D
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim D ≤ (m : WithBot ℕ∞) := by
    generalize ringKrullDim D = e at hlt ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe k => exact ⟨k, le_rfl⟩
  exact isReduced_of_dim_le m D hm J hJ

end GlobalTheory.CompletionReduced
end
