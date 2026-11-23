module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix

namespace GlobalTheory

theorem conjTranspose_mul_mul_eq_of_form_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ z w : Fin n → E, star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w)) :
    γᴴ * J * γ = J := by
  have key : ∀ z w : Fin n → E, star z ⬝ᵥ ((γᴴ * J * γ) *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) := by
    intro z w
    rw [← h z w, star_mulVec, ← dotProduct_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  ext i j
  simpa [single_dotProduct, mulVec_single_one] using key (star (Pi.single i 1)) (Pi.single j 1)

theorem star_form_eq_of_hermitian {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (z w : Fin n → E) :
    star (star z ⬝ᵥ (J *ᵥ w)) = star w ⬝ᵥ (J *ᵥ z) := by
  rw [star_dotProduct z (J *ᵥ w), star_star, star_mulVec, ← dotProduct_mulVec, hJ]

private lemma form_sub_smul_left {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (s : E) :
    star (z - s • u) ⬝ᵥ (J *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) - star s * (star u ⬝ᵥ (J *ᵥ w)) := by
  rw [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma form_sub_smul_right {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (t : E) :
    star z ⬝ᵥ (J *ᵥ (w - t • u)) = star z ⬝ᵥ (J *ᵥ w) - t * (star z ⬝ᵥ (J *ᵥ u)) := by
  rw [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private lemma form_mulVec_eq_of_transvection {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (γ : Matrix (Fin n) (Fin n) E)
    (u : Fin n → E) (c : E)
    (hγ : ∀ v, γ *ᵥ v = v - (c * (star u ⬝ᵥ (J *ᵥ v))) • u)
    (hc : c + star c = star c * c * (star u ⬝ᵥ (J *ᵥ u))) (z w : Fin n → E) :
    star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w) := by
  have hzu := star_form_eq_of_hermitian J hJ u z
  rw [hγ z, hγ w, form_sub_smul_left, form_sub_smul_right J z u w,
    form_sub_smul_right J u u w, star_mul']
  linear_combination (c * (star u ⬝ᵥ (J *ᵥ w))) * hzu +
    (-(star (star u ⬝ᵥ (J *ᵥ z))) * (star u ⬝ᵥ (J *ᵥ w))) * hc

theorem exists_quasiReflection_mulVec_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (x y : Fin n → E)
    (hxy : star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y))
    (h0 : star (x - y) ⬝ᵥ (J *ᵥ x) ≠ 0) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  have hγ : ∀ v, (1 - (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ • vecMulVec (x - y) (star (x - y) ᵥ* J)) *ᵥ v
      = v - ((star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ v))) • (x - y) := by
    intro v
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec]
    congr 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  have hsa : star (star (x - y) ⬝ᵥ (J *ᵥ x)) = star x ⬝ᵥ (J *ᵥ (x - y)) :=
    star_form_eq_of_hermitian J hJ (x - y) x
  have hsum : star (x - y) ⬝ᵥ (J *ᵥ x) + star (star (x - y) ⬝ᵥ (J *ᵥ x))
      = star (x - y) ⬝ᵥ (J *ᵥ (x - y)) := by
    rw [hsa]
    simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
    linear_combination hxy
  have hs0 : star (star (x - y) ⬝ᵥ (J *ᵥ x)) ≠ 0 := (star_ne_zero).mpr h0
  have hc : (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ + star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
      = star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
        * (star (x - y) ⬝ᵥ (J *ᵥ (x - y))) := by
    rw [star_inv₀, ← hsum]
    field_simp
    ring
  refine ⟨_, conjTranspose_mul_mul_eq_of_form_eq J _
    (form_mulVec_eq_of_transvection J hJ _ (x - y) _ hγ hc), ?_⟩
  rw [hγ, inv_mul_cancel₀ h0, one_smul, sub_sub_cancel]

theorem exists_unitary_mulVec_eq_of_form_eq :
    ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E,
      star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 →
      ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  intro E _ _ _ n J hJ _ x y hxy hx
  by_cases h0 : star (x - y) ⬝ᵥ (J *ᵥ x) = 0
  · have hneg : star (-y) ⬝ᵥ (J *ᵥ (-y)) = star y ⬝ᵥ (J *ᵥ y) := by
      rw [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    have hyx : star y ⬝ᵥ (J *ᵥ x) = star x ⬝ᵥ (J *ᵥ x) := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at h0
      exact h0.symm
    have h1 : star (x - -y) ⬝ᵥ (J *ᵥ x) ≠ 0 := by
      rw [sub_neg_eq_add, star_add, add_dotProduct, hyx, ← two_mul]
      exact mul_ne_zero two_ne_zero hx
    obtain ⟨γ, hγ, hγx⟩ := exists_quasiReflection_mulVec_eq J hJ x (-y) (hxy.trans hneg.symm) h1
    refine ⟨-γ, ?_, ?_⟩
    · rw [conjTranspose_neg, neg_mul, mul_neg, neg_mul, neg_neg, hγ]
    · rw [neg_mulVec, hγx, neg_neg]
  · exact exists_quasiReflection_mulVec_eq J hJ x y hxy h0

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem map_transpose_mul_rev {R : Type} [CommRing R] (s : R →+* R) {l m n : Type} [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    ((A * B).map s)ᵀ = (B.map s)ᵀ * (A.map s)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem unitary_stabiliser_orthogonal_summand :
    ∀ (R : Type) [CommRing R] (s : R →+* R) (N ι κ : Type) [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R) (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R), Q * Qi = 1 → Qi * Q = 1 → (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G' → IsUnit G'.det → (∀ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G → ((Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi).map s)ᵀ * J * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) = J) ∧ ∀ h : Matrix N N R, (h.map s)ᵀ * J * h = J → (∀ b : κ, h *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) → ∃ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G ∧ h = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi := by
  intro R _ s N ι κ _ _ _ _ _ _ J G G' Q Qi h1 h2 hD hG'
  have h1s : (Qi.map s)ᵀ * (Q.map s)ᵀ = 1 := by
    rw [← map_transpose_mul_rev, h1, Matrix.map_one _ (map_zero s) (map_one s), transpose_one]
  have hblk : ∀ (y : Matrix ι ι R) (c : Matrix κ ι R),
      ((Matrix.fromBlocks y 0 c (1 : Matrix κ κ R)).map s)ᵀ * Matrix.fromBlocks G 0 0 G' *
        Matrix.fromBlocks y 0 c (1 : Matrix κ κ R) =
      Matrix.fromBlocks ((y.map s)ᵀ * G * y + (c.map s)ᵀ * G' * c) ((c.map s)ᵀ * G') (G' * c) G' := by
    intro y c
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero s) (map_one s),
      Matrix.map_zero _ (map_zero s)]
    simp
  refine ⟨fun y hy => ?_, fun h hh hfix => ?_⟩
  · have hb := hblk y 0
    rw [hy] at hb
    simp only [Matrix.mul_zero, add_zero, Matrix.map_zero _ (map_zero s), transpose_zero,
      Matrix.zero_mul] at hb
    rw [map_transpose_mul_rev, map_transpose_mul_rev]
    calc _ = (Qi.map s)ᵀ * (((Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)).map s)ᵀ *
            ((Q.map s)ᵀ * J * Q) * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = (Qi.map s)ᵀ * ((Q.map s)ᵀ * J * Q) * Qi := by rw [hD, hb]
      _ = ((Qi.map s)ᵀ * (Q.map s)ᵀ) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1s, h1, Matrix.one_mul, Matrix.mul_one]
  · set M : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Qi * h * Q with hM
    have hQM : Q * M = h * Q := by
      rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hhM : h = Q * M * Qi := by
      rw [hQM, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcol : ∀ x b, M x (Sum.inr b) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) x (Sum.inr b) := by
      intro x b
      rw [← h2, hM, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact congrFun (hfix b) i
    have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 1 := by
      ext x z
      rcases z with z | z
      · rcases x with x | x <;> rfl
      · rw [hcol]
        rcases x with x | x <;> simp [Matrix.one_apply]
    have hU : (M.map s)ᵀ * Matrix.fromBlocks G 0 0 G' * M = Matrix.fromBlocks G 0 0 G' := by
      rw [← hD]
      calc _ = ((Q * M).map s)ᵀ * J * (Q * M) := by
            rw [map_transpose_mul_rev s Q M]; simp only [Matrix.mul_assoc]
        _ = (Q.map s)ᵀ * ((h.map s)ᵀ * J * h) * Q := by
            rw [hQM, map_transpose_mul_rev]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hh]
    rw [hMb, hblk, Matrix.fromBlocks_inj] at hU
    obtain ⟨ha, -, hc, -⟩ := hU
    have hc0 : M.toBlocks₂₁ = 0 := by
      have := congrArg (G'⁻¹ * ·) hc
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG'] using this
    rw [hc0] at ha hMb
    refine ⟨M.toBlocks₁₁, by simpa using ha, ?_⟩
    rw [← hMb]
    exact hhM

end GlobalTheory
end

section

namespace GlobalTheory.MeasurableFundamentalDomain

open Set Topology

theorem exists_small_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : Subgroup G)
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ Γ → a * b⁻¹ = 1 := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hfin : ((K ∩ (↑Γ : Set G)) \ {1}).Finite := (hΓ K hK).subset sdiff_subset
  have hcl : IsClosed ((K ∩ (↑Γ : Set G)) \ {1}) := hfin.isClosed
  have h1 : ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) :=
    hcl.isOpen_compl.mem_nhds (by simp)
  have hW : K ∩ ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) := Filter.inter_mem hK1 h1
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv hW
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro a ha b hb hab
  have h := hVW a (interior_subset ha) b (interior_subset hb)
  rw [div_eq_mul_inv] at h
  by_contra hne
  exact h.2 ⟨⟨h.1, hab⟩, hne⟩

theorem exists_measurable_fundamental_domain {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable ↥Γ]
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y : G, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = (1 : G) := by
  classical
  obtain ⟨V, hVo, hV1, hV⟩ := exists_small_open Γ hΓ
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq G
  let U : ℕ → Set G := fun n => {y | y * (g n)⁻¹ ∈ V}
  let S : ℕ → Set G := fun n => ⋃ γ ∈ Γ, {y | γ * y ∈ U n}
  have hUo : ∀ n, IsOpen (U n) := fun n => hVo.preimage (continuous_id.mul continuous_const)
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_biUnion fun γ _ => (hUo n).preimage (continuous_const.mul continuous_id)
  have hS : ∀ n y, y ∈ S n ↔ ∃ γ ∈ Γ, γ * y ∈ U n := by
    intro n y
    simp [S]
  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ y, γ * y ∈ S n → y ∈ S n := by
    intro n γ hγ y hy
    obtain ⟨δ, hδ, h⟩ := (hS _ _).1 hy
    exact (hS _ _).2 ⟨δ * γ, Γ.mul_mem hδ hγ, by rwa [mul_assoc]⟩
  refine ⟨⋃ n, (U n \ ⋃ m ∈ Set.Iio n, S m), ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n =>
      (hUo n).measurableSet.diff (isOpen_biUnion fun m _ => hSo m).measurableSet
  · intro y
    have hex : ∃ n, y ∈ S n := by
      have ho : IsOpen {x : G | y * x⁻¹ ∈ V} :=
        hVo.preimage (continuous_const.mul continuous_inv)
      obtain ⟨n, hn⟩ := hg.exists_mem_open ho ⟨y, by simpa using hV1⟩
      exact ⟨n, (hS _ _).2 ⟨1, Γ.one_mem, by rw [one_mul]; exact hn⟩⟩
    obtain ⟨γ, hγ, h⟩ := (hS _ _).1 (Nat.find_spec hex)
    refine ⟨γ, hγ, mem_iUnion.2 ⟨Nat.find hex, h, ?_⟩⟩
    intro hm
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.1 hm
    exact Nat.find_min hex hm (hSinv m γ hγ y hy)
  · intro γ hγ y hy hγy
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hy
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hγy
    have hnm : n = m := by
      rcases lt_trichotomy n m with h | h | h
      · exact absurd (mem_iUnion₂.2 ⟨n, h, (hS _ _).2
          ⟨γ⁻¹, Γ.inv_mem hγ, by rwa [inv_mul_cancel_left]⟩⟩) hm'
      · exact h
      · exact absurd (mem_iUnion₂.2 ⟨m, h, (hS _ _).2 ⟨γ, hγ, hm⟩⟩) hn'
    subst hnm
    have e : (γ * y * (g n)⁻¹) * (y * (g n)⁻¹)⁻¹ = γ := by group
    have := hV _ hm _ hn (by rw [e]; exact hγ)
    rwa [e] at this

end GlobalTheory.MeasurableFundamentalDomain
end

section

open MeasureTheory Set TopologicalSpace

namespace GlobalTheory

theorem discreteSubgroup_countable_and_exists_strict_fundamentalDomain : ∀ {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ],
    Countable Γ ∧ ∃ D : Set G, MeasurableSet D ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ D := by
  intro G _ _ _ _ _ _ Γ _
  refine ⟨TopologicalSpace.separableSpace_iff_countable.1 inferInstance, ?_⟩

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have hU1 : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU]; rfl
    simpa using this
  have hUΓ : ∀ x : G, x ∈ U → x ∈ Γ → x = 1 := by
    intro x hx hxΓ
    have : (⟨x, hxΓ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hx
    rw [hU] at this
    simpa using congrArg Subtype.val (show (⟨x, hxΓ⟩ : Γ) = 1 from this)
  obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split (hUo.mem_nhds hU1)

  let P : Set G → Prop := fun W => ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ Γ → x = y
  let S : Set (Set G) := {W | W ∈ countableBasis G ∧ P W}
  have hcover : ∀ g : G, ∃ W ∈ S, g ∈ W := by
    intro g
    let N : Set G := (fun x => x * g⁻¹) ⁻¹' (V ∩ (fun x => x⁻¹) ⁻¹' V)
    have hNo : IsOpen N :=
      (hVo.inter (hVo.preimage continuous_inv)).preimage (continuous_mul_const g⁻¹)
    have hgN : g ∈ N := by simp [N, hV1]
    obtain ⟨W, hWb, hgW, hWN⟩ := (isBasis_countableBasis G).exists_subset_of_mem_open hgN hNo
    refine ⟨W, ⟨hWb, ?_⟩, hgW⟩
    intro x hx y hy hxy
    have hx' := hWN hx
    have hy' := hWN hy
    simp only [N, mem_preimage, mem_inter_iff] at hx' hy'
    have h1 : (x * g⁻¹) * (y * g⁻¹)⁻¹ ∈ U := hVU _ hx'.1 _ hy'.2
    have h2 : (x * g⁻¹) * (y * g⁻¹)⁻¹ = x * y⁻¹ := by group
    rw [h2] at h1
    have := hUΓ _ h1 hxy
    exact mul_inv_eq_one.1 this
  have hSc : S.Countable := (countable_countableBasis G).mono fun W hW => hW.1
  have hSne : S.Nonempty := by
    obtain ⟨W, hW, -⟩ := hcover 1
    exact ⟨W, hW⟩
  obtain ⟨f, hf⟩ := hSc.exists_eq_range hSne
  have hfS : ∀ n, f n ∈ S := fun n => hf ▸ mem_range_self n

  let Sat : ℕ → Set G := fun m => {x | ∃ γ : Γ, (γ : G) * x ∈ f m}
  have hSat : ∀ m, IsOpen (Sat m) := by
    intro m
    have : Sat m = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' f m := by
      ext x; simp [Sat]
    rw [this]
    exact isOpen_iUnion fun γ => ((isBasis_countableBasis G).isOpen (hfS m).1).preimage
      (continuous_const_mul _)
  let D : Set G := ⋃ n, (f n ∩ ⋂ m ∈ Finset.range n, (Sat m)ᶜ)
  refine ⟨D, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => ?_
    refine (((isBasis_countableBasis G).isOpen (hfS n).1).measurableSet).inter ?_
    exact Finset.measurableSet_biInter _ fun m _ => (hSat m).measurableSet.compl
  · intro g
    have hex : ∃ n, ∃ γ : Γ, (γ : G) * g ∈ f n := by
      obtain ⟨W, hW, hgW⟩ := hcover g
      rw [hf] at hW
      obtain ⟨n, rfl⟩ := hW
      exact ⟨n, 1, by simpa using hgW⟩
    classical
    obtain ⟨γ, hγ⟩ := Nat.find_spec hex
    have hmem : ∀ (δ : Γ) n, (δ : G) * g ∈ f n → (∀ m < n, (δ : G) * g ∉ Sat m) → (δ : G) * g ∈ D := by
      intro δ n h1 h2
      refine mem_iUnion.2 ⟨n, h1, ?_⟩
      simp only [mem_iInter, Finset.mem_range, mem_compl_iff]
      exact h2
    refine ⟨γ, hmem γ _ hγ fun m hm hS => ?_, ?_⟩
    · obtain ⟨δ, hδ⟩ := hS
      refine Nat.find_min hex hm ⟨δ * γ, ?_⟩
      simpa [mul_assoc] using hδ
    · intro δ hδ
      have hD : ∀ (ε : Γ), (ε : G) * g ∈ D → ∃ n, (ε : G) * g ∈ f n ∧ ∀ m < n, (ε : G) * g ∉ Sat m := by
        intro ε hε
        obtain ⟨n, h1, h2⟩ := mem_iUnion.1 hε
        refine ⟨n, h1, fun m hm => ?_⟩
        simp only [mem_iInter, Finset.mem_range, mem_compl_iff] at h2
        exact h2 m hm
      obtain ⟨n1, h11, h12⟩ := hD δ hδ
      obtain ⟨n2, h21, h22⟩ := hD γ (hmem γ _ hγ fun m hm hS => by
        obtain ⟨δ', hδ'⟩ := hS
        exact Nat.find_min hex hm ⟨δ' * γ, by simpa [mul_assoc] using hδ'⟩)
      have hn : n1 = n2 := by
        rcases lt_trichotomy n1 n2 with h | h | h
        · exact absurd ⟨δ * γ⁻¹, by simpa [mul_assoc] using h11⟩ (h22 n1 h)
        · exact h
        · exact absurd ⟨γ * δ⁻¹, by simpa [mul_assoc] using h21⟩ (h12 n2 h)
      subst hn
      have hP := (hfS n1).2 _ h11 _ h21 (by
        have : ((δ : G) * g) * ((γ : G) * g)⁻¹ = ((δ * γ⁻¹ : Γ) : G) := by simp [mul_assoc]
        rw [this]; exact (δ * γ⁻¹).2)
      exact Subtype.ext (mul_right_cancel hP)

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem integrable_exp_neg_mul_of_sublevel_growth :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d →
      (∀ x, 0 ≤ d x) →
      (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b →
      Integrable (fun x => Real.exp (-(b * d x))) μ := by
  intro X _ μ d a b C hd hd0 hgrowth hab
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hmeas : Measurable fun x => Real.exp (-(b * d x)) :=
    Real.measurable_exp.comp ((hd.const_mul b).neg)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpos : 0 ≤ᵐ[μ] fun x => Real.exp (-(b * d x)) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [hasFiniteIntegral_iff_ofReal hpos]

  let s : ℕ → Set X := fun n => {x | d x ≤ (n : ℝ) + 1}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le hd measurable_const
  let g : ℕ → X → ENNReal := fun n =>
    (s n).indicator (fun _ => ENNReal.ofReal (Real.exp (|b| - b * n)))
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ∑' n, g n x := by
    intro x
    set n := ⌊d x⌋₊ with hn
    have h1 : (n : ℝ) ≤ d x := Nat.floor_le (hd0 x)
    have h2 : d x < (n : ℝ) + 1 := Nat.lt_floor_add_one (d x)
    have hxs : x ∈ s n := by
      show d x ≤ (n : ℝ) + 1
      exact h2.le
    have hexp : Real.exp (-(b * d x)) ≤ Real.exp (|b| - b * n) := by
      apply Real.exp_le_exp.mpr
      have hdist : |d x - n| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have : |b * (d x - n)| ≤ |b| := by
        rw [abs_mul]
        calc |b| * |d x - n| ≤ |b| * 1 := mul_le_mul_of_nonneg_left hdist (abs_nonneg b)
          _ = |b| := mul_one _
      have hlow := neg_abs_le (b * (d x - n))
      have hy : -(b * d x) = |b| - b * n - (|b| + b * (d x - n)) := by ring
      rw [hy]
      linarith
    calc ENNReal.ofReal (Real.exp (-(b * d x))) ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) :=
          ENNReal.ofReal_le_ofReal hexp
      _ = g n x := by simp only [g, Set.indicator_of_mem hxs]
      _ ≤ ∑' m, g m x := ENNReal.le_tsum (f := fun m => g m x) n

  let u : ℕ → ℝ := fun n => C' * Real.exp (|b| + a) * Real.exp (a - b) ^ n
  have hu0 : ∀ n, 0 ≤ u n := fun n => by positivity
  have hr0 : 0 ≤ Real.exp (a - b) := (Real.exp_pos _).le
  have hr1 : Real.exp (a - b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable u := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hterm : ∀ n, ∫⁻ x, g n x ∂μ ≤ ENNReal.ofReal (u n) := by
    intro n
    simp only [g]
    rw [lintegral_indicator_const (hs n)]
    have hμ : μ (s n) ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by
      calc μ (s n) ≤ ENNReal.ofReal (C * Real.exp (a * ((n : ℝ) + 1))) :=
            hgrowth _ (by positivity)
        _ ≤ ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ENNReal.ofReal (Real.exp (|b| - b * n)) * μ (s n)
        ≤ ENNReal.ofReal (Real.exp (|b| - b * n)) *
            ENNReal.ofReal (C' * Real.exp (a * ((n : ℝ) + 1))) := by gcongr
      _ = ENNReal.ofReal (Real.exp (|b| - b * n) * (C' * Real.exp (a * ((n : ℝ) + 1)))) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (u n) := by
          congr 1
          simp only [u]
          rw [← Real.exp_nat_mul]
          have hE : Real.exp (|b| - b * n) * Real.exp (a * ((n : ℝ) + 1)) =
              Real.exp (|b| + a) * Real.exp (n * (a - b)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          linear_combination C' * hE
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-(b * d x))) ∂μ ≤ ∫⁻ x, ∑' n, g n x ∂μ :=
        MeasureTheory.lintegral_mono hpt
    _ = ∑' n, ∫⁻ x, g n x ∂μ :=
        MeasureTheory.lintegral_tsum fun n => (measurable_const.indicator (hs n)).aemeasurable
    _ ≤ ∑' n, ENNReal.ofReal (u n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n, u n) := (ENNReal.ofReal_tsum_of_nonneg hu0 hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
end
