module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Basic.Complex.Basic
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousNonvanishing

open GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem exists_component_ne (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Σ k, ι k) ℤ)
    (hq : eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0) :
    ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (weightedHomogeneousComponent (blockWeight ι) a q)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hq
  have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight ι) q
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) q]
  have key := map_finsum ((eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))) hfin
  simp only [RingHom.coe_comp, Function.comp_apply] at key
  rw [key]
  simp [h]

theorem exists_form_ne (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (d : K → ℕ) :
    ∃ m : MvPolynomial (Σ k, ι k) ℤ, IsWeightedHomogeneous (blockWeight ι) m d ∧
      eval z (MvPolynomial.map (Int.castRingHom ℂ) m) ≠ 0 := by
  choose i hi using hz
  refine ⟨∏ k, X ⟨k, i k⟩ ^ d k, ?_, ?_⟩
  · have h := IsWeightedHomogeneous.prod Finset.univ
      (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, i k⟩).pow (d k))
    convert h using 1
    conv_lhs => rw [← Finset.univ_sum_single d]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ext j
    simp [blockWeight, Pi.single_apply]
  · simp [Finset.prod_ne_zero_iff, hi]

end PositivityTheory.Xgn.MultihomogeneousNonvanishing

theorem PositivityTheory.Xgn.multihomogeneous_nonvanishing_off : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
  intro K _ _ ι _ P bf bg z q hP hz hqP hq
  obtain ⟨a, ha⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_component_ne z q hq
  obtain ⟨m1, hm1, hm1z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bg
  obtain ⟨m2, hm2, hm2z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bf
  have hcP : weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q ∈ P :=
    hP q hqP a
  have hch := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q
  refine ⟨a + bg, a + bf, _ * m1, _ * m2, hch.mul hm1, hch.mul hm2, by abel,
    P.mul_mem_right _ hcP, P.mul_mem_right _ hcP, ?_, ?_⟩
  · simpa using mul_ne_zero ha hm1z
  · simpa using mul_ne_zero ha hm2z
end

section

open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousTwistFinite
open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homog_prod {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k) d := by
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
    (fun k => d k • blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, c k⟩).pow (d k))
  have e : ∑ k, d k • blockWeight ι ⟨k, c k⟩ = d := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem eval_mul_ne {K : Type} [Fintype K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (u : MvPolynomial (Σ k, ι k) ℤ)
    (hu : eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) :
    eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)) ≠ 0 := by
  rw [map_mul, map_mul]
  refine mul_ne_zero hu ?_
  simp only [map_prod, map_pow, MvPolynomial.map_X, MvPolynomial.eval_X]
  exact Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (hc k))

end PositivityTheory.Xgn.MultihomogeneousTwistFinite

theorem PositivityTheory.Xgn.multihomogeneous_twist_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) := by
  intro K _ _ ι _ Q bf bg hQmul hQ hU hV
  obtain ⟨TU, hTU, hselU⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {u | ∃ a b v, Q a b u v}
  obtain ⟨TV, hTV, hselV⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {v | ∃ a b u, Q a b u v}
  have wU : ∀ t : TU, ∃ a b v, Q a b t.1 v := fun t => hTU t.2
  have wV : ∀ t : TV, ∃ a b u, Q a b u t.1 := fun t => hTV t.2
  choose aU bU vU hqU using wU
  choose aV bV uV hqV using wV
  obtain ⟨A, hA⟩ : ∃ A : K → ℕ, A = bg + (∑ t, aU t + ∑ t, aV t) := ⟨_, rfl⟩
  have leU : ∀ t k, aU t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aU t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have leV : ∀ t k, aV t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aV t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have hbgA : ∀ k, bg k ≤ A k := by
    intro k
    rw [hA]
    simp only [Pi.add_apply]
    omega
  obtain ⟨B, hB⟩ : ∃ B : K → ℕ, B = A + bf - bg := ⟨_, rfl⟩
  have hAB : A + bf = B + bg := by
    funext k
    rw [hB]
    simp only [Pi.add_apply, Pi.sub_apply]
    have := hbgA k
    omega
  have lift : ∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ) (c : ∀ k, ι k), Q a b u v →
      (∀ k, a k ≤ A k) →
      Q A B (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k)
        (v * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k) := by
    intro a b u v c hq hle
    have h := hQmul a b (A - a) u v _ hq (MultihomogeneousTwistFinite.homog_prod c (A - a))
    obtain ⟨_, _, hab⟩ := hQ a b u v hq
    have e1 : a + (A - a) = A := by
      funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      have := hle k
      omega
    have e2 : b + (A - a) = B := by
      funext k
      have h1 := congrFun hab k
      have h2 := congrFun hAB k
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
      have := hle k
      omega
    rw [e1, e2] at h
    exact h
  let e := Fintype.equivFin ((TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)))
  let uu : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => uV p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  let vv : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => vU p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  refine ⟨A, B, _, fun j => uu (e.symm j), fun j => vv (e.symm j), hAB, ?_, ?_, ?_⟩
  · intro j
    show Q A B (uu (e.symm j)) (vv (e.symm j))
    generalize e.symm j = w
    rcases w with ⟨t, c⟩ | ⟨t, c⟩
    · exact lift _ _ _ _ c (hqU t) (leU t)
    · exact lift _ _ _ _ c (hqV t) (leV t)
  · intro z hz
    obtain ⟨a, b, u, v, hq, hu⟩ := hU z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselU z ⟨u, ⟨a, b, v, hq⟩, hu⟩
    refine ⟨e (Sum.inl (⟨t, ht⟩, c)), ?_⟩
    simp only [uu, Equiv.symm_apply_apply, Sum.elim_inl]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
  · intro z hz
    obtain ⟨a, b, u, v, hq, hv⟩ := hV z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselV z ⟨v, ⟨a, b, u, hq⟩, hv⟩
    refine ⟨e (Sum.inr (⟨t, ht⟩, c)), ?_⟩
    simp only [vv, Equiv.symm_apply_apply, Sum.elim_inr]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem PositivityTheory.Xgn.finite_surjective_image_open : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V := by
  intro Z Z' _ _ π hπ _ V hV
  haveI : IsFinite π := hπ
  have hCc : IsClosed ((V : Set Z')ᶜ) := V.isOpen.isClosed_compl
  refine ⟨⟨(π '' (V : Set Z')ᶜ)ᶜ, (π.isClosedMap _ hCc).isOpen_compl⟩, ⟨genericPoint Z, ?_⟩, ?_⟩
  · show genericPoint Z ∉ π '' (V : Set Z')ᶜ
    rintro ⟨x, hxC, hx⟩
    have h1 : genericPoint Z' ⤳ x := (genericPoint_spec Z').specializes (Set.mem_univ x)
    have h2 : π (genericPoint Z') = genericPoint Z := by
      have a : π (genericPoint Z') ⤳ π x := h1.map π.continuous
      rw [hx] at a
      exact (a.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq
    haveI hd := (π.isDiscrete_preimage_singleton (genericPoint Z)).to_subtype
    have m2 : genericPoint Z' ∈ (π ⁻¹' {genericPoint Z} : Set Z') := h2
    have mx : x ∈ (π ⁻¹' {genericPoint Z} : Set Z') := hx
    have h3 : (⟨genericPoint Z', m2⟩ : (π ⁻¹' {genericPoint Z} : Set Z')) ⤳ ⟨x, mx⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp h1
    have h4 : genericPoint Z' = x := congrArg Subtype.val (specializes_iff_eq.mp h3)
    apply hxC
    rw [← h4]
    exact ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩
end
