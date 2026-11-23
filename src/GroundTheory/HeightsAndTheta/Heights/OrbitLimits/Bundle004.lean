module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
import Mathlib.Algebra.CharP.Subring
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult)

def LelongPolyLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (f k : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → p ∉ J →
    SmoothNear (ComplexSets.zeroSet J) f → HasCompactSupport f →
    (∀ j, SmoothNear (ComplexSets.zeroSet J) (φ j)) →
    SmoothNear (ComplexSets.zeroSet J) k → (∀ x ∈ ComplexSets.zeroSet J, 0 < k x) →
      Tendsto (fun ε : ℝ =>
          varInt J (d + 1) f (vecCons (fun x => Real.log (‖eval x p‖ ^ 2 + ε * k x ^ 2) / 2) φ))
        (𝓝[>] 0)
        (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {p}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {p}) W : ℝ) * varInt W d f φ))

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single euclPot)

def LelongWeightLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f k : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    SmoothNear (ComplexSets.zeroSet J) f → HasCompactSupport f →
    (∀ j, SmoothNear (ComplexSets.zeroSet J) (φ j)) →
    SmoothNear (ComplexSets.zeroSet J) k → (∀ x ∈ ComplexSets.zeroSet J, 0 < k x) →
      Tendsto (fun ε : ℝ =>
          varInt J (d + 1) f (vecCons (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) φ))
        (𝓝[>] 0)
        (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem exists_pair_poly {n d : ℕ} (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hJJ' : ¬ J' ≤ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ x ∈ zeroSet J, x ∈ zeroSet J' → eval (A *ᵥ x) c = 0 := by
  obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hJJ'
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  have := hJ
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) := hA.finite.to_isIntegral _
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨c, hc0, fun x hx hx' => ?_⟩
  have h1 : Ideal.Quotient.mk J (pullback A c) = Ideal.Quotient.mk J (r * f) := by
    rw [map_mul]; exact hr.symm
  have h2 := hx _ (Ideal.Quotient.eq.1 h1)
  rwa [map_sub, map_mul, hx' f hfJ', mul_zero, sub_zero, ComplexSets.FibreBound.eval_pullback] at h2

theorem encard_biUnion_le {ι α : Type*} (F : Finset ι) (S : ι → Set α) :
    (⋃ i ∈ F, S i).encard ≤ ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (by gcongr)

theorem encard_biUnion_eq {ι α : Type*} (F : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ F, S i).encard = ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ih]
    · exact fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · refine Set.disjoint_iUnion₂_right.2 fun j hj =>
        h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) ?_
      rintro rfl
      exact ha hj

theorem exists_prod_ne_zero {ι : Type*} {k : ℕ} (F : Finset ι) (p : ι → MvPolynomial (Fin k) ℂ → Prop)
    (h : ∀ i ∈ F, ∃ P, P ≠ 0 ∧ p i P) :
    ∃ Δ : MvPolynomial (Fin k) ℂ, Δ ≠ 0 ∧
      ∀ y, eval y Δ ≠ 0 → ∀ i ∈ F, ∃ P, p i P ∧ eval y P ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨Δ, hΔ, hΔy⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨P, hP, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨P * Δ, mul_ne_zero hP hΔ, fun y hy i hi => ?_⟩
    rw [map_mul] at hy
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨P, hPa, left_ne_zero_of_mul hy⟩
    · exact hΔy y (right_ne_zero_of_mul hy) i hi

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def FibreDegreeSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (a : Fin e → K → ℤ) (p : ℕ),
    IsArithVar P (e + 1) → p.Prime →
      NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
        ∑ᶠ V ∈ divSupp P (C (p : ℤ)), (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℤ) * geoNum e V a

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

theorem InvertibleIndexCharP.finite_subring {Ω : Type} [Field Ω] (B : Subring Ω) (hp : ringChar Ω ≠ 0)
    (hB : Module.Finite ℤ B) : Finite B := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(ringChar Ω : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, ?_⟩
  rw [Submonoid.smul_def]
  ext
  simp [zsmul_eq_mul]

theorem InvertibleIndexCharP.proof : InvertibleIndexCharP.Statement := by
  intro Ω _ B X η _ f hp hB hX hf hloc
  have hfin : Finite B := InvertibleIndexCharP.finite_subring B hp hB
  have hfield : IsField B := Finite.isField_of_domain B
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨i, ⟨b₀, hb₀m, hb₀X⟩, hgen⟩ := hloc m hm

  have hunit : ∀ b : B, b ∉ m → ∃ b' : B, (b' : Ω) * b = 1 := by
    intro b hb
    have hb0 : b ≠ 0 := fun h => hb (h ▸ m.zero_mem)
    obtain ⟨b', hb'⟩ := hfield.mul_inv_cancel hb0
    refine ⟨b', ?_⟩
    have := congrArg Subtype.val hb'
    simpa [mul_comm] using this

  have hXeq : (X : Set Ω) = (fun y => f i * y) '' (B : Set Ω) := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, c, hbm, hbc⟩ := hgen z hz
      obtain ⟨b', hb'⟩ := hunit b hbm
      refine ⟨((b' * c : B) : Ω), (b' * c).2, ?_⟩
      calc f i * ((b' * c : B) : Ω) = b' * (c * f i) := by push_cast; ring
        _ = b' * (b * z) := by rw [hbc]
        _ = z := by rw [← mul_assoc, hb', one_mul]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨b', hb'⟩ := hunit b₀ hb₀m
      have hfX : f i ∈ X := by
        have := hX b' b'.2 _ hb₀X
        rwa [← mul_assoc, hb', one_mul] at this
      have := hX y hy _ hfX
      rw [mul_comm] at this
      exact this
  set A := B.toAddSubgroup with hA
  have hAfin : Finite A := hfin
  have hXfin' : (X : Set Ω).Finite := by
    rw [hXeq]; exact (Set.toFinite (B : Set Ω)).image _
  have hXfin : Finite X := hXfin'.to_subtype

  have hcard : Nat.card X = Nat.card A := by
    have h := Nat.card_image_of_injective (mul_right_injective₀ (hf i)) (B : Set Ω)
    rw [← hXeq] at h
    exact h
  have hc : Nat.card (A.addSubgroupOf X) = Nat.card (X.addSubgroupOf A) :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        invFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have k1 : Nat.card (A.addSubgroupOf X) * A.relIndex X = Nat.card X :=
    (A.addSubgroupOf X).card_mul_index
  have k2 : Nat.card (X.addSubgroupOf A) * X.relIndex A = Nat.card A :=
    (X.addSubgroupOf A).card_mul_index
  have hpos : 0 < Nat.card (A.addSubgroupOf X) := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have heq : A.relIndex X = X.relIndex A := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [k1, hc, k2, hcard]
  have hne : X.relIndex A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at k2
    omega
  unfold genIndex
  rw [heq]
  exact div_self (by exact_mod_cast hne)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem LocalGenFamily.proof : LocalGenFamily.Statement := by
  intro Ω _ B X η _ f hfin hX hf0 hc hloc
  have : Module.Finite ℤ B := hfin
  have : IsNoetherianRing B := IsNoetherianRing.of_finite ℤ B

  let K : η → Ideal B := fun i =>
    { carrier := {t : B | (t : Ω) * f i ∈ X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at ha hb ⊢
        exact X.add_mem ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact X.zero_mem
      smul_mem' := fun c t ht => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at ht ⊢
        exact hX _ c.2 _ ht }
  have hK : ∀ i, ∀ t : B, t ∈ K i ↔ (t : Ω) * f i ∈ X := fun _ _ => Iff.rfl
  have hfg : ∀ i, ∃ T : Finset B, Ideal.span (T : Set B) = K i := fun i => IsNoetherian.noetherian (K i)
  choose T hT using hfg
  refine ⟨?_, Σ i : η, {t : B // t ∈ T i}, inferInstance, fun j => (j.2.1 : Ω) * f j.1, ?_, ?_, ?_⟩
  ·
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    obtain ⟨i, ⟨b, hbm, hbX⟩, -⟩ := hloc m hm
    have hb : (b : Ω) ≠ 0 := by
      intro h
      exact hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)
    intro hbot
    rw [hbot, AddSubgroup.mem_bot] at hbX
    exact mul_ne_zero hb (hf0 i) hbX
  · rintro ⟨i, t, ht⟩
    rw [← hK, ← hT i]
    exact Ideal.subset_span ht
  · rintro ⟨i, t, -⟩
    obtain ⟨c, hcB, hc0, hcf⟩ := hc i
    refine ⟨c, hcB, hc0, ?_⟩
    rw [mul_left_comm]
    exact B.mul_mem t.2 hcf
  · intro m hm
    obtain ⟨i, ⟨b, hbm, hbX⟩, hall⟩ := hloc m hm
    have : ∃ t ∈ T i, t ∉ m := by
      by_contra hno
      push Not at hno
      have hle : K i ≤ m := by
        rw [← hT i, Ideal.span_le]
        exact fun t ht => hno t ht
      exact hbm (hle ((hK i b).2 hbX))
    obtain ⟨t, htT, htm⟩ := this
    refine ⟨⟨i, t, htT⟩, fun z hz => ?_⟩
    obtain ⟨b', c', hb'm, hbz⟩ := hall z hz
    refine ⟨t * b', c', fun h => ?_, ?_⟩
    · rcases hm.isPrime.mem_or_mem h with h | h
      · exact htm h
      · exact hb'm h
    · simp only [Subring.coe_mul]
      calc (t : Ω) * b' * z = t * (b' * z) := by ring
        _ = t * (c' * f i) := by rw [hbz]
        _ = c' * (t * f i) := by ring

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem InvertibleProductRep.mem_of_local {Ω : Type} [Field Ω] (B : Subring Ω) (Y : AddSubgroup Ω)
    (hY : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y) (z : Ω)
    (hz : ∀ m : Ideal B, m.IsMaximal → ∃ b : B, b ∉ m ∧ (b : Ω) * z ∈ Y) : z ∈ Y := by
  let A : Ideal B :=
    { carrier := {a : B | (a : Ω) * z ∈ Y}
      add_mem' := by
        intro a c ha hc
        show ((a + c : B) : Ω) * z ∈ Y
        push_cast
        rw [add_mul]
        exact Y.add_mem ha hc
      zero_mem' := by
        show ((0 : B) : Ω) * z ∈ Y
        simp
      smul_mem' := by
        intro c a ha
        show ((c * a : B) : Ω) * z ∈ Y
        push_cast
        rw [mul_assoc]
        exact hY c c.2 _ ha }
  by_cases hA : A = ⊤
  · have h1 : (1 : B) ∈ A := hA ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * z ∈ Y := h1
    simpa using h2
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨b, hb, hbz⟩ := hz m hm
    exact absurd (hle (show b ∈ A from hbz)) hb

theorem InvertibleProductRep.proof : InvertibleProductRep.Statement := by
  intro Ω _ B M N P η _ g h β δ β' δ' I J hβ hδ hβ' hδ' hM hN hP hloc x
  have hβΩ : (β : Ω) ≠ 0 := fun h0 => hβ (Subtype.ext (by rw [h0]; rfl))
  have hβ'Ω : (β' : Ω) ≠ 0 := fun h0 => hβ' (Subtype.ext (by rw [h0]; rfl))
  have hne : ((β * β' : B) : Ω) ≠ 0 := by push_cast; exact mul_ne_zero hβΩ hβ'Ω
  have notin : ∀ (m : Ideal B), m.IsMaximal → ∀ a b c : B, a ∉ m → b ∉ m → c ∉ m → a * b * c ∉ m := by
    intro m hm a b c ha hb hc h0
    rcases hm.isPrime.mem_or_mem h0 with h1 | h1
    · rcases hm.isPrime.mem_or_mem h1 with h2 | h2
      · exact ha h2
      · exact hb h2
    · exact hc h1
  constructor
  · intro hx
    let Y : AddSubgroup Ω :=
      { carrier := {w | ∃ y ∈ I * J, ((β * β' : B) : Ω) * w = ((δ * δ' : B) : Ω) * (y : Ω)}
        add_mem' := by
          rintro a c ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
          refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
          push_cast at e₁ e₂ ⊢
          linear_combination e₁ + e₂
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        neg_mem' := by
          rintro a ⟨y, hy, e⟩
          refine ⟨-y, neg_mem hy, ?_⟩
          push_cast at e ⊢
          linear_combination -e }
    have hYst : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y := by
      rintro b hb z ⟨y, hy, e⟩
      refine ⟨⟨b, hb⟩ * y, (I * J).mul_mem_left _ hy, ?_⟩
      push_cast at e ⊢
      linear_combination b * e
    have key : x ∈ Y := by
      refine InvertibleProductRep.mem_of_local B Y hYst x fun m hm => ?_
      obtain ⟨i, ⟨⟨b₁, hb₁, hgM⟩, -⟩, ⟨⟨b₂, hb₂, hhN⟩, -⟩, ⟨-, hPz⟩⟩ := hloc m hm
      obtain ⟨b, c, hb, e⟩ := hPz x hx
      obtain ⟨u, hu, eu⟩ := (hM _).1 hgM
      obtain ⟨v, hv, ev⟩ := (hN _).1 hhN
      refine ⟨b₁ * b₂ * b, notin m hm _ _ _ hb₁ hb₂ hb, c * (u * v),
        (I * J).mul_mem_left _ (Ideal.mul_mem_mul hu hv), ?_⟩
      push_cast at e eu ev ⊢
      linear_combination ((β : Ω) * β' * b₁ * b₂) * e + ((c : Ω) * β' * b₂ * h i) * eu +
        ((c : Ω) * δ * u) * ev
    obtain ⟨y, hy, e⟩ := key
    exact ⟨y, hy, by push_cast at e ⊢; linear_combination e⟩
  · rintro ⟨y, hy, e⟩
    have claim : ∀ r ∈ I * J, ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P := by
      intro r hr
      refine Submodule.mul_induction_on
        (C := fun r : B => ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P) hr ?_ ?_
      · intro u hu v hv
        have hp : (δ : Ω) * u / β ∈ M := (hM _).2 ⟨u, hu, by field_simp⟩
        have hq : (δ' : Ω) * v / β' ∈ N := (hN _).2 ⟨v, hv, by field_simp⟩
        have hpq : ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') ∈ P := by
          refine InvertibleProductRep.mem_of_local B P hP _ fun m hm => ?_
          obtain ⟨i, ⟨-, hMz⟩, ⟨-, hNz⟩, ⟨⟨b'', hb'', hgh⟩, -⟩⟩ := hloc m hm
          obtain ⟨b, c, hb, e₁⟩ := hMz _ hp
          obtain ⟨b', c', hb', e₂⟩ := hNz _ hq
          refine ⟨b * b' * b'', notin m hm _ _ _ hb hb' hb'', ?_⟩
          have eq : ((b * b' * b'' : B) : Ω) * (((δ : Ω) * u / β) * ((δ' : Ω) * v / β')) =
              ((c * c' : B) : Ω) * ((b'' : Ω) * (g i * h i)) := by
            push_cast
            linear_combination ((b' : Ω) * b'' * ((δ' : Ω) * v / β')) * e₁ + ((c : Ω) * b'' * g i) * e₂
          rw [eq]
          exact hP _ (c * c').2 _ hgh
        have : ((δ * δ' : B) : Ω) * ((u * v : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') := by
          push_cast
          field_simp
        rw [this]
        exact hpq
      · intro a c ha hc
        have : ((δ * δ' : B) : Ω) * ((a + c : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ * δ' : B) : Ω) * (a : Ω) / ((β * β' : B) : Ω) +
              ((δ * δ' : B) : Ω) * (c : Ω) / ((β * β' : B) : Ω) := by
          push_cast
          ring
        rw [this]
        exact P.add_mem ha hc
    have hx : x = ((δ * δ' : B) : Ω) * (y : Ω) / ((β * β' : B) : Ω) := by
      rw [eq_div_iff hne]
      push_cast at e ⊢
      linear_combination e
    rw [hx]
    exact claim y hy

end GroundTheory.Heights₂.Heights.Targets
end
