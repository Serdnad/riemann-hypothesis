module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord mcIdeal mcMap assocDeg assocVar joinCoord_assocVar IsVertDiv)

noncomputable section

namespace JoinVerticalDivisorLeft

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocVar_fst (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    (assocVar ι₂ p).1 = Sum.map id Sum.inl p.1 := by
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem assocBlock_injective :
    Function.Injective (Sum.map id Sum.inl : K ⊕ K' → K ⊕ (K' ⊕ K₂)) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem mcMap_rename_assocVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord z w)) (rename (assocVar ι₂) h) =
      rename (Sum.map id Sum.inl) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, rename_X, hp]
    congr 1
    simp [mcMap, joinCoord_assocVar, assocVar_fst]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem rename_assocVar_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord z w)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker]
  rw [mcMap_rename_assocVar]
  exact map_eq_zero_iff _ (rename_injective _ assocBlock_injective)


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem blockWeight_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (p : Σ k : K ⊕ K', Sum.elim ι ι' k) (s : K ⊕ (K' ⊕ K₂)) :
    blockWeight (Sum.elim ι (Sum.elim ι' ι₂)) (assocVar ι₂ p) s =
      Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inl k))
        (Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inr k)) 0) s := by
  obtain ⟨k | k, i⟩ := p <;> rcases s with l | l | l <;> simp [blockWeight, assocVar, Pi.single_apply]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem weight_mapDomain_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι' ι₂))) (Finsupp.mapDomain (assocVar ι₂) d) =
      Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
        (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
    Finsupp.weight_apply]
  funext s
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockWeight_assocVar]
  rcases s with l | l | l <;> simp


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem isMultiHomog_rename_assocVar' [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    exact weight_mapDomain_assocVar d

theorem isMultiHomog_rename_assocVar {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_rename_assocVar' hf


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (c : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) c h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι' ι₂)))
        (Sum.elim (fun k => c (.inl k)) (Sum.elim (fun k => c (.inr k)) 0)) (rename (assocVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MRing (Sum.elim ι ι') R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename_assocVar' (ι₂ := ι₂) hm
    by_cases hc : c = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hc
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · have hc' : (Sum.elim (fun k => c (.inl k)) (Sum.elim (fun k => c (.inr k)) 0) :
            K ⊕ (K' ⊕ K₂) → ℕ) ≠
          Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
            (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by
        intro e
        apply hc
        funext k
        rcases k with k | k
        · exact congrFun e (.inl k)
        · exact congrFun e (.inr (.inl k))
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne c hm hc,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj hc', map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh c => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · rcases k with k | k
    · obtain ⟨i, hi⟩ := hQ.relevant (.inl k)
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
    · obtain ⟨i, hi⟩ := hQ.relevant (.inr (.inl k))
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinVerticalDivisorLeft


open JoinVerticalDivisorLeft in
theorem JoinVerticalDivisorLeft.proof : JoinVerticalDivisorLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨_, _, isMultiHomog_rename_assocVar (ι₂ := ι₂) hf, isMultiHomog_rename_assocVar (ι₂ := ι₂) hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · simpa [assocDeg] using hb (.inl k)
    · simpa [assocDeg] using hb (.inr k)
    · simp [assocDeg]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_assocVar_mem_mcIdeal_iff O x z w h).mpr hh))
    have hO : (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (assocVar ι₂) u, rename (assocVar ι₂) v, ⟨_, isMultiHomog_rename_assocVar hu⟩,
      ⟨_, isMultiHomog_rename_assocVar hv⟩, huQ, hvQ, ?_⟩
    have := (rename_assocVar_mem_mcIdeal_iff O x z w _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)

noncomputable section

namespace JoinVerticalDivisorRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def midNat (a : K ⊕ K' → ℕ) : K ⊕ (K₂ ⊕ K') → ℕ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))

theorem midNat_injective : Function.Injective (midNat (K := K) (K' := K') (K₂ := K₂)) := by
  intro a b e
  funext l
  rcases l with k | k
  · exact congrFun e (.inl k)
  · exact congrFun e (.inr (.inr k))

theorem midVar_injective : Function.Injective (midVar (ι := ι) (ι' := ι') ι₂) := by
  rintro ⟨k | k, i⟩ ⟨l | l, j⟩ h <;> dsimp only [midVar] at h <;> cases h <;> rfl

theorem mcMap_rename_midVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord w z)) (rename (midVar ι₂) h) =
      rename (Sum.map id Sum.inr) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    obtain ⟨k | k, i⟩ := v <;> simp [mcMap, midVar, joinCoord]

theorem rename_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord w z)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker, mcMap_rename_midVar]
  exact map_eq_zero_iff _ (rename_injective _ (Sum.map_injective.mpr ⟨Function.injective_id,
    Sum.inr_injective⟩))

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem weight_mapDomain_midVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (Finsupp.mapDomain (midVar ι₂) d) =
      midNat (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := by
  funext l
  rw [Objects.weight_blockWeight_apply]
  rcases l with k | k | k
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply_of_injective midVar_injective d ⟨.inl k, i⟩
  · change _ = 0
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨k' | k', j⟩, h⟩ <;> dsimp only [midVar] at h <;> cases h
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply_of_injective midVar_injective d ⟨.inr k, i⟩

theorem isMultiHomog_rename [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [weight_mapDomain_midVar, hr])

theorem isMultiHomog_rename' {R : Type} [CommRing R] {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R}
    {a : K ⊕ K' → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_rename hf

theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (b : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (midNat b)
        (rename (midVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename (ι₂ := ι₂) hm
    by_cases hb : b = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj (fun e => hb (midNat_injective e)),
        map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · rcases k with k | k
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inr (Sum.inr k))
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinVerticalDivisorRight


open JoinVerticalDivisorRight in
theorem JoinVerticalDivisorRight.proof : JoinVerticalDivisorRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨midNat α, midNat β, isMultiHomog_rename' hf, isMultiHomog_rename' hg, ?_⟩, ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · exact hb (.inl k)
    · simp [midNat, midDeg]
    · exact hb (.inr k)
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x w z h).mpr hh))
    have hO : (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (midVar ι₂) u, rename (midVar ι₂) v, ⟨_, isMultiHomog_rename' hu⟩,
      ⟨_, isMultiHomog_rename' hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x w z _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpFibreDegree.proof (ha : HomLocRingLocal.Statement.{u}) (hb : DivCycleHomLoc.Statement.{u})
    (hc : FiniteBirationalLength.Statement.{u}) (hd : BlowUpFibreSemilocal.Statement.{u}) :
    BlowUpFibreDegree.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hdiv
  have hsupp : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hdiv (by unfold divCycle; rw [dite_eq_right h])
  have hWp : W.IsPrime := hsupp.1.1.1
  have := hP.multiProj.isPrime
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hsupp.2 c
  have hg : IsMultiHomog (powMonomial c i : MRing ι O) c := isMultiHomog_powMonomial c i
  have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
        (Ideal.Quotient.mk P (powMonomial c i)) ∈ homLocRing P W :=
    Subring.subset_closure ⟨c, x, _, hx, hg, hi, rfl⟩
  obtain ⟨hloc, hnoeth, hdim⟩ := ha O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2
  have := hloc
  have := hnoeth
  obtain ⟨B, _, _, _, hfin, hinj, hrank, e, he⟩ :=
    hd O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hsupp.1 hsupp.2 _ hg hi hz
  have hz0 : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun w : homLocRing P W => (w : FractionRing (MRing ι O ⧸ P))) h0
    simp only [ZeroMemClass.coe_zero] at h1
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))
    · exact hi (hsupp.1.1.2 (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))))
  obtain ⟨hfinite, hlen⟩ := hc (homLocRing P W) B hdim hinj hrank _ hz0
  have hmult := hb O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2 _ hg hi hz
  have hdivW : divCycle P x W = ((multAt (P ⊔ Ideal.span {x}) W).toNat : ℤ) := by
    unfold divCycle
    rw [dite_eq_left hsupp]
  have := Fintype.ofFinite {𝔫 : Ideal B // 𝔫.IsMaximal}

  have hterm : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
      (have := 𝔫.2.isPrime;
       Module.length (Localization.AtPrime 𝔫.1)
         (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {(algebraMap B (Localization.AtPrime 𝔫.1)
           (algebraMap (homLocRing P W) B ⟨_, hz⟩))})) * (𝔫.1.inertiaDeg (homLocRing P W) : ℕ∞) =
        (((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat * specialRelDeg (e 𝔫).1 : ℕ) : ℕ∞) := by
    intro 𝔫
    rw [(he 𝔫).1, (he 𝔫).2, Nat.cast_mul]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum] at hlen
  rw [hdivW, hmult, hlen, ENat.toNat_natCast, Nat.cast_sum]

  classical
  let p : Ideal (MRing (extIdx ι J) O) → Prop := fun W' =>
    W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
  have hite : ∀ W' : Ideal (MRing (extIdx ι J) O),
      (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
        divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) =
      ∑ᶠ (_ : p W'), divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) := by
    intro W'
    rw [finsum_eq_if]
    by_cases hc' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
    · by_cases hp : p W'
      · rw [if_pos hc', if_pos hp]
      · rw [if_pos hc', if_neg hp]
        have h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0 := by
          unfold divCycle
          rw [dite_eq_right]
          exact fun h => hp ⟨h.1, h.2, hc'⟩
        rw [h0, zero_mul]
    · rw [if_neg hc', if_neg (fun h => hc' h.2.2)]
  rw [finsum_congr hite, ← finsum_subtype_eq_finsum_cond p,
    ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have h0 : 0 ≤ divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1 := by
    unfold divCycle
    split_ifs <;> positivity
  rw [Nat.cast_mul, Int.toNat_of_nonneg h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
