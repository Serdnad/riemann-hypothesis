module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Continuity
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
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem isRelevant_iff {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (I : Ideal (MRing ι R)) :
    IsRelevant I ↔ ∀ k, ∃ v : Σ k, ι k, v.1 = k ∧ (X v : MRing ι R) ∉ I := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · intro h k
    obtain ⟨⟨k', i⟩, hk, hi⟩ := h k
    subst hk
    exact ⟨i, hi⟩

theorem extend_zero_inj {K K' : Type*} {j : K → K'} (hj : Function.Injective j)
    {x y : K → ℕ} : Function.extend j x 0 = Function.extend j y 0 ↔ x = y :=
  ⟨fun h => funext fun k => by simpa [hj.extend_apply] using congrFun h (j k), fun h => h ▸ rfl⟩

variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)

include hgj

include hgj in
theorem weight_mapDomain (hj : Function.Injective j) (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g d) =
      Function.extend j (Finsupp.weight (blockWeight ι) d) 0 := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • blockWeight ι' i)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext k'
  by_cases hk : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hj.extend_apply]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      hj.eq_iff]
  · rw [Function.extend_apply' _ _ _ hk]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight, hgj, Pi.single_apply,
      Pi.zero_apply]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [ite_eq_right fun h => hk ⟨v.1, h.symm⟩, smul_zero]


include hgj in
theorem rename_weightedHomogeneousComponent (hj : Function.Injective j)
    (hg : Function.Injective g) {R : Type*} [CommSemiring R] (b : K → ℕ)
    (f : MvPolynomial (Σ k, ι k) R) :
    rename g (weightedHomogeneousComponent (blockWeight ι) b f) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0) (rename g f) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain g d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain g hg, coeff_rename_mapDomain g hg,
      coeff_weightedHomogeneousComponent, weight_mapDomain hgj hj, extend_zero_inj hj]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (hd u)]
    · rfl


include hgj in
theorem isMultiProjPrime_comap_rename (hj : Function.Injective j) (hg : Function.Injective g)
    (hsurj : ∀ w : Σ k, ι' k, w.1 ∈ Set.range j → ∃ v, g v = w) {R : Type*} [CommRing R]
    {P : Ideal (MRing ι' R)} (hP : IsMultiProjPrime P) :
    IsMultiProjPrime (P.comap (rename (R := R) g)) := by
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [rename_weightedHomogeneousComponent hgj hj hg]
    exact hP.multiHomog _ hf _
  · rw [isRelevant_iff]
    intro k
    obtain ⟨w, hw, hwP⟩ := (isRelevant_iff P).1 hP.relevant (j k)
    obtain ⟨v, rfl⟩ := hsurj w ⟨k, hw.symm⟩
    refine ⟨v, hj (by rw [← hgj, hw]), ?_⟩
    rw [Ideal.mem_comap, rename_X]
    exact hwP

end

end GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u u' v v' w

section Objects

def HasRelDim {F : Type u} [Field F] {K : Type v} [Fintype K] {ι : K → Type w}
    (I : Ideal (MRing ι F)) (n : ℕ) : Prop :=
  ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)



end Objects


section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace PFContracted

section Drop

variable {K : Type*} {ι : K → Type*} {F : Type*} [Field F]

theorem ringKrullDim_add_one_le {P Q : Ideal (MRing ι F)} [P.IsPrime] (hPQ : P ≤ Q)
    {f : MRing ι F} (hfP : f ∉ P) (hfQ : f ∈ Q) :
    ringKrullDim (MRing ι F ⧸ Q) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P f) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfQ

theorem ringKrullDim_lt_top [Finite K] [∀ k, Finite (ι k)] (Q : Ideal (MRing ι F)) :
    ringKrullDim (MRing ι F ⧸ Q) < ⊤ := by
  refine lt_of_le_of_lt (ringKrullDim_quotient_le Q) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)

end Drop

section Kill

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def killBlocks (T : Finset K) : MRing ι F →ₐ[F] MRing ι F :=
  aeval fun v => if v.1 ∈ T then 0 else X v

theorem killBlocks_X (T : Finset K) (v : Σ k, ι k) :
    killBlocks (F := F) T (X v) = if v.1 ∈ T then 0 else X v := by
  simp [killBlocks]

theorem killBlocks_empty : killBlocks (ι := ι) (F := F) (∅ : Finset K) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [killBlocks_X]

theorem killBlocks_comp {T T' : Finset K} (h : T ⊆ T') :
    (killBlocks (ι := ι) (F := F) T').comp (killBlocks T) = killBlocks T' := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, killBlocks_X]
  by_cases hv : v.1 ∈ T
  · simp [hv, h hv]
  · simp [hv, killBlocks_X]

theorem killBlocks_monomial (T : Finset K) (d : (Σ k, ι k) →₀ ℕ) (c : F) :
    killBlocks T (monomial d c) =
      if ∀ v ∈ d.support, v.1 ∉ T then monomial d c else 0 := by
  rw [killBlocks, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    exact Finsupp.prod_congr fun v hv => by rw [if_neg (h v hv)]
  · simp only [not_forall, not_not] at h
    obtain ⟨v, hv, hT⟩ := h
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)
    dsimp only
    rw [if_pos hT, zero_pow (Finsupp.mem_support_iff.mp hv)]

theorem coeff_killBlocks (T : Finset K) (q : MRing ι F) (d : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (killBlocks T q) d = if ∀ v ∈ d.support, v.1 ∉ T then AddMonoidAlgebra.coeff q d else 0 := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial d' c =>
    rw [killBlocks_monomial, apply_ite (AddMonoidAlgebra.coeff · d), AddMonoidAlgebra.coeff_zero, coeff_monomial]
    by_cases hd : d' = d
    · subst hd
      simp
    · simp [hd]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add]
    change AddMonoidAlgebra.coeff (killBlocks T p) d + AddMonoidAlgebra.coeff (killBlocks T q) d = _
    rw [hp, hq]
    split_ifs <;> simp

theorem weight_apply_eq_zero_iff (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = 0 ↔ ∀ v ∈ d.support, v.1 ≠ k := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff]
  refine forall₂_congr fun v hv => ?_
  simp only [Pi.smul_apply, smul_eq_mul, blockWeight, Pi.single_apply, mul_ite, mul_one, mul_zero]
  have := Finsupp.mem_support_iff.mp hv
  constructor
  · intro h hk
    rw [if_pos hk.symm] at h
    exact this h
  · intro h
    rw [if_neg (fun hk => h hk.symm)]

theorem killBlocks_of_isMultiHomog (T : Finset K) {p : MRing ι F} {b : K → ℕ}
    (hp : IsMultiHomog p b) : killBlocks T p = if ∀ k ∈ T, b k = 0 then p else 0 := by
  ext d
  rw [coeff_killBlocks]
  by_cases hd : AddMonoidAlgebra.coeff p d = 0
  · split_ifs <;> simp [hd]
  · have hw : Finsupp.weight (blockWeight ι) d = b := hp hd
    have key : (∀ v ∈ d.support, v.1 ∉ T) ↔ ∀ k ∈ T, b k = 0 := by
      constructor
      · intro h k hk
        rw [← hw, weight_apply_eq_zero_iff]
        intro v hv hvk
        exact h v hv (hvk ▸ hk)
      · intro h v hv hvT
        have := h v.1 hvT
        rw [← hw, weight_apply_eq_zero_iff] at this
        exact this v hv rfl
    by_cases hb : ∀ k ∈ T, b k = 0
    · rw [if_pos (key.mpr hb), if_pos hb]
    · rw [if_neg (fun h => hb (key.mp h)), if_neg hb, AddMonoidAlgebra.coeff_zero]
      rfl

theorem killBlocks_mem_of_isMultiHomogIdeal {Q : Ideal (MRing ι F)} (hQ : IsMultiHomogIdeal Q)
    (T : Finset K) {q : MRing ι F} (hq : q ∈ Q) : killBlocks T q ∈ Q := by

  rw [← sum_weightedHomogeneousComponent (blockWeight ι) q,
  finsum_eq_sum _ (weightedHomogeneousComponent_finsupp q), map_sum]
  refine Ideal.sum_mem _ fun b _ => ?_
  rw [killBlocks_of_isMultiHomog T (weightedHomogeneousComponent_isWeightedHomogeneous b q)]
  split_ifs
  · exact hQ q hq b
  · exact Q.zero_mem

def killIdeal (Q : Ideal (MRing ι F)) (T : Finset K) : Ideal (MRing ι F) :=
  Q.comap (killBlocks T)

theorem card_le_ringKrullDim [Fintype K] {Q : Ideal (MRing ι F)} [hQp : Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q) :
    (Fintype.card K : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q) := by
  choose i hi using hrel
  have hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T' := by
    intro T T' h q hq
    change killBlocks T' q ∈ Q
    rw [← killBlocks_comp h]
    exact hQ T' _ hq
  have hprime : ∀ T, (killIdeal Q T).IsPrime := fun T => Ideal.comap_isPrime _ _
  have hchain : ∀ T : Finset K,
      ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
        ringKrullDim (MRing ι F ⧸ Q) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : killIdeal Q (∅ : Finset K) = Q := by
        ext q
        simp [killIdeal, killBlocks_empty]
      rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
    | insert k T hk ih =>
      have := hprime T
      have hstep := ringKrullDim_add_one_le (P := killIdeal Q T) (Q := killIdeal Q (insert k T))
        (hmono (Finset.subset_insert k T)) (f := X ⟨k, i k⟩)
        (by
          change killBlocks T (X ⟨k, i k⟩) ∉ Q
          rw [killBlocks_X, if_neg hk]
          exact hi k)
        (by
          change killBlocks (insert k T) (X ⟨k, i k⟩) ∈ Q
          rw [killBlocks_X, if_pos (Finset.mem_insert_self k T)]
          exact Q.zero_mem)
      calc ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + ((insert k T).card : WithBot ℕ∞)
          = (ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + 1) + (T.card : WithBot ℕ∞) := by
            rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_assoc,
              add_comm (1 : WithBot ℕ∞)]
        _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) := by gcongr
        _ ≤ _ := ih
  have := hprime Finset.univ
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ killIdeal Q Finset.univ)
  have := hchain Finset.univ
  rw [Finset.card_univ] at this
  calc (Fintype.card K : WithBot ℕ∞) = 0 + (Fintype.card K : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q Finset.univ) + (Fintype.card K : WithBot ℕ∞) := by
        gcongr
    _ ≤ _ := this

end Kill

end PFContracted

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ValuativeCentre.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P),
    haveI := hP.isPrime
    ∀ R : ValuationSubring (FractionRing (MRing ι F ⧸ P)),
      (∀ c : F, algebraMap F (FractionRing (MRing ι F ⧸ P)) c ∈ R) →
      ∃ y : Ideal (MRing ι F), IsMultiProjPrime y ∧ P ≤ y ∧
        ∀ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
              algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ R ∧
            (f ∈ y ↔ algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
                (Ideal.Quotient.mk P f) / algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈
              R.nonunits)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Split

variable {K K' : Type}

end Split

def RenameMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K K' : Type) [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k')), (∀ v, (g v).1 = j v.1) →
    ∀ (f : MRing ι R) (d : K → ℕ), IsMultiHomog f d →
      IsMultiHomog (rename g f) (Function.extend j d 0)

def RenameHilbFn.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (m : S → ℤ),
      hilbFn (P.comap (rename σ)) m = hilbFn P (m ∘ E.symm)

def RenameIntNum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ (P : Ideal (MRing ι' F)) (n : ℕ) (bs : Fin n → S → ℤ),
      intNum F (P.comap (rename σ)) bs = intNum F P (fun i => bs i ∘ E.symm)

def RenameMultiProjPrime.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (S K' : Type) [DecidableEq S] [DecidableEq K'] (κ : S → Type)
    (ι' : K' → Type) (E : S ≃ K') (σ : (Σ s, κ s) ≃ (Σ k', ι' k')), (∀ v, (σ v).1 = E v.1) →
    ∀ P : Ideal (MRing ι' R), IsMultiProjPrime P → IsMultiProjPrime (P.comap (rename σ))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
