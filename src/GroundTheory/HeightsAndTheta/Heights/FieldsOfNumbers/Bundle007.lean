module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle006
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import Mathlib.Algebra.MvPolynomial.Monad
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
public import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Filter.AtTopBot.Group

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DivCycleMinimal.ringKrullDim_eq {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type u} [Field F] (Q : Ideal (MRing ι F)) (m : ℕ)
    (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MRing ι F ⧸ Q) = d := by
    have h2 := PFContracted.ringKrullDim_lt_top Q
    cases hc : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [relDim, hc] at h
      exact absurd h (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [hc] at h2
        exact absurd h2 (by simp)
      | coe d => exact ⟨d, rfl⟩
  rw [PFContracted.relDim_eq_int hd, PFContracted.natCast_withBot_withTop] at h
  have h' : (d : ℤ) - Fintype.card K = m := by
    have := WithBot.coe_injective h
    exact_mod_cast WithTop.coe_injective this
  rw [hd]
  congr 1
  omega

theorem DivCycleMinimal.proof : DivCycleMinimal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hPn a ha W hW hWn hle
  have hmin : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hW, hle⟩, fun Q hQ hQW => ?_⟩
    obtain ⟨hQp, hJQ⟩ := hQ
    by_contra hWQ
    obtain ⟨f, hfW, hfQ⟩ := Set.not_subset.mp hWQ
    have h1 := PFContracted.ringKrullDim_add_one_le (P := Q) (Q := W) hQW hfQ hfW
    have h2 := PFContracted.ringKrullDim_add_one_le (P := P) (Q := Q) (le_sup_left.trans hJQ) ha
      (hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
    have h3 := (add_le_add h1 (le_refl 1)).trans h2
    rw [DivCycleMinimal.ringKrullDim_eq W n hWn, DivCycleMinimal.ringKrullDim_eq P (n + 1) hPn] at h3
    have h4 : (((n + Fintype.card K + 1 + 1 : ℕ)) : WithBot ℕ∞) ≤ ((n + 1 + Fintype.card K : ℕ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 := ENat.natCast_le_natCast.mp h5
    omega
  exact ⟨hmin, length_localizedQuot_ne_top _ _ hmin⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

namespace ContractRelDimLe

section Chain

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem ringKrullDim_killIdeal_add_card_le {Q : Ideal (MRing ι F)} [Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q)
    (T : Finset K) :
    ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
      ringKrullDim (MRing ι F ⧸ Q) := by
  choose i hi using hrel
  have hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T' := by
    intro T T' h q hq
    change killBlocks T' q ∈ Q
    rw [← killBlocks_comp h]
    exact hQ T' _ hq
  induction T using Finset.induction_on with
  | empty =>
    have : killIdeal Q (∅ : Finset K) = Q := by
      ext q
      simp [killIdeal, killBlocks_empty]
    rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
  | insert k T hk ih =>
    have : (killIdeal Q T).IsPrime := Ideal.comap_isPrime _ _
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

end Chain

section Contract

variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)


omit [DecidableEq K] in
theorem killBlocks_compl_rename :
    (killBlocks (ι := ι') (F := F) (Finset.univ.map j)ᶜ).comp (rename (blockIncl j ι')) =
      rename (blockIncl j ι') := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [killBlocks_X, blockIncl]


omit [DecidableEq K] in
theorem exists_rename_eq_killBlocks_compl (x : MRing ι' F) :
    ∃ a : MRing (fun k => ι' (j k)) F,
      rename (blockIncl j ι') a = killBlocks (Finset.univ.map j)ᶜ x := by
  induction x using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [killBlocks]⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩
  | mul_X p v hp =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨k', i⟩ := v
    rw [map_mul, killBlocks_X, ← ha]
    by_cases h : k' ∈ (Finset.univ.map j)ᶜ
    · exact ⟨0, by rw [if_pos h, mul_zero, map_zero]⟩
    · rw [if_neg h]
      simp only [Finset.mem_compl, Finset.mem_map, Finset.mem_univ, true_and, not_not] at h
      obtain ⟨k, rfl⟩ := h
      exact ⟨a * X ⟨k, i⟩, by rw [map_mul, rename_X]; rfl⟩

theorem ringKrullDim_contract_eq_killIdeal (P' : Ideal (MRing ι' F)) :
    ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') =
      ringKrullDim (MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ) := by
  set f : MRing (fun k => ι' (j k)) F →+* MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ :=
    (Ideal.Quotient.mk _).comp (rename (blockIncl j ι')).toRingHom
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_rename_eq_killBlocks_compl j ι' (F := F) x
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = _
    rw [Ideal.Quotient.eq, ha]
    change killBlocks _ (killBlocks _ x - x) ∈ P'
    rw [map_sub, ← AlgHom.comp_apply, killBlocks_comp le_rfl, sub_self]
    exact P'.zero_mem
  have hker : RingHom.ker f = contractPrime j P' := by
    ext a
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = 0 ↔ rename (blockIncl j ι') a ∈ P'
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change killBlocks _ (rename (blockIncl j ι') a) ∈ P' ↔ _
    rw [← AlgHom.comp_apply, killBlocks_compl_rename]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)

end Contract

theorem proof : ContractRelDimLe.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP'
  have := hP'.isPrime
  have hstab : ∀ (T : Finset K') (q : MRing ι' F), q ∈ P' → killBlocks T q ∈ P' :=
    fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq hstab hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (Q := contractPrime j P')
    (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)
  have hchain := ringKrullDim_killIdeal_add_card_le hstab hP'.relevant (Finset.univ.map j)ᶜ
  rw [← ringKrullDim_contract_eq_killIdeal, hD, hD', ← Nat.cast_add] at hchain
  have hle : D + ((Finset.univ.map j)ᶜ).card ≤ D' := by exact_mod_cast hchain
  have hcard : ((Finset.univ.map j)ᶜ).card + Fintype.card K = Fintype.card K' := by
    rw [Finset.card_compl, Finset.card_map, Finset.card_univ]
    have := Fintype.card_le_of_embedding j
    omega
  rw [relDim_eq_int hD, relDim_eq_int hD']
  exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by omega))

end ContractRelDimLe

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventuallyPolyUnique.proof : EventuallyPolyUnique.Statement := by
  intro K _ h p q hp hq
  classical
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (hp.and hq)
  have hpq : p - q = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset (p - q)
      (fun k => (Finset.range ((p - q).degreeOf k + 1)).image
        (fun i : ℕ => ((M k + (i : ℤ) : ℤ) : ℚ)))
    · intro k
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        simpa using hab
    · intro x hx
      choose i _ hix using fun k => Finset.mem_image.1 (hx k)
      have hm : M ≤ fun k => M k + (i k : ℤ) := fun k => by simp
      have hxm : x = fun k => (((M k + (i k : ℤ) : ℤ)) : ℚ) := funext fun k => (hix k).symm
      obtain ⟨h1, h2⟩ := hM _ hm
      rw [map_sub, hxm, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 hpq

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem IntNumUnique.proof (h1 : CutRational.Statement.{u}) (h2 : IntNumBase.Statement.{u})
    (h3 : ExistsForm.Statement.{u}) (h4 : DivCycleSupport.Statement.{u}) :
    IntNumUnique.Statement.{u} := by
  intro F _ K _ _ ι _ N hN P hP n
  induction n generalizing P with
  | zero =>
    intro hdim bs
    have hbs : bs = ![] := Subsingleton.elim _ _
    subst hbs
    rw [hN.base P hP hdim]
    obtain ⟨-, h⟩ := h2 F K ι P hP hdim
    rw [h]
    have := hP.isPrime
    simp [resDeg, hP.isPrime]
  | succ n ih =>
    intro hdim bs
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ := h3 F K ι P hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    rw [hbs, hN.cut P n hP hdim bf bg f g hf hg hfP hgP,
      h1 F K ι P hP n hdim bf bg f g hf hg hfP hgP]
    unfold cycEval
    congr 1
    funext W
    by_cases hW : ratDiv P f g W = 0
    · rw [hW, zero_mul, zero_mul]
    · have hsupp : IsMultiProjPrime W ∧ relDim W = (n : ℕ) := by
        unfold ratDiv at hW
        by_cases hfW : divCycle P f W = 0
        · have hgW : divCycle P g W ≠ 0 := by
            intro h
            apply hW
            rw [hfW, h, sub_zero]
          exact h4 F K ι P hP n hdim bg g hg hgP W hgW
        · exact h4 F K ι P hP n hdim bf f hf hfP W hfW
      simp only [ih W hsupp.1 hsupp.2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem RelevantPrimeDimGe.proof : RelevantPrimeDimGe.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  classical
  choose i hi using hP.relevant
  let j : K → (Σ k, ι k) := fun k => ⟨k, i k⟩
  let x : K → MRing ι F ⧸ P := fun k => Ideal.Quotient.mk P (X (j k))
  have key : ∀ p : MvPolynomial K F, aeval x p = Ideal.Quotient.mk P (rename j p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp only [aeval_C, rename_C]
      rfl
    | add p q hp hq => simp [hp, hq]
    | mul_X p k hp => simp [hp, x]
  have hw : ∀ β : K →₀ ℕ, Finsupp.weight (blockWeight ι) (Finsupp.mapDomain j β) = ⇑β := by
    intro β
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    funext k'
    simp [Finsupp.sum, Finset.sum_apply, blockWeight, j, Pi.single_apply]
    exact fun h => h.symm
  have hind : AlgebraicIndependent F x := by
    rw [algebraicIndependent_iff]
    intro G hG
    rw [key] at hG
    have hmem : rename j G ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hG
    ext α
    simp only [AddMonoidAlgebra.coeff_zero]
    have hcomp := hP.multiHomog _ hmem ⇑α
    have hsum : rename j G = ∑ β ∈ G.support, monomial (Finsupp.mapDomain j β) (AddMonoidAlgebra.coeff G β) := by
      calc rename j G = rename j (∑ β ∈ G.support, monomial β (AddMonoidAlgebra.coeff G β)) := by
            congr 1; exact G.as_sum
        _ = _ := by rw [map_sum]; simp only [rename_monomial]
    have hc : weightedHomogeneousComponent (blockWeight ι) (⇑α) (rename j G) =
        rename j (monomial α (AddMonoidAlgebra.coeff G α)) := by

      rw [hsum, map_sum, rename_monomial]
      rw [Finset.sum_eq_single α]
      · rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw α)),
          if_pos rfl]
      · intro β _ hβ
        rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw β)),
          if_neg]
        exact fun h => hβ (DFunLike.coe_injective h).symm
      · intro hα
        rw [notMem_support_iff.mp hα]
        simp
    rw [hc, ← Ideal.Quotient.eq_zero_iff_mem, ← key, aeval_monomial] at hcomp
    rcases mul_eq_zero.mp hcomp with h | h
    · exact (map_eq_zero_iff _ (algebraMap F _).injective).mp h
    · exfalso
      rw [Finsupp.prod] at h
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h
      exact hi k (Ideal.Quotient.eq_zero_iff_mem.mp (pow_eq_zero_iff'.mp hk).1)
  have h1 := hind.lift_cardinalMk_le_trdeg
  simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_uzero] at h1
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F]
  have h2 : (Fintype.card K : ℕ∞) ≤ (Algebra.trdeg F (MRing ι F ⧸ P)).toENat :=
    Cardinal.natCast_le_toENat.mpr h1
  exact_mod_cast h2

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial Filter

noncomputable section

theorem totalDegree_bind₁_le_of_le_one {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by

  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem EventuallyPolyShift.proof : EventuallyPolyShift.Statement := by
  intro K _ h p c hp
  refine ⟨bind₁ (fun k => X k - C (c k : ℚ)) p, ?_, ?_, ?_⟩
  · have ht : Tendsto (fun m : K → ℤ => m + -c) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-c) tendsto_id
    refine (ht.eventually hp).mono fun m hm => ?_
    simp only [← sub_eq_add_neg] at hm
    have e := eval₂Hom_bind₁ (RingHom.id ℚ) (fun k => (m k : ℚ)) (fun k => X k - C (c k : ℚ)) p
    rw [hm]
    refine Eq.trans ?_ e.symm
    show eval _ p = eval _ p
    refine congrArg (fun x => eval x p) (funext fun k => ?_)
    simp
  · exact totalDegree_bind₁_le_of_le_one _
      (fun k => (totalDegree_sub_C_le _ _).trans (totalDegree_X k).le) p
  · rintro rfl
    exact map_zero _

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
