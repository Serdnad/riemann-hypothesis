module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle076
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle087
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle086
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle033
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

namespace GroundTheory.Heights₂.Heights

theorem IntegralIndep.closed : IntegralIndep.Statement :=
  IntegralIndep.proof
    (PosPartIndep.proof
      (SheetOnlyNull.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof)
      PosPartLocal.proof PosPartSplit.proof)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

attribute [local instance] twistMonoid

theorem InterSumTopVanish.proof (hM : MixedTwistShift.Statement.{u, w}) : InterSumTopVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L hW
  classical
  set L₀ : Fin n → LineBundle k x := fun j => L (Fin.castSucc j) with hL₀
  have hdim : ringKrullDim (Poly k N ⧸ pp) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := hW.dim.le
  have hA := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (L (Fin.last n)) 0
  have hB := hM k Ω N x n pp hW.isPrime hW.homog hW.le hdim L₀ (twistBundle k x 0) 0
  filter_upwards [hA, hB] with c hAc hBc
  have hL : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
      (fun j => (L₀ j).toSubSystem) (L (Fin.last n)).toSubSystem := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [hL₀]
  rw [interSum_eq_mixDiff, hL, mixDiff_snoc]
  have eA : mixDiff (fun g => restrLen pp (((L (Fin.last n)).toSubSystem * g).twist (twistSys k x (c : ℤ))))
      (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (L (Fin.last n)).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hc : (L (Fin.last n)).toSubSystem * ∏ j ∈ T, (L₀ j).toSubSystem =
        (∏ j ∈ T, (L₀ j).toSubSystem).twist (L (Fin.last n)).toSubSystem := SubSystem.twist_comm _ _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hc]
  have eB : mixDiff (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ)))) (fun j => (L₀ j).toSubSystem) =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen pp (((tensorSub (fun i => (L₀ i).toSubSystem) T).twist (twistBundle k x 0).toSubSystem).twist
          (twistSys k x ((c : ℤ) + 0))) := by
    unfold mixDiff
    refine Finset.sum_congr rfl fun T _ => ?_
    have hz : (∏ j ∈ T, (L₀ j).toSubSystem).twist (twistBundle k x 0).toSubSystem =
        ∏ j ∈ T, (L₀ j).toSubSystem := SubSystem.twist_twistSys_zero _
    rw [tensorSub_eq_prod, add_zero]
    beta_reduce
    rw [hz]
  rw [eA, eB, hAc, hBc, sub_self]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Finset

noncomputable section

theorem sum_subsets_neg_one_pow_prod_indicator (n : ℕ) (a : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, (if i ∈ T then (1 : ℚ) else 0) ^ a i =
      ∏ i, (1 - (0 : ℚ) ^ a i) := by
  have h := Finset.prod_add (fun _ : Fin n => (1 : ℚ)) (fun i => -((0 : ℚ) ^ a i)) univ
  simp only [← sub_eq_add_neg, powerset_univ, prod_const_one, one_mul] at h
  rw [h]
  refine sum_congr rfl fun T _ => ?_
  rw [prod_neg, ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin]
  congr 1
  rw [← prod_mul_prod_compl T]
  rw [prod_congr rfl (fun i hi => by rw [if_pos hi, one_pow]), prod_const_one, one_mul]
  exact prod_congr rfl fun i hi => by rw [if_neg (mem_compl.mp hi)]

theorem prod_snoc_snoc_pow (n : ℕ) (T : Finset (Fin n)) (m : ℕ) (c : ℤ) (e : Fin (n + 1 + 1) → ℕ) :
    ∏ j, (Fin.snoc (α := fun _ => ℚ)
        (fun j => ((Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m j : ℕ) : ℚ))
        (c : ℚ) j) ^ e j =
      (∏ i : Fin n, (if i ∈ T then (1 : ℚ) else 0) ^ e i.castSucc.castSucc) *
        (m : ℚ) ^ e (Fin.last n).castSucc * (c : ℚ) ^ e (Fin.last (n + 1)) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  congr 2
  refine prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem subsetDiff_eq_sum_support (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ)
    (Q : MvPolynomial (Fin (n + 1 + 1)) ℚ)
    (hf : ∀ (x : Fin (n + 1) → ℕ) (c : ℤ),
      f x c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (x j : ℚ)) (c : ℚ)) Q)
    (m : ℕ) (c : ℤ) :
    subsetDiff n f m c = ∑ e ∈ Q.support, Q.coeff e *
      ((∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) * (m : ℚ) ^ e (Fin.last n).castSucc *
        (c : ℚ) ^ e (Fin.last (n + 1))) := by
  unfold subsetDiff
  simp only [hf, eval_eq', prod_snoc_snoc_pow, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  have h := sum_subsets_neg_one_pow_prod_indicator n (fun i => e i.castSucc.castSucc)
  rw [← h, sum_mul, sum_mul, mul_sum]
  exact sum_congr rfl fun T _ => by ring

theorem sum_exponents_lt_of_mem_support {σ : Type*} [Fintype σ] {Q : MvPolynomial σ ℚ} {D : ℕ}
    (h : Q = 0 ∨ Q.totalDegree < D) {e : σ →₀ ℕ} (he : e ∈ Q.support) : ∑ j, e j < D := by
  rcases h with h | h
  · simp [h] at he
  · have := le_totalDegree he
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact lt_of_le_of_lt this h

theorem le_sum_of_prod_ne_zero (n : ℕ) (a : Fin n → ℕ) (h : (∏ i, (1 - (0 : ℚ) ^ a i)) ≠ 0) :
    n ≤ ∑ i, a i := by
  have hpos : ∀ i, 1 ≤ a i := fun i => by
    by_contra h0
    have h1 : a i = 0 := by omega
    exact h (prod_eq_zero (mem_univ i) (by rw [h1, pow_zero, sub_self]))
  calc n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i, a i := sum_le_sum fun i _ => hpos i

theorem SubsetDiffConst.proof : SubsetDiffConst.Statement := by
  intro n f ⟨Q, hQ, hf⟩
  have split : ∀ e : Fin (n + 1 + 1) →₀ ℕ, ∑ j, e j =
      ∑ i : Fin n, e i.castSucc.castSucc + e (Fin.last n).castSucc + e (Fin.last (n + 1)) := fun e => by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  refine ⟨fun m m' c c' => ?_, fun ⟨Q', hQ', hf'⟩ m c => ?_⟩
  · rw [subsetDiff_eq_sum_support n f Q hf, subsetDiff_eq_sum_support n f Q hf]
    refine sum_congr rfl fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ he
      rw [split] at h2
      have ha : e (Fin.last n).castSucc = 0 := by omega
      have hb : e (Fin.last (n + 1)) = 0 := by omega
      simp [ha, hb]
  · rw [subsetDiff_eq_sum_support n f Q' hf']
    refine sum_eq_zero fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ' he
      rw [split] at h2
      omega

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZTwist.proof_closed : VeryAmpleZTwist.Statement.{u, v, w} :=
  VeryAmpleZTwist.proof VeryAmpleZFamily.proof

end GroundTheory.Heights₂.Heights.Kleiman
end
