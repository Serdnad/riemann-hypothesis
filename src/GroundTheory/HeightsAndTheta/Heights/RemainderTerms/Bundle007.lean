module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle002
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

open Coinv

theorem CoinvStepReduction.proof : CoinvStepReduction.Statement := by
  classical
  intro K _ _ f n b k e he
  obtain ⟨c, hc⟩ := Coinv.exists_reduction (K := K) (f := f) (n := n) b k
  set φ : ↥(Finset.Ioi k) → Fin f × Fin n := fun s => (b, (s : Fin n)) with hφ
  have hinj : Function.Injective φ := fun s t h => Subtype.ext (Prod.ext_iff.mp h).2
  obtain ⟨e₀, rfl⟩ : ∃ e₀ : Fin f × Fin n →₀ ℕ, e = e₀ + Finsupp.single (b, k) ((k : ℕ) + 1) := by
    refine ⟨e - Finsupp.single (b, k) ((k : ℕ) + 1), ?_⟩
    ext u
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hu : u = (b, k)
    · subst hu; simp only [Finsupp.single_eq_same]; omega
    · simp [Ne.symm hu]
  set P : MvPolynomial (Fin f × Fin n) K := ∑ j ∈ range ((k : ℕ) + 1),
      monomial e₀ 1 * (rename φ (-c j) * X (b, k) ^ j) with hP
  refine ⟨P.support, fun e' => P.coeff e', ?_, ?_⟩
  · intro e' he'
    have h1 := support_sum he'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨j, hj, hj'⟩ := h1
    have h2 := support_mul _ _ hj'
    rw [Finset.mem_add] at h2
    obtain ⟨a, ha, d', hd', rfl⟩ := h2
    have ha' : a = e₀ := Finset.mem_singleton.mp (support_monomial_subset ha)
    have h3 := support_mul _ _ hd'
    rw [Finset.mem_add] at h3
    obtain ⟨d, hd, s, hs, rfl⟩ := h3
    rw [X_pow_eq_monomial] at hs
    have hs' : s = Finsupp.single (b, k) j := Finset.mem_singleton.mp (support_monomial_subset hs)
    rw [support_rename_of_injective hinj, Finset.mem_image] at hd
    obtain ⟨d₀, -, rfl⟩ := hd
    subst ha' hs'
    have hoff : ∀ u : Fin f × Fin n, (u.1 ≠ b ∨ u.2 ≤ k) → Finsupp.mapDomain φ d₀ u = 0 := by
      intro u hu
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨s, rfl⟩
      have hks : k < (s : Fin n) := Finset.mem_Ioi.mp s.2
      rcases hu with hu | hu
      · exact hu rfl
      · exact absurd hu (not_le.mpr hks)
    rw [Finset.mem_range] at hj
    refine ⟨fun u hu => ?_, ?_⟩
    · have hne : u ≠ (b, k) := by
        rintro rfl
        rcases hu with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
      have h0 := hoff u (by
        rcases hu with h | ⟨-, h⟩
        · exact Or.inl (ne_of_lt h)
        · exact Or.inr (le_of_lt h))
      simp [h0, Ne.symm hne]
    · have h0 := hoff (b, k) (Or.inr le_rfl)
      simp only [Finsupp.add_apply, h0, Finsupp.single_eq_same]
      omega
  · have hsum : ∑ e' ∈ P.support, P.coeff e' • monomial e' (1 : K) = P := by
      conv_rhs => rw [P.as_sum]
      refine Finset.sum_congr rfl fun e' _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum]
    have hm : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) =
        monomial e₀ 1 * X (b, k) ^ ((k : ℕ) + 1) := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have hdiff : monomial (e₀ + Finsupp.single (b, k) ((k : ℕ) + 1)) (1 : K) - P =
        monomial e₀ 1 * (X (b, k) ^ ((k : ℕ) + 1) +
          ∑ j ∈ range ((k : ℕ) + 1), rename φ (c j) * X (b, k) ^ j) := by
      rw [hm, hP, mul_add, Finset.mul_sum]
      simp only [map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
    rw [hdiff]
    exact Ideal.mul_mem_left _ _ hc

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Coinv

noncomputable section

theorem CoinvStaircaseComponent.proof (h1 : CoinvStaircaseDegree.Statement) :
    CoinvStaircaseComponent.Statement := by
  intro K _ f n v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have hhom : monomial e (1 : K) ∈ homogeneousSubmodule (Fin f × Fin n) K e.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    obtain ⟨hle, heq⟩ := h1 f n e he
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [homogeneousComponent_of_mem hhom, if_neg (by omega)]
    · rw [homogeneousComponent_of_mem hhom]
      by_cases h : coinvTop f n = e.degree
      · refine ⟨1, ?_⟩
        rw [if_pos h, heq h.symm, C_1, one_mul]
      · exact ⟨0, by rw [if_neg h, C_0, zero_mul]⟩
  | zero => exact ⟨fun d _ => map_zero _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    obtain ⟨hy1, cy, hy2⟩ := hy
    refine ⟨fun d hd => by rw [map_add (f := _), hx1 d hd, hy1 d hd, add_zero], cx + cy, ?_⟩
    rw [map_add (f := _), hx2, hy2, C_add, add_mul]
  | smul a x _ hx =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    refine ⟨fun d hd => by rw [map_smul, hx1 d hd, smul_zero], a * cx, ?_⟩
    rw [map_smul, hx2, smul_eq_C_mul, C_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAboveTopGeneral.proof (h1 : CoinvAboveTop.Statement) :
    CoinvAboveTopGeneral.Statement := by
  intro K _ _ β ι _ _ _ _ d H hH hd
  set eβ := Fintype.equivFin β
  set eι := Fintype.equivFin ι
  set ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι) := eβ.prodCongr eι with hψ
  obtain ⟨Q', hQ'h, hQ'⟩ := h1 K (Fintype.card β) (Fintype.card ι) d (rename ψ H)
    hH.rename_isHomogeneous hd
  refine ⟨fun m b => rename ψ.symm (Q' m (eβ b)),
    fun m b => (hQ'h m (eβ b)).rename_isHomogeneous, ?_⟩
  have hback : H = rename ψ.symm (rename ψ H) := by
    rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]

  rw [hback, hQ', map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_

  rw [map_sum, ← Equiv.sum_comp eβ.symm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [map_mul]
  simp only [Equiv.apply_symm_apply]
  congr 1

  rw [bps, map_sum, ← Equiv.sum_comp eι.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hψ]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvAtTop.proof (h1 : CoinvPolynomialReduction.Statement)
    (h2 : CoinvIdealComponent.Statement) (h3 : CoinvStaircaseComponent.Statement) :
    CoinvAtTop.Statement := by
  intro K _ _ f n H hH
  obtain ⟨v, hv, hJ⟩ := h1 K f n H
  obtain ⟨Q, -, hQ⟩ := h2 K f n (H - v) hJ (coinvTop f n)
  obtain ⟨-, c, hc⟩ := h3 K f n v hv
  refine ⟨c, ?_⟩
  have hcomp : H - C c * monomial (staircase f n) 1 =
      homogeneousComponent (coinvTop f n) (H - v) := by
    rw [map_sub, homogeneousComponent_eq_self hH, hc]
  rw [hcomp, hQ]
  refine Ideal.sum_mem _ fun m hm => Ideal.sum_mem _ fun b _ => ?_
  rw [Finset.mem_Icc] at hm
  exact Ideal.mul_mem_right _ _ (bps_mem_psumIdeal b hm.1 hm.2)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvMonomialReduction.proof (h1 : CoinvStepReduction.Statement) :
    CoinvMonomialReduction.Statement := by
  intro K _ _ f n e
  classical
  let r : Fin f × Fin n → Fin f × Fin n → Prop := fun u v => toLex u < toLex v
  have : IsStrictTotalOrder (Fin f × Fin n) r :=
    inferInstanceAs (IsStrictTotalOrder (Lex (Fin f × Fin n)) (· < ·))
  have wf : WellFounded
      (Finsupp.Lex r (· < ·) : (Fin f × Fin n →₀ ℕ) → (Fin f × Fin n →₀ ℕ) → Prop) :=
    Finsupp.Lex.wellFounded_of_finite r wellFounded_lt
  induction e using wf.induction with
  | _ e ih =>
  by_cases hu : IsUnderStaircase e
  · exact ⟨monomial e 1, Submodule.subset_span ⟨e, hu, rfl⟩, by simp⟩
  · simp only [IsUnderStaircase, not_forall, not_le] at hu
    obtain ⟨⟨b, k⟩, hbk⟩ := hu
    obtain ⟨T, c, hT, hmem⟩ := h1 K f n b k e (by simpa using hbk)
    have hlt : ∀ e' ∈ T, Finsupp.Lex r (· < ·) e' e := by
      intro e' he'
      refine Finsupp.lex_def.mpr ⟨(b, k), fun j hj => (hT e' he').1 j ?_, (hT e' he').2⟩
      exact Prod.Lex.toLex_lt_toLex.mp hj
    choose! w hw hwm using fun e' (he' : e' ∈ T) => ih e' (hlt e' he')
    refine ⟨∑ e' ∈ T, c e' • w e',
      Submodule.sum_mem _ fun e' he' => Submodule.smul_mem _ _ (hw e' he'), ?_⟩
    have hsplit : monomial e (1 : K) - ∑ e' ∈ T, c e' • w e' =
        (monomial e 1 - ∑ e' ∈ T, c e' • monomial e' 1) +
          ∑ e' ∈ T, C (c e') * (monomial e' 1 - w e') := by
      simp only [smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ hmem (Ideal.sum_mem _ fun e' he' => Ideal.mul_mem_left _ _ (hwm e' he'))

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvPolynomialReduction.proof (h1 : CoinvMonomialReduction.Statement) :
    CoinvPolynomialReduction.Statement := by
  intro K _ _ f n H
  choose v hv hvI using fun d => h1 K f n d
  refine ⟨∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hv d)
  · have e1 : H - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d := by
      rw [← H.as_sum]
    have e2 : (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        ∑ d ∈ H.support, C (AddMonoidAlgebra.coeff H d) * (monomial d (1 : K) - v d) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_sub, C_mul_monomial, mul_one, smul_eq_C_mul]
    rw [e1, e2]
    exact Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hvI d)

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

theorem Coinv.sum_staircase_exponents (f n : ℕ) :
    ∑ v : Fin f × Fin n, (v.2 : ℕ) = coinvTop f n := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rfl

theorem CoinvStaircaseDegree.proof : CoinvStaircaseDegree.Statement := by
  intro f n e he
  have hle : ∀ v ∈ (Finset.univ : Finset (Fin f × Fin n)), e v ≤ (v.2 : ℕ) := fun v _ => he v
  rw [Finsupp.degree_eq_sum, ← Coinv.sum_staircase_exponents f n]
  refine ⟨Finset.sum_le_sum hle, fun hEq => ?_⟩
  have hall := (Finset.sum_eq_sum_iff_of_le hle).1 hEq
  ext v
  simp [staircase, hall v (Finset.mem_univ v)]

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

theorem RestPolynomialDecomposes.proof (h1 : RestPolynomialHomogeneousDecomposition.Statement) :
    RestPolynomialDecomposes.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, -⟩ := h1 f r a c
  exact ⟨Q, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem choose_two_add (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by
  rw [← Finset.sum_range_id, ← Finset.sum_range_id, ← Finset.sum_range_id, Finset.sum_range_add,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

theorem RestPolynomialHomogeneous.proof (h1 : VandermondeOfHomogeneous.Statement) :
    RestPolynomialHomogeneous.Statement := by
  intro f r a c
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a) + 1)).mul hfib
  have hdeg : 1 * (f * (r * a) + 1) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) + 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem RestPolynomialHomogeneousDecomposition.proof (h1 : CoinvAboveTop.Statement)
    (h2 : RestPolynomialHomogeneous.Statement) :
    RestPolynomialHomogeneousDecomposition.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, hF⟩ := h1 ℚ f (r + a) (topDegree f (r + a) + 1) (restPolynomial f r a c)
    (h2 f r a c) (by unfold Coinv.coinvTop topDegree; omega)
  exact ⟨Q, hF, hQ⟩

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestPrimeBound.proof (h₁ : RestPrimeBoundOfFactor.Statement)
    (h₂ : SameFactorBound.Statement) (h₃ : OtherFactorBound.Statement) :
    RestPrimeBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  obtain ⟨_, hQex, hsame⟩ := h₂ f r a c hf hr ha
  obtain ⟨_, _, hother⟩ := h₃ f r a c hf hr ha
  refine ⟨hQex, ?_⟩
  intro Q hQ s e he p hp hBp
  refine h₁ f r a c B₀ hf hr ha hB Q ?_ s e he p hp hBp
  intro k hk2 hkN τ τ'
  by_cases h : τ' = τ
  · subst h
    exact hsame Q hQ k hk2 hkN τ'
  · exact (hother Q hQ k hk2 hkN τ τ' h).2

end RestTerms

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem RestKSumBound.proof : RestKSumBound.Statement := by
  intro p X N hp hX hXp
  obtain ⟨hsum, htsum, hexp⟩ := ExponentialTail.intersectionNumber_baseChange p X hp hX hXp
  set g : ℕ → ℝ := fun j => 2 * (p ^ (j + 2))⁻¹ * X ^ (j + 1) / ((j + 2).factorial : ℝ) with hg
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hre : ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) =
      ∑ j ∈ Finset.range (N + 1 - 2), g j := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    simp only
    rw [show 2 + j = j + 2 from Nat.add_comm 2 j, show j + 2 - 1 = j + 1 by omega]
  have hnn : ∀ j, 0 ≤ g j := fun j => by rw [hg]; positivity
  rw [hre]
  calc ∑ j ∈ Finset.range (N + 1 - 2), g j ≤ ∑' j, g j :=
        hsum.sum_le_tsum _ fun j _ => hnn j
    _ ≤ Real.exp (3 / 8) * X / p ^ 2 := htsum
    _ ≤ 1.5 * X / p ^ 2 := hexp

end

end RestTerms

end GroundTheory.Heights₂.Heights
end
