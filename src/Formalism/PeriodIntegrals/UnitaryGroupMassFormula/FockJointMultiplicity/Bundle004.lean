module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurCauchy
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PosIffLtNP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LeadTDerCols
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.MemLeftHighestWeightOfIsMinimalJointVector
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMS

open PI.FJM PI.FJMP

theorem pos_of_sign {x : ℚ} {b : Bool} (hb : b = true) (h : b = true ↔ 0 < x) : 0 < x := h.mp hb

theorem neg_of_sign {x : ℚ} {b : Bool} (hb : b = false) (h0 : x ≠ 0) (h : b = true ↔ 0 < x) : x < 0 := by
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · exact hlt
  · exact absurd (h.mpr hgt) (by rw [hb]; decide)

theorem segs_of {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : SegFacts p q r s μ μ' :=
  segJ_of leftDiagonalActionFormula rightDiagonalActionFormula leftOffDiagonalActionFormula rightOffDiagonalActionFormula p q r s μ μ' P hM

theorem hypothesis_first_cover : HypA := by
  intro p q r s μ μ' P hM
  obtain ⟨sL1p, -, -, -, sL2p, -, -, -⟩ := segs_of hM
  refine blkHyp_pos hM (fun i => (Sum.inl (Fin.castLE (nP_le_nW _) i) : Ix p q))
    (fun k => (Sum.inl (Fin.castLE (nP_le_nW _) k) : Ix r s))
    (Sum.inl_injective.comp (Fin.castLE_injective _)) (Sum.inl_injective.comp (Fin.castLE_injective _))
    (fun a b h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun c d h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => pos_of_lt (leftWeightFirst p q r s μ) sL1p i) (fun k => pos_of_lt (rightWeightFirst p q r s μ') sL2p k)
    _ _ (fun i => rfl) (fun k => rfl)
  · cases c with
    | inl c =>
      obtain ⟨x, hx⟩ := idxP (rightWeightFirst p q r s μ') sL2p c h2
      exact ⟨x, by simp only [hx]⟩
    | inr c => simp [linePos] at h1
  · cases a with
    | inl a =>
      obtain ⟨x, hx⟩ := idxP (leftWeightFirst p q r s μ) sL1p a h2
      exact ⟨x, by simp only [hx]⟩
    | inr a => simp [linePos] at h1

theorem hypothesis_third_cover : HypC := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, sR1p, -, -, -, sR2p, -⟩ := segs_of hM
  refine blkHyp_pos hM (fun i => (Sum.inr (Fin.castLE (nP_le_nW _) i) : Ix p q))
    (fun k => (Sum.inr (Fin.castLE (nP_le_nW _) k) : Ix r s))
    (Sum.inr_injective.comp (Fin.castLE_injective _)) (Sum.inr_injective.comp (Fin.castLE_injective _))
    (fun a b h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun c d h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => pos_of_lt (leftWeightSecond p q r s μ) sR1p i) (fun k => pos_of_lt (rightWeightSecond p q r s μ') sR2p k)
    _ _ (fun i => rfl) (fun k => rfl)
  · cases c with
    | inl c => simp [linePos] at h1
    | inr c =>
      obtain ⟨x, hx⟩ := idxP (rightWeightSecond p q r s μ') sR2p c h2
      exact ⟨x, by simp only [hx]⟩
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxP (leftWeightSecond p q r s μ) sR1p a h2
      exact ⟨x, by simp only [hx]⟩

theorem hypothesis_second_cover : HypB := by
  intro p q r s μ μ' P hM
  obtain ⟨-, sL1n, -, -, -, -, -, sR2n⟩ := segs_of hM
  refine blkHyp_neg hM (fun i => (Sum.inl (Fin.rev (Fin.castLE (nN_le _) i)) : Ix p q))
    (fun k => (Sum.inr (Fin.rev (Fin.castLE (nN_le _) k)) : Ix r s))
    (Sum.inl_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (Sum.inr_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (fun a b h => ?_) (fun c d h => ?_)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => neg_of_lt (leftWeightFirst p q r s μ) sL1n i) (fun k => neg_of_lt (rightWeightSecond p q r s μ') sR2n k)
    _ _ (fun i => rfl) (fun k => rfl)
  · have h' : a.val < b.val := h
    have := b.isLt
    have := nN_le (leftWeightFirst p q r s μ)
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · have h' : c.val < d.val := h
    have := d.isLt
    have := nN_le (rightWeightSecond p q r s μ')
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · cases c with
    | inl c => simp [linePos] at h1
    | inr c =>
      obtain ⟨x, hx⟩ := idxN (rightWeightSecond p q r s μ') sR2n c h2
      exact ⟨x, by simp only [hx]⟩
  · cases a with
    | inl a =>
      obtain ⟨x, hx⟩ := idxN (leftWeightFirst p q r s μ) sL1n a h2
      exact ⟨x, by simp only [hx]⟩
    | inr a => simp [linePos] at h1

theorem hypothesis_fourth_cover : HypD := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, -, sR1n, -, sL2n, -, -⟩ := segs_of hM
  refine blkHyp_neg hM (fun i => (Sum.inr (Fin.rev (Fin.castLE (nN_le _) i)) : Ix p q))
    (fun k => (Sum.inl (Fin.rev (Fin.castLE (nN_le _) k)) : Ix r s))
    (Sum.inr_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (Sum.inl_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (fun a b h => ?_) (fun c d h => ?_)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => neg_of_lt (leftWeightSecond p q r s μ) sR1n i) (fun k => neg_of_lt (rightWeightFirst p q r s μ') sL2n k)
    _ _ (fun i => rfl) (fun k => rfl)
  · have h' : a.val < b.val := h
    have := b.isLt
    have := nN_le (leftWeightSecond p q r s μ)
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · have h' : c.val < d.val := h
    have := d.isLt
    have := nN_le (rightWeightFirst p q r s μ')
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · cases c with
    | inl c =>
      obtain ⟨x, hx⟩ := idxN (rightWeightFirst p q r s μ') sL2n c h2
      exact ⟨x, by simp only [hx]⟩
    | inr c => simp [linePos] at h1
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxN (leftWeightSecond p q r s μ) sR1n a h2
      exact ⟨x, by simp only [hx]⟩

theorem cover_by_blocks : CoverJ := by
  intro p q r s μ μ' P hM e he l hl
  obtain ⟨sL1p, sL1n, sR1p, sR1n, sL2p, sL2n, sR2p, sR2n⟩ := segs_of hM
  obtain ⟨h1, h2, h3, h4⟩ := pure_of hM he hl
  rcases l with ⟨a | a, c | c⟩
  · obtain ⟨x, hx⟩ := idxP (leftWeightFirst p q r s μ) sL1p a (pos_of_sign rfl h3)
    obtain ⟨y, hy⟩ := idxP (rightWeightFirst p q r s μ') sL2p c (pos_of_sign rfl h4)
    exact Or.inl (Or.inl (Or.inl ⟨(x, y), by simp only [ιA, hx, hy]⟩))
  · obtain ⟨x, hx⟩ := idxN (leftWeightFirst p q r s μ) sL1n a (neg_of_sign rfl h1 h3)
    obtain ⟨y, hy⟩ := idxN (rightWeightSecond p q r s μ') sR2n c (neg_of_sign rfl h2 h4)
    exact Or.inl (Or.inl (Or.inr ⟨(x, y), by simp only [ιB, hx, hy]⟩))
  · obtain ⟨x, hx⟩ := idxN (leftWeightSecond p q r s μ) sR1n a (neg_of_sign rfl h1 h3)
    obtain ⟨y, hy⟩ := idxN (rightWeightFirst p q r s μ') sL2n c (neg_of_sign rfl h2 h4)
    exact Or.inr ⟨(x, y), by simp only [ιD, hx, hy]⟩
  · obtain ⟨x, hx⟩ := idxP (leftWeightSecond p q r s μ) sR1p a (pos_of_sign rfl h3)
    obtain ⟨y, hy⟩ := idxP (rightWeightSecond p q r s μ') sR2p c (pos_of_sign rfl h4)
    exact Or.inl (Or.inr ⟨(x, y), by simp only [ιC, hx, hy]⟩)

theorem intFacts_of {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : IntFacts p q r s μ μ' := by
  obtain ⟨e0, he0⟩ := exists_mem_support hM.2.1
  refine ⟨fun a => ?_, fun c => ?_⟩
  · rw [← monomialLeftWeight_eq_weight_sub leftDiagonalActionFormula (mem_leftHighestWeight_of_isMinimalJointVector hM) e0 he0 a, Int.floor_intCast]
  · rw [← monomialRightWeight_eq_weight_sub rightDiagonalActionFormula (mem_rightHighestWeight_of_isMinimalJointVector hM) e0 he0 c, Int.floor_intCast]

end PI.FJMS
end
end

section

noncomputable section

open MvPolynomial Classical

namespace PI.FJMB

variable {σ : Type*}

theorem cd_mono_factor {m : ℕ} (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (e : σ →₀ ℕ) :
    aeval (killS (offD ι)) (monomial e (1 : ℂ)) =
      (∏ i, X (ι (i, i)) ^ (∑ k : Fin m, e (ι (i, k)))) * aeval (diagOne' ι) (monomial e (1 : ℂ)) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, map_one, one_mul, one_mul]
  by_cases hoff : ∃ v ∈ e.support, v ∈ offD ι
  · obtain ⟨v, hv, hvo⟩ := hoff
    have h1 : (e.prod fun v k => killS (offD ι) v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [killS, if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    have h2 : (e.prod fun v k => diagOne' ι v ^ k) = 0 := by
      refine Finset.prod_eq_zero hv ?_
      simp only [diagOne', if_pos hvo]
      exact zero_pow (Finsupp.mem_support_iff.mp hv)
    rw [h1, h2, mul_zero]
  · push_neg at hoff
    have hsum : ∀ i, ∑ k : Fin m, e (ι (i, k)) = e (ι (i, i)) := by
      intro i
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        by_contra hne
        exact hoff (ι (i, k)) (Finsupp.mem_support_iff.mpr hne) ⟨i, k, rfl, fun h => hk (Fin.ext h).symm⟩
      · intro h
        exact absurd (Finset.mem_univ i) h
    simp only [hsum]
    have hL : (e.prod fun v k => killS (offD ι) v ^ k) = ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [killS, if_neg (hoff v hv)]
    have hR : (e.prod fun v k => diagOne' ι v ^ k) =
        ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      unfold Finsupp.prod
      refine Finset.prod_congr rfl fun v hv => ?_
      simp only [diagOne', if_neg (hoff v hv)]
      split_ifs <;> simp
    have hsplit : ∏ v ∈ e.support, (X v : MvPolynomial σ ℂ) ^ e v =
        (∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1) *
          ∏ v ∈ e.support, (if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then 1 else (X v : MvPolynomial σ ℂ) ^ e v) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      split_ifs <;> simp
    have hF : ∏ v ∈ e.support.filter (fun v => ∃ i k, ι (i, k) = v ∧ (i : ℕ) = k), (X v : MvPolynomial σ ℂ) ^ e v =
        ∏ v ∈ e.support, if (∃ i k, ι (i, k) = v ∧ (i : ℕ) = k) then (X v : MvPolynomial σ ℂ) ^ e v else 1 := by
      rw [Finset.prod_filter]
    have hinj : Function.Injective (fun i : Fin m => ι (i, i)) := fun a b h => (Prod.mk.inj (hι h)).1
    have himg : ∏ i, (X (ι (i, i)) : MvPolynomial σ ℂ) ^ e (ι (i, i)) =
        ∏ v ∈ Finset.univ.image (fun i : Fin m => ι (i, i)), (X v : MvPolynomial σ ℂ) ^ e v := by
      rw [Finset.prod_image (fun a _ b _ h => hinj h)]
    rw [hL, hR, hsplit, ← hF, himg]
    congr 1
    apply Finset.prod_subset
    · intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨i, k, hik, hk⟩ := hv.2
      rw [Finset.mem_image]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [← hik, ← Fin.ext hk]
    · intro v hv hvf
      rw [Finset.mem_image] at hv
      obtain ⟨i, _, rfl⟩ := hv
      have h0 : e (ι (i, i)) = 0 := by
        by_contra hne
        exact hvf (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, i, i, rfl, rfl⟩)
      rw [h0, pow_zero]

theorem diagonal_hypothesis : HypDiag := by
  intro σ m ι hι α P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hm : MvPolynomial.monomial e (P.coeff e) = MvPolynomial.C (P.coeff e) * MvPolynomial.monomial e 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hm, map_mul, map_mul, cd_mono_factor ι hι e]
  have hs : ∀ i, ∑ k : Fin m, e (ι (i, k)) = α i := hP e he
  simp only [hs, MvPolynomial.aeval_C]
  ring

theorem diagonal_image_block_free : HypFree := by
  intro σ m n ι hι P
  have hC : ∀ c : ℂ, ∀ e ∈ (MvPolynomial.C c : MvPolynomial σ ℂ).support, ∀ x, e (ι x) = 0 := by
    intro c e he x
    rw [MvPolynomial.C_apply] at he
    have h0 := MvPolynomial.support_monomial_subset he
    rw [Finset.mem_singleton] at h0
    rw [h0]
    rfl
  have hadd : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q + R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact hQ e h x
    · exact hR e h x
  have hmul : ∀ Q R : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) →
      (∀ e ∈ R.support, ∀ x, e (ι x) = 0) → ∀ e ∈ (Q * R).support, ∀ x, e (ι x) = 0 := by
    intro Q R hQ hR e he x
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul Q R he)
    rw [Finsupp.add_apply, hQ a ha x, hR b hb x]
  have hgen : ∀ w, ∀ e ∈ (diagOne' ι w).support, ∀ x, e (ι x) = 0 := by
    intro w
    unfold diagOne'
    split_ifs with h1 h2
    · simpa using hC 0
    · simpa using hC 1
    · intro e he x
      have hne : w ≠ ι x := by
        rintro rfl
        obtain ⟨i, k⟩ := x
        by_cases hik : (i : ℕ) = k
        · exact h2 ⟨i, k, rfl, hik⟩
        · exact h1 ⟨i, k, rfl, hik⟩
      rw [MvPolynomial.support_X, Finset.mem_singleton] at he
      rw [he, Finsupp.single_apply, if_neg hne]
  induction P using MvPolynomial.induction_on
  next a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    exact hC a
  next p q hp hq =>
    rw [map_add (f := _)]
    exact hadd _ _ hp hq
  next p w hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact hmul _ _ hp (hgen w)

end PI.FJMB
end
end

section

namespace PI.FJMB

theorem cauchy_highest_weight_of_shape (hS : HypShape) (hD : HypDiag) (hF : HypFree) : PI.FJM.CauchyHW := by
  refine cauchyHW_of ?_ hS hD hF
  intro σ m n ι hι α P hP hrow hdeg
  exact PI.FJMF.block_degree_antitone σ m n ι hι α P hP hrow hdeg

end PI.FJMB
end

section

namespace PI.FJMX

theorem minorProductDiagonal : PI.FJMB.HypShape := fun _ _ ι hι α hα =>
  ⟨shapeProd_hwb ι hι _, shapeProd_diag ι hι α hα⟩

end PI.FJMX
end
