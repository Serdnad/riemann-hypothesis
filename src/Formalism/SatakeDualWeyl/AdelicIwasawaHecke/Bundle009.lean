module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
public import Formalism.SatakeDualWeyl.StatementW
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaRed

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

def fIwasawaTri (r : ℕ) (M : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ i j : Fin n, j.val < r → j < i → M i j = 0

def fIwasawaKm (M : Matrix (Fin n) (Fin n) L) : Prop := fIwasawaUn σ M ∧ fIwasawaInt M

private theorem antiJ_apply_adelic_iwasawa_hecke (i j : Fin n) :
    antiJ L n i j = if (i : ℕ) + j + 1 = n then 1 else 0 := rfl

private theorem mul_antiJ_apply' (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (N * antiJ L n) i j = N i (Fin.rev j) := by
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · rw [antiJ_apply_adelic_iwasawa_hecke, if_pos (by rw [Fin.val_rev]; omega), mul_one]
  · intro k _ hk
    have hk' := k.isLt
    rw [antiJ_apply_adelic_iwasawa_hecke, if_neg, mul_zero]
    intro h
    apply hk
    ext
    rw [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem cT_apply_eq_sigma_transpose (N : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    cT σ N i j = σ (N j i) := rfl

private theorem cT_mul_reverse (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one_eq_one : cT σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  rw [cT_apply_eq_sigma_transpose]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]

theorem fIwasawa_Km_mul {A B : Matrix (Fin n) (Fin n) L} (hA : fIwasawaKm σ A) (hB : fIwasawaKm σ B) :
    fIwasawaKm σ (A * B) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt at *
  obtain ⟨hAu, hAi⟩ := hA
  obtain ⟨hBu, hBi⟩ := hB
  refine ⟨?_, fun i j => ?_⟩
  · calc cT σ (A * B) * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B := by
          rw [cT_mul_reverse]
          simp only [Matrix.mul_assoc]
      _ = antiJ L n := by rw [hAu, hBu]
  · rw [Matrix.mul_apply]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hAi i k) (hBi k j)

theorem fIwasawa_Km_one : fIwasawaKm σ (1 : Matrix (Fin n) (Fin n) L) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt
  refine ⟨by rw [cT_one_eq_one, Matrix.one_mul, Matrix.mul_one], fun i j => ?_⟩
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, map_zero]
    exact zero_le'

theorem fIwasawa_gram_un (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (a b : Fin n) :
    ∑ j, σ (M (Fin.rev j) a) * M j b = if b = Fin.rev a then 1 else 0 := by
  unfold fIwasawaUn at hM
  have h := congrFun (congrFun hM a) b
  rw [Matrix.mul_apply] at h
  simp only [mul_antiJ_apply', cT_apply_eq_sigma_transpose, antiJ_apply_adelic_iwasawa_hecke] at h
  rw [h]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : b = Fin.rev a
  · rw [if_pos, if_pos hab]
    rw [hab, Fin.val_rev]
    omega
  · rw [if_neg, if_neg hab]
    intro h'
    apply hab
    ext
    rw [Fin.val_rev]
    omega

private theorem sigma_diag_mul_rev_diag_and_rev_entries_zero (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (m : ℕ) : ∀ s : Fin n, s.val = m → s.val < r →
      σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
        ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s hsm hs
    have key : ∀ b : Fin n, b ≤ Fin.rev s →
        σ (M s s) * M (Fin.rev s) b = if b = Fin.rev s then 1 else 0 := by
      intro b hb
      rw [← fIwasawa_gram_un σ M hM s b, Finset.sum_eq_single (Fin.rev s)]
      · rw [Fin.rev_rev]
      · intro j _ hj
        have hne : Fin.rev j ≠ s := fun h => hj (by rw [← h, Fin.rev_rev])
        rcases lt_or_gt_of_ne hne with h | h
        · have hjs : (Fin.rev j).val < m := by
            rw [← hsm]
            exact h
          have hjr : (Fin.rev j).val < r := by omega
          have hjb : b < Fin.rev (Fin.rev j) := by
            have := b.isLt
            have := j.isLt
            have := s.isLt
            rw [Fin.rev_rev]
            rw [Fin.le_def, Fin.val_rev] at hb
            rw [Fin.lt_def, Fin.val_rev] at h
            rw [Fin.lt_def]
            omega
          have h0 := (ih _ hjs (Fin.rev j) rfl hjr).2 b hjb
          rw [Fin.rev_rev] at h0
          rw [h0, mul_zero]
        · rw [hT (Fin.rev j) s hs h, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h1 := key (Fin.rev s) le_rfl
    rw [if_pos rfl] at h1
    refine ⟨h1, fun b hb => ?_⟩
    have h2 := key b hb.le
    rw [if_neg (ne_of_lt hb)] at h2
    exact (mul_eq_zero.mp h2).resolve_left (left_ne_zero_of_mul_eq_one h1)

theorem fIwasawa_rows (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (s : Fin n) (hs : s.val < r) :
    σ (M s s) * M (Fin.rev s) (Fin.rev s) = 1 ∧
      ∀ b : Fin n, b < Fin.rev s → M (Fin.rev s) b = 0 := by
  exact sigma_diag_mul_rev_diag_and_rev_entries_zero σ M hM r hT s.val s rfl hs

theorem fIwasawa_col_zero (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ)
    (hT : fIwasawaTri r M) (ρ : Fin n) (hρr : ρ.val = r) (hρ : ρ < Fin.rev ρ) :
    ∀ i, Fin.rev ρ < i → M i ρ = 0 := by
  intro i hi
  have hi' := i.isLt
  have hρ' := ρ.isLt
  have hs : (Fin.rev i).val < r := by
    rw [Fin.val_rev, ← hρr]
    rw [Fin.lt_def, Fin.val_rev] at hi
    omega
  have h := (fIwasawa_rows σ M hM r hT (Fin.rev i) hs).2 ρ (by rw [Fin.rev_rev]; exact lt_trans hρ hi)
  rwa [Fin.rev_rev] at h

theorem fIwasawa_iso (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (ρ : Fin n)
    (hρ : ρ < Fin.rev ρ) : ∑ j, σ (M (Fin.rev j) ρ) * M j ρ = 0 := by
  rw [fIwasawa_gram_un σ M hM ρ ρ, if_neg (ne_of_lt hρ)]

theorem fIwasawa_perm (ρ a : Fin n) (hρ : ρ < Fin.rev ρ) (ha1 : ρ ≤ a) (ha2 : a ≤ Fin.rev ρ)
    (haa : a ≠ Fin.rev a) :
    ∃ π : Equiv.Perm (Fin n), π ρ = a ∧ (∀ i, π (Fin.rev i) = Fin.rev (π i)) ∧
      (∀ i, (i < ρ ∨ Fin.rev ρ < i) → π i = i) := by
  have hρn := ρ.isLt
  have han := a.isLt
  have haa' : a.val ≠ (Fin.rev a).val := fun h => haa (Fin.ext h)
  clear haa
  have harn := (Fin.rev a).isLt
  by_cases haρ : a = Fin.rev ρ
  · subst haρ
    refine ⟨Equiv.swap ρ (Fin.rev ρ), Equiv.swap_apply_left _ _, fun i => ?_, fun i hi => ?_⟩
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)
    · have hin := i.isLt
      simp only [Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)
  · refine ⟨Equiv.swap ρ a * Equiv.swap (Fin.rev ρ) (Fin.rev a), ?_, fun i => ?_, fun i hi => ?_⟩
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> (try simp only [not_true_eq_false] at *) <;> omega)
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)
    · have hin := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs <;> (simp only [Fin.rev_rev, Fin.ext_iff, Fin.val_rev, Fin.lt_def, Fin.le_def] at * <;> omega)

end FIwasawaRed

end Formalism.UG.P
end

section

noncomputable section

open MvPolynomial

namespace Formalism.UG.P

theorem wact_rowAct_mul (R : Type) [CommRing R] (r n : ℕ) (A B : Matrix (Fin r) (Fin r) R) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (A * B) = (Formalism.GradedWeylDivisibility.rowAct R (n := n) B).comp (Formalism.GradedWeylDivisibility.rowAct R A) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩

  simp only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
  Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  first
  | exact Finset.sum_comm
  | (rw [Finset.sum_comm])

theorem wact_rowAct_one (R : Type) [CommRing R] (r n : ℕ) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply, apply_ite C, ite_mul]

theorem dual_weyl_action_mul : Formalism.UG.DwActMul := by
  intro R _ r n g h
  refine ⟨?_, ?_⟩
  · simp only [Formalism.UG.dwAct]
    rw [mul_inv_rev, Units.val_mul, wact_rowAct_mul]
  · simp only [Formalism.UG.dwAct, inv_one, Units.val_one]
    exact wact_rowAct_one R r n

private theorem isWeightedHomogeneous_pow' {σ R M : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M}
    {φ : MvPolynomial σ R} {m : M} (h : IsWeightedHomogeneous w φ m) (k : ℕ) :
    IsWeightedHomogeneous w (φ ^ k) (k • m) := by
  induction k with
  | zero =>
    first
    | simpa using isWeightedHomogeneous_C w (1 : R)
    | simpa using isWeightedHomogeneous_one R w
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul h

private theorem isWeightedHomogeneous_algHom_apply {σ R M : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (hφ : ∀ v, IsWeightedHomogeneous w (φ (X v)) (w v)) (f : MvPolynomial σ R) (m : M)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (φ f) m := by

  rw [← mem_weightedHomogeneousSubmodule, f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hdw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  have hprod : IsWeightedHomogeneous w (φ (d.prod fun n e => X n ^ e)) (Finsupp.weight w d) := by
    rw [Finsupp.prod, map_prod, Finsupp.weight_apply, Finsupp.sum]
    apply IsWeightedHomogeneous.prod
    intro v _
    rw [map_pow]
    exact isWeightedHomogeneous_pow' (hφ v) (d v)
  have hC : φ (C (AddMonoidAlgebra.coeff f d)) = C (AddMonoidAlgebra.coeff f d) := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes _
  rw [monomial_eq, map_mul, hC, ← hdw, ← zero_add (Finsupp.weight w d)]
  exact (isWeightedHomogeneous_C w _).mul hprod

theorem dual_weyl_module_stable : Formalism.UG.DwStable := by
  intro R _ r n ν g f hf
  unfold Formalism.UG.dwAct
  generalize ((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = M
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  rw [Submodule.mem_inf] at hf ⊢
  obtain ⟨hw, hk⟩ := hf
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at hw ⊢
    apply isWeightedHomogeneous_algHom_apply _ _ _ f ν hw
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X]
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have h1 := (isWeightedHomogeneous_C (Formalism.GradedWeylDivisibility.colW r n) (M v.1 b)).mul
      (isWeightedHomogeneous_X R (Formalism.GradedWeylDivisibility.colW r n) (b, v.2))
    rw [zero_add] at h1
    exact h1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero] at hk ⊢
    intro l j hlj
    have h1 : (Formalism.GradedWeylDivisibility.colAddGen R (r := r) l j).comp (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) =
        (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none)
          (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp
          (Formalism.GradedWeylDivisibility.colAddGen R (r := r) l j) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, k⟩
      by_cases hkj : k = j
      · subst hkj

        simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, aeval_X, map_sum, map_mul,
        aeval_C, map_add, if_true, Option.elim, algebraMap_eq]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        ring
      · simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.colAddGen, hkj]
    have h2 : (aeval (fun o : Option (Fin r × Fin n) => o.elim (X none)
          (fun v => ∑ b : Fin r, C (M v.1 b) * X (some (b, v.2))))).comp
          (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp
          (Formalism.GradedWeylDivisibility.rowAct R (n := n) M) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, k⟩
      simp [Formalism.GradedWeylDivisibility.rowAct]
    have e1 := DFunLike.congr_fun h1 f
    have e2 := DFunLike.congr_fun h2 f
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, hk l j hlj, e2]

end Formalism.UG.P
end
end
