module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle001
public import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial FockH1Action

namespace PI.FJMF

def BlockAntitone : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 → (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b P = 0) →
    (∀ e ∈ P.support, ∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) → Antitone α

section Block

variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)

theorem bRow_apply' (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  simp [PI.FJM.bRow, LinearMap.sum_apply, Module.End.mul_apply]

theorem pd_X_mul [DecidableEq σ] (l v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv l (X v * Q) = X v * pderiv l Q + (if v = l then Q else 0) := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp

theorem sum_ite_row [DecidableEq σ] (hι : Function.Injective ι) (b : Fin m) (k : Fin n) (G : Fin n → MvPolynomial σ ℂ) :
    ∑ j : Fin n, (if ι (b, j) = ι (b, k) then G j else 0) = G k := by
  simp [hι.eq_iff]

theorem EF_expand (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) =
      (∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P))) +
        ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P := by
  classical
  rw [bRow_apply' ι a b, bRow_apply' ι b a]

  simp only [map_sum, pd_X_mul, Finset.sum_add_distrib, sum_ite_row ι hι, mul_add, Finset.mul_sum]

private theorem pderiv_pderiv_comm' {σ : Type} (i j : σ) (p : MvPolynomial σ ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  have h : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X, Derivation.zero_apply]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D => D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.1 this

theorem comm_eq (hι : Function.Injective ι) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b (PI.FJM.bRow ι b a P) - PI.FJM.bRow ι b a (PI.FJM.bRow ι a b P) =
      ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P - ∑ k : Fin n, X (ι (b, k)) * pderiv (ι (b, k)) P := by
  rw [EF_expand ι hι a b, EF_expand ι hι b a]
  have hS : (∑ k : Fin n, ∑ j : Fin n,
      X (ι (b, k)) * (X (ι (a, j)) * pderiv (ι (a, k)) (pderiv (ι (b, j)) P))) =
      ∑ k : Fin n, ∑ j : Fin n, X (ι (a, k)) * (X (ι (b, j)) * pderiv (ι (b, k)) (pderiv (ι (a, j)) P)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_pderiv_comm' (ι (a, j)) (ι (b, k)) P]
    ring
  rw [hS]
  abel

theorem euler_row (a : Fin m) (c : ℕ) (P : MvPolynomial σ ℂ)
    (hP : ∀ e ∈ P.support, ∑ k : Fin n, e (ι (a, k)) = c) :
    ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P = (c : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]

  simp only [map_sum, Finset.mul_sum, X_mul_pderiv_monomial]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_smul, hP e he]
  exact (Nat.cast_smul_eq_nsmul ℂ c _).symm

end Block

section Inner

variable {σ : Type}

theorem inner_zero_right (P : MvPolynomial σ ℂ) : fockInner P 0 = 0 := by
  unfold fockInner
  simp

theorem inner_sum_right {ι : Type*} (t : Finset ι) (P : MvPolynomial σ ℂ) (f : ι → MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, fockInner P (f i) := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, inner_zero_right]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_right, ih]

theorem inner_conj (P Q : MvPolynomial σ ℂ) : fockInner Q P = starRingEnd ℂ (fockInner P Q) := by
  classical

  rw [FockRaiseLowInner.fockInner_eq_sum_left Q P (P.support ∪ Q.support) Finset.subset_union_right,
  FockRaiseLowInner.fockInner_eq_sum_left P Q (P.support ∪ Q.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, FockRaiseLowInner.wt_conj]
  ring

theorem inner_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, FockRaiseLowInner.fockInner_zero_left]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_left, ih]

theorem inner_X_left (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (X l * P) Q = fockInner P (pderiv l Q) := by
  rw [inner_conj Q (X l * P), FockRaiseLowInner.fockInner_mul_X, inner_conj P (pderiv l Q), Complex.conj_conj]

theorem inner_pd_left (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (pderiv l P) Q = fockInner P (X l * Q) := by
  rw [inner_conj Q (pderiv l P), ← inner_X_left l Q P, inner_conj P (X l * Q), Complex.conj_conj]

end Inner

theorem bRow_adj {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (x y : MvPolynomial σ ℂ) :
    fockInner (PI.FJM.bRow ι b a x) y = fockInner x (PI.FJM.bRow ι a b y) := by
  rw [bRow_apply' ι b a x, bRow_apply' ι a b y, inner_sum_left, inner_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_X_left, inner_pd_left]

theorem block_degree_antitone : BlockAntitone := by
  intro σ m n ι hι α P hP hE hdeg a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hc := comm_eq ι hι a b P
    rw [hE a b h, map_zero, sub_zero, euler_row ι a (α a) P (fun e he => hdeg e he a),
      euler_row ι b (α b) P (fun e he => hdeg e he b)] at hc
    have hadj := bRow_adj ι a b P (PI.FJM.bRow ι b a P)
    rw [hc, ← sub_smul, FockRaiseLowInner.fockInner_smul_right] at hadj
    have h1 := PI.FockOneDegW.Inner.fockInner_self_re_nonneg (PI.FJM.bRow ι b a P)
    rw [hadj] at h1
    have hre := PI.FockOneDegW.Inner.fockInner_self_re_nonneg P
    have him := PI.FockOneDegW.Inner.fockInner_self_im P
    have hpos : 0 < (fockInner P P).re := lt_of_le_of_ne hre
      (fun h0 => hP (PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re P h0.symm))
    rw [Complex.mul_re, him, mul_zero, sub_zero] at h1
    simp only [Complex.sub_re, Complex.natCast_re] at h1
    have hlt : (α b : ℝ) ≤ α a := by nlinarith
    exact_mod_cast hlt

end PI.FJMF
end
end

section

noncomputable section

open MvPolynomial

namespace PI.FJMB

variable {σ : Type*}

theorem bRow_apply {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  rw [PI.FJM.bRow, LinearMap.sum_apply]; simp

theorem bCol_apply {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by
  rw [PI.FJM.bCol, LinearMap.sum_apply]; simp

theorem translate_pairs {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq σ] (u w : κ → σ)
    (_hw : Function.Injective w) (huw : ∀ k k', u k ≠ w k') (f : MvPolynomial σ R)
    (h : ∑ k, X (u k) * pderiv (w k) f = 0) {K : Type*} [Field K] [CharZero K] [Algebra R K] (y : σ → K) (t : K) :
    aeval (fun v => y v + t * ∑ k, if w k = v then y (u k) else 0) f = aeval y f := by
  classical
  refine aeval_translate_eq f (Finset.univ.image w) (fun v => ∑ k, if w k = v then X (u k) else 0) ?_ y
    (fun v => ∑ k, if w k = v then y (u k) else 0) ?_ ?_ t
  · calc ∑ v ∈ Finset.univ.image w, (∑ k, if w k = v then (X (u k) : MvPolynomial σ R) else 0) * pderiv v f
        = ∑ k, ∑ v ∈ Finset.univ.image w, if w k = v then X (u k) * pderiv v f else 0 := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
      _ = ∑ k, X (u k) * pderiv (w k) f := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_ite_eq]; simp
      _ = 0 := h
  · intro v hv
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have : w k ≠ v := fun e => hv (by rw [← e]; exact Finset.mem_image_of_mem w (Finset.mem_univ k))
    simp [this]
  · intro v _
    have hz : ∀ k, (∑ k', if w k' = u k then (Polynomial.C (y (u k')) : Polynomial K) else 0) = 0 :=
      fun k => Finset.sum_eq_zero (fun k' _ => by simp [Ne.symm (huw k k')])

    simp only [map_sum, apply_ite (aeval _), aeval_X, map_zero, apply_ite Polynomial.C]
    simp only [hz, mul_zero, add_zero]

def fill {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K) (p : σ → K) : σ → K :=
  Function.extend ι (fun x => M x.1 x.2) p

theorem fill_ι {K : Type*} {m n : ℕ} {ι : Fin m × Fin n → σ} (hι : Function.Injective ι) (M : Fin m → Fin n → K)
    (p : σ → K) (x : Fin m × Fin n) : fill ι M p (ι x) = M x.1 x.2 :=
  hι.extend_apply _ _ _

theorem fill_not {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K)
    (p : σ → K) (v : σ) (hv : ∀ x, ι x ≠ v) : fill ι M p v = p v :=
  Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hv x hx)

def rowAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (a b : Fin m) (t : K) : Fin m → Fin n → K :=
  fun i k => if i = b then M i k + t * M a k else M i k

def colAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (c d : Fin n) (t : K) : Fin m → Fin n → K :=
  fun i k => if k = d then M i k + t * M i c else M i k

theorem row_inv {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (a b : Fin m) (hab : a ≠ b)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bRow ι a b f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (rowAddM M a b t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun k : Fin n => ι (a, k)) (fun k => ι (b, k))
    (fun k k' e => by have := hι e; simp at this; exact this)
    (fun k k' e => hab (by have := hι e; simp at this; exact this.1)) f (by rw [← bRow_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [rowAddM]
    have hs : (∑ k', if ι (b, k') = ι (i, k) then fill ι M p (ι (a, k')) else 0) = if i = b then M a k else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hib : i = b
      · subst hib; simp
      · simp [Ne.symm hib, hib]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ k', if ι (b, k') = v then fill ι M p (ι (a, k')) else 0) = 0 :=
      Finset.sum_eq_zero (fun k' _ => by simp [hv (b, k')])
    rw [this, mul_zero, add_zero]

theorem col_inv {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (hcd : c ≠ d)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bCol ι c d f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (colAddM M c d t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun i : Fin m => ι (i, c)) (fun i => ι (i, d))
    (fun i i' e => by have := hι e; simp at this; exact this)
    (fun i i' e => hcd (by have := hι e; simp at this; exact this.2)) f (by rw [← bCol_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [colAddM]
    have hs : (∑ i', if ι (i', d) = ι (i, k) then fill ι M p (ι (i', c)) else 0) = if k = d then M i c else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hkd : k = d
      · subst hkd; simp
      · simp [Ne.symm hkd, hkd]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ i', if ι (i', d) = v then fill ι M p (ι (i', c)) else 0) = 0 :=
      Finset.sum_eq_zero (fun i' _ => by simp [hv (i', d)])
    rw [this, mul_zero, add_zero]

end PI.FJMB
end
end

section

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJM

def nP {n : ℕ} (f : Fin n → ℚ) : ℕ := (Finset.univ.filter fun i => 0 < f i).card

def nN {n : ℕ} (f : Fin n → ℚ) : ℕ := (Finset.univ.filter fun i => f i < 0).card

theorem nP_le_nW {n : ℕ} (f : Fin n → ℚ) : nP f ≤ n := by
  unfold nP
  exact (Finset.card_filter_le _ _).trans (Finset.card_fin n).le

theorem nN_le {n : ℕ} (f : Fin n → ℚ) : nN f ≤ n := by
  unfold nN
  exact (Finset.card_filter_le _ _).trans (Finset.card_fin n).le

section Blocks

variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)

def leftWeightFirst : Fin p → ℚ := fun i => nu1 p q r s μ (.inl i)
def leftWeightSecond : Fin q → ℚ := fun j => nu1 p q r s μ (.inr j)
def rightWeightFirst : Fin r → ℚ := fun k => nu2 p q r s μ' (.inl k)
def rightWeightSecond : Fin s → ℚ := fun l => nu2 p q r s μ' (.inr l)

def ιA : Fin (nP (leftWeightFirst p q r s μ)) × Fin (nP (rightWeightFirst p q r s μ')) → Ln p q r s := fun x =>
  (.inl (Fin.castLE (nP_le_nW _) x.1), .inl (Fin.castLE (nP_le_nW _) x.2))

def ιB : Fin (nN (leftWeightFirst p q r s μ)) × Fin (nN (rightWeightSecond p q r s μ')) → Ln p q r s := fun x =>
  (.inl (Fin.rev (Fin.castLE (nN_le _) x.1)), .inr (Fin.rev (Fin.castLE (nN_le _) x.2)))

def ιC : Fin (nP (leftWeightSecond p q r s μ)) × Fin (nP (rightWeightSecond p q r s μ')) → Ln p q r s := fun x =>
  (.inr (Fin.castLE (nP_le_nW _) x.1), .inr (Fin.castLE (nP_le_nW _) x.2))

def ιD : Fin (nN (leftWeightSecond p q r s μ)) × Fin (nN (rightWeightFirst p q r s μ')) → Ln p q r s := fun x =>
  (.inr (Fin.rev (Fin.castLE (nN_le _) x.1)), .inl (Fin.rev (Fin.castLE (nN_le _) x.2)))

def αA : Fin (nP (leftWeightFirst p q r s μ)) → ℕ := fun i => ⌊leftWeightFirst p q r s μ (Fin.castLE (nP_le_nW _) i)⌋₊
def βA : Fin (nP (rightWeightFirst p q r s μ')) → ℕ := fun k => ⌊rightWeightFirst p q r s μ' (Fin.castLE (nP_le_nW _) k)⌋₊
def αB : Fin (nN (leftWeightFirst p q r s μ)) → ℕ := fun i => ⌊-leftWeightFirst p q r s μ (Fin.rev (Fin.castLE (nN_le _) i))⌋₊
def βB : Fin (nN (rightWeightSecond p q r s μ')) → ℕ := fun l => ⌊-rightWeightSecond p q r s μ' (Fin.rev (Fin.castLE (nN_le _) l))⌋₊
def αC : Fin (nP (leftWeightSecond p q r s μ)) → ℕ := fun j => ⌊leftWeightSecond p q r s μ (Fin.castLE (nP_le_nW _) j)⌋₊
def βC : Fin (nP (rightWeightSecond p q r s μ')) → ℕ := fun l => ⌊rightWeightSecond p q r s μ' (Fin.castLE (nP_le_nW _) l)⌋₊
def αD : Fin (nN (leftWeightSecond p q r s μ)) → ℕ := fun j => ⌊-leftWeightSecond p q r s μ (Fin.rev (Fin.castLE (nN_le _) j))⌋₊
def βD : Fin (nN (rightWeightFirst p q r s μ')) → ℕ := fun k => ⌊-rightWeightFirst p q r s μ' (Fin.rev (Fin.castLE (nN_le _) k))⌋₊

def vLine : Pol p q r s :=
  shapeProd (Matrix.of fun i k => (X (ιA p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αA p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιB p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αB p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιC p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αC p q r s μ)) *
  shapeProd (Matrix.of fun i k => (X (ιD p q r s μ μ' (i, k)) : Pol p q r s)) (List.ofFn (αD p q r s μ))

end Blocks

def IsBlockHighestWeight {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ) (α : Fin m → ℕ) (β : Fin n → ℕ) (P : MvPolynomial σ ℂ) : Prop :=
  (∀ a b : Fin m, a < b → bRow ι a b P = 0) ∧ (∀ c d : Fin n, c < d → bCol ι c d P = 0) ∧
  (∀ e ∈ P.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k)) ∧
  (∀ i, 0 < α i) ∧ (∀ k, 0 < β k)

def HypA : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιA p q r s μ μ') (αA p q r s μ) (βA p q r s μ') P
def HypB : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιB p q r s μ μ') (αB p q r s μ) (βB p q r s μ') P
def HypC : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιC p q r s μ μ') (αC p q r s μ) (βC p q r s μ') P
def HypD : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  IsBlockHighestWeight (ιD p q r s μ μ') (αD p q r s μ) (βD p q r s μ') P

def CoverJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  ∀ e ∈ P.support, ∀ l : Ln p q r s, e l ≠ 0 →
    l ∈ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') ∪
      Set.range (ιD p q r s μ μ')

def SqFacts {m n : ℕ} (α : Fin m → ℕ) (β : Fin n → ℕ) : Prop :=
  m = n ∧ Antitone α ∧ ∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = β k

def BlockFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  SqFacts (αA p q r s μ) (βA p q r s μ') ∧ SqFacts (αB p q r s μ) (βB p q r s μ') ∧
  SqFacts (αC p q r s μ) (βC p q r s μ') ∧ SqFacts (αD p q r s μ) (βD p q r s μ')

def SegFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  (∀ i i' : Fin p, i < i' → 0 < nu1 p q r s μ (.inl i') → 0 < nu1 p q r s μ (.inl i)) ∧
  (∀ i i' : Fin p, i < i' → nu1 p q r s μ (.inl i) < 0 → nu1 p q r s μ (.inl i') < 0) ∧
  (∀ j j' : Fin q, j < j' → 0 < nu1 p q r s μ (.inr j') → 0 < nu1 p q r s μ (.inr j)) ∧
  (∀ j j' : Fin q, j < j' → nu1 p q r s μ (.inr j) < 0 → nu1 p q r s μ (.inr j') < 0) ∧
  (∀ k k' : Fin r, k < k' → 0 < nu2 p q r s μ' (.inl k') → 0 < nu2 p q r s μ' (.inl k)) ∧
  (∀ k k' : Fin r, k < k' → nu2 p q r s μ' (.inl k) < 0 → nu2 p q r s μ' (.inl k') < 0) ∧
  (∀ l l' : Fin s, l < l' → 0 < nu2 p q r s μ' (.inr l') → 0 < nu2 p q r s μ' (.inr l)) ∧
  (∀ l l' : Fin s, l < l' → nu2 p q r s μ' (.inr l) < 0 → nu2 p q r s μ' (.inr l') < 0)

def IntFacts (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Prop :=
  (∀ a, ((⌊nu1 p q r s μ a⌋ : ℤ) : ℚ) = nu1 p q r s μ a) ∧ (∀ c, ((⌊nu2 p q r s μ' c⌋ : ℤ) : ℚ) = nu2 p q r s μ' c)

def ShapeFromFacts : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  BlockFacts p q r s μ μ' → SegFacts p q r s μ μ' → IntFacts p q r s μ μ' → JointShape p q r s μ μ'

end PI.FJM
end
end
