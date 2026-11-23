module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle312
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CompactHarm

open MvPolynomial

theorem pd_comm {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
      intro a b
      rw [pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, h]
    ring

theorem pd_X_mul {σ : Type*} [DecidableEq σ] (x u : σ) (Q : MvPolynomial σ ℂ) :
    pderiv x (X u * Q) = (if u = x then Q else 0) + X u * pderiv x Q := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : u = x
  · subst h; simp only [Pi.single_eq_same, mul_one, if_true]; ring
  · simp only [Pi.single_apply, h, if_false, mul_zero, add_zero, zero_add]

theorem dd_X_mul {σ : Type*} [DecidableEq σ] (x y u : σ) (R : MvPolynomial σ ℂ) :
    pderiv x (pderiv y (X u * R)) = (if u = y then pderiv x R else 0) + (if u = x then pderiv y R else 0) +
      X u * pderiv x (pderiv y R) := by
  rw [pd_X_mul, map_add (f := _), pd_X_mul]
  split_ifs <;> (try simp only [map_zero]) <;> ring

theorem gen {σ : Type*} [DecidableEq σ] {n : ℕ} (x y u w : Fin n → σ) (P : MvPolynomial σ ℂ)
    (hxy : ∑ j, pderiv (x j) (pderiv (y j) P) = 0)
    (hA1 : ∑ j, ∑ k, (if u k = y j then pderiv (x j) (pderiv (w k) P) else 0) = 0)
    (hA2 : ∑ j, ∑ k, (if u k = x j then pderiv (y j) (pderiv (w k) P) else 0) = 0) :
    ∑ j, pderiv (x j) (pderiv (y j) (∑ k, X (u k) * pderiv (w k) P)) = 0 := by

  simp only [map_sum, dd_X_mul]
  simp only [Finset.sum_add_distrib]
  rw [hA1, hA2, zero_add, zero_add, Finset.sum_comm]
  have : ∀ k, ∑ j, X (u k) * pderiv (x j) (pderiv (y j) (pderiv (w k) P)) = 0 := by
    intro k
    rw [← Finset.mul_sum]
    simp only [pd_comm (y _) (w k), pd_comm (x _) (w k)]

    rw [← map_sum, hxy, map_zero, mul_zero]
  simp [this]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_single {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      ∑ j, (raiO τ (fun _ : Fin n => true) ε' i j * lowO τ (fun _ : Fin n => true) ε' l j) Q +
        (if i = l then ((n : ℂ) / 2) • Q else 0) := by
  classical
  unfold fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    congr 1
    split_ifs with h
    · simp only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_smul]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk
    rw [Finset.sum_eq_zero]
    intro l' _
    simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem low_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (hi : ε' i = false)
    (hl : ε' l = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      -∑ j, pderiv (τ, i, j) (pderiv (τ, l, j) Q) := by
  have hil : i ≠ l := fun e => by rw [e, hl] at hi; exact Bool.noConfusion hi
  rw [fockT_single, if_neg hil, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, hi, hl]

theorem up_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = true)
    (hb : ε' b = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      ∑ j, X (τ, a, j) * pderiv (τ, b, j) Q + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

theorem dn_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = false)
    (hb : ε' b = false) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      -∑ j, pderiv (τ, a, j) (X (τ, b, j) * Q) + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem fockT_compact_harm : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  classical
  intro D n m p P hP τ a b hab τ' i l hi hl
  have hL : ∀ (σ : D.what₂.Tau) (i l : Fin m), p σ ≤ (i : ℕ) → (l : ℕ) < p σ →
      ∑ j, pderiv (σ, i, j) (pderiv (σ, l, j) P) = 0 := by
    intro σ i l hi hl
    have := hP σ i l hi hl
    rw [low_eq σ _ i l (by simpa using hi) (by simpa using hl)] at this
    exact neg_eq_zero.1 this
  rw [low_eq τ' _ i l (by simpa using hi) (by simpa using hl), neg_eq_zero]
  let Lop : PolF D m n →ₗ[ℂ] PolF D m n :=
    ∑ j, (pderiv (τ', i, j)).toLinearMap ∘ₗ (pderiv (τ', l, j)).toLinearMap
  have hLop : ∀ Q, Lop Q = ∑ j, pderiv (τ', i, j) (pderiv (τ', l, j) Q) := by
    intro Q; simp [Lop, LinearMap.sum_apply]
  have hP0 : Lop P = 0 := by rw [hLop]; exact hL τ' i l hi hl
  have hite : ∀ (c : Prop) [Decidable c] (z : ℂ), Lop (if c then z • P else 0) = 0 := by
    intro c _ z; split_ifs <;> simp [hP0]
  rw [← hLop]
  by_cases ha : (a : ℕ) < p τ
  · have hb : (b : ℕ) < p τ := hab.1 ha
    rw [up_eq τ _ a b (by simpa using ha) (by simpa using hb), map_add (f := _), hite, add_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, a, k)) (fun k => (τ, b, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · by_cases h : τ = τ' ∧ a = l
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hL τ i b hi hb
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
  · have hb : ¬ (b : ℕ) < p τ := fun h => ha (hab.2 h)
    rw [dn_eq τ _ a b (by simpa using ha) (by simpa using hb)]
    have e : ∑ k, pderiv (τ, a, k) (X (τ, b, k) * P) =
        (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) + ∑ k, X (τ, b, k) * pderiv (τ, a, k) P := by
      simp only [pd_X_mul, Finset.sum_add_distrib]
    have hS1 : Lop (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) = 0 := by

      rw [map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs <;> simp [hP0]
    rw [e, map_add (f := _), map_neg, map_add (f := _), hS1, zero_add, hite, add_zero, neg_eq_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, b, k)) (fun k => (τ, a, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
    · by_cases h : τ = τ' ∧ b = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [pd_comm (τ, l, _) (τ, a, _)]
        exact hL τ a l (not_lt.1 ha) hl
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩

end GlobalTheory.CompactHarm
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.UnipKill

open Matrix

section General

variable {R S : Type} [CommRing R] [CommRing S] {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {N : ℕ}

theorem cornerGL_mem_unipRad (s : R →ₙ+* S) (e : (Σ a, m a) ≃ Fin N) {g : GL (Fin N) R}
    (hg : g ∈ unipRad R e) : cornerGL N s g ∈ unipRad S e := by
  rw [mem_unipRad] at hg ⊢
  have hval : ∀ i j, ((cornerGL N s g : GL (Fin N) S) : Matrix (Fin N) (Fin N) S) i j =
      (1 : Matrix (Fin N) (Fin N) S) i j - s ((1 : Matrix (Fin N) (Fin N) R) i j) +
        s ((g : Matrix (Fin N) (Fin N) R) i j) := fun i j => rfl
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [hval, mem_parab.1 hg.1 i j hij]
    simp [Matrix.one_apply_ne hne]
  · rw [hval, hg.2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
      simp [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]


omit [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
def tv {p q : Fin N} (hpq : p ≠ q) (c : R) : GL (Fin N) R :=
  ⟨transvection p q c, transvection p q (-c),
    (transvection_mul_transvection_same p q hpq c (-c)).trans (by rw [add_neg_cancel, transvection_zero]),
    (transvection_mul_transvection_same p q hpq (-c) c).trans (by rw [neg_add_cancel, transvection_zero])⟩


omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem ne_of_blk_lt (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) : p ≠ q := by
  rintro rfl; exact lt_irrefl _ hpq

theorem tv_mem_unipRad (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) (c : R) :
    tv (ne_of_blk_lt e hpq) c ∈ unipRad R e := by
  rw [mem_unipRad]
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    change (transvection p q c) i j = 0
    rw [transvection, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply]
    rw [if_neg, zero_add]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hpq hij
  · change (transvection p q c) (e ⟨a, i⟩) (e ⟨a, j⟩) = _
    rw [transvection, Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]
    · by_cases hij : i = j
      · subst hij; simp
      · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
        rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]
    · rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [h1]; simp
      have h2' : blk e q = a := by rw [h2]; simp
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq

end General

section Adelic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem toL_tv {p q : Fin N} (hpq : p ≠ q) (x : Cinf E) (t : ℝ) :
    toL ((tv hpq (t • x) : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) =
      oneL E N + t • toL (Matrix.single p q x) := by
  funext i j
  change (transvection p q (t • x)) i j = (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j + t • (Matrix.single p q x) i j
  rw [transvection, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem lieD_single_leviEmb {c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) {p q : Fin N}
    (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (x : Cinf E) (m : Levi (Ad E) fun i => Fin (n i)) :
    lieD (toL (Matrix.single p q x)) ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  set e := stdBlocks n h
  set g := leviEmb (Ad E) e m
  have hne := ne_of_blk_lt e hpq
  let u : ℝ → GL (Fin N) (Cinf E) := fun t => tv hne (t • x)
  have hu0 : u 0 = 1 := Units.ext (by
    show transvection p q ((0 : ℝ) • x) = 1
    rw [zero_smul, transvection_zero])
  have hline : HasDerivAt (fun t => toL (u t).val) (toL (Matrix.single p q x)) 0 := by
    have : (fun t => toL (u t).val) = fun t : ℝ => oneL E N + t • toL (Matrix.single p q x) :=
      funext fun t => toL_tv hne x t
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (Matrix.single p q x))).const_add (oneL E N)
  have hc := hasDerivAt_curve ψ g u (toL (Matrix.single p q x)) hu0 hline
  have hconst : (fun t => ψ.1 (g * infGL E N (u t))) = fun _ => ψ.1 g := by
    funext t
    have hv : infGL E N (u t) ∈ unipRad (Ad E) e := cornerGL_mem_unipRad (sInf E) e (tv_mem_unipRad e hpq _)
    have hw : g * infGL E N (u t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 hv
    rw [← hψ _ hw g, inv_mul_cancel_right]
  rw [hconst] at hc
  exact hc.unique (hasDerivAt_const 0 _)

end Adelic


open Complex in
theorem eop_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (ψ : Sm E N) (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g)
    (τ : E →+* ℂ) (p q : Fin N) (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (m) :
    (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  have key := fun x => lieD_single_leviEmb h ψ hψ hpq x m
  change ((1 / 2 : ℂ) • (lieS E N p q (atEmb τ 1) - Complex.I • lieS E N p q (atEmb τ Complex.I)) ψ).1 _ = 0
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_apply, CuspRep.lie_apply, key, smul_zero, sub_zero]

end GlobalTheory.UnipKill
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.UnipZero

theorem mem_unipRad_of_eq_one {R : Type} [CommRing R] {c N : ℕ} {n : Fin c → ℕ}
    {e : (Σ i, Fin (n i)) ≃ Fin N} {p q : Fin N} (hpq : blk e p < blk e q) (u : GL (Fin N) R)
    (hu : ∀ i j, ¬ (i = p ∧ j = q) → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j) :
    u ∈ unipRad R e := by
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : ¬ (i = p ∧ j = q) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hij hpq
    rw [hu i j hne, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  · have hne : ¬ (e ⟨a, i⟩ = p ∧ e ⟨a, j⟩ = q) := by
      rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [← h1, blk_apply]
      have h2' : blk e q = a := by rw [← h2, blk_apply]
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq
    rw [hu _ _ hne]
    simp [Matrix.one_apply, e.injective.eq_iff]

end GlobalTheory.UnipZero

namespace GlobalTheory.UnipZero

theorem lieD_single_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g) (p q : Fin N) (hpq : blk e p < blk e q)
    (x : Cinf E) (m : ∀ i, GA E (n i)) :
    (lie E N (toL (Matrix.single p q x)) ψ).1 (leviEmb (Ad E) e m) = 0 := by
  set S : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.single p q x with hS
  have hpq' : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
  have hSS : S * S = 0 := by rw [hS]; simp [hpq'.symm]
  let cc : ℝ → GL (Fin N) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by
      rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel, by
      rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel⟩
  have h0 : cc 0 = 1 := Units.ext (by simp [cc])
  have hc : HasDerivAt (fun t => toL (cc t).val) (toL S) 0 := by
    have h : HasDerivAt (fun t : ℝ => toL (1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • toL S) ((1 : ℝ) • toL S) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add _
    rw [one_smul] at h
    exact h
  set g := leviEmb (Ad E) e m
  have hmem : ∀ t, infGL E N (cc t) ∈ unipRad (Ad E) e := by
    intro t
    refine mem_unipRad_of_eq_one hpq _ fun i j hij => ?_
    have hij' : ((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j =
        (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j := by
      change ((1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • S) i j = _
      have h1 : S i j = 0 := by
        rw [hS, Matrix.single_apply_of_ne]
        exact fun h => hij ⟨h.1.symm, h.2.symm⟩
      rw [Matrix.add_apply, Matrix.smul_apply, h1, smul_zero, add_zero]
    change (1 : Matrix (Fin N) (Fin N) (Ad E)) i j - sInf E ((1 : Matrix (Fin N) (Fin N) (Cinf E)) i j) +
      sInf E (((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j) = _
    rw [hij', sub_add_cancel]
  have hconst : (fun t => ψ.1 (g * infGL E N (cc t))) = fun _ => ψ.1 g := by
    funext t
    have hconj : g * infGL E N (cc t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 (hmem t)
    have := hψ _ hconj g
    rwa [inv_mul_cancel_right] at this
  have hd := hasDerivAt_curve ψ g cc (toL S) h0 hc
  rw [hconst] at hd
  rw [lie_apply]
  exact hd.unique (hasDerivAt_const _ _)

end GlobalTheory.UnipZero
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.mem_smooth_of_chart_derivatives_at_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  first | exact @GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | exact GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt | (intros; apply GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem cocycle_dies_dR_of_dies_st : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (c : ↥(GK K) → V) (z : V ⊗[ℚ_[l]] Bst P), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b := by
  intro l _ P AI T K V _ _ ρ c z hz
  obtain ⟨ι, hC, hEq⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hst, -, hone⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hC hEq K V ρ
  refine ⟨LinearMap.lTensor V ι.toLinearMap z, fun g => ?_⟩
  rw [← hone (c g), hz g, map_sub, hst g z]

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem tilt_of_compatible_roots : ∀ (l : ℕ) [Fact l.Prime] (s : ℕ → OC l),
    (∀ n, s (n + 1) ^ l = s n) → ∃ y : OCb l, ∀ n, GlobalTheory.MemLoc.rootT y n = s n := by
  intro l _ s hs
  exact (GlobalTheory.MemLoc.tilt_facts l).1 s hs

end GlobalTheory
end
