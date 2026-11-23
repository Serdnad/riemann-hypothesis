module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

section
end

section
end

section
end

section
end

section
end

section
end

section
end

section

namespace GlobalTheory.SplittingAdditive

open BigOperators

def Splits {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (p : G → ℂ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
    (∀ i : Fin m, a i ∈ A ∧ b i ∈ A) ∧ ∀ x k : G, p (x * k) = ∑ i : Fin m, a i x * b i k

theorem splits_add {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p + q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  refine ⟨m + n, Fin.append a c, Fin.append b d, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hab j
    · simpa using hcd j
  · intro x k
    rw [Fin.sum_univ_add]
    simp [h, h']

theorem splits_mul {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p * q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  refine ⟨m * n, fun j => a (e.symm j).1 * c (e.symm j).2,
    fun j => b (e.symm j).1 * d (e.symm j).2, ?_, ?_⟩
  · intro j
    exact ⟨A.mul_mem (hab _).1 (hcd _).1, A.mul_mem (hab _).2 (hcd _).2⟩
  · intro x k
    have key : ∀ f : Fin m × Fin n → ℂ, ∑ j : Fin (m * n), f (e.symm j) = ∑ q, f q :=
      fun f => Equiv.sum_comp e.symm f
    simp only [Pi.mul_apply]
    rw [key (fun q => a q.1 x * c q.2 x * (b q.1 k * d q.2 k)), h, h', Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring

theorem splits_algebraMap {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (r : ℂ) :
    Splits A (algebraMap ℂ (G → ℂ) r) := by
  refine ⟨1, fun _ => algebraMap ℂ (G → ℂ) r, fun _ => 1, ?_, ?_⟩
  · intro _
    exact ⟨A.algebraMap_mem r, A.one_mem⟩
  · intro x k
    simp

theorem main :
    ∀ {G : Type} [inst : Mul G] (S : Set (G → ℂ)),
      (∀ p ∈ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k) →
      ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k := by
  intro G _ S hS p hp
  change Splits (Algebra.adjoin ℂ S) p
  induction hp using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap r => exact splits_algebraMap _ r
  | add x y _ _ hx hy => exact splits_add _ hx hy
  | mul x y _ _ hx hy => exact splits_mul _ hx hy

end GlobalTheory.SplittingAdditive
end

section

namespace GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable

theorem finsum_quot_eq {V K : Type} [AddCommGroup V] [Field K] (f : V → K) (M N : AddSubgroup V)
    (S : Finset V) (hMN : M ≤ N) (hidx : M.relIndex N ≠ 0)
    (hf : ∀ v, ∀ u ∈ N, f (v + u) = f v)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) :
    ∑ᶠ c : V ⧸ M, f c.out = (M.relIndex N : K) * ∑ s ∈ S, f s := by
  classical
  haveI : Finite (N ⧸ M.addSubgroupOf N) := Nat.finite_of_card_ne_zero hidx
  letI : Fintype (N ⧸ M.addSubgroupOf N) := Fintype.ofFinite _
  let φ : V × (N ⧸ M.addSubgroupOf N) → V ⧸ M :=
    fun p => QuotientAddGroup.mk (p.1 + ((p.2.out : N) : V))
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := by
    intro v
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    have := hf v _ (hMN h)
    simpa using this
  rw [finsum_eq_sum_of_support_subset (s := (S ×ˢ Finset.univ).image φ)]
  · rw [Finset.sum_image]
    · rw [Finset.sum_product]
      have : ∀ s ∈ S, ∑ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = (M.relIndex N : K) * f s := by
        intro s _
        have : ∀ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = f s := by
          intro q
          simp only [φ]
          rw [hout, hf _ _ (q.out).2]
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card]
        rfl
      rw [Finset.sum_congr rfl this, Finset.mul_sum]
    · rintro ⟨s, q⟩ hp ⟨s', q'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
      simp only [φ, QuotientAddGroup.eq] at h
      have hs : s = s' := by
        apply hinj s hp.1 s' hp'.1
        have h1 := N.add_mem (N.sub_mem (q'.out).2 (q.out).2) (N.neg_mem (hMN h))
        convert h1 using 1
        abel
      subst hs
      have hq : q = q' := by
        rw [← Quotient.out_eq q, ← Quotient.out_eq q']
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_addSubgroupOf]
        convert h using 1
        push_cast
        abel
      rw [hq]
  · intro c hc
    obtain ⟨s, hs, hn⟩ := hcov c.out hc
    simp only [Finset.coe_image, Set.mem_image]
    refine ⟨(s, QuotientAddGroup.mk ⟨c.out - s, hn⟩), by simp [hs], ?_⟩
    have h : -(QuotientAddGroup.mk (⟨c.out - s, hn⟩ : N) : N ⧸ M.addSubgroupOf N).out
        + (⟨c.out - s, hn⟩ : N) ∈ M.addSubgroupOf N := by
      rw [← QuotientAddGroup.eq]; simp
    rw [AddSubgroup.mem_addSubgroupOf] at h
    conv_rhs => rw [← Quotient.out_eq c]
    apply QuotientAddGroup.eq.2
    convert h using 1
    push_cast
    abel

theorem sum_reps_ne_zero_iff : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by
  intro V K _ _ _ f N N' S S' h1 h2 hf hf' hi hc hi' hc'
  have e1 : (N ⊓ N').relIndex N ≠ 0 := by rwa [AddSubgroup.inf_relIndex_left]
  have e2 : (N ⊓ N').relIndex N' ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have a := finsum_quot_eq f (N ⊓ N') N S inf_le_left e1 hf hi hc
  have b := finsum_quot_eq f (N ⊓ N') N' S' inf_le_right e2 hf' hi' hc'
  have c1 : (((N ⊓ N').relIndex N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e1
  have c2 : (((N ⊓ N').relIndex N' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e2
  rw [← mul_ne_zero_iff_left c1, ← a, b, mul_ne_zero_iff_left c2]

end GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
end

section

namespace GlobalTheory.PeriodicSumShift

theorem periodic_shift {K : Type} (g : ℕ → K) (N : ℕ) (h : ∀ i, g (N + i) = g i) :
    ∀ k i, g (N * k + i) = g i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih => intro i; rw [Nat.mul_succ, add_assoc, ih, h]

theorem sum_range_mul_of_periodic : ∀ {K : Type} [inst : Field K] (g : ℕ → K) (N : ℕ),
    (∀ (i : ℕ), g (N + i) = g i) → ∀ (k : ℕ),
      ∑ i ∈ Finset.range (N * k), g i = (↑k : K) * ∑ i ∈ Finset.range N, g i := by
  intro K _ g N h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [periodic_shift g N h k]
    push_cast; ring

end GlobalTheory.PeriodicSumShift
end

section

namespace GlobalTheory

open Finset

theorem sum_piFinset_fin_succ_cons {α K : Type} [AddCommMonoid K] (n : ℕ) (S : Finset α)
    (F : (Fin (n + 1) → α) → K) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F t =
      ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
  rw [← Finset.sum_product' S (Fintype.piFinset (fun _ : Fin n => S))
    (fun a t => F (Fin.cons a t))]
  symm
  refine Finset.sum_equiv (Fin.consEquiv (fun _ => α)) ?_ ?_
  · rintro ⟨a, t⟩
    simp [Fin.forall_fin_succ, Fin.consEquiv]
  · rintro ⟨a, t⟩ _
    rfl

theorem weighted_sum_piFinset_fin {α K : Type} [CommRing K] (G : (α → K) → Prop)
    (S S' : Finset α) (w w' : K)
    (h : ∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) (n : ℕ) :
    ∀ F : (Fin n → α) → K, (∀ (t : Fin n → α) (i : Fin n), G (fun a => F (Function.update t i a))) →
      w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F t =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F t := by
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
    intro F hF
    have h1 : ∀ a : α, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
      intro a
      refine ih (fun t => F (Fin.cons a t)) ?_
      intro t i
      have := hF (Fin.cons a t) i.succ
      simpa only [← Fin.cons_update] using this
    have h2 : ∀ t : Fin n → α, w * ∑ a ∈ S, F (Fin.cons a t) =
        w' * ∑ a ∈ S', F (Fin.cons a t) := by
      intro t
      rcases isEmpty_or_nonempty α with hα | ⟨⟨a0⟩⟩
      · simp [Finset.eq_empty_of_isEmpty S, Finset.eq_empty_of_isEmpty S']
      · refine h _ ?_
        have := hF (Fin.cons a0 t) 0
        simpa only [Fin.update_cons_zero] using this
    rw [sum_piFinset_fin_succ_cons, sum_piFinset_fin_succ_cons]
    calc w ^ (n + 1) * ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t)
        = w * ∑ a ∈ S, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
          rw [← Finset.mul_sum]; ring
      _ = w * ∑ a ∈ S, w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
          simp only [h1]
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w * ∑ a ∈ S, F (Fin.cons a t) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]; ring
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w' * ∑ a ∈ S', F (Fin.cons a t) := by
          simp only [h2]
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_comm]; ring

theorem weighted_sum_piFinset : ∀ (ι α K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] (G : (α → K) → Prop) (S S' : Finset α) (w w' : K), (∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) → ∀ F : (ι → α) → K, (∀ (t : ι → α) (i : ι), G (fun a => F (Function.update t i a))) → w ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S), F t = w' ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S'), F t := by
  intro ι α K _ _ _ G S S' w w' h F hF
  let e := Fintype.equivFin ι
  have key : ∀ T : Finset α, ∑ t ∈ Fintype.piFinset (fun _ : ι => T), F t =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin (Fintype.card ι) => T), F (t ∘ e) := by
    intro T
    symm
    refine Finset.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl α)) ?_ ?_
    · intro t
      simp only [Fintype.mem_piFinset, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
        Function.comp, id]
      exact ⟨fun H i => H _, fun H i => by simpa using H (e.symm i)⟩
    · intro t _
      rfl
  rw [key, key]
  refine weighted_sum_piFinset_fin G S S' w w' h _ (fun t => F (t ∘ e)) ?_
  intro t i
  simp only [Function.update_comp_equiv]
  exact hF _ _

end GlobalTheory
end

section

namespace GlobalTheory.PrimeOrderModule

theorem exists_character (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (T : ℕ)
    (hT : T.Prime) (hM : Nat.card M = T) :
    ∃ χ : S →+* ZMod T, ∀ (a : S) (m : M), χ a = 0 → a • m = 0 := by
  haveI : Fact T.Prime := ⟨hT⟩
  have hZ : Nat.card (ZMod T) = T := Nat.card_zmod T
  let e : M ≃+ ZMod T := addEquivOfPrimeCardEq hM hZ
  have key : ∀ (a : S) (m : M), e (a • m) = e (a • e.symm 1) * e m := by
    intro a m
    have hm : m = (e m).val • e.symm 1 := by
      apply e.injective
      rw [map_nsmul, e.apply_symm_apply, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    calc e (a • m) = e (a • ((e m).val • e.symm 1)) := by rw [← hm]
      _ = (e m).val • e (a • e.symm 1) := by rw [smul_comm, map_nsmul]
      _ = e (a • e.symm 1) * e m := by
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  let χ : S →+* ZMod T :=
    { toFun := fun a => e (a • e.symm 1)
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_smul, key]
      map_zero' := by simp
      map_add' := fun a b => by rw [add_smul, map_add (f := _)] }
  refine ⟨χ, fun a m h => ?_⟩
  apply e.injective
  have h' : e (a • e.symm 1) = 0 := h
  rw [key, h', zero_mul, map_zero]

end GlobalTheory.PrimeOrderModule
end
