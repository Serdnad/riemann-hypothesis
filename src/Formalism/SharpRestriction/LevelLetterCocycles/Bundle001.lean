module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
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
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

section
end

section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds

open Polynomial

variable {O M₁ M₂ : Type*} [CommRing O] [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂]
  [Module O M₂]

private theorem linearMap_mul_apply {M : Type*} [AddCommGroup M] [Module O M] (g h : M →ₗ[O] M)
    (x : M) : (g * h) x = g (h x) := rfl

theorem linearMap_pow_apply_comm_of_intertwine (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (k : ℕ) (y : M₁) : f ((d₁ ^ k) y) = (d₂ ^ k) (f y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, linearMap_mul_apply, linearMap_mul_apply, ih, hf]

private theorem linearMap_add_apply {M : Type*} [AddCommGroup M] [Module O M] (g h : M →ₗ[O] M)
    (x : M) : (g + h) x = g x + h x := rfl

private theorem aeval_end_monomial_apply {M : Type*} [AddCommGroup M] [Module O M]
    (d : M →ₗ[O] M) (n : ℕ) (a : O) (x : M) :
    aeval d (monomial n a) x = a • (d ^ n) x := by
  rw [aeval_monomial, linearMap_mul_apply]
  first
    | rw [Module.algebraMap_end_apply]
    | simp

theorem linearMap_aeval_apply_comm_of_intertwine (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (P : O[X]) (y : M₁) :
    f (aeval d₁ P y) = aeval d₂ P (f y) := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), map_add (f := _), linearMap_add_apply, linearMap_add_apply, map_add (f := _), hp, hq]
  · rw [aeval_end_monomial_apply, aeval_end_monomial_apply, map_smul, linearMap_pow_apply_comm_of_intertwine f d₁ d₂ hf]

private theorem pow_apply_mem_of_invariant' (N : Submodule O M₁) (d : M₁ →ₗ[O] M₁) (hN : ∀ y ∈ N, d y ∈ N)
    (k : ℕ) {y : M₁} (hy : y ∈ N) : (d ^ k) y ∈ N := by
  induction k generalizing y with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ, linearMap_mul_apply]
    exact ih (hN y hy)

theorem aeval_apply_mem_of_invariant (N : Submodule O M₁) (d : M₁ →ₗ[O] M₁) (hN : ∀ y ∈ N, d y ∈ N)
    (P : O[X]) {y : M₁} (hy : y ∈ N) : aeval d P y ∈ N := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), linearMap_add_apply]
    exact N.add_mem hp hq
  · rw [aeval_end_monomial_apply]
    exact N.smul_mem a (pow_apply_mem_of_invariant' N d hN n hy)

private theorem aeval_end_C_apply {M : Type*} [AddCommGroup M] [Module O M]
    (d : M →ₗ[O] M) (a : O) (x : M) : aeval d (C a) x = a • x := by
  rw [aeval_C]
  first
    | rw [Module.algebraMap_end_apply]
    | simp

theorem exists_mem_map_eq_smul (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (N₁ : Submodule O M₁) (hN : ∀ y ∈ N₁, d₁ y ∈ N₁)
    (P₁ P₂ : O[X]) (e : O) (he : C e ∈ Ideal.span ({P₁, P₂} : Set O[X])) (x : M₂)
    (h₁ : ∃ y ∈ N₁, f y = aeval d₂ P₁ x) (h₂ : ∃ y ∈ N₁, f y = aeval d₂ P₂ x) :
    ∃ y ∈ N₁, f y = e • x := by
  obtain ⟨A, B, hAB⟩ : ∃ A B : O[X], A * P₁ + B * P₂ = C e := by
    first
      | exact Ideal.mem_span_pair.1 he
      | simpa [smul_eq_mul] using Submodule.mem_span_pair.1 he
  obtain ⟨y₁, hy₁, hfy₁⟩ := h₁
  obtain ⟨y₂, hy₂, hfy₂⟩ := h₂
  refine ⟨aeval d₁ A y₁ + aeval d₁ B y₂,
    N₁.add_mem (aeval_apply_mem_of_invariant N₁ d₁ hN A hy₁) (aeval_apply_mem_of_invariant N₁ d₁ hN B hy₂), ?_⟩
  rw [← aeval_end_C_apply d₂ e x, ← hAB, map_add (aeval d₂), map_mul (aeval d₂), map_mul (aeval d₂),
    linearMap_add_apply, linearMap_mul_apply, linearMap_mul_apply, ← hfy₁, ← hfy₂, map_add f,
    linearMap_aeval_apply_comm_of_intertwine f d₁ d₂ hf,
    linearMap_aeval_apply_comm_of_intertwine f d₁ d₂ hf]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrA

variable {K : Type*} [Field K] {d : ℕ}

def PiLocalization₂ (G : ℤ → Submodule K (Fin d → K)) (hi u : ℤ) : Prop :=
  ∃ (S : Set (Fin d → K)) (ℓ : (Fin d → K) → ℤ), LinearIndepOn K id S ∧
    (∀ x ∈ S, x ∈ G (ℓ x) ∧ u ≤ ℓ x ∧ ℓ x ≤ hi) ∧ S ⊆ G u ∧
    ∀ u', u ≤ u' → u' ≤ hi → G u' ≤ Submodule.span K {x | x ∈ S ∧ u' ≤ ℓ x}

theorem stage_top (G : ℤ → Submodule K (Fin d → K)) (hi : ℤ) : PiLocalization₂ G hi hi := by
  unfold PiLocalization₂
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent K (G hi : Set (Fin d → K))
  refine ⟨b, fun _ => hi, hli, fun x hx => ⟨hbt hx, le_rfl, le_rfl⟩, hbt, ?_⟩
  intro u' h1 h2 v hv
  have hsub : b ⊆ {x | x ∈ b ∧ u' ≤ (fun _ => hi) x} := fun x hx => ⟨hx, h2⟩
  refine Submodule.span_mono hsub ?_
  rw [hspan, Submodule.span_eq]
  rwa [← le_antisymm h2 h1]

theorem stage_step (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi u : ℤ) (hu : u < hi)
    (h : PiLocalization₂ G hi (u + 1)) : PiLocalization₂ G hi u := by
  unfold PiLocalization₂ at h ⊢
  obtain ⟨S, ℓ, hli, hmem, hSG, hspan⟩ := h
  have hSu : S ⊆ (G u : Set (Fin d → K)) := fun x hx => hG (by omega : u ≤ u + 1) (hSG hx)
  obtain ⟨b, hbt, hSb, htb, hlib⟩ := exists_linearIndepOn_id_extension hli hSu
  refine ⟨b, fun x => if x ∈ S then ℓ x else u, hlib, ?_, hbt, ?_⟩
  · intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨h1, h2, h3⟩ := hmem x hxS
      simp only [hxS, if_true]
      exact ⟨h1, by omega, h3⟩
    · simp only [hxS, if_false]
      exact ⟨hbt hx, le_rfl, hu.le⟩
  · intro u' h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · intro v hv
      have hsub : b ⊆ {x | x ∈ b ∧ u ≤ (fun x => if x ∈ S then ℓ x else u) x} := by
        intro x hx
        refine ⟨hx, ?_⟩
        by_cases hxS : x ∈ S
        · have h3 := (hmem x hxS).2.1
          simp only [hxS, if_true]
          omega
        · simp only [hxS, if_false]
          exact le_rfl
      exact Submodule.span_mono hsub (htb hv)
    · refine (hspan u' (by omega) h2).trans (Submodule.span_mono ?_)
      rintro x ⟨hxS, hx⟩
      exact ⟨hSb hxS, by simpa [hxS] using hx⟩

theorem stage_all (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi : ℤ) :
    ∀ u ≤ hi, PiLocalization₂ G hi u := by
  have key : ∀ k : ℕ, PiLocalization₂ G hi (hi - k) := by
    intro k
    induction k with
    | zero => simpa using stage_top G hi
    | succ k ih =>
      refine stage_step G hG hi (hi - ((k + 1 : ℕ) : ℤ)) (by push_cast; omega) ?_
      have e : hi - ((k + 1 : ℕ) : ℤ) + 1 = hi - (k : ℤ) := by push_cast; ring
      rw [e]
      exact ih
  intro u hu
  have h := key (hi - u).toNat
  rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at h

theorem adapted (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (lo hi : ℤ) (hlh : lo ≤ hi)
    (hlo : G lo = ⊤) :
    ∃ (I : ℕ) (P : Fin I → Fin d → K) (Q : Fin I → Fin d → K) (h : Fin I → ℤ),
      (∀ c : Fin d → K, c = ∑ i, (∑ m, Q i m * c m) • P i) ∧
      (∀ i, P i ∈ G (h i)) ∧ (∀ i, lo ≤ h i ∧ h i ≤ hi) ∧
      ∀ u : ℤ, u ≤ hi → ∀ c ∈ G u, ∀ i, h i < u → ∑ m, Q i m * c m = 0 := by
  obtain ⟨S, ℓ, hli, hmem, _, hspan⟩ := stage_all G hG hi lo hlh
  have hfin : S.Finite := LinearIndependent.set_finite_of_isNoetherian hli
  have := hfin.fintype
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : S → Fin d → K)) := by
    rw [Subtype.range_coe, ← hlo]
    exact (hspan lo le_rfl hlh).trans (Submodule.span_mono fun x hx => hx.1)
  let B0 : Module.Basis S K (Fin d → K) := Module.Basis.mk (v := ((↑) : S → Fin d → K)) hli hsp
  let e := Fintype.equivFin S
  let B := B0.reindex e
  have hB : ∀ i, B i = ((e.symm i : S) : Fin d → K) := fun i => by
    simp only [B, B0, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply hli hsp (e.symm i)
  have hQ : ∀ (c : Fin d → K) i, ∑ m, B.repr (Pi.single m 1) i * c m = B.repr c i := by
    intro c i
    conv_rhs => rw [← Finset.univ_sum_single c]

    rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hs : (Pi.single m (c m) : Fin d → K) = c m • Pi.single m 1 := by
      ext j
      by_cases hj : j = m
      · subst hj
        simp
      · simp [hj]
    rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨Fintype.card S, fun i => B i, fun i m => B.repr (Pi.single m 1) i, fun i => ℓ (B i),
    ?_, ?_, ?_, ?_⟩
  · intro c
    simp only [hQ]
    exact (B.sum_repr c).symm
  · intro i
    show B i ∈ G (ℓ (B i))
    rw [hB]
    exact (hmem _ (e.symm i).2).1
  · intro i
    show lo ≤ ℓ (B i) ∧ ℓ (B i) ≤ hi
    rw [hB]
    obtain ⟨_, h1, h2⟩ := hmem _ (e.symm i).2
    exact ⟨h1, h2⟩
  · intro u hu c hc i hi'
    have hi'' : ℓ (B i) < u := hi'
    show ∑ m, B.repr (Pi.single m 1) i * c m = 0
    rw [hQ]
    by_cases hul : u ≤ lo
    · exfalso
      have h1 := (hmem _ (e.symm i).2).2.1
      rw [hB] at hi''
      omega
    · have hcs := hspan u (by omega) hu hc
      have hset : {x | x ∈ S ∧ u ≤ ℓ x} = B '' {j | u ≤ ℓ (B j)} := by
        ext x
        constructor
        · rintro ⟨hxS, hx⟩
          refine ⟨e ⟨x, hxS⟩, ?_, ?_⟩
          · show u ≤ ℓ (B (e ⟨x, hxS⟩))
            rw [hB, Equiv.symm_apply_apply]
            exact hx
          · rw [hB, Equiv.symm_apply_apply]
        · rintro ⟨j, hj, rfl⟩
          exact ⟨by rw [hB]; exact (e.symm j).2, hj⟩
      rw [hset, Module.Basis.mem_span_image] at hcs
      by_contra hne
      have hmemi := hcs (Finsupp.mem_support_iff.2 hne)
      exact absurd (show u ≤ ℓ (B i) from hmemi) (not_le.2 hi'')

end Formalism.MainNotions.UnusedSlot80.CrA
end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def conv (g : PowerSeries L) (f : ℤ → M) (k : ℤ) : M := ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem conv_vanish (g : PowerSeries L) (f : ℤ → M) (m : ℤ) (hf : ∀ k < m, f k = 0) (e : ℕ)
    (hg : (PowerSeries.X : PowerSeries L) ^ e ∣ g) (k : ℤ) (hk : k < m + e) : conv g f k = 0 := by
  unfold conv
  rw [PowerSeries.X_pow_dvd_iff] at hg
  have hz : ∀ j : ℕ, PowerSeries.coeff j g • f (k - j) = 0 := by
    intro j
    by_cases hj : j < e
    · rw [hg j hj, zero_smul]
    · rw [hf _ (by omega), smul_zero]
  exact (finsum_congr hz).trans finsum_zero

theorem conv_lead (g : PowerSeries L) (f : ℤ → M) (m : ℤ) (hf : ∀ k < m, f k = 0) (e : ℕ)
    (hg : ∀ j < e, PowerSeries.coeff j g = 0) :
    conv g f (m + e) = PowerSeries.coeff e g • f m := by
  unfold conv
  rw [finsum_eq_single _ e]
  · rw [add_sub_cancel_right]
  · intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hg j h, zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem triangular {ι : Type} [Fintype ι] (D : ι → ℤ → M) (m : ℤ) (hD : ∀ a, ∀ k < m, D a k = 0)
    (hind : LinearIndependent L (fun a => D a m)) (g : ι → PowerSeries L) (b : ℕ)
    (hsum : ∀ k < m + b, ∑ a, conv (g a) (D a) k = 0) :
    ∀ a, (PowerSeries.X : PowerSeries L) ^ b ∣ g a := by
  have key : ∀ n : ℕ, n < b → ∀ a, PowerSeries.coeff n (g a) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h1 : ∑ a, PowerSeries.coeff n (g a) • D a m = 0 := by
        have hs := hsum (m + n) (by omega)
        calc ∑ a, PowerSeries.coeff n (g a) • D a m
            = ∑ a, conv (g a) (D a) (m + n) :=
              Finset.sum_congr rfl fun a _ =>
                (conv_lead (g a) (D a) m (hD a) n
                  (fun j hj => ih j hj (by omega) a)).symm
          _ = 0 := hs
      exact Fintype.linearIndependent_iff.mp hind (fun a => PowerSeries.coeff n (g a)) h1
  intro a
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  exact key n hn a

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv
end
end

section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

theorem padicValNat_factorial_succ (p : ℕ) [Fact p.Prime] (M : ℕ) :
    padicValNat p (M + 1).factorial = padicValNat p M.factorial + padicValNat p (M + 1) := by
  rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.add_one_ne_zero M) (Nat.factorial_ne_zero M)]
  omega

theorem padicValNat_sum_Ioc_add_factorial (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    ∑ k ∈ Finset.Ioc K M, padicValNat p k + padicValNat p K.factorial = padicValNat p M.factorial := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [Finset.sum_Ioc_succ_top hKM, padicValNat_factorial_succ]
    omega

theorem digits_sum_le_log (p : ℕ) [Fact p.Prime] (K : ℕ) :
    (p.digits K).sum ≤ (p - 1) * (Nat.log p K + 1) := by
  have hp : p.Prime := Fact.out
  have h1 : (p.digits K).sum ≤ (p.digits K).length * (p - 1) := by
    have := List.sum_le_card_nsmul (p.digits K) (p - 1) (fun x hx => by
      have := Nat.digits_lt_base hp.one_lt hx
      omega)
    simpa using this
  have h2 : (p.digits K).length ≤ Nat.log p K + 1 := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [Nat.length_digits p K hp.one_lt hK.ne']
  calc (p.digits K).sum ≤ (p.digits K).length * (p - 1) := h1
    _ ≤ (Nat.log p K + 1) * (p - 1) := Nat.mul_le_mul h2 (le_refl _)
    _ = (p - 1) * (Nat.log p K + 1) := Nat.mul_comm _ _

theorem padicValNat_sum_Ioc_le (p : ℕ) [Fact p.Prime] (K M : ℕ) (h : K ≤ M) :
    (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k ≤ M - K + (p.digits K).sum := by
  have h2 := padicValNat_sum_Ioc_add_factorial p K M h
  have hM : (p - 1) * padicValNat p M.factorial = M - (p.digits M).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := M) (Fact.out : p.Prime))
  have hK : (p - 1) * padicValNat p K.factorial = K - (p.digits K).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := K) (Fact.out : p.Prime))
  have sM := Nat.digit_sum_le p M
  have sK := Nat.digit_sum_le p K
  have e : (p - 1) * ∑ k ∈ Finset.Ioc K M, padicValNat p k + (p - 1) * padicValNat p K.factorial =
      (p - 1) * padicValNat p M.factorial := by
    rw [← Nat.mul_add, h2]
  omega

theorem padicValInt_sum_le_Ioc (p : ℕ) (Y : Finset ℤ) (K M : ℕ) (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    ∑ x ∈ Y, padicValInt p x ≤ ∑ k ∈ Finset.Ioc K M, padicValNat p k := by
  have e : ∑ k ∈ Y.image Int.natAbs, padicValNat p k = ∑ x ∈ Y, padicValInt p x :=
    by
      simpa only [padicValInt, Nat.padicValNat_def] using
        (Finset.sum_image (f := fun k => padicValNat p k) (by intro x hx y hy hxy; exact hinj x hx y hy hxy))
  rw [← e]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  rw [Finset.mem_Ioc]
  exact hY x hx

private theorem sub_one_mul_sum_padicValInt_le_sub_add_digits_sum (p : ℕ) [Fact p.Prime] (Y : Finset ℤ) (K M : ℕ) (h : K ≤ M)
    (hY : ∀ x ∈ Y, K < x.natAbs ∧ x.natAbs ≤ M)
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, x.natAbs = y.natAbs → x = y) :
    (p - 1) * ∑ x ∈ Y, padicValInt p x ≤ M - K + (p.digits K).sum :=
  le_trans (Nat.mul_le_mul (le_refl _) (padicValInt_sum_le_Ioc p Y K M hY hinj))
    (padicValNat_sum_Ioc_le p K M h)

theorem padicValInt_sum_le (p : ℕ) [Fact p.Prime] (bb S η a : ℕ) (hab : a + η < bb) (X : Finset ℤ)
    (hX : ∀ x ∈ X, x ≠ 0 ∧ ((1 - ((bb + S : ℕ) : ℤ) ≤ x ∧ x ≤ (a : ℤ) - bb) ∨
      (1 - (η : ℤ) ≤ x ∧ x ≤ ((η + a : ℕ) : ℤ)))) :
    (p - 1) * ∑ x ∈ X, padicValInt p x ≤
      2 * a + 2 * η + S + (p - 1) * (Nat.log p (bb - a - 1) + 1) := by
  have e1 : ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x = ∑ x ∈ X, padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not X (fun x => x ≤ (a : ℤ) - bb) (padicValInt p)
  have e2 : ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x), padicValInt p x =
      ∑ x ∈ X.filter (fun x => ¬ x ≤ (a : ℤ) - bb), padicValInt p x :=
    Finset.sum_filter_add_sum_filter_not _ (fun x => 0 < x) (padicValInt p)
  have b1 : (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x ≤
      (bb + S - 1) - (bb - a - 1) + (p.digits (bb - a - 1)).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hx' := hX x hx.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b2 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x),
      padicValInt p x ≤ (η + a) - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have b3 : (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
      padicValInt p x ≤ η - 0 + (p.digits 0).sum := by
    apply sub_one_mul_sum_padicValInt_le_sub_add_digits_sum p _ _ _ (by omega)
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx
      have hx' := hX x hx.1.1
      push_cast at hx'
      rcases Int.natAbs_eq x with h | h <;> omega
    · intro x hx y hy hxy
      rw [Finset.mem_filter, Finset.mem_filter] at hx hy
      have hx' := hX x hx.1.1
      have hy' := hX y hy.1.1
      rcases Int.natAbs_eq x with h1 | h1 <;> rcases Int.natAbs_eq y with h2 | h2 <;> omega
  have z : (p.digits 0).sum = 0 := by simp
  have d := digits_sum_le_log p (bb - a - 1)
  have total : (p - 1) * ∑ x ∈ X, padicValInt p x =
      (p - 1) * ∑ x ∈ X.filter (fun x => x ≤ (a : ℤ) - bb), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => 0 < x), padicValInt p x +
      (p - 1) * ∑ x ∈ (X.filter (fun x => ¬ x ≤ (a : ℤ) - bb)).filter (fun x => ¬ 0 < x),
        padicValInt p x := by
    rw [← e1, ← e2]
    ring
  omega

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
end
