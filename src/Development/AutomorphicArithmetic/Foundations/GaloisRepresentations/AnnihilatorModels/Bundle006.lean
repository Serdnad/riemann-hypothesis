module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem mapP_mapP {R B C ι : Type} [CommRing R] [CommRing B] [CommRing C] (f : R →+* B) (g : B →+* C)
    (N : Polynomial (MvPolynomial ι R)) : mapP g (mapP f N) = mapP (g.comp f) N := by
  simp only [mapP, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun p => MvPolynomial.map_map f g p

private theorem step_one (hPP : PtsProd) {R C C' ι J : Type} [CommRing R] [CommRing C] [CommRing C'] [Algebra R C]
    [Fintype ι] [Fintype J] (S : J → Type) [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)]
    (N : J → Polynomial (MvPolynomial ι R)) (a : J → ℕ) (s : ∀ j, ι → S j) (ρ : C →+* C')
    (I : J → Type) [∀ j, Fintype (I j)] (z : ∀ j, I j → (S j →ₐ[R] C))
    (h : ∀ j, mapP (algebraMap R C) (N j) = ∏ i, form fun k => z j i (s j k)) :
    ((pts a fun j i k => ρ (z j i (s j k))).map form).prod = mapP (ρ.comp (algebraMap R C)) (∏ j, N j ^ a j) := by
  rw [hPP C C' ρ ι J I a (fun j i k => z j i (s j k))]
  simp_rw [← h]
  rw [← mapP_mapP]
  congr 1
  simp only [mapP, Polynomial.map_prod, Polynomial.map_pow]

theorem UpperTheory.Gal.crystallineComparison.sameNormRing_of :
    NormRead → ValLift → PtsProd → CongrRad → SameNormRing := by
  intro hNR hVL hPP hCR l R _ 𝔞 hB J _ S _ _ d hS a b ι _ s hV B _ _ hl I _ z hz B' _ ρ hρ
  choose N hN using fun j => hNR l (d j) R (S j) (hS j) hB.closed ι (s j)
  have hB1 : ∀ j, mapP (algebraMap R B) (N j) = ∏ i, form fun k => z j i (s j k) :=
    fun j => (hN j).1 B hl (I j) (z j) (hz j)
  have key : mapP (ρ.comp (algebraMap R B)) (∏ j, N j ^ a j) = mapP (ρ.comp (algebraMap R B)) (∏ j, N j ^ b j) := by
    refine hCR R 𝔞 hB.rad ι _ _ ?_ B' _ hρ
    intro 𝔭 hp
    haveI : 𝔭.IsPrime := hp.1.1
    obtain ⟨V, _, _, _, _, _, hl', hc⟩ := hVL R (l : R) hB.nzd 𝔭
    have hl0 : (l : V) ≠ 0 := by simpa using hl'
    refine ⟨IsLocalRing.ResidueField V, inferInstance, (IsLocalRing.residue V).comp (algebraMap R V), ?_, ?_⟩
    · rw [← RingHom.comap_ker, IsLocalRing.ker_residue, hc]
    · have hfin : ∀ j, Finite (S j →ₐ[R] V) := fun j => ((hN j).2 V hl0).1
      letI : ∀ j, Fintype (S j →ₐ[R] V) := fun j => @Fintype.ofFinite _ (hfin j)
      have hV1 : ∀ j, mapP (algebraMap R V) (N j) = ∏ i : S j →ₐ[R] V, form fun k => i (s j k) :=
        fun j => ((hN j).2 V hl0).2 (S j →ₐ[R] V) id Function.bijective_id
      have hm := hV V hl0 (by rw [hc]; exact hp) (fun j => S j →ₐ[R] V) (fun j i => i) (fun j => Function.bijective_id)
      rw [← step_one hPP S N a s (IsLocalRing.residue V) (fun j => S j →ₐ[R] V) (fun j i => i) hV1,
        ← step_one hPP S N b s (IsLocalRing.residue V) (fun j => S j →ₐ[R] V) (fun j i => i) hV1, hm]
  show ((pts a fun j i k => ρ (z j i (s j k))).map form).prod = ((pts b fun j i k => ρ (z j i (s j k))).map form).prod
  rw [step_one hPP S N a s ρ I z hB1, step_one hPP S N b s ρ I z hB1, key]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private lemma coeff_lin_form {A ι : Type} [CommRing A] [Fintype ι] (a : ι → A) (k₀ : ι) :
    AddMonoidAlgebra.coeff (∑ k, MvPolynomial.C (a k) * MvPolynomial.X k : MvPolynomial ι A) (Finsupp.single k₀ 1) = a k₀ := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k _ hk
    rw [MvPolynomial.coeff_X', if_neg, mul_zero]
    intro h
    exact hk (Finsupp.single_left_injective one_ne_zero h)
  · simp

theorem UpperTheory.Gal.crystallineComparison.matchStep_of :
    GaussLin → SameNormBasic → LinFactor → MatchStep := by
  intro hG hS hL B _ ϖ hϖ hnu ι _ N m hm u u' hcard hsame x hx hchain hdich
  by_contra hcon
  push_neg at hcon
  have hex : ∀ y : ι → B, ∃ c : B, ∃ e : ι → B,
      y ∈ u' → c ∣ ϖ ^ m ∧ (∃ k₀, e k₀ = 1) ∧ ∀ k, x k - y k = c * e k := by
    intro y
    by_cases hy : y ∈ u'
    · obtain ⟨k, hk⟩ := hcon y hy
      have hdk : x k - y k ∣ ϖ ^ m := (hdich y hy k).resolve_right hk
      obtain ⟨c, e, k₀, hc, he, hd⟩ := hL B ι (ϖ ^ m) (fun k => x k - y k) ⟨k, hdk⟩ (hchain y hy)
      exact ⟨c, e, fun _ => ⟨hc, ⟨k₀, he⟩, hd⟩⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose c e hce using hex
  set M := ϖ ^ (m * (N + 1)) with hM
  have h4 := (hS (B ⧸ Ideal.span {M}) ι).2.2.2 (fun k => Ideal.Quotient.mk (Ideal.span {M}) (x k))
    (redMod M u) (redMod M u') hsame (Multiset.mem_map_of_mem _ hx)
  let L : (ι → B) → MvPolynomial ι (B ⧸ Ideal.span {M}) :=
    fun y => ∑ k, MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (e y k)) * MvPolynomial.X k
  have h4' : (u'.map (fun y => MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (c y)) * L y)).prod = 0 := by
    rw [← h4]
    congr 1
    unfold redMod
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun y hy => ?_
    simp only [Function.comp, L, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_sub, (hce y hy).2.2 k, map_mul, map_mul, mul_assoc]
  rw [Multiset.prod_map_mul] at h4'
  have hC : (u'.map fun y => (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (c y)) :
        MvPolynomial ι (B ⧸ Ideal.span {M}))).prod =
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (u'.map c).prod) :
        MvPolynomial ι (B ⧸ Ideal.span {M})) := by
    rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    rfl
  rw [hC] at h4'
  have hz : Ideal.Quotient.mk (Ideal.span {M}) (u'.map c).prod = 0 := by
    refine hG _ ι _ (u'.map L) ?_ h4'
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨k₀, hk₀⟩ := (hce y hy).2.1
    exact ⟨Finsupp.single k₀ 1, by simp only [L]; rw [coeff_lin_form, hk₀, map_one]⟩
  have hdvd : M ∣ (u'.map c).prod :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hdvd2 : (u'.map c).prod ∣ (ϖ ^ m) ^ Multiset.card u' := by
    have hh := Multiset.prod_dvd_prod_of_dvd (S := u') c (fun _ => ϖ ^ m) (fun y hy => (hce y hy).1)
    simpa [Multiset.map_const', Multiset.prod_replicate] using hh
  obtain ⟨t, ht⟩ := hdvd.trans hdvd2
  have hr : M = (ϖ ^ m) ^ Multiset.card u' * ϖ ^ (m * (N + 1 - Multiset.card u')) := by
    rw [hM, ← pow_mul, ← pow_add, ← Nat.mul_add]
    congr 2
    omega
  rw [hr, mul_assoc] at ht
  have hpa : (ϖ ^ m) ^ Multiset.card u' ∈ nonZeroDivisors B := pow_mem (pow_mem hϖ m) _
  have h0 : (ϖ ^ (m * (N + 1 - Multiset.card u')) * t - 1) * (ϖ ^ m) ^ Multiset.card u' = 0 := by
    linear_combination -ht
  have h1 : ϖ ^ (m * (N + 1 - Multiset.card u')) * t = 1 :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpa).2 _ h0)
  have hu : IsUnit (ϖ ^ (m * (N + 1 - Multiset.card u'))) := isUnit_iff_exists_inv.mpr ⟨t, h1⟩
  exact hnu ((isUnit_pow_iff (Nat.mul_ne_zero (by omega) (by omega))).mp hu)
end

section

namespace UpperTheory.Gal.crystallineComparison

private theorem exists_min_dvd {B ι : Type} [CommRing B] (w : B) (d : ι → B)
    (hd : ∀ k k', d k ∣ w → d k ∣ d k' ∨ d k' ∣ d k) (s : Finset ι) (hs : s.Nonempty)
    (hw : ∀ k ∈ s, d k ∣ w) : ∃ k₀ ∈ s, ∀ k ∈ s, d k₀ ∣ d k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    by_cases hs' : s.Nonempty
    · obtain ⟨k₁, hk₁, hmin⟩ := ih hs' (fun k hk => hw k (Finset.mem_insert_of_mem hk))
      rcases hd a k₁ (hw a (Finset.mem_insert_self a s)) with h | h
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact dvd_refl _
        · exact h.trans (hmin k hk)
      · refine ⟨k₁, Finset.mem_insert_of_mem hk₁, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact h
        · exact hmin k hk
    · rw [Finset.not_nonempty_iff_eq_empty] at hs'
      subst hs'
      refine ⟨a, by simp, fun k hk => ?_⟩
      simp at hk
      subst hk
      exact dvd_refl _

theorem linFactor_of : LinFactor := by
  intro B ι _ _ w d hex hd
  classical
  obtain ⟨k₀, hk₀, hmin⟩ := exists_min_dvd w d hd (Finset.univ.filter fun k => d k ∣ w)
    (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by simpa using hk⟩)
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hk₀w : d k₀ ∣ w := (Finset.mem_filter.mp hk₀).2
  have hall : ∀ k, d k₀ ∣ d k := by
    intro k
    rcases hd k₀ k hk₀w with h | h
    · exact h
    · exact hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans hk₀w⟩)
  refine ⟨d k₀, fun k => if k = k₀ then 1 else (hall k).choose, k₀, hk₀w, by simp, ?_⟩
  intro k
  by_cases hk : k = k₀
  · subst hk
    simp
  · simp only [hk, if_false]
    exact (hall k).choose_spec

end UpperTheory.Gal.crystallineComparison
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem telescope_core {P : Type} (q n : ℕ) (F : P → P) (T A : ℕ → Multiset P)
    (h0 : T 0 = A 0)
    (hs : ∀ j, j < n → T (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1)) (m : ℕ) (hm : m ≤ n) :
    (Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) ∧
    (¬ Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) := by
  induction m with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd ⟨0, rfl⟩ h⟩
    simp [h0]
  | succ m ih =>
    have hmn : m < n := hm
    obtain ⟨ihE, ihO⟩ := ih (by omega)
    have key : (T (m + 1)).map F^[n - (m + 1)] =
        (A m).map F^[n - m] + q ^ (m + 1) • (A (m + 1)).map F^[n - (m + 1)] := by
      rw [hs m hmn, Multiset.map_add (f := _), Multiset.map_nsmul, Multiset.map_map]
      congr 2
      have e : n - m = (n - (m + 1)) + 1 := by omega
      rw [e, Function.iterate_succ]
    have hc : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    simp only [Finset.sum_range_succ _ (m + 1), key, hc, pow_add, smul_add, mul_smul]
    rcases Nat.even_or_odd m with he | ho
    · have hne : ¬ Even (m + 1) := Nat.not_even_iff_odd.mpr he.add_one
      simp only [hne, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun h => h.elim, fun _ => ?_⟩
      rw [ihE he]
      abel
    · have hne : ¬ Even m := Nat.not_even_iff_odd.mpr ho
      have hev : Even (m + 1) := ho.add_one
      simp only [hev, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
      rw [ihO hne]
      abel

theorem UpperTheory.Gal.crystallineComparison.telescope_of :
    Telescope := by
  intro q n P F T A hAn h0 hs
  let T' : ℕ → Multiset P := fun j => if h : j < n + 1 then T ⟨j, h⟩ else 0
  have hT : ∀ j : Fin (n + 1), T j = T' j := fun j => by
    simp only [T', dif_pos j.isLt, Fin.eta]
  have h0' : T' 0 = A 0 := by simpa [T'] using h0
  have hs' : ∀ j, j < n → T' (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1) := by
    intro j hj
    have hh := hs ⟨j, hj⟩
    simpa [T', hj, Fin.succ] using hh
  have hE : ∑ j : Fin (n + 1), wEv q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  have hO : ∑ j : Fin (n + 1), wOd q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  obtain ⟨h1, h2⟩ := telescope_core q n F T' A h0' hs' n le_rfl
  rw [hE, hO]
  by_cases he : Even n
  · rw [h1 he]
    simp [hAn]
  · rw [h2 he]
    simp [hAn]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private lemma idem_prod_one_sub {B : Type} [CommRing B] (s : Finset B)
    (hs : ∀ e ∈ s, IsIdempotentElem e) : IsIdempotentElem (∏ e ∈ s, (1 - e)) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e he => (hs e he).one_sub

private lemma one_sub_prod_mem {B : Type} [CommRing B] (I : Ideal B) (s : Finset B)
    (hs : ∀ e ∈ s, e ∈ I) : 1 - ∏ e ∈ s, (1 - e) ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : a ∈ I := hs a (Finset.mem_insert_self a s)
    have h2 := ih fun e he => hs e (Finset.mem_insert_of_mem he)
    have : 1 - (1 - a) * ∏ e ∈ s, (1 - e) = (1 - ∏ e ∈ s, (1 - e)) + a * ∏ e ∈ s, (1 - e) := by ring
    rw [this]
    exact I.add_mem h2 (I.mul_mem_right _ h1)

private lemma cover_step {B : Type} [CommRing B] (Λ : Type) [Fintype Λ] (J : Λ → Ideal B)
    (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ σ, ∃ e ∈ J σ, IsIdempotentElem e ∧ e ∉ 𝔪) :
    ∃ f : Λ → B, (∀ σ, IsIdempotentElem (f σ)) ∧ (∀ σ, f σ ∈ J σ) ∧ ∏ σ, (1 - f σ) = 0 := by
  classical
  let E : Set B := {e | IsIdempotentElem e ∧ ∃ σ, e ∈ J σ}
  have hE : Ideal.span E = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨σ, e, he, hi, hn⟩ := h 𝔪 hm
    exact hn (hle (Ideal.subset_span ⟨hi, σ, he⟩))
  obtain ⟨t, htE, ht⟩ := (Ideal.span_eq_top_iff_finite E).1 hE
  refine ⟨fun σ => 1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e), fun σ => ?_, fun σ => ?_, ?_⟩
  · exact (idem_prod_one_sub _ fun e he => (htE (Finset.mem_filter.1 he).1).1).one_sub
  · exact one_sub_prod_mem _ _ fun e he => (Finset.mem_filter.1 he).2
  · set g : B := ∏ σ, (1 - (1 - ∏ e ∈ t.filter (· ∈ J σ), (1 - e))) with hg
    have hkill : ∀ e ∈ t, e * g = 0 := by
      intro e he
      obtain ⟨hi, σ, hσ⟩ := htE he
      have hef : e ∈ t.filter (· ∈ J σ) := Finset.mem_filter.2 ⟨he, hσ⟩
      obtain ⟨c, hc⟩ : (1 - e) ∣ g := by
        refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ σ))
        rw [sub_sub_cancel]
        exact Finset.dvd_prod_of_mem _ hef
      have h0 : e * (1 - e) = 0 := by
        have : e * e = e := hi
        rw [mul_sub, mul_one, this, sub_self]
      rw [hc, ← mul_assoc, h0, zero_mul]
    have hall : ∀ x ∈ Ideal.span (t : Set B), x * g = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hkill x hx
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
    have := hall 1 (by rw [ht]; trivial)
    rwa [one_mul] at this

theorem UpperTheory.Gal.crystallineComparison.idemCover_of :
    IdemCover := by
  intro B _ Λ _ J h
  classical
  obtain ⟨f, hfi, hfJ, hf0⟩ := cover_step Λ J h
  letI : LinearOrder Λ := LinearOrder.lift' (Fintype.equivFin Λ) (Equiv.injective _)
  let P : Λ → B := fun σ => ∏ τ ∈ Finset.univ.filter (· < σ), (1 - f τ)
  have hP : ∀ σ, IsIdempotentElem (P σ) := by
    intro σ
    show P σ * P σ = P σ
    simp only [P]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => (hfi τ).one_sub
  have hkill : ∀ σ τ, τ < σ → P σ * f τ = 0 := by
    intro σ τ hτ
    obtain ⟨c, hc⟩ : (1 - f τ) ∣ P σ :=
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ τ, hτ⟩)
    have h0 : (1 - f τ) * f τ = 0 := by
      have : f τ * f τ = f τ := hfi τ
      rw [sub_mul, one_mul, this, sub_self]
    rw [hc, mul_comm (1 - f τ) c, mul_assoc, h0, mul_zero]
  have hlt : ∀ σ τ, τ < σ → (f σ * P σ) * (f τ * P τ) = 0 := by
    intro σ τ hτ
    have : (f σ * P σ) * (f τ * P τ) = f σ * (P σ * f τ) * P τ := by ring
    rw [this, hkill σ τ hτ, mul_zero, zero_mul]
  refine ⟨fun σ => f σ * P σ, ⟨⟨fun σ => (hfi σ).mul (hP σ), ?_⟩, ?_⟩, fun σ => (J σ).mul_mem_right _ (hfJ σ)⟩
  · intro σ τ hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · show (f σ * P σ) * (f τ * P τ) = 0
      rw [mul_comm]
      exact hlt τ σ hl
    · exact hlt σ τ hl
  · have := Finset.prod_one_sub_ordered (Finset.univ : Finset Λ) f
    rw [hf0] at this
    exact (sub_eq_zero.1 this.symm).symm
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem form_map' {B B' ι : Type} [CommRing B] [CommRing B'] [Fintype ι] (f : B →+* B') (c : ι → B) :
    (form c).map (MvPolynomial.map f) = form fun k => f (c k) := by

  simp [form, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_sum, map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem descend {R S B B' ι I : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing B']
    [Algebra R S] [Algebra R B] [Algebra R B'] [Fintype ι] [Fintype I]
    (j : B →ₐ[R] B') (hj : Function.Injective j) (N : Polynomial (MvPolynomial ι R)) (s : ι → S)
    (z : I → (S →ₐ[R] B))
    (h : mapP (algebraMap R B') N = ∏ i, form fun k => j (z i (s k))) :
    mapP (algebraMap R B) N = ∏ i, form fun k => z i (s k) := by
  have hj' : Function.Injective (j : B →+* B') := hj
  apply Polynomial.map_injective _ (MvPolynomial.map_injective _ hj')
  rw [Polynomial.map_prod]
  have e : ∀ i, (form fun k => z i (s k)).map (MvPolynomial.map (j : B →+* B'))
      = form fun k => j (z i (s k)) := fun i => form_map' _ _
  simp only [e]
  have hc : (MvPolynomial.map (σ := ι) (j : B →+* B')).comp (MvPolynomial.map (algebraMap R B))
      = MvPolynomial.map (algebraMap R B') := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp
  rw [← h, mapP, Polynomial.map_map, hc]

theorem UpperTheory.Gal.crystallineComparison.normRead_of :
    NormInt → EtOfUnit → SplitsField → ValPts → NormRead := by
  intro hInt hEt hSF hVP l d R S _ _ _ hE hcl ι _ s
  obtain ⟨N, hN⟩ := hInt l d R S hE hcl ι s
  refine ⟨N, ?_, ?_⟩
  · intro B _ _ hl I _ z hz
    have hinj : Function.Injective (algebraMap B (Localization.Away (l : B))) :=
      IsLocalization.injective _ (Submonoid.powers_le.2 hl)
    have hu : IsUnit (l : Localization.Away (l : B)) := by
      have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : B)) (l : B)
      simpa using this
    have h1 := hN (Localization.Away (l : B)) hu I
      (fun i => (IsScalarTower.toAlgHom R B (Localization.Away (l : B))).comp (z i)) hz
    exact descend (IsScalarTower.toAlgHom R B (Localization.Away (l : B))) hinj N s z h1
  · intro V _ _ _ _ _ hl
    have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
      IsFractionRing.injective V (FractionRing V)
    have hlK : ((l : ℕ) : FractionRing V) ≠ 0 := by
      intro h0
      apply hl
      apply hinj
      simpa using h0
    have hu : IsUnit ((l : ℕ) : FractionRing V) := hlK.isUnit
    have het : Algebra.Etale (FractionRing V) (FractionRing V ⊗[R] S) := hEt l R S _ hE.et hu
    obtain ⟨hfin, hsp⟩ := hSF R S (FractionRing V) het
    haveI := hE.fin
    have hb := hVP R S V
    have hfinV : Finite (S →ₐ[R] V) := Finite.of_injective _ hb.1
    refine ⟨hfinV, fun I _ z hz => ?_⟩
    letI := Fintype.ofFinite (S →ₐ[R] FractionRing V)
    have h1 := hN (FractionRing V) hu (S →ₐ[R] FractionRing V) (fun z => z) hsp
    refine descend (IsScalarTower.toAlgHom R V (FractionRing V)) hinj N s z ?_
    rw [h1]
    symm
    exact Fintype.prod_bijective (fun i => (IsScalarTower.toAlgHom R V (FractionRing V)).comp (z i))
      (hb.comp hz) _ _ (fun i => rfl)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.permMap_of :
    PermOfMap := by
  classical
  intro I I' P _ _ f g h
  have hc : ∀ p : P, Fintype.card {i // f i = p} = Fintype.card {j // g j = p} := by
    intro p
    have hp := congrArg (Multiset.count p) h
    simp only [Multiset.count_map] at hp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using hp
  let e : ∀ p, {i // f i = p} ≃ {j // g j = p} := fun p => Fintype.equivOfCardEq (hc p)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  intro i
  show f i = g ((e (f i)) ⟨i, rfl⟩).1
  exact ((e (f i)) ⟨i, rfl⟩).2.symm
end
