module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle038
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle041
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem alt_alt (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) (n : ℕ) (z : K n) :
    alt (δ (n + 1)) (alt (δ n) z) = 0 := by
  have hrel : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)),
      δ (n + 1) (j.succAbove i) (δ n (i.predAbove j) z) = δ (n + 1) j (δ n i z) := fun j i =>
    DFunLike.congr_fun (coface_rel A B K ι δ hwp hδ n j i) z
  have hexp : alt (δ (n + 1)) (alt (δ n) z) = ∑ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (p.1 : ℕ) * (-1 : ℤ) ^ (p.2 : ℕ)) • δ (n + 1) p.1 (δ n p.2 z) := by
    rw [Fintype.sum_prod_type]

    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
    map_zsmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    rw [hrel, GlobalTheory.CatH.DSq.sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

end GlobalTheory.CompanionTheory.WpCoface
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.AicStep


open Polynomial in
theorem aic_step : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → ∀ P : Polynomial T, P.Monic → 0 < P.natDegree → ∀ (M : ℕ) (a : B), P.eval (g a) ∈ Ideal.span {g π ^ (P.natDegree * M)} → ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ P.eval (g a₁) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
  open Polynomial in
  intro B _ T _ π g hC hπ hA hV P hP hd M a ha
  obtain ⟨_, hsurj, hinj⟩ := hC
  haveI : Nontrivial T := by
    by_contra hT
    rw [not_nontrivial_iff_subsingleton] at hT
    have hP0 : P = 0 := Polynomial.ext fun n => Subsingleton.elim _ _
    simp [hP0] at hd
  haveI : Nontrivial B := g.domain_nontrivial
  choose c hc using fun i : ℕ => hsurj (P.natDegree * (M + 1)) (P.coeff i)
  have hsum : (∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : Polynomial B) =
      ∑ i : Fin P.natDegree, C (c i) * X ^ (i : ℕ) :=
    (Fin.sum_univ_eq_sum_range (fun i => (C (c i) * X ^ i : Polynomial B)) _).symm
  let Q : Polynomial B := X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i
  have hQm : Q.Monic := by
    show (X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : Polynomial B).Monic
    rw [hsum]
    exact monic_X_pow_add (degree_sum_fin_lt _)
  have hQd : Q.natDegree = P.natDegree := by
    show (X ^ P.natDegree + ∑ i ∈ Finset.range P.natDegree, C (c i) * X ^ i : Polynomial B).natDegree = _
    rw [hsum, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have key : ∀ x : B, P.eval (g x) - g (Q.eval x) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := by
    intro x
    have e : P.eval (g x) - g (Q.eval x) =
        ∑ i ∈ Finset.range P.natDegree, (P.coeff i - g (c i)) * g x ^ i := by
      conv_lhs => rw [hP.as_sum]

      simp only [Q, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add (f := _), map_pow,
      map_sum, map_mul, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hc i)
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.AicSplit.exists_eval_eq_prod_of_natDegree_eq
    (fun p hp hpd => hA p hp hpd) P.natDegree Q hQm hQd
  have hle : Ideal.span {g π ^ (P.natDegree * (M + 1))} ≤ Ideal.span {g π ^ (P.natDegree * M)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (by gcongr; omega))
  have h1 : g (Q.eval a) ∈ Ideal.span {g π ^ (P.natDegree * M)} := by
    have h := Ideal.sub_mem _ ha (hle (key a))
    rwa [sub_sub_cancel] at h
  have h2 := hinj _ _ h1
  rw [hb a] at h2
  obtain ⟨a₁, ha₁, h0⟩ := GlobalTheory.CompanionTheory.RootNear.root_near B π hπ hV P.natDegree M b a hd h2
  refine ⟨a₁, ha₁, ?_⟩
  have h3 := key a₁
  rwa [hb a₁, h0, map_zero, sub_zero] at h3

end GlobalTheory.CompanionTheory.AicStep
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem laurent_eq_toLaurent_sub_invert {K : Type} [CommRing K] (h : K[T;T⁻¹]) :
    ∃ α β : Polynomial K, h = Polynomial.toLaurent α -
      LaurentPolynomial.invert (Polynomial.toLaurent β) := by
  induction h using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨α₁, β₁, rfl⟩ := hf
    obtain ⟨α₂, β₂, rfl⟩ := hg
    refine ⟨α₁ + α₂, β₁ + β₂, ?_⟩
    simp only [map_add (f := _)]
    ring
  | C_mul_T n a =>
    rcases le_total 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨Polynomial.monomial m a, 0, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T]
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)
      refine ⟨0, -Polynomial.monomial m a, ?_⟩
      have hn' : n = -(m : ℤ) := by omega
      subst hn'
      simp [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_T,
        LaurentPolynomial.invert_C]

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ _ h₁ h₂ h₃ e₁ e₂ y
  obtain ⟨k, h, hy⟩ := h₃.pow y
  obtain ⟨α, β, rfl⟩ := laurent_eq_toLaurent_sub_invert h
  obtain ⟨-, -, root₁, -, -⟩ := pf_facts p K₁ h₁.pf
  obtain ⟨-, -, root₂, -, -⟩ := pf_facts p K₂ h₂.pf
  obtain ⟨-, -, -, inj₃, -⟩ := pf_facts p K₃ h₃.pf
  obtain ⟨b₁, hb₁⟩ := root₁ k (i₁ α)
  obtain ⟨b₂, hb₂⟩ := root₂ k (i₂ β)
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K₃ h₃.pf.char k
  refine ⟨b₁, b₂, inj₃ k _ _ ?_⟩
  have key : (ρ₁ b₁ - ρ₂ b₂) ^ p ^ k = ρ₁ (b₁ ^ p ^ k) - ρ₂ (b₂ ^ p ^ k) := by
    rw [← hF (ρ₁ b₁ - ρ₂ b₂), map_sub F, hF, hF, map_pow, map_pow]
  rw [hy, key, hb₁, hb₂, e₁, e₂, map_sub]

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.BMid

theorem exists_const_of_rho_eq : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ (b₁ : K₁) (b₂ : K₂), ρ₁ b₁ = ρ₂ b₂ → ∃ a : K, i₁ (Polynomial.C a) = b₁ ∧ i₂ (Polynomial.C a) = b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ hK h₁ h₂ h₃ hρ₁ hρ₂ b₁ b₂ hb
  obtain ⟨k₁, α₁, hα₁⟩ := h₁.2 b₁
  obtain ⟨k₂, α₂, hα₂⟩ := h₂.2 b₂
  have e₁ : b₁ ^ p ^ (k₁ + k₂) = i₁ (α₁ ^ p ^ k₂) := by
    rw [pow_add, pow_mul, hα₁, map_pow]
  have e₂ : b₂ ^ p ^ (k₁ + k₂) = i₂ (α₂ ^ p ^ k₁) := by
    rw [add_comm, pow_add, pow_mul, hα₂, map_pow]
  generalize α₁ ^ p ^ k₂ = α at e₁
  generalize α₂ ^ p ^ k₁ = β at e₂
  generalize k₁ + k₂ = m at e₁ e₂
  have h30 : i₃ (Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β)) = 0 := by
    rw [map_sub, ← hρ₁, ← hρ₂, ← e₁, ← e₂, map_pow, map_pow, hb, sub_self]
  obtain ⟨k, hk⟩ := (h₃.3 _).1 h30
  have hchar : (p : K[T;T⁻¹]) = 0 := by
    rw [← map_natCast (LaurentPolynomial.C : K →+* K[T;T⁻¹]) p, hK.1, map_zero]
  obtain ⟨Fr, hFr⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (K[T;T⁻¹]) hchar k
  have hx : (Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β)) ^ p ^ k =
      Polynomial.toLaurent (α ^ p ^ k) - LaurentPolynomial.invert (Polynomial.toLaurent (β ^ p ^ k)) := by
    rw [← hFr, map_sub, hFr, hFr, map_pow, map_pow, map_pow]
  rw [hx] at hk
  obtain ⟨c, hc₁, hc₂⟩ := GlobalTheory.CompanionTheory.LaurSplit.exists_const_of_mem_span K f g _ _ hk
  have hz₁ : i₁ (α ^ p ^ k - Polynomial.C c) = 0 := (h₁.3 _).2 ⟨0, by simpa using hc₁⟩
  have hz₂ : i₂ (β ^ p ^ k - Polynomial.C c) = 0 := (h₂.3 _).2 ⟨0, by simpa using hc₂⟩
  rw [map_sub, sub_eq_zero, map_pow, ← e₁, ← pow_mul, ← pow_add] at hz₁
  rw [map_sub, sub_eq_zero, map_pow, ← e₂, ← pow_mul, ← pow_add] at hz₂
  obtain ⟨a, ha⟩ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K hK).2.2.1 (m + k) c
  have inj₁ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K₁ h₁.1).2.2.2.1
  have inj₂ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K₂ h₂.1).2.2.2.1
  refine ⟨a, inj₁ (m + k) _ _ ?_, inj₂ (m + k) _ _ ?_⟩
  · rw [← map_pow, ← map_pow, ha, hz₁]
  · rw [← map_pow, ← map_pow, ha, hz₂]

end GlobalTheory.CompanionTheory.BMid
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B →
    ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧
      q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧
      (VAL π → VAL (q π)) := by
  intro p _ B _ π h
  have hp : p.Prime := Fact.out
  obtain ⟨⟨F, hF⟩, hred, -, -, -⟩ := pf_facts p B h

  have hpow : ∀ (N : ℕ) (x : B), π ^ N * x = 0 → π * x = 0 := by
    intro N x e
    apply hred _ (N + 1)
    calc (π * x) ^ (N + 1) = π * x ^ N * (π ^ N * x) := by ring
      _ = 0 := by rw [e, mul_zero]

  have hfrob : ∀ x : B, π * x ^ p = 0 → π * x = 0 := by
    intro x e
    apply hred _ p
    have h1 : p = (p - 1) + 1 := by have := hp.one_lt; omega
    rw [mul_pow]
    conv_lhs => rw [h1, pow_succ π]
    rw [← h1, mul_assoc, e, mul_zero]
  let I : Ideal B :=
    { carrier := {x | π * x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [mul_left_comm, hx, mul_zero] }
  have hI : ∀ x, Ideal.Quotient.mk I x = 0 ↔ π * x = 0 := fun x => Ideal.Quotient.eq_zero_iff_mem
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  refine ⟨B ⧸ I, inferInstance, Ideal.Quotient.mk I, hsurj, ⟨?_, ?_, ?_⟩, ?_, hI, ?_, ?_⟩
  · rw [← map_natCast (Ideal.Quotient.mk I), h.char, map_zero]
  · intro a b e
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    simp only at e
    rw [← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, hI] at e
    rw [← sub_eq_zero, ← map_sub, hI]
    apply hfrob
    have : (x - y) ^ p = x ^ p - y ^ p := by
      rw [← hF, map_sub, hF, hF]
    rw [this, e]
  · intro a
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := h.bij.2 x
    exact ⟨Ideal.Quotient.mk I y, by simp only [map_pow]⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro a e
    obtain ⟨x, rfl⟩ := hsurj a
    rw [← map_mul, hI] at e
    rw [hI]
    apply hpow 2
    rw [← e]
    ring
  · intro hA P hP hdeg
    have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
      (Polynomial.map_surjective _ hsurj P).imp (fun Q hQ => by simpa using hQ) |> fun ⟨Q, hQ⟩ =>
        (Polynomial.mem_lifts _).2 ⟨Q, hQ⟩
    obtain ⟨Q, rfl, hQd, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨x, hx⟩ := hA Q hQm (hQd ▸ hdeg)
    exact ⟨Ideal.Quotient.mk I x, hx.map (Ideal.Quotient.mk I)⟩
  · intro hV f₁ g₁ ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := hsurj f₁
    obtain ⟨g, rfl⟩ := hsurj g₁
    obtain ⟨a₁, b₁, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := hsurj a₁
    obtain ⟨b, rfl⟩ := hsurj b₁
    have ht : π * (a * f + b * g - π ^ N) = 0 := by
      rw [← hI, map_sub, map_add (f := _), map_mul, map_mul, map_pow, hab, sub_self]
    have hmem : π ^ (N + 1) ∈ Ideal.span {f, g} := by
      refine Ideal.mem_span_pair.2 ⟨π * a, π * b, ?_⟩
      linear_combination ht
    obtain ⟨e, he, h1, h2⟩ := hV f g ⟨N + 1, hmem⟩
    refine ⟨Ideal.Quotient.mk I e, he.map _, ?_, ?_⟩
    · rw [Ideal.mem_span_singleton] at h1 ⊢
      rw [← map_mul]
      exact map_dvd _ h1
    · rw [Ideal.mem_span_singleton] at h2 ⊢
      have : (1 - Ideal.Quotient.mk I e) * Ideal.Quotient.mk I g
          = Ideal.Quotient.mk I ((1 - e) * g) := by
        rw [map_mul, map_sub, map_one]
      rw [this]
      exact map_dvd _ h2

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem mul_eq_zero_of_C_pow_mem_span (K : Type) [CommRing K]
    (hred : ∀ (x : K) (n : ℕ), x ^ n = 0 → x = 0) (f g a : K) (n : ℕ)
    (h : (Polynomial.C a) ^ n ∈
      Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) : g * a = 0 := by
  let L := Localization.Away g
  let u : L := IsLocalization.Away.invSelf g
  have hu : algebraMap K L g * u = 1 := IsLocalization.Away.mul_invSelf g
  let φ : Polynomial K →+* L := Polynomial.eval₂RingHom (algebraMap K L) (u * algebraMap K L f)
  have h0 : φ (Polynomial.C f - Polynomial.X * Polynomial.C g) = 0 := by
    have e1 : φ (Polynomial.C f) = algebraMap K L f := by simp [φ]
    have e2 : φ Polynomial.X = u * algebraMap K L f := by simp [φ]
    have e3 : φ (Polynomial.C g) = algebraMap K L g := by simp [φ]
    rw [map_sub, map_mul, e1, e2, e3]
    linear_combination (-(algebraMap K L f)) * hu
  have h1 : φ ((Polynomial.C a) ^ n) = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hc, map_mul, h0, mul_zero]
  have h2 : algebraMap K L (a ^ n) = 0 := by
    have e : φ ((Polynomial.C a) ^ n) = algebraMap K L (a ^ n) := by simp [φ]
    rw [← e, h1]
  obtain ⟨⟨m, hm⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) L _).1 h2
  obtain ⟨M, rfl⟩ := hm
  have e' : g ^ M * a ^ n = 0 := e
  apply hred _ (M + n)
  calc (g * a) ^ (M + n) = g ^ n * a ^ M * (g ^ M * a ^ n) := by ring
    _ = 0 := by rw [e', mul_zero]

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁]
    (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂)
    (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} →
    PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) →
    PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) →
    ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := by
  intro p _ K _ K₁ _ K₂ _ f g i₁ i₂ r N hK hr hN h₁ h₂ a ha₁ ha₂
  obtain ⟨-, hred, -, -, hroots⟩ := pf_facts p K hK
  obtain ⟨k₁, hk₁⟩ := (h₁.ker _).1 ha₁
  obtain ⟨k₂, hk₂⟩ := (h₂.ker _).1 ha₂
  have hg : g * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred f g a _ hk₁
  have hf : f * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred g f a _ hk₂
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hN
  have h0 : r 0 ^ N * a = 0 := by
    rw [← huv]
    linear_combination u * hf + v * hg
  exact (hroots r hr).2.2 N a h0

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)),
    IsWP ι → Pf p A → Pf p B → Pf p K := by
  intro p _ A _ B _ _ K _ _ n ι hW hA hB
  obtain ⟨⟨FA, hFA⟩, -⟩ := pf_facts p A hA
  obtain ⟨⟨FB, hFB⟩, -⟩ := pf_facts p B hB
  have hchar : (p : K) = 0 := by
    have := congrArg (algebraMap A K) hA.char
    simpa using this
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K hchar 1
  have hF' : ∀ x, F x = x ^ p := fun x => by rw [hF, pow_one]
  have hcompat : ∀ i, (((ι i : B →+* K)).comp (FB.symm : B →+* B)).comp (algebraMap A B) =
      (algebraMap A K).comp (FA.symm : A →+* A) := by
    intro i
    ext a
    obtain ⟨b, rfl⟩ := FA.surjective a
    have h1 : algebraMap A B (FA b) = FB (algebraMap A B b) := by
      rw [hFA, hFB, map_pow]
    simp [h1]
  obtain ⟨z, hz1, hz2⟩ := hW.ex K ((algebraMap A K).comp (FA.symm : A →+* A))
    (fun i => ((ι i : B →+* K)).comp (FB.symm : B →+* B)) hcompat
  have hz1' : ∀ a, z (algebraMap A K a) = algebraMap A K (FA.symm a) := fun a => by
    simpa using congrArg (fun f : A →+* K => f a) hz1
  have hz2' : ∀ i b, z (ι i b) = ι i (FB.symm b) := fun i b => by
    simpa using congrArg (fun f : B →+* K => f b) (hz2 i)
  have hFa : ∀ a, F (algebraMap A K a) = algebraMap A K (FA a) := fun a => by
    rw [hF', hFA, map_pow]
  have hFb : ∀ i b, F (ι i b) = ι i (FB b) := fun i b => by
    rw [hF', hFB, map_pow]
  have hFz : F.comp z = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  have hzF : z.comp F = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  refine ⟨hchar, ?_, ?_⟩
  · intro x y hxy
    have h : F x = F y := by rw [hF', hF']; exact hxy
    have := congrArg z h
    have hx : ∀ w, z (F w) = w := fun w => by
      simpa using congrArg (fun f : K →+* K => f w) hzF
    rwa [hx, hx] at this
  · intro y
    refine ⟨z y, ?_⟩
    have : F (z y) = y := by simpa using congrArg (fun f : K →+* K => f y) hFz
    simpa [hF'] using this

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem solv_of_solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  intro p _ A _ B _ _ m n k a c hB hS
  obtain ⟨y, hy⟩ := hS
  obtain ⟨-, -, hroot, hinj, -⟩ := pf_facts p B hB
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char k
  choose y' hy' using fun j => hroot k (y j)
  refine ⟨y', fun i => hinj k _ _ ?_⟩

  rw [← hF, ← hF, map_sum, hF, ← map_pow, ← hy i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hF, Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow, hy' j]

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open CrystallineSemistableComparison.Onto

theorem _root_.GlobalTheory.T.onto_form_laws : CrystallineSemistableComparison.Onto.FormLaws := by
  first | exact @GlobalTheory.CompanionTheory.OntoForms.formLaws | exact GlobalTheory.CompanionTheory.OntoForms.formLaws | (intros; apply GlobalTheory.CompanionTheory.OntoForms.formLaws <;> assumption)
end
