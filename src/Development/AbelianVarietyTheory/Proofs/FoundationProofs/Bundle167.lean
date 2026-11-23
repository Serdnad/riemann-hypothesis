module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle154
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import ReciprocityTheory.SemistableReduction.SemiDegZA
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle086
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle153
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle151
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle156
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle155
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
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma summable_norm_qterm_of_polyB (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  apply GlobalTheory.EisM.Lin.summ_norm <;> assumption

end GlobalTheory.EisM

namespace GlobalTheory.EisM

lemma qs_sub_eq_const (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) (hab : ∀ n, n ≠ 0 → a n = b n) (τ : ℍ) :
    qs a τ - qs b τ = a 0 - b 0 := by
  unfold qs
  rw [← (summable_norm_qterm_of_polyB a ha τ).of_norm.tsum_sub (summable_norm_qterm_of_polyB b hb τ).of_norm]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    rw [hab n hn, sub_self]

theorem eq_of_coeff_pos_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b →
    (∀ n, n ≠ 0 → a n = b n) → a = b := by
  intro k L χ a b hk hL ha hb hab
  set c : ℂ := a 0 - b 0 with hc
  have hconst := qs_sub_eq_const a b ha.1 hb.1 hab
  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  have hγ10 : γ 1 0 = (L : ℤ) := rfl
  have hγ11 : γ 1 1 = 1 := rfl
  have key : ∀ τ : ℍ, c = χ 1 * ((L : ℂ) * τ + 1) ^ k * c := by
    intro τ
    have h1 := ha.2 γ (by rw [hγ10]) τ
    have h2 := hb.2 γ (by rw [hγ10]) τ
    rw [hγ10, hγ11] at h1 h2
    have e1 := hconst (γ • τ)
    rw [h1, h2, ← mul_sub, hconst τ, ← hc] at e1
    push_cast at e1
    exact e1.symm
  by_contra hne
  have hc0 : c ≠ 0 := by
    intro h0
    apply hne
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · exact sub_eq_zero.mp h0
    · exact hab n hn
  have hone : ∀ τ : ℍ, ‖χ 1‖ * ‖(L : ℂ) * τ + 1‖ ^ k = 1 := by
    intro τ
    have h := key τ
    have h' : χ 1 * ((L : ℂ) * τ + 1) ^ k = 1 := by
      have : (χ 1 * ((L : ℂ) * τ + 1) ^ k - 1) * c = 0 := by rw [sub_mul, ← h]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)
    rw [← norm_pow, ← norm_mul, h', norm_one]
  let τ₁ : ℍ := ⟨Complex.I, by simp⟩
  let τ₂ : ℍ := ⟨2 * Complex.I, by simp⟩
  have e1 := hone τ₁
  have e2 := hone τ₂
  have hχ : ‖χ 1‖ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e1; exact zero_ne_one e1
  have heq : ‖(L : ℂ) * τ₁ + 1‖ ^ k = ‖(L : ℂ) * τ₂ + 1‖ ^ k :=
    mul_left_cancel₀ hχ (e1.trans e2.symm)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlt : ‖(L : ℂ) * τ₁ + 1‖ < ‖(L : ℂ) * τ₂ + 1‖ := by
    have s1 : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 = 1 + (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₁, UpperHalfPlane.coe_mk]
      ring
    have s2 : ‖(L : ℂ) * τ₂ + 1‖ ^ 2 = 1 + 4 * (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₂, UpperHalfPlane.coe_mk]
      ring
    have : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 < ‖(L : ℂ) * τ₂ + 1‖ ^ 2 := by
      rw [s1, s2]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  have := pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega : k ≠ 0)
  exact absurd heq (ne_of_lt this)

end GlobalTheory.EisM
end

section

namespace GlobalTheory.DeterminantSimpLemma

open NumberField

theorem main {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
    {M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)} {x : Fin n → K} :
    x ∈ Submodule.span K (↑M : Set (Fin n → K)) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ M := by
  apply ReciprocityTheory.MultiplicativeHeights.SemiPt.clear_denom <;> assumption

end GlobalTheory.DeterminantSimpLemma
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN.Lag

theorem mdiff_of_hasQ {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  obtain ⟨a, ha⟩ := h
  exact (GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N f a hN ha).1

theorem hasQ_of_qConj {g : ℂ ≃+* ℂ} {N : ℕ} {f f' : ℍ → ℂ} (h : QConj g N f f') :
    (∃ a, HasQ N f a) ∧ ∃ a, HasQ N f' a := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨⟨a, ha⟩, ⟨_, hb⟩⟩

theorem qConj_refl {N : ℕ} {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) : QConj (RingEquiv.refl ℂ) N f f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha, by simpa using ha⟩

theorem hasQ_zero (N : ℕ) : HasQ N (0 : ℍ → ℂ) (fun _ => 0) := by
  intro τ
  simp only [zero_mul, Pi.zero_apply]
  exact hasSum_zero

theorem qConj_ne_zero {g : ℂ ≃+* ℂ} {N : ℕ} (hN : 0 < N) {f f' : ℍ → ℂ} (h : QConj g N f f') (hf : f ≠ 0) :
    f' ≠ 0 := by
  obtain ⟨a, ha, hb⟩ := h
  rintro rfl
  have h1 := (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).1 N 0 _ _ hN hb (hasQ_zero N)
  have h2 : a = fun _ => 0 := funext fun n => by
    have := congrFun h1 n
    simpa using this
  subst h2
  exact hf ((GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).2 N f 0 _ ha (hasQ_zero N))

theorem prod_ne_zero {N : ℕ} (hN : 0 < N) {κ : Type} (s : Finset κ) (u : κ → ℍ → ℂ)
    (hu : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a) : (fun τ => ∏ l ∈ s, u l τ) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    have := congrFun h UpperHalfPlane.I
    simp at this
  | insert x s hx ih =>
    have hs : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a := fun l hl => hu l (Finset.mem_insert_of_mem hl)
    have hQ : ∃ b, HasQ N (fun τ => ∏ l ∈ s, u l τ) b :=
      (hasQ_of_qConj ((GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure (RingEquiv.refl ℂ) N hN).2.2.2.2.2 κ s u u
        fun l hl => qConj_refl (hs l hl).2).2).1
    intro h
    have hprod : ∀ τ, u x τ * (∏ l ∈ s, u l τ) = 0 := fun τ => by
      have := congrFun h τ
      simpa [Finset.prod_insert hx] using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff (u x) _ (mdiff_of_hasQ hN (hu x (Finset.mem_insert_self x s)).2)
      (mdiff_of_hasQ hN hQ) hprod with h1 | h1
    · exact (hu x (Finset.mem_insert_self x s)).1 h1
    · exact ih hs h1

end GlobalTheory.FN.Lag

namespace GlobalTheory.FN.Lag


open Finset in
theorem conj_family_of_injective : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → Function.Injective t → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hb hb' ht ht' hF hinj htt' hFq
  classical
  have hR := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hRr := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure (RingEquiv.refl ℂ) N hN
  have hA := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act'

  obtain ⟨c, hc, hlag⟩ := GlobalTheory.T.modular_form_symmetric_function_decomp ι act m k N t F hN hb ht hF (fun i => (hasQ_of_qConj (htt' i)).1) hFq
  choose c' hc' using fun j => GlobalTheory.T.exists_qConj_level_one_invariant g (k + m * j) N (c j) hN (hc j).1 (hc j).2

  obtain ⟨s, hs, hmin⟩ := GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant ι act k N F ⊤ hN hb hF
    (fun i => let ⟨a, ha⟩ := hFq i; ⟨a, ha, fun _ => Subring.mem_top _⟩)
  choose s' hs' using fun j : Fin (Fintype.card ι) => GlobalTheory.T.exists_qConj_level_one_invariant g (k * (Fintype.card ι - j)) N (s j) hN (hs j).1
    (let ⟨a, ha, _⟩ := (hs j).2; ⟨a, ha⟩)

  obtain ⟨D, hD⟩ : ∃ D : ι → ℍ → ℂ, ∀ i, D i = fun τ => ∏ l ∈ univ.erase i, (t i τ - t l τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ι → ℍ → ℂ, ∀ i, D' i = fun τ => ∏ l ∈ univ.erase i, (t' i τ - t' l τ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ι → ℍ → ℂ, ∀ i, A i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  obtain ⟨A', hA'd⟩ : ∃ A' : ι → ℍ → ℂ, ∀ i, A' i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c' j τ * t' i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  have hDD : ∀ i, QConj g N (D i) (D' i) := fun i => by
    rw [hD i, hD' i]
    exact (hR.2.2.2.2.2 ι (univ.erase i) (fun l τ => t i τ - t l τ) (fun l τ => t' i τ - t' l τ)
      (fun l _ => hR.2.2.1 _ _ _ _ (htt' i) (htt' l))).2
  have hAA : ∀ i, QConj g N (A i) (A' i) := fun i => by
    rw [hAd i, hA'd i]
    exact (hR.2.2.2.2.2 ℕ (range (Fintype.card ι)) (fun j τ => c j τ * t i τ ^ (Fintype.card ι - 1 - j))
      (fun j τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j))
      (fun j _ => hR.2.2.2.1 _ _ _ _ (hc' j).2 (hR.2.2.2.2.1 _ _ _ (htt' i)))).1
  have hDne : ∀ i, D i ≠ 0 := fun i => by
    rw [hD i]
    refine prod_ne_zero hN (univ.erase i) (fun l τ => t i τ - t l τ) fun l hl => ⟨?_, ?_⟩
    · intro h
      apply Finset.ne_of_mem_erase hl
      apply hinj
      funext τ
      have := congrFun h τ
      simp only [Pi.zero_apply] at this
      exact (sub_eq_zero.mp this).symm
    · exact (hasQ_of_qConj (hRr.2.2.1 _ _ _ _ (qConj_refl (hasQ_of_qConj (htt' i)).1)
        (qConj_refl (hasQ_of_qConj (htt' l)).1))).1
  have hD'ne : ∀ i, D' i ≠ 0 := fun i => qConj_ne_zero hN (hDD i) (hDne i)

  choose F' hF'1 hF'2 using fun i => GlobalTheory.T.exists_coeffwiseConjugate_of_integral_quotient g N (Fintype.card ι) (F i) (D i) (D' i) (A i) (A' i) s s' hN
    (hFq i) (hDD i) (hAA i) (fun j => (hs' j).2) (hDne i)
    (fun τ => by simp only [hD, hAd]; exact hlag i τ) (fun τ => hmin i τ)
  refine ⟨F', ?_, hF'1⟩

  have hv := (GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values ι act' m t').1 ht'
  have hD'fam : IsFam act' ((m * (Fintype.card ι - 1) : ℕ) : ℤ) D' := by
    rw [GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values]
    intro i γ τ
    simp only [hD', hv]
    set X : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)
    have e : ∀ l ∈ univ.erase i, X ^ (m : ℤ) * t' (act' i γ) τ - X ^ (m : ℤ) * t' (act' l γ) τ =
        X ^ (m : ℤ) * (t' (act' i γ) τ - t' (act' l γ) τ) := fun _ _ => by ring
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ]
    congr 1
    · rw [← zpow_natCast, ← zpow_mul]
      push_cast
      ring_nf
    · apply Finset.prod_nbij (fun l => act' l γ)
      · intro l hl
        exact Finset.mem_erase.mpr ⟨fun h => Finset.ne_of_mem_erase hl ((hb' γ).1 h), mem_univ _⟩
      · intro l _ l' _ h
        exact (hb' γ).1 h
      · intro y hy
        obtain ⟨l, hl⟩ := (hb' γ).2 y
        refine ⟨l, ?_, hl⟩
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun h => ?_, mem_univ _⟩)
        subst h
        exact Finset.ne_of_mem_erase (Finset.mem_coe.mp hy) hl.symm
      · intro l _
        rfl
  have hA'fam : IsFam act' ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) A' := by
    have e : A' = fun i τ => ∑ j ∈ range (Fintype.card ι), (fun j i τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j)) j i τ := by
      funext i τ
      rw [hA'd i]
    rw [e]
    refine hA.2.2.2.2.2.1 ℕ _ _ _ fun j hj => ?_
    have hj' : j < Fintype.card ι := Finset.mem_range.mp hj
    have hw : ((k + m * j : ℕ) : ℤ) + ((Fintype.card ι - 1 - j : ℕ) : ℤ) * (m : ℤ) =
        ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_sub_one_of_lt hj')
      rw [hr, show j + r - j = r by omega]
      push_cast
      ring
    rw [← hw]
    exact hA.2.2.2.1 _ _ (fun _ => c' j) (fun i τ => t' i τ ^ (Fintype.card ι - 1 - j))
      (fun _ γ => (hc' j).1 γ) (hA.2.2.2.2.1 _ _ _ ht')
  intro i γ
  have e1 : (F' i ∣[(k : ℤ)] γ) * (D' i ∣[((m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ) =
      A' i ∣[((k + m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ := by
    rw [show ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) = (k : ℤ) + ((m * (Fintype.card ι - 1) : ℕ) : ℤ) by push_cast; ring,
      ← ModularForm.mul_slash_SL2]
    congr 1
    funext τ
    exact hF'2 i τ
  rw [hD'fam i γ, hA'fam i γ] at e1
  have hz : ∀ τ, ((F' i ∣[(k : ℤ)] γ) τ - F' (act' i γ) τ) * D' (act' i γ) τ = 0 := fun τ => by
    have := congrFun e1 τ
    simp only [Pi.mul_apply] at this
    rw [sub_mul, this, hF'2, sub_self]
  have hol1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F' i ∣[(k : ℤ)] γ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 i)).2) _ _
  rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ (hol1.sub (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 (act' i γ))).2))
    (mdiff_of_hasQ hN (hasQ_of_qConj (hDD (act' i γ))).2) hz with h | h
  · funext τ
    exact sub_eq_zero.mp (congrFun h τ)
  · exact absurd h (hD'ne _)

end GlobalTheory.FN.Lag
end
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.approxPthRoot_fixedField_cyclotomic_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ApproxRoot p v (Fix Ω (⨅ n, Gn T n)) := by
  first | exact @GlobalTheory.K5.TopRoots.approxRoot_fix_tower | exact GlobalTheory.K5.TopRoots.approxRoot_fix_tower | (intros; apply GlobalTheory.K5.TopRoots.approxRoot_fix_tower <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.almostPurity_moves_integers_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_of_ne_one | exact GlobalTheory.AlmostEt.moves_of_ne_one | (intros; apply GlobalTheory.AlmostEt.moves_of_ne_one <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq : ∀ (L : ℕ) (v : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ), 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x => ‖G x‖) → (Summable fun x => ‖dif L v G x‖) ∧ ∑' x, Φ x * dif L v G x = ∑' x, Φ x * G x := by
  first | exact @GlobalTheory.EisM.kills_sum_dif_eq | exact GlobalTheory.EisM.kills_sum_dif_eq | (intros; apply GlobalTheory.EisM.kills_sum_dif_eq <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth : ∀ a : ℕ → ℂ, PolyB a → Mod (qs a) := by
  first | exact @GlobalTheory.EisM.mod_qs_of_polyB | exact GlobalTheory.EisM.mod_qs_of_polyB | (intros; apply GlobalTheory.EisM.mod_qs_of_polyB <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ), 1 ≤ k → 0 < l → MF k N (ch ε) h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  first | exact @GlobalTheory.EisM.adjU_sum | exact GlobalTheory.EisM.adjU_sum | (intros; apply GlobalTheory.EisM.adjU_sum <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.eigenvector_eq_zero_of_mem_twistedSpan_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  first | exact @GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain | exact GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain | (intros; apply GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), (CF k N (ch χ) g → CF k N (ch χ⁻¹) (fun n => conj (g n))) ∧ (Prim k N χ g → Prim k N χ⁻¹ (fun n => conj (g n))) := by
  first | exact @GlobalTheory.EisM.ConjForm.conj_form | exact GlobalTheory.EisM.ConjForm.conj_form | (intros; apply GlobalTheory.EisM.ConjForm.conj_form <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities : ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l → (∀ a b : ℕ → R, Uo l (mul a (Vo l b)) = mul (Uo l a) b) ∧ (∀ a b : ℕ → R, Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b)) ∧ (∀ a b : ℕ → R, mul a b = mul b a) ∧ (∀ (a b b' : ℕ → R) (c c' : R), mul a (c • b + c' • b') = c • mul a b + c' • mul a b') ∧ (∀ (k q : ℕ) (c : R) (a : ℕ → R), q.Coprime l → 0 < q → To k c q (Vo l a) = Vo l (To k c q a)) ∧ (∀ (B : ℕ) (c a b : ℕ → R) (x y : R), lam B c (x • a + y • b) = x * lam B c a + y * lam B c b) := by
  first | exact @GlobalTheory.EisM.formal_identities | exact GlobalTheory.EisM.formal_identities | (intros; apply GlobalTheory.EisM.formal_identities <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.norm_trm_sub_trm_add_le : ∀ j : ℕ, ∃ C : ℝ, ∀ (s : ℝ) (z a : ℂ), 0 ≤ s → s ≤ 1 → 1 ≤ ‖z‖ → 2 * ‖a‖ ≤ ‖z‖ → ‖trm j s z - trm j s (z + a)‖ ≤ C * ‖a‖ / ‖z‖ ^ (j + 1) := by
  first | exact @GlobalTheory.EisM.TermDiff.first_diff | exact GlobalTheory.EisM.TermDiff.first_diff | (intros; apply GlobalTheory.EisM.TermDiff.first_diff <;> assumption)
end
