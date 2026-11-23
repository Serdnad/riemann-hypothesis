module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.AdicCompletion.LocalRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.K5

namespace GlobalTheory.K5

theorem dvr_of_separated {S : Type*} [CommRing S] (π : S) (hn : ∀ n : ℕ, π ^ n ≠ 0)
    (hnu : ¬ IsUnit π) (hu : ∀ x, ¬ π ∣ x → IsUnit x) (hsep : ∀ x, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      exact hx (hsep x fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (h n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · have := Nat.find_min hex (m := m) (by omega)
        simpa using this
    obtain ⟨u, hxu⟩ := h1
    refine ⟨Nat.find hex, u, hu u ?_, hxu⟩
    rintro ⟨v, hv⟩
    exact Nat.find_spec hex ⟨v, by rw [pow_succ, mul_assoc, ← hv]; exact hxu⟩
  have : Nontrivial S := ⟨⟨π ^ 0, 0, hn 0⟩⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨a, u, hu', rfl⟩ := hfac x h.1
    obtain ⟨b, v, hv', rfl⟩ := hfac y h.2
    apply hn (a + b)
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ((hu'.mul hv').mul_left_eq_zero).1 this⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by simpa using hn 1
  have hprime : Prime π := by
    refine ⟨hπ0, hnu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    exact hnu (isUnit_of_dvd_unit hab ((hu a h.1).mul (hu b h.2)))
  refine ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hprime.irreducible, fun {x} hx => ?_⟩, hprime.irreducible⟩
  obtain ⟨n, u, hu', rfl⟩ := hfac x hx
  exact ⟨n, hu'.unit, rfl⟩

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0)
    (hmax : (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a}).IsMaximal) :
    ∃ _ : IsDomain (AdicCompletion (Ideal.span {a}) R),
      IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R) ∧
        Irreducible (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  have fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton _
  have hc := AdicCompletion.isAdicComplete_self (Ideal.span {a}) fg
  rw [Ideal.map_span, Set.image_singleton] at hc
  have hnu : ¬ IsUnit (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := fun h =>
    hmax.ne_top (Ideal.span_singleton_eq_top.2 h)
  have := isLocalRing_of_isAdicComplete_maximal
    (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
  refine dvr_of_separated _ (fun n hn => ?_) hnu (fun x hx => ?_) (fun x hx => ?_)
  · rw [← map_pow] at hn
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hn
    rw [AlgHom.commutes, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ] at h2
    have h3 : a ^ n * a ∣ a ^ n * 1 := by simpa using h2
    exact hnu ((isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n ha)).1 h3)).map _)
  · by_contra hxu
    have : x ∈ IsLocalRing.maximalIdeal _ := hxu
    rw [← IsLocalRing.eq_maximalIdeal hmax, Ideal.mem_span_singleton] at this
    exact hx this
  · refine hc.toIsHausdorff.haus' x fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx n

theorem completed_laurent_isDVR (p : ℕ) [Fact p.Prime] :
    ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  have hp : (p : Lau p) ≠ 0 := by
    have h : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [← map_natCast (HahnSeries.C : ℤ_[p] →+* Lau p)]
    exact HahnSeries.C_ne_zero h
  obtain ⟨e⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have := adicCompletion_dvr (p : Lau p) hp (by rw [map_natCast]; exact hmax)
  rw [map_natCast] at this
  exact this

end GlobalTheory.K5
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem index_comap_toSpanSingleton_ne_zero {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) {y : X} (hy : y ∈ B) :
    (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index ≠ 0 := by
  have h1 : (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup =
      A.toAddSubgroup.comap (LinearMap.toSpanSingleton R X y).toAddMonoidHom := rfl
  rw [h1, AddSubgroup.index_comap]
  intro h0
  refine hAB (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨r, rfl⟩
  exact B.smul_mem r hy

theorem exists_mem_maximal_annihilator {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) (hBA : ¬ B ≤ A) :
    ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ ∀ r : R, r • x ∈ A ↔ r ∈ P := by
  have hex : ∃ n, ∃ y ∈ B, y ∉ A ∧
      (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index = n := by
    obtain ⟨y, hyB, hyA⟩ := SetLike.not_le_iff_exists.1 hBA
    exact ⟨_, y, hyB, hyA, rfl⟩
  obtain ⟨x, hxB, hxA, hx⟩ := Nat.find_spec hex
  have hne := index_comap_toSpanSingleton_ne_zero A B hAB hxB
  let P : Ideal R := A.comap (LinearMap.toSpanSingleton R X x)
  have hP : ∀ r : R, r • x ∈ A ↔ r ∈ P := fun r => Iff.rfl
  have hfin : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero hne
  have hprime : P.IsPrime := by
    refine ⟨fun htop => hxA ?_, fun {r s} hrs => ?_⟩
    · have : (1 : R) ∈ P := htop ▸ Submodule.mem_top
      simpa using (hP 1).2 this
    · by_contra hcon
      rw [not_or] at hcon
      have hs : s • x ∉ A := fun h => hcon.2 ((hP s).1 h)
      have hmin := Nat.find_min' hex ⟨s • x, B.smul_mem s hxB, hs, rfl⟩
      have hne' := index_comap_toSpanSingleton_ne_zero A B hAB (B.smul_mem s hxB)
      have hle : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup ≤
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        intro a ha
        have ha' : a • x ∈ A := ha
        show a • s • x ∈ A
        rw [smul_comm]
        exact A.smul_mem s ha'
      have hmul := AddSubgroup.relIndex_mul_index hle
      rw [← hx, ← hmul] at hmin
      have h1 : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup.relIndex
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup = 1 := by
        rw [← hmul] at hne
        have h2 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hne)
        have h3 := Nat.pos_of_ne_zero hne'
        nlinarith
      rw [AddSubgroup.relIndex_eq_one] at h1
      have hr : r ∈ (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        show r • s • x ∈ A
        rw [smul_smul]
        exact (hP _).2 hrs
      exact hcon.1 (h1 hr)
  haveI := hprime
  exact ⟨x, hxB, P, Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain _), hfin, hP⟩

theorem exists_adj_selfDual_step : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hA hB hAB hBA
  obtain ⟨x, hxB, P, hPm, hPf, hP⟩ := exists_mem_maximal_annihilator A B hAB hBA
  let T : Submodule R X := Submodule.span R {x}
  have hTB : T ≤ B := (Submodule.span_singleton_le_iff_mem x B).2 hxB
  have hxT : x ∈ T := Submodule.mem_span_singleton_self x
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]
        exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hS : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSA : S ≤ A := fun a ha => ha.1
  have hidx : A.toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := fun h0 =>
    hAB (AddSubgroup.relIndex_eq_zero_of_le_right (fun t ht => hTB ht) h0)
  obtain ⟨-, hdual, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup (fun a ha => ⟨fun h1 => h1.2, fun h1 => ⟨ha, h1⟩⟩)
    (fun t _ => ⟨fun h1 a ha => h.iso hA ha h1,
      fun h1 => (hA t).2 fun a ha => h.swap_eq_one (h1 a ha)⟩) hidx
  refine ⟨S ⊔ T, fun y => ⟨fun hy z hz => ?_, fun hy => ?_⟩,
    ⟨x, Submodule.mem_sup_right hxT, P, hPm, hPf, hP, ?_⟩, ?_⟩
  · obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, hb, u, hu, rfl⟩ := Submodule.mem_sup.1 hz
    rw [h.add_left, h.add_right, h.add_right, h.iso hA ha.1 hb.1, ha.2 u hu,
      h.swap_eq_one (hb.2 t ht), h.iso hB (hTB ht) (hTB hu)]
    simp
  · obtain ⟨t, ht, hyt⟩ := hdual y fun a _ ha =>
      h.swap_eq_one (hy a (Submodule.mem_sup_left ha))
    have ht' : t ∈ T := ht
    have h1 : y + -t ∈ S := by
      refine ⟨(hA _).2 fun a ha => h.swap_eq_one ?_, fun u hu => ?_⟩
      · rw [h.add_right, h.neg_right, hyt a ha, mul_inv_cancel₀ (h.ne_zero _ _)]
      · rw [h.add_left, hy u (Submodule.mem_sup_right hu),
          h.iso hB (B.neg_mem (hTB ht')) (hTB hu), one_mul]
    exact Submodule.mem_sup.2 ⟨_, h1, t, ht', by abel⟩
  · exact sup_le_sup_right (le_inf hSA le_sup_left) _
  · exact sup_le_sup (le_inf le_sup_left hSA) (le_inf le_sup_right hTB)

end GlobalTheory.FinWeil
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private lemma existsUnique_quotient_sub_smul_mem {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (P : Ideal R)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x}) :
    ∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A := by
  intro b hb
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨Ideal.Quotient.mk P r, ?_, ?_⟩
  · have h1 : (r - Quotient.out (Ideal.Quotient.mk P r)) • x ∈ A := by
      rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
    have h2 : c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x =
        c + (r - Quotient.out (Ideal.Quotient.mk P r)) • x := by
      rw [sub_smul]; abel
    show c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x ∈ A
    rw [h2]
    exact A.add_mem (Submodule.mem_inf.1 hc).1 h1
  · intro q hq
    have h2 : (r - Quotient.out q) • x ∈ A := by
      have h3 : (r - Quotient.out q) • x = (c + r • x - Quotient.out q • x) - c := by
        rw [sub_smul]; abel
      rw [h3]
      exact A.sub_mem hq (Submodule.mem_inf.1 hc).1
    rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out] at h2
    exact h2.symm

open Classical in
open scoped BigOperators in
private lemma le_or_eq_of_inf_le_of_le_of_isMaximal {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (hx : x ∈ B) (P : Ideal R) (hP : P.IsMaximal)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x})
    (T : Submodule R X) (h1 : A ⊓ B ≤ T) (h2 : T ≤ B) : T ≤ A ∨ T = B := by
  by_cases hTA : T ≤ A
  · exact Or.inl hTA
  right
  obtain ⟨t, htT, htA⟩ := Set.not_subset.1 hTA
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle (h2 htT))
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hr : r ∉ P := fun hr => htA (A.add_mem (Submodule.mem_inf.1 hc).1 ((hxP r).2 hr))
  obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hr
  have hrx : r • x ∈ T := by
    have h3 := T.sub_mem htT (h1 hc)
    rwa [add_sub_cancel_left] at h3
  have hix : i • x ∈ T := h1 (Submodule.mem_inf.2 ⟨(hxP i).2 hi, B.smul_mem i hx⟩)
  have hxT : x ∈ T := by
    have h4 : x = s • r • x + i • x := by rw [smul_smul, ← add_smul, hsi, one_smul]
    rw [h4]
    exact T.add_mem (T.smul_mem s hrx) hix
  refine le_antisymm h2 (hBle.trans (sup_le h1 ?_))
  rw [Submodule.span_singleton_le_iff_mem]
  exact hxT

open Classical in
open scoped BigOperators in
private lemma toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) ∧ _root_.GlobalTheory.FinWeil.idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB x hx P hP hfin hxP hBle
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hrep := existsUnique_quotient_sub_smul_mem A B x P hxP hBle
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB : _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) := by
    haveI := Fintype.ofFinite (R ⧸ P)
    rw [Nat.card_eq_fintype_card]
    exact (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB (0 : M) (fun a _ => map_zero (W a)) (R ⧸ P)
      (fun q => Quotient.out q • x) (fun q => B.smul_mem _ hx) hrep).2
  have hAB' : A.toAddSubgroup.relIndex B.toAddSubgroup = Nat.card (R ⧸ P) := hAB
  have hBA : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup A.toAddSubgroup
      B.toAddSubgroup (fun a _ => by simpa only [Submodule.mem_toAddSubgroup] using hB' a)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup] at ht ⊢
        rw [hA' t]
        exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
          fun h a ha => hW.swap_eq_one (h a ha)⟩)
      (by rw [hAB']; exact hN)).1
    rw [key, hAB']
  have hdich := le_or_eq_of_inf_le_of_le_of_isMaximal A B x hx P hP hxP hBle
  refine ⟨hAB, hBA, hrep, hdich, ?_⟩
  intro T h1 h2
  by_cases hTB : T ≤ B
  · exact Or.inl hTB
  right
  let T' : Submodule R X :=
    { carrier := {b | b ∈ B ∧ ∀ t ∈ T, γ t b = 1}
      add_mem' := fun {b b'} hb hb' => ⟨B.add_mem hb.1 hb'.1, fun t ht => by
        rw [hW.add_right, hb.2 t ht, hb'.2 t ht, one_mul]⟩
      zero_mem' := ⟨B.zero_mem, fun t _ => hW.zero_right t⟩
      smul_mem' := fun r b hb => ⟨B.smul_mem r hb.1, fun t ht => by
        have h3 := hW.adj (σ r) t b
        rw [hW.sg_sg] at h3
        rw [← h3]
        exact hb.2 _ (T.smul_mem _ ht)⟩ }
  have hmemT' : ∀ b, b ∈ T' ↔ b ∈ B ∧ ∀ t ∈ T, γ t b = 1 := fun b => Iff.rfl
  have hT'1 : A ⊓ B ≤ T' := fun c hc => (hmemT' c).2
    ⟨(Submodule.mem_inf.1 hc).2, fun t ht =>
      hW.iso hA (h2 ht) (Submodule.mem_inf.1 hc).1⟩
  have hT'2 : T' ≤ B := fun b hb => ((hmemT' b).1 hb).1
  rcases hdich T' hT'1 hT'2 with hle | heq
  · have hT'eq : T' = A ⊓ B := le_antisymm (le_inf hle hT'2) hT'1
    have hprod : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup *
        T.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
      rw [AddSubgroup.relIndex_mul_relIndex (A ⊓ B).toAddSubgroup T.toAddSubgroup
        A.toAddSubgroup (fun y hy => h1 hy) (fun y hy => h2 hy),
        toAddSubgroup_inf, AddSubgroup.inf_relIndex_left, hBA]
    have hne : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hprod; exact hN hprod.symm
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T'.toAddSubgroup B.toAddSubgroup
      (A ⊓ B).toAddSubgroup T.toAddSubgroup
      (fun b hb => by
        simp only [Submodule.mem_toAddSubgroup] at hb ⊢
        rw [hmemT']
        exact ⟨fun h t ht => hW.swap_eq_one (h.2 t ht),
          fun h => ⟨hb, fun t ht => hW.swap_eq_one (h t ht)⟩⟩)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf] at ht ⊢
        rw [hB' t]
        exact ⟨fun h b hb => hW.swap_eq_one (h.2 b hb),
          fun h => ⟨h2 ht, fun b hb => hW.swap_eq_one (h b hb)⟩⟩)
      hne).1
    rw [hT'eq, toAddSubgroup_inf, AddSubgroup.inf_relIndex_right, hAB',
      ← toAddSubgroup_inf] at key
    rw [← key] at hprod
    have hone : T.toAddSubgroup.relIndex A.toAddSubgroup = 1 := by
      have h5 : Nat.card (R ⧸ P) * T.toAddSubgroup.relIndex A.toAddSubgroup =
          Nat.card (R ⧸ P) * 1 := by rw [hprod, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h5
    have hAT := AddSubgroup.relIndex_eq_one.1 hone
    exact le_antisymm h2 (fun a ha => hAT ha)
  · exfalso
    apply hTB
    intro t ht
    rw [hB' t]
    intro b hb
    rw [← heq] at hb
    exact ((hmemT' b).1 hb).2 t ht

end GlobalTheory.FinWeil
end

section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem span_translates_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, (∀ v, Fixes W A v → ∃ c : ℂ, v = c • e) → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W h A hA e he hsm
  rw [eq_top_iff]
  intro v _
  obtain ⟨T, hT, hv⟩ := hsm v
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, mul_one]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]; exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hSm : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSv : Fixes W S v := fun a ha => hv a ha.1 ha.2
  have hSt : ∀ t ∈ T, Fixes W S (W (-t) v) := by
    intro t ht a ha
    rw [h.comm, ha.2 _ (T.neg_mem ht), one_smul, hSv a ha]
  obtain ⟨h1, -, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup
    (fun a ha => ⟨fun hs => hs.2, fun hs => ⟨ha, hs⟩⟩)
    (fun t _ => ⟨fun ht a ha => h.iso hA ha ht,
      fun ht => (hA t).2 fun a ha => h.swap_eq_one (ht a ha)⟩) hT
  have hn : idx S A ≠ 0 := by
    unfold idx
    rw [h1]
    exact hT
  obtain ⟨-, -, h2⟩ := perfect_pairing_quotients h A.toAddSubgroup T.toAddSubgroup
    S.toAddSubgroup A.toAddSubgroup
    (fun t _ => hA t)
    (fun a ha => ⟨fun hs t ht => h.swap_eq_one (hs.2 t ht),
      fun hs => ⟨ha, fun t ht => h.swap_eq_one (hs t ht)⟩⟩) hn
  obtain ⟨t1, t2, -⟩ := sumOp_transversal h S A hA
  obtain ⟨⟨m, f, hf, hu⟩, hfix, -⟩ := t2 hn
  have hg : ∀ t ∈ T, ∑ i, γ t (f i) • W (f i) v ∈ Submodule.span ℂ (Set.range fun x => W x e) := by
    intro t ht
    obtain ⟨c, hc⟩ := he _ (hfix _ (hSt t ht))
    rw [(t1 _ (hSt t ht) _ f hf hu).1] at hc
    have h3 := congrArg (W t) hc

    rw [map_sum, map_smul] at h3
    have h4 : ∀ i, W t (W (f i) (W (-t) v)) = γ (w • t) (-t) • (γ t (f i) • W (f i) v) := by
      intro i
      rw [h.comm, h.comp t (-t), add_neg_cancel, h.zero, map_smul, smul_comm]
    rw [Finset.sum_congr rfl fun i _ => h4 i, ← Finset.smul_sum] at h3
    rw [← Submodule.smul_mem_iff _ (h.ne_zero (w • t) (-t)), h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  haveI : Finite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hT
  letI := Fintype.ofFinite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)
  have h5 := Submodule.sum_mem (Submodule.span ℂ (Set.range fun x => W x e))
    (t := (Finset.univ : Finset
      (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)))
    (fun q _ => hg _ (Quotient.out q : T.toAddSubgroup).2)
  rw [Finset.sum_comm] at h5
  obtain ⟨i₀, hi₀, hi⟩ := hu 0 A.zero_mem
  simp only [zero_sub, neg_mem_iff] at hi₀ hi
  have h6 : ∀ i, ∑ q : T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup,
      γ ((Quotient.out q : T.toAddSubgroup) : X) (f i) • W (f i) v
      = if i = i₀ then (idx A T : ℂ) • v else 0 := by
    intro i
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, h2 _ (hf i)]
    by_cases hii : i = i₀
    · subst hii
      rw [if_pos rfl, if_pos (show f i ∈ S.toAddSubgroup from hi₀), hSv _ hi₀]
      rfl
    · rw [if_neg hii, if_neg (fun hh : f i ∈ S.toAddSubgroup => hii (hi i hh)), zero_smul]
  rw [Finset.sum_congr rfl fun i _ => h6 i, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h5
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hT)).1 h5

end GlobalTheory.FinWeil
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_levelOne_form_one_add_expDecay : ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧ (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.levelOne_form_one_add_expDecay | exact GlobalTheory.levelOne_form_one_add_expDecay | (intros; apply GlobalTheory.levelOne_form_one_add_expDecay <;> assumption)
end
