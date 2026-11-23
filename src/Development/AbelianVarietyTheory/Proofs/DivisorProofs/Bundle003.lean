module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory.Poinc

open IsLocalRing in
variable {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] in
private theorem mem_of_forall_mem_sup_maximalIdeal_pow' (N : Ideal V) (x : V)
    (hx : ∀ e : ℕ, x ∈ N ⊔ maximalIdeal V ^ e) : x ∈ N := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := V) (M := V ⧸ N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmem : Ideal.Quotient.mk N x ∈
      ⨅ i : ℕ, (maximalIdeal V ^ i • ⊤ : Submodule V (V ⧸ N)) := by
    refine Submodule.mem_iInf _ |>.2 fun e => ?_
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 (hx e)
    have h1 : Ideal.Quotient.mk N (a + y) = y • Ideal.Quotient.mk N 1 := by
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, Algebra.smul_def, map_one,
        mul_one]
      rfl
    rw [h1]
    exact Submodule.smul_mem_smul hy Submodule.mem_top
  rw [hbot] at hmem
  exact hmem

open IsLocalRing in
variable {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] in
private theorem exists_not_mem_span_mul_maximalIdeal_sup_pow [IsDomain V] {g : V} (hg : g ≠ 0) :
    ∃ e : ℕ, g ∉ Ideal.span {g} * maximalIdeal V ⊔ maximalIdeal V ^ e := by
  by_contra h
  push_neg at h
  have hg' := mem_of_forall_mem_sup_maximalIdeal_pow' _ g h
  obtain ⟨z, hz, hgz⟩ := Ideal.mem_span_singleton_mul.1 hg'
  have hz1 : z = 1 := by
    have : g * (z - 1) = 0 := by rw [mul_sub, hgz, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hg
    · exact sub_eq_zero.1 h0
  exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))


open IsLocalRing in
theorem _root_.GlobalTheory.Poinc.const_mod_prime_of_approx (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] [IsNoetherianRing V] (p : Ideal V) [p.IsPrime] (O' : Subring V)
    (hO : ∀ h ∈ O', h ∈ maximalIdeal V → h ∈ p) (g b u : V) (I : Ideal V) (hg : g ≠ 0)
    (hI : I ≤ maximalIdeal V)
    (H : ∀ e : ℕ, ∃ h ∈ O',
      h * g - u * (b * g) ∈ Ideal.span {b * g} * I ⊔ maximalIdeal V ^ e) :
    (IsUnit u → b ∈ maximalIdeal V → b ∈ p) ∧ (I ≤ p → ∃ h ∈ O', h - u * b ∈ p) := by
  obtain ⟨e₀, he₀⟩ := exists_not_mem_span_mul_maximalIdeal_sup_pow hg
  choose a haO haH using H
  have hspan : Ideal.span {b * g} ≤ Ideal.span {g} :=
    Ideal.span_singleton_le_span_singleton.2 ⟨b, mul_comm b g⟩
  have hbgI : Ideal.span {b * g} * I ≤ Ideal.span {g} * maximalIdeal V := Ideal.mul_mono hspan hI
  have hpow : ∀ {e : ℕ}, e₀ ≤ e → maximalIdeal V ^ e ≤ maximalIdeal V ^ e₀ :=
    fun h => Ideal.pow_le_pow_right h

  have hunit : ∀ x ∈ O', x * g ∈ Ideal.span {g} * maximalIdeal V ⊔ maximalIdeal V ^ e₀ →
      x ∈ p := by
    intro x hxO hx
    by_contra hxp
    have hxu : IsUnit x := by
      by_contra hnu
      exact hxp (hO x hxO ((mem_maximalIdeal x).2 hnu))
    apply he₀
    have key : ((hxu.unit⁻¹ : Vˣ) : V) * (x * g) = g := by
      rw [← mul_assoc, hxu.val_inv_mul, one_mul]
    have hmul := Ideal.mul_mem_left _ ((hxu.unit⁻¹ : Vˣ) : V) hx
    rwa [key] at hmul
  refine ⟨fun hu hb => ?_, fun hIp => ?_⟩
  · have hap : ∀ e, e₀ ≤ e → a e ∈ p := by
      intro e he
      refine hunit (a e) (haO e) ?_
      have h1 : a e * g = (a e * g - u * (b * g)) + g * (u * b) := by ring
      rw [h1]
      refine Ideal.add_mem _ ?_ (Ideal.mem_sup_left (Ideal.mem_span_singleton_mul.2
        ⟨u * b, Ideal.mul_mem_left _ _ hb, rfl⟩))
      exact sup_le_sup hbgI (hpow he) (haH e)
    have hN : u * (b * g) ∈ Ideal.span {g} * p ⊔ Ideal.span {b * g} * maximalIdeal V := by
      refine mem_of_forall_mem_sup_maximalIdeal_pow' _ _ fun e => ?_
      have h1 : u * (b * g) = g * a (max e e₀) - (a (max e e₀) * g - u * (b * g)) := by ring
      rw [h1]
      refine Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left
        (Ideal.mem_span_singleton_mul.2 ⟨_, hap _ (le_max_right _ _), rfl⟩))) ?_
      refine sup_le_sup (le_sup_of_le_right (Ideal.mul_mono_right hI))
        (Ideal.pow_le_pow_right (le_max_left e e₀)) (haH (max e e₀))
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hN
    obtain ⟨q, hq, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
    obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
    have hcancel : b * (u - r) = q := by
      apply mul_left_cancel₀ hg
      linear_combination hyz.symm
    have hur : IsUnit (u - r) := by
      by_contra hnu
      have hm : u - r ∈ maximalIdeal V := (mem_maximalIdeal _).2 hnu
      have : u ∈ maximalIdeal V := by
        simpa using Ideal.add_mem _ hm hr
      exact (mem_maximalIdeal u).1 this hu
    rcases (inferInstance : p.IsPrime).mem_or_mem (hcancel ▸ hq) with h | h
    · exact h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hur) (inferInstance : p.IsPrime).ne_top
  · have hdiff : ∀ e, e₀ ≤ e → a e - a e₀ ∈ p := by
      intro e he
      refine hunit _ (Subring.sub_mem _ (haO e) (haO e₀)) ?_
      have h1 : (a e - a e₀) * g =
          (a e * g - u * (b * g)) - (a e₀ * g - u * (b * g)) := by ring
      rw [h1]
      exact Ideal.sub_mem _ (sup_le_sup hbgI (hpow he) (haH e)) (sup_le_sup hbgI le_rfl (haH e₀))
    refine ⟨a e₀, haO e₀, ?_⟩
    have hN : (a e₀ - u * b) * g ∈ Ideal.span {g} * p := by
      refine mem_of_forall_mem_sup_maximalIdeal_pow' _ _ fun e => ?_
      have h1 : (a e₀ - u * b) * g =
          g * (-(a (max e e₀) - a e₀)) + (a (max e e₀) * g - u * (b * g)) := by ring
      rw [h1]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_mul.2
        ⟨_, neg_mem (hdiff _ (le_max_right _ _)), rfl⟩)) ?_
      exact sup_le_sup (Ideal.mul_mono hspan hIp) (Ideal.pow_le_pow_right (le_max_left e e₀))
        (haH (max e e₀))
    obtain ⟨q, hq, hgq⟩ := Ideal.mem_span_singleton_mul.1 hN
    have : a e₀ - u * b = q := by
      apply mul_left_cancel₀ hg
      rw [hgq, mul_comm]
    exact this ▸ hq

end GlobalTheory.Poinc
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem smul_mem_of_maximalIdeal_pow_of_locally_eq :
    ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B]
      [Module.Finite R B] (N : Submodule R B),
      (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) →
      ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  intro R B _ _ _ _ _ _ N h
  classical
  set J : Ideal R := N.colon (Set.univ : Set B) with hJ
  have hmem : ∀ r : R, r ∈ J ↔ ∀ b : B, r • b ∈ N := by
    intro r
    rw [hJ, Submodule.mem_colon]
    simp
  have hrad : maximalIdeal R ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hJp, hp⟩
    by_cases hpm : p = maximalIdeal R
    · exact hpm.ge
    exfalso
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R B).FG)
    have hg : ∀ g : B, ∃ t ∉ p, t • g ∈ N := h p hp hpm
    choose t ht1 ht2 using hg
    set u : R := ∏ g ∈ s, t g with hu
    have hu_notin : u ∉ p := by
      rw [hu, Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact ht1 i hi
    apply hu_notin
    apply hJp
    rw [hmem]
    intro b
    have hb : b ∈ Submodule.span R (s : Set B) := by rw [hs]; trivial
    have hle : Submodule.span R (s : Set B) ≤ N.comap (u • LinearMap.id) := by
      rw [Submodule.span_le]
      intro g hgs
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hu, ← Finset.prod_erase_mul s t hgs, mul_smul]
      exact N.smul_mem _ (ht2 g)
    have := hle hb
    simpa using this
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (maximalIdeal R))
  exact ⟨k, fun x hx b => (hmem x).1 (hk hx) b⟩

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem adic_coeffs_tendsto_zero :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ M _ _ r s hs X z hz
  classical
  set m := maximalIdeal R

  have coef : ∀ (x : M) (k : ℕ), x ∈ (m ^ k • ⊤ : Submodule R M) →
      ∃ a : Fin r → R, x = ∑ j, a j • s j ∧ ∀ j, a j ∈ m ^ k := by
    intro x k hx
    rw [← hs, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, hsum⟩ := hx
    refine ⟨a, ?_, ha⟩
    rw [← hsum, Finsupp.sum_fintype]
    intro j; simp
  haveI : Module.Finite R M := ⟨by rw [← hs]; exact Submodule.fg_span (Set.finite_range s)⟩
  have krull : (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have anti : ∀ {a b : ℕ}, a ≤ b → (m ^ b • ⊤ : Submodule R M) ≤ m ^ a • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have choiceχ : ∀ χ, ∃ a : Fin r → R, z χ = ∑ j, a j • s j ∧
      ∀ n, (¬ ∀ j, a j ∈ m ^ n) → z χ ∉ (m ^ n • ⊤ : Submodule R M) := by
    intro χ
    by_cases h : ∃ n, z χ ∉ (m ^ n • ⊤ : Submodule R M)
    · set N := Nat.find h with hN
      have hN0 : N ≠ 0 := by
        intro h0
        have := Nat.find_spec h
        rw [← hN, h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul] at this
        exact this Submodule.mem_top
      have hmem : z χ ∈ (m ^ (N - 1) • ⊤ : Submodule R M) := by
        by_contra hc
        have := Nat.find_min' h hc
        omega
      obtain ⟨a, ha, hm⟩ := coef _ _ hmem
      refine ⟨a, ha, fun n hn hzn => hn fun j => ?_⟩
      have hlt : n < N := by
        by_contra hle
        push_neg at hle
        exact (Nat.find_spec h) (anti hle hzn)
      exact Ideal.pow_le_pow_right (by omega) (hm j)
    · push_neg at h
      have hz0 : z χ = 0 := by
        have : z χ ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr h
        rw [krull] at this
        exact (Submodule.mem_bot R).mp this
      refine ⟨0, by simp [hz0], fun n hn _ => hn fun j => ?_⟩
      simp
  choose c hc hbad using choiceχ
  refine ⟨c, hc, fun n => (hz n).subset ?_⟩
  intro χ hχ
  exact hbad χ n hχ

end GlobalTheory
end

section

open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem fg_of_saturated_ideal_power_into_image :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] (I : Ideal S),
      (∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ I ^ k, IsLocalization.IsInteger S (a • c)) →
        IsLocalization.IsInteger S c) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M]
        (N : Submodule S (FractionRing S ⊗[S] M)),
        (∀ z ∈ N, ∃ k : ℕ, ∀ a ∈ I ^ k,
          a • z ∈ LinearMap.range (TensorProduct.mk S (FractionRing S) M 1)) → N.FG := by
  intro S _ _ _ I hsat M _ _ _ N hN
  classical
  set K := FractionRing S
  let V := K ⊗[S] M
  let b := Module.Free.chooseBasis K V
  let ι := Module.Free.ChooseBasisIndex K V
  let T : V →ₗ[S] (ι → K) := (b.equivFun.toLinearMap).restrictScalars S

  let L : Submodule S (ι → K) := LinearMap.range ((Algebra.linearMap S K).compLeft ι)
  have memL : ∀ v : ι → K, (∀ i, IsLocalization.IsInteger S (v i)) → v ∈ L := by
    intro v hv
    choose w hw using hv
    exact ⟨w, funext fun i => hw i⟩
  have memL' : ∀ v ∈ L, ∀ i, IsLocalization.IsInteger S (v i) := by
    rintro v ⟨w, rfl⟩ i
    exact ⟨w i, rfl⟩
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := S) (M := M)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors S)
    (Finset.univ : Finset (Fin n × ι)) (fun p => T (1 ⊗ₜ g p.1) p.2)
  let F : V →ₗ[S] (ι → K) := (d : S) • T
  have hFM : ∀ m : M, F (1 ⊗ₜ m) ∈ L := by
    intro m
    have hle : Submodule.span S (Set.range g) ≤ L.comap (F ∘ₗ TensorProduct.mk S K M 1) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show F (1 ⊗ₜ g j) ∈ L
      apply memL
      intro i
      exact hd (j, i) (Finset.mem_univ _)
    have : m ∈ Submodule.span S (Set.range g) := by rw [hg]; trivial
    exact hle this
  have hFN : ∀ z ∈ N, F z ∈ L := by
    intro z hz
    obtain ⟨k, hk⟩ := hN z hz
    apply memL
    intro i
    apply hsat k
    intro a ha
    obtain ⟨m, hm⟩ := hk a ha
    have h1 := hFM m
    simp only [TensorProduct.mk_apply] at hm
    rw [hm, map_smul] at h1
    simpa using memL' _ h1 i
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hd0 : algebraMap S K (d : S) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have : algebraMap S K (d : S) • b.equivFun x = algebraMap S K (d : S) • b.equivFun y := by
      simpa [F, T, algebraMap_smul] using hxy
    exact b.equivFun.injective (smul_right_injective _ hd0 this)
  have hLfg : L.FG := by
    show (LinearMap.range ((Algebra.linearMap S K).compLeft ι)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian S L := isNoetherian_of_fg_of_noetherian L hLfg
  apply Submodule.fg_of_fg_map_injective F hFinj
  exact Submodule.FG.of_le_of_isNoetherian (T := L) (by
    rintro _ ⟨z, hz, rfl⟩
    exact hFN z hz)

end GlobalTheory
end

section

namespace GlobalTheory

theorem inf_sup_pow_eq_of_torsion : ∀ (B : Type) [CommRing B] [IsNoetherianRing B]
    (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  intro B _ _ K τ τ' hle htor
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian τ' : τ'.FG)
  have hrad : K ≤ (τ.colon (s : Set B)).radical := by
    intro f hf
    have hm : ∀ b ∈ s, ∃ m : ℕ, f ^ m * b ∈ τ := fun b hb =>
      htor b (hs ▸ Submodule.subset_span hb) f hf
    choose! m hm using hm
    refine ⟨∑ b ∈ s, m b, ?_⟩
    rw [Submodule.mem_colon]
    intro b hb
    have hb' : b ∈ s := hb
    have hle' : m b ≤ ∑ b ∈ s, m b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb'
    rw [smul_eq_mul, ← Nat.sub_add_cancel hle', pow_add, mul_assoc]
    exact τ.mul_mem_left _ (hm b hb')
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian K)
  have hKm : K ^ m * τ' ≤ τ := by
    rw [Ideal.mul_le]
    intro r hr t ht
    have hr' := Submodule.mem_colon.mp (hm hr)
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem x hx => simpa [smul_eq_mul] using hr' x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact τ.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact τ.mul_mem_left a hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul K (M := B) (τ' : Submodule B B)
  refine ⟨c + m, fun k hk => ?_⟩
  have hAR : K ^ k ⊓ τ' ≤ τ := by
    have h := hc k (by omega)
    simp only [smul_eq_mul, Ideal.mul_top] at h
    rw [h]
    calc K ^ (k - c) * (K ^ c ⊓ τ') ≤ K ^ (k - c) * τ' := Ideal.mul_mono_right inf_le_right
      _ ≤ K ^ m * τ' := Ideal.mul_mono_left (Ideal.pow_le_pow_right (by omega))
      _ ≤ τ := hKm
  apply le_antisymm
  · rw [inf_comm, sup_inf_assoc_of_le _ hle]
    exact sup_le le_rfl hAR
  · exact le_inf hle le_sup_left

end GlobalTheory
end

section

namespace GlobalTheory

theorem krull_inter_ideal_local (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B)
    (h : ∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) : ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  set N : Submodule B (B ⧸ a') := Submodule.map (Submodule.mkQ a') a with hN
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  have hle : N ≤ I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h k hx)
    have h1 : Submodule.mkQ a' (y + z) = z • Submodule.mkQ a' 1 := by
      have hy0 : Submodule.mkQ a' y = 0 := by
        rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero a').2 hy
      rw [map_add (f := _), hy0, zero_add, ← map_smul, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  have hNI : N ≤ I • N := by
    have e1 : N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := (inf_eq_right.2 hle).symm
    calc N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := e1
      _ = I ^ (k + 1 - k) • (I ^ k • ⊤ ⊓ N) := hk (k + 1) (Nat.le_succ k)
      _ ≤ I • N := by
        rw [Nat.add_sub_cancel_left, pow_one]
        exact Submodule.smul_mono le_rfl inf_le_right
  have hfg : N.FG := IsNoetherian.noetherian N
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N hfg hNI
  refine ⟨r, hr, fun x hx => ?_⟩
  have hx' := hrN (Submodule.mkQ a' x) ⟨x, hx, rfl⟩
  rw [← map_smul, smul_eq_mul] at hx'
  have : Submodule.mkQ a' ((1 - r) * x) = 0 := by
    rw [sub_mul, one_mul, map_sub, hx', sub_self]
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero a').1 this

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.FiniteExtensionEmbedding

theorem exists_finite_extension_embedding (F K : Type) [Field F] [CharZero F]
    [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  haveI : Nontrivial (K ⊗[ℚ] F) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[ℚ] F)
  letI : Field ((K ⊗[ℚ] F) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(K ⊗[ℚ] F) ⧸ m, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  · exact (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := F)).toRingHom

end GlobalTheory.FiniteExtensionEmbedding
end
