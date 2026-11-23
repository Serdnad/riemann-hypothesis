module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
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
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_sub_eq_p_mul_of_constantCoeff_eq {x y : WittVector p k}
    (h : WittVector.constantCoeff x = WittVector.constantCoeff y) : ∃ z, x - y = p * z := by
  by_cases hxy : x - y = 0
  · exact ⟨0, by rw [hxy, mul_zero]⟩
  obtain ⟨m, z, hz, hxyz⟩ := WittVector.exists_eq_pow_p_mul (x - y) hxy
  rcases m with _ | m
  · exfalso; apply hz
    have h1 := congrArg WittVector.constantCoeff hxyz
    rw [map_sub, h, sub_self, pow_zero, one_mul] at h1
    exact h1.symm
  · exact ⟨p ^ m * z, by rw [hxyz, pow_succ]; ring⟩

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem prod_sub_prod_divisible_lemma_2 {σ τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k)
    (U V : σ → MvPowerSeries τ (WittVector p k)) (e : σ → ℕ) (S : Finset σ)
    (h : ∀ i ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (U i ^ e i - V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (∏ i ∈ S, U i ^ e i - ∏ i ∈ S, V i ^ e i) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i S hi ih =>
    obtain ⟨Y1, hY1⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨Y2, hY2⟩ := h i (Finset.mem_insert_self i S)
    refine ⟨U i ^ e i * Y1 + Y2 * ∏ j ∈ S, V j ^ e j, ?_⟩
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    simp only [Algebra.smul_def, map_sub, map_mul, map_add (f := _), map_pow, map_prod] at hY1 hY2 ⊢
    linear_combination
      (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i)) ^ e i * hY1 +
      (∏ j ∈ S, (MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V j)) ^ e j) * hY2

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem exists_choose_mul_p_pow_mul_eq_p_mul (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ t : WittVector p k, c * ((n.choose j : _root_.GlobalTheory.Katz.Fr p k) * (p : _root_.GlobalTheory.Katz.Fr p k) ^ j) =
      algebraMap (WittVector p k) _ (p * t) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨e, j', hj', hjeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : j ≠ 0) p hp.ne_one
  have hj'0 : j' ≠ 0 := by rintro rfl; simp at hj'
  have hej : e < j := by
    have h1 : p ^ e ≤ j := by rw [hjeq]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj'0)
    exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) h1
  obtain ⟨q, rfl⟩ : ∃ q, j = q + e + 1 := ⟨j - e - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hunit : IsUnit (j' : WittVector p k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have h2 : (j' : WittVector p k).coeff 0 = (j' : k) :=
      map_natCast (WittVector.constantCoeff (p := p) (R := k)) j'
    rw [h2]
    exact (CharP.cast_eq_zero_iff k p j').not.2 hj'
  obtain ⟨s, hs⟩ := hunit.exists_right_inv
  refine ⟨m * (n'.choose (q + e) : WittVector p k) * (p : WittVector p k) ^ q * s, ?_⟩
  set ι := algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)
  have hs' : (j' : _root_.GlobalTheory.Katz.Fr p k) * ι s = 1 := by
    rw [← map_natCast ι, ← map_mul, hs, map_one]
  have hjK : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) = (p : _root_.GlobalTheory.Katz.Fr p k) ^ e * j' := by
    rw [hjeq]; push_cast; ring
  have hchoose : ((n' + 1).choose (q + e + 1) : _root_.GlobalTheory.Katz.Fr p k) * ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) =
      ((n' + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) := by
    have := Nat.add_one_mul_choose_eq n' (q + e)
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  have hj0 : ((q + e + 1 : ℕ) : _root_.GlobalTheory.Katz.Fr p k) ≠ 0 := by
    rw [hjK]
    have hinj : Function.Injective ι := IsFractionRing.injective _ _
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 (WittVector.p_nonzero p k)
    · rw [← map_natCast ι]; exact (map_ne_zero_iff ι hinj).2 hunit.ne_zero
  apply mul_right_cancel₀ hj0
  simp only [map_mul, map_pow, map_natCast]
  linear_combination (c * (p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1)) * hchoose +
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k)) * hc -
    ((p : _root_.GlobalTheory.Katz.Fr p k) * ι m * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) *
      (p : _root_.GlobalTheory.Katz.Fr p k) ^ q * ι s) * hjK -
    ((p : _root_.GlobalTheory.Katz.Fr p k) ^ (q + e + 1) * (n'.choose (q + e) : _root_.GlobalTheory.Katz.Fr p k) * ι m) * hs'

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_algebraMap_smul' {τ : Type} (a : WittVector p k) (Y : MvPowerSeries τ (WittVector p k)) :
    MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (a • Y) =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) a •
        MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
  ext β
  simp only [MvPowerSeries.coeff_map, map_smul, smul_eq_mul, map_mul]

open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
private theorem map_add_p_mul_pow_sub_pow_eq_p_smul {τ : Type} (c : _root_.GlobalTheory.Katz.Fr p k) (m : WittVector p k)
    {n : ℕ} (hc : (n : _root_.GlobalTheory.Katz.Fr p k) * c = algebraMap (WittVector p k) _ m)
    (V H : MvPowerSeries τ (WittVector p k)) :
    ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      ((V + (p : MvPowerSeries τ (WittVector p k)) * H) ^ n - V ^ n) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by

  rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
  mul_one, add_sub_cancel_right, map_sum, Finset.smul_sum]
  have key : ∀ j ∈ Finset.range n, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨t, ht⟩ := exists_choose_mul_p_pow_mul_eq_p_mul c m hc (n - j) (by omega) (by omega)
    rw [Nat.choose_symm (by omega)] at ht
    refine ⟨t • (V ^ j * H ^ (n - j)), ?_⟩
    have e1 : V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k)) =
        ((n.choose j * p ^ (n - j) : ℕ) : WittVector p k) • (V ^ j * H ^ (n - j)) := by
      rw [Algebra.smul_def, map_natCast]; push_cast; ring
    rw [e1, map_algebraMap_smul', map_algebraMap_smul', smul_smul, smul_smul, map_natCast]
    congr 1
    rw [← map_mul, ← ht]; push_cast; ring
  have hsum : ∀ S : Finset ℕ, (∀ j ∈ S, ∃ Y, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y) →
      ∃ Y, ∑ j ∈ S, c • MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k))
      (V ^ j * ((p : MvPowerSeries τ (WittVector p k)) * H) ^ (n - j) * (n.choose j : MvPowerSeries τ (WittVector p k))) =
        algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) p •
          MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) Y := by
    intro S hS
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j S hj ih =>
      obtain ⟨Y1, hY1⟩ := ih fun i hi => hS i (Finset.mem_insert_of_mem hi)
      obtain ⟨Y2, hY2⟩ := hS j (Finset.mem_insert_self j S)
      exact ⟨Y2 + Y1, by rw [Finset.sum_insert hj, hY1, hY2, map_add (f := _), smul_add]⟩
  exact hsum _ key


open CategoryTheory TensorProduct MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] in
theorem _root_.GlobalTheory.Katz.subst_sub_subst_mem_intBy : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (_root_.GlobalTheory.Katz.Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (_root_.GlobalTheory.Katz.Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, _root_.GlobalTheory.Katz.Red p (u i) (w i)) → (∀ i, _root_.GlobalTheory.Katz.Red p (v i) (w i)) → f ∈ _root_.GlobalTheory.Katz.quasiInt p k σ → subst u f - subst v f ∈ _root_.GlobalTheory.Katz.intBy p k τ p := by
  intro p _ k _ _ _ σ τ _ u v w f hu0 hv0 hu hv hf
  classical
  choose a ha using fun i β => hu i β
  choose b hb using fun i β => hv i β
  choose hh hhh using fun i β =>
    exists_sub_eq_p_mul_of_constantCoeff_eq ((ha i β).2.trans (hb i β).2.symm)
  let U : σ → MvPowerSeries τ (WittVector p k) := fun i β => a i β
  let V : σ → MvPowerSeries τ (WittVector p k) := fun i β => b i β
  let Hs : σ → MvPowerSeries τ (WittVector p k) := fun i β => hh i β
  have hUV : ∀ i, U i = V i + (p : MvPowerSeries τ (WittVector p k)) * Hs i := by
    intro i; refine MvPowerSeries.ext fun β => ?_
    have e : (p : MvPowerSeries τ (WittVector p k)) * Hs i = (p : WittVector p k) • Hs i := by
      rw [Algebra.smul_def, map_natCast]
    rw [e, map_add (f := _), map_smul, smul_eq_mul]
    show a i β = b i β + p * hh i β
    rw [← hhh]; ring
  have huM : u = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (U i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (ha i β).1
  have hvM : v = fun i => MvPowerSeries.map (algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k)) (V i) := by
    funext i; ext β; rw [MvPowerSeries.coeff_map]; exact (hb i β).1
  have hf' : ∀ (α : σ →₀ ℕ) (i : σ), ∃ m, ((α i : ℕ) : _root_.GlobalTheory.Katz.Fr p k) * MvPowerSeries.coeff α f =
      algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) m := hf
  have hsu := MvPowerSeries.hasSubst_of_constantCoeff_zero hu0
  have hsv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  unfold _root_.GlobalTheory.Katz.intBy
  refine fun β => ?_
  rw [map_sub, MvPowerSeries.coeff_subst hsu, MvPowerSeries.coeff_subst hsv,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hsu f β)
      (MvPowerSeries.coeff_subst_finite hsv f β)]
  refine finsum_induction (fun x => ∃ w, x = algebraMap (WittVector p k) (_root_.GlobalTheory.Katz.Fr p k) (p * w))
    ⟨0, by simp⟩ (fun x y ⟨w1, h1⟩ ⟨w2, h2⟩ => ⟨w1 + w2, by rw [h1, h2, mul_add, map_add (f := _)]⟩) fun α => ?_
  obtain ⟨Y, hY⟩ := prod_sub_prod_divisible_lemma_2 (MvPowerSeries.coeff α f) U V α α.support fun i _ => by
    obtain ⟨mi, hmi⟩ := hf' α i
    rw [hUV i]
    exact map_add_p_mul_pow_sub_pow_eq_p_smul _ mi hmi (V i) (Hs i)
  refine ⟨MvPowerSeries.coeff β Y, ?_⟩
  rw [huM, hvM]
  simp only [Finsupp.prod, ← map_pow, ← map_prod]
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← map_sub, ← smul_eq_mul, ← map_smul, hY,
    map_smul, MvPowerSeries.coeff_map, smul_eq_mul, map_mul]

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.OnePair.coeff_subst_kill {σ R : Type} [CommRing R] [Finite σ] (p : σ → Prop)
    [DecidablePred p] (c : MvPowerSeries σ R) (γ : σ →₀ ℕ) [Decidable (∀ s, ¬ p s → γ s = 0)] :
    coeff γ (subst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) c) =
      if ∀ s, ¬ p s → γ s = 0 then coeff γ c else 0 := by
  classical
  have hsub : HasSubst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) :=
    hasSubst_of_constantCoeff_zero fun s => by split_ifs <;> simp
  have key : ∀ d : σ →₀ ℕ,
      coeff γ (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
        if d = γ ∧ ∀ s, ¬ p s → γ s = 0 then 1 else 0 := by
    intro d
    by_cases hd : ∀ s, ¬ p s → d s = 0
    · have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
          monomial d 1 := by
        rw [monomial_one_eq]
        refine Finsupp.prod_congr fun s hs => ?_
        have hps : p s := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp hs) (hd s h)
        rw [if_pos hps]
      rw [hprod, coeff_monomial]
      by_cases hγ : γ = d
      · subst hγ
        rw [if_pos rfl, if_pos ⟨rfl, hd⟩]
      · rw [if_neg hγ, if_neg fun h => hγ h.1.symm]
    · push_neg at hd
      obtain ⟨s, hps, hds⟩ := hd
      have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds) (by rw [if_neg hps, zero_pow hds])
      rw [hprod, map_zero, if_neg]
      rintro ⟨rfl, h⟩
      exact hds (h s hps)
  rw [coeff_subst hsub, finsum_eq_single _ γ]
  · rw [key]
    by_cases h : ∀ s, ¬ p s → γ s = 0 <;> simp [h]
  · intro d hd
    rw [key, if_neg fun h => hd h.1, smul_zero]

end OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.coeff_at2_single_X_inl_inr (R : Type) [CommRing R] (d : ℕ)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ) :
    coeff γ (_root_.GlobalTheory.Katz.at2 c
      (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m)))) =
      if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  classical
  have hfun : Sum.elim (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m))) = fun s =>
        if (s = Sum.inl m ∨ s = Sum.inr m) then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0 := by
    funext s
    rcases s with i | i <;> by_cases h : i = m <;> simp [h, Pi.single_apply]
  have hiff : (∀ s, ¬ (s = Sum.inl m ∨ s = Sum.inr m) → γ s = 0) ↔
      γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) := by
    constructor
    · intro h
      ext s
      by_cases hs : s = Sum.inl m ∨ s = Sum.inr m
      · rcases hs with rfl | rfl <;> simp [Finsupp.single_apply]
      · push_neg at hs
        rw [h s (not_or.mpr hs)]
        simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
    · intro h s hs
      push_neg at hs
      rw [h]
      simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
  unfold _root_.GlobalTheory.Katz.at2
  rw [hfun, _root_.GlobalTheory.OnePair.coeff_subst_kill]
  by_cases hγ : γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (γ (Sum.inr m))
  · rw [if_pos hγ, if_pos (hiff.mpr hγ)]
  · rw [if_neg hγ, if_neg fun h => hγ (hiff.mp h)]

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem evA_X (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A]
    (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ) : evA k x hx (X i) = x i := by
  have ha : HasSubst (fun i => (C (x i) : MvPowerSeries Empty A)) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  show (constantCoeff : MvPowerSeries Empty A →+* A) (substAlgHom (R := k) ha (X i)) = x i
  rw [substAlgHom_apply, subst_X ha, constantCoeff_C]

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {d : ℕ} {τ : Type}

theorem map_powerSeriesEvalTwoGroups (c : MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    MvPowerSeries.map σ (at2 c u v) =
      at2 (MvPowerSeries.map σ c) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hu, hv])
  unfold at2
  rw [map_subst hs]
  congr 1
  funext s
  cases s <;> rfl

theorem constantCoeff_powerSeriesEvalTwoGroups_zero_of {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : constantCoeff c = 0) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    constantCoeff (at2 c u v) = 0 := by
  have h0 : ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hc

theorem map_op_of_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => MvPowerSeries.map σ (op μ u v i)) =
      op (fun i => MvPowerSeries.map σ (μ i)) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  funext i
  exact map_powerSeriesEvalTwoGroups σ (μ i) hu hv

theorem isLaw_map (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : IsLaw μ) :
    IsLaw (fun i => MvPowerSeries.map σ (μ i)) := by
  have hX : ∀ {κ : Type} (f : Fin d → κ), (fun i => MvPowerSeries.map σ
      (X (f i) : MvPowerSeries κ R)) = fun i => (X (f i) : MvPowerSeries κ S) := by
    intro κ f; funext i; exact map_X σ (f i)
  have hcX : ∀ {κ : Type} (f : Fin d → κ) (i : Fin d),
      constantCoeff (X (f i) : MvPowerSeries κ R) = 0 := fun f i => constantCoeff_X _
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d) R =>
      fun i => MvPowerSeries.map σ (w i)) h.unit
    rw [map_op_of_const σ μ (u := fun i => (X i : MvPowerSeries (Fin d) R)) (fun i => constantCoeff_X i)
      (fun _ => map_zero _)] at h1
    simpa only [map_X, map_zero] using h1
  · have h1 := congrArg (MvPowerSeries.map σ) (h.comm i)
    unfold swap at h1 ⊢
    rw [map_powerSeriesEvalTwoGroups σ (μ i) (hcX Sum.inr) (hcX Sum.inl)] at h1
    simpa only [map_X] using h1
  · have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have c12 : ∀ i, constantCoeff (op μ x1 x2 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx1 hx2
    have c23 : ∀ i, constantCoeff (op μ x2 x3 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx2 hx3
    have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
      fun i => MvPowerSeries.map σ (w i)) h.assoc
    rw [map_op_of_const σ μ c12 hx3, map_op_of_const σ μ hx1 c23,
      map_op_of_const σ μ hx1 hx2, map_op_of_const σ μ hx2 hx3] at h1
    have e1 : (fun i => MvPowerSeries.map σ (x1 (R := R) (d := d) i)) = x1 := hX _
    have e2 : (fun i => MvPowerSeries.map σ (x2 (R := R) (d := d) i)) = x2 := hX _
    have e3 : (fun i => MvPowerSeries.map σ (x3 (R := R) (d := d) i)) = x3 := hX _
    rwa [e1, e2, e3] at h1

end GlobalTheory.Katz
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace Katz

theorem red_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) →
    (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧
    ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c →
      subst u f ∈ intBy p k τ c := by
  intro p _ k _ _ _ σ τ _ u u' hu0 hu
  have hinj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
    IsFractionRing.injective _ _
  have hu1 : ∀ i (α : τ →₀ ℕ), ∃ w : WittVector p k, coeff α (u i) = algebraMap _ (Fr p k) w ∧
      WittVector.constantCoeff w = coeff α (u' i) := hu
  choose U hU using hu1
  let V : σ → MvPowerSeries τ (WittVector p k) := U
  have hV : ∀ i α, coeff α (V i) = U i α := fun _ _ => rfl
  have hmap : u = fun i => map (algebraMap (WittVector p k) (Fr p k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).1]
  have hmap' : u' = fun i => map (WittVector.constantCoeff (p := p) (R := k)) (V i) := by
    funext i; ext α; rw [coeff_map, hV, (hU i α).2]
  have hV0 : ∀ i, constantCoeff (V i) = 0 := by
    intro i
    apply hinj
    rw [map_zero, ← hu0 i, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      hV, (hU i 0).1]
  have hVs : HasSubst V := hasSubst_of_constantCoeff_zero hV0
  refine ⟨?_, ?_⟩
  · intro f f' hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) w ∧
        WittVector.constantCoeff w = coeff α f' := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_map]; exact (hF α).1
    have e2 : f' = map (WittVector.constantCoeff (p := p) (R := k)) G := by
      ext α; rw [coeff_map]; exact (hF α).2.symm
    rw [e1, e2, hmap, hmap', ← map_subst hVs, ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_map], by rw [coeff_map]⟩
  · intro c f hf
    have hf1 : ∀ α, ∃ w : WittVector p k, coeff α f = algebraMap _ (Fr p k) (c * w) := hf
    choose F hF using hf1
    let G : MvPowerSeries σ (WittVector p k) := F
    have e1 : f = algebraMap (WittVector p k) (Fr p k) c •
        map (algebraMap (WittVector p k) (Fr p k)) G := by
      ext α; rw [coeff_smul, coeff_map, hF α, map_mul]; rfl
    rw [e1, hmap, subst_smul (hVs.map _), ← map_subst hVs]
    intro α
    exact ⟨coeff α (subst V G), by rw [coeff_smul, coeff_map, map_mul]⟩

end Katz

end GlobalTheory
end
end
