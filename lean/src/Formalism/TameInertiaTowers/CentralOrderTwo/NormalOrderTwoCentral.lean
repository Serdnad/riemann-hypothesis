import Mathlib
import Formalism.TameInertiaTowers.StatementGroup

/-! # The central involution in two-adic inertia towers -/

section TwoAdic

namespace Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

lemma vEq (z : ℤ) (hz : z ≠ 0) : (padicValInt 2 z : ℕ∞) = emultiplicity (2 : ℤ) z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show padicValInt 2 z = padicValNat 2 z.natAbs from rfl,
    padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hz), Int.emultiplicity_natAbs]
  rfl

lemma vNat (e : ℕ) (he : e ≠ 0) : (padicValNat 2 e : ℕ∞) = emultiplicity (2 : ℤ) (e : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_eq_emultiplicity he, ← Int.natCast_emultiplicity]
  rfl

lemma pow_sub_one_ne (a : ℤ) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) : a ^ e - 1 ≠ 0 := by
  intro h
  apply ha2
  have h1 : |a| ^ e = 1 := by rw [pow_abs, sub_eq_zero.mp h, abs_one]
  have h2 : |a| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg a) he.ne').mp h1
  rw [← sq_abs, h2, one_pow]

lemma geom_odd (a : ℤ) (ha : Odd a) (n : ℕ) : (Odd (∑ i ∈ Finset.range n, a ^ i) ↔ Odd n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ¬ Even (a ^ n) := Int.not_even_iff_odd.mpr (ha.pow)
    rw [Finset.sum_range_succ, Int.odd_add, ih]
    simp [hp, Nat.odd_add_one]

lemma sq_split (a : ℤ) (ha2 : a ^ 2 ≠ 1) :
    padicValInt 2 (a ^ 2 - 1) = padicValInt 2 (a - 1) + padicValInt 2 (a + 1) := by
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, padicValInt.mul h1 h2]

lemma val_even (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) (hev : Even e) :
    padicValInt 2 (a ^ e - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + padicValNat 2 e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne := pow_sub_one_ne a ha2 e he
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  have hdiv : (2 : ℤ) ∣ a - 1 := by
    obtain ⟨k, rfl⟩ := ha; exact ⟨k, by ring⟩
  have hnd : ¬ (2 : ℤ) ∣ a := by
    rw [← even_iff_two_dvd]; exact Int.not_even_iff_odd.mpr ha
  have key := Int.two_pow_sub_pow (y := 1) (n := e) hdiv hnd hev
  rw [one_pow, ← vEq _ hne, ← vEq _ h2, ← vEq _ h1, ← vNat _ he.ne'] at key
  rw [sq_split a ha2]
  norm_cast at key
  omega

lemma val_odd (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (hod : Odd e) :
    padicValInt 2 (a ^ e - 1) = padicValInt 2 (a - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have hs : Odd (∑ i ∈ Finset.range e, a ^ i) := (geom_odd a ha e).mpr hod
  have hs0 : (∑ i ∈ Finset.range e, a ^ i) ≠ 0 := fun h => by
    rw [h] at hs; exact Int.not_even_iff_odd.mpr hs ⟨0, by norm_num⟩
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ ∑ i ∈ Finset.range e, a ^ i := by
    intro hd
    exact Int.not_even_iff_odd.mpr hs (even_iff_two_dvd.mpr (by exact_mod_cast hd))
  rw [← mul_geom_sum, padicValInt.mul h1 hs0, padicValInt.eq_zero_of_not_dvd hnd, add_zero]

lemma powEq (N m : ℕ) (a : ℤ) (hz : a ^ m - 1 ≠ 0) :
    (a : ZMod (2 ^ N)) ^ m = 1 ↔ N ≤ padicValInt 2 (a ^ m - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : ((a : ZMod (2 ^ N)) ^ m = 1) ↔ (((a ^ m - 1 : ℤ)) : ZMod (2 ^ N)) = 0 := by
    push_cast; exact sub_eq_zero.symm
  rw [h0, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 := padicValInt_dvd_iff (p := 2) N (a ^ m - 1)
  push_cast at h2 ⊢
  rw [h2, or_iff_right hz]

end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

namespace Formalism.TwoAdicCyclotomicDecomposition

open TwoAdicValuation in
theorem twoAdicVal : TwoAdicVal := by
  intro a ha ha2 e he
  by_cases hev : Even e
  · have h := val_even a ha ha2 e he hev
    have hl : padicValNat 2 e ≤ Nat.log 2 e := padicValNat_le_nat_log e
    rw [if_pos hev]
    constructor <;> omega
  · have hod : Odd e := Nat.not_even_iff_odd.mp hev
    have h := val_odd a ha ha2 e hod
    have hs := sq_split a ha2
    rw [if_neg hev]
    constructor <;> omega

open TwoAdicValuation in
theorem twoAdicOrder : TwoAdicOrder := by
  intro N a ha ha2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  split_ifs with h1
  · rw [h1, orderOf_one]
  · have hv : ∀ j : ℕ, 1 ≤ j →
        padicValInt 2 (a ^ 2 ^ j - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + j := by
      intro j hj
      have := val_even a ha ha2 (2 ^ j) (by positivity) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      rwa [padicValNat.prime_pow] at this
    have hpow : ∀ j : ℕ,
        ((a : ZMod (2 ^ N)) ^ 2 ^ j = 1 ↔ N ≤ padicValInt 2 (a ^ 2 ^ j - 1)) := fun j =>
      powEq N (2 ^ j) a (pow_sub_one_ne a ha2 _ (by positivity))
    set K := max 1 (N + 1 - padicValInt 2 (a ^ 2 - 1)) with hK
    have hK1 : 1 ≤ K := le_max_left _ _
    have hK2 : N + 1 - padicValInt 2 (a ^ 2 - 1) ≤ K := le_max_right _ _
    have hK3 : K = 1 ∨ K = N + 1 - padicValInt 2 (a ^ 2 - 1) := max_choice _ _
    clear_value K
    obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    apply orderOf_eq_prime_pow
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, pow_zero, pow_one]; exact h1
      · rw [hpow]
        have := hv n h0
        omega
    · rw [hpow]
      have := hv (n + 1) (by omega)
      omega

end Formalism.TwoAdicCyclotomicDecomposition

end TwoAdic

section NormalOrderTwoCentral

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem normalOrderTwoCentral : NormalOrderTwoCentral := by
  intro H _ N hN h2 z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · simp [hz1]
  have hc : g * z * g⁻¹ ∈ N := hN.conj_mem z hz g
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp h2
  have e1 : (⟨g * z * g⁻¹, hc⟩ : N) = y := huniq _ (by
    intro h; apply hz1
    have h' : g * z * g⁻¹ = 1 := congrArg Subtype.val h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group)
  have e2 : (⟨z, hz⟩ : N) = y := huniq _ (by
    intro h; exact hz1 (congrArg Subtype.val h))
  have : g * z * g⁻¹ = z := congrArg Subtype.val (e1.trans e2.symm)
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [this]

lemma v24 : padicValInt 2 ((5 : ℤ) ^ 2 - 1) = 3 := by
  have : ((5 : ℤ) ^ 2 - 1) = ((2 ^ 3 * 3 : ℕ) : ℤ) := by norm_num
  rw [this, padicValInt.of_nat, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

lemma v4 : padicValInt 2 ((5 : ℤ) - 1) = 2 := by
  have : ((5 : ℤ) - 1) = ((2 ^ 2 : ℕ) : ℤ) := by norm_num
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

theorem twistVal : TwistVal := by
  intro s e he
  have h5 : Odd (5 : ℤ) := by decide
  have h52 : (5 : ℤ) ^ 2 ≠ 1 := by norm_num
  have hpos : 0 < 2 ^ s * e := Nat.mul_pos (Nat.two_pow_pos s) he
  have key := (twoAdicVal 5 h5 h52 (2 ^ s * e) hpos).1
  rw [key]
  split_ifs with hev
  · rw [v24, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
    omega
  · rw [v4]
    have hs : s = 0 := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exact h
      · exfalso; apply hev
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
        exact ⟨2 ^ k * e, by ring⟩
    subst hs
    have he' : ¬ 2 ∣ e := by
      intro hd; apply hev; simpa using (even_iff_two_dvd.mpr hd)
    rw [padicValNat.eq_zero_of_not_dvd he']

lemma gcd_two_pow (N k : ℕ) (hk : k ≠ 0) : Nat.gcd (2 ^ N) k = 2 ^ min N (padicValNat 2 k) := by
  have hp : Nat.Prime 2 := Nat.prime_two
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk 2 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hv : padicValNat 2 (2 ^ v * m) = v := by
    rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [hv]
  have hcop : Nat.Coprime m (2 ^ N) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm))
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_right_cancel _ hcop]
  rcases le_total N v with h | h
  · rw [min_eq_left h, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_left (Nat.pow_dvd_pow 2 h)]

theorem coinvLength : CoinvLength := by
  intro N u _ hu1
  set k := (u - 1).natAbs with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef]; intro h; apply hu1; have := Int.natAbs_eq_zero.mp h; linarith
  have hsub : AddSubgroup.zmultiples (((u - 1 : ℤ)) : ZMod (2 ^ N)) =
      AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)) := by
    rcases Int.natAbs_eq (u - 1) with h | h
    · rw [h]; simp [hkdef]
    · rw [h]; simp [hkdef]
  rw [hsub]
  have hN : (2 ^ N : ℕ) ≠ 0 := by positivity
  have hc := AddSubgroup.card_mul_index (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N)))
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hN, Nat.card_zmod] at hc
  have hidx : (AddSubgroup.zmultiples ((k : ℕ) : ZMod (2 ^ N))).index = Nat.gcd (2 ^ N) k := by
    have hg : Nat.gcd (2 ^ N) k ∣ 2 ^ N := Nat.gcd_dvd_left _ _
    have hgpos : 0 < Nat.gcd (2 ^ N) k := Nat.gcd_pos_of_pos_left _ (by positivity)
    have hd : 2 ^ N / Nat.gcd (2 ^ N) k * Nat.gcd (2 ^ N) k = 2 ^ N := Nat.div_mul_cancel hg
    have hdpos : 0 < 2 ^ N / Nat.gcd (2 ^ N) k :=
      Nat.div_pos (Nat.le_of_dvd (by positivity) hg) hgpos
    exact Nat.eq_of_mul_eq_mul_left hdpos (hc.trans hd.symm)
  rw [← AddSubgroup.index, hidx, gcd_two_pow N k hk]
  rfl

theorem genusAbelian : GenusAbelian := by
  intro G _ _ A B C hsup hcard a ha b hb c hc habc
  let f : A × B × C →* G := A.subtype.coprod (B.subtype.coprod C.subtype)
  have hf : ∀ x : A × B × C, f x = (x.1 : G) * ((x.2.1 : G) * (x.2.2 : G)) := fun x => rfl
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hsup]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx; exact ⟨(⟨x, hx⟩, 1, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, ⟨x, hx⟩, 1), by simp [hf]⟩
    · intro x hx; exact ⟨(1, 1, ⟨x, hx⟩), by simp [hf]⟩
  have hbij : Function.Bijective f := by
    apply hsurj.bijective_of_nat_card_le
    rw [Nat.card_prod, Nat.card_prod, hcard, mul_assoc]
  have h1 : f (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩) = f 1 := by
    rw [hf, map_one]; simpa [mul_assoc] using habc
  have h2 := hbij.1 h1
  simp only [Prod.mk_eq_one, Subgroup.mk_eq_one] at h2
  exact ⟨h2.1, h2.2.1, h2.2.2⟩

theorem pGroupGen : PGroupGen := by
  intro p _ H _ _ hP S hS
  by_contra hne
  obtain ⟨Mx, hMx, hle⟩ := (eq_top_or_exists_le_coatom (Subgroup.closure S)).resolve_left hne
  have := hP.isNilpotent
  have hMn : Mx.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom Mx (Group.normalizerCondition_of_isNilpotent) hMx
  have : Subgroup.normalClosure S ≤ Mx :=
    Subgroup.normalClosure_le_normal (fun x hx => hle (Subgroup.subset_closure hx))
  rw [hS] at this
  exact hMx.1 (top_le_iff.mp this)

end Formalism.TwoAdicCyclotomicDecomposition

end NormalOrderTwoCentral
