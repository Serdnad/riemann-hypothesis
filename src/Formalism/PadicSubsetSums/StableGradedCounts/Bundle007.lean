module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle006
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem pow_lpow_add {M : Type*} [Monoid M] {l a : ℕ} {x z : M} (h : x ^ (l ^ a) = z ^ (l ^ a))
    (b : ℕ) : x ^ (l ^ (a + b)) = z ^ (l ^ (a + b)) := by
  rw [pow_add, pow_mul, pow_mul, h]

theorem eq_of_pow_eq_of_coprime_order {M : Type*} [Monoid M] {r : ℕ} {u w : M}
    (hu : 0 < orderOf u) (hw : 0 < orderOf w) (hcu : Nat.Coprime r (orderOf u))
    (hcw : Nat.Coprime r (orderOf w)) (h : u ^ r = w ^ r) : u = w := by
  by_cases h1 : orderOf u * orderOf w = 1
  · have hu1 : orderOf u = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hw1 : orderOf w = 1 := Nat.eq_one_of_mul_eq_one_left h1
    rw [orderOf_eq_one_iff.mp hu1, orderOf_eq_one_iff.mp hw1]
  · have hpos : 0 < orderOf u * orderOf w := Nat.mul_pos hu hw
    have hlt : 1 < orderOf u * orderOf w := by omega
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.mul_right hcu hcw) hlt
    have hmod : r * s ≡ 1 [MOD orderOf u * orderOf w] := by
      unfold Nat.ModEq
      rw [hs, Nat.mod_eq_of_lt hlt]
    have hm1 : r * s ≡ 1 [MOD orderOf u] := Nat.ModEq.of_mul_right (orderOf w) hmod
    have hm2 : r * s ≡ 1 [MOD orderOf w] := Nat.ModEq.of_mul_left (orderOf u) hmod
    have hu' : u ^ (r * s) = u := by
      rw [← pow_mod_orderOf, show r * s % orderOf u = 1 % orderOf u from hm1, pow_mod_orderOf,
        pow_one]
    have hw' : w ^ (r * s) = w := by
      rw [← pow_mod_orderOf, show r * s % orderOf w = 1 % orderOf w from hm2, pow_mod_orderOf,
        pow_one]
    rw [← hu', ← hw', pow_mul, pow_mul, h]

theorem prime_to_part_eq_iff : PrimeToPartEqIff := by
  intro M _ l x y hl hx hy
  obtain ⟨hox, a, ha⟩ := prime_to_part_spec M l x hl hx
  obtain ⟨hoy, b, hb⟩ := prime_to_part_spec M l y hl hy
  have hnx : orderOf x ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  have hny : orderOf y ≠ 0 := (orderOf_pos_iff.mpr hy).ne'
  constructor
  · intro h
    refine ⟨a + b, ?_⟩
    rw [pow_lpow_add ha b, h, add_comm a b, pow_lpow_add hb a]
  · rintro ⟨c, hc⟩
    have e1 : primeToPart l x ^ (l ^ (a + (b + c))) = x ^ (l ^ (a + (b + c))) :=
      (pow_lpow_add ha _).symm
    have e2 : primeToPart l y ^ (l ^ (b + (a + c))) = y ^ (l ^ (b + (a + c))) :=
      (pow_lpow_add hb _).symm
    have e3 : x ^ (l ^ (c + (a + b))) = y ^ (l ^ (c + (a + b))) := pow_lpow_add hc _
    have s1 : a + (b + c) = c + (a + b) := by omega
    have s2 : b + (a + c) = c + (a + b) := by omega
    rw [s1] at e1
    rw [s2] at e2
    refine eq_of_pow_eq_of_coprime_order (r := l ^ (c + (a + b))) ?_ ?_ ?_ ?_ (by rw [e1, e2, e3])
    · rw [hox]; exact Nat.ordCompl_pos l hnx
    · rw [hoy]; exact Nat.ordCompl_pos l hny
    · rw [hox]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hnx)
    · rw [hoy]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hny)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem central_idempotents_orthogonal : CentralIdemOrthogonal := by
  intro G V W _ _ _ _ _ _ _ _ _ _ ρ σ hρ hσ hne
  obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ σ hσ
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hno : ¬ Nonempty (Representation.Equiv ρ σ) := by
    rintro ⟨φ⟩
    exact hne ⟨φ.toLinearEquiv, fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x⟩
  have horth := Representation.char_orthonormal σ ρ
  rw [if_neg hno, Nat.card_eq_fintype_card] at horth
  have h3 : ∑ g, ρ.character g⁻¹ * σ.character g = 0 := by
    have e : ∑ g, ρ.character g⁻¹ * σ.character g = ∑ g, σ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => mul_comm _ _
    rw [e]
    simpa using horth
  rw [h3] at h1
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have hμ : μ = 0 := (mul_eq_zero.mp h1).resolve_right hd
  rw [h2, hμ, mul_zero, zero_smul]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem prime_cycle_probability_sum : CycleProbSum := cycleProbSum_of_cycleProbPrime prime_cycle_probability

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ 1 ≤ ∏ l ∈ s, f l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l hl => hf l (Finset.mem_insert_of_mem hl)
    have hfa : 2 ≤ f a := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, by nlinarith⟩
    rcases s.eq_empty_or_nonempty with hs | ⟨b, hb⟩
    · subst hs
      simp
    · have hP2 : 2 ≤ ∏ l ∈ s, f l :=
        (hf b (Finset.mem_insert_of_mem hb)).trans
          (Finset.single_le_prod' (fun l hl => by
            have := hf l (Finset.mem_insert_of_mem hl)
            omega) hb)
      nlinarith

private theorem one_sub_sum_mul_prod_le_prod (q x y z T P : ℕ) (hx : 16 ≤ x) (hy : q ≤ y) (hz : 16 ≤ z) (hqz : q ≤ z)
    (hT : T ≤ P) (hP : 1 ≤ P) : 4 * q * (x + (y + (z + T))) ≤ x * (y * (z * P)) := by
  have h1 : 16 * q ≤ y * z * P := by
    calc 16 * q = q * 16 * 1 := by ring
      _ ≤ y * z * P := Nat.mul_le_mul (Nat.mul_le_mul hy hz) hP
  have h2 : 16 * q ≤ x * z * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * z * P := Nat.mul_le_mul (Nat.mul_le_mul hx hqz) hP
  have h3 : 16 * q ≤ x * y * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * y * P := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hP
  have h4 : 16 * q * T ≤ x * y * z * P := by
    have h5 : 16 * q ≤ x * y * z := by
      calc 16 * q = 16 * q * 1 := by ring
        _ ≤ x * y * z := Nat.mul_le_mul (Nat.mul_le_mul hx hy) (by omega)
    exact Nat.mul_le_mul h5 hT
  nlinarith [Nat.mul_le_mul_left x h1, Nat.mul_le_mul_left y h2, Nat.mul_le_mul_left z h3]

theorem prime_power_order_share : PrimePowerOrderShare := by
  intro g q₁ d hg hq hd hqd hq2 hd2 hM h16 hqn hdn
  set n := g - 1 with hn
  have hn0 : n ≠ 0 := by omega
  have h2n : 2 ∣ n := (show 2 ∣ 16 by norm_num).trans h16
  have hmem : ∀ l, l.Prime → l ∣ n → l ∈ n.primeFactors := fun l hl hln =>
    Nat.mem_primeFactors.mpr ⟨hl, hln, hn0⟩
  have hge : ∀ l, l.Prime → l ∣ n → l ≤ l ^ padicValNat l n := by
    intro l hl hln
    haveI := Fact.mk hl
    have hv : 1 ≤ padicValNat l n := by
      simpa only [Nat.padicValNat_def] using one_le_multiplicity_of_dvd hn0 hln
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ padicValNat l n := Nat.pow_le_pow_right hl.pos hv
  have hf2 : 16 ≤ 2 ^ padicValNat 2 n := by
    haveI := Fact.mk Nat.prime_two
    have hv : 4 ≤ padicValNat 2 n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn0).mp (by norm_num; exact h16)
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ padicValNat 2 n := Nat.pow_le_pow_right (by norm_num) hv
  have h2m := hmem 2 Nat.prime_two h2n
  have hqm : q₁ ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨hq2, hmem q₁ hq hqn⟩
  have hdm : d ∈ (n.primeFactors.erase 2).erase q₁ :=
    Finset.mem_erase.mpr ⟨fun h => hqd h.symm, Finset.mem_erase.mpr ⟨hd2, hmem d hd hdn⟩⟩
  have hsum : ∑ l ∈ n.primeFactors, l ^ padicValNat l n =
      2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
        ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    rw [← Finset.add_sum_erase _ _ h2m, ← Finset.add_sum_erase _ _ hqm, ← Finset.add_sum_erase _ _ hdm]
  have hprod : n = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
        ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    have h1 : ∏ l ∈ n.primeFactors, l ^ padicValNat l n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hl), Nat.padicValNat_def]
    rw [← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ hqm,
      ← Finset.mul_prod_erase _ _ hdm] at h1
    exact h1.symm
  have hR2 : ∀ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, 2 ≤ l ^ padicValNat l n := by
    intro l hl
    have hl' : l ∈ n.primeFactors :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
    have hlp := Nat.prime_of_mem_primeFactors hl'
    exact hlp.two_le.trans (hge l hlp (Nat.dvd_of_mem_primeFactors hl'))
  obtain ⟨hTP, hP1⟩ := sum_le_prod_of_two_le _ (fun l => l ^ padicValNat l n) hR2
  have hq16 := hge q₁ hq hqn
  have hd16 := hge d hd hdn
  have hnat : (∑ l ∈ n.primeFactors, l ^ padicValNat l n) * (4 * min q₁ d) ≤ n := by
    rw [hsum]
    rcases le_total q₁ d with hle | hle
    · rw [min_eq_left hle]
      have key := one_sub_sum_mul_prod_le_prod q₁ _ _ _ _ _ hf2 hq16 (le_trans (by omega : 16 ≤ d) hd16)
        (hle.trans hd16) hTP hP1
      calc _ = 4 * q₁ * (2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = n := hprod.symm
    · rw [min_eq_right hle]
      have key := one_sub_sum_mul_prod_le_prod d (2 ^ padicValNat 2 n) (d ^ padicValNat d n) (q₁ ^ padicValNat q₁ n) _ _
        hf2 hd16 (le_trans (by omega : 16 ≤ q₁) hq16) (hle.trans hq16) hTP hP1
      calc _ = 4 * d * (2 ^ padicValNat 2 n + (d ^ padicValNat d n + (q₁ ^ padicValNat q₁ n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
            ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by ring
        _ = n := hprod.symm
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hmpos : (0 : ℝ) < 4 * ((min q₁ d : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (lt_min hq.pos hd.pos))
  rw [← Nat.cast_sum, div_le_div_iff₀ hnpos hmpos, one_mul]
  exact_mod_cast hnat

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

namespace CISum

open Classical in
theorem centralIdem_act {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsIrr ρ) (hσ : IsIrr σ) :
    σ.asAlgebraHom (centralIdem ρ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  have := hρ.1
  have := hσ.1
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ.2
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ.2
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  set c : ℂ := (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) with hc
  have e : σ.asAlgebraHom (centralIdem ρ) = ∑ g, (c * ρ.character g⁻¹) • σ g := by
    unfold centralIdem

    simp [map_sum]
    rfl
  obtain ⟨μ, hμ⟩ := schur_scalar σ hσ.2 (fun g => c * ρ.character g⁻¹) (by
    intro g k
    have : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
    simp only [this, Representation.char_conj])
  have htr : μ * (Module.finrank ℂ W : ℂ) = c * ∑ g, σ.character g * ρ.character g⁻¹ := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ

    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by simp only [Representation.character]; ring
  have horth := Representation.char_orthonormal σ ρ
  rw [Nat.card_eq_fintype_card] at horth
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  rw [e, hμ]
  split_ifs with hiso
  · rw [if_pos hiso] at horth
    obtain ⟨φ⟩ := hiso
    have hdim : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = (Fintype.card G : ℂ) := by
      field_simp at horth
      simpa using horth
    rw [hsum, hc, hdim, div_mul_cancel₀ _ hc0] at htr
    have : μ = 1 := by
      have := mul_right_cancel₀ hd (htr.trans (one_mul _).symm)
      exact this
    rw [this, one_smul]
  · rw [if_neg hiso] at horth
    have hsum : ∑ g, σ.character g * ρ.character g⁻¹ = 0 := by
      simpa [hc0] using horth
    rw [hsum, mul_zero] at htr
    rw [(mul_eq_zero.mp htr).resolve_right hd, zero_smul]

theorem isIrr_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrr ρ := by
  unfold Representation.IsIrreducible at h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) (Subrepresentation.ext (Subsingleton.elim _ _))
  · rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h1 | h1
    · left
      exact congrArg Subrepresentation.toSubmodule h1
    · right
      exact congrArg Subrepresentation.toSubmodule h1

end CISum

open CISum in
set_option backward.isDefEq.respectTransparency false in
theorem central_idempotents_sum_one : CentralIdemSumOne := by
  intro G I _ _ _ V _ _ _ ρ hirr hne hfull
  classical
  set z : MonoidAlgebra ℂ G := ∑ i, centralIdem (ρ i) with hz
  have hcentral : ∀ x : MonoidAlgebra ℂ G, z * x = x * z := by
    intro x
    rw [hz, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hirr i).1
    exact (central_idempotent_holds G (V i) (ρ i) (hirr i).2).2 x

  have hact : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (σ : Representation ℂ G W), IsIrr σ → σ.asAlgebraHom z = 1 := by
    intro W _ _ _ σ hσ
    obtain ⟨i₀, φ, hφ⟩ := hfull W σ hσ

    rw [hz, map_sum, Finset.sum_eq_single i₀]
    · rw [centralIdem_act (ρ i₀) σ (hirr i₀) hσ, if_pos]
      exact ⟨(Representation.Equiv.mk φ (fun g => LinearMap.ext fun x => hφ g x)).symm⟩
    · intro i _ hi
      rw [centralIdem_act (ρ i) σ (hirr i) hσ, if_neg]
      rintro ⟨ψ⟩
      apply hi
      apply hne
      refine ⟨ψ.toLinearEquiv.trans φ, fun g x => ?_⟩
      have h1 : ψ (ρ i g x) = σ g (ψ x) := LinearMap.congr_fun (ψ.isIntertwining' g) x
      simp only [LinearEquiv.trans_apply]
      erw [h1]
      exact hφ g _
    · intro h; exact absurd (Finset.mem_univ _) h
  have : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩
  let N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    { carrier := {x | z * x = x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [mul_add, hx, hy]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc, hcentral a, mul_assoc, hx] }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G)]
    apply sSup_le
    intro S hS x hx
    have hS' : IsSimpleModule (MonoidAlgebra ℂ G) S := hS
    have hirrS := (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) S).mp hS'
    have hfd : FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) S) := by
      let ι : RestrictScalars ℂ (MonoidAlgebra ℂ G) S →ₗ[ℂ] MonoidAlgebra ℂ G :=
        { toFun := fun y => ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S y : S) :
            MonoidAlgebra ℂ G)
          map_add' := by intro a b; simp
          map_smul' := by
            intro c y
            simp [RestrictScalars.addEquiv_map_smul, Algebra.smul_def] }
      refine Module.Finite.of_injective ι ?_
      intro a b hab
      exact (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).injective (Subtype.ext hab)
    have h1 := hact _ (Representation.ofModule S) (isIrr_of_isIrreducible _ hirrS)
    have h2 := LinearMap.congr_fun h1 ((RestrictScalars.addEquiv _ _ _).symm ⟨x, hx⟩)
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at h2
    have h3 := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm.injective h2
    have h4 : z * x = x := by simpa using congrArg Subtype.val h3
    exact h4
  have h1 : (1 : MonoidAlgebra ℂ G) ∈ N := hN ▸ Submodule.mem_top
  have h2 : z * 1 = 1 := h1
  rwa [mul_one] at h2

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
