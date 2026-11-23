module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace UpperTheory.Small

open Formalism.BasicNotions NumberField IsDedekindDomain Ideal
open scoped Pointwise

variable {R : Ranks} (H : Host R)

theorem exists_unit_neg : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] ∧ (H.art u).1.1 = -1 := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hdq : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).2 (by omega)
  have hsq : Nat.Coprime H.QS H.q := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) H.QS_coprime
  have hcop : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left hsq hdq
  obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder hcop 1 (H.q - 1)
  have hq2 : 2 ≤ H.q := hq.two_le
  have hxm : Nat.Coprime x (H.QS * H.d) := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hx1]; simp
  have hxq : Nat.Coprime x H.q := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hx2]
    have : H.q - 1 + 1 = H.q := by omega
    rw [← this, Nat.gcd_comm]; simp
  have hxN : Nat.Coprime x H.condN := by
    have e : H.condN = H.QS * H.d * H.q := by simp only [Formalism.HC.HostRaw.condN]; ring
    rw [e]; exact Nat.Coprime.mul_right hxm hxq
  refine ⟨ZMod.unitOfCoprime x hxN, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    refine Nat.ModEq.trans ?_ hx1
    refine Nat.ModEq.of_dvd ?_ (Nat.mod_modEq x _)
    exact ⟨H.q, by simp only [Formalism.HC.HostRaw.condN]; ring⟩
  · have h := H.flPS (ZMod.unitOfCoprime x hxN)
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast] at h
    have hJ : jacobiSym ((x % H.condN : ℕ) : ℤ) H.q = -1 := by
      rw [jacobiSym.mod_left]
      have h3 : ((x % H.condN : ℕ) : ℤ) % (H.q : ℤ) = (-1 : ℤ) % (H.q : ℤ) := by
        have hqN : H.q ∣ H.condN := ⟨H.QS * H.d, by simp only [Formalism.HC.HostRaw.condN]; ring⟩
        have h4 : x % H.condN % H.q = H.q - 1 := by
          rw [Nat.mod_mod_of_dvd _ hqN, hx2, Nat.mod_eq_of_lt (by omega)]
        rw [← Int.natCast_mod, h4]
        push_cast [Nat.cast_sub (by omega : 1 ≤ H.q)]
        rw [show (-1 : ℤ) = ((H.q : ℤ) - 1) + (-1) * (H.q : ℤ) by ring, Int.add_mul_emod_self_right,
          Int.emod_eq_of_lt] <;> omega
      rw [h3, ← jacobiSym.mod_left, jacobiSym.at_neg_one (hq.odd_of_ne_two (by omega))]
      exact ZMod.χ₄_nat_three_mod_four (by omega)
    rw [hJ] at h
    exact Units.ext (by simpa using h)

theorem inertia_q : ∃ g : R.GG, g ≠ 1 ∧ ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.q : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = g) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  haveI : Fact (Nat.Prime H.q) := ⟨hq⟩
  obtain ⟨u0, hu0, hneg⟩ := exists_unit_neg H
  have hdq : Nat.Coprime H.d H.q := (Nat.coprime_primes hd hq).2 (by omega)
  have hsq : Nat.Coprime H.QS H.q := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) H.QS_coprime
  have hcop : Nat.Coprime (H.QS * H.d) H.q := Nat.Coprime.mul_left hsq hdq
  have hN : H.condN = H.QS * H.d * H.q := by simp only [Formalism.HC.HostRaw.condN]; ring
  have hNpos : 0 < H.condN := by
    rw [hN]; exact Nat.mul_pos (Nat.mul_pos H.QS_pos hd.pos) hq.pos
  haveI : NeZero H.condN := ⟨hNpos.ne'⟩
  have hfq : H.condN.factorization H.q = 1 := by
    rw [hN, Nat.factorization_mul (Nat.mul_pos H.QS_pos hd.pos).ne' hq.ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization_self hq, Nat.factorization_eq_zero_of_not_dvd]
    intro h
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) h)
  have hfac : H.condN / H.q ^ H.condN.factorization H.q = H.QS * H.d := by
    rw [hfq, pow_one, hN, Nat.mul_div_cancel _ hq.pos]
  have hmN : H.QS * H.d ∣ H.condN := ⟨H.q, hN⟩
  have hqN : H.q ∣ H.condN := ⟨H.QS * H.d, by rw [hN]; ring⟩
  let f : (ZMod H.condN)ˣ →* (ZMod (H.QS * H.d))ˣ :=
    Units.map (ZMod.castHom hmN (ZMod (H.QS * H.d))).toMonoidHom
  have hmem : ∀ u : (ZMod H.condN)ˣ, u ∈ f.ker ↔ (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff]
    change ((u : ZMod H.condN).cast : ZMod (H.QS * H.d)) = 1 ↔ _
    rw [ZMod.cast_eq_val, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  let fq : f.ker →* (ZMod H.q)ˣ :=
    (Units.map (ZMod.castHom hqN (ZMod H.q)).toMonoidHom).comp f.ker.subtype
  have hinj : Function.Injective fq := by
    intro a b hab
    have ha := (hmem a).1 a.2
    have hb := (hmem b).1 b.2
    have hab' : ((a.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ ((b.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val [MOD H.q] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have := congrArg (fun x : (ZMod H.q)ˣ => (x : ZMod H.q)) hab
      change (((a.1 : (ZMod H.condN)ˣ) : ZMod H.condN).cast : ZMod H.q) = ((b.1 : (ZMod H.condN)ˣ) : ZMod H.condN).cast at this
      rwa [ZMod.cast_eq_val, ZMod.cast_eq_val] at this
    have hall : ((a.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ ((b.1 : (ZMod H.condN)ˣ) : ZMod H.condN).val [MOD H.condN] := by
      have h0 := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨ha.trans hb.symm, hab'⟩
      rwa [← hN] at h0
    apply Subtype.ext; apply Units.ext
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hall
    exact hall
  haveI : IsCyclic f.ker := isCyclic_of_injective fq hinj
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := f.ker)
  have hc2 : H.art (c : (ZMod H.condN)ˣ) ^ 2 = 1 := H.art_q _ ((hmem _).1 c.2)
  have key : ∀ u : (ZMod H.condN)ˣ, u ∈ f.ker → H.art u = 1 ∨ H.art u = H.art c := by
    intro u hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨u, hu⟩)
    have hu' : u = (c : (ZMod H.condN)ˣ) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [hu', map_zpow]
    have hc2' : H.art (c : (ZMod H.condN)ˣ) ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hc2
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left; rw [zpow_mul, hc2', one_zpow]
    · right; rw [zpow_add, zpow_mul, hc2', one_zpow, one_mul, zpow_one]
  have hu0k : u0 ∈ f.ker := (hmem u0).2 hu0
  have hg : H.art u0 = H.art c := by
    rcases key u0 hu0k with h | h
    · rw [h, Prod.fst_one, Prod.fst_one] at hneg; exact absurd hneg (by decide)
    · exact h
  refine ⟨H.art u0, ?_, ?_⟩
  · intro h; rw [h, Prod.fst_one, Prod.fst_one] at hneg; exact absurd hneg (by decide)
  · intro P _ _ σ
    rw [H.der.inertia H.q P σ, hfac]
    constructor
    · rintro ⟨u, hu, he⟩
      rw [he]
      rcases key u ((hmem u).2 hu) with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hg.symm)
    · rintro (h | h)
      · exact ⟨1, (hmem 1).1 (one_mem _), by rw [h, map_one]⟩
      · exact ⟨u0, hu0, h⟩

end UpperTheory.Small
end

section

noncomputable section

namespace UpperTheory.KStar.Words

open Formalism.HC Formalism.FrobeniusOrbits

variable {φ : Frame}

theorem cc_mul_cc : φ.cc * φ.cc = 1 := by
  show ((c0, (1 : φ.MA)) : G0 × φ.MA) * (c0, 1) = 1
  simp [c0]

theorem orderOf_moving (g : φ.GG) (h : g.1.2 = -1) : orderOf g = Nat.lcm 2 (orderOf g.2) := by
  have h1 : orderOf g.1 = 2 := by
    rw [Prod.orderOf, h]
    have ha : orderOf g.1.1 ∣ 2 := orderOf_dvd_of_pow_eq_one (Int.units_sq g.1.1)
    have hn : orderOf (-1 : ℤˣ) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [hn]
    exact Nat.lcm_eq_right ha
  rw [Prod.orderOf, h1]

theorem placeOf_cc_mul (g : φ.GG) : Frame.placeOf (φ.cc * g) = Frame.placeOf g := by
  have hc : (φ.cc * g).1.2 = -g.1.2 := by
    show (((c0, (1 : φ.MA)) : G0 × φ.MA) * g).1.2 = -g.1.2
    simp [c0]
  unfold Frame.placeOf
  rcases Int.units_eq_one_or g.1.2 with h | h
  · rw [if_neg (by rw [hc, h]; decide), if_pos h, ← mul_assoc, cc_mul_cc, one_mul]
  · rw [if_pos (by rw [hc, h]; decide), if_neg (by rw [h]; decide)]

theorem placeOf_snd (g : φ.GG) : (Frame.placeOf g).2 = g.2 := by
  unfold Frame.placeOf
  split_ifs
  · rfl
  · show (((c0, (1 : φ.MA)) : G0 × φ.MA) * g).2 = g.2
    simp

theorem placeOf_eq_iff (x y : φ.GG) : Frame.placeOf x = Frame.placeOf y ↔ x = y ∨ x = φ.cc * y := by
  constructor
  · intro hxy
    unfold Frame.placeOf at hxy
    split_ifs at hxy with hx hy hy
    · exact Or.inl hxy
    · exact Or.inr hxy
    · right
      rw [← hxy, ← mul_assoc, cc_mul_cc, one_mul]
    · exact Or.inl (mul_left_cancel hxy)
  · rintro (rfl | rfl)
    · rfl
    · exact placeOf_cc_mul y

theorem placeOf_letter_eq_iff (τ g : φ.GG) (a b : ℕ) :
    Frame.placeOf (τ * g ^ a) = Frame.placeOf (τ * g ^ b) ↔ g ^ a = g ^ b ∨ g ^ a = φ.cc * g ^ b := by
  rw [placeOf_eq_iff, mul_left_comm φ.cc τ, mul_left_cancel_iff, mul_left_cancel_iff]

theorem pow_val_add (g : φ.GG) (i : ZMod (orderOf g)) (k : ℕ) :
    g ^ (i + (k : ZMod (orderOf g))).val = g ^ (i.val + k) := by
  haveI : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, pow_mod_orderOf]

theorem placeOf_letter_succ_ne (τ g : φ.GG) (h1 : g ≠ 1) (hc : g ≠ φ.cc) (i : ZMod (orderOf g)) :
    Frame.placeOf (τ * g ^ (i + 1).val) ≠ Frame.placeOf (τ * g ^ i.val) := by
  intro heq
  have hv := pow_val_add g i 1
  rw [Nat.cast_one] at hv
  rw [placeOf_letter_eq_iff, hv, pow_succ] at heq
  rcases heq with h | h
  · exact h1 (by simpa using h)
  · apply hc
    rw [mul_comm φ.cc] at h
    exact mul_left_cancel h

theorem thick_one_place {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (u₀ : φ.A) (τ g : φ.GG)
    (hord : orderOf (φ.hH g.2) ≤ 4 * L) (a b : ℕ)
    (ha : ∃ s ∈ T, φ.tau2 (φ.dig s + u₀) = Frame.placeOf (τ * g ^ a))
    (hb : ∃ s ∈ T, φ.tau2 (φ.dig s + u₀) = Frame.placeOf (τ * g ^ b)) :
    Frame.placeOf (τ * g ^ a) = Frame.placeOf (τ * g ^ b) := by
  obtain ⟨s, hs, hsa⟩ := ha
  obtain ⟨s', hs', hsb⟩ := hb
  have mem : ∀ (n s : ℕ), s ∈ T → φ.tau2 (φ.dig s + u₀) = Frame.placeOf (τ * g ^ n) →
      φ.dig s + u₀ ∈ {y | (∃ i : ℤ, y = φ.iotaInv τ.2 + i • φ.iotaInv g.2) ∧ φ.InTranslate T u₀ y} := by
    intro n s hsT hsn
    refine ⟨⟨(n : ℤ), ?_⟩, s, hsT, rfl⟩
    have h2 := congrArg Prod.snd hsn
    rw [placeOf_snd] at h2
    have h3 : φ.iota (φ.dig s + u₀) = τ.2 * g.2 ^ n := by
      rw [← Prod.pow_snd, ← Prod.snd_mul]
      exact h2
    rw [← φ.iotaInv_iota (φ.dig s + u₀), h3, natCast_zsmul]
    unfold Frame.iotaInv
    rw [toAdd_mul, toAdd_pow]
  have hord' : addOrderOf (φ.h (φ.iotaInv g.2)) ≤ 4 * L := by
    rw [← φ.orderOf_hH_iota, φ.iota_iotaInv]
    exact hord
  have hle := φ.thick_part_two T hT u₀ (φ.iotaInv τ.2) (φ.iotaInv g.2) hord'
  have heq := (Set.ncard_le_one).1 hle _ (mem a s hs hsa) _ (mem b s' hs' hsb)
  rw [← hsa, ← hsb, heq]

end UpperTheory.KStar.Words

end
end
