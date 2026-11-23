module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.RegNorm

theorem geom_mul (q m l : ℕ) (hq : 0 < q) :
    (q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) = (q ^ l) ^ m - 1 := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ (q ^ l) ^ m := Nat.one_le_pow _ _ (pow_pos hq _)
  have hZ : (((q ^ m : ℕ) : ℤ) - 1) * ∑ i ∈ Finset.range l, ((q ^ m : ℕ) : ℤ) ^ i
      = ((q ^ m : ℕ) : ℤ) ^ l - 1 := mul_geom_sum _ _
  have : (((q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) : ℕ) : ℤ) = (((q ^ l) ^ m - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    simp only [pow_mul] at *
    push_cast at hZ
    rw [hZ, ← pow_mul, ← pow_mul, mul_comm m l]
  exact_mod_cast this

theorem pow_modEq_pow_mod (q m x : ℕ) (hq : 1 ≤ q) :
    q ^ x ≡ q ^ (x % m) [MOD q ^ m - 1] := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have hm : q ^ m ≡ 1 [MOD q ^ m - 1] := Nat.modEq_sub h1
  calc q ^ x = (q ^ m) ^ (x / m) * q ^ (x % m) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / m) * q ^ (x % m) [MOD q ^ m - 1] := (hm.pow _).mul_right _
    _ = q ^ (x % m) := by simp

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin.RegNorm

theorem lift_iff (q m l k x y : ℕ) (hq : 0 < q) (hl : 0 < l) :
    (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * x ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * y
      [MOD (q ^ l) ^ m - 1] ↔ k * x ≡ k * y [MOD q ^ m - 1] := by
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hS : S ≠ 0 := by
    have : 0 < S := Finset.sum_pos (fun i _ => pow_pos hq _) ⟨0, by simp [hl]⟩
    omega
  rw [← geom_mul q m l hq, ← hSdef]
  have e1 : k * S * x = k * x * S := by ring
  have e2 : k * S * y = k * y * S := by ring
  rw [e1, e2]
  exact ⟨Nat.ModEq.mul_right_cancel' hS, Nat.ModEq.mul_right' S⟩

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin

theorem reg_norm_frob : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k →
    Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧
      ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡
        (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  intro q l m k hq hl hm hlm hreg
  have hq0 : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  refine ⟨?_, ?_⟩
  · intro i hi0 him h
    have h' : (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * (q ^ l) ^ i ≡
        (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * 1 [MOD (q ^ l) ^ m - 1] := by
      simpa using h
    have h2 := (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).1 h'
    rw [← pow_mul, mul_one] at h2
    have h3 : k * q ^ (l * i % m) ≡ k [MOD q ^ m - 1] :=
      ((RegNorm.pow_modEq_pow_mod q m (l * i) hq1).mul_left k).symm.trans h2
    refine hreg (l * i % m) ?_ (Nat.mod_lt _ hm) h3
    rcases Nat.eq_zero_or_pos (l * i % m) with h0 | h0
    · exfalso
      have hd : m ∣ l * i := Nat.dvd_of_mod_eq_zero h0
      have : m ∣ i := hcop.symm.dvd_of_dvd_mul_left hd
      exact absurd (Nat.le_of_dvd hi0 this) (by omega)
    · exact h0
  · have ha : ∃ a, l * a % m = 1 % m := by
      rcases Nat.lt_or_ge 1 m with h1 | h1
      · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
        exact ⟨a, by rw [ha, Nat.mod_eq_of_lt h1]⟩
      · have : m = 1 := by omega
        subst this
        exact ⟨0, by simp⟩
    obtain ⟨a, ha⟩ := ha
    refine ⟨a, (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).2 ?_⟩
    rw [← pow_mul]
    have e1 : q ^ 1 ≡ q ^ (1 % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m 1 hq1
    have e2 : q ^ (l * a) ≡ q ^ (l * a % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m (l * a) hq1
    rw [ha] at e2
    rw [pow_one] at e1
    exact (e1.trans e2.symm).mul_left k

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem Reg.not_modEq_of_lt {q N k u v : ℕ} (hq : 2 ≤ q) (h : Reg q N k) (huv : u < v) (hv : v < u + N) :
    ¬ k * q ^ v ≡ k * q ^ u [MOD q ^ N - 1] := by
  intro hmod
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  have hd0 : 0 < d := by omega
  have hdN : d < N := by omega
  have hN : 0 < N := by omega
  have hcop : Nat.Coprime (q ^ N - 1) (q ^ u) := by
    obtain ⟨t, ht⟩ : ∃ t, q ^ N = t + 1 := ⟨q ^ N - 1, by have := Nat.one_le_pow N q (by omega); omega⟩
    have h2 : Nat.Coprime (q ^ N - 1) (q ^ N) := by
      rw [ht, Nat.add_sub_cancel]
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right t)
    exact (h2.coprime_dvd_right (dvd_pow_self q hN.ne')).pow_right u
  have key : k * q ^ d ≡ k [MOD q ^ N - 1] := by
    apply Nat.ModEq.cancel_right_of_coprime (c := q ^ u) hcop
    have e : k * q ^ d * q ^ u = k * q ^ (u + d) := by ring
    rw [e]
    exact hmod
  exact h d hd0 hdN key

theorem reg_step_of_dvd : ∀ q l m k : ℕ, 2 ≤ q → 0 < l → 0 < m → Reg q (l * m) k →
    (∀ i, Reg (q ^ l) m (k * q ^ i)) ∧ (2 ≤ l * m → ∀ i, ¬ k * q ^ i ≡ 0 [MOD q ^ (l * m) - 1]) ∧
    ∀ i j a, i < l → j < l → a < m →
      (k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1] ↔ i = j ∧ a = 0) := by
  intro q l m k hq hl hm h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj0 hjm hmod
    simp only [← pow_mul] at hmod
    rw [mul_assoc, ← pow_add] at hmod
    have hlj : 0 < l * j := Nat.mul_pos hl hj0
    have hljm : l * j < l * m := (Nat.mul_lt_mul_left hl).mpr hjm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + l * j) (by omega : i + l * j < i + l * m) hmod
  · intro hlm i hmod
    have h1 : k * q ^ (i + 1) ≡ k * q ^ i [MOD q ^ (l * m) - 1] := by
      have e : k * q ^ (i + 1) = k * q ^ i * q := by ring
      rw [e]
      have h0 := hmod.mul_right q
      rw [zero_mul] at h0
      exact h0.trans hmod.symm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + 1) (by omega : i + 1 < i + l * m) h1
  · intro i j a hi hj ha
    constructor
    · intro hmod
      simp only [← pow_mul] at hmod
      rw [mul_assoc, ← pow_add] at hmod
      have hla : l * a + l ≤ l * m := by
        calc l * a + l = l * (a + 1) := by ring
          _ ≤ l * m := Nat.mul_le_mul_left l ha
      rcases lt_trichotomy (i + l * a) j with hlt | heq | hgt
      · exact absurd hmod.symm (Reg.not_modEq_of_lt hq h hlt (by omega))
      · rcases Nat.eq_zero_or_pos a with ha0 | ha0
        · subst ha0
          simp at heq
          exact ⟨heq, rfl⟩
        · have := Nat.le_mul_of_pos_right l ha0
          omega
      · exact absurd hmod (Reg.not_modEq_of_lt hq h hgt (by omega))
    · rintro ⟨rfl, rfl⟩
      simp [Nat.ModEq]

end GlobalTheory.Shin
end

section

open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section

variable {K : Type} [CommRing K]

theorem kaehlerZ_span_induction {P : Ω[K⁄ℤ] → Prop} (v : Ω[K⁄ℤ]) (hD : ∀ a, P (KaehlerDifferential.D ℤ K a))
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : K) x, P x → P (c • x)) : P v := by
  have hv : v ∈ Submodule.span K (Set.range (KaehlerDifferential.D ℤ K)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hD a
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem kaehlerZ_D_pow_char (c : K) : KaehlerDifferential.D ℤ K (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem extD_algebraMap_pow_char_mul {d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ]} (hd : IsExtD ℤ K d)
    (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]) :
    d (algebraMap K _ (c ^ p) * x) = algebraMap K _ (c ^ p) * d x := by
  rw [hd.mul, hd.alg, kaehlerZ_D_pow_char p, map_zero, zero_mul, zero_add]
  congr 1
  exact AlgHom.commutes _ _

end

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem isDatum_of_frobenius_lifts {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ])
    (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (hπ : IsFlatLift p π)
    (hF : ∀ i, IsFrob p π (F i)) (hd : IsExtD ℤ K d) (hf : ∀ i, IsF p π (F i) (f i))
    (hh : ∀ i j, IsH p π (F i) (F j) (h i j)) : IsDatum p d f h := by

  have hw : ∀ i z, ∃ w, F i z = z ^ p + p * w := by
    intro i z
    obtain ⟨w, hw⟩ := (hπ.ker (F i z - z ^ p)).1 (by rw [map_sub, hF i, map_pow, sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have hsm : ∀ (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]), d (c ^ p • x) = c ^ p • d x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, extD_algebraMap_pow_char_mul p hd]

  have hfD : ∀ i z w, F i z = z ^ p + p * w → ExteriorAlgebra.ι K (f i (KaehlerDifferential.D ℤ K (π z))) =
      algebraMap K _ (π z ^ (p - 1)) * ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z)) +
        d (algebraMap K _ (π w)) := by
    intro i z w hz
    rw [(hf i).2 z w hz, map_add (f := _), map_smul, Algebra.smul_def, hd.alg]
  refine ⟨fun i c v => (hf i).1 c v, fun i j c v => (hh i j).1 c v, ?_, ?_, ?_⟩
  · intro i v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨w, hz⟩ := hw i z
      have h2 : d (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z))) = 0 := by
        rw [← hd.alg, hd.sq]
      rw [hfD i z w hz, map_add (f := _), hd.sq, add_zero, hd.mul, h2, mul_zero, add_zero, hd.alg,
        Derivation.leibniz_pow, map_nsmul, map_smul, smul_mul_assoc, smul_mul_assoc,
        ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero]
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, add_zero]
    | hsmul c x hx => rw [(hf i).1, map_smul, hsm, hx, smul_zero]
  · intro i j v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), hfD i z wi hzi, hfD j z wj hzj, map_sub, map_sub,
        map_sub]
      abel
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]; abel
    | hsmul c x hx =>
      rw [(hh i j).1, (hf i).1, (hf j).1, map_mul, ← Algebra.smul_def, hsm, hx, map_smul, map_smul, smul_sub]
  · intro i j l v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      obtain ⟨wl, hzl⟩ := hw l z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), (hh j l).2 z (wl - wj) (by rw [hzj, hzl]; ring),
        (hh i l).2 z (wl - wi) (by rw [hzi, hzl]; ring), map_sub, map_sub, map_sub]
      ring
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), ← hx, ← hy]; ring
    | hsmul c x hx => rw [(hh i j).1, (hh j l).1, (hh i l).1, ← hx]; ring

end GlobalTheory.DI
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem adjoin_conj_inPar : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → InPar a (y₀⁻¹ * γ * y₀) → InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
  intro F F' _ _ _ a n γ y₀ δ hδ hγ

  let T : Subalgebra F' (Matrix (Fin n) (Fin n) F') :=
    { carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0}
      mul_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : (k : ℕ) < a
        · rw [hM i k hk hi, zero_mul]
        · rw [hN k j hj (not_lt.1 hk), mul_zero]
      add_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]
      algebraMap_mem' := by
        intro r i j hj hi
        have hij : i ≠ j := by
          intro h; subst h; omega
        simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne hij] }
  let c : GL (Fin n) F' := incl F F' n y₀
  have key : ∀ (M : Matrix (Fin n) (Fin n) F') (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}),
      ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * M * (c : Matrix (Fin n) (Fin n) F') ∈ T := by
    intro M hM
    induction hM using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (c : Matrix (Fin n) (Fin n) F')
          = ((incl F F' n (y₀⁻¹ * γ * y₀) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
        simp only [c, map_mul, map_inv, Units.val_mul]
      rw [e]
      intro i j hj hi
      simp only [incl, gal, Matrix.GeneralLinearGroup.map_apply]
      rw [hγ i j hj hi, map_zero]
    | algebraMap r =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * algebraMap F' (Matrix (Fin n) (Fin n) F') r * (c : Matrix (Fin n) (Fin n) F')
          = algebraMap F' (Matrix (Fin n) (Fin n) F') r := by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
      rw [e]; exact T.algebraMap_mem r
    | add x y _ _ hx hy =>
      rw [mul_add, add_mul]; exact T.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (x * y) * (c : Matrix (Fin n) (Fin n) F')
          = (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * x * (c : Matrix (Fin n) (Fin n) F')) *
            (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * y * (c : Matrix (Fin n) (Fin n) F')) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [e]; exact T.mul_mem hx hy
  intro i j hj hi
  have := key _ hδ i j hj hi
  simpa [c, Units.val_mul] using this

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

namespace FrobTwist

def Tw (K V : Type) [CommRing K] [AddCommGroup V] [Module K V] : Type := ExteriorAlgebra K V

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

instance : Ring (Tw K V) := inferInstanceAs (Ring (ExteriorAlgebra K V))

abbrev twAlg (p : ℕ) [Fact p.Prime] [CharP K p] : Algebra K (Tw K V) :=
  RingHom.toAlgebra' ((algebraMap K (ExteriorAlgebra K V)).comp (frobenius K p))
    (fun c x => Algebra.commutes (R := K) (A := ExteriorAlgebra K V) _ x)

end FrobTwist


open FrobTwist in
theorem exists_isGamma {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (p : ℕ)
    [Fact p.Prime] [CharP K p] (f : V →+ V) (hf : ∀ (c : K) v, f (c • v) = c ^ p • f v) :
    ∃ γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V, IsGamma p f γ := by
  letI : Algebra K (Tw K V) := twAlg p
  let g : V →ₗ[K] Tw K V :=
    { toFun := fun v => (ExteriorAlgebra.ι K (f v) : ExteriorAlgebra K V)
      map_add' := fun v w => by
        show ExteriorAlgebra.ι K (f (v + w)) = ExteriorAlgebra.ι K (f v) + ExteriorAlgebra.ι K (f w)
        rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c v => by
        have h1 : ExteriorAlgebra.ι K (f (c • v)) =
            algebraMap K (ExteriorAlgebra K V) (c ^ p) * ExteriorAlgebra.ι K (f v) := by
          rw [hf, map_smul, Algebra.smul_def]
        exact h1 }
  have hg : ∀ v, g v * g v = 0 := fun v => ExteriorAlgebra.ι_sq_zero (R := K) (f v)
  let Γ : ExteriorAlgebra K V →ₐ[K] Tw K V := ExteriorAlgebra.lift K ⟨g, hg⟩
  refine ⟨(Γ.toRingHom : ExteriorAlgebra K V →+* ExteriorAlgebra K V), ?_, ?_⟩
  · intro c
    have := Γ.commutes c
    exact this
  · intro v
    have := ExteriorAlgebra.lift_ι_apply K (A := Tw K V) g hg v
    exact this

end GlobalTheory.DI
end
end

section

set_option autoImplicit false

namespace GlobalTheory.DI


set_option autoImplicit false in
theorem _root_.GlobalTheory.DI.logLift_of_unit_mem_map : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (At : Subring Kt), _root_.GlobalTheory.DI.IsFlatLift p π →
    (∀ i ∈ s, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w) → ∀ g : K, g ≠ 0 → g ∈ At.map π →
    g⁻¹ ∈ At.map π → _root_.GlobalTheory.DI.LogLift p π F s (At.map π : Set K) g := by
  intro K Kt _ _ p _ _ π ι F s At hflat hF g hg hmem hinv
  obtain ⟨z, hz, rfl⟩ := Subring.mem_map.mp hmem
  obtain ⟨y, hy, hyz⟩ := Subring.mem_map.mp hinv
  unfold _root_.GlobalTheory.DI.LogLift
  refine ⟨z, rfl, fun i hi => ?_⟩
  obtain ⟨w, hw, hFw⟩ := hF i hi z hz
  refine ⟨y ^ p * w, Subring.mem_map.mpr ⟨y ^ p * w, At.mul_mem (At.pow_mem hy p) hw, rfl⟩, ?_⟩
  have h0 : (p : Kt) * (w - z ^ p * y ^ p * w) = 0 := by
    rw [hflat.ann]
    simp only [map_sub, map_mul, map_pow, hyz]
    rw [← mul_pow, mul_inv_cancel₀ hg, one_pow, one_mul, sub_self]
  rw [hFw]
  linear_combination h0

end GlobalTheory.DI
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem ch_eq_exp_pow_val (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I / N) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]; congr 1; ring

theorem exists_unit_zetaAct : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ), ∃ a : (ZMod N)ˣ, ZetaAct g N a := by
  intro N _ g
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hg : IsPrimitiveRoot (g (Complex.exp (2 * Real.pi * Complex.I / N))) N :=
    hζ.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime N := by
    rw [← hi] at hg
    exact (hζ.pow_iff_coprime (NeZero.pos N) i).mp hg
  refine ⟨ZMod.unitOfCoprime i hcop, fun j => ?_⟩
  rw [ch_eq_exp_pow_val, ch_eq_exp_pow_val, map_pow, ← hi, ← pow_mul, ZMod.coe_unitOfCoprime,
    ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  conv_lhs => rw [← Nat.div_add_mod (i * j.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.WpFam
end
