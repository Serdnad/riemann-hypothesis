module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Formalism.LocalToGlobal.CharacterGerms.GeOfPowEqOne
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Lemmata.PowMulVecEigen.PowMulVecEig
public import Formalism.LocalToGlobal.CharacterGerms.Bundle004
public import Formalism.DropLevelBounds.ThBounds
public import Formalism.LocalToGlobal.Divisibility.Numbers
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finite.Basic
import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.Bundle013
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB
import Formalism.LocalToGlobal.CharacterGerms.Bundle018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace TypAr

variable {C : Type} [Field C] {V : VF C}

theorem ge_lpow (k : ℕ) : V.Ge (k : ℝ) ((V.l : C) ^ k) := by
  induction k with
  | zero => simpa using VF.Ge.one (V := V)
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul VF.ge_l
    convert this using 1
    push_cast; ring

theorem ge_of_lpow_dvd {k m : ℕ} (h : V.l ^ k ∣ m) : V.Ge (k : ℝ) (m : C) := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, Nat.cast_pow]
  simpa using (ge_lpow (V := V) k).mul (VF.ge_natCast t)

theorem vlim_const {N : Type} {a : ℕ → C} {b : C} (h : ∀ K : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (b - a k)) :
    VLim V (fun k (_ : ℕ) (_ : N) => a k) (fun _ _ => b) := fun K _ _ => h K

theorem eventually_ge_nat (K : ℝ) (c : ℕ) : ∃ k0 : ℕ, ∀ k ≥ k0, K ≤ ((k + c : ℕ) : ℝ) := by
  obtain ⟨k0, hk0⟩ := exists_nat_ge K
  refine ⟨k0, fun k hk => ?_⟩
  have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  linarith

theorem typ_gen {N : Type} (M : Set (ℕ → N → C))
    (hroot : ∀ p : ℕ, p.Prime → p ≠ V.l → ∃ ζ : C, IsPrimitiveRoot ζ p)
    (h1 : 1 ∈ M) (hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M) (hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M)
    (hteich : ∀ c : C, V.Ge 0 c → (fun n (_ : N) => c ^ n) ∈ M)
    (hlim : ∀ (m : ℕ → ℕ → N → C) (m' : ℕ → N → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M) :
    (fun n (_ : N) => if ∃ s, V.l ^ s = n then (1 : C) else 0) ∈ M := by
  have hl2 := V.l_prime.two_le

  have hconst : ∀ k : ℕ, (fun (_ : ℕ) (_ : N) => ((k + 1 : ℕ) : C)) ∈ M := by
    intro k
    induction k with
    | zero => convert h1 using 1; funext n x; simp
    | succ k ih =>
      have := hadd _ _ ih h1
      convert this using 1
      funext n x; simp only [Pi.add_apply, Pi.one_apply]; push_cast; ring

  have h0 : (0 : ℕ → N → C) ∈ M := by
    have hm : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) ∈ M := fun k => hconst _
    have e : ∀ k, ((V.l ^ k - 1 + 1 : ℕ) : C) = (V.l : C) ^ k := fun k => by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ V.l_prime.pos)]; push_cast; rfl
    refine hlim (fun k (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) 0 hm ?_
    intro K s x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 0
    refine ⟨k0, fun k hk => ?_⟩
    simp only [Pi.zero_apply, zero_sub, e]
    exact ((ge_lpow k).neg).mono (by simpa using hk0 k hk)

  have hneg : ∀ m, m ∈ M → -m ∈ M := by
    intro m hm
    have hc : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) * m ∈ M :=
      fun k => hmul _ _ (hconst _) hm
    have e : ∀ k, ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C) = (V.l : C) ^ (k + 1) - 1 := fun k => by
      have h2 : 2 ≤ V.l ^ (k + 1) := le_trans hl2 (Nat.le_self_pow (Nat.succ_ne_zero k) _)
      have : V.l ^ (k + 1) - 2 + 1 = V.l ^ (k + 1) - 1 := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hv : VLim V (fun k (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) (fun _ _ => (-1 : C)) := by
      apply vlim_const
      intro K
      obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
      refine ⟨k0, fun k hk => ?_⟩
      rw [e]
      have : (-1 : C) - ((V.l : C) ^ (k + 1) - 1) = -((V.l : C) ^ (k + 1)) := by ring
      rw [this]
      exact ((ge_lpow (k + 1)).neg).mono (by simpa using hk0 k hk)
    have := hlim _ _ hc (hv.mul_right m)
    convert this using 1
    funext n x; simp
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∑ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact hadd _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∏ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact hmul _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hpow : ∀ m, m ∈ M → ∀ e : ℕ, m ^ e ∈ M := by
    intro m hm e
    induction e with
    | zero => simpa using h1
    | succ e ih => rw [pow_succ]; exact hmul _ _ ih hm

  have hD : ∀ p : ℕ, p.Prime → p ≠ V.l → (fun n (_ : N) => if p ∣ n then (1 : C) else 0) ∈ M := by
    intro p hp hpl
    obtain ⟨ζ, hζ⟩ := hroot p hp hpl
    have hζi : ∀ j : ℕ, V.Ge 0 (ζ ^ j) := fun j =>
      VF.ge_of_pow_eq_one V hp.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    set G : ℕ → N → C := ∑ j ∈ Finset.range p, fun n (_ : N) => (ζ ^ j) ^ n with hG
    have hGM : G ∈ M := hsum _ _ fun j _ => hteich _ (hζi j)
    have hGv : ∀ n x, G n x = if p ∣ n then (p : C) else 0 := by
      intro n x
      rw [hG, Finset.sum_apply, Finset.sum_apply]
      have e : ∀ j ∈ Finset.range p, (ζ ^ j) ^ n = (ζ ^ n) ^ j := fun j _ => by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [Finset.sum_congr rfl e]
      by_cases hn : p ∣ n
      · rw [if_pos hn]
        obtain ⟨t, rfl⟩ := hn
        rw [pow_mul, hζ.pow_eq_one, one_pow]
        simp
      · rw [if_neg hn]
        have hcop : n.Coprime p := (Nat.coprime_comm.trans (Nat.Prime.coprime_iff_not_dvd hp)).mpr hn
        exact (hζ.pow_of_coprime n hcop).geom_sum_eq_zero hp.one_lt
    refine hlim (fun k => G ^ Nat.totient (V.l ^ (k + 1))) _ (fun k => hpow _ hGM _) ?_
    intro K n x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
    refine ⟨k0, fun k hk => ?_⟩
    have hφ : 0 < Nat.totient (V.l ^ (k + 1)) := Nat.totient_pos.mpr (pow_pos V.l_prime.pos _)
    show V.Ge K ((if p ∣ n then (1 : C) else 0) - (G ^ Nat.totient (V.l ^ (k + 1))) n x)
    rw [Pi.pow_apply, Pi.pow_apply, hGv]
    by_cases hn : p ∣ n
    · rw [if_pos hn, if_pos hn]
      have hcop : p.Coprime (V.l ^ (k + 1)) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp V.l_prime).mpr hpl)
      have hmod := Nat.ModEq.pow_totient hcop
      have hdvd : V.l ^ (k + 1) ∣ p ^ Nat.totient (V.l ^ (k + 1)) - 1 :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp hmod.symm
      have hge := ge_of_lpow_dvd (V := V) hdvd
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, Nat.cast_one] at hge
      have : (1 : C) - (p : C) ^ Nat.totient (V.l ^ (k + 1)) = -((p : C) ^ Nat.totient (V.l ^ (k + 1)) - 1) := by ring
      rw [this]
      exact hge.neg.mono (by simpa using hk0 k hk)
    · rw [if_neg hn, if_neg hn, zero_pow hφ.ne', sub_zero]
      exact VF.Ge.zero K

  set S : ℕ → Finset ℕ := fun P => (Finset.range (P + 1)).filter fun p => p.Prime ∧ p ≠ V.l with hS
  set T : ℕ → ℕ → N → C := fun P => ∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0)) with hT
  have hTM : ∀ P, T P ∈ M := fun P => hprod _ _ fun p hp => by
    have hp' := (Finset.mem_filter.mp hp).2
    exact hadd _ _ h1 (hneg _ (hD p hp'.1 hp'.2))
  refine hlim T _ hTM ?_
  intro K n x
  refine ⟨n + 3, fun P hP => ?_⟩
  show V.Ge K ((if ∃ s, V.l ^ s = n then (1 : C) else 0) - T P n x)
  have hTv : T P n x = ∏ p ∈ S P, (1 - if p ∣ n then (1 : C) else 0) := by
    show (∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0))) n x = _
    rw [Finset.prod_apply, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro p _
    simp [sub_eq_add_neg]
  rw [hTv]
  by_cases hpow' : ∃ s, V.l ^ s = n
  · rw [if_pos hpow']
    obtain ⟨s, rfl⟩ := hpow'
    have : ∏ p ∈ S P, (1 - if p ∣ V.l ^ s then (1 : C) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hnd : ¬ p ∣ V.l ^ s := fun h => hp'.2 ((Nat.prime_dvd_prime_iff_eq hp'.1 V.l_prime).mp (hp'.1.dvd_of_dvd_pow h))
      rw [if_neg hnd, sub_zero]
    rw [this, sub_self]
    exact VF.Ge.zero K
  · rw [if_neg hpow']
    have hex : ∃ p ∈ S P, p ∣ n := by
      by_cases hn0 : n = 0
      · subst hn0
        by_cases hl2' : V.l = 2
        · refine ⟨3, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_three, by omega⟩, dvd_zero 3⟩
        · refine ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two, fun h => hl2' h.symm⟩, dvd_zero 2⟩
      · by_contra hne
        push_neg at hne
        apply hpow'
        refine ⟨n.primeFactorsList.length, (Nat.eq_prime_pow_of_unique_prime_dvd hn0 ?_).symm⟩
        intro q hq hqn
        by_contra hql
        have hqle : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqn
        exact hne q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hql⟩) hqn
    obtain ⟨p, hpS, hpn⟩ := hex
    rw [Finset.prod_eq_zero hpS (by rw [if_pos hpn, sub_self]), sub_zero]
    exact VF.Ge.zero K

end TypAr

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

structure KeyData (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) where
  ρ : O →+* Matrix (Fin n) (Fin n) C
  ρ_int : ∀ x i j, V.Ge 0 (ρ x i j)
  P : Matrix (Fin n) (Fin n) C
  em : ZMod d → (O →+* C)
  em_int : ∀ a x, V.Ge 0 (em a x)
  em_frob : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)
  ε : O
  ε_idem : ∃ y, ε * ε - ε = (V.l : O) * y
  ε_one : ∀ a, V.MM (em a ε - 1)
  ε_ann : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y
  P_lim : ∀ (N : ℕ) i j, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (P i j - ρ (ε ^ V.l ^ n) i j)

def KeyEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (v : Fin n → C),
      ∃ (m : ℕ) (w : Fin m → Fin n → C) (χ : Fin m → (O →+* C)),
        Matrix.mulVec K.P v = ∑ j, w j ∧ ∀ j, Matrix.mulVec K.P (w j) = w j ∧
          ∀ x, Matrix.mulVec (K.ρ x) (w j) = χ j x • w j

def KeyResSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) [NeZero d]
    (K : KeyData C V O n d) (χ : O →+* C), (∀ y, V.Ge 0 (χ y)) →
    (∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z)) → ∃ c, ∀ y, V.MM (χ y - K.em c y)

def KeyDeltaSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) [NeZero d]
    (K : KeyData C V O n d) (χ : O →+* C) (c : ZMod d), (∀ y, V.Ge 0 (χ y)) →
    (∀ y, V.MM (χ y - K.em c y)) → ∀ y, χ y = K.em c y

section Lemmas

variable {C : Type} [Field C] {V : VF C}

theorem aeval_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (f : Polynomial C) :
    Matrix.mulVec (Polynomial.aeval A f) w = f.eval lam • w := by
  first | exact Bl.PowMulVecEigen.goal1 .. | (apply Bl.PowMulVecEigen.goal1 <;> assumption) | (intros; apply Bl.PowMulVecEigen.goal1 <;> assumption) | (apply @Bl.PowMulVecEigen.goal1 <;> assumption) | (intros; apply @Bl.PowMulVecEigen.goal1 <;> assumption) | (apply @Bl.PowMulVecEigen.goal1 <;> first | assumption | infer_instance)

theorem eig_int {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (hA : ∀ i j, V.Ge 0 (A i j)) (w : Fin n → C) (hw : w ≠ 0)
    (lam : C) (h : Matrix.mulVec A w = lam • w) : V.Ge 0 lam := by
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => V.v (w i)) ⟨i0, Finset.mem_univ _⟩
  have hwi : w i ≠ 0 := by
    intro h0
    have := hi i0 (Finset.mem_univ _)
    rw [h0, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hi0 this
  have hrow : lam * w i = ∑ j, A i j * w j := by
    have := congrFun h i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hge : V.v (w i) ≤ V.v (lam * w i) := by
    rw [hrow]
    refine AddValuation.map_le_sum V.v fun j _ => ?_
    rw [AddValuation.map_mul]
    have h1 := hA i j
    unfold VF.Ge at h1
    calc V.v (w i) ≤ V.v (w j) := hi j (Finset.mem_univ _)
      _ = 0 + V.v (w j) := (zero_add _).symm
      _ ≤ V.v (A i j) + V.v (w j) := add_le_add (by exact_mod_cast h1) le_rfl
  rw [AddValuation.map_mul] at hge
  unfold VF.Ge
  have hne : V.v (w i) ≠ ⊤ := (AddValuation.ne_top_iff V.v).mpr hwi
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hr] at hge
  by_contra hlt
  push_neg at hlt
  have h2 : V.v lam + (r : WithTop ℝ) < 0 + (r : WithTop ℝ) := by
    exact WithTop.add_lt_add_right (WithTop.coe_ne_top) hlt
  rw [zero_add] at h2
  exact absurd (lt_of_le_of_lt hge h2) (lt_irrefl _)

end Lemmas

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

def i0 (k l : ℕ) : ℕ := sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}

def ThlEq : Prop := ∀ k l : ℕ, 1 ≤ k → 2 ≤ l →
  Odd (i0 k l) ∧ 3 ≤ i0 k l ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i0 k l ∧
    thl k l = ((l : ℝ) ^ i0 k l)⁻¹

def LevelBound : Prop := ∀ k l : ℕ, 1 ≤ k → 5 ≤ l → ((i0 k l : ℝ) - 1) ≤ 2 + 2 * Real.log k

structure Plan (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) where
  y : ZMod d → ℕ → ℕ
  u : ZMod d → ℕ
  supp : ∀ a i, i ∉ oddLevels d → y a i = 0
  bal : ∀ a, W a = (∑ i ∈ oddLevels d, l ^ i * y a i) +
    (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) + u a

def Plan.triv (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) : Plan l d W where
  y := fun _ _ => 0
  u := W
  supp := fun _ _ _ => rfl
  bal := fun a => by simp

def blockBd (l n m i y : ℕ) : ℝ :=
  if y = 0 then 0 else bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)

def chBd (l n m u : ℕ) : ℝ := (u : ℝ) * (n * gam l + m / ((l : ℝ) - 1))

def Plan.bound {l d : ℕ} [NeZero d] {W : ZMod d → ℕ} (p : Plan l d W) (n m : ℕ) : ℝ :=
  (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (p.y a i)) + ∑ a, chBd l n m (p.u a)

def Windows (S : ℕ) (G : Set ℕ) : Prop := 0 ∈ G ∧ ∀ Y0 : ℕ, ∃ y ∈ G, Y0 ≤ y ∧ y < Y0 + S

def IsReps (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) : Prop :=
  ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z'

def alongOrb {X : Type} (N : NumDatum) (l : ℕ) (z : RPl N.R) (W : RPl N.R → X) : ZMod (N.ordP l) → X :=
  fun s => W (N.pos l z s.val)

def FInertReps : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    N.FInert j l = ∑ z ∈ Z, Fnum l (N.ordP l)
        (fun s => ((N.R.k : ℝ) - 1) * alongOrb N l z (N.w j) s) ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → N.FjP j l = N.FInert j l)

def LemmaFe : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → 2 ≤ d → Even d → ∀ D : ZMod d → ℝ, (∀ a, 0 ≤ D a) →
    (∀ a a', D a' ≤ l * D a) → Fnum l d D = rho l * ∑ a, D a

end Formalism.L2.FormalSeriesBounds
end
end
