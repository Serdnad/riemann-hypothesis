module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.CharP.Subring
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.Pigeonhole

@[expose] public section

section

open Polynomial

namespace GlobalTheory.SumScalarVanishing

section
variable {F C E : Type} [Field F] [Ring C] [Algebra F C] [Field E] [Algebra F E]

theorem eq_zero_of_sum_smul [Algebra.IsCentral F C] [IsSimpleRing C] {n : ℕ} (hn : 0 < n)
    (ρ : C →+* Matrix (Fin n) (Fin n) E)
    (hρ : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (algebraMap F E a))
    {ι : Type} (e : ι → E) (he : LinearIndependent F e) (s : Finset ι) :
    ∀ c : ι → C, ∑ i ∈ s, e i • ρ (c i) = 0 → ∀ i ∈ s, c i = 0 := by
  classical
  have hmain : ∀ (k : ℕ) (c : ι → C), (s.filter (fun i => c i ≠ 0)).card = k →
      ∑ i ∈ s, e i • ρ (c i) = 0 → ∀ i ∈ s, c i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro c hk hsum i0 hi0
    by_contra hci0

    let I : TwoSidedIdeal C := TwoSidedIdeal.mk'
      {a | ∃ d : ι → C, d i0 = a ∧ (∀ i ∈ s, c i = 0 → d i = 0) ∧ ∑ i ∈ s, e i • ρ (d i) = 0}
      ⟨0, rfl, fun _ _ _ => rfl, by simp⟩
      (by
        rintro x y ⟨d, rfl, hd, hds⟩ ⟨d', rfl, hd', hds'⟩
        refine ⟨d + d', rfl, fun i hi hc => by simp [hd i hi hc, hd' i hi hc], ?_⟩
        simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib, hds, hds', add_zero])
      (by
        rintro x ⟨d, rfl, hd, hds⟩
        refine ⟨-d, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [Pi.neg_apply, map_neg, smul_neg, Finset.sum_neg_distrib, hds, neg_zero])
      (by
        rintro x y ⟨d, rfl, hd, hds⟩
        refine ⟨fun i => x * d i, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [map_mul, ← Matrix.mul_smul, ← Finset.mul_sum, hds, mul_zero])
      (by
        rintro x y ⟨d, rfl, hd, hds⟩
        refine ⟨fun i => d i * y, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [map_mul, ← Matrix.smul_mul, ← Finset.sum_mul, hds, zero_mul])
    have hmem : ∀ a, a ∈ I ↔
        ∃ d : ι → C, d i0 = a ∧ (∀ i ∈ s, c i = 0 → d i = 0) ∧ ∑ i ∈ s, e i • ρ (d i) = 0 :=
      fun a => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a
    have hI : I = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top I with h | h
      · exfalso
        have h' : c i0 ∈ I := (hmem _).2 ⟨c, rfl, fun i _ hc => hc, hsum⟩
        rw [h, TwoSidedIdeal.mem_bot] at h'
        exact hci0 h'
      · exact h
    have h1 : (1 : C) ∈ I := by rw [hI]; trivial
    obtain ⟨d, hd0, hdc, hds⟩ := (hmem 1).1 h1

    have hcen : ∀ i ∈ s, ∀ y : C, y * d i = d i * y := by
      intro i hi y
      let d' : ι → C := fun j => y * d j - d j * y
      have hs' : ∑ j ∈ s, e j • ρ (d' j) = 0 := by
        have hsplit : ∑ j ∈ s, e j • ρ (d' j) =
            ρ y * (∑ j ∈ s, e j • ρ (d j)) - (∑ j ∈ s, e j • ρ (d j)) * ρ y := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [d', map_sub, map_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
        rw [hsplit, hds, mul_zero, zero_mul, sub_zero]
      have hsub : s.filter (fun j => d' j ≠ 0) ⊂ s.filter (fun j => c j ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i0, Finset.mem_filter.2 ⟨hi0, hci0⟩, fun h => ?_⟩
          exact (Finset.mem_filter.1 h).2 (by simp [d', hd0])
        · intro j hj
          rw [Finset.mem_filter] at hj ⊢
          refine ⟨hj.1, fun hc => hj.2 ?_⟩
          simp [d', hdc j hj.1 hc]
      have hlt := Finset.card_lt_card hsub
      rw [hk] at hlt
      have := ih _ hlt d' rfl hs' i hi
      exact sub_eq_zero.1 this
    have hex : ∀ i, ∃ a : F, i ∈ s → algebraMap F C a = d i := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨a, ha⟩ := Algebra.mem_bot.1
          (Algebra.IsCentral.out ((Subalgebra.mem_center_iff (R := F)).2 (hcen i hi)))
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose f hf using hex
    have hsum2 : ∑ i ∈ s, f i • e i = 0 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) E => M ⟨0, hn⟩ ⟨0, hn⟩) hds
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← hf i hi, hρ]
      simp [Algebra.smul_def, mul_comm]
    have hf0 := linearIndependent_iff'.1 he s f hsum2 i0 hi0
    have := hf i0 hi0
    rw [hf0, map_zero, hd0] at this
    exact zero_ne_one this
  exact fun c hc => hmain _ c rfl hc

theorem exists_expansion {ι : Type} (b : Module.Basis ι F E) (p : E[X]) :
    ∃ q : ι →₀ F[X], p = q.sum (fun k r => b k • r.map (algebraMap F E)) := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨u, rfl⟩ := hp
    obtain ⟨v, rfl⟩ := hq
    refine ⟨u + v, ?_⟩
    rw [Finsupp.sum_add_index']
    · intro k
      simp
    · intro k r r'
      rw [Polynomial.map_add (f := _), smul_add]
  | monomial j a =>
    refine ⟨(b.repr a).mapRange (fun c => Polynomial.monomial j c) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (by simp)]
    simp only [Polynomial.map_monomial, Polynomial.smul_monomial]
    rw [← map_finsuppSum (Polynomial.monomial j)]
    congr 1
    conv_lhs => rw [← b.linearCombination_repr a]
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [smul_eq_mul, Algebra.smul_def, mul_comm]

end

theorem isRoot_charpoly_of_isRoot_minpoly {F C E : Type} [Field F] [Ring C] [Algebra F C]
    [FiniteDimensional F C] [Algebra.IsCentral F C] [IsSimpleRing C] [Field E] (τ : F →+* E)
    {n : ℕ} (hn : 0 < n) (ρ : C →+* Matrix (Fin n) (Fin n) E)
    (hρ : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (τ a)) (x : C) (μ : E)
    (hμ : ((minpoly F x).map τ).IsRoot μ) : (ρ x).charpoly.IsRoot μ := by
  classical
  let _ : Algebra F E := τ.toAlgebra
  have hρ' : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (algebraMap F E a) := hρ
  let b := Module.Basis.ofVectorSpace F E
  obtain ⟨q, hq⟩ := exists_expansion b (ρ x).charpoly

  have heval : ∀ r : F[X],
      Polynomial.aeval (ρ x) (r.map (algebraMap F E)) = ρ (Polynomial.aeval x r) := by
    intro r
    induction r using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), hp, hq]
    | monomial j a =>
      simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, map_mul, map_pow, hρ']
      congr 1

  have h0 : ∑ k ∈ q.support, b k • ρ (Polynomial.aeval x (q k)) = 0 := by
    have h := Matrix.aeval_self_charpoly (ρ x)

    rw [hq, Finsupp.sum, map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, heval]
  have hz := eq_zero_of_sum_smul hn ρ hρ' b b.linearIndependent q.support
    (fun k => Polynomial.aeval x (q k)) h0
  have hdvd : (minpoly F x).map (algebraMap F E) ∣ (ρ x).charpoly := by
    rw [hq, Finsupp.sum]
    refine Finset.dvd_sum fun k hk => ?_
    rw [Polynomial.smul_eq_C_mul]
    exact Dvd.dvd.mul_left (Polynomial.map_dvd _ (minpoly.dvd F x (hz k hk))) _
  exact Polynomial.IsRoot.dvd hμ hdvd

end GlobalTheory.SumScalarVanishing
end

section

open Finset

namespace GlobalTheory

theorem ringHom_sep_charZero (k : Type) [Field k] [CharZero k] (C : Type) [CommRing C]
    (S : Finset (C →+* k)) (χ₀ : C →+* k) : ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert χ' S hχ' ih =>
    obtain ⟨c, hc⟩ := ih
    by_cases h0 : χ' = χ₀
    · refine ⟨c, fun χ hχ hne => ?_⟩
      rcases Finset.mem_insert.1 hχ with rfl | h
      · exact absurd h0 hne
      · exact hc χ h hne
    obtain ⟨d, hd⟩ := DFunLike.ne_iff.1 h0
    have key : ∀ χ ∈ insert χ' S, χ ≠ χ₀ →
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ).Subsingleton := by
      intro χ hχ hne n hn m hm
      simp only [Set.mem_setOf_eq, map_add (f := _), map_mul, map_natCast] at hn hm
      have hsub : ((n : k) - m) * (χ d - χ₀ d) = 0 := by linear_combination hn - hm
      rcases mul_eq_zero.1 hsub with h | h
      · exact_mod_cast sub_eq_zero.1 h
      · have hb : χ d = χ₀ d := sub_eq_zero.1 h
        rcases Finset.mem_insert.1 hχ with rfl | h'
        · exact absurd hb hd
        · exact absurd (by rw [hb] at hn; linear_combination hn) (hc χ h' hne)
    have hfin : (⋃ χ ∈ (insert χ' S).filter (· ≠ χ₀),
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ)).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun χ hχ => ?_
      rw [Finset.mem_coe, Finset.mem_filter] at hχ
      exact (key χ hχ.1 hχ.2).finite
    obtain ⟨n, hn⟩ := hfin.exists_notMem
    refine ⟨c + n * d, fun χ hχ hne heq => hn ?_⟩
    simp only [Set.mem_iUnion]
    exact ⟨χ, Finset.mem_filter.2 ⟨hχ, hne⟩, heq⟩

theorem ringHom_pow_eq_one_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (ψ : C →+* k) [Finite ψ.range] (a : C) (ha : ψ a ≠ 0) (m : ℕ)
    (hm : (Nat.card ψ.range).factorial ∣ m) : ψ a ^ m = 1 := by
  classical
  haveI := Fintype.ofFinite ψ.range
  let f : Fin (Nat.card ψ.range + 1) → ψ.range := fun i => ⟨ψ a ^ (i : ℕ), ⟨a ^ (i : ℕ), by simp⟩⟩
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hf' : ψ a ^ (i : ℕ) = ψ a ^ (j : ℕ) := congrArg Subtype.val hf
  have hpos : ∀ (u v : ℕ), u < v → v ≤ Nat.card ψ.range → ψ a ^ u = ψ a ^ v → ψ a ^ m = 1 := by
    intro u v huv hv he
    have h1 : ψ a ^ (v - u) = 1 := by
      have : ψ a ^ u * (ψ a ^ (v - u) - 1) = 0 := by
        rw [mul_sub, ← pow_add, Nat.add_sub_cancel' huv.le, mul_one, he, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff'.1 h).1 ha
      · exact sub_eq_zero.1 h
    have hd : v - u ∣ m := (Nat.dvd_factorial (by omega) (by omega)).trans hm
    obtain ⟨t, rfl⟩ := hd
    rw [pow_mul, h1, one_pow]
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact hpos i j h (by omega) hf'
  · exact hpos j i h (by omega) hf'.symm

theorem ringHom_exists_generator_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (χ₀ : C →+* k) [Finite χ₀.range] :
    ∃ g : C, χ₀ g ≠ 0 ∧ ∀ b, χ₀ b ≠ 0 → ∃ n : ℕ, χ₀ b = χ₀ g ^ n := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (χ₀.range)ˣ)
  obtain ⟨g, hg⟩ := ((u : χ₀.range)).2
  refine ⟨g, ?_, fun b hb => ?_⟩
  · rw [hg]
    exact fun h => u.ne_zero (Subtype.ext h)
  · set y : χ₀.range := ⟨χ₀ b, ⟨b, rfl⟩⟩
    have hy0 : y ≠ 0 := fun h => hb (congrArg Subtype.val h)
    have hyu : IsUnit y := by
      have hpow := ringHom_pow_eq_one_of_finite_range χ₀ b hb _ dvd_rfl
      exact ⟨Units.ofPowEqOne y (Nat.card χ₀.range).factorial
        (Subtype.ext (by simpa [y] using hpow)) (Nat.factorial_ne_zero _), rfl⟩
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.2 (hu hyu.unit) : hyu.unit ∈ Submonoid.powers u)
    refine ⟨n, ?_⟩
    have h1 : ((u ^ n : (χ₀.range)ˣ) : χ₀.range) = y := by
      rw [show u ^ n = hyu.unit from hn]; rfl
    have h2 : ((u : χ₀.range) : k) ^ n = χ₀ b := by
      have := congrArg Subtype.val h1
      simpa [y] using this
    rw [hg]
    exact h2.symm

end GlobalTheory

namespace GlobalTheory

theorem ringHom_sep_of_finite_range (k : Type) [Field k] (C : Type) [CommRing C]
    (hfin : ∀ ψ : C →+* k, Finite ψ.range) (S : Finset (C →+* k)) (χ₀ : C →+* k) :
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  let M : ℕ := ∏ ψ ∈ insert χ₀ S, (Nat.card ψ.range).factorial
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hpow : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ a ≠ 0 → ψ a ^ M = 1 := fun ψ hψ a ha => by
    haveI := hfin ψ
    exact ringHom_pow_eq_one_of_finite_range ψ a ha M (Finset.dvd_prod_of_mem _ hψ)
  have hpow' : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ (a ^ M) = if ψ a = 0 then 0 else 1 := by
    intro ψ hψ a
    rw [map_pow]
    split_ifs with h
    · rw [h, zero_pow hM0]
    · exact hpow ψ hψ a h
  haveI := hfin χ₀
  obtain ⟨g, hg0, hgen⟩ := ringHom_exists_generator_of_finite_range χ₀
  have hsep : ∀ χ ∈ S, χ ≠ χ₀ → χ g = χ₀ g → ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := by
    intro χ hχ hne hgeq
    by_contra hcon
    push_neg at hcon
    have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
    have hk : ∀ b, χ₀ b = 0 → χ b = 0 := by
      intro b hb
      by_contra hb'
      have h1 := hcon (1 - b ^ M) (by rw [map_sub, map_one, map_pow, hpow χ hχ' b hb', sub_self])
      rw [map_sub, map_one, map_pow, hb, zero_pow hM0, sub_zero] at h1
      exact one_ne_zero h1
    apply hne
    ext b
    by_cases hb : χ₀ b = 0
    · rw [hb, hk b hb]
    · obtain ⟨n, hn⟩ := hgen b hb
      have h3 : χ (b - g ^ n) = 0 := hk _ (by rw [map_sub, map_pow, hn, sub_self])
      rw [map_sub, map_pow, sub_eq_zero, hgeq, ← hn] at h3
      exact h3
  let V := S.filter (fun χ => χ ≠ χ₀ ∧ χ g = χ₀ g)
  have hV : ∀ χ ∈ V, ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := fun χ hχ => by
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hχ)
    exact hsep χ h1 h2 h3
  choose! a ha using hV
  let A : C := ∏ χ ∈ V, a χ
  have hA0 : χ₀ A ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun χ hχ => (ha χ hχ).2
  have hAV : ∀ χ ∈ V, χ A = 0 := fun χ hχ => by
    rw [map_prod]
    exact Finset.prod_eq_zero hχ (ha χ hχ).1
  refine ⟨g * A ^ M, fun χ hχ hne => ?_⟩
  have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
  rw [map_mul, map_mul, hpow' χ₀ (Finset.mem_insert_self _ _), if_neg hA0, mul_one,
    hpow' χ hχ']
  by_cases hgeq : χ g = χ₀ g
  · rw [if_pos (hAV χ (Finset.mem_filter.2 ⟨hχ, hne, hgeq⟩)), mul_zero]
    exact fun h => hg0 h.symm
  · split_ifs
    · rw [mul_zero]; exact fun h => hg0 h.symm
    · rwa [mul_one]

theorem ringHom_finite_range_of_charP {k : Type} [Field k] {C : Type} [CommRing C]
    [Module.Finite ℤ C] (p : ℕ) [hp : CharP k p] (hp0 : p ≠ 0) (ψ : C →+* k) :
    Finite ψ.range := by
  haveI : Module.Finite ℤ ψ.range :=
    Module.Finite.of_surjective (ψ.rangeRestrict.toAddMonoidHom.toIntLinearMap)
      ψ.rangeRestrict_surjective
  haveI : AddGroup.FG ψ.range := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨p, Nat.pos_of_ne_zero hp0, ?_⟩
  apply Subtype.ext
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

theorem ringHom_exists_sep_of_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C]
    [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k),
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  intro k _ C _ _ S χ₀
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · exact ringHom_sep_of_finite_range k C
      (fun ψ => ringHom_finite_range_of_charP p hpp.ne_zero ψ) S χ₀
  · haveI := CharP.charP_to_charZero k
    exact ringHom_sep_charZero k C S χ₀

end GlobalTheory
end

section

open IsLocalRing

noncomputable section

namespace GlobalTheory.Henselisation

variable (R : Type) [CommRing R] [IsLocalRing R]

structure EtNbhd where

  n : ℕ

  I : Ideal (MvPolynomial (Fin n) R)

  etale : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ I)

  pt : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] ResidueField R

namespace EtNbhd

variable {R}

abbrev A (i : EtNbhd R) : Type := MvPolynomial (Fin i.n) R ⧸ i.I

instance (i : EtNbhd R) : Algebra.Etale R i.A := i.etale

def q (i : EtNbhd R) : Ideal i.A := RingHom.ker i.pt

instance (i : EtNbhd R) : i.q.IsPrime := RingHom.ker_isPrime _

abbrev B (i : EtNbhd R) : Type := Localization.AtPrime i.q

instance : Preorder (EtNbhd R) where
  le i j := ∃ f : i.A →ₐ[R] j.A, j.pt.comp f = i.pt
  le_refl i := ⟨AlgHom.id R i.A, AlgHom.comp_id _⟩
  le_trans i j k := fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨g.comp f, by rw [← AlgHom.comp_assoc, hg, hf]⟩

theorem q_eq_comap {i j : EtNbhd R} (f : i.A →ₐ[R] j.A) (hf : j.pt.comp f = i.pt) :
    i.q = j.q.comap (f : i.A →+* j.A) := by
  ext a
  simp only [q, RingHom.mem_ker, Ideal.mem_comap]
  rw [← hf]
  rfl

noncomputable def trans {i j : EtNbhd R} (h : i ≤ j) : i.B →+* j.B :=
  Localization.localRingHom i.q j.q (h.choose : i.A →+* j.A) (q_eq_comap _ h.choose_spec)

noncomputable def base : EtNbhd R where
  n := 0
  I := RingHom.ker (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom
  etale := Algebra.Etale.of_equiv (Ideal.quotientKerAlgEquivOfSurjective
    (f := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom)
    (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).surjective).symm
  pt := (IsScalarTower.toAlgHom R R (ResidueField R)).comp
    (Ideal.quotientKerAlgEquivOfSurjective (f := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom)
      (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).surjective).toAlgHom

instance : Nonempty (EtNbhd R) := ⟨base⟩

end EtNbhd

def Hens : Type :=
  Ring.DirectLimit (fun i : EtNbhd R => i.B) (fun _ _ h => ⇑(EtNbhd.trans h))

noncomputable instance : CommRing (Hens R) :=
  inferInstanceAs (CommRing (Ring.DirectLimit (fun i : EtNbhd R => i.B) (fun _ _ h => ⇑(EtNbhd.trans h))))

variable {R}

noncomputable def Hens.of (i : EtNbhd R) : i.B →+* Hens R :=
  Ring.DirectLimit.of (fun i : EtNbhd R => i.B) (fun _ _ h => ⇑(EtNbhd.trans h)) i


variable (R) in
noncomputable instance : Algebra R (Hens R) :=
  ((Hens.of (EtNbhd.base (R := R))).comp (algebraMap R (EtNbhd.base (R := R)).B)).toAlgebra

end GlobalTheory.Henselisation

end
end
