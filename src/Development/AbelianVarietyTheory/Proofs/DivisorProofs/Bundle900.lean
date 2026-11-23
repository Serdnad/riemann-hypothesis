module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitDegreeOverPrimeFieldFbar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
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

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel.Congr

theorem part_pow {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, ?_⟩
  rw [hz, ← pow_mul, mul_comm, pow_mul]
  have := pow_eq_pow_of_modEq hmod hone
  rwa [pow_one] at this

theorem part_pow_compl {G : Type} [Monoid G] (l : ℕ) (x : G) :
    Formalism.CyclotomicNorms.primeToPart l x ^ (orderOf x / l ^ (orderOf x).factorization l) = 1 := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [← pow_mul, mul_right_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_mul, pow_orderOf_eq_one, one_pow]

theorem eq_of_pow_eq {G : Type} [Monoid G] {M k : ℕ} (hM : M ≠ 0) (hk : k.Coprime M) {y z : G}
    (hy : y ^ M = 1) (hz : z ^ M = 1) (h : y ^ k = z ^ k) : y = z := by
  haveI : NeZero M := ⟨hM⟩
  set u := ((k : ZMod M)⁻¹).val with hu
  have hmod : k * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hk
  have h1 := pow_eq_pow_of_modEq hmod hy
  have h2 := pow_eq_pow_of_modEq hmod hz
  rw [pow_one, pow_mul] at h1 h2
  rw [← h1, h, h2]

theorem part_eq_iff {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x y : G} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) :
    (∃ n : ℕ, x ^ (l ^ n) = y ^ (l ^ n)) ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y := by
  obtain ⟨a, ha⟩ := part_pow hl hx
  obtain ⟨b, hb⟩ := part_pow hl hy
  have h1 : ∀ n, x ^ (l ^ (a + b + n)) = Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ (a + b + n)) := fun n => by
    rw [add_assoc, pow_add, pow_mul, pow_mul, ha]
  have h2 : ∀ n, y ^ (l ^ (a + b + n)) = Formalism.CyclotomicNorms.primeToPart l y ^ (l ^ (a + b + n)) := fun n => by
    rw [add_comm a b, add_assoc, pow_add, pow_mul, pow_mul, hb]
  constructor
  · rintro ⟨n, hn⟩
    have hx0 : orderOf x ≠ 0 := hx.orderOf_pos.ne'
    have hy0 : orderOf y ≠ 0 := hy.orderOf_pos.ne'
    refine eq_of_pow_eq (M := (orderOf x / l ^ (orderOf x).factorization l) *
      (orderOf y / l ^ (orderOf y).factorization l)) (k := l ^ (a + b + n))
      (mul_ne_zero (Nat.ordCompl_pos l hx0).ne' (Nat.ordCompl_pos l hy0).ne')
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (Nat.coprime_ordCompl hl hx0)
        (Nat.coprime_ordCompl hl hy0))) ?_ ?_ ?_
    · rw [pow_mul, part_pow_compl, one_pow]
    · rw [mul_comm, pow_mul, part_pow_compl, one_pow]
    · rw [← h1, ← h2, add_comm, pow_add, pow_mul, pow_mul, hn]
  · intro h
    exact ⟨a + b + 0, by rw [h1, h2, h]⟩

variable {p : ℕ} [Fact p.Prime]

theorem thetaOf_gen (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  have hfin : IsOfFinOrder (L.gen d) := by
    rw [← orderOf_pos_iff, L.gen_order d hd]; exact hp
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left h]
  have h1 := hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  rw [L.gen_order d hd] at h1
  exact (pow_eq_pow_of_modEq h1 (by rw [← map_pow, hx, map_one])).symm

theorem pow_eq_iff (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {θ θ' : Tor p d →* ℂˣ} {x x' : Fbar p}
    (h : LabelsChar L θ x) (h' : LabelsChar L θ' x') (m : ℕ) : θ ^ m = θ' ^ m ↔ x ^ m = x' ^ m := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hx0 : x ≠ 0 := fun e => by
    have := h.1; rw [e, zero_pow hp.ne'] at this; exact zero_ne_one this
  have hx0' : x' ≠ 0 := fun e => by
    have := h'.1; rw [e, zero_pow hp.ne'] at this; exact zero_ne_one this
  constructor
  · intro e
    let u : Tor p d := rootsOfUnity.mkOfPowEq (L.gen d) hprim.pow_eq_one
    have hu : ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ 1 := by rw [pow_one]; rfl
    have e1 := h.2 u
    have e2 := h'.2 u
    rw [hu, thetaOf_gen L hd h.1, pow_one] at e1
    rw [hu, thetaOf_gen L hd h'.1, pow_one] at e2
    have e3 : ((θ u : ℂˣ) : ℂ) ^ m = ((θ' u : ℂˣ) : ℂ) ^ m := by
      have := congrArg (fun f : Tor p d →* ℂˣ => ((f u : ℂˣ) : ℂ)) e
      simpa using this
    refine L.teich_inj _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0') ?_
    rw [map_pow, map_pow, ← e1, ← e2, e3]
  · intro e
    refine MonoidHom.ext fun u => Units.ext ?_
    have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
    have e1 := h.2 u
    have e2 := h'.2 u
    rw [← hn, thetaOf_gen L hd h.1] at e1
    rw [← hn, thetaOf_gen L hd h'.1] at e2
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e1, e2,
      ← pow_mul, ← pow_mul, mul_comm n m, pow_mul, pow_mul, ← map_pow L.teich x m, ← map_pow L.teich x' m, e]

theorem eq_and_congr : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (d : ℕ), 0 < d → ∀ (θ θ' : Tor p d →* ℂˣ) (x x' : Fbar p), LabelsChar L θ x → LabelsChar L θ' x' → (θ = θ' ↔ x = x') ∧ ∀ l : ℕ, l.Prime → (CongrMod l θ θ' ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l x') := by
  intro p _ L d hd θ θ' x x' h h'
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  refine ⟨by simpa using pow_eq_iff L hd h h' 1, fun l hl => ?_⟩
  rw [← part_eq_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hp, h.1⟩) (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hp, h'.1⟩)]
  refine exists_congr fun n => ?_
  rw [div_pow, div_eq_one]
  exact pow_eq_iff L hd h h' _

end GlobalTheory.ParamLabel.Congr
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel.RootPolyFactor

open GlobalTheory.GoodCharsCompare

theorem card_sigma_cyc {r : ℕ} (b : Fin r → Fin r) :
    Fintype.card (Σ c : Cyc b, Fin (cycLen b c)) = r := by
  have e : (Σ c : Cyc b, {i : Fin r // b i = c.1}) ≃ Fin r :=
    { toFun := fun y => y.2.1
      invFun := fun i => ⟨⟨b i, i, rfl⟩, i, rfl⟩
      left_inv := by
        rintro ⟨⟨c, hc⟩, i, hi⟩
        cases hi
        rfl
      right_inv := fun i => rfl }
  have := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at this
  rw [Fintype.card_sigma]
  simpa using this

theorem rootsBar_prod {p : ℕ} [Fact p.Prime] {ι : Type} (s : Finset ι) (φ : ι → (ZMod p)[X])
    (h : ∀ c, (φ c).Monic) {z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (∏ c ∈ s, φ c) ↔ ∃ c ∈ s, z ∈ Formalism.CyclotomicNorms.rootsBar (φ c) := by
  rw [mem_rootsBar (monic_prod_of_monic _ _ fun c _ => h c).ne_zero, map_prod, Finset.prod_eq_zero_iff]
  simp only [mem_rootsBar (h _).ne_zero]

theorem dg_eq {p : ℕ} [Fact p.Prime] {r : ℕ} {b : Fin r → Fin r} {x : Cyc b → Fbar p}
    (hx : ∀ c, x c ^ (p ^ cycLen b c - 1) = 1) (hinj : Function.Injective (rootElt x)) (c : Cyc b) :
    dg (x c) = cycLen b c := by
  obtain ⟨k, hk⟩ := exists_dg_mul (cycLen_pos b c) (hx c)
  have h0 := cycLen_pos b c
  have hle : dg (x c) ≤ cycLen b c := Nat.le_of_dvd h0 ⟨k, hk⟩
  by_contra hne
  have hlt : dg (x c) < cycLen b c := lt_of_le_of_ne hle hne
  have := @hinj ⟨c, ⟨dg (x c), hlt⟩⟩ ⟨c, ⟨0, h0⟩⟩ (by
    show x c ^ p ^ dg (x c) = x c ^ p ^ 0
    rw [(frobenius_orbit_degreeOverPrimeFieldFbar (x c)).1, pow_zero, pow_one])
  have h2 := congrArg (fun y : (Σ c : Cyc b, Fin (cycLen b c)) => (y.2 : ℕ)) this
  exact (dg_pos (x c)).ne' h2

theorem mem_roots_lt {p : ℕ} [Fact p.Prime] {y z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y) ↔ ∃ i < dg y, y ^ p ^ i = z := by
  classical
  rw [← Multiset.mem_toFinset, roots_minpoly]
  simp

theorem rootPoly_factor : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → Fin r) (x : Cyc b → Fbar p) (f : (ZMod p)[X]), IsRootPoly x f → f.natDegree = r ∧ f.coeff 0 ≠ 0 ∧ (Squarefree f ↔ Function.Injective (rootElt x)) ∧ (Squarefree f → (∀ c, (minpoly (ZMod p) (x c)).natDegree = cycLen b c) ∧ Function.Injective (fun c => minpoly (ZMod p) (x c)) ∧ f = ∏ c, minpoly (ZMod p) (x c)) := by
  intro p _ r b x f ⟨hx, hm, hr⟩
  have hdeg : f.natDegree = r := by
    rw [← card_rootsBar, hr, Multiset.card_map, ← Finset.card_def, Finset.card_univ, card_sigma_cyc]
  have hsq : Squarefree f ↔ Function.Injective (rootElt x) := by
    rw [squarefree_iff hm.ne_zero, hr, Multiset.nodup_map_iff_inj_on Finset.univ.nodup]
    simp [Function.Injective]
  refine ⟨hdeg, ?_, hsq, fun hs => ?_⟩
  · rw [coeff_zero_iff hm.ne_zero, hr, Multiset.mem_map]
    rintro ⟨⟨c, i⟩, -, h⟩
    have h1 : x c = 0 := eq_zero_of_pow_eq_zero h
    have := hx c
    rw [h1, zero_pow (g_pow_sub_pos (cycLen_pos b c)).ne'] at this
    exact zero_ne_one this
  · have hinj := hsq.1 hs
    have hd := dg_eq hx hinj
    refine ⟨hd, fun c c' h => ?_, ?_⟩
    · have h1 : x c' ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) (x c)) := by
        rw [show minpoly (ZMod p) (x c) = minpoly (ZMod p) (x c') from h]
        exact mem_roots_minpoly.2 ⟨0, by simp⟩
      obtain ⟨i, hi, e⟩ := mem_roots_lt.1 h1
      have := @hinj ⟨c, ⟨i, hd c ▸ hi⟩⟩ ⟨c', ⟨0, cycLen_pos b c'⟩⟩ (by
        show x c ^ p ^ i = x c' ^ p ^ 0
        rw [e, pow_zero, pow_one])
      exact congrArg Sigma.fst this
    · have hmon : ∀ c, (minpoly (ZMod p) (x c)).Monic := fun c => minpoly.monic (isInt _)
      have hP := monic_prod_of_monic Finset.univ _ fun c _ => hmon c
      apply eq_of_rootsBar hm hP
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset ((squarefree_iff hm.ne_zero).1 hs)]
        intro z hz
        rw [hr, Multiset.mem_map] at hz
        obtain ⟨⟨c, i⟩, -, rfl⟩ := hz
        exact (rootsBar_prod _ _ hmon).2 ⟨c, Finset.mem_univ _, mem_roots_minpoly.2 ⟨i, rfl⟩⟩
      · rw [card_rootsBar, card_rootsBar, hdeg, natDegree_prod_of_monic _ _ fun c _ => hmon c]
        have := card_sigma_cyc b
        rw [Fintype.card_sigma] at this
        simp only [Fintype.card_fin] at this
        exact ((Finset.sum_congr rfl fun c _ => hd c).trans this).le

end GlobalTheory.ParamLabel.RootPolyFactor
end

section

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamExists

open GlobalTheory.GoodCharsCompare

variable {p : ℕ} [Fact p.Prime]

theorem thetaOf_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have hp : 0 < p ^ d - 1 := g_pow_sub_pos hd
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left h]
  have hfin : IsOfFinOrder (L.gen d) := by
    rw [← orderOf_pos_iff, L.gen_order d hd]; exact hp
  have h1 := hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  rw [L.gen_order d hd] at h1
  have h2 : L.teich x ^ (p ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2]
  exact congrArg _ h1.symm

theorem exists_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (u : Tor p d) :
    ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := by
  haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  exact ⟨n, hn.symm⟩

theorem exists_char (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    ∃ θ : Tor p d →* ℂˣ, LabelsChar L θ x := by
  let φ : Tor p d →* ℂ :=
    { toFun := fun u => GlobalTheory.GLq.thetaOf L d x ((u : (Fbar p)ˣ) : Fbar p)
      map_one' := by
        have := thetaOf_gen_pow L hd hx 0
        simpa using this
      map_mul' := by
        intro u v
        obtain ⟨n, hn⟩ := exists_gen_pow L hd u
        obtain ⟨m, hm⟩ := exists_gen_pow L hd v
        rw [Subgroup.coe_mul, Units.val_mul, hn, hm, ← pow_add, thetaOf_gen_pow L hd hx,
          thetaOf_gen_pow L hd hx, thetaOf_gen_pow L hd hx, pow_add] }
  exact ⟨φ.toHomUnits, hx, fun u => rfl⟩

theorem minpoly_eq_of_mem {y z : Fbar p} (h : z ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y)) :
    minpoly (ZMod p) z = minpoly (ZMod p) y :=
  (eq_minpoly (minpoly.monic (isInt y)) (minpoly.irreducible (isInt y)) h).symm

theorem self_mem (y : Fbar p) : y ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y) :=
  mem_roots_minpoly.2 ⟨0, by simp⟩

theorem exists_rootPoly (r : ℕ) (f : (ZMod p)[X]) (hm : f.Monic) (hr : f.natDegree = r) (h0 : f.coeff 0 ≠ 0)
    (hs : Squarefree f) : ∃ (b : Fin r → Fin r) (x : Cyc b → Fbar p), IsRootPoly x f := by
  classical
  have hf := hm.ne_zero
  have hnd := (squarefree_iff hf).1 hs
  have hz0 := (coeff_zero_iff hf).1 h0
  let S := (Formalism.CyclotomicNorms.rootsBar f).toFinset
  have hS : S.card = r := by rw [Multiset.toFinset_card_of_nodup hnd, card_rootsBar, hr]
  let e : Fin r ≃ S := (Finset.equivFinOfCardEq hS).symm
  let z : Fin r → Fbar p := fun i => (e i : Fbar p)
  have zinj : Function.Injective z := Subtype.val_injective.comp e.injective
  have zmem : ∀ i, z i ∈ Formalism.CyclotomicNorms.rootsBar f := fun i => Multiset.mem_toFinset.1 (e i).2
  have zsurj : ∀ w ∈ Formalism.CyclotomicNorms.rootsBar f, ∃ i, z i = w := fun w hw =>
    ⟨e.symm ⟨w, Multiset.mem_toFinset.2 hw⟩, by simp [z]⟩
  let m : Fin r → (ZMod p)[X] := fun i => minpoly (ZMod p) (z i)
  have hsub : ∀ i w, w ∈ Formalism.CyclotomicNorms.rootsBar (m i) → w ∈ Formalism.CyclotomicNorms.rootsBar f := by
    intro i w hw
    obtain ⟨k, rfl⟩ := mem_roots_minpoly.1 hw
    rw [mem_rootsBar hf]
    exact aeval_pow_g _ _ _ ((mem_rootsBar hf).1 (zmem i))
  have hb : ∃ b : Fin r → Fin r, (∀ i, m (b i) = m i) ∧ ∀ i j, m i = m j → b i = b j := by
    refine ⟨fun i => @Function.invFun _ _ ⟨i⟩ m (m i), fun i => @Function.invFun_eq _ _ ⟨i⟩ m _ ⟨i, rfl⟩, ?_⟩
    intro i j h
    simp only [h]
  obtain ⟨b, hb1, hb2⟩ := hb
  have hbc : ∀ c : Cyc b, ∀ i, b i = c.1 ↔ m i = m c.1 := by
    rintro ⟨c, j, rfl⟩ i
    exact ⟨fun h => by rw [← hb1 i]; exact congrArg m h, fun h => hb2 _ _ (h.trans (hb1 j))⟩
  have hlen : ∀ c : Cyc b, cycLen b c = dg (z c.1) := by
    intro c
    rw [dg, ← card_rootsBar, ← Multiset.toFinset_card_of_nodup (nodup_minpoly _), cycLen, Fintype.card_subtype]
    refine Finset.card_bij (fun i _ => z i) ?_ ?_ ?_
    · intro i hi
      have h1 : m i = m c.1 := (hbc c i).1 (Finset.mem_filter.1 hi).2
      rw [Multiset.mem_toFinset]
      exact (show minpoly (ZMod p) (z i) = minpoly (ZMod p) (z c.1) from h1) ▸ self_mem (z i)
    · intro i _ j _ h
      exact zinj h
    · intro w hw
      rw [Multiset.mem_toFinset] at hw
      obtain ⟨i, rfl⟩ := zsurj w (hsub _ w hw)
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hbc c i).2 (minpoly_eq_of_mem hw)⟩, rfl⟩
  refine ⟨b, fun c => z c.1, fun c => ?_, hm, ?_⟩
  · rw [hlen]
    exact pow_dg (fun h => hz0 (h ▸ zmem _))
  · rw [Multiset.Nodup.ext hnd (Finset.univ.nodup.map ?_)]
    · intro w
      rw [Multiset.mem_map]
      constructor
      · intro hw
        obtain ⟨i, rfl⟩ := zsurj w hw
        let c : Cyc b := ⟨b i, i, rfl⟩
        have h1 : z i ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) (z c.1)) :=
          (show minpoly (ZMod p) (z i) = minpoly (ZMod p) (z c.1) from (hb1 i).symm) ▸ self_mem (z i)
        rw [← Multiset.mem_toFinset, roots_minpoly] at h1
        obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h1
        exact ⟨⟨c, ⟨k, by rw [hlen]; exact Finset.mem_range.1 hk⟩⟩, Finset.mem_univ_val _, hk'⟩
      · rintro ⟨y, -, rfl⟩
        exact hsub y.1.1 _ (mem_roots_minpoly.2 ⟨_, rfl⟩)
    · rintro ⟨c, i⟩ ⟨c', j⟩ h
      have h' : z c.1 ^ p ^ (i : ℕ) = z c'.1 ^ p ^ (j : ℕ) := h
      have e1 := minpoly_eq_of_mem (y := z c.1) (mem_roots_minpoly.2 ⟨i, rfl⟩)
      have e2 := minpoly_eq_of_mem (y := z c'.1) (mem_roots_minpoly.2 ⟨j, rfl⟩)
      have e3 : m c.1 = m c'.1 := e1.symm.trans (h' ▸ e2)
      have e4 : c = c' := Subtype.ext (((hbc c c.1).2 rfl).symm.trans ((hbc c' c.1).2 e3))
      subst e4
      have := (frobenius_orbit_degreeOverPrimeFieldFbar (z c.1)).2 i (hlen c ▸ i.2) j (hlen c ▸ j.2) h'
      rw [Fin.ext this]

theorem param_exists : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (f : (ZMod p)[X]),
    f.Monic → f.natDegree = r → f.coeff 0 ≠ 0 → Squarefree f →
    ∃ (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p), Labels L s x f := by
  intro p _ L r f hm hr h0 hs
  obtain ⟨b, x, hx⟩ := exists_rootPoly r f hm hr h0 hs
  choose θ hθ using fun c => exists_char L (cycLen_pos b c) (hx.1 c)
  exact ⟨⟨b, θ⟩, x, hθ, hx⟩

end GlobalTheory.ParamExists

end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem isOpen_levelSub : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E))
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
      IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  intro E _ _ a r hr t L hL
  have hblk : Continuous fun l : GL (Fin (a - r)) (Af E) => blkGL hr (1, l) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 (l : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_val).matrix_reindex _ _
    · have e : ∀ l : GL (Fin (a - r)) (Af E), ((blkGL hr (1, l))⁻¹ : GL (Fin a) (Af E)) = blkGL hr (1, l⁻¹) := by
        intro l; rw [← map_inv]; rfl
      simp_rw [e]
      show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 ((l⁻¹ : GL _ _) : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_coe_inv).matrix_reindex _ _
  have hc : Continuous fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t :=
    (continuous_const.mul hblk).mul continuous_const
  have hs : (levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) =
      (fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t) ⁻¹' (L : Set (GL (Fin a) (Af E))) := by
    ext l
    simp only [levelSub, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, e⟩
      rw [← e]; simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  rw [hs]
  exact hL.preimage hc

end GlobalTheory.SliceTwo
end

section

open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K)
    (w : Cot K ((PDivGroup.frobTwist h G).A 1)) :
    ∃ (β : (PDivGroup.frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((PDivGroup.relFrob h G).app 1 β) = 0 ∧
        dUnit (R := K) β = w + cotMap ((PDivGroup.verschiebung h G).app 1) w' :=
  PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq p K h G w
end

section

noncomputable section

open NumberField

namespace GlobalTheory.VacRead

def cE (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {x | ∃ c ∈ cc, x = ((c : D.host.K) : D.host.E)}

def bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {y | ∃ α ∈ cE D cc, ∃ γ ∈ cE D D.host.ccK,
    y = r * D.host.conj α * γ / (Ideal.absNorm cc : D.host.E)}

def lsB (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) : GlobalTheory.InertSign.Lat D a :=
  Submodule.pi Set.univ fun _ => bInv D cc r

theorem mem_lsB {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} {a : ℕ} {y : Fin a → D.host.E} :
    y ∈ lsB D cc r a ↔ ∀ i, y i ∈ bInv D cc r := by
  simp [lsB, Submodule.mem_pi]

end GlobalTheory.VacRead
end
end
