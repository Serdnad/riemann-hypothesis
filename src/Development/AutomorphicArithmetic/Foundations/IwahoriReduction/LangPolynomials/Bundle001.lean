module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.ZMod.UnitsCyclic
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace UpperTheory.Kd.C7

private theorem mem_zpowers_un_of_primitive_root_mod_sq {l : ℕ} [Fact (Nat.Prime l)] (hl2 : l ≠ 2) (g : ℕ) (hg : ¬ l ∣ g)
    (ho : orderOf (g : ZMod l) = l - 1) (hnd : ¬ ((l : ℤ) ^ 2 ∣ (g : ℤ) ^ (l - 1) - 1))
    (r : ℕ) (x : (ZMod (l ^ r))ˣ) : x ∈ Subgroup.zpowers (un g hg r) := by
  have hp : l.Prime := Fact.out
  have hgl : (g : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hg
  have hf : (l : ℤ) ∣ (g : ℤ) ^ (l - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one hgl, sub_self]
  obtain ⟨a, ha⟩ := hf
  have han : ¬ (l : ℤ) ∣ a := by
    rintro ⟨b, rfl⟩
    exact hnd ⟨b, by rw [ha]; ring⟩
  have hga : (g : ℤ) ^ (l - 1) = 1 + l * a := by
    rw [← ha]; ring
  rcases r with _ | n
  · have : Subsingleton (ZMod (l ^ 0))ˣ := by
      rw [pow_zero]; infer_instance
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  set u := un g hg (n + 1) with hu
  have hcast : (u : ZMod (l ^ (n + 1))) = (g : ZMod (l ^ (n + 1))) := by
    simp [hu, un]
  have h1 : orderOf (u ^ (l - 1)) = l ^ n := by
    rw [← orderOf_units, Units.val_pow_eq_pow_val, hcast]
    have e : (g : ZMod (l ^ (n + 1))) ^ (l - 1) = 1 + (l : ZMod (l ^ (n + 1))) * (a : ZMod (l ^ (n + 1))) := by
      have := congrArg (Int.cast : ℤ → ZMod (l ^ (n + 1))) hga
      push_cast at this
      exact this
    rw [e]
    exact ZMod.orderOf_one_add_mul_prime hp hl2 a han n
  have hm : l ∣ l ^ (n + 1) := dvd_pow_self l (Nat.succ_ne_zero n)
  have h2 : l - 1 ∣ orderOf u := by
    have h3 : orderOf (ZMod.unitsMap hm u) = l - 1 := by
      rw [← orderOf_units]
      have : ((ZMod.unitsMap hm u : (ZMod l)ˣ) : ZMod l) = (g : ZMod l) := by
        simp [ZMod.unitsMap, hcast]
      rw [this, ho]
    rw [← h3]
    exact orderOf_map_dvd _ u
  have h4 : l ^ n ∣ orderOf u := h1 ▸ orderOf_pow_dvd _
  have hcard : Nat.card (ZMod (l ^ (n + 1)))ˣ = l ^ n * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp]
  have hcop : Nat.Coprime (l ^ n) (l - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_self_sub_right hp.pos]
    simp
  have h5 : orderOf u = Nat.card (ZMod (l ^ (n + 1)))ˣ := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_natCard u
    · rw [hcard]
      exact hcop.mul_dvd_of_dvd_of_dvd h4 h2
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, h5]
  rw [htop]
  exact Subgroup.mem_top x

theorem pGenEx : SGenEx := by
  intro l _ hl2
  have hp : l.Prime := Fact.out
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hc
  have hc0 : (((c : ZMod l).val : ℕ) : ZMod l) = c := ZMod.natCast_zmod_val _
  set c0 : ℕ := (c : ZMod l).val with hc0def
  have hnd0 : ¬ l ∣ c0 := by
    intro h
    have h' := (ZMod.natCast_eq_zero_iff c0 l).mpr h
    rw [hc0] at h'
    exact c.ne_zero h'
  have hord : ∀ k : ℕ, orderOf ((c0 + l * k : ℕ) : ZMod l) = l - 1 := by
    intro k
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, hc0, orderOf_units, hc]
  have hndk : ∀ k : ℕ, ¬ l ∣ c0 + l * k := by
    intro k h
    exact hnd0 ((Nat.dvd_add_left (dvd_mul_right l k)).mp h)
  have hc2 : 2 ≤ c0 := by
    by_contra h
    push_neg at h
    have h01 : c0 = 0 ∨ c0 = 1 := by omega
    rcases h01 with h0 | h1
    · exact hnd0 (h0 ▸ dvd_zero l)
    · have h1' : (c : ZMod l) = 1 := by
        rw [← hc0, h1, Nat.cast_one]
      have hc1 : c = 1 := Units.ext h1'
      rw [hc1, orderOf_one] at hc
      have := hp.two_le
      omega
  by_cases hsq : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1) - 1
  · have hnd1 : ¬ ((l : ℤ) ^ 2 ∣ ((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1) := by
      intro hB
      have key := sq_dvd_add_pow_sub_sub (l : ℤ) (c0 : ℤ) (l - 1)
      have hsum : (l : ℤ) ^ 2 ∣ (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by
        have e : (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) =
            (((c0 + l * 1 : ℕ) : ℤ) ^ (l - 1) - 1)
              - (((c0 : ℤ) + l) ^ (l - 1) - (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ)
                - (c0 : ℤ) ^ (l - 1))
              - ((c0 : ℤ) ^ (l - 1) - 1) := by
          push_cast
          ring
        rw [e]
        exact dvd_sub (dvd_sub hB key) hsq
      have h6 : (l : ℤ) ∣ (c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ) := by
        have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        rw [← mul_dvd_mul_iff_left hl0]
        have e2 : (l : ℤ) * ((c0 : ℤ) ^ (l - 1 - 1) * ((l - 1 : ℕ) : ℤ))
            = (c0 : ℤ) ^ (l - 1 - 1) * l * ((l - 1 : ℕ) : ℤ) := by ring
        rw [e2, ← sq]
        exact hsum
      have h7 : l ∣ c0 ^ (l - 1 - 1) * (l - 1) := by exact_mod_cast h6
      rcases (Nat.Prime.dvd_mul hp).mp h7 with h8 | h8
      · exact hnd0 (hp.dvd_of_dvd_pow h8)
      · have := hp.two_le
        have := Nat.le_of_dvd (by omega) h8
        omega
    exact ⟨c0 + l * 1, hndk 1, by omega, mem_zpowers_un_of_primitive_root_mod_sq hl2 _ (hndk 1) (hord 1) hnd1⟩
  · have h0 := hord 0
    simp only [mul_zero, add_zero] at h0
    exact ⟨c0, hnd0, hc2, mem_zpowers_un_of_primitive_root_mod_sq hl2 c0 hnd0 h0 hsq⟩

end UpperTheory.Kd.C7
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pKumTriv :
    UpperTheory.Kd.C7.SKumTriv := by
  intro l _ _ Ω _ _ _ A _ ζ hζ m n hnm u hu h
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
    exact ⟨⟨ζ i, (hζ i).1⟩, inferInstance⟩
  have hpos : 0 < l ^ n := pow_pos hp.pos n
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq u hpos
  refine ⟨v, hv, fun s hs => ?_⟩
  obtain ⟨w, hw, hsw⟩ := h s hs
  rw [ZMod.val_zero, pow_zero, one_mul] at hsw
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (v / w) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  have hc : cycMod ℚ Ω l m s = 1 := (Subgroup.mem_inf.1 hs).2
  have h2 : s (v / w) = v / w := fix_of_cycMod hnm hc h1
  have e : v = v / w * w := by field_simp
  calc s v = s (v / w * w) := by rw [← e]
    _ = v / w * w := by rw [map_mul, h2, hsw]
    _ = v := e.symm
end

section

noncomputable section

open GlobalTheory.Col

namespace UpperTheory.Kd.C7

private theorem cyc_charP (S : Type) [CommRing S] (p : ℕ) [hp : Fact p.Prime] [CharP S p] (j : ℕ) :
    cyc S p (j + 1) = PowerSeries.X ^ (p ^ (j + 1) - p ^ j) := by
  have h := Polynomial.cyclotomic_mul_prime_pow_eq S (p := p) (m := 1) (by simpa using hp.out.one_lt.ne') (k := j + 1) (Nat.succ_pos j)
  rw [mul_one, Polynomial.cyclotomic_one] at h
  rw [cyc, h, Polynomial.eval₂_pow]
  simp

private theorem dvd_of_map {R : Type} [CommRing R] (p : ℕ) (h : PowerSeries R)
    (H : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) h = 0) :
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) * h' := by
  have : ∀ k, ∃ y : R, y * p = PowerSeries.coeff k h := by
    intro k
    have := congrArg (PowerSeries.coeff k) H
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this
    exact Ideal.mem_span_singleton'.1 this
  choose y hy using this
  refine ⟨PowerSeries.mk y, ?_⟩
  ext k
  rw [← map_natCast (PowerSeries.C (R := R)), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hy, mul_comm]

private theorem step {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime] (hpr : Prime (p : R))
    (h : PowerSeries R) (c m₀ : ℕ)
    (H : ∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b) :
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) * h' ∧ ∀ m, m₀ + c + 1 ≤ m →
      ∃ a b : PowerSeries R, h' = (p : PowerSeries R) ^ (m - (c + 1)) * a + cyc R p m * b := by
  set π := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hπ
  haveI : Nontrivial (R ⧸ Ideal.span {(p : R)}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact hpr.not_isUnit)
  have hp0 : ((p : ℕ) : R ⧸ Ideal.span {(p : R)}) = 0 := by
    rw [← map_natCast π]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0
  have hp1 : ((p : ℕ) : PowerSeries (R ⧸ Ideal.span {(p : R)})) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := R ⧸ Ideal.span {(p : R)})), hp0, map_zero]
  have key : ∀ j, c ≤ j → ∀ a b : PowerSeries R, h = (p : PowerSeries R) ^ (j + 1 - c) * a + cyc R p (j + 1) * b →
      PowerSeries.map π h = PowerSeries.X ^ (p ^ (j + 1) - p ^ j) * PowerSeries.map π b := by
    intro j hj a b hab
    rw [hab, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, hp1, zero_pow (by omega), zero_mul, zero_add,
      coeffMap_cyc, cyc_charP]
  have h0 : PowerSeries.map π h = 0 := by
    ext k
    obtain ⟨a, b, hab⟩ := H (m₀ + c + k + 1) (by omega)
    have h1 := key (m₀ + c + k) (by omega) a b hab
    have h2 : k < p ^ (m₀ + c + k + 1) - p ^ (m₀ + c + k) := by
      have h3 : m₀ + c + k < p ^ (m₀ + c + k) := Nat.lt_pow_self hp.out.one_lt
      have h4 : p ^ (m₀ + c + k) * 2 ≤ p ^ (m₀ + c + k + 1) := by
        rw [pow_succ]; exact Nat.mul_le_mul_left _ hp.out.two_le
      omega
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 ⟨_, h1⟩ k h2
  obtain ⟨h', hh'⟩ := dvd_of_map p h h0
  refine ⟨h', hh', fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a, b, hab⟩ := H (j + 1) (by omega)
  have h1 := key j (by omega) a b hab
  rw [h0] at h1
  have h2 : PowerSeries.map π b = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff (k + (p ^ (j + 1) - p ^ j))) h1
    rw [PowerSeries.coeff_X_pow_mul] at this
    simpa using this.symm
  obtain ⟨b', hb'⟩ := dvd_of_map p b h2
  refine ⟨a, b', ?_⟩
  have hne : ((p : ℕ) : PowerSeries R) ≠ 0 := by
    rw [← map_natCast (PowerSeries.C (R := R))]
    intro h3
    exact hpr.ne_zero (by simpa using congrArg (PowerSeries.coeff 0) h3)
  apply mul_left_cancel₀ hne
  have e : j + 1 - c = (j + 1 - (c + 1)) + 1 := by omega
  rw [← hh', hab, hb', e]
  ring

private theorem allDvd {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime] (hpr : Prime (p : R)) (n : ℕ) :
    ∀ (h : PowerSeries R) (c m₀ : ℕ),
    (∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b) →
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) ^ n * h' := by
  induction n with
  | zero => intro h _ _ _; exact ⟨h, by simp⟩
  | succ n ih =>
    intro h c m₀ H
    obtain ⟨h', e, H'⟩ := step p hpr h c m₀ H
    obtain ⟨h'', e'⟩ := ih h' (c + 1) (m₀ + c + 1) H'
    exact ⟨h'', by rw [e, e']; ring⟩

private theorem pow_comp_pow {R : Type} [CommRing R] (σ : R ≃+* R) (m : ℕ) (x : R) :
    ((σ : R →+* R) ^ m) ((((σ.symm : R ≃+* R) : R →+* R) ^ m) x) = x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (σ : R →+* R), pow_succ' ((σ.symm : R ≃+* R) : R →+* R)]
    simp only [RingHom.mul_def, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact ih x

theorem pUniq : SUniq := by
  intro R _ p hp σ hF h c m₀ H
  haveI := hF.dom
  haveI := hF.complete
  have H' : ∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b := by
    intro m hm
    have h1 := H m hm
    rw [LC, map_zero, sub_zero] at h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_natCast (ev R p m), ← map_pow, ← map_mul, eq_comm, Ideal.Quotient.eq] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hy
    have h2 := congrArg (PowerSeries.map ((σ : R →+* R) ^ m)) hb
    have h3 : PowerSeries.map ((σ : R →+* R) ^ m) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ m) h) = h := by
      ext k
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map, pow_comp_pow]
    rw [map_sub, h3, map_mul, map_mul, map_pow, map_natCast, coeffMap_cyc] at h2
    exact ⟨PowerSeries.map ((σ : R →+* R) ^ m) a, PowerSeries.map ((σ : R →+* R) ^ m) b, by linear_combination -h2⟩
  ext k
  rw [map_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : R)}) inferInstance _ fun n => ?_
  obtain ⟨h', e⟩ := allDvd p hF.prime n h c m₀ H'
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨PowerSeries.coeff k h', ?_⟩
  rw [e, ← map_natCast (PowerSeries.C (R := R)), ← map_pow, PowerSeries.coeff_C_mul, mul_comm]

end UpperTheory.Kd.C7
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

private theorem roots_pow {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : Roots l ζ) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, (h (n + d)).2, ih]

private theorem nat_le_one {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem add_le {l : ℕ} [Fact l.Prime] {a b : Qbar l} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max (S := PadicAlgCl l) a b).trans (max_le ha hb)

theorem pPresMono : SPresMono := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z Z' m n n' P hn hZ hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hlp.pos i).ne'⟩
    infer_instance
  haveI : NeZero (l ^ n') := ⟨(pow_pos hlp.pos n').ne'⟩
  refine ⟨(hζ n').1, hn.trans h2, h3, h4, fun s hs hc _ => ?_⟩
  obtain ⟨k, hk, hcg⟩ := h5 s hs hc (fix_of_cycMod h2 hc h1.pow_eq_one)
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hk i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm d n', hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, roots_pow hζ, ZMod.val_natCast]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n'), pow_add, pow_mul, (hζ n').1.pow_eq_one, one_pow, one_mul]
  · have hz := hZ s ⟨hs, hc⟩
    unfold Cg at hz hcg ⊢
    have e1 : ‖Z m s 1 - ∑ i, β.val i * (((k i).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine hcg.trans ?_
      rw [pow_add, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      exact_mod_cast nat_le_one (l := l) (l ^ d)
    have e2 : ‖∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ 1 := by
      refine Finset.sum_induction _ (fun x : Qbar l => ‖x‖ ≤ 1) (fun a b => add_le) (by simp) (fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_one₀ (h4 i) (norm_nonneg _) (nat_le_one _)
    have e3 : ‖((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) e2
    rw [norm_sub_rev] at hz
    have e4 : ∑ i, β.val i * (((k i).val : ℕ) : Qbar l) =
        ((l : ℕ) : Qbar l) ^ n' * ∑ i, β.val i * ((((k i).val / l ^ n' : ℕ) : Qbar l)) +
        ∑ i, β.val i * (((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZMod.val_natCast]
      conv_lhs => rw [← Nat.div_add_mod (k i).val (l ^ n')]
      push_cast
      ring
    have := add_le (add_le hz e1) e3
    rw [e4] at this
    convert this using 2
    ring

end UpperTheory.Kd.C7
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem iwOps_red_un {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) (r : ℕ) :
    red l r (un b hb (r + 1)) = un b hb r := by
  ext
  simp only [un, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, map_natCast]

private theorem iwOps_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {A : ValuationSubring Ω} {Z : Sy Ω l} (h : IwI c A Z) (b : ℕ) (hb : ¬ l ∣ b) : IwI c A (tr b hb Z) := by
  refine ⟨fun r s hs x => h.int r s hs _, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.coc r s hs t ht, mul_right_comm]
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.nrm r s hs]
    symm
    refine Finset.sum_equiv (Equiv.mulRight (un b hb (r + 1))) (fun y => ?_) (fun y _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    rw [map_mul, iwOps_red_un, mul_left_inj]

theorem UpperTheory.Kd.C7.pIwOps :
    UpperTheory.Kd.C7.SIwOps := by
  intro l _ _ Ω _ _ _ A _ c Z h b hb
  have h' := iwOps_tr h b hb
  refine ⟨h', fun r s hs x => ?_, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · exact c.O.sub_mem (h.int r s hs x) (c.O.mul_mem (natCast_mem c.O b) (h'.int r s hs x))
  · simp only [sharp]
    rw [h.coc r s hs t ht, h'.coc r s hs t ht]
    ring
  · simp only [sharp]
    rw [h.nrm r s hs, h'.nrm r s hs, Finset.sum_sub_distrib, Finset.mul_sum]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem ka_pw {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {z : Ω} (hz : z ^ N = 1) (a : ℕ) (k : ZMod N)
    (h : (a : ZMod N) = k) : z ^ k.val = z ^ a := by
  rw [← h, ZMod.val_natCast]
  exact (pow_eq_pow_mod a hz).symm

private theorem ka_down {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : ∀ m, ζ (m + 1) ^ l = ζ m) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← Nat.add_assoc, h, ih]

theorem UpperTheory.Kd.C7.pKumAlg :
    UpperTheory.Kd.C7.SKumAlg := by
  intro l hl _ Ω _ _ _ A _ ζ hζ m n _ s _
  have hne : ∀ r : ℕ, NeZero (l ^ r) := fun r => ⟨(pow_pos hl.out.pos r).ne'⟩
  have h1 : ∀ r, ζ r ^ l ^ r = 1 := fun r => (hζ r).1.pow_eq_one
  haveI := hne n
  refine ⟨?_, ?_, ?_⟩
  · rintro u u' k k' ⟨v, rfl, hv⟩ ⟨v', rfl, hv'⟩
    refine ⟨⟨v * v', mul_pow _ _ _, ?_⟩, ⟨v⁻¹, inv_pow _ _, ?_⟩, fun a => ⟨v ^ a, ?_, ?_⟩⟩
    · rw [map_mul, hv, hv', ka_pw (h1 n) (k.val + k'.val) (k + k') (by simp), pow_add]
      ring
    · have e : ζ n ^ (-k).val * ζ n ^ k.val = 1 := by
        rw [← pow_add, ← ka_pw (h1 n) ((-k).val + k.val) 0 (by simp), ZMod.val_zero, pow_zero]
      rw [map_inv₀, hv, mul_inv, eq_inv_of_mul_eq_one_left e]
    · rw [← pow_mul, ← pow_mul, mul_comm]
    · rw [map_pow, hv, ka_pw (h1 n) (k.val * a) (a * k) (by simp [mul_comm]), mul_pow, pow_mul]
  · rintro u k n' hn' - ⟨v, rfl, hv⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn'
    haveI := hne n'
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm], ?_⟩
    rw [map_pow, hv, ka_pw (h1 n') k.val _ rfl, mul_pow, ← pow_mul, mul_comm k.val, pow_mul,
      ka_down (fun r => (hζ r).2)]
  · rintro u k t ⟨v, hu, hv⟩
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
    have ht : t (ζ n) = ζ n ^ ((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω t) (ζ n) (h1 n)
    refine ⟨t v, ?_, ?_⟩
    · rw [← map_pow, hu, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    · rw [← AlgEquiv.mul_apply, inv_mul_cancel_right, AlgEquiv.mul_apply, hv, map_mul, map_pow, ht, ← pow_mul,
        ka_pw (h1 n) (((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val * k.val) _ (by simp)]
end
