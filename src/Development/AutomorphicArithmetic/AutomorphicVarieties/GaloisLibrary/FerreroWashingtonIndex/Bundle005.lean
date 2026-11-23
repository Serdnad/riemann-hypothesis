module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle004
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

section

open UpperTheory.V.FW

private theorem coeff_thetaH (M c : ℕ) [NeZero M] (s : (ZMod M)ˣ) :
    (thetaH M c).coeff s = if 2 * (s : ZMod M).val < M then gc M c s else 0 := by
  classical
  simp [thetaH, Finsupp.single_apply, Finset.sum_ite_eq']

private theorem coeff_mul_J (M : ℕ) [NeZero M] (f : MonoidAlgebra ℤ (ZMod M)ˣ) (s : (ZMod M)ˣ) :
    (f * MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)).coeff s = f.coeff (-s) := by
  rw [show MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ) = MonoidAlgebra.single (-1) 1 from rfl]
  rw [MonoidAlgebra.coeff_mul_single_eq_coeff_mul (-s), mul_one]
  intro m _
  rw [mul_neg_one, neg_eq_iff_eq_neg]

private theorem half (M : ℕ) [NeZero M] (hM : 2 < M) (s : (ZMod M)ˣ) :
    (s : ZMod M) ≠ 0 ∧ (2 * (-(s : ZMod M)).val < M ↔ ¬ 2 * (s : ZMod M).val < M) := by
  have hs0 : (s : ZMod M) ≠ 0 := by
    haveI : Fact (1 < M) := ⟨by omega⟩
    exact s.ne_zero
  refine ⟨hs0, ?_⟩
  rw [ZMod.neg_val, if_neg hs0]
  have hlt := ZMod.val_lt (s : ZMod M)
  have hne : 2 * (s : ZMod M).val ≠ M := by
    intro h
    have h2 : (2 : ZMod M) * (s : ZMod M) = 0 := by
      have : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0 := by
        rw [h]
        exact ZMod.natCast_self M
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    have h3 : (2 : ZMod M) = 0 := by
      have := congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h2
      simpa [mul_assoc] using this
    have h4 : ((2 : ℕ) : ZMod M) = 0 := by exact_mod_cast h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  omega

theorem UpperTheory.V.FW.thetaFull :
    ∀ (M c : ℕ) [NeZero M], c.Coprime M → Odd c → 2 < M → thetaH M c * (1 - MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)) = ∑ s : (ZMod M)ˣ, MonoidAlgebra.single s (gc M c s) ∧ ∀ s : (ZMod M)ˣ, (((thetaH M c * (1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ))).coeff s : ℤ) : ZMod 2) = (gc M c s : ZMod 2) := by
  intro M c _ hc hodd hM
  have key : ∀ s : (ZMod M)ˣ, (thetaH M c).coeff (-s) = if 2 * (s : ZMod M).val < M then 0 else -gc M c s := by
    intro s
    obtain ⟨hs0, hiff⟩ := half M hM s
    rw [coeff_thetaH, Units.val_neg]
    by_cases h : 2 * (s : ZMod M).val < M
    · rw [if_neg (fun h' => hiff.mp h' h), if_pos h]
    · rw [if_pos (hiff.mpr h), if_neg h, gcNeg M c _ hc hodd hs0]
  constructor
  · rw [mul_sub, mul_one, sub_eq_iff_eq_add]
    refine MonoidAlgebra.ext (Finsupp.ext fun s => ?_)
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    classical
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs <;> simp
  · intro s
    rw [mul_add, mul_one, MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    split_ifs
    · simp
    · push_cast
      simp [ZMod.neg_eq_self_mod_two]
end

section

open UpperTheory.V.FW

private theorem gauss_count_shift_eq_sum (M c : ℕ) [NeZero M] (s : ZMod M) (hc : c.Coprime M) (n : ℕ) :
    gc M c s - gc M c (s - ((c * n : ℕ) : ZMod M)) =
      ∑ j ∈ Finset.range (c * n), if (j : ZMod M) = s then (1 - if c ∣ j then (c : ℤ) else 0) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := gcDiff M c (s - ((c * n : ℕ) : ZMod M)) hc
    have e : s - ((c * (n + 1) : ℕ) : ZMod M) = s - ((c * n : ℕ) : ZMod M) - c := by
      push_cast; ring
    rw [e, Nat.mul_succ, Finset.sum_range_add, ← ih]
    have key : (∑ j ∈ Finset.range c, if ((c * n + j : ℕ) : ZMod M) = s then
        (1 - if c ∣ c * n + j then (c : ℤ) else 0) else 0) =
        (∑ j ∈ Finset.range c, if (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) then 1 else 0) -
          if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0 := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · simp
      have h2 : (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) =
          ∑ j ∈ Finset.range c, if j = 0 then
            (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range c) 0]
        simp [hpos]
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have h3 : (((c * n + j : ℕ) : ZMod M) = s) ↔ (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) := by
        rw [Nat.cast_add, eq_sub_iff_add_eq']
      have h4 : c ∣ c * n + j ↔ j = 0 := by
        rw [Nat.dvd_add_right (dvd_mul_right c n)]
        exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hj', fun h => h ▸ dvd_zero c⟩
      simp only [h3, h4]
      generalize s - ((c * n : ℕ) : ZMod M) = t
      by_cases h0 : j = 0
      · subst h0
        by_cases ht : t = 0
        · simp [ht]
        · simp [ht, Ne.symm ht]
      · simp [h0]
    rw [key, ← h]
    ring

theorem UpperTheory.V.FW.gcShift :
    ∀ (M c F : ℕ) [NeZero M] (k : Type) [CommRing k] (Ψ : ZMod M → k) (s : ZMod M), c.Coprime M → (∀ x, Ψ (x + F) = Ψ x) → (gc M c s : k) * Ψ s - (gc M c (s - ((c * F : ℕ) : ZMod M)) : k) * Ψ (s - ((c * F : ℕ) : ZMod M)) = ∑ j ∈ Finset.range (c * F), if (j : ZMod M) = s then Ψ j * (1 - if c ∣ j then (c : k) else 0) else 0 := by
  intro M c F _ k _ Ψ s hc hΨ
  have hp : ∀ n : ℕ, Ψ (s - ((n * F : ℕ) : ZMod M)) = Ψ s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← hΨ (s - (((n + 1) * F : ℕ) : ZMod M))]
      congr 1
      push_cast; ring
  rw [hp c, ← sub_mul, ← Int.cast_sub, gauss_count_shift_eq_sum M c s hc F, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ZMod M) = s
  · rw [if_pos h, if_pos h, h, mul_comm]
    by_cases h' : c ∣ j <;> simp [h']
  · simp [h]
end

section

open UpperTheory.V.FW

private theorem even_tot (l : ℕ) [hl : Fact l.Prime] : Even (Nat.totient (l ^ ee l)) := by
  apply Nat.totient_even
  unfold ee
  split_ifs with h
  · subst h; norm_num
  · have := hl.out.two_le
    rw [pow_one]; omega

private theorem pos_tot (l : ℕ) [hl : Fact l.Prime] : 0 < Nat.totient (l ^ ee l) :=
  Nat.totient_pos.2 (pow_pos hl.out.pos _)

private theorem neg_ne (l : ℕ) [Fact l.Prime] (r : ℤ_[l]ˣ) : r ≠ -r := by
  intro h
  have h1 : (r : ℤ_[l]) = -(r : ℤ_[l]) := by
    have := congrArg Units.val h
    simpa using this
  exact r.ne_zero (self_eq_neg.1 h1)

theorem UpperTheory.V.FW.reps :
    ∀ (l : ℕ) [Fact l.Prime], ∃ R : Finset ℤ_[l]ˣ, R.Nonempty ∧ (∀ r ∈ R, r ∈ WW l) ∧ (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ∀ a b : ℤ, (a : ℤ_[l]) * r = (b : ℤ_[l]) * r' → a = 0) ∧ (∀ r ∈ R, -r ∉ R) ∧ (∀ w ∈ WW l, w ∈ R ∨ -w ∈ R) ∧ (-1 : ℤ_[l]ˣ) ∈ WW l ∧ ∀ n, 2 ≤ n → ∀ w ∈ WW l, redU l n w = 1 → w = 1 := by
  intro l _
  classical
  have hev := even_tot l
  have hpos := pos_tot l
  haveI : NeZero (Nat.totient (l ^ ee l)) := ⟨hpos.ne'⟩
  have hfin : (WW l : Set ℤ_[l]ˣ).Finite := by
    have : Finite (rootsOfUnity (Nat.totient (l ^ ee l)) ℤ_[l]) := inferInstance
    exact Set.finite_coe_iff.1 this
  have hm1 : (-1 : ℤ_[l]ˣ) ∈ WW l := by
    unfold WW
    rw [mem_rootsOfUnity]
    exact hev.neg_one_pow
  have hneg : ∀ w ∈ WW l, -w ∈ WW l := fun w hw => by
    have := (WW l).mul_mem hm1 hw
    simpa using this
  letI : LinearOrder ℤ_[l]ˣ := linearOrderOfSTO WellOrderingRel
  let R : Finset ℤ_[l]ˣ := hfin.toFinset.filter fun r => r < -r
  have hR : ∀ r, r ∈ R ↔ r ∈ WW l ∧ r < -r := fun r => by simp [R]
  have h4 : ∀ r ∈ R, -r ∉ R := fun r hr hr' => by
    have h1 := ((hR _).1 hr).2
    have h2 := ((hR _).1 hr').2
    rw [neg_neg] at h2
    exact lt_asymm h1 h2
  have h5 : ∀ w ∈ WW l, w ∈ R ∨ -w ∈ R := fun w hw => by
    rcases lt_or_gt_of_ne (neg_ne l w) with h | h
    · exact Or.inl ((hR _).2 ⟨hw, h⟩)
    · exact Or.inr ((hR _).2 ⟨hneg w hw, by rwa [neg_neg]⟩)
  refine ⟨R, ?_, fun r hr => ((hR r).1 hr).1, ?_, h4, h5, hm1, ?_⟩
  · rcases h5 1 (WW l).one_mem with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  · intro r hr r' hr' hne a b hab
    by_contra ha
    have e1 : (r : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1 :=
      (mem_rootsOfUnity' _ _).1 ((hR _).1 hr).1
    have e2 : (r' : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1 :=
      (mem_rootsOfUnity' _ _).1 ((hR _).1 hr').1
    have e3 := congrArg (· ^ Nat.totient (l ^ ee l)) hab
    simp only [mul_pow, e1, e2, mul_one] at e3
    have e4 : a ^ Nat.totient (l ^ ee l) = b ^ Nat.totient (l ^ ee l) := by exact_mod_cast e3
    have ha' : (a : ℤ_[l]) ≠ 0 := by exact_mod_cast ha
    rcases (pow_eq_pow_iff_of_ne_zero hpos.ne').1 e4 with h | ⟨h, -⟩
    · subst h
      exact hne (Units.ext (mul_left_cancel₀ ha' hab))
    · have hb : (b : ℤ_[l]) = -(a : ℤ_[l]) := by rw [h]; simp
      rw [hb, neg_mul, ← mul_neg] at hab
      have : r = -r' := Units.ext (by simpa using mul_left_cancel₀ ha' hab)
      exact h4 r' hr' (this ▸ hr)
  · intro n hn w hw h1
    have hle : ee l ≤ n := by
      unfold ee; split_ifs <;> omega
    have h2 : PadicInt.toZModPow n (w : ℤ_[l]) = 1 := by
      have := congrArg Units.val h1
      simpa [redU] using this
    have h3 : PadicInt.toZModPow (ee l) (w : ℤ_[l]) = 1 := by
      rw [← PadicInt.zmod_cast_comp_toZModPow (ee l) n hle, RingHom.comp_apply, h2, map_one]
    have h4 : ((redU l (ee l)).comp (WW l).subtype) ⟨w, hw⟩ = ((redU l (ee l)).comp (WW l).subtype) 1 := by
      rw [map_one]
      apply Units.ext
      simpa [redU] using h3
    exact congrArg Subtype.val ((teich l).1 h4)
end

section

open UpperTheory.V.FW

private theorem crt_apply {a b : ℕ} (hab : a.Coprime b) (x : ZMod (a * b)) :
    ZMod.chineseRemainder hab x =
      (ZMod.castHom (Dvd.intro b rfl) (ZMod a) x, ZMod.castHom (Dvd.intro_left a rfl) (ZMod b) x) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, map_intCast, map_intCast]
  rfl

private theorem crt_inj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b) (x y : (ZMod (a * b))ˣ)
    (h1 : ZMod.unitsMap ha x = ZMod.unitsMap ha y) (h2 : ZMod.unitsMap hb x = ZMod.unitsMap hb y) : x = y := by
  apply Units.ext
  apply (ZMod.chineseRemainder hab).injective
  rw [crt_apply, crt_apply]
  exact Prod.ext (congrArg Units.val h1) (congrArg Units.val h2)

private theorem crt_surj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b)
    (u : (ZMod a)ˣ) (v : (ZMod b)ˣ) :
    ∃ x : (ZMod (a * b))ˣ, ZMod.unitsMap ha x = u ∧ ZMod.unitsMap hb x = v := by
  let x : (ZMod (a * b))ˣ :=
    Units.map (ZMod.chineseRemainder hab).symm.toMonoidHom (MulEquiv.prodUnits.symm (u, v))
  have hx : ZMod.chineseRemainder hab (x : ZMod (a * b)) = ((u : ZMod a), (v : ZMod b)) :=
    (ZMod.chineseRemainder hab).apply_symm_apply _
  rw [crt_apply] at hx
  exact ⟨x, Units.ext (congrArg Prod.fst hx), Units.ext (congrArg Prod.snd hx)⟩

private theorem map_map {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (x : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 x) = ZMod.unitsMap (h1.trans h2) x := by
  rw [← ZMod.unitsMap_comp h1 h2]
  rfl

private theorem map_redU (l : ℕ) [Fact l.Prime] {m n : ℕ} (hmn : m ≤ n) (h : l ^ m ∣ l ^ n) (w : ℤ_[l]ˣ) :
    ZMod.unitsMap h (redU l n w) = redU l m w := by
  apply Units.ext
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])

theorem UpperTheory.V.FW.deltaBij :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (h' : l ^ n ∣ f * l ^ n), f.Coprime l → ee l ≤ n → Function.Bijective ((ZMod.unitsMap h).comp (((WW l).map (redU l n)).comap (ZMod.unitsMap h')).subtype) := by
  intro l _ f n h h' hf hn
  have hen : l ^ ee l ∣ l ^ n := pow_dvd_pow l hn
  have hfe : f ∣ f * l ^ ee l := Dvd.intro _ rfl
  have hle : l ^ ee l ∣ f * l ^ ee l := Dvd.intro_left _ rfl
  have hfn : f ∣ f * l ^ n := Dvd.intro _ rfl
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨g, w, hw, hwg⟩ hg
    have hg' : ZMod.unitsMap h g = 1 := hg
    have h1 : redU l (ee l) w = 1 := by
      rw [← map_redU l hn hen, hwg, map_map, ← map_map hle h, hg', map_one]
    have h2 : (⟨w, hw⟩ : WW l) = 1 := (injective_iff_map_eq_one _).1 (teich l).1 _ h1
    have h3 : w = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    show g = 1
    apply crt_inj (hf.pow_right n) hfn h'
    · rw [← map_map hfe h, hg', map_one, map_one]
    · rw [← hwg, h3, map_one, map_one]
  · intro u
    obtain ⟨w, hw⟩ := (teich l).2 (ZMod.unitsMap hle u)
    have hw' : redU l (ee l) w = ZMod.unitsMap hle u := hw
    obtain ⟨g, hg1, hg2⟩ := crt_surj (hf.pow_right n) hfn h' (ZMod.unitsMap hfe u) (redU l n w)
    refine ⟨⟨g, w, w.2, hg2.symm⟩, ?_⟩
    show ZMod.unitsMap h g = u
    apply crt_inj (hf.pow_right (ee l)) hfe hle
    · rw [map_map, hg1]
    · rw [map_map, ← map_map hen h', hg2, map_redU l hn, hw']
end

section

open UpperTheory.V.FW

private theorem gen2 {G Q W : Type} [Group G] [Finite Q] [AddCommGroup W] (h2 : ∀ w : W, 2 • w = 0)
    (ψ : MonoidAlgebra ℤ G →+ W) (hψ : Function.Surjective ψ) (p : G → Q) (v : Q → W)
    (hv : ∀ g, ψ (MonoidAlgebra.single g 1) = v (p g)) :
    Finite W ∧ Nat.card W ≤ 2 ^ Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Module (ZMod 2) W := AddCommGroup.zmodModule h2
  let φ : (Q → ZMod 2) →ₗ[ZMod 2] W := Fintype.linearCombination (ZMod 2) v
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hψ w
    change ψ x ∈ (LinearMap.range φ).toAddSubgroup
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add ψ]; exact add_mem ha hb
    | single g n =>
      have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
      rw [this, map_zsmul]
      refine zsmul_mem ?_ _
      rw [hv]
      exact ⟨Pi.single (p g) 1, by simp [φ]⟩
  refine ⟨Finite.of_surjective φ hs, ?_⟩
  have := Nat.card_le_card_of_surjective φ hs
  simpa [Nat.card_fun] using this

private noncomputable def kap {G : Type} [CommGroup G] (J : G) : MonoidAlgebra ℤ G →+ (G → ZMod 2) where
  toFun x := fun g => (((x * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)
  map_zero' := by ext g; simp
  map_add' a b := by ext g; simp [add_mul]

private theorem kap_apply {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J x g = (x.coeff g : ZMod 2) + (x.coeff (J * g) : ZMod 2) := by
  have : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ
  simp [kap, mul_add, this, mul_comm J g]

private theorem kap_single_mul {G : Type} [CommGroup G] {J : G} (hJ : J * J = 1) (x : MonoidAlgebra ℤ G) (g : G) :
    kap J (MonoidAlgebra.single g 1 * x) = fun h => kap J x (g⁻¹ * h) := by
  ext h
  simp [kap_apply hJ, mul_left_comm]

private theorem kap_range {G : Type} [CommGroup G] [Finite G] {J : G} (hJ : J * J = 1) (hJ1 : J ≠ 1) :
    (kap J).range = evenF J := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩ g
    rw [kap_apply hJ, kap_apply hJ, ← mul_assoc, hJ, one_mul, add_comm]
  · intro f hf
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => if e g < e (J * g) then ((f g).val : ℤ) else 0), ?_⟩
    ext g
    have hne : e g ≠ e (J * g) := fun h => hJ1 (by simpa using e.injective h)
    have hfg : f (J * g) = f g := hf g
    rw [kap_apply hJ]
    simp only [MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm, ← mul_assoc, hJ, one_mul]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, h.le]
    · simp [h, h.le, hfg]

theorem UpperTheory.V.FW.sgnAlg :
    ∀ (G : Type) [CommGroup G] [Finite G] (J γ : G) (θ : MonoidAlgebra ℤ G) (N : ℕ) (S : AddSubgroup (G → ZMod 2)), J * J = 1 → J ≠ 1 → (∀ f ∈ S, ∀ g, (fun x => f (g * x)) ∈ S) → (fun g => (((θ * (1 + MonoidAlgebra.of ℤ G J)).coeff g : ℤ) : ZMod 2)) ∈ S → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, ((2 : ℕ) : MonoidAlgebra ℤ G)} → S.relIndex (evenF J) ≤ (2 ^ (Subgroup.zpowers γ).index) ^ N := by
  intro G _ _ J γ θ N S hJ hJ1 hS hθ hN
  have hdbl : ∀ y, kap J (y + y) ∈ S := fun y => by
    have : kap J (y + y) = 0 := by
      rw [map_add (f := _)]; ext g; simp [CharTwo.add_self_eq_zero]
    rw [this]; exact zero_mem _
  let I : Ideal (MonoidAlgebra ℤ G) :=
    { (S.comap (kap J)).toAddSubmonoid with
      smul_mem' := fun r x hx => by
        change kap J (r * x) ∈ S
        induction r using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => rw [add_mul, map_add (f := _)]; exact add_mem ha hb
        | single g n =>
          have : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • MonoidAlgebra.single g 1 := by simp
          rw [this, smul_mul_assoc, map_zsmul, kap_single_mul hJ]
          exact zsmul_mem (hS _ hx _) _ }
  have hI : ∀ x, x ∈ I ↔ kap J x ∈ S := fun x => Iff.rfl
  have hNI : (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ I := by
    refine Ideal.span_le.2 ?_ hN
    rintro x (rfl | rfl | rfl)
    · exact hθ
    · change kap J _ ∈ S
      have : kap J (1 + MonoidAlgebra.of ℤ G J) = kap J (1 + 1) := by
        ext g
        have h1 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by rw [← map_mul, hJ, map_one]
        have : (1 + MonoidAlgebra.of ℤ G J) * (1 + MonoidAlgebra.of ℤ G J) = (1 + 1) * (1 + MonoidAlgebra.of ℤ G J) := by
          linear_combination h1
        simp only [kap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, this]
      rw [this]; exact hdbl 1
    · change kap J _ ∈ S
      have : ((2 : ℕ) : MonoidAlgebra ℤ G) = 1 + 1 := by norm_num
      rw [this]; exact hdbl 1
  have hidx : S.relIndex (evenF J) = Nat.card (MonoidAlgebra ℤ G ⧸ I) := by
    rw [← kap_range hJ hJ1, ← AddSubgroup.index_comap]
    rfl
  have h2 : ∀ w : MonoidAlgebra ℤ G ⧸ I, 2 • w = 0 := fun w => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [two_nsmul, ← map_add (f := _), Ideal.Quotient.eq_zero_iff_mem]
    exact hdbl x
  haveI hfin : Finite (MonoidAlgebra ℤ G ⧸ I) :=
    (gen2 h2 (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective id
      (fun g => Ideal.Quotient.mk I (MonoidAlgebra.single g 1)) fun _ => rfl).1
  set t : MonoidAlgebra ℤ G ⧸ I := Ideal.Quotient.mk I (MonoidAlgebra.of ℤ G γ - 1) with ht
  let T : AddMonoid.End (MonoidAlgebra ℤ G ⧸ I) := Module.toAddMonoidEnd (MonoidAlgebra ℤ G ⧸ I) (MonoidAlgebra ℤ G ⧸ I) t
  have hT : T ^ N = 0 := by
    have : t ^ N = 0 := by rw [ht, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hNI
    rw [← map_pow, this, map_zero]
  rw [hidx]
  refine (nilCard _ T N hT).trans (Nat.pow_le_pow_left ?_ N)
  let ψ : MonoidAlgebra ℤ G →+ (MonoidAlgebra ℤ G ⧸ I) ⧸ AddMonoidHom.range T :=
    (QuotientAddGroup.mk' _).comp (Ideal.Quotient.mk I).toAddMonoidHom
  have hstep : ∀ g, ψ (MonoidAlgebra.single (γ * g) 1) = ψ (MonoidAlgebra.single g 1) := fun g => by
    rw [← sub_eq_zero, ← map_sub]
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨Ideal.Quotient.mk I (MonoidAlgebra.single g 1), ?_⟩
    change t * _ = Ideal.Quotient.mk I _
    rw [ht, ← map_mul, sub_mul]
    simp [MonoidAlgebra.single_mul_single]
  have hpow : ∀ (n : ℕ) g, ψ (MonoidAlgebra.single (γ ^ n * g) 1) = ψ (MonoidAlgebra.single g 1) := fun n g => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hstep, ih]
  refine (gen2 (Q := G ⧸ Subgroup.zpowers γ) ?_ ψ ?_ QuotientGroup.mk
    (fun q => ψ (MonoidAlgebra.single q.out 1)) ?_).2
  · intro w
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ w
    rw [← map_nsmul, h2, map_zero]
  · exact (QuotientAddGroup.mk'_surjective _).comp Ideal.Quotient.mk_surjective
  · intro g
    obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers γ) g
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hh)
    simp only at e ⊢
    rw [e, mul_comm, hpow]
end
