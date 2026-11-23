module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PrimeEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForFrobeniusFieldsBundle004 (Ω : Type) [Field Ω] [CharZero Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem odd_pow_ne {k : Type} [Field k] {x : k} {n : ℕ} (hn : x ^ 2 ^ n = 1) (h4 : x ^ 4 ≠ 1) {m : ℤ} (hm : Odd m) :
    x ^ m ≠ 1 := by
  intro hxm
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hn
  set u := Units.mk0 x hx0 with hu_def
  have hu : u ^ 2 ^ n = 1 := Units.ext (by simpa [u] using hn)
  have hum : u ^ m = 1 := Units.ext (by simpa [u] using hxm)
  obtain ⟨j, -, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu)
  have hdm : (orderOf u : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hum
  cases j with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff] at hoj
    apply h4
    have hx1 : x = 1 := by simpa [u] using congrArg Units.val hoj
    simp [hx1]
  | succ j =>
    have h2 : (2 : ℤ) ∣ m := by
      refine dvd_trans ?_ hdm
      rw [hoj]
      exact_mod_cast dvd_pow_self 2 (Nat.succ_ne_zero j)
    exact (Int.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

private theorem dist4 {k : Type} [Field k] {x : k} (h1 : (-1 : k) ≠ 1) (h0 : x ≠ 0) (hx : x ^ 2 ≠ 1) :
    Function.Injective (![x * -1, -1, x, 1] : Fin 4 → k) := by
  have h2 : (2 : k) ≠ 0 := by
    intro h
    apply h1
    linear_combination -h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢
  all_goals first
    | exact absurd (by linear_combination h * h) hx
    | exact absurd (by linear_combination (-x - 1) * h) hx
    | exact absurd (by linear_combination (x - 1) * h) hx
    | exact absurd (by linear_combination (-x + 1) * h) hx
    | exact absurd (by linear_combination (x + 1) * h) hx
    | exact h1 h
    | exact h1 h.symm
    | exact h0 ((mul_eq_zero.mp (by linear_combination -h : (2 : k) * x = 0)).resolve_left h2)
    | exact h0 ((mul_eq_zero.mp (by linear_combination h : (2 : k) * x = 0)).resolve_left h2)

private theorem lab_inj (pr : Bool) : Function.Injective (lab pr) := by
  cases pr <;> decide

private theorem lab_surj (pr : Bool) : ∃ i, lab pr i = 3 := by
  cases pr <;> decide

theorem UpperTheory.V.Ws.ok2A :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ a u t, X.Elts a u t → (∀ w, ∃ g ∈ T.GalL, T.rb w g ≠ Raw.bar D.om (resQ T.F g)) ∧ (∀ w ∈ roots, ∃ g ∈ T.GalL, T.rb w g ≠ 1) ∧ (∀ η : T.GalL →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (∀ g : T.GalL, D.om (resQ T.F g) = 1 → η g = 1) → (∀ i, ∃ j, ∀ g : T.GalL, η g * Raw.bar (chi D T.pr i) (resQ T.F g) = Raw.bar (chi D T.pr j) (resQ T.F g)) → η = 1) ∧ (∃ w ∈ roots, ∀ n : ℕ, 0 < n → n ≤ 4 → ∃ g ∈ T.GalL, T.rb w g ^ n ≠ 1) ∧ (resQ T.F T.g0 = t → ∀ i j, i ≠ j → Raw.bar (chi D T.pr i) (resQ T.F T.g0) ≠ Raw.bar (chi D T.pr j) (resQ T.F T.g0)) := by
  intro Ω _ _ _ l _ c D hD X T hOn a u t hE
  obtain ⟨h1, -, hal, hth, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨n, hn⟩ := X.ord
  have hxord : ∀ g, Raw.bar D.ξ g ^ 2 ^ n = 1 := by
    intro g
    simp only [Raw.bar]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hn]
    simp
  have hchi : ∀ b i, chi D b i = D.ps (lab b i) := fun b i => rfl
  have lift : ∀ y ∈ X.H ⊓ X.η.ker, ∃ s ∈ T.GalL, resQ T.F s = y := by
    intro y hy
    obtain ⟨s, hs⟩ := exists_resQ (F := T.F) (g := y) (by rw [hOn.1]; exact hy.1)
    refine ⟨s, ?_, hs⟩
    unfold Tower.GalL
    rw [Subgroup.mem_comap, hOn.2, hs]
    exact hy.2
  have hbu : Raw.bar D.om u = 1 := by simp [Raw.bar, hE.u_om]
  have hxu1 : Raw.bar D.ξ u ≠ 1 := by
    intro h
    apply hE.u_xi
    rw [h, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rcases Int.even_or_odd w.1 with he | ho
    · obtain ⟨s, hsG, hs⟩ := lift a hE.a_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.a_xi, hE.a_psi, hE.a_om, one_zpow, mul_one, he.neg_one_zpow]
      exact fun h => h1 h.symm
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one, hbu]
      exact odd_pow_ne (hxord u) hE.u_xi ho
  · intro w hw
    by_cases ho : Odd w.1
    · obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.u_psi, one_zpow, mul_one]
      exact odd_pow_ne (hxord u) hE.u_xi ho
    · obtain ⟨w1, w2⟩ := w
      simp [UpperTheory.V.Ws.roots, oddRoots, wAl, wBe, wTh, wPs] at hw
      obtain ⟨s, hsG, hs⟩ := lift t hE.t_mem
      refine ⟨s, hsG, ?_⟩
      rw [hrb, hs, hE.t_psi]
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact absurd (by decide) ho
        | (split_ifs <;> simpa using h1)
  · intro η hη2 hηom hperm
    obtain ⟨i0, hi0⟩ := lab_surj T.pr
    obtain ⟨j, hj⟩ := hperm i0
    have key : ∀ s : T.GalL, (η s : ResidueField c.O) = Raw.bar (D.ps (lab T.pr j)) (resQ T.F s) := by
      intro s
      have h := hj s
      rw [hchi, hchi, hi0] at h
      have h3 : D.ps 3 = 1 := rfl
      rw [h3] at h
      simpa [Raw.bar] using h
    obtain ⟨su, hsuG, hsu⟩ := lift u hE.u_mem
    obtain ⟨st, hstG, hst⟩ := lift t hE.t_mem
    have hηu : η ⟨su, hsuG⟩ = 1 := hηom _ (by simp only [hsu]; exact hE.u_om)
    have hηt : η ⟨st, hstG⟩ = 1 := hηom _ (by simp only [hst]; exact hE.t_om)
    have ku := key ⟨su, hsuG⟩
    have kt := key ⟨st, hstG⟩
    rw [hηu] at ku
    rw [hηt] at kt
    simp only [hsu] at ku
    simp only [hst] at kt
    generalize lab T.pr j = k at ku kt key
    fin_cases k
    · exfalso
      change _ = Raw.bar D.th u at ku
      simp only [hth, hE.u_psi, mul_one, Units.val_one] at ku
      exact hxu1 ku.symm
    · exfalso
      change _ = Raw.bar D.Psi t at kt
      simp only [hE.t_psi, Units.val_one] at kt
      exact h1 kt.symm
    · exfalso
      change _ = Raw.bar D.al u at ku
      simp only [hal, Units.val_one] at ku
      exact hxu1 ku.symm
    · ext s
      have h0 : D.ps 3 = 1 := rfl
      have := key s
      simp only [Fin.reduceFinMk, Fin.isValue] at this
      rw [h0] at this
      simpa [Raw.bar] using this
  · refine ⟨(1, 0), by simp [UpperTheory.V.Ws.roots, oddRoots, wAl], fun m hm0 hm4 => ?_⟩
    obtain ⟨s, hsG, hs⟩ := lift u hE.u_mem
    refine ⟨s, hsG, ?_⟩
    rw [hrb, hs, hE.u_psi]
    simp only [one_zpow, mul_one, zpow_one]
    interval_cases m
    · simpa using hxu1
    · intro h
      apply hE.u_xi
      rw [show 4 = 2 * 2 by rfl, pow_mul, h, one_pow]
    · have h3 := odd_pow_ne (hxord u) hE.u_xi (m := 3) (by decide)
      simpa using h3
    · exact hE.u_xi
  · intro hg0 i j hij heq
    rw [hg0] at heq
    have hx0 : Raw.bar D.ξ t ≠ 0 := by
      intro h0
      have h := hxord t
      rw [h0, zero_pow (by positivity)] at h
      exact zero_ne_one h
    have hinj := dist4 h1 hx0 hE.t_xi
    have hvals : ∀ k, Raw.bar (D.ps k) t = ![Raw.bar D.ξ t * -1, -1, Raw.bar D.ξ t, 1] k := by
      intro k
      fin_cases k
      · show Raw.bar D.th t = _
        simp [hth, hE.t_psi]
      · show Raw.bar D.Psi t = _
        simp [hE.t_psi]
      · show Raw.bar D.al t = _
        simp [hal]
      · show Raw.bar (1 : G ℚ Ω →* (↥c.O)ˣ) t = _
        simp [Raw.bar]
    rw [hchi, hchi, hvals, hvals] at heq
    exact hij (lab_inj T.pr (hinj heq))
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem quadEx_jac (p q : ℕ) (s : ℤˣ) (hq : q.Prime) (h8 : (p : ℤ) ≡ s [ZMOD 8]) (hpq : (p : ℤ) ≡ s [ZMOD q]) :
    jacobiSym q p = 1 := by
  have hp : Odd p := by
    rw [Nat.odd_iff]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 <;> omega
  rcases hq.eq_two_or_odd' with rfl | hq2
  · rw [Nat.cast_ofNat, jacobiSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8
    · rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e : jacobiSym p q = jacobiSym s q := jacobiSym.mod_left' hpq
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 e
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hq2 (by omega), e, jacobiSym.one_left]
    · have hq' := Nat.odd_iff.1 hq2
      rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four h hp, e, jacobiSym.at_neg_one hq2, ZMod.χ₄_nat_one_mod_four h]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four h (by omega), e, jacobiSym.at_neg_one hq2,
          ZMod.χ₄_nat_three_mod_four h, neg_neg]

private theorem quadEx_prime (s : ℤˣ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ∉ S ∧ p ≠ 2 ∧ quadraticChar (ZMod p) (-1) = s ∧
      ∀ q ∈ S, quadraticChar (ZMod p) (q : ZMod p) = 1 := by
  have h0 : 8 * ∏ q ∈ S, q ≠ 0 := mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.2 fun q hq => (hS q hq).ne_zero)
  have hc : IsCoprime (s : ℤ) ((8 * ∏ q ∈ S, q : ℕ) : ℤ) := ⟨(s⁻¹ : ℤˣ), 0, by simp⟩
  obtain ⟨p, hpn, hp, hps⟩ := Nat.forall_exists_prime_gt_and_zmodEq (S.sup id) h0 hc
  have h8 : (p : ℤ) ≡ s [ZMOD 8] := hps.of_dvd (by exact_mod_cast Int.natCast_dvd_natCast.2 (dvd_mul_right 8 _))
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : p ≠ 2 := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 <;> omega
  refine ⟨p, inferInstance, fun h => absurd (Finset.le_sup (f := id) h) (not_le.2 hpn), h2, ?_, fun q hq => ?_⟩
  · have e := legendreSym.at_neg_one h2
    rw [legendreSym, Int.cast_neg, Int.cast_one] at e
    rw [e]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 ⊢
    · exact ZMod.χ₄_nat_one_mod_four (by omega)
    · exact ZMod.χ₄_nat_three_mod_four (by omega)
  · have e := quadEx_jac p q s (hS q hq) h8
      (hps.of_dvd (Int.natCast_dvd_natCast.2 ((Finset.dvd_prod_of_mem _ hq).mul_left 8)))
    rwa [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast] at e

private theorem quadEx_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p q : ℕ) [hp : Fact p.Prime] (γ : G ℚ Ω)
    (h : ((cycZ ℚ Ω p γ : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p])) (u : (ZMod p)ˣ) (hu : (u : ZMod p) = q) : UpperTheory.V.Chr.cls ℚ Ω p γ = u := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  refine (UpperTheory.V.Chr.clsFacts ℚ Ω p).2.2.1 γ u fun ζ hζ => ?_
  have hζ' : ζ ^ p ^ 1 = 1 := by rwa [pow_one]
  have h1 := cyclotomicCharacter.spec p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) ζ hζ'
  have h2 : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p]) := h
  rw [h2, map_natCast, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ'] at h1
  rw [hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  exact h1

private theorem quadEx_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hq : A.valuation (q : Ω) < 1) : ¬ A.valuation (p : Ω) < 1 := fun hp => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hv : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv a)) hp
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv b)) hq
  have h2 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

theorem UpperTheory.V.Ws.quadEx :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (s : ℤˣ) (S : Finset ℕ), (∀ q ∈ S, q.Prime) → ∃ (p : ℕ) (η : G ℚ Ω →* ℤˣ), QuadAt p s S η := by
  intro Ω _ _ _ s S hS
  obtain ⟨p, hp, hpS, h2, hs, hq⟩ := quadEx_prime s S hS
  obtain ⟨hopen, -, -, hcc, hine⟩ := Chr.clsFacts ℚ Ω p
  let χ : DirichletCharacter ℤ p := quadraticChar (ZMod p)
  have hval : ∀ g : G ℚ Ω, ((Chr.dirG ℚ Ω χ g : ℤˣ) : ℤ) = quadraticChar (ZMod p) (Chr.cls ℚ Ω p g : (ZMod p)ˣ) := fun g => rfl
  have hle : (Chr.cls ℚ Ω p).ker ≤ (Chr.dirG ℚ Ω χ).ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hg, map_one]
  have hopn : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hle hopen
  obtain ⟨u, hu⟩ : ∃ u : (ZMod p)ˣ, quadraticChar (ZMod p) u = -1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    have h0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact ⟨Units.mk0 a h0, ha⟩
  refine ⟨p, Chr.dirG ℚ Ω χ, hp.out, hpS, hopn, ?_, fun A hA => (hine A hA).trans hle, fun A hA => ?_, fun σ hσ => ?_,
    fun q hqS A hA => ?_⟩
  · obtain ⟨g, hg⟩ := (Chr.clsOnto Ω p).1 u
    have ht : (Chr.dirG ℚ Ω χ).range = ⊤ := by
      refine eq_top_iff.2 fun t _ => ?_
      rcases Int.units_eq_one_or t with rfl | rfl
      · exact one_mem _
      · exact ⟨g, Units.ext (by rw [hval, hg, hu]; rfl)⟩
    rw [Subgroup.index_ker, ht, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  · have hm : u ∈ (proj p p).range := by
      rw [(projFacts p p hp.out).2.2.2.2.2.1, MonoidHom.mem_ker]
      have h1 : ordCompl[p] p = 1 := by
        rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
      have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [h1]; infer_instance
      exact Units.ext (Subsingleton.elim _ _)
    rw [← (compIne Ω p p hp.out A hA).1] at hm
    obtain ⟨g, hg, hgu⟩ := hm
    exact ⟨g, hg, Units.ext (by rw [hval, hgu, hu]; rfl)⟩
  · exact Units.ext (by rw [hval, hcc σ hσ, Units.val_neg, Units.val_one, hs])
  · have hne : p ≠ q := fun h => hpS (h ▸ hqS)
    have hc : p.Coprime q := (Nat.coprime_primes hp.out (hS q hqS)).2 hne
    obtain ⟨-, -, γ, -, hD, hγ⟩ := Chr.decCyc Ω q A (hS q hqS) hA
    refine hD.trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ((hine A (quadEx_val A hc hA)).trans hle))
      (Subgroup.isClosed_of_isOpen _ hopn))
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hval, quadEx_cls p q γ (hγ p hne) (ZMod.unitOfCoprime q hc.symm) rfl, ZMod.coe_unitOfCoprime, hq q hqS, Units.val_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]

private theorem kx_cls (n : ℕ) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) : Chr.cls ℚ Ω (l ^ n) s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  refine (Chr.clsFacts ℚ Ω (l ^ n)).2.2.1 s _ fun ζ hζ => ?_
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) ζ hζ
  have h2 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) = 1 := h
  rw [h2, Units.val_one, map_one] at h1
  exact h1

variable {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N]

private theorem kx_kapL (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) :
    kapL l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
  haveI : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have h3 : proj l N (Chr.cls ℚ Ω N s) = 1 := by
    rw [← MonoidHom.mem_ker, (projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      (Chr.clsFacts ℚ Ω N).2.1]
    exact kx_cls _ h
  have h4 : (kapL l ψ).toUnitHom (Chr.cls ℚ Ω N s) = 1 := by rw [kapL, (compAlg O N l hl.out).1, h3, map_one]
  exact congrArg Units.val h4

private theorem kx_pow (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hk : Chr.dirG ℚ Ω (kapB l ψ) s = 1) : Chr.dirG ℚ Ω ψ s ^ orderOf (th0 l ψ) = 1 := by
  ext1
  show ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  have a1 : kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hk
  have a3 : ψ = th0 l ψ * (kapB l ψ * kapL l ψ) := by rw [kapB, inv_mul_cancel_right, dirichletPrimeToLPart_mul_lPowerPart]
  have a4 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = th0 l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) := by
    conv_lhs => rw [a3]
    rw [MulChar.mul_apply, MulChar.mul_apply, a1, kx_kapL ψ h, one_mul, mul_one]
  rw [a4, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem kx_unr (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hψ : Chr.dirG ℚ Ω ψ s = 1) : Chr.dirG ℚ Ω (kapB l ψ) s = 1 := by
  ext1
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1
  have a1 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hψ
  have a2 : kap l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [kap, lPart, MulChar.pow_apply_coe, a1, one_pow]
  have a3 : kap l ψ = kapB l ψ * kapL l ψ := by rw [kapB, inv_mul_cancel_right]
  rwa [a3, MulChar.mul_apply, kx_kapL ψ h, mul_one] at a2

private theorem kx_ord (ψ : DirichletCharacter O N) :
    Chr.dirG ℚ Ω (kapB l ψ) ^ l ^ (orderOf ψ).factorization l = 1 := by
  have h1 : kap l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [← (partOrd _ l hl.out ψ ψ.orderOf_pos).1]
    exact pow_orderOf_eq_one _
  obtain ⟨-, -, hone, -, hpow, -⟩ := compAlg O N l hl.out
  have h2 : kapB l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [kapB, kapL, mul_pow, inv_pow, ← hpow, h1, hone, inv_one, one_mul]
  refine MonoidHom.ext fun s => Units.ext ?_
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.kapEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N), D.ψ = Chr.dirG ℚ Ω ψ → ∃ κ, Kap D κ := by
  intro Ω _ _ _ l hl c D hD N _ ψ hψ
  have hnd : ¬ l ∣ orderOf (th0 l ψ) := (partOrd _ l hl.out ψ ψ.orderOf_pos).2.2.1
  refine ⟨Chr.dirG ℚ Ω (kapB l ψ), ?_, ⟨_, kx_ord ψ⟩, fun A hA g hg => ?_, fun A hA => ?_, fun A hA g hg hb hk => ?_,
    orderOf (th0 l ψ), (Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd, fun g hg hk => hψ ▸ kx_pow ψ hg hk⟩
  · refine Subgroup.isOpen_mono (fun s hs => ?_) (Chr.clsFacts ℚ Ω N).1
    rw [MonoidHom.mem_ker] at hs ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hs, map_one]
  · exact kx_unr ψ ((places ℚ Ω l A).2.2.2 (hA l hD.l_mem) hg) (hψ ▸ hD.psi_unr A hA hg)
  · refine ((compIne Ω N l hl.out A hA).2 c.O _).2.2 ?_
    obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O N l hl.out
    rw [kapB, kapL, hmul, hinv, (h6 _).1, mul_inv_cancel]
  · have h1 : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 (hA l (Finset.mem_singleton_self l)) hg
    have h2 : chiO ℚ Ω l c.O g = 1 := by rw [chiO, MonoidHom.comp_apply, h1, map_one]
    have h3 : D.Psi g = D.ψ g := by
      rw [Raw.Psi, Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, h2, one_pow, one_mul]
    refine (congrFacts Ω l c).2.2.2.1 _ 1 _ hnd (hψ ▸ kx_pow ψ h1 hk) (one_pow _) ?_
    rw [← residue_eq_zero_iff, map_sub, Units.val_one, map_one, sub_eq_zero, ← h3]
    exact hb
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.ok2B :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → (∀ A : ValuationSubring Ω, Ine (F := T.F) A ≤ T.GalL) ∧ (∀ A : ValuationSubring Ω, Raw.Away {l} A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 → D.ψ (resQ T.F g) = 1) ∧ (∃ m : ℕ, l.Coprime m ∧ ∀ g : G T.F Ω, cycZ T.F Ω l g = 1 → D.ψ (resQ T.F g) ^ m = 1) ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 := by
  intro Ω _ _ _ l hl c D hD X T hT
  obtain ⟨hpq, -, hxi, -, -⟩ := away D hD
  obtain ⟨-, -, -, -, -, hrb, -, -, -⟩ := barFacts D hD
  have hH : ∀ g : G T.F Ω, resQ T.F g ∈ X.H := fun g => hT.1 ▸ resQ_mem T.F g
  refine ⟨fun A g hg => ?_, fun A hA g hg h => ?_, ?_, fun A hA g hg => ?_⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    change resQ T.F g ∈ T.K.fixingSubgroup
    rw [hT.2]
    by_cases hp : A.valuation (X.p : Ω) < 1
    · have hp' : ¬ A.valuation (X.p' : Ω) < 1 := fun h =>
        X.hη'.nm (hpq A _ _ X.hη.prime X.hη'.prime hp h ▸ Finset.mem_insert_self _ _)
      exact (X.mem_H.1 (hH g)).2.1.trans (X.hη'.unr A hp' hg')
    · exact X.hη.unr A hp hg'
  · exact X.kap.kb A hA _ ((resQ_Ine T.F A g).1 hg) ((hrb _).1 h).2 (X.mem_H.1 (hH g)).2.2
  · obtain ⟨m, hm, h⟩ := X.kap.kc
    exact ⟨m, hm, fun g hg => h _ ((resQ_cyc T.F g).trans hg) (X.mem_H.1 (hH g)).2.2⟩
  · have hg' := (resQ_Ine T.F A g).1 hg
    have h3 : ¬ A.valuation (X.p₃ : Ω) < 1 := fun h =>
      X.hφ.nm (hpq A _ _ hl.out X.hφ.prime hA h ▸ hD.l_mem)
    have h1 : D.ξ (resQ T.F g) = 1 := hxi A hA hg'
    have h2 : X.φ (resQ T.F g) = 1 := X.hφ.unr A h3 hg'
    refine (hrb _).2 ⟨?_, ?_⟩
    · rw [Raw.bar, h1, Units.val_one, map_one]
    · rw [(X.mem_H.1 (hH g)).1, h2, Units.val_one, Int.cast_one]
end
