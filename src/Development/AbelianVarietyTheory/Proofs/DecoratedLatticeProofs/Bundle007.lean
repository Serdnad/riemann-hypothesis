module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
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

open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory

theorem adicCompletion_valuation_map_uniformiser : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  intro F _ _ v k _ _ _ _ φ hφ ϖ hϖ

  have hnu : ∀ c : 𝒪[k], Valued.v (φ (c : k)) < 1 → ¬ IsUnit c := by
    intro c hc hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : φ (c : k) * φ (w : k) = 1 := by
      rw [← map_mul, ← map_one φ]
      congr 1
      exact_mod_cast congrArg (fun t : 𝒪[k] => (t : k)) hw
    have h1 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) = 1 := by
      rw [← map_mul, hw', map_one]
    have h2 : Valued.v (φ (w : k)) ≤ 1 := (hφ _).2 w.2
    have h3 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) ≤ Valued.v (φ (c : k)) * 1 :=
      by gcongr
    rw [h1, mul_one] at h3
    exact absurd hc (not_lt.2 h3)
  set x := φ (ϖ : k) with hxdef
  have hϖ0 : (ϖ : k) ≠ 0 := by
    intro h; exact hϖ.ne_zero (Subtype.ext h)
  have hx0 : x ≠ 0 := by
    simpa [hxdef] using hϖ0
  have hvx0 : Valued.v x ≠ 0 := by
    simpa using hx0
  have hvx1 : Valued.v x < 1 := by
    have hle : Valued.v x ≤ 1 := (hφ _).2 ϖ.2
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hϖ.not_isUnit
    have hinv : ((ϖ : k))⁻¹ ∈ 𝒪[k] := by
      refine (hφ _).1 ?_
      rw [map_inv₀, map_inv₀, ← hxdef, heq, inv_one]
    refine IsUnit.of_mul_eq_one (b := (⟨_, hinv⟩ : 𝒪[k])) ?_
    apply Subtype.ext
    simp [mul_inv_cancel₀ hϖ0]
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have hlt1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    norm_num
  have hvπ0 : Valued.v π₀ ≠ 0 := by rw [hπ₀]; exact WithZero.coe_ne_zero
  have hπ0 : π₀ ≠ 0 := by
    intro h; apply hvπ0; rw [h, map_zero]
  set a := φ.symm π₀ with hadef
  have hφa : φ a = π₀ := by simp [hadef]
  have ha0 : a ≠ 0 := by
    intro h; apply hπ0; rw [← hφa, h, map_zero]
  have ha : a ∈ 𝒪[k] := (hφ a).1 (by rw [hφa, hπ₀]; exact hlt1.le)
  apply le_antisymm
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 hvx0
    rw [← hm] at hvx1 ⊢
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hvx1
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := hvx1
    show Multiplicative.toAdd m ≤ -1
    omega
  · by_contra hcon
    rw [not_le] at hcon
    set b := (ϖ : k) / a with hbdef
    have hφb : Valued.v (φ b) < 1 := by
      rw [hbdef, map_div₀, hφa, map_div₀, ← hxdef, div_lt_one₀ (pos_iff_ne_zero.2 hvπ0), hπ₀]
      exact hcon
    have hb : b ∈ 𝒪[k] := (hφ b).1 hφb.le
    have hprod : ϖ = (⟨a, ha⟩ : 𝒪[k]) * ⟨b, hb⟩ := by
      apply Subtype.ext
      show (ϖ : k) = a * ((ϖ : k) / a)
      rw [mul_div_cancel₀ _ ha0]
    rcases hϖ.isUnit_or_isUnit hprod with h | h
    · exact hnu ⟨a, ha⟩ (by rw [hφa, hπ₀]; exact hlt1) h
    · exact hnu ⟨b, hb⟩ hφb h

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.AdeleIdempotents

open IsDedekindDomain NumberField

def finiteComponent (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    AdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun x := x.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def infiniteComponent (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    AdeleRing (𝓞 F) F →+* w.Completion where
  toFun x := x.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_orthogonal_idempotents_of_sum_mul_eq_one (F : Type) [Field F] [NumberField F]
    (ι : Type) [Fintype ι] (f s : ι → AdeleRing (𝓞 F) F) (h : ∑ i, s i * f i = 1) :
    ∃ e t : ι → AdeleRing (𝓞 F) F, ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧
      ∀ i, t i * f i = e i := by
  classical
  have hinf : ∀ w : InfinitePlace F, ∃ i, (s i).1 w * (f i).1 w ≠ 0 := by
    intro w
    have h1 : ∑ i, (s i).1 w * (f i).1 w = 1 := by
      have := congrArg (infiniteComponent F w) h

      rw [map_sum, map_one] at this
      exact this
    by_contra hc
    push_neg at hc
    rw [Finset.sum_eq_zero (fun i _ => hc i)] at h1
    exact zero_ne_one h1
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ i, 1 ≤ Valued.v ((s i).2 v * (f i).2 v) := by
    intro v
    have h1 : ∑ i, (s i).2 v * (f i).2 v = 1 := by
      have := congrArg (finiteComponent F v) h

      rw [map_sum, map_one] at this
      exact this
    by_contra hc
    push_neg at hc
    have := Valuation.map_sum_lt (Valued.v) (s := Finset.univ) (g := 1) one_ne_zero
      (fun i _ => hc i)
    rw [h1, map_one] at this
    exact lt_irrefl _ this
  choose a ha using hinf
  choose b hb using hfin
  have hfv : ∀ v, (f (b v)).2 v ≠ 0 := by
    intro v h0
    have := hb v
    rw [h0, mul_zero, map_zero] at this
    exact absurd this (by simp)
  refine ⟨fun i => (fun w => if a w = i then 1 else 0,
      ⟨fun v => if b v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
        dsimp only
        split_ifs
        · exact one_mem _
        · exact zero_mem _⟩),
    fun i => (fun w => if a w = i then ((f i).1 w)⁻¹ else 0,
      ⟨fun v => if b v = i then ((f i).2 v)⁻¹ else 0, (s i).2.2.mono fun v hv => by
        dsimp only
        split_ifs with hbi
        · subst hbi
          have hv' : Valued.v ((s (b v)).2 v) ≤ 1 := hv
          change Valued.v ((f (b v)).2 v)⁻¹ ≤ 1
          refine le_trans ?_ hv'
          calc Valued.v ((f (b v)).2 v)⁻¹ = Valued.v ((f (b v)).2 v)⁻¹ * 1 := (mul_one _).symm
            _ ≤ Valued.v ((f (b v)).2 v)⁻¹ * Valued.v ((s (b v)).2 v * (f (b v)).2 v) :=
              mul_le_mul' le_rfl (hb v)
            _ = Valued.v ((s (b v)).2 v) := by
              rw [← map_mul, mul_comm ((s (b v)).2 v), ← mul_assoc, inv_mul_cancel₀ (hfv v),
                one_mul]
        · exact zero_mem _⟩), ?_, ?_, ?_⟩
  · refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · refine (map_sum (infiniteComponent F w) _ _).trans ?_
      change ∑ i, (if a w = i then (1 : w.Completion) else 0) = 1
      simp
    · refine (map_sum (finiteComponent F v) _ _).trans ?_
      change ∑ i, (if b v = i then (1 : v.adicCompletion F) else 0) = 1
      simp
  · intro i j hij
    refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · change (if a w = i then (1 : w.Completion) else 0) * (if a w = j then 1 else 0) = 0
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij
      all_goals simp
    · change (if b v = i then (1 : v.adicCompletion F) else 0) * (if b v = j then 1 else 0) = 0
      split_ifs with h1 h2
      · exact absurd (h1.symm.trans h2) hij
      all_goals simp
  · intro i
    refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
    · change (if a w = i then ((f i).1 w)⁻¹ else 0) * (f i).1 w = (if a w = i then 1 else 0)
      split_ifs with h1
      · subst h1
        exact inv_mul_cancel₀ (right_ne_zero_of_mul (ha w))
      · simp
    · change (if b v = i then ((f i).2 v)⁻¹ else 0) * (f i).2 v = (if b v = i then 1 else 0)
      split_ifs with h1
      · subst h1
        exact inv_mul_cancel₀ (hfv v)
      · simp

end GlobalTheory.AdeleIdempotents
end
end
