module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.GaloisValuations.GlobalB
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Neutral.B1
  GlobalTheory.HeckeGal

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tame

variable {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 M)}

theorem normV_mem (v : HeightOneSpectrum (𝓞 M)) : ((normV v : ℕ) : 𝓞 M) ∈ v.asIdeal := by
  have : Finite (𝓞 M ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 M ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 M ⧸ v.asIdeal) : ℕ) : 𝓞 M ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hc


omit [IsAlgClosure M Ω] in
theorem weil_fix_root (h : IsPlaceOver A v) (s : Weil h) (ζ : Ω) (hζ : ζ ^ (normV v - 1) = 1) :
    (s : G M Ω) ζ = ζ := by
  have hq : 1 < normV v := one_lt_normV v
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow (n := normV v - 1) (by omega) (by rw [hζ]; exact isIntegral_one)
  have hζA : A.valuation ζ ≤ 1 := (A.valuation_le_one_iff _).2 (ReciprocityTheory.Gal.mem_of_isIntegral_int A hζi)
  have hζ1 : ζ ^ normV v = ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have hpow : ∀ (y : Ω), y ^ normV v = y → ∀ k : ℕ, y ^ (normV v ^ k) = y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hy]
  have hsζ : ((s : G M Ω) ζ) ^ (normV v - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hsζ1 : ((s : G M Ω) ζ) ^ normV v = (s : G M Ω) ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hsζ, one_mul]
  obtain ⟨a, b, hab⟩ := s.2
  have hc := hab.2 ζ hζA
  rw [hpow _ hsζ1, hpow _ hζ1] at hc
  have hsA : A.valuation ((s : G M Ω) ζ) ≤ 1 := by
    rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hab.1, ← A.valuation_le_one_iff]
    exact hζA
  have hval1 : A.valuation ζ = 1 := by
    refine le_antisymm hζA (not_lt.1 fun hlt => ?_)
    have := pow_lt_one₀ zero_le hlt (show normV v - 1 ≠ 0 by omega)
    rw [← map_pow, hζ, map_one] at this
    exact lt_irrefl _ this
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (h ((normV v : ℕ) : 𝓞 M)).2 (normV_mem v)
    simpa using this
  have hd : ¬ A.valuation (aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X]))) < 1 := by
    have e : aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X])) =
        (((normV v - 1 : ℕ) : Ω)) * ζ ^ (normV v - 1 - 1) := by
      simp [derivative_X_pow]
    rw [e, map_mul, map_pow, hval1, one_pow, mul_one]
    have e2 : (((normV v - 1 : ℕ) : Ω)) = -1 + ((normV v : ℕ) : Ω) := by
      rw [Nat.cast_sub hq.le]; ring
    have h' : A.valuation ((normV v : ℕ) : Ω) < A.valuation (-1 : Ω) := by
      rw [Valuation.map_neg, map_one]; exact hqA
    rw [e2, Valuation.map_add_eq_of_lt_left _ h', Valuation.map_neg, map_one]
    exact lt_irrefl _
  exact (GlobalTheory.eq_of_root_congr_of_deriv_unit A (X ^ (normV v - 1) - 1) ζ ((s : G M Ω) ζ) hζA hsA
    (by simp [hζ]) (by simp [hsζ]) hd (by rw [Valuation.map_sub_swap]; exact hc)).symm

end Tame

end DiscreteGroups.sglob.DzType
end
end

section

noncomputable section

open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord_le (x y : kˣ) :
    valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hx : φ (valuation k (x : k)) ≠ 0 := by simp
  have hy : φ (valuation k (y : k)) ≠ 0 := by simp
  have ho : ∀ z : kˣ, ord k z = -WithZero.log (φ (valuation k (z : k))) := fun _ => rfl
  rw [← φ.strictMono.le_iff_le, ← WithZero.exp_log hx, ← WithZero.exp_log hy, WithZero.exp_le_exp, ho x, ho y]
  omega

theorem ord_inv_eq_neg_ord (x : kˣ) : ord k x⁻¹ = -ord k x := by
  have h := ord_mul k x⁻¹ x
  rw [inv_mul_cancel, ord_eq_zero (k := k) (x := 1) (by simp)] at h
  omega

theorem ord_pow_bis (x : kˣ) (n : ℕ) : ord k (x ^ n) = n * ord k x := by
  induction n with
  | zero => simp [ord_eq_zero]
  | succ n ih => rw [pow_succ, ord_mul, ih]; push_cast; ring

theorem exists_uniformizer_valuation : ∃ t : kˣ, valuation k (t : k) = uniformizer k := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have h0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact absurd ht.symm (by simp)
  exact ⟨Units.mk0 t h0, ht⟩

theorem exists_ball_char_trivial (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ s : kˣ, ∀ y ∈ cball s, ψ y = 1 := by
  have hU : {x : k | ‖(ψ x : ℂ) - 1‖ < 1 / 2} ∈ nhds (0 : k) := by
    have hc : Continuous fun x : k => ‖(ψ x : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp hψ).sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  refine ⟨s, fun y hy => ?_⟩
  have hn : ∀ n : ℕ, n • y ∈ cball s := by
    intro n
    induction n with
    | zero => simp [cball]
    | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hy
  have h := GlobalTheory.CharConductor.eq_one_of_pow_near_one (z := (ψ y : ℂ)) fun n => by
    have := hs (hn n)
    simp only [Set.mem_ofPred_eq, AddChar.map_nsmul_eq_pow] at this
    simpa using this
  exact Circle.ext (by rw [h, Circle.coe_one])

theorem exists_hasConductor_of_continuous_ne_one (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ c : kˣ, HasConductor ψ c := by
  obtain ⟨s, hs⟩ := exists_ball_char_trivial ψ hψ
  obtain ⟨t, ht⟩ := exists_uniformizer_valuation (k := k)
  have hot : ord k t = 1 := ord_eq_one (k := k) ht
  let b : ℕ → kˣ := fun n => s * t⁻¹ ^ n
  have hb : ∀ n : ℕ, ord k (b n) = ord k s - n := fun n => by
    simp only [b]
    rw [ord_mul, ord_pow_bis, ord_inv_eq_neg_ord, hot]
    ring
  have hex : ∃ n : ℕ, ¬ ∀ y : k, valuation k y ≤ valuation k (b n : k) → ψ y = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hψ1 (by ext x; rw [h x, AddChar.one_apply])
    have hx0 : x ≠ 0 := by rintro rfl; exact hx (AddChar.map_zero_eq_one ψ)
    refine ⟨(ord k s - ord k (Units.mk0 x hx0)).toNat, fun h => hx (h x ?_)⟩
    have := (valuation_le_iff_ord_le (Units.mk0 x hx0) (b (ord k s - ord k (Units.mk0 x hx0)).toNat)).2
      (by rw [hb]; omega)
    simpa using this
  classical
  set N := Nat.find hex with hNdef
  have hN : ¬ ∀ y : k, valuation k y ≤ valuation k (b N : k) → ψ y = 1 := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0
    apply hN
    intro y hy
    rw [h0] at hy
    exact hs y (by simpa [b, cball] using hy)
  have hP : ∀ y : k, valuation k y ≤ valuation k (b (N - 1) : k) → ψ y = 1 :=
    Classical.not_not.1 (Nat.find_min hex (show N - 1 < Nat.find hex by omega))
  refine ⟨b (N - 1), fun x => ⟨fun h => ?_, fun h y hy => hP y (hy.trans h)⟩⟩
  by_contra hlt
  apply hN
  intro y hy
  apply h y
  refine hy.trans ?_
  have hx0 : x ≠ 0 := by rintro rfl; exact hlt (by simp)
  have h2 : ¬ ord k (b (N - 1)) ≤ ord k (Units.mk0 x hx0) := fun h3 =>
    hlt (by simpa using (valuation_le_iff_ord_le (Units.mk0 x hx0) (b (N - 1))).2 h3)
  have e1 := hb N
  have e2 := hb (N - 1)
  have := (valuation_le_iff_ord_le (b N) (Units.mk0 x hx0)).2 (by omega)
  simpa using this


theorem residue_eq_iff_valuation_lt (a b : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] a = IsLocalRing.residue 𝒪[k] b ↔ valuation k ((a : k) - b) < 1 := by
  have hv := Valuation.integer.integers (valuation k)
  have h1 : valuation k (((a - b : 𝒪[k])) : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (a - b).2
  have e : ∀ x : 𝒪[k], algebraMap 𝒪[k] k x = (x : k) := fun _ => rfl
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one, e]
  push_cast at h1 ⊢
  exact ⟨fun h => lt_of_le_of_ne h1 h, fun h => h.ne⟩


end DiscreteGroups.sglob.DzType
end
end

section

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

def InH (j : ℕ) (g : GL (Fin (m + 1)) k) : Prop :=
  ∀ p q : Fin (m + 1), ¬ (p.val < j ∧ q.val < j) →
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def colM (c : Fin (m + 1)) (x : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  1 + Matrix.of fun p q => if q = c ∧ p < c then x p else 0

theorem colM_zero (c : Fin (m + 1)) : colM c (0 : Fin (m + 1) → k) = 1 := by
  ext p q; simp [colM]

theorem colM_mul (c : Fin (m + 1)) (x y : Fin (m + 1) → k) : colM c x * colM c y = colM c (x + y) := by
  have hAB : (Matrix.of fun p q => if q = c ∧ p < c then x p else 0) *
      (Matrix.of fun p q => if q = c ∧ p < c then y p else (0 : k)) = 0 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = c
    · subst hr; simp
    · simp [hr]
  simp only [colM, add_mul, mul_add, one_mul, mul_one, hAB, add_zero]
  ext p q
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

def U (c : Fin (m + 1)) (x : Fin (m + 1) → k) : GL (Fin (m + 1)) k :=
  ⟨colM c x, colM c (-x), by rw [colM_mul, add_neg_cancel, colM_zero],
    by rw [colM_mul, neg_add_cancel, colM_zero]⟩

theorem U_add (c : Fin (m + 1)) (x y : Fin (m + 1) → k) : U c (x + y) = U c x * U c y :=
  Units.ext (colM_mul c x y).symm

theorem U_mem (c : Fin (m + 1)) (x : Fin (m + 1) → k) : U c x ∈ unipB k (Fin (m + 1)) := by
  refine (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · show colM c x i j = 0
    simp only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h⟩; exact absurd (h.trans hji) (lt_irrefl _)
  · show colM c x i i = 1
    simp only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h⟩; exact lt_irrefl _ h

theorem superDiag_U (j : ℕ) (hj : j + 1 < m + 1) (x : Fin (m + 1) → k) :
    superDiag (U ⟨j + 1, hj⟩ x) = x ⟨j, by omega⟩ := by
  unfold superDiag
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (m + 1))]
  · rw [Finset.sum_eq_single (⟨j + 1, hj⟩ : Fin (m + 1))]
    · show colM _ x _ _ = _
      simp [colM, Fin.ext_iff]
    · intro b hb hne
      exact absurd (Fin.ext (by simpa using (Finset.mem_filter.1 hb).2)) hne
    · intro h; exact absurd (by simp) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' : q.val = b.val + 1 := (Finset.mem_filter.1 hq).2
    show colM _ x _ _ = 0
    simp only [colM, Matrix.add_apply, Matrix.of_apply]
    rw [Matrix.one_apply_ne (fun h => by rw [h] at hq'; omega), if_neg, add_zero]
    rintro ⟨rfl, -⟩
    exact hb (Fin.ext (by simp at hq' ⊢; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem InH_zero (g : GL (Fin (m + 1)) k) (hg : InH 0 g) : g = 1 :=
  Units.ext (Matrix.ext fun p q => hg p q (by simp))

end DiscreteGroups.sglob.LConvKir
end
end
