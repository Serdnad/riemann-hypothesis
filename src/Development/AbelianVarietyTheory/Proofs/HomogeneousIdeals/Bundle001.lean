module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Star.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.RootNormBound

open Polynomial

theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 ≤ ε) (s : Multiset ℂ)
    (hs : ∀ t ∈ s, ε ≤ ‖t‖) :
    ε ^ Multiset.card s ≤ ‖(s.map (fun a => (0 : ℂ) - a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_comm]
    have ha : ε ≤ ‖(0 : ℂ) - a‖ := by
      rw [zero_sub, norm_neg]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hε _)
      (norm_nonneg _)

theorem exists_root_norm_lt {h : Polynomial ℂ} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t : ℂ, h.IsRoot t ∧ ‖t‖ < ε := by
  by_contra hne
  push Not at hne
  have hsp : h.Splits := IsAlgClosed.splits h
  have hne0 : h ≠ 0 := hm.ne_zero
  have key := pow_card_le_norm_prod hε h.roots fun t ht => hne t ((mem_roots hne0).1 ht)
  rw [← hsp.eval_eq_prod_roots_of_monic hm 0, ← coeff_zero_eq_eval_zero,
    ← hsp.natDegree_eq_card_roots] at key
  exact absurd hc (not_lt.2 key)

end GlobalTheory.RootNormBound
end

section

namespace GlobalTheory

namespace QuadRefinement

section Additive

variable {O Y M : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y]
  [AddCommGroup M]

variable {τ : Y →+ Y →+ M} {w : O}

end Additive

section Multiplicative

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]

def mulRefine (τ : Y →+ Y →+ Additive A) (w : O) (y : Y) : A := (τ y (w • y)).toMul

variable {τ : Y →+ Y →+ Additive A} {w : O}

end Multiplicative

section HalfElement

variable {K : Type*} [Field K] [CharZero K] [StarRing K] {d : ℤ} {s : K}


end HalfElement

section Example

open QuadraticAlgebra

end Example

end QuadRefinement

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_add_apply_smul_eq_of_add_star_eq_one (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ y (w • y') + τ y' (w • y) = τ y y' := by
  rw [hsymm y' (w • y), hadj, ← map_add (τ y), ← add_smul, hw, one_smul]

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_add_smul_add_eq_add_add (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ (y + y') (w • (y + y')) = τ y (w • y) + τ y' (w • y') + τ y y' := by
  rw [← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y']
  simp only [smul_add, map_add (f := _), AddMonoidHom.add_apply]
  abel

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_neg_smul_neg_eq (y : Y) : τ (-y) (w • -y) = τ y (w • y) := by
  simp

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_smul_smul_eq_zsmul_of_mul_star_eq (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y'))
    (a : O) (n : ℤ) (h : a * star a = n) (y : Y) :
    τ (a • y) (w • a • y) = n • τ y (w • y) := by
  have e : star a * w * a = (n : O) * w := by rw [← h]; ring
  rw [hadj, smul_smul, smul_smul, e, mul_smul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem _root_.GlobalTheory.quadratic_refinement :
    (∀ {O Y A : Type} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]
      (τ : Y →+ Y →+ Additive A) (w : O), (∀ y y', τ y y' = τ y' y) →
      (∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) → w + star w = 1 →
      (∀ y y', _root_.GlobalTheory.QuadRefinement.mulRefine τ w (y + y') =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y *
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y' * (τ y y').toMul) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w (-y) =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ 2 = (τ y y).toMul) ∧
      (∀ (a : O) (n : ℤ), a * star a = n → ∀ y,
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w (a • y) =
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ n) ∧
      (∀ ψ : Y → A, (∀ y y', ψ (y + y') = ψ y * ψ y' * (τ y y').toMul) → (∀ y, ψ (-y) = ψ y) →
        (∃ α : Multiplicative Y →* A,
          (∀ y, α (Multiplicative.ofAdd y) = ψ y / _root_.GlobalTheory.QuadRefinement.mulRefine τ w y)
            ∧ α ^ 2 = 1) ∧
        ∀ n : ℤ, w * star w = n → (∀ y, ψ (w • y) = ψ y ^ n) →
          (∀ y, ψ (star w • y) = ψ y ^ n) → ψ = _root_.GlobalTheory.QuadRefinement.mulRefine τ w) ∧
      (∀ (v : Additive A →+ ℚ) y,
        2 * v (Additive.ofMul (_root_.GlobalTheory.QuadRefinement.mulRefine τ w y)) =
          τ.compr₂ v y y)) ∧
    (∀ {K : Type} [Field K] [CharZero K] [StarRing K] (d : ℤ) (s : K), d % 8 = 7 →
      s ^ 2 = -(d : K) → star s = -s →
      IsIntegral ℤ ((1 + s) / 2) ∧ (1 + s) / 2 + star ((1 + s) / 2) = 1 ∧
      (1 + s) / 2 * star ((1 + s) / 2) = (((1 + d) / 4 : ℤ) : K) ∧
      4 * ((1 + d) / 4) = 1 + d ∧ Even ((1 + d) / 4)) := by
  refine ⟨?_, ?_⟩
  · intro O Y A _ _ _ _ _ τ w hsymm hadj hw
    set m := _root_.GlobalTheory.QuadRefinement.mulRefine τ w with hmdef
    have hm : ∀ y, m y = (τ y (w • y)).toMul := fun _ => rfl
    have hadd : ∀ y y', m (y + y') = m y * m y' * (τ y y').toMul := by
      intro y y'
      simp only [hm, apply_add_smul_add_eq_add_add hsymm hadj hw, toMul_add]
    have hneg : ∀ y, m (-y) = m y := by
      intro y
      simp only [hm, apply_neg_smul_neg_eq]
    have hsq : ∀ y, m y ^ 2 = (τ y y).toMul := by
      intro y
      rw [hm, ← toMul_nsmul, two_nsmul, apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw]
    have hpow : ∀ (a : O) (n : ℤ), a * star a = n → ∀ y, m (a • y) = m y ^ n := by
      intro a n h y
      rw [hm, hm, apply_smul_smul_smul_eq_zsmul_of_mul_star_eq hadj a n h, toMul_zsmul]
    refine ⟨hadd, hneg, hsq, hpow, ?_, ?_⟩
    · intro ψ hψ heven
      have h0 : ψ 0 = 1 := by
        have := hψ 0 0
        simpa using this
      have hψsq : ∀ y, ψ y ^ 2 = (τ y y).toMul := by
        intro y
        have h := hψ y (-y)
        rw [add_neg_cancel, h0, heven, map_neg, toMul_neg, eq_comm, mul_inv_eq_one] at h
        rw [sq, h]
      have hb : ∀ y y', ψ (y + y') / m (y + y') = ψ y / m y * (ψ y' / m y') := by
        intro y y'
        rw [hψ, hadd, mul_div_mul_right_eq_div, div_mul_div_comm]
      have hbsq : ∀ y, (ψ y / m y) ^ 2 = 1 := by
        intro y
        rw [div_pow, hψsq, hsq, div_self']
      let β : Multiplicative Y →* A :=
        MonoidHom.mk' (fun y => ψ y.toAdd / m y.toAdd) (fun y y' => by
          simp only [toAdd_mul]
          exact hb _ _)
      refine ⟨⟨β, fun y => rfl, ?_⟩, ?_⟩
      · ext y
        show β y ^ 2 = 1
        exact hbsq (Multiplicative.toAdd y)
      · intro n hn h1 h2
        funext y
        have hw1 : ψ (w • y) / m (w • y) = (ψ y / m y) ^ n := by
          rw [h1, hpow w n hn, div_zpow]
        have hw2 : ψ (star w • y) / m (star w • y) = (ψ y / m y) ^ n := by
          rw [h2, hpow (star w) n (by rw [star_star, mul_comm, hn]), div_zpow]
        have e : w • y + star w • y = y := by rw [← add_smul, hw, one_smul]
        have key : ψ y / m y = 1 := by
          calc ψ y / m y = ψ (w • y + star w • y) / m (w • y + star w • y) := by rw [e]
            _ = ((ψ y / m y) ^ 2) ^ n := by rw [hb, hw1, hw2, ← mul_zpow, ← sq]
            _ = 1 := by rw [hbsq, one_zpow]
        exact div_eq_one.mp key
    · intro v y
      rw [hm, ofMul_toMul, AddMonoidHom.compr₂_apply, ← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y,
        map_add, two_mul]
  · intro K _ _ _ d s hd hs hstar
    obtain ⟨k, rfl⟩ : ∃ k, d = 8 * k + 7 := ⟨d / 8, by omega⟩
    have hq : (1 + (8 * k + 7)) / 4 = 2 * k + 2 := by omega
    rw [hq]
    push_cast at hs
    have hst : star ((1 + s) / 2) = (1 - s) / 2 := by
      rw [div_eq_mul_inv, star_mul', star_inv₀, star_add, star_one, hstar, star_ofNat]
      ring
    refine ⟨?_, ?_, ?_, by omega, ⟨k + 1, by ring⟩⟩
    · refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 2 : ℤ)), ?_, ?_⟩
      · monicity!
      · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        rw [algebraMap_int_eq, eq_intCast]
        push_cast
        linear_combination (1 / 4 : K) * hs
    · rw [hst]; ring
    · rw [hst]; push_cast; linear_combination (-1 / 4 : K) * hs

end GlobalTheory
end

section

namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine

theorem map_add_of_triples {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A → B)
    (h0 : f 0 = 0) (hneg : ∀ P, f (-P) = -f P)
    (h3 : ∀ P Q R, P ≠ 0 → Q ≠ 0 → R ≠ 0 → P + Q + R = 0 → f P + f Q + f R = 0) (P Q : A) :
    f (P + Q) = f P + f Q := by
  by_cases hP : P = 0
  · simp [hP, h0]
  by_cases hQ : Q = 0
  · simp [hQ, h0]
  by_cases hR : P + Q = 0
  · have : P = -Q := eq_neg_of_add_eq_zero_left hR
    rw [hR, h0, this, hneg, neg_add_cancel]
  have := h3 P Q (-(P + Q)) hP hQ (neg_ne_zero.mpr hR) (add_neg_cancel _)
  rw [hneg] at this
  exact (add_neg_eq_zero.mp this).symm

variable {k : Type*} [Field k] [DecidableEq k] {W : Affine k}

theorem add_add_eq_zero_of_line {x₁ y₁ x₂ y₂ x₃ y₃ : k} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (h₃ : W.Nonsingular x₃ y₃) (l n : k)
    (e₁ : y₁ = l * x₁ + n) (e₂ : y₂ = l * x₂ + n) (e₃ : y₃ = l * x₃ + n)
    (s₁ : x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂)
    (s₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0 := by
  have key : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) ∧ W.slope x₁ x₂ y₁ y₂ = l := by
    by_cases hx : x₁ = x₂
    · subst hx
      have hy : y₁ = y₂ := e₁.trans e₂.symm
      subst hy
      have ht : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ = l * (y₁ - W.negY x₁ y₁) := by
        rw [negY]
        linear_combination (2 * x₁) * s₁ - s₂ - (W.a₁ + 2 * l) * e₁
      have hne : y₁ ≠ W.negY x₁ y₁ := by
        intro h
        rw [nonsingular_iff] at h₁
        rcases h₁.2 with h' | h'
        · apply h'
          rw [← h, sub_self, mul_zero] at ht
          linear_combination -ht
        · exact h' h
      refine ⟨fun h => hne h.2, ?_⟩
      rw [slope_of_Y_ne rfl hne, ht, mul_div_assoc, div_self (sub_ne_zero.mpr hne), mul_one]
    · refine ⟨fun h => hx h.1, ?_⟩
      rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
      linear_combination e₁ - e₂
  rw [Point.add_some key.1]
  apply Point.add_of_Y_eq
  · rw [key.2, addX]
    linear_combination -s₁
  · have hx : W.addX x₁ x₂ l = x₃ := by
      rw [addX]
      linear_combination -s₁
    rw [key.2, addY, negAddY, hx]
    congr 1
    linear_combination e₁ - e₃

theorem exists_line_of_add_add_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ : k} {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} {h₃ : W.Nonsingular x₃ y₃}
    (h : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0) :
    ∃ l n : k, y₁ = l * x₁ + n ∧ y₂ = l * x₂ + n ∧ y₃ = l * x₃ + n ∧
      x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l ∧
      x₁ * x₂ * x₃ = n ^ 2 + W.a₃ * n - W.a₆ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    rw [Point.add_of_Y_eq hx hy, zero_add] at h
    exact Point.some_ne_zero _ h
  rw [Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at h
  obtain ⟨hx, hy⟩ := h
  have hp := addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hx] at hp
  have hl : W.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    by_cases hx' : x₁ = x₂
    · have := Y_eq_of_Y_ne h₁.1 h₂.1 hx' (fun h => hxy ⟨hx', h⟩)
      rw [hx', this, sub_self, sub_self, mul_zero]
    · rw [slope_of_X_ne hx', div_mul_cancel₀ _ (sub_ne_zero.mpr hx')]
  rw [addY, negAddY, hx, negY, negY] at hy
  set l := W.slope x₁ x₂ y₁ y₂
  simp only [Cubic.mk.injEq, true_and] at hp
  obtain ⟨p₁, p₂, p₃⟩ := hp
  refine ⟨l, y₁ - l * x₁, by ring, by linear_combination hl, by linear_combination hy,
    by linear_combination p₁, by linear_combination -p₂, by linear_combination p₃⟩

section VariableChange


omit [DecidableEq k] in
theorem nonsingular_variableChange_iff (W : WeierstrassCurve k) (C : VariableChange k) (x y : k) :
    W.toAffine.Nonsingular ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t) ↔ (C • W).toAffine.Nonsingular x y := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [nonsingular_iff', equation_iff', variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  obtain ⟨u, r, s, t⟩ := C
  dsimp only at hu ⊢
  generalize (u : k) = v at hu ⊢
  obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := W
  dsimp only [toAffine]
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h
  · rw [← not_iff_not]
    simp only [not_or, not_not]
    refine ⟨fun ⟨h, h'⟩ => ⟨?_, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
    · field_simp
      linear_combination h + s * h'
    · field_simp
      linear_combination h'
    · field_simp at h h'
      exact ⟨by linear_combination h - s * h', by linear_combination h'⟩

def variableChangePointFun {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point → W.toAffine.Point
  | .zero => 0
  | .some x y hP => .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP))

def variableChangePoint {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point →+ W.toAffine.Point :=
  AddMonoidHom.mk' (variableChangePointFun C h) <| by
    subst h
    have hu : (C.u : k) ≠ 0 := C.u.ne_zero
    refine map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, variableChangePointFun, Point.some.injEq, true_and, negY,
          variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
        field_simp
        ring
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := exists_line_of_add_add_eq_zero h
      simp only [variableChange_a₁, variableChange_a₂,
        variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val] at s₁ s₂
      field_simp at s₁ s₂
      refine add_add_eq_zero_of_line _ _ _ ((C.u : k) * l + C.s)
        ((C.u : k) ^ 3 * n + C.t - C.r * ((C.u : k) * l + C.s)) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; ring
      · rw [e₂]; ring
      · rw [e₃]; ring
      · linear_combination s₁
      · linear_combination s₂ + 2 * C.r * s₁

@[simp]
theorem variableChangePoint_some {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') {x y : k} (hP : W'.toAffine.Nonsingular x y) :
    variableChangePoint C h (.some x y hP) = .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP)) :=
  rfl

theorem variableChangePoint_bijective {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : Function.Bijective (variableChangePoint C h) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro (_ | ⟨x, y, hP⟩) h0
    · rfl
    · exact absurd h0 (Point.some_ne_zero _)
  · rintro (_ | ⟨x, y, hP⟩)
    · exact ⟨0, map_zero _⟩
    · have hx : x = (C.u : k) ^ 2 * ((x - C.r) / (C.u : k) ^ 2) + C.r := by field_simp; ring
      have hy : y = (C.u : k) ^ 3 * ((y - C.s * (x - C.r) - C.t) / (C.u : k) ^ 3)
          + (C.u : k) ^ 2 * C.s * ((x - C.r) / (C.u : k) ^ 2) + C.t := by field_simp; ring
      have hP' := hP
      rw [hx, hy, ← hx] at hP'
      nth_rw 1 [hx] at hP'
      rw [nonsingular_variableChange_iff, h] at hP'
      refine ⟨.some _ _ hP', ?_⟩
      rw [variableChangePoint_some, Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩

noncomputable def variableChangePointEquiv {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : W'.toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (variableChangePoint C h) (variableChangePoint_bijective C h)

end VariableChange

end GlobalTheory
end

section

universe u_1

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SchemeDominantSpecMap

theorem appTop_injective {R A : CommRingCat.{u_1}} (φ : R ⟶ A) (h : Function.Injective φ) :
    Function.Injective (Spec.map φ).appTop := by

  have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality φ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1.comp
    (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)

theorem isSchemeTheoreticallyDominant_specMap {R A : CommRingCat.{u_1}} (φ : R ⟶ A)
    (h : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot (Spec.map φ).appTop.hom).1 (appTop_injective φ h),
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]

end GlobalTheory.SchemeDominantSpecMap
end
