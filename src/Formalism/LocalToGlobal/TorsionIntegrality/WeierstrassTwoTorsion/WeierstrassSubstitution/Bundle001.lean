module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementF
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

universe u

namespace Formalism.L2.Th1.A
namespace QuadraticFlow

variable {A : Type u} [CommRing A] {D : A → A}

lemma der_add (h : IsDer D) (a b : A) : D (a + b) = D a + D b := h.1 a b

lemma der_mul (h : IsDer D) (a b : A) : D (a * b) = a * D b + b * D a := h.2 a b

lemma der_zero (h : IsDer D) : D 0 = 0 := by
  have e := h.1 0 0
  rw [add_zero] at e
  linear_combination -e

lemma der_one (h : IsDer D) : D 1 = 0 := by
  have e := h.2 1 1
  simp only [mul_one, one_mul] at e
  linear_combination -e

lemma der_neg (h : IsDer D) (a : A) : D (-a) = -D a := by
  have e := h.1 a (-a)
  rw [add_neg_cancel, der_zero h] at e
  linear_combination -e

lemma der_sub (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, der_add h, der_neg h, ← sub_eq_add_neg]

lemma der_natCast (h : IsDer D) (n : ℕ) : D (n : A) = 0 := by
  induction n with
  | zero => simpa using der_zero h
  | succ n ih => rw [Nat.cast_succ, der_add h, ih, der_one h, add_zero]

lemma der_ofNat (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by
  simpa using der_natCast h (OfNat.ofNat n)

lemma der_sq (h : IsDer D) (a : A) : D (a ^ 2) = 2 * a * D a := by
  rw [sq, der_mul h]
  ring

lemma der_inv (h : IsDer D) {t s : A} (hts : t * s = 1) : D t = -t ^ 2 * D s := by
  have e := h.2 t s
  rw [hts, der_one h] at e
  linear_combination (-t) * e + (-D t) * hts

lemma cancel_unit {k a b : A} (hk : IsUnit k) (e : k * a = k * b) : a = b := hk.mul_left_cancel e

lemma unit_four (h6 : IsUnit (6 : A)) : IsUnit (4 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  rw [e6] at h6
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left h6
  have e4 : (4 : A) = 2 * 2 := by norm_num
  rw [e4]
  exact h2.mul h2

lemma unit_twelve (h6 : IsUnit (6 : A)) : IsUnit (12 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left (e6 ▸ h6)
  have e12 : (12 : A) = 6 * 2 := by norm_num
  rw [e12]
  exact h6.mul h2

lemma weierstrassSubstitution_unit_fact (h6 : IsUnit (6 : A)) : IsUnit (432 : A) := by
  have e : (432 : A) = 6 * 6 * 12 := by norm_num
  rw [e]
  exact (h6.mul h6).mul (unit_twelve h6)

end QuadraticFlow

open QuadraticFlow

theorem twoTorsionTranslation : FlowTwoTorsion.{u} := by
  intro A _ W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  obtain ⟨hE, hDx, hDy⟩ := hF
  obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := hC
  rw [WeierstrassCurve.Affine.equation_iff] at hE hT
  have hDt : D t = -t ^ 2 * (2 * y + W.a₁ * x + W.a₃) := by
    rw [der_inv hD ht, der_sub hD, hDxT, sub_zero, hDx]
  refine ⟨?_, ?_, ?_⟩
  · simp only [WeierstrassCurve.Affine.addX]
    linear_combination t ^ 2 * hE - t ^ 2 * hT - t ^ 2 * (y - yT) * h2 +
      ((3 * xT + (x - xT) + W.a₂) + t * ((x ^ 2 + x * xT + xT ^ 2 + W.a₂ * (x + xT) + W.a₄) - W.a₁ * yT) - W.a₁ * (y - yT) * t) * ht
  · rw [hDt]
    simp only [WeierstrassCurve.b₂]
    linear_combination 4 * t ^ 4 * hE - 4 * t ^ 4 * hT + t ^ 4 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) * h2 +
      (4 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 3 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t ^ 2 * (2 + (t * (x - xT) - 1)) + 4 * t * (3 + 3 * (t * (x - xT) - 1) + (t * (x - xT) - 1) ^ 2)) * ht
  · rw [hDt]
    simp only [der_neg hD, der_mul hD, der_add hD, der_sq hD, der_ofNat hD, hDx, hDy, hDt, ha1, ha3,
      WeierstrassCurve.b₂]
    linear_combination 8 * t ^ 3 * hE - 8 * t ^ 3 * hT +
      (2 * t ^ 3 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) - W.a₁ * t ^ 2) * h2 +
      (8 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 2 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t * (3 + 2 * (t * (x - xT) - 1)) + 12 + 18 * (t * (x - xT) - 1) + 8 * (t * (x - xT) - 1) ^ 2) * ht

theorem twoTorsionTranslationWeierstrassForm : FlowTwoTorsionWp.{u} := by
  intro A _ W D x y xT yT t c g2 g3 kap hD hC hF hT hDxT hDyT h2 ht h6 hc hg2 hg3 hk
  have H1 := twoTorsionTranslation A W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  rw [WeierstrassCurve.Affine.equation_iff] at hT
  have hkap : kap = (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) := by
    apply cancel_unit ((unit_four h6).mul (unit_twelve h6))
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.c₄] at hc hg2
    linear_combination 12 * hk + (24 * xT + 12 * c + (W.a₁ ^ 2 + 4 * W.a₂)) * hc - hg2 + 24 * W.a₁ * h2
  have ha : 4 * (xT + c) ^ 3 - g2 * (xT + c) - g3 = 0 := by
    apply cancel_unit (weierstrassSubstitution_unit_fact h6)
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.c₄,
      WeierstrassCurve.c₆] at hc hg2 hg3
    linear_combination ((12 * xT + 12 * c) ^ 2 + (12 * xT + 12 * c) * (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) ^ 2 - 3 * ((W.a₁ ^ 2 + 4 * W.a₂) ^ 2 - 24 * (2 * W.a₄ + W.a₁ * W.a₃))) * hc - 36 * (xT + c) * hg2 -
      2 * hg3 + 432 * (2 * yT + W.a₁ * xT + W.a₃) * h2 - 1728 * hT
  have hd : D t ^ 2 = 4 * t * (1 + 3 * (xT + c) * t + kap * t ^ 2) := by
    linear_combination H1.2.1 - t ^ 2 * hc - 4 * t ^ 3 * hkap
  refine ⟨ha, hkap, ?_, hd, ?_⟩
  · rw [H1.1, hkap]
    ring
  · intro e2 e3 hs he
    linear_combination hd + (4 * t ^ 2 + 8 * (xT + c) * t ^ 3) * hs + t ^ 3 * hk - t ^ 3 * he

end Formalism.L2.Th1.A
end

section

universe u

namespace Formalism.L2.Th1.A

variable {A : Type u} [CommRing A]

theorem IsDer.exists_derivation {D : A → A} (h : IsDer D) :
    ∃ d : Derivation ℤ A A, ∀ a, D a = d a := by
  refine ⟨Derivation.mk' (AddMonoidHom.mk' D h.1).toIntLinearMap (fun a b => ?_), fun a => rfl⟩
  simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
  exact h.2 a b

theorem der_mul (d : Derivation ℤ A A) (a b : A) : d (a * b) = a * d b + b * d a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem der_sq (d : Derivation ℤ A A) (a : A) : d (a ^ 2) = 2 * a * d a := by
  rw [pow_two, der_mul]
  ring

theorem der_inv (d : Derivation ℤ A A) {t s : A} (ht : t * s = 1) : d t = -t ^ 2 * d s := by
  have h0 : t * d s + s * d t = 0 := by rw [← der_mul, ht, Derivation.map_one_eq_zero]
  have h1 : d t = t * s * d t := by rw [ht, one_mul]
  rw [h1]
  linear_combination t * h0

theorem chord_rel {a₁ a₂ a₃ a₄ a₆ x y xP yP t L : A}
    (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hEP : yP ^ 2 + a₁ * xP * yP + a₃ * yP = xP ^ 3 + a₂ * xP ^ 2 + a₄ * xP + a₆)
    (ht : t * (x - xP) = 1) (hL : L * (x - xP) = y - yP) :
    (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
        - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 ∧
      (a₆ - (y - L * x) ^ 2 - a₃ * (y - L * x))
        + x * xP * (L ^ 2 + a₁ * L - a₂ - x - xP) = 0 := by
  have hα : (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 := by
    linear_combination (-((a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)))) * ht - t * hE + t * hEP
      - t * (L * xP + (y - L * x) + yP + a₁ * xP + a₃) * hL
  refine ⟨hα, ?_⟩
  linear_combination (-1 : A) * hE - x * hα

theorem der_slope (W : WeierstrassCurve A) (d : Derivation ℤ A A) {x y xP yP t : A}
    (hE : W.toAffine.Equation x y) (hx : d x = 2 * y + W.a₁ * x + W.a₃)
    (hy : d y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hEP : W.toAffine.Equation xP yP) (hxP : d xP = 0) (hyP : d yP = 0)
    (ht : t * (x - xP) = 1) :
    d ((y - yP) * t) = x - W.toAffine.addX x xP ((y - yP) * t) := by
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, -⟩ := chord_rel hE' hEP' ht hL
  have hdt : d t = -t ^ 2 * d (x - xP) := der_inv d ht
  have hdxs : d (x - xP) = d x := by rw [map_sub, hxP, sub_zero]
  rw [der_mul, map_sub, hyP, sub_zero, hdt, hdxs, hx, hy]
  simp only [WeierstrassCurve.Affine.addX]
  linear_combination (x - (((y - yP) * t) ^ 2 + W.a₁ * ((y - yP) * t) - W.a₂ - x - xP)) * ht + t * hα

theorem flowTranslation : FlowTranslate.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hDL := der_slope W d hE hx hy hEP hxP hyP ht
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, hβ⟩ := chord_rel hE' hEP' ht hL
  set L := (y - yP) * t with hLdef
  have hDL' : d L = x - (L ^ 2 + W.a₁ * L - W.a₂ - x - xP) := hDL
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX]
    linear_combination (-1 : A) * hβ - (L ^ 2 + W.a₁ * L - W.a₂ - x - xP) * hα
  · rw [hd]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, map_sub, map_add, der_sq, der_mul, c1, c2, hx, hxP, hDL']
    ring
  · rw [hd]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, map_neg, map_sub, map_add, der_sq, der_mul, c1, c2, c3, hx, hy, hxP, hDL']
    linear_combination (-2 : A) * hα

theorem flowLogDerivative : FlowLogDeriv.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hEQ : W.toAffine.Equation xP (W.toAffine.negY xP yP) :=
    (WeierstrassCurve.Affine.equation_neg xP yP).2 hEP
  have hyQ : d (W.toAffine.negY xP yP) = 0 := by
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, der_mul, hyP, hxP, c1, c3]
    ring
  have hP := der_slope W d hE hx hy hEP hxP hyP ht
  have hQ := der_slope W d hE hx hy hEQ hxP hyQ ht

  have hsplit : t * (2 * y + W.a₁ * x + W.a₃) =
      (y - yP) * t + (y - W.toAffine.negY xP yP) * t + W.a₁ * (t * (x - xP)) := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  simp only [hd]
  rw [hx, hsplit, map_add (f := _), map_add (f := _), hP, hQ, ht, mul_one, c1]
  ring

end Formalism.L2.Th1.A
end
