module

public import Formalism.DropLevelBounds.Statement
public import Formalism.IncomingBounds.Bundle001
public import Mathlib.RingTheory.Binomial
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Mathlib.Algebra.MvPolynomial.Variables
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

def Ereal (l i : ℕ) : ℝ := 1 + ((l : ℝ) ^ i - l) * rho l

def r1 (l i : ℕ) : ℝ := rho l + 1 / (2 * (l : ℝ) ^ i)

def r2 (l : ℕ) : ℝ := rho l + 1 / 2

def del (l i : ℕ) : ℝ := 1 / (8 * (l : ℝ) ^ i)

def EInt : Prop := ∀ l i : ℕ, 2 ≤ l → Odd i → gam l = l * rho l ∧ (expE l i : ℝ) = Ereal l i

def I1 : Prop := ∀ l i : ℕ, 2 ≤ l →
  (l : ℝ) ^ i * r1 l i + r2 l = ((l : ℝ) ^ i + 1) * rho l + 1 ∧
    ((l : ℝ) ^ i + 1) * rho l + 1 = Ereal l i + 1 / ((l : ℝ) - 1)

def I2 : Prop := ∀ l i : ℕ, 2 ≤ l → 1 ≤ i →
  (l : ℝ) ^ i / ((l : ℝ) - 1) - Ereal l i = ((l : ℝ) ^ i + 1) * gam l - 1 ∧
    0 ≤ ((l : ℝ) ^ i + 1) * gam l - 1

def ValOther : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 →
    ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0

def HM1 {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (l i n0 : ℕ)
    (h1 : MvPowerSeries (PVar n0) C) : Prop :=
  ∀ m : PVar n0 →₀ ℕ,
    (((1 / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) ≤
      v (MvPowerSeries.coeff m h1) +
        (((degL m : ℝ) * (r1 l i - del l i) + (degR m : ℝ) * (r2 l - del l i) : ℝ) : WithTop ℝ)

def HM2 {C : Type} [Field C] {n0 : ℕ} (h1 : MvPowerSeries (PVar n0) C) : Prop :=
  ∀ m : PVar n0 →₀ ℕ, MvPowerSeries.coeff m h1 ≠ 0 → 1 ≤ degR m

def HSeparatedRowSum {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (l n0 : ℕ)
    (h1 : MvPowerSeries (PVar n0) C) : Prop :=
  ∃ hb : Fin n0 → MvPowerSeries (PVar n0) C, h1 = ∑ b, hb b ∧
    (∀ b (m : PVar n0 →₀ ℕ), MvPowerSeries.coeff m (hb b) ≠ 0 → ∀ x ∈ m.support, rowOf x = b) ∧
    ∀ b (m : PVar n0 →₀ ℕ), degL m < l ^ 2 → degR m < l → 0 ≤ v (MvPowerSeries.coeff m (hb b))

def WeightConditionIff : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l i n0 : ℕ)
    (h1 : MvPowerSeries (PVar n0) C), HM1 v l i n0 h1 ↔ WeightCond v l i n0 h1

def bdP (l i n0 n y : ℕ) : ℝ :=
  (n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1)

def F1 : Prop := CayleyId

def CapacityFactorialProduct : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 x : ℕ),
    jetAt0 (detL C n0 ^ x) ((detL C n0 ^ x : MvPolynomial (PVar n0) C) : MvPowerSeries (PVar n0) C) =
        ((∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n0, (t + c) : ℕ) : C) ∧
      (∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n0, (t + c)) = capNat n0 x ∧
      (∀ c, c.factorial ∣ (x + c).factorial) ∧ capNat n0 x ≠ 0

def F3 : Prop :=
  ∀ l : ℕ, l.Prime → ∀ n0 n x : ℕ, 1 ≤ n → n0 ≤ n →
    (padicValNat l (capNat n0 x) : ℝ) ≤
        (n0 : ℝ) * x / ((l : ℝ) - 1) + n0 * (Real.logb l n0 + 1) ∧
      (n0 : ℝ) * x / ((l : ℝ) - 1) + n0 * (Real.logb l n0 + 1) ≤
        (n0 : ℝ) * x / ((l : ℝ) - 1) + n * (Real.logb l n + 1)

def F5 : Prop :=
  (∀ (y : ℤ) (s : ℕ), ((Ring.choose y s : ℤ) : ℚ) =
      (∏ j ∈ Finset.range s, ((y : ℚ) - j)) / (s.factorial : ℚ)) ∧
    (∀ (y : ℤ) (s : ℕ), Ring.choose (y + 1) (s + 1) - Ring.choose y (s + 1) = Ring.choose y s) ∧
    (∀ y : ℤ, Ring.choose (y + 1) 0 - Ring.choose y 0 = 0) ∧
    (∀ s : ℕ, Ring.choose (0 : ℤ) s = if s = 0 then 1 else 0)

def S0 (l i n0 : ℕ) : ℕ := ⌈64 * (n0 : ℝ) ^ 2 * ((i : ℝ) + 3 + 3 * Real.logb l ((n0 : ℝ) + 1))⌉₊

def ThmP : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i : ℕ, Odd i → ∀ n n0 : ℕ, 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) C, HM1 v l i n0 h1 → HM2 h1 →
      (1 ≤ n0 → ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧ y < Y0 + S0 l i n0 ∧
        v (LamP C l i n0 h1 y) ≤ ((bdP l i n0 n y : ℝ) : WithTop ℝ)) ∧
      (n0 = 0 → ∀ y : ℕ, LamP C l i n0 h1 y = 1)

def CoefficientExpansionLambda : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i : ℕ, Odd i → ∀ n0 : ℕ,
    ∀ h1 : MvPowerSeries (PVar n0) C, HM1 v l i n0 h1 → HM2 h1 →
      ∃ a : ℕ → C, a 0 = 1 ∧
        (∀ y : ℕ, LamP C l i n0 h1 y =
          (-((l : C) ^ (expE l i))⁻¹) ^ (n0 * y) * (capNat n0 (l ^ i * y) : C) *
            ∑ s ∈ Finset.range (y + 1), ((Nat.choose y s : ℕ) : C) * a s) ∧
        ∀ s : ℕ, 1 ≤ s →
          ((((s : ℝ) / 8 - (n0 : ℝ) ^ 2 *
            (3 * Real.logb l n0 + 2 * Real.logb l s + i + 3)) : ℝ) : WithTop ℝ) ≤ v (a s)

def NewtonBoundPositive : Prop :=
  ∀ l : ℕ, 5 ≤ l → ∀ i n0 s : ℕ, 1 ≤ i → 1 ≤ n0 → S0 l i n0 ≤ s →
    0 < (s : ℝ) / 8 - (n0 : ℝ) ^ 2 * (3 * Real.logb l n0 + 2 * Real.logb l s + i + 3)

def P7 : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : ℕ) (a : ℕ → C), 1 ≤ S →
    a 0 = 1 → (∀ s : ℕ, S ≤ s → 0 < v (a s)) → ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧ y < Y0 + S ∧
      v (∑ s ∈ Finset.range (y + 1), ((Nat.choose y s : ℕ) : C) * a s) ≤ 0

def minorK (C : Type) [CommRing C] (N N' k : ℕ) : MvPolynomial (Fin N × Fin N') C :=
  if h : k ≤ N ∧ k ≤ N' then
    (Matrix.of fun b c : Fin k =>
      (MvPolynomial.X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') C)).det
  else 1

def monP (C : Type) [CommRing C] (N N' : ℕ) (e : ℕ → ℕ) : MvPolynomial (Fin N × Fin N') C :=
  ∏ k ∈ Finset.Icc 1 (min N N'), minorK C N N' k ^ e k

def monAl (N N' : ℕ) (e : ℕ → ℕ) (ρ : ℕ) : ℕ := ∑ k ∈ Finset.Icc (ρ + 1) (min N N'), e k

def monDeg (N N' : ℕ) (e : ℕ → ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 (min N N'), k * e k

def TangentId {C : Type} [CommRing C] {σ : Type} (t : σ → MvPowerSeries σ C) : Prop :=
  ∀ (x : σ) (m : σ →₀ ℕ), m.degree ≤ 1 →
    MvPowerSeries.coeff m (t x) = MvPowerSeries.coeff m (MvPowerSeries.X x : MvPowerSeries σ C)

def monG {C : Type} [CommRing C] {σ : Type} (N N' : ℕ) (e : ℕ → ℕ)
    (t : Fin N × Fin N' → MvPowerSeries σ C) : MvPowerSeries σ C :=
  ∏ ρ : Fin N, if h : ρ.val < N' then t (ρ, ⟨ρ.val, h⟩) ^ monAl N N' e ρ.val else 1

def InRow {C : Type} [Field C] {n : ℕ} (ρ : Fin n) (G : MvPowerSeries (PVar n) C) : Prop :=
  ∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m G ≠ 0 → ∀ x ∈ m.support, rowOf x = ρ

def DiagCoord {C : Type} [Field C] {n : ℕ} (w : Fin n → PVar n) (ρ : Fin n)
    (t : MvPowerSeries (PVar n) C) : Prop :=
  (∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m t ≠ 0 → ∀ x ∈ m.support, ∃ c, x = w c) ∧
    ∀ m : PVar n →₀ ℕ, m.degree ≤ 1 →
      MvPowerSeries.coeff m t = MvPowerSeries.coeff m (MvPowerSeries.X (w ρ) : MvPowerSeries (PVar n) C)

structure BiHyp {C : Type} [Field C] (l i n0 n : ℕ) (hn : n0 ≤ n)
    (hr t t' : Fin n → MvPowerSeries (PVar n) C) (h1 : MvPowerSeries (PVar n0) C) : Prop where
  biadditive_in_single_variables : ∀ ρ, InRow ρ (hr ρ)
  constantCoeff_biadditive_zero : ∀ ρ, MvPowerSeries.constantCoeff (hr ρ) = 0
  diagonal_coordinate_left : ∀ ρ : Fin n, n0 ≤ ρ.val → DiagCoord (fun c => Sum.inl (ρ, c)) ρ (t ρ)
  diagonal_coordinate_right : ∀ ρ : Fin n, n0 ≤ ρ.val → DiagCoord (fun c => Sum.inr (ρ, c)) ρ (t' ρ)
  R3 : restr hn (∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => ρ.val < n0), hr ρ) =
    hP C l i n0 h1

def BiF {C : Type} [Field C] (l i n0 n y : ℕ) (hr t t' : Fin n → MvPowerSeries (PVar n) C) :
    MvPowerSeries (PVar n) C :=
  ∏ ρ : Fin n, (if ρ.val < n0 then 1 else t ρ ^ (l ^ i * y) * t' ρ ^ y) * mvExp (hr ρ)

def BiValue : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (l i n0 n : ℕ) (hn : n0 ≤ n)
    (hr t t' : Fin n → MvPowerSeries (PVar n) C) (h1 : MvPowerSeries (PVar n0) C),
    BiHyp l i n0 n hn hr t t' h1 → ∀ y : ℕ,
      jetAt0 (detL C n ^ (l ^ i * y) * detR C n ^ y) (BiF l i n0 n y hr t t') =
        ((((l ^ i * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * LamP C l i n0 h1 y

def BiContent : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i n n0 y : ℕ, Odd i → 1 ≤ n → n0 ≤ n → ∀ Λ : C,
      v Λ ≤ ((bdP l i n0 n y : ℝ) : WithTop ℝ) →
      v (((((l ^ i * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * Λ) ≤
        (((bdP l i n n y + ((n : ℝ) - n0) * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ)

def BiWindow : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i : ℕ, Odd i → ∀ (n0 n m : ℕ) (hn : n0 ≤ n), 1 ≤ n0 →
    n - n0 ≤ (i + 1) * m →
    ∀ (hr t t' : Fin n → MvPowerSeries (PVar n) C) (h1 : MvPowerSeries (PVar n0) C),
    BiHyp l i n0 n hn hr t t' h1 → HM1 v l i n0 h1 → HM2 h1 →
      ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧ y < Y0 + S0 l i n0 ∧
        v (jetAt0 (detL C n ^ (l ^ i * y) * detR C n ^ y) (BiF l i n0 n y hr t t')) ≤
          (((bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)) : ℝ) :
            WithTop ℝ)

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.GmExArith

open Formalism.L2.FormalSeriesBounds NumberField

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_neg {a : C} (h : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *; rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]; exact mm_add ha (mm_neg hb)

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact add_pos_of_pos_of_nonneg ha hb'

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ge_natCast' (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

theorem ge_intCast' (m : ℤ) : V.Ge 0 (m : C) := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact ge_natCast' n
  | negSucc n => rw [Int.cast_negSucc]; exact (ge_natCast' (n + 1)).neg

theorem geom_int {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (n : ℕ) :
    V.Ge 0 (∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i)) :=
  VF.Ge.sum fun i _ => (hA.pow i).mul_int (hB.pow _)

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) (n : ℕ) :
    V.MM (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact mm_int_mul (geom_int hA hB n) h

end Formalism.L2.FormalSeriesBounds.GmExArith
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

abbrev Knd (d : ℕ) := Option (Fin 2 × ZMod d × ZMod d)

section Place

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}

def kindAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (kind : ∀ i, Fin (what₂ i) → Knd d) (ρ : Fin N) : Knd d :=
  if h : ∃ s, pl s = ρ then kind h.choose.1 h.choose.2 else none

def grAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C) (ρ : Fin N) :
    MvPowerSeries (WV I) C :=
  if h : ∃ s, pl s = ρ then gr h.choose.1 h.choose.2 else 1

def prodAll (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N) (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) :
    MvPolynomial (Fin N × WV I) C :=
  ∏ i, MvPolynomial.rename (fun x : Fin (what₂ i) × WV I => (pl ⟨i, x.1⟩, x.2)) (P i)

theorem kindAll_pl {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (kind : ∀ i, Fin (what₂ i) → Knd d) (s : Σ i : Fin K, Fin (what₂ i)) : kindAll pl kind (pl s) = kind s.1 s.2 := by
  unfold kindAll
  have hex : ∃ s', pl s' = pl s := ⟨s, rfl⟩
  rw [dite_eq_left hex]
  have hc : hex.choose = s := hpl hex.choose_spec
  rw [hc]

theorem mem_vars_prodAll {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} {P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C}
    {ρ : Fin N} {w : WV I} (h : (ρ, w) ∈ (prodAll pl P).vars) :
    ∃ s : Σ i : Fin K, Fin (what₂ i), pl s = ρ ∧ (s.2, w) ∈ (P s.1).vars := by
  unfold prodAll at h
  have h1 := MvPolynomial.vars_prod _ h
  rw [Finset.mem_biUnion] at h1
  obtain ⟨i, -, hi⟩ := h1
  have h2 := MvPolynomial.vars_rename _ _ hi
  rw [Finset.mem_image] at h2
  obtain ⟨⟨r, w'⟩, hw', heq⟩ := h2
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨⟨i, r⟩, rfl, hw'⟩

end Place

section Rows

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}

private lemma forall_support_ne_zero_iff_forall_mem_vars {R0 : Type} [Field R0] {α β : Type} (Q : MvPolynomial (α × β) R0)
    (ρ : α) (T : β → Prop) :
    (∀ μ ∈ Q.support, ∀ w, μ (ρ, w) ≠ 0 → T w) ↔ (∀ w, (ρ, w) ∈ Q.vars → T w) := by
  constructor
  · intro H w hw
    obtain ⟨μ, hμ, hx⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 hw
    exact H μ hμ w (Finsupp.mem_support_iff.1 hx)
  · intro H μ hμ w hx
    exact H w ((MvPolynomial.mem_vars_iff_mem_support _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hx⟩)

theorem rowsOK_iff (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ} (P : MvPolynomial (Fin N × WV I) C)
    (kind : Fin N → Knd d) : RowsOK G alt P kind ↔
      (∀ ρ g a a', kind ρ = some (g, a, a') → alt ∧ Odd (a' - a).val ∧
        ∀ w, (ρ, w) ∈ P.vars → OnLeafV G g a a' w) ∧
      (∀ ρ, kind ρ = none → ∃ g : Fin 2, ∀ w : WV I, (ρ, w) ∈ P.vars → w.1 = g) := by
  unfold RowsOK
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).1 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).1 hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).2 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).2 hg⟩

theorem rowsOK_prodAll (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop)
    {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
    (h : ∀ i, RowsOK G alt (P i) (kind i)) : RowsOK G alt (prodAll pl P) (kindAll pl kind) := by
  rw [rowsOK_iff]
  have h' := fun i => (rowsOK_iff G alt (P i) (kind i)).1 (h i)
  refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨h1, h2, h3⟩ := (h' s.1).1 s.2 g a a' hk
      refine ⟨h1, h2, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact h3 w hw'
    · exfalso
      unfold kindAll at hk
      rw [dite_eq_right hex] at hk
      cases hk
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨g, hg⟩ := (h' s.1).2 s.2 hk
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact hg w hw'
    · refine ⟨0, fun w hw => ?_⟩
      obtain ⟨s', hs', -⟩ := mem_vars_prodAll hw
      exact absurd ⟨s', hs'⟩ hex

end Rows

def JetProdSt : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)]
    (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (N K : ℕ) (what₂ : Fin K → ℕ)
    (pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N), Function.Injective pl →
    ∀ (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
      (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C),
      ValOf hL (prodAll pl P) (kindAll pl kind) (grAll pl gr) = ∏ i, ValOf hL (P i) (kind i) (gr i)

end Formalism.L2.FormalSeriesBounds
end
end
