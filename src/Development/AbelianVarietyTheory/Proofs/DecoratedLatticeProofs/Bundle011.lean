module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001

@[expose] public section

section

open ValuativeRel GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.relIndex_inf_mul_relIndex_inf_eq_resCard_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) → (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) → (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := by
  first | exact @GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal | exact GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal | (intros; apply GlobalTheory.ScaledIdealIndex.relIndex_scaled_maxIdeal <;> assumption)
end

section

open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.PartRed
open GlobalTheory.SplitWeil GlobalTheory.RootEx

section Gen
variable {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

def fillAt (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) : Matrix R Q k :=
  Matrix.of fun r q => if h : (r, q) ∈ I then y ⟨(r, q), h⟩ else if (r, q) ∈ E then β r q else x r q

variable [TopologicalSpace k] [MeasurableSpace k]

def red (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k) : ℂ :=
  ∫ y : I → k, Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) ∂(Measure.pi fun _ => ν)

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def Kills (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) : Prop :=
  ∀ Φ : SB (Matrix R Q k), red ψ ν w β E I Φ.1 = 0 → L Φ = 0

def EvalLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (b : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = (ψ (b * (x e.1 e.2 - β e.1 e.2)) : ℂ) * red ψ ν w β E I Φ.1 x

def IntLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (a : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 a)

end Gen

section Flat
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def chL : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k →ₗ[k] k where
  toFun := ch
  map_add' x y := by simp [ch, Finset.sum_add_distrib]
  map_smul' a x := by simp [ch, Finset.mul_sum]

theorem chL_apply (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : chL x = ch x := rfl


open Classical in
def fixSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)


open Classical in
def transSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val


open Classical in
def lowSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val


open Classical in
def upSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ

def colIx (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : ℕ := Sum.elim (fun _ => 0) (fun i => i.val) e.2

end Flat

end GlobalTheory.PartRed
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FlatFactor

section Gen
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

def fill (ev it : Finset (m × m')) (β t : Matrix m m' k) (a : {e : m × m' // e ∈ it} → k) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

def red (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (t : Matrix m m' k) : ℂ :=
  ∫ a, Θ (fill ev it β t a) ∂(Measure.pi fun _ => ν)

def KerRed {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : Prop :=
  ∀ Θ : SB (Matrix m m' k), (∀ t, red ν ev it β Θ.1 t = 0) → l Θ = 0

end Gen

section Pos
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)


open Classical in
def evC : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e =>
    (∃ i, e.2 = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l, e.1 = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, e.2 = Sum.inr i → i.val = ρ)


open Classical in
def itB : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ ≤ i.val

def IsRead : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (.inl _, .inl _) => True
  | (.inl _, .inr i) => i.val = ρ
  | (.inr _, _) => False


open Classical in
def evAll : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e


open Classical in
def itFree : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e

variable {n n' c}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def TwLaw {M : Type} [AddCommGroup M] [Module ℂ M] (ψ : AddChar k Circle)
    (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M) : Prop :=
  ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ i j : Fin c, i.val < ρ → ρ ≤ j.val → u.val i j = 0) →
    ∀ Θ Θ' Θ'' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ t, Θ'.1 t = Θ.1 (((embA n u)⁻¹).val * t)) →
      (∀ t, Θ''.1 t = (ψ (ch ((embA n u).val * t) - ch t) : ℂ) * Θ.1 t) →
      l Θ' = (ψ (-simpleSum (embA n u)) : ℂ) • l Θ''

end Pos

end GlobalTheory.FlatFactor
end
end

section

open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.Klein.DiffUnit

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.Klein.DiffUnit

namespace GlobalTheory.Klein
open DiffUnit

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_add_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x + y‖ ≤ a :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_sub_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x - y‖ ≤ a := by
  rw [sub_eq_add_neg]
  exact padicComplex_norm_add_le_of_norm_le hx (by rwa [norm_neg])

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_mul_le_of_norm_le_one {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ a) :
    ‖x * y‖ ≤ a := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma norm_sub_eq_one_of_discriminant_relations (hp2 : ‖(2 : ℂ_[p])‖ = 1)
    {X₁ X₂ S T Y₁ Y₂ b c D : ℂ_[p]} (hX₁ : ‖X₁‖ ≤ 1) (hX₂ : ‖X₂‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hT : ‖T‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : ‖D‖ = 1) (hne : X₁ - X₂ ≠ 0)
    (hA : (Y₁ - Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (S + X₁ + X₂) + b))
    (hB : (Y₁ + Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (T + X₁ + X₂) + b))
    (hsym : (X₁ - X₂) ^ 2 * (S + T - 2 * X₂) =
      (6 * X₂ ^ 2 + b * X₂ + c / 2) * (X₁ - X₂) + Y₂ ^ 2)
    (hdisc : 4 * D = Y₂ ^ 2 * (36 * (12 * X₂ + b) * (6 * X₂ ^ 2 + b * X₂ + c / 2)
        - 108 * Y₂ ^ 2 - (12 * X₂ + b) ^ 3) +
      (6 * X₂ ^ 2 + b * X₂ + c / 2) ^ 2 * ((12 * X₂ + b) ^ 2 - 32 * (6 * X₂ ^ 2 + b * X₂ + c / 2))) :
    ‖X₁ - X₂‖ = 1 := by
  have hc2 : ‖c / 2‖ ≤ 1 := by rw [norm_div, hp2, div_one]; exact hc
  set d := X₁ - X₂ with hd
  set H := 6 * X₂ ^ 2 + b * X₂ + c / 2 with hH
  set K := 12 * X₂ + b with hK
  have h1 : ‖d‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le hX₁ hX₂
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hne
  have hfour : ∀ {W : ℂ_[p]}, ‖W‖ ≤ 1 → ‖4 * (W + X₁ + X₂) + b‖ ≤ 1 := fun hW =>
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 4)
      (padicComplex_norm_add_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hW hX₁) hX₂)) hb
  have hsq : ∀ {Y W : ℂ_[p]}, Y ^ 2 = d ^ 2 * W → ‖W‖ ≤ 1 → ‖Y‖ ≤ ‖d‖ := fun {Y W} hY hW => by
    have : ‖Y‖ ^ 2 ≤ ‖d‖ ^ 2 := by
      rw [← norm_pow, hY, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) hW
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hm := hsq hA (hfour hS)
  have hp := hsq hB (hfour hT)
  have hY₂ : ‖Y₂‖ ≤ ‖d‖ := by
    have h2 : 2 * Y₂ = (Y₁ + Y₂) - (Y₁ - Y₂) := by ring
    have := padicComplex_norm_sub_le_of_norm_le hp hm
    rwa [← h2, norm_mul, hp2, one_mul] at this
  have hX₂' : ‖2 * X₂‖ ≤ 1 := padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 2) hX₂
  have hHd : ‖H‖ ≤ ‖d‖ := by
    have heq : H * d = d ^ 2 * (S + T - 2 * X₂) - Y₂ ^ 2 := by linear_combination -hsym
    have hST : ‖S + T - 2 * X₂‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hS hT) hX₂'
    have : ‖H‖ * ‖d‖ ≤ ‖d‖ * ‖d‖ := by
      rw [← norm_mul, heq]
      refine padicComplex_norm_sub_le_of_norm_le ?_ ?_
      · rw [norm_mul, norm_pow]
        nlinarith [norm_nonneg (S + T - 2 * X₂), sq_nonneg ‖d‖]
      · rw [norm_pow]
        nlinarith [norm_nonneg Y₂]
    exact le_of_mul_le_mul_right this hdpos
  have hK1 : ‖K‖ ≤ 1 :=
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 12) hX₂) hb
  have hH1 : ‖H‖ ≤ 1 := hHd.trans h1
  have hα : ‖Y₂ ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg Y₂]
  have hH2 : ‖H ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg H]
  have hP : ‖36 * K * H - 108 * Y₂ ^ 2 - K ^ 3‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_sub_le_of_norm_le
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 36) hK1) hH1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 108) hα.le))
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
  have hQ : ‖K ^ 2 - 32 * H‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 32) hH1)
  have hlt4 : ‖4 * D‖ < 1 := by
    rw [hdisc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hP).trans_lt hα
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hQ).trans_lt hH2
  have h4 : ‖4 * D‖ = 1 := by
    rw [norm_mul, hD, show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, hp2]
    norm_num
  linarith

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_two_eq_one_of_ne_two (h : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h1 : ‖algebraMap ℚ_[p] ℂ_[p] 2‖ = ‖(2 : ℚ_[p])‖ := norm_algebraMap' _ _
  rw [map_ofNat] at h1
  rw [h1]
  have h2 : ‖(2 : ℚ_[p])‖ = ‖((2 : ℤ) : ℤ_[p])‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; norm_num
  rw [h2]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
  have : p ∣ 2 := by exact_mod_cast hlt
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this


open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
theorem _root_.GlobalTheory.Klein.norm_weierstrassP_sub_eq_one (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (L : PeriodPair) (r : ℂ)
    (hG : _root_.GlobalTheory.Klein.Good ι L r) (u v : ℂ) (hu : _root_.GlobalTheory.Klein.Red ι L r u)
    (hv : _root_.GlobalTheory.Klein.Red ι L r v)
    (h₁ : _root_.GlobalTheory.Klein.Red ι L r (u + v))
    (h₂ : _root_.GlobalTheory.Klein.Red ι L r (u - v)) :
    ‖ι (L.weierstrassP u - L.weierstrassP v)‖ = 1 := by
  obtain ⟨hp, h12r, hc, -, hΔ⟩ := hG
  obtain ⟨hu, hXu⟩ := hu
  obtain ⟨hv, hXv⟩ := hv
  obtain ⟨hs, hS⟩ := h₁
  obtain ⟨ht, hT⟩ := h₂
  have hne : L.weierstrassP u ≠ L.weierstrassP v := by
    rw [Ne, _root_.GlobalTheory.weierstrassP_eq_iff L hu hv]
    rintro (h | h)
    exacts [ht h, hs h]
  have hd : L.weierstrassP u - L.weierstrassP v ≠ 0 := sub_ne_zero.2 hne
  have hA := (_root_.GlobalTheory.weierstrassP_add L hu hv hne).1
  have hnv : -v ∉ L.lattice := fun h => hv (by simpa using neg_mem h)
  have hne' : L.weierstrassP u ≠ L.weierstrassP (-v) := by rwa [PeriodPair.weierstrassP_neg]
  have hB := (_root_.GlobalTheory.weierstrassP_add L hu hnv hne').1
  rw [PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg, ← sub_eq_add_neg,
    sub_neg_eq_add] at hB
  have hsym := _root_.GlobalTheory.weierstrassP_add_add_sub L hu hv hne
  have hY := L.derivWeierstrassP_sq v hv
  set x₁ := L.weierstrassP u
  set x₂ := L.weierstrassP v
  set s := L.weierstrassP (u + v)
  set t := L.weierstrassP (u - v)
  set y₁ := L.derivWeierstrassP u
  set y₂ := L.derivWeierstrassP v
  have cA : (y₁ - y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((s - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hA]; field_simp; ring
  have cB : (y₁ + y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((t - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hB]; field_simp; ring
  have cS : ((x₁ - r) - (x₂ - r)) ^ 2 * ((s - r) + (t - r) - 2 * (x₂ - r)) =
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) * ((x₁ - r) - (x₂ - r)) +
        y₂ ^ 2 := by
    have e : s = (6 * x₂ ^ 2 - L.g₂ / 2) / (x₁ - x₂) + y₂ ^ 2 / (x₁ - x₂) ^ 2 - t + 2 * x₂ := by
      linear_combination hsym
    rw [e]; field_simp; ring
  have cD : 4 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) =
      y₂ ^ 2 * (36 * (12 * (x₂ - r) + 12 * r) *
          (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)
        - 108 * y₂ ^ 2 - (12 * (x₂ - r) + 12 * r) ^ 3) +
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) ^ 2 *
        ((12 * (x₂ - r) + 12 * r) ^ 2 -
          32 * (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)) := by
    rw [hY]; ring
  have key := norm_sub_eq_one_of_discriminant_relations (padicComplex_norm_two_eq_one_of_ne_two hp) hXu hXv hS hT h12r hc
    hΔ (Y₁ := ι y₁) (Y₂ := ι y₂)
    (by rw [← map_sub]; exact (map_ne_zero ι).2 (by rwa [sub_sub_sub_cancel_right]))
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cA)
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cB)
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cS)
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cD)
  rwa [← map_sub, sub_sub_sub_cancel_right] at key

end GlobalTheory.Klein
end

section

open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocFlat.CFac

def prodSBBil (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X →ₗ[ℂ] SB Y →ₗ[ℂ] SB (X × Y) :=
  LinearMap.mk₂ ℂ prodSB
    (fun f f' g => by ext p; simp [add_mul])
    (fun c f g => by ext p; simp [mul_assoc])
    (fun f g g' => by ext p; simp [mul_add])
    (fun c f g => by ext p; simp; ring)

def tensorToProd (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X ⊗[ℂ] SB Y →ₗ[ℂ] SB (X × Y) := TensorProduct.lift (prodSBBil X Y)

theorem tensorToProd_tmul {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) :
    tensorToProd X Y (f ⊗ₜ g) = prodSB f g := by
  simp [tensorToProd, prodSBBil]

theorem tensorToProd_injective (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Function.Injective (tensorToProd X Y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB X)
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i n => b i ⊗ₜ n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ x y, ∑ i ∈ c.support, (b i).1 x * (c i).1 y = 0 := by
    intro x y
    have := congrArg (fun F : SB (X × Y) => F.1 (x, y)) ht

    simp only [ht', Finsupp.sum, map_sum, tensorToProd_tmul] at this
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hzero : c = 0 := by
    ext i y
    by_cases hi : i ∈ c.support
    · have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support (fun i => (c i).1 y)
        (by
          ext x
          simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
          rw [← hm x y]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
      simpa using hli
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

end GlobalTheory.LocFlat.CFac

namespace GlobalTheory.LocFlat.CFac

theorem exists_linear_of_bilinear_prodSB : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  intro X Y _ _ M _ _ B
  let m := tensorToProd X Y
  let e := LinearEquiv.ofInjective m (tensorToProd_injective X Y)
  let l₀ : LinearMap.range m →ₗ[ℂ] M := (TensorProduct.lift B).comp e.symm.toLinearMap
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  refine ⟨l, fun f g => ?_⟩
  have hmem : prodSB f g = ((e (f ⊗ₜ g) : LinearMap.range m) : SB (X × Y)) := by
    simp [e, LinearEquiv.ofInjective_apply, m, tensorToProd_tmul]
  have := LinearMap.congr_fun hl (e (f ⊗ₜ g))
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, l₀,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul] at this
  rw [hmem, this]

end GlobalTheory.LocFlat.CFac
end
end

section

open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) → (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | exact GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs <;> assumption)
end
