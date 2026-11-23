module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorCoreA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle003
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

noncomputable section

open MvPolynomial Matrix

namespace PositivityTheory.Rg.Sw.SP.Mi

open scoped IsMulCommutative

variable {R : Type} [CommRing R]

def Aop (α : R) (ρ : ℕ) : Matrix (Fin ρ) (Fin ρ) (Algebra.adjoin R (gens α ρ)) :=
  fun p q => ⟨opE α p q, Algebra.subset_adjoin ⟨(p, q), rfl⟩⟩

theorem coe_det_sub (α : R) (ρ r : ℕ) (I J : Fin r → Fin ρ) :
    letI : IsMulCommutative (Algebra.adjoin R (gens α ρ)) :=
      Algebra.isMulCommutative_adjoin R fun a ha b hb _ => gens_comm α ρ a ha b hb
    ((((Aop α ρ).submatrix I J).det : Algebra.adjoin R (gens α ρ)) : Module.End R (Pm R ρ)) =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : R) •
        ((List.finRange r).map (fun k => opE α (I k) (J (σ k)))).prod := by
  let : IsMulCommutative (Algebra.adjoin R (gens α ρ)) :=
    Algebra.isMulCommutative_adjoin R fun a ha b hb _ => gens_comm α ρ a ha b hb
  rw [← det_transpose, det_apply']
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Subalgebra.coe_mul, ← List.prod_ofFn, coe_list_prod, List.ofFn_eq_map, List.map_map]
  have hε : (((((Equiv.Perm.sign σ : ℤ) : Algebra.adjoin R (gens α ρ))) : Module.End R (Pm R ρ))) =
      ((Equiv.Perm.sign σ : ℤ) : Module.End R (Pm R ρ)) := by push_cast; rfl
  rw [hε, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul R]
  rfl

theorem detE_eq_sum (α : R) (ρ : ℕ) :
    detE α = ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : R) •
      ((List.finRange ρ).map (fun k => opE α k (σ k))).prod := by
  unfold detE
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [foldr_eq_prod (fun k => opE α k (σ k))]

theorem prod_ren (α : R) {r s : ℕ} (I J : Fin r ↪ Fin s) (σ : Equiv.Perm (Fin r)) (l : List (Fin r)) (f : Pm R r) :
    (l.map (fun k => opE α (I k) (J (σ k)))).prod (ren I J f) = ren I J ((l.map (fun k => opE α k (σ k))).prod f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, ih]
    exact renInt R r s I J α a (σ a) _

theorem core : Core := by
  intro R _ ρ α
  induction ρ with
  | zero =>
    rw [detE_eq_sum]
    simp
  | succ ρ ih =>
    let : IsMulCommutative (Algebra.adjoin R (gens α (ρ + 1))) :=
      Algebra.isMulCommutative_adjoin R fun a ha b hb _ => gens_comm α (ρ + 1) a ha b hb
    have hfull := coe_det_sub α (ρ + 1) (ρ + 1) id id
    simp only [submatrix_id_id, id] at hfull
    rw [detE_eq_sum, ← hfull, det_succ_row_zero, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
    have hsub : ∀ j : Fin (ρ + 1),
        ((((Aop α (ρ + 1)).submatrix Fin.succ j.succAbove).det : Algebra.adjoin R (gens α (ρ + 1))) :
          Module.End R (Pm R (ρ + 1))) 1 =
        C (∏ i ∈ Finset.range ρ, (α - (i : R))) * ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det := by
      intro j
      have h := coe_det_sub α (ρ + 1) ρ Fin.succ j.succAbove
      rw [h, LinearMap.sum_apply]
      have h1 : (1 : Pm R (ρ + 1)) = ren (Fin.succEmb ρ) (Fin.succAboveEmb j) 1 := by simp
      rw [h1]
      have h2 : ∀ σ : Equiv.Perm (Fin ρ),
          (((Equiv.Perm.sign σ : ℤ) : R) • ((List.finRange ρ).map (fun k => opE α (Fin.succ k) (j.succAbove (σ k)))).prod)
            (ren (Fin.succEmb ρ) (Fin.succAboveEmb j) 1) =
          ren (Fin.succEmb ρ) (Fin.succAboveEmb j) ((((Equiv.Perm.sign σ : ℤ) : R) •
            ((List.finRange ρ).map (fun k => opE α k (σ k))).prod) 1) := by
        intro σ
        rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
        congr 1
        exact prod_ren α (Fin.succEmb ρ) (Fin.succAboveEmb j) σ (List.finRange ρ) 1
      simp_rw [h2]

      rw [← map_sum, ← LinearMap.sum_apply, ← detE_eq_sum, ih, map_mul, AlgHom.map_det]
      congr 1
      · rw [map_prod, map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [ren]
      · congr 1
        ext p q
        simp [ren, Xm]
    have hterm : ∀ j : Fin (ρ + 1),
        ((((-1) ^ (j : ℕ) * Aop α (ρ + 1) 0 j * ((Aop α (ρ + 1)).submatrix Fin.succ j.succAbove).det :
            Algebra.adjoin R (gens α (ρ + 1))) : Module.End R (Pm R (ρ + 1))) 1) =
        C (∏ i ∈ Finset.range ρ, (α - (i : R))) * ((-1) ^ (j : ℕ) *
          (C α * X (j, 0) * ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det +
            del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det)) := by
      intro j
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
        Subalgebra.coe_one, mul_apply_eq_comp, mul_apply_eq_comp, hsub]
      have hA : ((Aop α (ρ + 1) 0 j : Algebra.adjoin R (gens α (ρ + 1))) : Module.End R (Pm R (ρ + 1))) = opE α 0 j := rfl
      rw [hA, opE_C_mul]
      have e1 : ((-1 : Module.End R (Pm R (ρ + 1))) ^ (j : ℕ)) = ((-1 : R) ^ (j : ℕ)) • LinearMap.id := by
        rw [← Module.End.one_eq_id, ← neg_one_smul R (1 : Module.End R (Pm R (ρ + 1))), smul_pow, one_pow]
      rw [e1, LinearMap.smul_apply, LinearMap.id_apply]
      change ((-1 : R) ^ (j : ℕ)) • (C (∏ i ∈ Finset.range ρ, (α - (i : R))) *
          (C α * X (j, 0) * ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det +
            del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det)) = _
      rw [smul_eq_C_mul, map_pow, map_neg, map_one]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hcol := det_succ_column_zero (Xm R (ρ + 1))
    have e2 : ∑ j : Fin (ρ + 1), (-1 : Pm R (ρ + 1)) ^ (j : ℕ) * (C α * X (j, 0) *
        ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det) = C α * (Xm R (ρ + 1)).det := by
      rw [hcol, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Xm]
      ring
    rw [e2, sum_del, Finset.prod_range_succ]
    simp only [map_prod, map_sub, map_natCast]
    ring

end PositivityTheory.Rg.Sw.SP.Mi
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def SPrime : Prop :=
  ∀ (n m : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → m < n → ∀ (t : ℝ), t ≠ 0 → ∀ β : E n, (herm β).det ≠ 0 →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧
      (∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re → Integrable (fun y => cls s z m 0 1 y * chr t β y) ∧
        W z = ∫ y, cls s z m 0 1 y * chr t β y) ∧
      ∀ j < n - m, iteratedDeriv j W 0 = 0

abbrev Fm (n : ℕ) := MvPolynomial (Bool × Fin n × Fin n) (Polynomial ℂ)

def yv (b : Bool) (i j : Fin n) : Fm n := MvPolynomial.X (b, i, j)

def opH (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  let c : ℂ := if b then Complex.I * s else -(Complex.I * s)
  let α : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X
  (-(c : ℂ)) • (LinearMap.mulLeft ℂ (MvPolynomial.C α * yv b l k)).restrictScalars ℂ +
    ∑ a : Fin n, ∑ d : Fin n, (-(c : ℂ)) •
      (LinearMap.mulLeft ℂ (yv b a k * yv b l d) ∘ₗ (MvPolynomial.pderiv (b, a, d)).toLinearMap.restrictScalars ℂ)

def opD (s : ℂ) (m : ℕ) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n := opH s m false k l + opH s m true k l

def cayF (s : ℂ) (m : ℕ) : Fm n →ₗ[ℂ] Fm n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => opD s m k (σ k) ∘ₗ g) LinearMap.id

def DivZ (i : ℕ) (Q : Fm n) : Prop := ∀ e, Polynomial.X ^ i ∣ AddMonoidAlgebra.coeff Q e

def Comm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n),
    opH s m b k l ∘ₗ opH s m b' k' l' = opH s m b' k' l' ∘ₗ opH s m b k l

def Bridge : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m N : ℕ) (z : ℂ) (B : MC n), B ∈ OmS s →
    (cay^[N] (clsC s z m 0 1)) B = clsC s z m 0 1 B *
      MvPolynomial.eval (fun k : Bool × Fin n × Fin n => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
        else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) (MvPolynomial.map (Polynomial.evalRingHom z) ((cayF s m)^[N] 1))

def minorOp (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : Fm n →ₗ[ℂ] Fm n :=
  ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange ρ).foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id

def MinorZ : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m i N : ℕ), i ≤ N → ∀ (I J : Fin (m + i) ↪ Fin n),
    DivZ i ((minorOp s m false I J)^[N] 1)

def MinorZ' : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m j N : ℕ), j ≤ N → ∀ (I J : Fin j ↪ Fin n),
    DivZ j ((minorOp s m true I J)^[N] 1)

abbrev PAB (n : ℕ) := MvPolynomial (Bool × Fin n × Fin n) ℂ

def minorPolynomial (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : PAB n :=
  Matrix.det (fun p q : Fin ρ => (MvPolynomial.X (b, I p, J q) : PAB n))

def Null : Prop :=
  ∀ (n m : ℕ), m < n → ∀ N₀ : ℕ, ∃ N : ℕ,
    (Matrix.det (fun p q : Fin n => (MvPolynomial.X (false, p, q) + MvPolynomial.X (true, p, q) : PAB n))) ^ N ∈
      Ideal.span {x : PAB n | ∃ i j : ℕ, i + j = n - m ∧
        ((i = 0 ∧ j = 0 ∧ x = 1) ∨
         (i = 0 ∧ 0 < j ∧ ∃ (I J : Fin j ↪ Fin n), x = minorPolynomial true I J ^ N₀) ∨
         (0 < i ∧ j = 0 ∧ ∃ (I J : Fin (m + i) ↪ Fin n), x = minorPolynomial false I J ^ N₀) ∨
         (0 < i ∧ 0 < j ∧ ∃ (I J : Fin (m + i) ↪ Fin n) (I' J' : Fin j ↪ Fin n),
            x = minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀))}

def CayDiv : Prop :=
  ∀ (n m : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → m < n → ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → DivZ (n - m) ((cayF s m)^[N] (1 : Fm n))

def MinorFormula : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (m : ℕ) (b : Bool) (ρ N : ℕ) (I J : Fin ρ ↪ Fin n),
    (minorOp s m b I J)^[N] 1 =
      MvPolynomial.C (Polynomial.C (((if b then Complex.I * s else -(Complex.I * s)) ^ ρ) ^ N) *
        ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ,
          (-(if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X) - Polynomial.C ((l : ℂ) - i))) *
      (Matrix.det (fun p q : Fin ρ => yv b (J p) (I q))) ^ N

def CayDivOf : Prop := Comm → MinorZ → MinorZ' → Null → CayDiv

def SPrimeOf : Prop := Bridge → CayDiv → SPrime

end PositivityTheory.Rg.Sw.SP
end
end
