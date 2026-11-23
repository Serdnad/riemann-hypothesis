module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem one_add_col_mul_rank_one_mulVec {n : ℕ} (u w v : Fin n → ℂ) :
    (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit w) *ᵥ v = v + (w ⬝ᵥ v) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

private theorem hv_sub_smul_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y z : Fin n → ℂ) (a : ℂ) :
    hv M (x - a • y) z = hv M x z - a * hv M y z := by
  simp [hv, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]

theorem UpperTheory.Gal.W2.lineBasis_of :
    UpperTheory.Gal.W2.LineBasis := by
  intro n M z _ hpos
  have hz : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    have : z = 0 := funext h
    subst this
    simp [hv] at hpos
  obtain ⟨i₀, hi₀⟩ := hz
  have hφ : hv M z z ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  set e : Fin n → ℂ := Pi.single i₀ 1 with he
  set c : Fin n → ℂ := fun j => if j = i₀ then 0 else hv M (Pi.single j 1) z / hv M z z with hc
  refine ⟨i₀, (1 + Matrix.replicateCol Unit (z - e) * Matrix.replicateRow Unit e) *
    (1 + Matrix.replicateCol Unit (-e) * Matrix.replicateRow Unit c), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    have h1 : e ⬝ᵥ (z - e) = z i₀ - 1 := by
      simp [he, dotProduct_sub]
    have h2 : c ⬝ᵥ (-e) = 0 := by
      simp [he, hc]
    rw [h1, h2]
    simpa using hi₀
  · rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ e = 0 := by simp [he, hc]
    have h3 : e ⬝ᵥ e = 1 := by simp [he]
    rw [h2]
    simp [h3, he]
  · intro i hi
    rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ (Pi.single i 1 : Fin n → ℂ) = hv M (Pi.single i 1) z / hv M z z := by
      simp [hc, hi]
    have h3 : e ⬝ᵥ ((Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e)) =
        - (hv M (Pi.single i 1) z / hv M z z) := by
      simp [he, dotProduct_add, Pi.single_apply, hi]
    rw [h2, h3]
    have h4 : (Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e) +
        (-(hv M (Pi.single i 1) z / hv M z z)) • (z - e) =
        (Pi.single i 1 : Fin n → ℂ) - (hv M (Pi.single i 1) z / hv M z z) • z := by
      ext a
      simp
      ring
    rw [h4, hv_sub_smul_left]
    field_simp
    ring
end

section

open scoped Matrix

namespace UpperTheory.Gal.W2

theorem sN_of : SN := by
  intro F K _ _ n τ ψ hψ
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp, fun M => Subsingleton.elim _ _⟩
  have i0 : Fin n := ⟨0, hn⟩
  haveI : Nonempty (Fin n) := ⟨i0⟩
  have hsc : ∀ {R : Type} [Field R] (i k : Fin n) (x : R),
      Matrix.single i k x = Matrix.scalar (Fin n) x * Matrix.single i k 1 := by
    intro R _ i k x
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hsum1 : ∀ {R : Type} [Field R], (∑ k : Fin n, Matrix.single k k (1 : R)) = 1 := by
    intro R _
    ext r s
    rw [Matrix.sum_apply, Finset.sum_eq_single r]
    · by_cases h : r = s
      · subst h
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, Matrix.one_apply, h]
    · intro k _ hk
      simp [Matrix.single_apply, hk]
    · simp
  have hEE : ∀ i j j' k, ψ (Matrix.single i j 1) * ψ (Matrix.single j' k 1) =
      if j = j' then ψ (Matrix.single i k 1) else 0 := by
    intro i j j' k
    rw [← map_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, map_zero]
  have hP : ψ (Matrix.single i0 i0 1) ≠ 0 := by
    intro h0
    have hk : ∀ k, ψ (Matrix.single k k 1) = 0 := by
      intro k
      have e1 : ψ (Matrix.single k k 1) = ψ (Matrix.single k i0 1) * ψ (Matrix.single i0 i0 1) *
          ψ (Matrix.single i0 k 1) := by
        rw [hEE k i0 i0 i0, if_pos rfl, hEE k i0 i0 k, if_pos rfl]
      rw [e1, h0, mul_zero, zero_mul]
    have h1 : ψ 1 = 0 := by

      rw [← hsum1 (R := F), map_sum]
      exact Finset.sum_eq_zero fun k _ => hk k
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨a, b, hab⟩ : ∃ a b, ψ (Matrix.single i0 i0 1) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (Matrix.ext h)
  have hL : ∀ i k, ψ (Matrix.single i k 1) * (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.mul_sum]
    have l1 : ∀ j, ψ (Matrix.single i k 1) * (ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
        if k = j then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [← mul_assoc, hEE]
      split_ifs with h
      · subst h
        rfl
      · rw [zero_mul]
    simp only [l1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hR : ∀ i k, (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) * Matrix.single i k 1 =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.sum_mul]
    have l2 : ∀ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1 * Matrix.single i k 1 =
        if j = i then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [mul_assoc]
      split_ifs with h
      · subst h
        rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, mul_zero]
    simp only [l2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1, ?_, ?_⟩
  · have hTS : (∑ k, Matrix.single k a (ψ (Matrix.single i0 i0 1) a b)⁻¹ * ψ (Matrix.single i0 k 1)) *
        (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) = 1 := by
      rw [Finset.sum_mul, ← hsum1 (R := K)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, hL, ← mul_assoc, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    have hd := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact right_ne_zero_of_mul_eq_one hd
  · intro M
    have hM : M = ∑ i, ∑ k, Matrix.scalar (Fin n) (M i k) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single M]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k (M i k)
    have hMt : M.map τ = ∑ i, ∑ k, Matrix.scalar (Fin n) (τ (M i k)) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single (M.map τ)]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k _
    rw [hMt]
    conv_lhs => rw [hM]

    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hψ, mul_assoc, hL, ← hR, ← mul_assoc, ← mul_assoc,
      (Matrix.scalar_commute (τ (M i k)) (fun r' => Commute.all _ r') _).eq]

end UpperTheory.Gal.W2
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p]) = ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w x) +
    ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w (IsCMField.complexConj G.F x))

def FInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), (∀ w, ‖(G.embW w x : PadicAlgCl p)‖ ≤ 1 ∧ ‖(G.embW w (IsCMField.complexConj G.F x) : PadicAlgCl p)‖ ≤ 1) →
    ∃ (m : ℕ) (c : 𝓞 G.F), m.Coprime p ∧ (c : G.F) = m * x

def EmbAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), ∃ (w : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
    (∀ x, τ x = σ (G.emb w x)) ∨ ∀ x, τ x = σ (G.emb w (IsCMField.complexConj G.F x))

def FApprox : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : ∀ w : Fin G.m, G.Fw w) (e : ℝ), 0 < e → ∃ x : G.F, ∀ w, ‖((G.embW w x - a w : G.Fw w) : PadicAlgCl p)‖ < e ∧
    ‖((G.embW w (IsCMField.complexConj G.F x) - b w : G.Fw w) : PadicAlgCl p)‖ < e

def TrDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m), ∃ d : G.Fw w, d ≠ 0 ∧ ∀ a : G.Fw w,
    (∀ z : G.Fw w, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] (G.Fw w) (a * z)‖ ≤ 1) ↔ ‖((a * d : G.Fw w) : PadicAlgCl p)‖ ≤ 1

def KpMem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : Gp G), inclG G 1 g ∈ KHT p G.m G.n 1 G.Fw ↔ IntPt g

def LocLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m) (s : Finset (Fin G.n → G.Fw w)), Submodule.span (G.Fw w) (s : Set (Fin G.n → G.Fw w)) = ⊤ →
    ∃ g : GL (Fin G.n) (G.Fw w), ∀ z : Fin G.n → G.Fw w,
      (∀ i, ‖(((((g⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z) i : G.Fw w) : PadicAlgCl p)‖ ≤ 1) ↔
        ∃ a : (Fin G.n → G.Fw w) → G.Fw w, (∀ y, ‖(a y : PadicAlgCl p)‖ ≤ 1) ∧ z = ∑ y ∈ s, a y • y

def PFrameEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∀ β : G.Cˣ, sh G β = β → Nonempty (PFrame L β)

def PLatOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)) (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ →
    (∀ c : D.O, ∀ x ∈ M, actQ D c x ∈ M) → (∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M) → (∀ x ∈ s, p ^ k • x ∈ M) →
    (∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))) → IsPLat D M

def MemDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∃ d : ∀ w : Fin G.m, G.Fw w, (∀ w, d w ≠ 0) ∧ ∀ a : Loc G,
    ((∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w))

def PkLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ g : Gp G, ∃ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) ∧ IsPLat D M

def PkEquiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (y : GlobalTheory.LKCx.grp G β) (g : Gp G) (x : VQ D), A.Mem (locC G (y : G.Cˣ × ℚˣ) * g) (actY L y x) ↔ A.Mem g x

def PkPerf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g : Gp G) (s : ℚ), ‖(s : ℚ_[p]) * (g.1 : ℚ_[p])‖ = 1 → ∀ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) → PerfAt L β s M

def PkInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g g' : Gp G), (∀ x, A.Mem g x ↔ A.Mem g' x) ↔ IntPt (g⁻¹ * g')

def PkOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ (M : AddSubgroup (VQ D)) (s : ℚ), IsPLat D M → 0 < s → PerfAt L β s M → ∃ g : Gp G, ∀ x, x ∈ M ↔ A.Mem g x

def OOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O)

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.hermOfJ_of :
    UpperTheory.Gal.W2.HermOfJ := by
  intro g E halt hI hpos
  have hskew : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
    linarith
  have hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x := by
    intro x
    rw [smul_smul, Complex.I_mul_I]
    simp
  have hcomm : ∀ x y : Fin g → ℂ, E (Complex.I • x) y = E (Complex.I • y) x := by
    intro x y
    have h := hI (Complex.I • x) y
    rw [hII, map_neg, LinearMap.neg_apply] at h
    rw [← h, hskew x]
    ring
  let H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y => ⟨E (Complex.I • x) y, E x y⟩
  have hsym : ∀ x y, H y x = star (H x y) := by
    intro x y
    apply Complex.ext
    · simpa [H] using hcomm y x
    · simpa [H] using hskew y x
  have hadd : ∀ a b y, H (a + b) y = H a y + H b y := by
    intro a b y
    apply Complex.ext <;> simp [H, smul_add]
  have hsmulI : ∀ x y, H (Complex.I • x) y = Complex.I * H x y := by
    intro x y
    apply Complex.ext
    · simp [H, hII]
    · simp [H]
  have hsmulR : ∀ (r : ℝ) x y, H (r • x) y = (r : ℂ) * H x y := by
    intro r x y
    apply Complex.ext
    · simp [H, smul_comm Complex.I r x]
    · simp [H]
  have hsmul : ∀ (c : ℂ) x y, H (c • x) y = c * H x y := by
    intro c x y
    have hc : c • x = c.re • x + c.im • (Complex.I • x) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hc, hadd, hsmulR, hsmulR, hsmulI]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let e : Fin g → Fin g → ℂ := fun i j => if i = j then 1 else 0
  have hexp : ∀ x y, H x y = ∑ i, x i * H (e i) y := by
    intro x y
    let f : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun x => H x y
        map_add' := fun a b => hadd a b y
        map_smul' := fun c a => by simpa using hsmul c a y }
    simpa [f, e] using LinearMap.pi_apply_eq_sum_univ f x
  have hform : ∀ x y, hermForm (Matrix.of fun i j => H (e i) (e j)) x y = H x y := by
    intro x y
    rw [hexp x y]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hsym y (e i), hexp y (e i), star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', ← hsym (e j) (e i), mul_comm]
  refine ⟨Matrix.of fun i j => H (e i) (e j), ?_, ?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.of_apply]
    rw [← hsym]
  · intro z hz
    rw [hform]
    exact hpos z hz
  · intro x y
    rw [hform]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem add_expand {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A) (w : V) :
    f w = ∑ i, ((b.repr w i : ℚ) : ℝ) • f (b i) := by
  conv_lhs => rw [← b.sum_repr w]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := map_ratCast_smul f ℚ ℝ (b.repr w i) (b i)
  simpa using h

private theorem span_basis {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A)
    (hs : Submodule.span ℝ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun i => f (b i))) := by
  rw [← hs]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  rw [add_expand b f w]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem equiv_of_spans {V A B : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A] [AddCommGroup B] [Module ℝ B]
    [FiniteDimensional ℝ B] (th : V →+ A) (Q : V →+ B)
    (hA : Submodule.span ℝ (Set.range th) = ⊤) (hB : Submodule.span ℝ (Set.range Q) = ⊤)
    (dA : Module.finrank ℝ A = Module.finrank ℚ V) (dB : Module.finrank ℝ B = Module.finrank ℚ V) :
    ∃ R : A ≃ₗ[ℝ] B, ∀ w, Q w = R (th w) := by
  let b := Module.finBasis ℚ V
  let bA : Module.Basis (Fin (Module.finrank ℚ V)) ℝ A :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => th (b i)) (span_basis b th hA) (by simp [dA])
  let bB : Module.Basis (Fin (Module.finrank ℚ V)) ℝ B :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => Q (b i)) (span_basis b Q hB) (by simp [dB])
  refine ⟨bA.equiv bB (Equiv.refl _), fun w => ?_⟩

  rw [add_expand b th w, add_expand b Q w, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  have h1 : bA i = th (b i) := by simp [bA]
  have h2 : bB i = Q (b i) := by simp [bB]
  rw [← h1, ← h2, Module.Basis.equiv_apply]
  rfl

theorem UpperTheory.Gal.W2.perExt_of :
    UpperTheory.Gal.W2.PerExt := by
  intro p _ D G L A β ρ Q hQ
  haveI : Module.Finite ℤ D.La := D.finLa
  haveI : Module.Finite ℚ (VQ D) := Module.Finite.base_change ℤ ℚ D.La
  refine equiv_of_spans A.th Q A.span hQ.2.1 A.dim ?_
  rw [← A.dim, A.dimg]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
end

section

namespace UpperTheory.Gal.W2

theorem intMult_of : IntMult := by
  unfold IntMult
  intro O _ bar D' ga r hr h
  let Iv : Ideal ℤ := Ideal.span {x | ∃ u u', D'.EF u u' = x}
  have hval : ∀ u u', D'.EF u u' ∈ Iv := fun u u' => Ideal.subset_span ⟨u, u', rfl⟩
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal Iv).principal
  have hc' : Iv = Ideal.span {c} := hc
  have key : ∀ x ∈ Iv, ∃ y ∈ Iv, (y : ℚ) = r * x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, u', rfl⟩ := hx
      exact ⟨_, hval (ga u) (ga u'), h u u'⟩
    | zero => exact ⟨0, Iv.zero_mem, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨y, hy, e⟩ := iha
      obtain ⟨z, hz, e'⟩ := ihb
      exact ⟨y + z, Iv.add_mem hy hz, by push_cast; rw [e, e']; ring⟩
    | smul a x _ ih =>
      obtain ⟨y, hy, e⟩ := ih
      exact ⟨a * y, Iv.mul_mem_left a hy, by simp only [smul_eq_mul]; push_cast; rw [e]; ring⟩
  by_cases hc0 : c = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have hz : ∀ u u', D'.EF u u' = 0 := fun u u' => by
      have := hval u u'
      rw [hc', hc0, Ideal.mem_span_singleton] at this
      simpa using this
    rw [hz, hz, mul_zero]
  · have hcI : c ∈ Iv := by rw [hc']; exact Ideal.mem_span_singleton_self c
    obtain ⟨y, hy, e⟩ := key c hcI
    rw [hc', Ideal.mem_span_singleton] at hy
    obtain ⟨m, rfl⟩ := hy
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hm : (m : ℚ) = r := by
      push_cast at e
      have : (c : ℚ) * m = c * r := by rw [e]; ring
      exact mul_left_cancel₀ hcq this
    refine ⟨m, ?_, fun u u' => ?_⟩
    · have : (0 : ℚ) < m := hm ▸ hr
      exact_mod_cast this
    · have := h u u'
      rw [← hm] at this
      exact_mod_cast this

end UpperTheory.Gal.W2
end
