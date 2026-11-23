module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SuccAboveEqFc
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

theorem dh_dh {a b : ℕ} (F : Bi P Q (a + 1) b) : dh (dh F) = 0 := by
  funext x y
  exact congrFun (dc_dc (fun x' => F x' y)) x

theorem dv_dv {a b : ℕ} (F : Bi P Q a (b + 1)) : dv (dv F) = 0 := by
  funext x y
  exact congrFun (dc_dc (F x)) y

theorem dh_dv {a b : ℕ} (F : Bi P Q (a + 1) (b + 1)) : dh (dv F) = dv (dh F) := by
  funext x y
  simp only [dh, dv, dc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dh_add {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F + G) = dh F + dh G := by
  funext x y; simp only [dh, Pi.add_apply, dc, mul_add, Finset.sum_add_distrib]

theorem dh_sub {a b : ℕ} (F G : Bi P Q (a + 1) b) : dh (F - G) = dh F - dh G := by
  funext x y
  exact congrFun (dc_sub (fun x' => F x' y) (fun x' => G x' y)) x

theorem dh_smul {a b : ℕ} (r : ℝ) (F : Bi P Q (a + 1) b) : dh (r • F) = r • dh F := by
  funext x y
  exact congrFun (dc_smul r (fun x' => F x' y)) x

theorem dv_sub {a b : ℕ} (F G : Bi P Q a (b + 1)) : dv (F - G) = dv F - dv G := by
  funext x y
  exact congrFun (dc_sub (F x) (G x)) y

theorem dv_smul {a b : ℕ} (r : ℝ) (F : Bi P Q a (b + 1)) : dv (r • F) = r • dv F := by
  funext x y
  exact congrFun (dc_smul r (F x)) y

section Inv

variable (pr : P →* Q)

theorem PInv.sub {a b : ℕ} {F G : Bi P Q a b} (hF : PInv pr F) (hG : PInv pr G) : PInv pr (F - G) := by
  intro g x y
  show F _ _ - G _ _ = F x y - G x y
  rw [hF g x y, hG g x y]

theorem PInv.smul {a b : ℕ} (r : ℝ) {F : Bi P Q a b} (hF : PInv pr F) : PInv pr (r • F) := by
  intro g x y
  show r * F _ _ = r * F x y
  rw [hF g x y]

theorem PInv.dh {a b : ℕ} {F : Bi P Q (a + 1) b} (hF : PInv pr F) : PInv pr (dh F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dh PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g (fun j => x (i.succAbove j)) y

theorem PInv.dv {a b : ℕ} {F : Bi P Q a (b + 1)} (hF : PInv pr F) : PInv pr (dv F) := by
  intro g x y
  unfold PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas.dv PositivityTheory.KB.SplitAffineSpectral.dc
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hF g x (fun j => y (i.succAbove j))

end Inv

theorem cons_mul {Z : Type} [Mul Z] {n : ℕ} (g a : Z) (x : Fin n → Z) :
    (fun i => g * (Fin.cons a x : Fin (n + 1) → Z) i) = Fin.cons (g * a) (fun i => g * x i) := by
  funext i; refine Fin.cases ?_ (fun k => ?_) i <;> simp

theorem row_exact (pr : P →* Q) {a b : ℕ} (F : Bi P Q (a + 2) (b + 1)) (hF : PInv pr F) (h : dh F = 0) :
    ∃ G : Bi P Q (a + 1) (b + 1), PInv pr G ∧ F = dh G := by
  have hcs : ∀ (c : Q) (u : Fin (a + 2) → Q) (k : Fin (a + 2)),
      (fun j => (Fin.cons c u : Fin (a + 3) → Q) (k.succ.succAbove j)) =
        Fin.cons c (fun j => u (k.succAbove j)) := by
    intro c u k
    funext j
    cases j using Fin.cases <;> simp [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
  refine ⟨fun x y => F (Fin.cons (pr (y 0)) x) y, ?_, ?_⟩
  · intro g x y
    show F (Fin.cons (pr (g * y 0)) (fun i => pr g * x i)) (fun j => g * y j) = F (Fin.cons (pr (y 0)) x) y
    rw [map_mul, ← cons_mul]
    exact hF g _ y
  · funext x y
    have h0 := congrFun (congrFun h (Fin.cons (pr (y 0)) x)) y
    simp only [dh, dc] at h0
    rw [Fin.sum_univ_succ] at h0
    simp only [hcs] at h0
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.cons_succ, Fin.val_succ,
      pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib] at h0
    show F x y = ∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y
    have h1 : F x y + -∑ i : Fin (a + 2), (-1) ^ (i : ℕ) * F (Fin.cons (pr (y 0)) (fun j => x (i.succAbove j))) y = 0 := h0
    linarith

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

theorem zz_smul (pr : P →* Q) {n : ℕ} (r : ℝ) (b : (Fin n → Q) → ℝ) (a c : ℕ) :
    zz pr (r • b) a c = r • zz pr b a c := rfl

theorem Wtop_smul (pr : P →* Q) {n : ℕ} (r : ℝ) (b : (Fin n → Q) → ℝ) :
    Wtop pr (r • b) = r • Wtop pr b := rfl

theorem QC.smul {n : ℕ} {b : (Fin (n + 1) → Q) → ℝ} (hb : QC b) (r : ℝ) : QC (r • b) := by
  refine ⟨fun g x => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hb.1 g x]
  · rw [dc_smul, hb.2, smul_zero]

def GoodS (pr : P →* Q) {p q : ℕ} (x : Bi P Q (p + 2) (q + 2)) : Prop :=
  ∃ n : ℕ, n = p + q + 2 ∧ ∃ b : (Fin (n + 1) → Q) → ℝ, QC b ∧
    ∃ (w : Bi P Q (p + 1) (q + 2)) (e : Bi P Q (p + 2) (q + 1)),
    PInv pr w ∧ dv w = 0 ∧ PInv pr e ∧ dh e = 0 ∧ x = dh (zz pr b (p + 1) (q + 2)) + dh w + dv e

def GoodT (pr : P →* Q) {q : ℕ} (x : Bi P Q 1 (q + 2)) : Prop :=
  ∃ b : (Fin (q + 2) → Q) → ℝ, QC b ∧ ∃ e : Bi P Q 1 (q + 1), PInv pr e ∧ dh e = 0 ∧ x = Wtop pr b + dv e

section Rec

variable (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g)
include hs

end Rec

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end

section

noncomputable section

open Finset

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

theorem cat_fc_lo {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q)
    (i : ℕ) (hi : i < a + 1) (l : Fin (m + 1)) :
    cat x z (m + 2) (fc i l) = cat (fun l' : Fin a => x (fc i l')) z (m + 1) l := by
  have hv := fc_val i l
  have hl := l.isLt
  simp only [cat]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first
    | (congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)
    | (exfalso; split_ifs at hv <;> omega)
    | rfl

theorem cat_fc_hi {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q)
    (j : ℕ) (hj : j < c + 1) (l : Fin (m + 1)) :
    cat x z (m + 2) (fc (a + 1 + j) l) = cat x (fun l' : Fin c => z (fc j l')) (m + 1) l := by
  have hv := fc_val (a + 1 + j) l
  have hl := l.isLt
  simp only [cat]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first
    | (congr 1; ext; simp only [fc_val, Fin.val_mk]; split_ifs <;> omega)
    | (exfalso; split_ifs at hv <;> omega)
    | rfl

private theorem fin_succAbove_eq_fc {n : ℕ} (i : Fin (n + 1)) (l : Fin n) : i.succAbove l = fc (i : ℕ) l := by
  ext
  rw [fc_val]
  split_ifs with hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    rfl

theorem dc_cat {Q : Type} [Group Q] {a c m : ℕ} (h : a + c = m) (F : (Fin (m + 1) → Q) → ℝ)
    (x : Fin (a + 1) → Q) (z : Fin (c + 1) → Q) :
    dc F (cat x z (m + 2)) =
      (∑ i : Fin (a + 1), (-1 : ℝ) ^ (i : ℕ) * F (cat (fun l => x (i.succAbove l)) z (m + 1))) +
        (-1 : ℝ) ^ (a + 1) *
          ∑ j : Fin (c + 1), (-1 : ℝ) ^ (j : ℕ) * F (cat x (fun l => z (j.succAbove l)) (m + 1)) := by
  simp only [dc]
  simp_rw [fin_succAbove_eq_fc]
  rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (fun l => cat x z (m + 2) (fc k l))) (m + 2),
    Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat (fun l => x (fc k l)) z (m + 1))) (a + 1),
    Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * F (cat x (fun l => z (fc k l)) (m + 1))) (c + 1),
    show Finset.range (m + 2) = Finset.range ((a + 1) + (c + 1)) by congr 1; omega,
    Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    congr 2
    funext l
    exact cat_fc_lo h x z k (Finset.mem_range.1 hk) l
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [pow_add, mul_assoc]
    congr 3
    funext l
    exact cat_fc_hi h x z j (Finset.mem_range.1 hj) l

theorem cat_zero_left {Q : Type} [Group Q] {n : ℕ} (x : Fin 0 → Q) (z : Fin n → Q) : cat x z n = z := by
  funext i
  simp [cat]

theorem cat_zero_right {Q : Type} [Group Q] {n : ℕ} (x : Fin n → Q) (z : Fin 0 → Q) : cat x z n = x := by
  funext i
  simp [cat]

theorem cat_mul {Q : Type} [Group Q] {a c n : ℕ} (h : a + c = n) (g : Q) (x : Fin a → Q) (z : Fin c → Q) :
    cat (fun i => g * x i) (fun j => g * z j) n = fun i => g * cat x z n i := by
  funext i
  have hi := i.isLt
  simp only [cat]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem splitA : SplitA := by
  intro P Q _ _ pr q b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (q + 1 + 2))
  rw [dc_cat (a := 0) (c := q + 1) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero] at h0
  simp only [cat_zero_left, Fin.val_zero, pow_zero, one_mul, zero_add,
    pow_one, Pi.zero_apply, add_zero] at h0
  simp only [Wtop, dv, dc, zz]
  change (b fun j => pr (y j)) =
    ∑ i : Fin (q + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat x (fun j => pr (y (i.succAbove j))) (q + 1 + 1))
  linarith

theorem splitS : SplitS := by
  intro P Q _ _ pr p q b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (p + q + 2 + 2))
  rw [dc_cat (a := p + 1) (c := q + 1) (by omega)] at h0
  simp only [Pi.zero_apply] at h0
  simp only [dh, dv, dc, zz, Pi.smul_apply, smul_eq_mul]
  change ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) *
      b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (p + q + 2 + 1)) =
    (-1 : ℝ) ^ (p + 1) * ∑ j : Fin (q + 2), (-1 : ℝ) ^ (j : ℕ) *
      b (cat x (fun l => pr (y (j.succAbove l))) (p + q + 2 + 1))
  linear_combination h0

theorem splitB : SplitB := by
  intro P Q _ _ pr N b hb
  funext x y
  have h0 := congrFun hb (cat x (fun j => pr (y j)) (N + 1 + 2))
  rw [dc_cat (a := N + 1) (c := 0) (by omega), Fin.sum_univ_succ (n := 0), Fin.sum_univ_zero] at h0
  simp only [cat_zero_right, Fin.val_zero, pow_zero, one_mul, Pi.zero_apply, add_zero] at h0
  simp only [dh, dc, zz, Pi.smul_apply, smul_eq_mul]
  change ∑ i : Fin (N + 2), (-1 : ℝ) ^ (i : ℕ) * b (cat (fun l => x (i.succAbove l)) (fun j => pr (y j)) (N + 1 + 1)) = _
  linear_combination h0

theorem zInv : ZInv := by
  intro P Q _ _ pr n a c b hn hb g x y
  simp only [zz, map_mul]
  rw [cat_mul hn]
  exact hb (pr g) _

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
end
