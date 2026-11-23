module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle001
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem error_exponent_lower_bound {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2) (hc : 1 ≤ X.c) :
    localOrderCap C0 X + (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ X.E0 C0 CE1 CE2 := by
  have hp5 : (5 : ℝ) ≤ X.p := by exact_mod_cast St.p5
  have hp : (0 : ℝ) < X.p := by linarith
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hk : (1 : ℝ) ≤ X.k := by have := St.N1k; linarith
  have hk0 : (0 : ℝ) < X.k := by linarith
  have hQ : (1 : ℝ) ≤ X.Q := one_le_pow₀ (by linarith)
  have hcr : (1 : ℝ) ≤ X.c := by exact_mod_cast hc
  have hLa : (0 : ℝ) ≤ X.La C0 := by have := St.La1; linarith
  have ha : (0 : ℝ) ≤ X.a := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ X.b' := St.bpos.le
  have A1 : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 := by positivity
  have B1 : 0 ≤ X.b' / (X.p : ℝ) := by positivity
  have L0 : 0 ≤ X.La C0 * X.a / (X.p * X.k) := by positivity
  have L2 : 0 ≤ X.La C0 * X.b' / X.k := by positivity
  have e1 : X.La C0 * X.N1 * X.a / (X.p * X.k) = X.N1 * (X.La C0 * X.a / (X.p * X.k)) := by ring
  have hL1 : X.La C0 * X.a / (X.p * X.k) ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := by
    rw [e1]; exact le_mul_of_one_le_left L0 hN1
  have e2 : X.La C0 / X.k * (4 * (X.a : ℝ) / X.p) = 4 * (X.La C0 * X.a / (X.p * X.k)) := by
    field_simp
  have e3 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) = (X.a : ℝ) / (X.p : ℝ) ^ 2 * (16 / X.p) := by
    field_simp
    ring
  have h16 : 16 / (X.p : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hp]; linarith
  have e4 : 4 / (X.p : ℝ) ^ 2 * (4 * (X.a : ℝ) / X.p) ≤ 4 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) := by
    rw [e3, mul_comm 4]; exact mul_le_mul_of_nonneg_left h16 A1
  have e5 : 2 * X.La C0 * X.b' / X.k = 2 * (X.La C0 * X.b' / X.k) := by ring
  have e6 : 3 * X.b' / (X.p : ℝ) = 3 * (X.b' / X.p) := by ring
  have hO : localOrderCap C0 X ≤ 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) := by
    unfold localOrderCap
    rw [add_mul, e2, e5, e6]
    linarith
  have L1 : 0 ≤ X.La C0 * X.N1 * X.a / (X.p * X.k) := le_trans L0 hL1
  have hfirst : 5 * ((X.a : ℝ) / (X.p : ℝ) ^ 2) + 3 * (X.b' / X.p) +
      4 * (X.La C0 * X.N1 * X.a / (X.p * X.k)) + 2 * (X.La C0 * X.b' / X.k) ≤
      CE1 * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k) := by
    have hs : 0 ≤ (X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + X.La C0 * X.N1 * X.a / (X.p * X.k) + X.La C0 * X.b' / X.k := by
      linarith
    have := mul_le_mul_of_nonneg_right h1 hs
    linarith
  have hkQ : 1 ≤ X.k * X.Q := one_le_mul_of_one_le_of_one_le hk hQ
  have hT : 0 ≤ X.k * X.N1 * X.Q * X.c := by positivity
  have t1 : X.k * X.N1 * X.Q * X.c ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = (X.k * X.Q) * (X.k * X.N1 * X.Q * X.c) := by ring
    rw [this]; exact le_mul_of_one_le_left hT hkQ
  have t2 : (X.N1 : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.N1 : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.N1 * (X.k * X.Q)) * X.c := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hcr
  have t3 : (X.c : ℝ) * (X.k * X.Q) ≤ X.k * X.N1 * X.Q * X.c := by
    have h0 : 0 ≤ (X.c : ℝ) * (X.k * X.Q) := by positivity
    have : X.k * X.N1 * X.Q * X.c = (X.c * (X.k * X.Q)) * X.N1 := by ring
    rw [this]; exact le_mul_of_one_le_right h0 hN1
  have t4 : (X.c : ℝ) * ka1 X = 13 * (X.k * X.N1 * X.Q * X.c) := by unfold ka1; ring
  have hT2 : 0 ≤ X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := le_trans hT t1
  have hsecond : (X.c : ℝ) * ka1 X + X.N1 * (X.k * X.Q) + X.c * (X.k * X.Q) ≤ CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c := by
    have : CE2 * X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c = CE2 * (X.k ^ 2 * X.N1 * X.Q ^ 2 * X.c) := by ring
    rw [this, t4]
    have := mul_le_mul_of_nonneg_right h2 hT2
    linarith
  unfold Loc.E0 errorTermBound
  linarith

theorem room_of_std {C0 Cde CE1 CE2 : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 1 X) (h1 : 17 ≤ CE1) (h2 : 17 ≤ CE2)
    (n : ℕ) (hn1 : 1 ≤ n) (hnc : n ≤ X.c) (β : GlobalTheory X)
    (hβ : ∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) (a0 : Fin (numSeg X.TT) → ℕ)
    (ha0 : ∀ j, (a0 j : ℤ) + ∑ i : Fin (segS X.TT j),
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤ (X.seg C0 CE1 CE2 j).A0 X.p)
    (j0 j : Fin (numSeg X.TT)) :
    usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus := by
  classical
  set j' := rot _ j with hj'
  have hp0 : 0 < X.p := St.pP.pos
  have hqG : X.p ^ segG X.TT j' ≤ X.p ^ X.G' := Nat.pow_le_pow_right hp0 (St.segB j').1
  have hq1 : 1 ≤ X.p ^ segG X.TT j' := Nat.one_le_pow _ _ hp0

  have hN2 : (∑ i : Fin (segS X.TT j'), X.p ^ (segDists X.TT j').get i *
      ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)) ≤ X.N1 * ((X.m + 1) * X.p ^ X.G') := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin (segS X.TT j'))), X.p ^ (segDists X.TT j').get i *
        ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0) ≤ (X.m + 1) * X.p ^ X.G' := by
      intro i _
      have hd := (hβ j').1.1 i
      have s1 : (∑ c : Fin X.m, (β j').rz i c.succ) ≤ X.m * (X.seg C0 CE1 CE2 j').P X.p i := by
        have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin X.m)) (fun c => (β j').rz i c.succ)
          ((X.seg C0 CE1 CE2 j').P X.p i) (fun c _ => (hd c.succ).1.le)
        simpa using this
      have s2 : (β j').ry i 0 ≤ (X.seg C0 CE1 CE2 j').P X.p i := (hd 0).2.le
      calc X.p ^ (segDists X.TT j').get i * ((∑ c : Fin X.m, (β j').rz i c.succ) + (β j').ry i 0)
          ≤ X.p ^ (segDists X.TT j').get i * ((X.m + 1) * (X.seg C0 CE1 CE2 j').P X.p i) :=
            Nat.mul_le_mul_left _ (by linarith)
        _ = (X.m + 1) * (X.p ^ (segDists X.TT j').get i * (X.seg C0 CE1 CE2 j').P X.p i) := by ring
        _ = (X.m + 1) * X.p ^ segG X.TT j' := by rw [pd_mul_P]
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ hqG
    have := Finset.sum_le_card_nsmul _ _ _ hi
    rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ (St.segB j').2)

  have hN3 : X.c * (X.m * (X.p ^ segG X.TT j' - 1)) + (if j' = j0 then X.c else 0) ≤ X.c * ((X.m + 1) * X.p ^ X.G') := by
    obtain ⟨q', hq'⟩ : ∃ q', X.p ^ segG X.TT j' = q' + 1 := ⟨X.p ^ segG X.TT j' - 1, by omega⟩
    have hite : (if j' = j0 then X.c else 0) ≤ X.c := by split_ifs <;> omega
    have e : X.p ^ segG X.TT j' - 1 = q' := by omega
    rw [e]
    have h3 : X.m * q' + 1 ≤ (X.m + 1) * X.p ^ X.G' := by
      calc X.m * q' + 1 ≤ (X.m + 1) * (q' + 1) := by nlinarith
        _ ≤ (X.m + 1) * X.p ^ X.G' := Nat.mul_le_mul_left _ (hq' ▸ hqG)
    calc X.c * (X.m * q') + (if j' = j0 then X.c else 0) ≤ X.c * (X.m * q') + X.c := by omega
      _ = X.c * (X.m * q' + 1) := by ring
      _ ≤ X.c * ((X.m + 1) * X.p ^ X.G') := Nat.mul_le_mul_left _ h3
  have hnat : usedX X β a0 j0 j' ≤ (X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') := by
    unfold usedX
    linarith

  have hsum : ∑ i : Fin (segS X.TT j'), (if (i : ℕ) < (X.seg C0 CE1 CE2 j').sigma then ((β j').sg i : ℤ) else 0) =
      ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · rw [((hβ j').2.1 i (not_lt.1 h)).2.2.2]; rfl
  have hA := ha0 j'
  rw [hsum] at hA
  have hAr : ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤ ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) := by
    exact_mod_cast hA
  have hfl : ((X.seg C0 CE1 CE2 j').A0 X.p : ℝ) ≤
      ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j' : ℕ) : ℝ) := Int.floor_le _
  have hqr : (0 : ℝ) < ((X.p ^ segG X.TT j' : ℕ) : ℝ) := by exact_mod_cast hq1
  have hN1 : ((X.p ^ segG X.TT j' : ℕ) : ℝ) * ((a0 j' : ℝ) + ((∑ i : Fin (segS X.TT j'), (β j').sg i : ℕ) : ℝ)) ≤
      (X.a : ℝ) - X.E0 C0 CE1 CE2 := by
    have := (le_div_iff₀ hqr).1 (hAr.trans hfl)
    linarith

  have hc1 : 1 ≤ X.c := le_trans hn1 hnc
  have hka : 0 ≤ ka1 X := by
    unfold ka1
    have hk : (0 : ℝ) ≤ X.k := by have := St.N1k; have : (0 : ℝ) ≤ X.N1 := Nat.cast_nonneg _; linarith
    have hQ : (0 : ℝ) ≤ X.Q := by unfold Loc.Q; positivity
    positivity
  have hoP : ((β j).oPlus : ℝ) ≤ localOrderCap C0 X + (X.c : ℝ) * ka1 X := by
    have h := (hβ j).2.2.2.2
    have hcn : ((X.c - n : ℕ) : ℝ) ≤ (X.c : ℝ) := by exact_mod_cast Nat.sub_le _ _
    have := mul_le_mul_of_nonneg_right hcn hka
    linarith
  have haP : (X.a : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := (St.winA _ (next_mem X.TT j).1).1
  have hE := error_exponent_lower_bound St h1 h2 hc1
  have hreal : ((usedX X β a0 j0 j' + (β j).oPlus : ℕ) : ℝ) ≤ (segAPlus X.TT X.aT j : ℝ) := by
    have hcast : ((usedX X β a0 j0 j' : ℕ) : ℝ) ≤
        (((X.p ^ segG X.TT j' * a0 j' + X.p ^ segG X.TT j' * (∑ i : Fin (segS X.TT j'), (β j').sg i)) +
      X.N1 * ((X.m + 1) * X.p ^ X.G') + X.c * ((X.m + 1) * X.p ^ X.G') : ℕ) : ℝ) := by exact_mod_cast hnat
    have hk : X.k = (X.m : ℝ) + 1 := rfl
    have hQ : X.Q = (X.p : ℝ) ^ X.G' := rfl
    push_cast at hcast hN1 ⊢
    rw [hk, hQ] at hE
    linarith
  have : usedX X β a0 j0 j' + (β j).oPlus ≤ segAPlus X.TT X.aT j := by exact_mod_cast hreal
  omega

theorem threshold_standard_seventeen : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => (17 ≤ CE1 ∧ 17 ≤ CE2) ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 17) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ a1 a2 _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨⟨a1, a2⟩, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

theorem restRoom : RestRoom :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h X hD hH hc n hn1 hnc β hβ a0 ha0 j0 j =>
    room_of_std (h.2 X hD hH hc) h.1.1 h.1.2 n hn1 hnc β hβ a0 ha0 j0 j) threshold_standard_seventeen

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Io

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O] (β : GlobalTheory X) (j : Fin (numSeg X.TT))

theorem ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

theorem ioD_scal (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.castSucc l, bb))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !bb), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  rw [ioD_X]
  have hl : ((Fin.castSucc l : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) < (X.seg C0 CE1 CE2 j).t := l.2
  simp only [symVar, symLev]
  rw [dite_eq_left hl, dite_eq_left hl]
  rfl

theorem ioD_scalLast (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t, bb))) =
      MvPolynomial.X ((topEnd X j, !bb), 0) := by
  rw [ioD_X]
  have hl : ¬ ((Fin.last (BDk C0 CE1 CE2 mu X β j).T.t : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) <
      (X.seg C0 CE1 CE2 j).t := lt_irrefl _
  simp only [symVar, symLev]
  rw [dite_eq_right hl, dite_eq_right hl, pow_one]

theorem ioD_odd (i : Fin (segS X.TT j)) (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * i + e)
    (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topOdd X j i, decide (e = 0)), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i := by
  rw [ioD_X]
  have hi := i.2
  have hl : (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dite_eq_left hl, dite_eq_left hl]
  have e1 : (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by simp only; omega)
  have e2 : decide ((a : ℕ) % 2 = 0) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e1, e2]

theorem ioD_end (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * segS X.TT j + e) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topEnd X j, decide (e = 0)), c.succ) := by
  rw [ioD_X]
  have hl : ¬ (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dite_eq_right hl, dite_eq_right hl, pow_one]
  have e2 : decide ((a : ℕ) = 2 * segS X.TT j) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e2]

theorem ioD_Ehat (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l) =
      EhatT O X (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l)) ((X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l)) := by
  unfold BlockData.Ehat EhatT scalZ scalS

  rw [map_add (f := _), map_mul, map_sum, ioD_scal, ioD_scal]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hu := (uTop (X.seg C0 CE1 CE2 j) l).2
  rw [map_mul, ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 0 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ)) (2 * segS X.TT j + 1) = _
      omega),
    ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 1 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ) + 1) (2 * segS X.TT j + 1) = _
      omega)]
  rfl

theorem ioD_Eplus :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) = hTop O X (topEnd X j) := by
  unfold hTop hKey
  rw [Fin.sum_univ_succ]
  unfold BlockData.Eplus scalZ scalS xiVar

  rw [map_add (f := _), map_mul, map_sum, ioD_scalLast, ioD_scalLast]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ioD_end β j 0 (by omega) _ (by rfl), ioD_end β j 1 (by omega) _ (by rfl)]
  rfl

end Io

theorem uTop_sum {s : ℕ} {M : Type} [AddCommMonoid M] (S : SegData s) (F : Fin s → M) :
    ∑ l : Fin S.t, F (uTop S l) = ∑ i : Fin s, if (i : ℕ) < S.sigma then 0 else F i := by
  classical
  have h1 : ∑ i : Fin s, (if (i : ℕ) < S.sigma then 0 else F i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬ (i : ℕ) < S.sigma), F i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < S.sigma <;> simp [h]
  rw [h1]
  refine Finset.sum_bij (fun l _ => uTop S l) ?_ ?_ ?_ ?_
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uTop]
    omega
  · intro l _ l' _ h
    have := congrArg Fin.val h
    simp only [uTop] at this
    exact Fin.ext (by omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨(i : ℕ) - S.sigma, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := i.2
      unfold SegData.t
      omega
    · apply Fin.ext
      simp only [uTop]
      omega
  · intro l _
    rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end
