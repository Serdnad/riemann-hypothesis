module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DegSplit
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentChainDegreeEven
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def TD (b : SegBlock (segS X.TT j) X.m) (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) : ℕ :=
  (∑ i : Fin (segS X.TT j),
    ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0)))) +
  (segAPlus X.TT X.aT j - b.oPlus) * ω ((topEnd X j, true), 0) + b.oPlus * ω ((topEnd X j, true), Fin.succ 0) +
    (X.seg C0 CE1 CE2 j).bPlus * ω ((topEnd X j, false), Fin.succ 0)

theorem ioBlock_wh (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (b : SegBlock (segS X.TT j) X.m)
    (ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ) (hc : ∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ))
    (hU : ∀ l : Fin (X.seg C0 CE1 CE2 j).t,
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) + ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), 0) =
      ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), Fin.succ 0) +
        ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), false), Fin.succ 0))
    (hP : ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
      ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0))
    (s : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O))
    (hs : s ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b).SSZ O (r := X.m)) :
    IsWeightedHomogeneous ω (ioBlock (KK O) X.p C0 CE1 CE2 X j b s) (TD C0 CE1 CE2 X j b ω) := by
  let ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ := fun v => symLev X.p C0 CE1 CE2 X j v * ω (symVar C0 CE1 CE2 X j v)
  let ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => ω' (Sum.inl (a, 0))
  have h1 : ∀ a c, ω' (Sum.inl (a, c)) = ωL a := by
    intro a c
    simp only [ω', ωL, symLev, symVar]
    split_ifs <;> rw [hc _ c 0]
  have e0 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ)) =
      Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val) (2 * segS X.TT j + 1) = 2 * i.val
    omega
  have e1 : ∀ i : Fin (segS X.TT j), finPos (2 * segS X.TT j + 1) (2 * (i : ℕ) + 1) =
      Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) := by
    intro i
    have := i.2
    apply Fin.ext
    show min (2 * i.val + 1) (2 * segS X.TT j + 1) = 2 * i.val + 1
    omega
  have hW : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [symbol_variable_lower_letter, symbol_level_lower_letter]
  have hE : ∀ i : Fin (segS X.TT j), ωL (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      (X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0) := by
    intro i
    simp only [ωL, ω']
    rw [sv_E, sl_E]
  have hUU : ωL (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))) =
      ω ((topEnd X j, true), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_U, sl_U, one_mul]
  have hXi : ωL (Fin.last _) = ω ((topEnd X j, false), Fin.succ 0) := by
    simp only [ωL, ω']
    rw [sv_xi, sl_xi, one_mul]
  have hZ : ∀ (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool), ω' (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) * ω ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
    intro l β
    simp only [ω']
    rw [sv_Z, sl_Z]
  have hx : ∀ β : Bool, ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, β)) = ω ((topEnd X j, !β), 0) := by
    intro β
    simp only [ω']
    rw [symbol_variable_last, symbol_level_last, one_mul]
  have h2 : ∀ l : Fin (X.seg C0 CE1 CE2 j).t, ω' (Sum.inr (Fin.castSucc l, false)) + ω' (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ))) + ωL (finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1)) := by
    intro l
    rw [hZ, hZ, e0, e1, hW, hE, ← mul_add, ← mul_add]
    congr 1
    exact hU l
  have h3 : ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, false)) + ω' (Sum.inr (Fin.last (X.seg C0 CE1 CE2 j).t, true)) =
      ωL (Fin.castSucc ⟨2 * segS X.TT j, by omega⟩) + ωL (Fin.last _) := by
    rw [hx, hx, hUU, hXi]
    exact hP
  have hS := ssz_wh O X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b ω' ωL h1 h2 h3 s hs
  have hA := wh_aeval ω (symVar C0 CE1 CE2 X j) (symLev X.p C0 CE1 CE2 X j) s _ hS
  have hDg : IsWeightedHomogeneous ω (digitMon (KK O) C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
        (b.rz i c • ω ((topOdd X j i, true), c) + b.ry i c • ω ((topOdd X j i, false), c))) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => IsWeightedHomogeneous.prod _ _ _ (fun c _ =>
      ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)))
  have hSt : IsWeightedHomogeneous ω (sTopMon (KK O) X.p C0 CE1 CE2 X j b)
      (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) • ω ((topOdd X j i, true), 0) +
          ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i) • ω ((topOdd X j i, false), 0) else 0) := by
    refine IsWeightedHomogeneous.prod _ _ _ (fun i _ => ?_)
    split_ifs
    · exact ((isWeightedHomogeneous_X _ ω _).pow _).mul ((isWeightedHomogeneous_X _ ω _).pow _)
    · exact isWeightedHomogeneous_one _ _
  have hall := (hDg.mul hSt).mul hA
  refine wh_congr hall ?_
  have E1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) - b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ω' (Sum.inr (Fin.castSucc l, false)) =
      ∑ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0 := by
    rw [← sum_uTop (X.seg C0 CE1 CE2 j) (fun i => (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hZ]
    rfl
  have E3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a * ωL (Fin.castSucc a) =
      ∑ i : Fin (segS X.TT j), ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) +
      b.oPlus * ω ((topEnd X j, true), Fin.succ 0) := by
    rw [sum_chain, hUU, chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, hE, segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl, chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ i rfl]
  unfold OmB TD
  rw [E1, E3, hx, hXi]
  simp only [smul_eq_mul, Bool.not_false]
  have key : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          b.sg i * ω ((topOdd X j i, false), 0) + b.w i * ω ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) * ω ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ω ((topOdd X j i, true), 0) +
          b.o i * ω ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i * ω ((topOdd X j i, false), Fin.succ 0))) =
      (∑ c : Fin (X.m + 1), (b.rz i c * ω ((topOdd X j i, true), c) + b.ry i c * ω ((topOdd X j i, false), c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * ω ((topOdd X j i, true), 0) +
          (X.seg C0 CE1 CE2 j).P X.p i * b.sg i * ω ((topOdd X j i, false), 0) else 0) +
      (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), 0)) else 0) +
      ((if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, true), Fin.succ 0)) +
        (if i.val < (X.seg C0 CE1 CE2 j).sigma then coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i
          else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) * ((X.seg C0 CE1 CE2 j).P X.p i * ω ((topOdd X j i, false), Fin.succ 0))) := by
    intro i
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, if_neg (not_le.2 h), if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_pos (not_lt.1 h), if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp only [Finset.sum_add_distrib]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def ωoL (l0 : Fin (X.seg C0 CE1 CE2 j).t) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if (a : ℕ) = 2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ) then 1 else 0

def ωo (l0 : Fin (X.seg C0 CE1 CE2 j).t) : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωoL C0 CE1 CE2 X j l0 a
  | Sum.inr (l, β) => if (l : ℕ) = (l0 : ℕ) ∧ β = true then 1 else 0

def ωpL : Fin (2 * segS X.TT j + 1 + 1) → ℕ := fun a => if (a : ℕ) = 2 * segS X.TT j then 1 else 0

def ωp : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, _) => ωpL X j a
  | Sum.inr (l, β) => if (l : ℕ) = (X.seg C0 CE1 CE2 j).t ∧ β = true then 1 else 0

theorem ωo_bal (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    Balanced X.m (X.seg C0 CE1 CE2 j) (ωo C0 CE1 CE2 X j l0) (ωoL C0 CE1 CE2 X j l0) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have hu : ∀ l' : Fin (X.seg C0 CE1 CE2 j).t, ((uTop (X.seg C0 CE1 CE2 j) l' : Fin _) : ℕ) =
        (X.seg C0 CE1 CE2 j).sigma + l' := fun _ => rfl
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωo, ωoL, v0, v1, Fin.val_castSucc]
    by_cases hl : (l : ℕ) = (l0 : ℕ)
    · rw [if_neg (by simp), if_pos (by simp [hl]), if_pos (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
    · rw [if_neg (by simp), if_neg (by simp [hl]), if_neg (by rw [hu, hu]; omega), if_neg (by rw [hu, hu]; omega)]
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
    simp only [ωo, ωoL, Fin.val_castSucc, Fin.val_last]
    rw [if_neg (by simp), if_neg (by intro h; have := l0.2; omega), if_neg (by omega), if_neg (by omega)]

theorem ωp_bal : Balanced X.m (X.seg C0 CE1 CE2 j) (ωp C0 CE1 CE2 X j) (ωpL X j) := by
  refine ⟨fun a c => rfl, fun l => ?_, ?_⟩
  · have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have v0 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) := Nat.min_eq_left (by omega)
    have v1 : ((finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) : Fin _) : ℕ) =
        2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1 := Nat.min_eq_left (by omega)
    simp only [ωp, ωpL, v0, v1, Fin.val_castSucc]
    rw [if_neg (by simp), if_neg (by intro h; have := l.2; omega), if_neg (by omega), if_neg (by omega)]
  · simp only [ωp, ωpL, Fin.val_castSucc, Fin.val_last]
    simp

theorem omB_ωo (b : SegBlock (segS X.TT j) X.m) (l0 : Fin (X.seg C0 CE1 CE2 j).t) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωo C0 CE1 CE2 X j l0)
      (ωoL C0 CE1 CE2 X j l0) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
  classical
  have hi := (uTop (X.seg C0 CE1 CE2 j) l0).2
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωo]
  have s2 : ωo C0 CE1 CE2 X j l0 (Sum.inr (Fin.last _, false)) = 0 := by simp [ωo]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωoL C0 CE1 CE2 X j l0 (Fin.castSucc a) = b.o (uTop (X.seg C0 CE1 CE2 j) l0) := by
    rw [Finset.sum_eq_single (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l0 : ℕ), by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωoL, Fin.val_castSucc, if_true, mul_one]
      rw [segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ (uTop (X.seg C0 CE1 CE2 j) l0) rfl,
        if_neg (by show ¬ ((X.seg C0 CE1 CE2 j).sigma + (l0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma); omega)]
    · intro a _ ha
      simp only [ωoL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωoL C0 CE1 CE2 X j l0 (Fin.last _) = 0 := by
    simp only [ωoL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

theorem omB_ωp (b : SegBlock (segS X.TT j) X.m) :
    OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (ωp C0 CE1 CE2 X j) (ωpL X j) = b.oPlus := by
  classical
  unfold OmB
  have s1 : ∑ l : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l) -
      b.o (uTop (X.seg C0 CE1 CE2 j) l)) * ωp C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, false)) = 0 :=
    Finset.sum_eq_zero fun l _ => by simp [ωp]
  have s2 : ωp C0 CE1 CE2 X j (Sum.inr (Fin.last _, false)) = 0 := by simp [ωp]
  have s3 : ∑ a : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a *
      ωpL X j (Fin.castSucc a) = b.oPlus := by
    rw [Finset.sum_eq_single (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1))]
    · simp only [ωpL, Fin.val_castSucc, if_true, mul_one]
      exact chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b _ rfl
    · intro a _ ha
      simp only [ωpL, Fin.val_castSucc]
      rw [if_neg (fun h => ha (Fin.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have s4 : ωpL X j (Fin.last _) = 0 := by
    simp only [ωpL, Fin.val_last]
    rw [if_neg (by omega)]
  rw [s1, s2, s3, s4]
  ring

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r] (D : BlockData N)

def beF (v : BVar N r D.T.t) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  match v with
  | Sum.inl a => X (Sum.inl a)
  | Sum.inr (_, false) => 1
  | Sum.inr (i, true) => X (Sum.inr (i, true))

def giF (v : BVar N r D.T.t) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  match v with
  | Sum.inl a => X (Sum.inl a)
  | Sum.inr (i, false) => X (Sum.inr (i, false))
  | Sum.inr (i, true) => X (Sum.inr (i, true)) - qq (O := O) (r := r) D i

theorem qq_fix (f : BVar N r D.T.t → MvPolynomial (BVar N r D.T.t) (KK O)) (hf : ∀ a, f (Sum.inl a) = X (Sum.inl a))
    (i : Fin (D.T.t + 1)) : aeval f (qq (O := O) (r := r) D i) = qq (O := O) (r := r) D i := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [qq, xiVar, hf]
  · simp [qq, hf]

theorem qq_int (i : Fin (D.T.t + 1)) : qq (O := O) (r := r) D i ∈ IntAlg O (BVar N r D.T.t) := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [qq, Fin.lastCases_last]
    exact Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)
  · simp only [qq, Fin.lastCases_castSucc]
    exact Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)

theorem gi_be_tau (P : MvPolynomial (BVar N r D.T.t) (KK O)) :
    aeval (giF (O := O) (r := r) D) (aeval (beF (O := O) (r := r) D) (tau D P)) = aeval (beF (O := O) (r := r) D) P := by
  have h : ((aeval (giF (O := O) (r := r) D)).comp ((aeval (beF (O := O) (r := r) D)).comp (tau D))) =
      aeval (beF (O := O) (r := r) D) := by
    apply MvPolynomial.algHom_ext
    rintro (a | ⟨i, _ | _⟩)
    · simp [tau, tauF, beF, giF]
    · simp [tau, tauF, beF, giF]
    · simp only [AlgHom.comp_apply, tau, aeval_X, tauF, map_add (f := _), map_mul, beF, one_mul, giF, map_one]
      rw [qq_fix D (beF D) (fun _ => rfl), qq_fix D (giF D) (fun _ => rfl)]
      ring
  exact DFunLike.congr_fun h P

theorem ppi_be (P : MvPolynomial (BVar N r D.T.t) (KK O)) :
    ppi D (aeval (beF (O := O) (r := r) D) P) = ppi D P := by
  have h : (ppi (O := O) (r := r) D).comp (aeval (beF (O := O) (r := r) D)) = ppi D := by
    apply MvPolynomial.algHom_ext
    rintro (a | ⟨i, _ | _⟩)
    · simp [beF]
    · simp [beF, ppi, piF]
    · simp [beF]
  exact DFunLike.congr_fun h P

theorem ppi_int (q : MvPolynomial (BVar N r D.T.t) O) (e : (Fin (D.T.t + 1) ⊕ Fin r) →₀ ℕ) :
    AddMonoidAlgebra.coeff (ppi (O := O) (r := r) D (map (algebraMap O (KK O)) q)) e ∈ IntAlg O (Fin N × Fin r) := by
  classical
  induction q using MvPolynomial.induction_on generalizing e with
  | C a =>
    rw [map_C]
    have : ppi (O := O) (r := r) D (C (algebraMap O (KK O) a)) = C (C (algebraMap O (KK O) a)) := by
      simp [ppi, MvPolynomial.algebraMap_eq]
    rw [this, coeff_C]
    split_ifs
    · exact ⟨C a, by simp⟩
    · exact (IntAlg O _).zero_mem
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), MvPolynomial.coeff_add]
    exact (IntAlg O _).add_mem (hp e) (hq e)
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_X]
    have hv : ppi (O := O) (r := r) D (X v) = piF D v := by simp [ppi]
    rw [hv]
    rcases v with ⟨a, c⟩ | ⟨i, _ | _⟩
    · refine Fin.lastCases ?_ (fun a' => ?_) a
      · simp only [piF, Fin.lastCases_last]
        rw [coeff_mul_X']
        split_ifs
        · exact hp _
        · exact (IntAlg O _).zero_mem
      · simp only [piF, Fin.lastCases_castSucc]
        rw [mul_comm, coeff_C_mul]
        exact (IntAlg O _).mul_mem (X_mem_intAlg O _) (hp e)
    · simp only [piF, mul_one]
      exact hp e
    · simp only [piF]
      rw [coeff_mul_X']
      split_ifs
      · exact hp _
      · exact (IntAlg O _).zero_mem

theorem sat_block (x : MvPolynomial (BVar N r D.T.t) (KK O))
    (hx : x ∈ Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
      Set (MvPolynomial (BVar N r D.T.t) (KK O)))) (hi : x ∈ IntPol O (BVar N r D.T.t)) : x ∈ D.SSZ O (r := r) := by
  classical
  rw [span_eq_range] at hx
  obtain ⟨v, rfl⟩ := hx
  have hv := Ltot_apply D v
  set B := ∑ i : ↥(IF (r := r) D), base D i.1.1 i.1.2 (v i : MvPolynomial (Fin N × Fin r) (KK O)) with hB
  have hT : Ltot D v = tau D B := by

    rw [hv, hB, map_sum]
    exact Finset.sum_congr rfl fun i _ => ell_eq_tau D _ _ _
  have h1 : aeval (beF (O := O) (r := r) D) B ∈ IntAlg O (BVar N r D.T.t) := by
    rw [← gi_be_tau D B, ← hT]
    refine aeval_mem_intAlg O _ ?_ (aeval_mem_intAlg O _ ?_ (intPol_le O hi))
    · rintro (a | ⟨i, _ | _⟩)
      · exact X_mem_intAlg O _
      · exact X_mem_intAlg O _
      · exact (IntAlg O _).sub_mem (X_mem_intAlg O _) (qq_int D i)
    · rintro (a | ⟨i, _ | _⟩)
      · exact X_mem_intAlg O _
      · exact (IntAlg O _).one_mem
      · exact X_mem_intAlg O _
  obtain ⟨q, hq⟩ := h1
  have hq' : map (algebraMap O (KK O)) q = aeval (beF (O := O) (r := r) D) B := hq
  have hint : ∀ i0 : ↥(IF (r := r) D), (v i0 : MvPolynomial (Fin N × Fin r) (KK O)) ∈ IntAlg O (Fin N × Fin r) := by
    intro i0
    have h2 := ppi_int D q (eExp D i0.1.1 i0.1.2)

    rw [hq', ppi_be, hB, map_sum] at h2
    simp only [ppi_base] at h2
    rw [coeff_sum, Finset.sum_eq_single i0] at h2
    · rwa [coeff_monomial, if_pos rfl] at h2
    · intro b _ hb
      rw [coeff_monomial, if_neg]
      intro he
      obtain ⟨e1, e2⟩ := eExp_inj D he
      exact hb (Subtype.ext (Sigma.ext e1 (heq_of_eq e2)))
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi' := i.2
  unfold IF at hi'
  rw [Finset.mem_sigma] at hi'
  have hlv := (mem_Lv D _).1 hi'.1
  have hβ := Finset.Nat.mem_antidiagonalTuple.1 hi'.2
  obtain ⟨q0, hq0⟩ := hint i
  unfold BlockData.SSZ
  refine Submodule.subset_span ?_
  simp only [Set.mem_iUnion]
  refine ⟨i.1.1.1, i.1.1.2, hlv, (v i : MvPolynomial (Fin N × Fin r) (KK O)), ⟨(v i).2, ⟨q0, hq0⟩⟩,
    xiMon (KK O) N r D.T.t i.1.2, xiMon_mem D _ _ hβ, ?_⟩
  rw [ell_apply]
  simp only [pre, mul_assoc]

end

theorem satAt : SatAt := fun _ _ _ _ _ _ _ D x hx hi => sat_block D x hx hi

end Formalism.MainNotions.ColumnSystems.Pf
end
end
