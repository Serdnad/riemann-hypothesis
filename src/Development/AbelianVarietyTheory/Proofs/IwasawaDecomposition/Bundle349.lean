module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle335
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Comb

def cw (ρ k : ℕ) (s : Bool) (i : ℕ) : ℤ :=
  if ρ ≤ i ∧ i + 1 ≠ ρ + k then (if i + 1 < ρ + k then (if s then 0 else -1) else if i = ρ + k then 1 else -1) else 0

theorem term_eq {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      if j.val = i.val + 1 then ((cw ρ k s i.val : ℤ) : R) * M i j else 0 := by
  unfold symEdge GlobalTheory.Mem.SymChar.wtB cw
  simp only [Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_neg]
  split_ifs <;> first | rfl | omega | (simp_all; done) | simp

theorem row_sum {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (c : R) (i : Fin r) :
    (∑ j : Fin r, if j.val = i.val + 1 then c * M i j else 0) =
      c * (if h : i.val + 1 < r then M i ⟨i.val + 1, h⟩ else 0) := by
  by_cases h : i.val + 1 < r
  · rw [dite_eq_left h]
    have : ∀ j : Fin r, (j.val = i.val + 1) ↔ j = ⟨i.val + 1, h⟩ := fun j => by simp [Fin.ext_iff]
    simp only [this]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dif_neg h, mul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega

theorem nat_id {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) (F : ℕ → R) :
    (∑ i ∈ Finset.range (2 * ρ + k), ((cw ρ k s i : ℤ) : R) * F i) =
      (∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) +
        (if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show ρ + k ≤ 2 * ρ + k by omega),
    ← Finset.sum_range_add_sum_Ico _ (show ρ ≤ ρ + k by omega),
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have h0 : (∑ i ∈ Finset.range ρ, ((cw ρ k s i : ℤ) : R) * F i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [cw, show ¬ ρ ≤ i by omega]
  have h1 : (∑ t ∈ Finset.range (2 * ρ + k - (ρ + k)), ((cw ρ k s (ρ + k + t) : ℤ) : R) * F (ρ + k + t)) =
      ∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k) := by
    rw [show 2 * ρ + k - (ρ + k) = ρ by omega, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finset.mem_range] at ht
    unfold cw
    by_cases h : t + 1 < ρ
    · rw [if_pos h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) = ρ + k) by omega),
        show ρ + k + (ρ - 1 - t) = 2 * ρ + k - t - 1 by omega]
      simp
    · rw [if_neg h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_pos (show ρ + k + (ρ - 1 - t) = ρ + k by omega),
        show ρ + k + (ρ - 1 - t) = ρ + k by omega]
      simp
  have h2 : (∑ t ∈ Finset.range (ρ + k - ρ), ((cw ρ k s (ρ + t) : ℤ) : R) * F (ρ + t)) =
      if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0 := by
    rw [show ρ + k - ρ = k by omega]
    cases s
    · simp only [Bool.false_eq_true, if_false]
      rw [← Finset.sum_range_reflect (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have e1 : ((cw ρ (k' + 1) false (ρ + k') : ℤ) : R) * F (ρ + k') = 0 := by
          unfold cw; rw [if_neg (by omega)]; simp
        have e2 : (if k' + 1 - 1 - 0 + 1 < k' + 1 then -F (ρ + (k' + 1) - 2 - (k' + 1 - 1 - 0)) else 0) = (0 : R) := by
          rw [if_neg (by omega)]
        rw [e1, e2, add_zero, add_zero]
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [Finset.mem_range] at ht
        rw [if_pos (show k' + 1 - 1 - (t + 1) + 1 < k' + 1 by omega),
          show ρ + (k' + 1) - 2 - (k' + 1 - 1 - (t + 1)) = ρ + t by omega]
        simp [cw, show ρ ≤ ρ + t ∧ ρ + t + 1 ≠ ρ + (k' + 1) by omega, show ρ + t + 1 < ρ + (k' + 1) by omega]
    · simp only [if_true]
      refine Finset.sum_eq_zero fun t ht => ?_
      simp only [Finset.mem_range] at ht
      unfold cw
      split_ifs <;> first | omega | simp_all
  rw [h0, h1, h2, zero_add, add_comm]

theorem weighted_sum_eq : ∀ {R : Type} [CommRing R] (ρ k r : ℕ) (hr : r = 2 * ρ + k + 1) (s : Bool) (M : Matrix (Fin r) (Fin r) R), (∑ i, ∑ j, if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = (∑ a : Fin ρ, if h : a.val + 1 < ρ then -M ⟨2 * ρ + k - a.val - 1, by omega⟩ ⟨2 * ρ + k - a.val, by omega⟩ else M ⟨ρ + k, by omega⟩ ⟨ρ + k + 1, by omega⟩) + (if s then 0 else ∑ i : Fin k, if h : i.val + 1 < k then -M ⟨ρ + k - 2 - i.val, by omega⟩ ⟨ρ + k - 1 - i.val, by omega⟩ else 0) := by
  intro R _ ρ k r hr s M
  subst hr
  let F : ℕ → R := fun i => if h : i + 1 < 2 * ρ + k + 1 then M ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0
  have hFv : ∀ i j (hi : i < 2 * ρ + k + 1) (hj : j < 2 * ρ + k + 1), j = i + 1 → F i = M ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j hi hj e; subst e; simp only [F]; rw [dite_eq_left hj]
  have hL : (∑ i : Fin (2 * ρ + k + 1), ∑ j : Fin (2 * ρ + k + 1), if symEdge ρ k i j then
      ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      ∑ i : Fin (2 * ρ + k + 1), ((cw ρ k s i.val : ℤ) : R) * F i.val := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [term_eq]
    rw [row_sum]
  rw [hL, Fin.sum_univ_eq_sum_range (fun i => ((cw ρ k s i : ℤ) : R) * F i), Finset.sum_range_succ,
    show F (2 * ρ + k) = 0 from dif_neg (by omega), mul_zero, add_zero, nat_id]
  congr 1
  · refine (Fin.sum_univ_eq_sum_range (fun a => if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) ρ).symm.trans
      (Finset.sum_congr rfl fun a _ => ?_)
    beta_reduce
    split_ifs with h
    · rw [hFv _ (2 * ρ + k - a.val) (by omega) (by omega) (by omega)]
    · rw [hFv _ (ρ + k + 1) (by omega) (by omega) (by omega)]
  · cases s
    · simp only [Bool.false_eq_true, if_false]
      refine (Fin.sum_univ_eq_sum_range (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k).symm.trans
        (Finset.sum_congr rfl fun i _ => ?_)
      beta_reduce
      split_ifs with h
      · rw [hFv _ (ρ + k - 1 - i.val) (by omega) (by omega) (by omega)]
      · rfl
    · rfl

end GlobalTheory.Mem.SymChar.Comb
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EdgeReindex

theorem sum_edge {Q : Type} [AddCommMonoid Q] {r t : ℕ} (ht : t < r) (P : Fin r → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j.val = t) (f : Fin r → Q) : (∑ j, if P j then f j else 0) = f ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [if_pos ((hP _).2 rfl)]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext ((hP b).1 h))
  · simp

def extF {Q : Type} [AddCommGroup Q] {r : ℕ} (F : Fin r → Fin r → Q) (a b : ℕ) : Q :=
  if h : a < r ∧ b < r then F ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def termAt {Q : Type} [AddCommGroup Q] (ρ k : ℕ) (s : Bool) {r : ℕ} (F : Fin r → Fin r → Q) (n : ℕ) : Q :=
  if n < ρ then extF F n (if n + 1 < ρ then n + 1 else ρ + k)
  else if n + 1 < ρ + k then (if s then extF F n (n + 1) else 0) else 0

theorem inner_eq {Q : Type} [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool)
    (F : Fin r → Fin r → Q) (i : Fin r) :
    (∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) =
      termAt ρ k s F i.1 := by
  have hi := i.2
  unfold termAt
  by_cases h1 : i.1 < ρ
  · by_cases h2 : i.1 + 1 < ρ
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_pos h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
    · rw [sum_edge (t := ρ + k) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_neg h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
  · by_cases h2 : i.1 + 1 < ρ + k
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_neg h1, if_pos h2]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_pos h2]
      cases s
      · simp
      · rw [extF, dite_eq_left ⟨i.2, by omega⟩]
        simp
    · rw [if_neg h1, if_neg h2]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_neg h2, zero_smul, ite_self]

theorem sum_symEdge_wtA : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  intro Q _ ρ k r hr s F
  rw [Finset.sum_congr rfl (fun i _ => inner_eq ρ k r hr s F i)]
  rw [Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) r]
  have e : Finset.range r = Finset.range (ρ + (k + (ρ + 1))) := congrArg Finset.range (by omega)
  rw [e, Finset.sum_range_add, Finset.sum_range_add]
  have h3 : (∑ x ∈ Finset.range (ρ + 1), termAt ρ k s F (ρ + (k + x))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    unfold termAt
    rw [if_neg (by omega), if_neg (by omega)]
  rw [h3, add_zero]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) ρ]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    unfold termAt extF
    rw [if_pos ha, dite_eq_left ⟨by omega, by split_ifs <;> omega⟩]
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F (ρ + n)) k]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dite_eq_left h]
      unfold termAt
      rw [if_neg (by omega), if_pos (by omega)]
      cases s
      · rfl
      · simp only [if_true]
        unfold extF
        rw [dite_eq_left ⟨by omega, by omega⟩]
    · rw [dite_eq_right h]
      unfold termAt
      rw [if_neg (by omega), if_neg (by omega)]

end GlobalTheory.Mem.SymChar.EdgeReindex
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

theorem mem_of_inclE_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E),
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w →
      α ∈ w.asIdeal := by
  intro D X w α hα
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE with he
  set Wx : Ideal (𝓞 X.B.I.E) := w.asIdeal.comap (e : 𝓞 X.B.I.E →+* 𝓞 D.host.E) with hWx
  have hWx0 : Wx ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    rw [eq_bot_iff]
    intro b hb
    have : e.symm b ∈ Wx := by
      show e (e.symm b) ∈ w.asIdeal
      simpa using hb
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    simpa using congrArg e this

  have key : ∀ c ∈ GlobalTheory.Mem.SymChar.wInt X w,
      ∃ h : c ∈ Formalism.L2.Herm.intAf X.B.I.F X.B.I.E,
        (⟨c, h⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) ∈ Formalism.L2.DIV.idS X.B.I.F Wx := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
      refine ⟨(Formalism.L2.DIV.oToS X.B.I.F X.B.I.E a).2, ?_⟩
      have ha : a ∈ Wx := by
        show e a ∈ w.asIdeal
        have : e a = b := Subtype.ext hab
        rw [this]; exact hb
      exact Ideal.mem_map_of_mem _ ha
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨add_mem hx1 hy1, add_mem hx2 hy2⟩
    | smul r x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨mul_mem r.2 hx1, ?_⟩
      have : (⟨r • x, mul_mem r.2 hx1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = ⟨r.1, r.2⟩ * ⟨x, hx1⟩ := rfl
      rw [this]
      exact Ideal.mul_mem_left _ _ hx2
  obtain ⟨h1, h2⟩ := key _ hα
  set c : 𝓞 X.B.I.E := e.symm α with hc
  have hoc : (⟨_, h1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c := rfl
  rw [hoc] at h2
  have hz : Formalism.L2.DIV.cmpS X.B.I.F Wx (Ideal.Quotient.mk Wx c) = Formalism.L2.DIV.cmpS X.B.I.F Wx 0 := by
    rw [map_zero]
    show Ideal.Quotient.mk _ (Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  have hcW : c ∈ Wx := Ideal.Quotient.eq_zero_iff_mem.1 (Formalism.L2.DIV.cmpS_inj Wx hWx0 hz)
  have : e c = α := by rw [hc]; exact e.apply_symm_apply α
  rw [← this]
  exact hcW

end GlobalTheory.Mem.SymChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

theorem smul_mem_wLf_of_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (hc : c ∈ wInt X w) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    c • y ∈ Formalism.L2.SG.RowDict.wLf X w := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, ha, rfl⟩ := hc
    exact GlobalTheory.Mem.SymFrame.inclE_smul_mem_wLf X w a ha hy
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | smul r a _ ha =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r ha

theorem mem_wInt_of_mem_idS (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {s : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E}
    (hs : s ∈ idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal) :
    (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  let J : Ideal (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :=
    { carrier := {s | (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w}
      add_mem' := fun {a b} ha hb => by
        show ((a + b : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [Subring.coe_add]; exact add_mem ha hb
      zero_mem' := by
        show ((0 : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [ZeroMemClass.coe_zero]; exact zero_mem _
      smul_mem' := fun r {a} ha => by
        show ((r * a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        exact (wInt X w).smul_mem r ha }
  have hle : idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show ((oToS X.B.I.F X.B.I.E a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :
      X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
    refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, rfl⟩, ?_⟩
    rw [oToS_coe]
    rfl
  exact hle hs

end GlobalTheory.Mem.SymChar

namespace GlobalTheory.Mem.SymChar

theorem sigA_ew_sub_one_mem_wInt : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X _ _ kv hg hne
  set w := D.naut.plGw kv.1 kv.2 with hw
  have h1 : 1 - X.ew - sigA X.B.I X.ew ∈ wInt X w :=
    wInt_of_zmod X kv.1 hg (Formalism.L2.SG.Pf.SatGram.one_sub_ew X)
  let PP := Formalism.L2.SG.Pf.RowDictPf.wB X w
  let e : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  have hidem : e * (1 - e) = 0 := by
    apply Subtype.ext
    show X.ew * (1 - X.ew) = 0
    rw [mul_sub, mul_one, X.ew_idem, sub_self]
  have hr : resS X.B.I.F PP e * resS X.B.I.F PP (1 - e) = 0 := by rw [← map_mul, hidem, map_zero]
  have he : X.ew ∈ wInt X w := by
    rcases mul_eq_zero.1 hr with h | h
    · exact mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP e).1 h)
    · exfalso
      apply hne
      intro y hy
      have := mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP (1 - e)).1 h)
      exact smul_mem_wLf_of_mem_wInt X w this hy
  have e2 : sigA X.B.I X.ew - 1 = -X.ew - (1 - X.ew - sigA X.B.I X.ew) := by ring
  rw [e2]
  exact sub_mem (neg_mem he) h1

end GlobalTheory.Mem.SymChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open GlobalTheory.Mem.SymFrame GlobalTheory.Mem.SymChar in
theorem GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg hEw hs m j
  have hm := m.2
  have hZ : ∀ c, ZMod' X.B.I X.B.g c → c ∈ wInt X (D.naut.plGw kv.1 kv.2) :=
    fun c hc => wInt_of_zmod X kv.1 hg hc
  have hS : ∀ v, ZMod' X.B.I X.B.g (hA X.B.I v (X.bw m)) → hA X.B.I (X.bw m) v ∈ wInt X (D.naut.plGw kv.1 kv.2) := by
    intro v hv
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I v (X.bw m)]
    exact hZ _ (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ hv)
  have hB : ∀ l : Fin D.R.k, hA X.B.I (X.bw m) (X.bwd l) - (if l = m then 1 else 0) ∈
      wInt X (D.naut.plGw kv.1 kv.2) := by
    intro l
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ (X.bw_dual l m)
    rw [map_sub, apply_ite (sigA X.B.I), map_zero] at h
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I (X.bwd l) (X.bw m)]
    by_cases hl : l = m
    · simp only [hl, if_true] at h ⊢
      have := add_mem (hZ _ h) hs
      convert this using 1
      ring
    · simp only [hl, if_false] at h ⊢
      simpa using hZ _ h
  unfold symVec epsW
  rw [if_neg hEw]
  unfold GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 ⟨j.1, h1⟩).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]
    have e : ((Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)) = m) ↔ j.val = D.R.rS + D.R.k - 1 - m.val := by
      rw [Fin.ext_iff, Fin.val_rev]; simp only [Fin.val_mk]; constructor <;> intro h <;> omega
    have := hB (Fin.rev ⟨j.1 - D.R.rS, by omega⟩)
    by_cases h' : j.val = D.R.rS + D.R.k - 1 - m.val
    · rw [if_pos h']; rwa [if_pos (e.2 h')] at this
    · rw [if_neg h']; rwa [if_neg (fun hh => h' (e.1 hh))] at this
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by omega), sub_zero]
    exact hS _ (X.weightVectorsIntegral m).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 _).2.1
  · rw [dite_eq_right h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact zero_mem _

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realIntertwiner_of_compactGroup_intertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank) (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank), IsInfFam θ → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → (∀ τ, FiniteDimensional ℂ (M'.H τ) ∧ M'.sm τ = ⊤) → I ≠ 0 → (∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) → (∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ x, I (ρ τ g φ) x = actT M τ g (I φ x)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ x, I (ρ' τ h φ) (actT M' τ h x) = I φ x) → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)), Function.Injective pt → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ)) → IsItW θ M M' ω pt It := by
  first | exact @GlobalTheory.CompactIntertwiner.exists_isItW | exact GlobalTheory.CompactIntertwiner.exists_isItW | (intros; apply GlobalTheory.CompactIntertwiner.exists_isItW <;> assumption)
end
