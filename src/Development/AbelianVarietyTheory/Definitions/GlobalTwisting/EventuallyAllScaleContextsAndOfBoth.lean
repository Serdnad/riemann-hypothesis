module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.Fc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

theorem eventuallyAllScaleContexts_and_of_both {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  apply _root_.GlobalTheory.Mem.Top.V4.TwoPass.ev_and <;> assumption

theorem eventuallyAllScaleContexts_mono_of_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  apply _root_.GlobalTheory.Mem.Top.V4.TwoPass.ev_mono <;> assumption

def sAnd (Q R : V4.Slot) : V4.Slot := fun K X f T c => Q K X f T c ∧ R K X f T c

def LargeBaseCondition (KP : ∀ B : Base, Fr B.toPre → Prop) (Q R : V4.Slot) : Prop :=
  EvLg fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

variable {KP : ∀ B : Base, Fr B.toPre → Prop} {Q Q' R R' : V4.Slot} {Bd : BdT} {Lk : LkT Bd}

theorem LargeBaseCondition.and (h : LargeBaseCondition KP Q R) (h' : LargeBaseCondition KP Q R') : LargeBaseCondition KP Q (sAnd R R') :=
  eventuallyAllScaleContexts_mono_of_imp (fun _ H => (H.1.inter H.2).imp fun _ _ _ _ t k C W V S N G c q => ⟨t.1 k C W V S N G c q, t.2 k C W V S N G c q⟩)
    (eventuallyAllScaleContexts_and_of_both h h')


variable (KP Q Q' Lk) in
def RowL (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) : Prop := ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ Row (sAnd Q' R) Lk H


variable (KP Q Q' Lk) in
def ExBL : Prop := ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk

theorem Row.strengthen {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (hQ : ∀ K X f T c, Q K X f T c → Q' K X f T c) (h : Row Q' Lk H) :
    Row Q Lk H := Row.map (fun _ _ _ b => b) hQ (fun _ _ _ _ _ t => t) h

theorem RowL.and {H H' : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (h : RowL KP Q Q' Lk H) (h' : RowL KP Q Q' Lk H') :
    RowL KP Q Q' Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ := by
  obtain ⟨R, r, h⟩ := h
  obtain ⟨R', r', h'⟩ := h'
  exact ⟨_, r.and r', (h.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.1⟩).and (h'.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩)⟩

theorem RowL.elim {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (hx : ExBL KP Q Q' Lk) (h : RowL KP Q Q' Lk H) :
    ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ ExB (sAnd Q' R) Lk ∧ Row (sAnd Q' R) Lk H := by
  obtain ⟨R, r, hx⟩ := hx
  obtain ⟨R', r', h⟩ := h
  exact ⟨_, r.and r', EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) hx, h.strengthen fun _ _ _ _ _ t => ⟨t.1, t.2.2⟩⟩

theorem Row.rowL {H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop} (r : LargeBaseCondition KP Q R) (h : Row Q' Lk H) : RowL KP Q Q' Lk H :=
  ⟨R, r, h.strengthen fun _ _ _ _ _ t => t.1⟩

theorem largeBaseProperty_true : LargeBaseCondition KP Q fun _ _ _ _ _ => True :=
  ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    ⟨0, fun _ _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial⟩⟩⟩⟩⟩⟩

end GlobalTheory.Fc

end
