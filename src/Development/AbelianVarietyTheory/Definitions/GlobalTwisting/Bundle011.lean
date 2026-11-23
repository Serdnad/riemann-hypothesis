module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SquareIntegrableColumnsCompatible
public import Formalism.LocalToGlobal.ThresholdSelection
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle030
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
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

section

noncomputable section

namespace GlobalTheory.Fc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

theorem eventuallyAllScaleContexts_and_of_both {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem eventuallyAllScaleContexts_mono_of_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

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
end

section

noncomputable section

namespace GlobalTheory.Fc.R0

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top GlobalTheory.Fc

def ClassCountBoundAllPoints (𝒜 : FamClass) : Prop :=
  Closed (W1 𝒜) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev

def ClassCountBoundAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ClassCountBoundAllPoints 𝒜

def H_jOn (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤

def JInvariantConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_jOn 𝒜

def H_la (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

def LambdaConditionAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_la 𝒜

end GlobalTheory.Fc.R0

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top

namespace GlobalTheory.Cp

abbrev BaseLevelCompatibleSelection (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // Formalism.L2.Rows.RowSideDetermined ((sel Fm hc).2 x hx h i).T P}

abbrev SelDH (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}

abbrev ColumnCompatibleSelection (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selP : BaseLevelCompatibleSelection 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    SquareIntegrableColumnsCompatible ((sel Fm hc).2 x hx h i).T (selP Fm hc x hx h i).1

abbrev SelS (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.L2.SG.SpectralTiesReal.STiesR ((sel Fm hc).2 x hx h i)

def ZscAt {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Indef.DefSub (selP Fm hc x hx h i).1.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale (selP Fm hc x hx h i).1.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _) (Fm.L x i).Nc Zs
    { z with l6m := fun j => z.l6m j - Fm.Csz * z.l6u, l6u := 0 }

abbrev SelB (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) (selC : ColumnCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.IndefR.RealTB ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (ZscAt sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)

def EvSel {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx h i

end GlobalTheory.Cp

namespace GlobalTheory.Fc

open GlobalTheory.Cp

def zsc {D : D7} {O : Obj D} (P : Formalism.L2.Rows.RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D O.L Del h0) (Equiv.refl _) O.L.Nc Zs
    { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Bundle (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : Formalism.L2.RecT O.ex
  S : Formalism.L2.SG.SpectralTiesReal.STiesR R
  P : Formalism.L2.Rows.RowSideFamily O.ex
  pin : Formalism.L2.Rows.RowSideDetermined R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  C : SquareIntegrableColumnsCompatible R.T P
  B : Formalism.IndefR.RealTB R P C.c.face C.Sp (zsc P DH.1.1 DH.1.2 c) S

variable {𝒜 : FamClass} (σ : RawSel Bundle 𝒜)

def sel : Formalism.L2.TSel 𝒜 := fun Fm hc => (⟨Fm.x1, fun x hx _ i => (σ Fm hc x hx i).R⟩ : Formalism.L2.TSelF Fm)

def selS : SelS 𝒜 (sel σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).S

def selP : BaseLevelCompatibleSelection 𝒜 (sel σ) := fun Fm hc x hx _ i => ⟨(σ Fm hc x hx i).P, (σ Fm hc x hx i).pin⟩

def selDH : SelDH 𝒜 (sel σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).DH

def selC : ColumnCompatibleSelection 𝒜 (sel σ) (selP σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).C

def selB : SelB 𝒜 (sel σ) (selS σ) (selP σ) (selDH σ) (selC σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).B

end GlobalTheory.Fc

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.AllBundlePointProperties

open GlobalTheory.Fc

def LevelPrimeColumnValuationsClosed (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u

def LevelPrimeColumnValuationsAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => LevelPrimeColumnValuationsClosed 𝒜

def H_aAtG (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1

def ArithmeticConditionAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aAtG 𝒜

end GlobalTheory.Fc.AllBundlePointProperties

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.ClassTwoEntries

open GlobalTheory.Fc

def H_hInstR (𝒜 : FamClass) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∀ (x : ℝ) (_ : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank

def InstanceRankAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_hInstR 𝒜

def DivisionSecondComplementAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm

def DivisionSecondComplementAtConstructedPoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => DivisionSecondComplementAdmissible 𝒜

end GlobalTheory.Fc.ClassTwoEntries

end
end
