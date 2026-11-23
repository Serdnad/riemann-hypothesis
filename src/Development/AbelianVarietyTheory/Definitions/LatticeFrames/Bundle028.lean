module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

section Frame

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : Formalism.BasicNotions.TH.HSp D}

theorem besVec_ne_zero (B : SBes X h u ψ A) : B.d.i₀ *ᵥ vecB B.o B.ζ ≠ 0 := fun h0 => by
  apply B.line.2
  have e : B.L.gram *ᵥ B.ζ = (B.o.iBᴴ * (B.d.i₀ᴴ * (D.sp.Y 0).gram)) *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) := by
    rw [← B.o.isoB, ← B.d.iso]
    simp only [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, h0]; simp

end Frame

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def InPlace : Prop := Placed f B ∧ Framed B

variable {f B}

variable (f B)

theorem shift_tOf (a₀ a : GA D (D.sp.X 0)) :
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * tOf f B a₀ a =
      embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) := by
  unfold tOf
  rw [mul_assoc, mul_inv_cancel_left]

theorem tOf_eq_iff (a₀ a : GA D (D.sp.X 0)) (t : GA D (D.sp.Y 0)) :
    tOf f B a₀ a = t ↔ embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0) =
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * t := by
  rw [← shift_tOf, mul_right_inj]

end GlobalTheory.MiTop

end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

abbrev chrK (W : RealPack ex) (t : W.P.T) (j : ℕ) : (AE (I.rec7 l Z))ˣ →* Circle := (pk W).toLevCh.mu t (j + 1)



structure QJ (a : GeoAll W u) (t : W.P.T) where
  Ch₀ : ℕ → Type
  A : TwDat I l Z u (W.P.I.tup t) Ch₀
  r : ℕ
  pl : Fin r → Pl (I.rec7 l Z).host.E
  mem : ∀ i, pl i ∈ (pk W).Q t
  E : ∀ i, QExt (a.Q (pl i) ⟨t, mem i⟩) (chrK W t)
  P : Fin r → BadPr I (W.P.I.tup t)
  hψ : ∀ i, Continuous (a.Q (pl i) ⟨t, mem i⟩).ψk
  sg : Fin r → ℂ
  π : ∀ i j, Ch₀ j → (E i).Ch j
  ι : ∀ j, (∀ i, (E i).Ch j) → Ch₀ j

variable {a : GeoAll W u} {t : W.P.T} (J : QJ a t)

abbrev QJ.G (i : Fin J.r) := a.Q (J.pl i) ⟨t, J.mem i⟩

abbrev QJ.Ch (j : ℕ) : Type := ∀ i, (J.E i).Ch j

structure QJ.Reads : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (pk W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = chrK W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((pk W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))

  cos : ∀ i β (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → (J.E i).cos (J.π i ((J.G i).s + 1) β) =
      Submodule.Quotient.mk fun r => (ofSplit (J.G i).q).pr (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2 (e r))

  std : ∀ j, j + 1 < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)

  pen : ∀ j (hj : j + 1 = B.R.m) β, ∃ k₀ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j),
    k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) k₀ = (TC.kStd X u (B.R.N j)).1 ∧ J.A.kA j β = k₀ * h ∧
    h ∈ GlobalTheory.FinPl.grpAt _ (fun p => ∃ i, (J.G i).q.v = p) ∧
    ∀ i (e : (J.G i).s + 1 = j), ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
      (mt _ (e ▸ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1)))).map (J.G i).q.pr =
        ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i

  cosG : ∀ (n : Fin a.n) y (e : XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r,
      (ofSplit (a.G n).q).pr (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ y)).1.2 (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k]
  live : J.A.Live J.ι

end GlobalTheory.Fam

end
end
