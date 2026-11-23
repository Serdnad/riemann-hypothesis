module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle703
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle705
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle708
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.representation_at_every_place : Big fun ch => ∀ s, RepAt ch s := by
  first | exact @GlobalTheory.RowRep.rep_at | exact GlobalTheory.RowRep.rep_at | (intros; apply GlobalTheory.RowRep.rep_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.jacobiFrameOfGridLattice_largeDepth : Big fun ch => JacP ch := by
  first | exact @GlobalTheory.FlatPlace.big_jacP | exact GlobalTheory.FlatPlace.big_jacP | (intros; apply GlobalTheory.FlatPlace.big_jacP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.lastTwoSteps_topVertex_frame_at_place : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (j : ℕ) (hj : j + 2 = D.R.m),
    ∃ e : Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit ≃ Fin (topRank (locGrid ch.G t w) (j + 1 + 1)),
      (∀ i, (e (Sum.inl i)).val = i.val) ∧ (e (Sum.inr ())).val = topRank (locGrid ch.G t w) (j + 1 + 1) - 1 ∧
      ∃ FX : Frame (Kw w) (ch.G.V (.top (j + 1 + 1))).rank (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit),
        FX.β = fromCols ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iA.map p.pr * (frRow ch.S.B t w D.R.m le_rfl).β)
          (Matrix.of fun r _ => ((topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)).iB.map p.pr *ᵥ fun _ => (1 : Kw w)) r) ∧
        ∀ r z, FX.β r z = (frTop ch.S.toGridChoice t w (j + 1 + 1) (by omega)).β r (e z) := by
  first | exact @GlobalTheory.FlatPlace.frame_top_last | exact GlobalTheory.FlatPlace.frame_top_last | (intros; apply GlobalTheory.FlatPlace.frame_top_last <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth : Big fun ch => LocP ch := by
  first | exact @GlobalTheory.FlatPlaceLoc.localization₂ | exact GlobalTheory.FlatPlaceLoc.localization₂ | (intros; apply GlobalTheory.FlatPlaceLoc.localization₂ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.flatTensor_pureTensor_eq_prod_localFactors : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s), 2 ≤ G.m → Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (GlobalTheory.SplitFlip.oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * ∏ n ∈ Finset.range (G.m / 2), locA G hs ψ ν φ (2 * n) (x (2 * n), x (2 * n + 1)) := by
  first | exact @GlobalTheory.FlatPlace.flatTensor_pureTensor_eq_prod_locA | exact GlobalTheory.FlatPlace.flatTensor_pureTensor_eq_prod_locA | (intros; apply GlobalTheory.FlatPlace.flatTensor_pureTensor_eq_prod_locA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.flatDictionaryScalar_largeDepth : Big fun ch => ScalP ch := by
  first | exact @GlobalTheory.FlatScal.scal | exact GlobalTheory.FlatScal.scal | (intros; apply GlobalTheory.FlatScal.scal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.lastTwoSteps_localModel_extendByZero_topStep : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w))
    (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m))
    (h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1)),
    ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m D.R.m)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃) (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x) := by
  first | exact @GlobalTheory.LastStepExt0.model_last | exact GlobalTheory.LastStepExt0.model_last | (intros; apply GlobalTheory.LastStepExt0.model_last <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.exists_localModel_movedFrames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z Z' : Type) [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) Tm, p.IsModel ψ FS FT Tm → ∀ (a : GA D S) (b : GA D T) (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y), ∃ Tm', p.IsModel ψ (mvFr p a FS εS σS) (mvFr p b FT εT σT) Tm' ∧ ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)), (∀ x, Φ.1 x = Φ'.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS)) → Tm' Φ' = ω (a, b) (Tm Φ) := by
  first | exact @GlobalTheory.FlatPlace.exists_isModel_mvFr | exact GlobalTheory.FlatPlace.exists_isModel_mvFr | (intros; apply GlobalTheory.FlatPlace.exists_isModel_mvFr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.frameLattice_points_eq_integralMatrices_largeDepth : Big fun ch => LatP ch := by
  first | exact @GlobalTheory.FlatPlace.big_latP | exact GlobalTheory.FlatPlace.big_latP | (intros; apply GlobalTheory.FlatPlace.big_latP <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.localCharacterComponents_largeDepth : Big fun ch => ChrP ch := by
  first | exact @GlobalTheory.FlatPlace.chrP_big | exact GlobalTheory.FlatPlace.chrP_big | (intros; apply GlobalTheory.FlatPlace.chrP_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBaseUniq
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem smul_eq_of_adj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {c : R} {A A' X X' G H : Matrix n n R}
    (h : A * (G * X) = G) (h' : A' * (G * X') = G) (hH : G * H = 1) (e : c • A = c • A') : c • X = c • X' := by
  have h1 : A * G * (X * H) = 1 := by rw [← Matrix.mul_assoc, Matrix.mul_assoc A, h, hH]
  have h2 : X * H * (A * G) = 1 := mul_eq_one_comm.1 h1
  have h3 : A * G * (c • X) = A * G * (c • X') := by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, h, ← Matrix.smul_mul, e, Matrix.smul_mul, h']
  have h4 := congrArg (X * H * ·) h3
  simp only [← Matrix.mul_assoc (X * H) (A * G), h2, Matrix.one_mul] at h4
  exact h4

theorem eq_of_halves {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b : R} {X X' : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (h' : ∀ i j, (a + b) * (X' - 1) i j = (X' - 1) i j)
    (ha : a • X = a • X') (hb : b • X = b • X') : X = X' := by
  ext i j
  have k1 : a * X i j = a * X' i j := congrFun (congrFun ha i) j
  have k2 : b * X i j = b * X' i j := congrFun (congrFun hb i) j
  have k3 := h i j
  have k4 := h' i j
  simp only [Matrix.sub_apply] at k3 k4
  linear_combination k1 + k2 - k3 + k4

theorem supp_shrink {R : Type} [CommRing R] {n : Type} [DecidableEq n] {a b a' b' : R} {X : Matrix n n R}
    (h : ∀ i j, (a + b) * (X - 1) i j = (X - 1) i j) (ha : (a - a') • X = (a - a') • (1 : Matrix n n R))
    (hb : (b - b') • X = (b - b') • (1 : Matrix n n R)) (i j : n) : (a' + b') * (X - 1) i j = (X - 1) i j := by
  have k1 : (a - a') * X i j = (a - a') * (1 : Matrix n n R) i j := congrFun (congrFun ha i) j
  have k2 : (b - b') * X i j = (b - b') * (1 : Matrix n n R) i j := congrFun (congrFun hb i) j
  have k3 := h i j
  simp only [Matrix.sub_apply] at k3 ⊢
  linear_combination k3 - k1 - k2

variable {D : D7}

theorem smul_conj {V : HSp D} {e : AE D} {g g' : GA D V} (h : e • mt V g = e • mt V g') :
    cA D e • mt V g = cA D e • mt V g' :=
  smul_eq_of_adj (mt_unitary V g) (mt_unitary V g') (gA_mul_giA V)
    ((adj_smul e _).symm.trans ((congrArg adj h).trans (adj_smul e _)))

theorem smul_eq_of_loc {V : HSp D} {e : AE D} (h0 : infPart D e = 0) {g g' : GA D V}
    (h : ∀ w : Pl D.host.E, piAt w e = 0 ∨ GlobalTheory.StdFrames.loc w (Lev.finE V g) = GlobalTheory.StdFrames.loc w (Lev.finE V g')) :
    e • mt V g = e • mt V g' := by
  refine mx_ext ?_ fun w => ?_
  · rw [map_smul_mx, map_smul_mx, h0, zero_smul, zero_smul]
  · rw [map_smul_mx, map_smul_mx]
    rcases h w with h | h
    · rw [h, zero_smul, zero_smul]
    · exact congrArg (piAt w e • ·) (congrArg Units.val h)

theorem loc_eq_of_inBasis {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x y : GL (Fin n) (Lev.EAf D)}
    (e : inBasis h β w x = inBasis h β w y) : GlobalTheory.StdFrames.loc w x = GlobalTheory.StdFrames.loc w y := by
  have e1 : GlobalTheory.StdFrames.loc w (β⁻¹ * x * β⁻¹⁻¹) = GlobalTheory.StdFrames.loc w (β⁻¹ * y * β⁻¹⁻¹) :=
    (GlobalTheory.StepData.reGL _).injective e
  rw [map_mul, map_mul, map_mul, map_mul] at e1
  exact mul_left_cancel (mul_right_cancel e1)

theorem isFinOf_unique {V : HSp D} {g b b' : GA D V} (h : IsFinOf g b) (h' : IsFinOf g b') : b = b' := by
  obtain ⟨hb, a, ha, e⟩ := h
  obtain ⟨hb', a', ha', e'⟩ := h'
  have i : infHom V b = infHom V b' := (MonoidHom.mem_ker.1 hb).trans (MonoidHom.mem_ker.1 hb').symm
  have f : finHom V b = finHom V b' := by
    have := congrArg (finHom V) (e.trans e'.symm)
    rwa [map_mul, map_mul, MonoidHom.mem_ker.1 ha, MonoidHom.mem_ker.1 ha', one_mul, one_mul] at this
  have f' : Lev.finE V b = Lev.finE V b' := congrArg (Formalism.UG.bc (Lev.swapAE D)) f
  refine Subtype.ext (Units.ext (mx_ext (congrArg Units.val i) fun w => ?_))
  exact congrArg (fun z => (GlobalTheory.StdFrames.loc w z).val) f'

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_indicator (P : Finset (Pl D.host.E)) :
    ∃ e : AE D, infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 := by
  obtain ⟨X, a, b, c⟩ := exists_lift (n := 1) P fun _ => 1
  exact ⟨X 0 0, congrFun (congrFun a 0) 0, fun w hw => (congrFun (congrFun (b ⟨w, hw⟩) 0) 0).trans (one_apply_eq _),
    fun w hw => congrFun (congrFun (c w hw) 0) 0⟩

theorem stair_off (t : T) {w : Pl D.host.E} (hw : w ∉ G.pl.W0) (j : ℕ) :
    stair (locGrid G t w) (unifAt w) (cosExp G w) j = 1 := by
  rw [(depthAt_of_notMem G hw).1, stair]
  simp only [zero_mul, pow_zero]
  exact Units.ext diagonal_one

theorem supp_base (B : Frames G) {t : T} {r : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) {e₀ : AE D}
    (h0 : infPart D e₀ = 0) (h1 : ∀ w ∈ G.pl.W0, piAt w e₀ = 1) (h2 : ∀ w ∉ G.pl.W0, piAt w e₀ = 0) : SuppAt e₀ _ r := by
  classical
  obtain ⟨e, he, hs, hl⟩ := h
  obtain ⟨e0, e1, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  replace e1 : ∀ w ∈ locPl G t, piAt w e = 1 := e1
  replace e2 : ∀ w ∉ locPl G t, piAt w e = 0 := e2
  have hsub : ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : (e - e₀) • mt _ r = (e - e₀) • mt _ (1 : GA D (G.V (.grid D.R.m 0))) := by
    refine smul_eq_of_loc (by rw [RingHom.map_sub, e0, h0, sub_self]) fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inl (by rw [RingHom.map_sub, e1 w (hsub w hw), h1 w hw, sub_self])
    · by_cases hp : w ∈ locPl G t
      · refine .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hp⟩).trans ?_))
        rw [map_one, map_one]
        exact inv_eq_one.2 (stair_off t hw 0)
      · exact .inl (by rw [RingHom.map_sub, e2 w hp, h2 w hw, sub_self])
  have k' := smul_conj k
  rw [RingHom.map_sub] at k'
  rw [GlobalTheory.MixModel.mt_one] at k k'
  exact supp_shrink hs k k'

theorem base_zero (B : Frames G) {t t' : T} {r r' : GA D (G.V (.grid D.R.m 0))}
    (h : HasLoc t B (Nat.zero_le _) r fun w => (stair (locGrid G t w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹)
    (h' : HasLoc t' B (Nat.zero_le _) r' fun w => (stair (locGrid G t' w.1) (unifAt w.1) (cosExp G w.1) 0)⁻¹) : r = r' := by
  classical
  obtain ⟨e₀, h0, h1, h2⟩ := exists_indicator (D := D) G.pl.W0
  have s := supp_base B h h0 h1 h2
  have s' := supp_base B h' h0 h1 h2
  obtain ⟨-, -, -, hl⟩ := h
  obtain ⟨-, -, -, hl'⟩ := h'
  have hsub : ∀ t, ∀ w ∈ G.pl.W0, w ∈ locPl G t := fun t w hw => by
    unfold locPl; convert Finset.mem_union_left _ hw
  have k : e₀ • mt _ r = e₀ • mt _ r' := by
    refine smul_eq_of_loc h0 fun w => ?_
    by_cases hw : w ∈ G.pl.W0
    · exact .inr (loc_eq_of_inBasis _ (B.β D.R.m 0) w ((hl ⟨w, hsub t w hw⟩).trans (hl' ⟨w, hsub t' w hw⟩).symm))
    · exact .inl (h2 w hw)
  exact Subtype.ext (Units.ext (eq_of_halves s s' k (smul_conj k)))

theorem isBase_eq (B : Frames G) {t t' : T} {b b' : Pts G} (h : IsBase t B b) (h' : IsBase t' B b') : b = b' := by
  funext j
  by_cases h0 : j = 0
  · subst h0
    exact base_zero B h.1 h'.1
  · by_cases hj : j ∈ GlobalTheory.RowVal.idx D
    · obtain ⟨δ, hδ, hb⟩ := h.2.1 j hj
      obtain ⟨δ', hδ', hb'⟩ := h'.2.1 j hj
      obtain rfl := isTilt_unique (by have := idx_le hj; omega) hδ hδ'
      exact isFinOf_unique hb hb'
    · rw [h.2.2 j h0 hj, h'.2.2 j h0 hj]

theorem isBase_unique : Big fun ch => ∀ t t' b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' → b = b' :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ _ _ _ _ h h' => isBase_eq ch.S.B h h'⟩⟩

end GlobalTheory.RowBaseUniq

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceCut

theorem idem_mul {D : D7} {e e' : AE D} {w w' : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') : (w = w' → e * e' = e) ∧ (w ≠ w' → e * e' = 0) := by
  have i0 : infPart D e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) h).1
  have a1 : GlobalTheory.RowRep.piAt w e = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).1
  have a2 : ∀ u, u ≠ w → GlobalTheory.RowRep.piAt u e = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).2
  have b1 : GlobalTheory.RowRep.piAt w' e' = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').1
  have b2 : ∀ u, u ≠ w' → GlobalTheory.RowRep.piAt u e' = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').2
  have i1 : infPart D (e * e') = 0 :=
    ((infPart D).map_mul e e').trans ((congrArg (· * infPart D e') i0).trans (zero_mul _))
  refine ⟨fun hw => ae_ext (i1.trans i0.symm) fun u => ?_, fun hw => ae_ext (i1.trans (infPart D).map_zero.symm) fun u => ?_⟩
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u e
    rw [RingHom.map_mul]
    by_cases hu : u = w
    · subst hu; subst hw; rw [b1, mul_one]
    · rw [a2 u hu, zero_mul]
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u 0
    rw [RingHom.map_mul, RingHom.map_zero]
    by_cases hu : u = w
    · subst hu; rw [b2 u hw, mul_zero]
    · rw [a2 u hu, zero_mul]

theorem mul_conj_zero {R ι : Type} [CommRing R] (c : R →+* R) (P : Finset ι) (a : ι → R)
    (h1 : ∀ i ∈ P, a i * a i = a i) (h2 : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → a i * a j = 0)
    (h0 : (∑ i ∈ P, a i) * c (∑ i ∈ P, a i) = 0) : ∀ i ∈ P, ∀ j ∈ P, a i * c (a j) = 0 := by
  have k : ∀ i ∈ P, a i * ∑ j ∈ P, a j = a i := fun i hi => by
    rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h2 i hi j hj (Ne.symm hji)) (fun h => absurd hi h), h1 i hi]
  intro i hi j hj
  rw [← k i hi, ← k j hj, map_mul, mul_mul_mul_comm, h0, mul_zero]

theorem add_mul_self_eq_of_orthogonal_idempotents {R : Type} [CommRing R] {a b : R} (h1 : a * a = a) (h2 : b * b = b) (h3 : a * b = 0) :
    (a + b) * (a + b) = a + b := by linear_combination h1 + h2 + 2 * h3

theorem add_mul_add_eq_zero_of_pairwise_products_zero {R : Type} [CommRing R] {a b a' b' : R} (h1 : a * a' = 0) (h2 : b * b' = 0) (h3 : a * b' = 0)
    (h4 : a' * b = 0) : (a + b) * (a' + b') = 0 := by linear_combination h1 + h2 + h3 + h4

theorem map_cut {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} {a b : R} (h1 : f a = 1) (h0 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) R) :
    ((a + b) • M + (1 - (a + b)) • (1 : Matrix (Fin n) (Fin n) R)).map f = M.map f := by
  have hb : f b = 0 := by
    have := congrArg f h0
    rwa [map_mul, h1, one_mul, map_zero] at this
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, h1, hb]
  ring



theorem exists_prod_pieces : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (es w) w) → (∑ w ∈ P, es w) * cA D (∑ w ∈ P, es w) = 0 → ∀ r : GA D V, SuppAt (∑ w ∈ P, es w) V r → ∃ h : P → GA D V, (∀ w, SuppAt (es w.1) V (h w)) ∧ (∀ w, (mt V (h w)).map (GlobalTheory.RowRep.piAt w.1) = (mt V r).map (GlobalTheory.RowRep.piAt w.1)) ∧ r = (Finset.univ.toList.map h).prod := by
  intro D V P es hes h0 r hr
  have h1 : ∀ w ∈ P, es w * es w = es w := fun w hw => (idem_mul (hes w hw) (hes w hw)).1 rfl
  have h2 : ∀ w ∈ P, ∀ w' ∈ P, w ≠ w' → es w * es w' = 0 := fun w hw w' hw' => (idem_mul (hes w hw) (hes w' hw')).2
  have h3 := mul_conj_zero (cA D) P es h1 h2 h0
  let E : P → AE D := fun w => es w.1 + cA D (es w.1)
  have hEE : ∀ w, E w * E w = E w := fun w =>
    add_mul_self_eq_of_orthogonal_idempotents (h1 _ w.2) (by rw [← RingHom.map_mul, h1 _ w.2]) (h3 _ w.2 _ w.2)
  have hEc : ∀ w, cA D (E w) = E w := fun w => by
    show cA D (es w.1 + cA D (es w.1)) = es w.1 + cA D (es w.1)
    rw [RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    have := h2 _ w.2 _ w'.2 fun h => hww (Subtype.ext h)
    exact add_mul_add_eq_zero_of_pairwise_products_zero this (by rw [← RingHom.map_mul, this, RingHom.map_zero]) (h3 _ w.2 _ w'.2) (h3 _ w'.2 _ w.2)
  choose h hh using fun w => GlobalTheory.SplitCut.cut_exists V r (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hh w]
    exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hh w]
    have a1 : GlobalTheory.RowRep.piAt w.1 (es w.1) = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes _ w.2)).1
    exact map_cut (GlobalTheory.RowRep.piAt w.1) a1 (h3 _ w.2 _ w.2) _
  · apply GlobalTheory.SplitCut.mt_injective
    have hsum : (Finset.univ.toList.map E).sum = (∑ w ∈ P, es w) + cA D (∑ w ∈ P, es w) := by

      rw [Finset.sum_map_toList, map_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_coe_sort P fun w => es w + cA D (es w)
    rw [GlobalTheory.SplitCut.mt_list_prod V h E (mt V r) hh hEo _ (Finset.nodup_toList _), hsum]
    refine GlobalTheory.SplitCut.exists_widePullback_of_iteratedLine _ _ fun i j => ?_
    rw [sub_mul, one_mul, hr i j, sub_self]

end GlobalTheory.PlaceCut

end
end
