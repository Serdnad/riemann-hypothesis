module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle013
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle055
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle956
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
section Fit
open GlobalTheory.ChiGrid Formalism.L2.Host
variable {T : Type} {Lc : LevCh D T} {sc : Consts}
end Fit
def LeafConditions (Comparison₂ : TieT) (Q : PropT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, ∀ C, C0 ≤ C → _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ d : FunIn p CF, Comparison₂ p CF d → Q p CF d C CH
def ExistsFunctionIn (Fld : FldT) (Comparison₂ : TieT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat → GridFit p G → Fld p CF G W →
    ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d
def LeafMinimalMass (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d C _ => LeafMM d.O C
def LeafUniqueMap (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d _ _ =>
  ∃ ze : Tup p → _, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
    LeafC (p.S false) (d.data ze ∅ fun _ => 0)
def LeafKernel (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d _ _ => LeafKer d.O
def LeafFixedPoint (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b
def LeafHeightMapBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ =>
  ∀ vb : Matrix (Fin d.n) (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0)) _,
    vb * (Df p).Pq p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 →
      Formalism.HN.htMap (Pi.basisFun _ (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0))) ((Df p).XQ p.P.A3.fam3.base3.μ0)
        (Pi.basisFun _ (Fin d.n)) d.X' (Matrix.mulVecLin vb) ≤ d.O.bIPa C p.Z.b
def LeafInfinitePlaceBound : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ =>
  ∃ g : InfinitePlace _ → ℝ, (∀ v q, (Df p).Qp p.P.A3.fam3.base3.μ0 q ≠ ⊥ →
      g v ≤ ∑ j, Real.log ((p.S false).lam j p.P.A3.fam3.base3.μ0 q v)) ∧
    -(3 * C * d.O.f * d.O.m * (d.O.N : ℝ) ^ 2 * Real.log p.Z.b) ≤ Formalism.PairingDivisionLocalBalance.meanInf _ g
def LeafUniqueSquareRoot (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafOneSquare d.O (p.S false).μ C p.Z.b
def LeafDensity (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => PrimeCountingSumBound d.O C p.Z.x p.Z.b
def LeafIntegrality (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafINT d.O C p.Z.b
def ArchimedeanCondition (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafARCH d.O C p.Z.b
def LeafThetaBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafTHB d.O C p.Z.x p.Z.b
def LeafWeightBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafWt d.O C p.Z.b
def DescentHeightCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d _ _ => leafHypothesesConst d.O ∧ LatticeConstantBound d.O p.Z.b
def RankGapBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => DegreeAndSizeBounds d.O C p.Z.b
def RamifiedSumBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => PrimePowerModuliSumBound d.O C p.Z.b ∧ LeafCS d.O p.Z.b
def DescentPolynomialCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C CH => LeafPol d.O C p.Z.x CH p.Z.b
def ScaleCondition : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p =>
  1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
def BundleCondition : Prop := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' →
  (Df p).WF ∧ ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false
def ConstantFunctionFits (Fld : FldT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => HasGrid Fld p CF → ∀ C, (p.S false).FUN (p.N C CH)
theorem evPt_and' {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (hQ : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => P x hx i p ∧ Q x hx i p :=
  let ⟨a, ha⟩ := hP
  let ⟨b, hb⟩ := hQ
  ⟨max a b, fun x hx h i p hp => ⟨ha x hx (le_of_max_le_left h) i p hp, hb x hx (le_of_max_le_right h) i p hp⟩⟩
theorem evPt_mono {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (h : ∀ x hx i p, p.PointConditions' → P x hx i p → Q x hx i p) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun x hx h' i p hp => h x hx i p hp (ha x hx h' i p hp)⟩
theorem LeafConditions.mono {Comparison₂ Tie' : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q)
    (h' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF) (C CH : ℝ), p.PointConditions' → Tie' p CF d →
      Comparison₂ p CF d ∧ (Q p CF d C CH → Q' p CF d C CH)) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Tie' Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ a hN => ?_⟩
  obtain ⟨C0, a⟩ := a hN
  exact ⟨C0, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (a C hC) fun _ _ _ p hp b d hd =>
    (h' p CF d C CH hp hd).2 (b d (h' p CF d C CH hp hd).1)⟩
theorem LeafConditions.and {Comparison₂ : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q) (h' : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q') :
    _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ fun p CF d C CH => Q p CF d C CH ∧ Q' p CF d C CH := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  refine ⟨max a b, fun CF hCF => ((h CF (le_of_max_le_left hCF)).and (h' CF (le_of_max_le_right hCF))).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1 hN
  obtain ⟨C1, c2⟩ := c.2 hN
  exact ⟨max C0 C1, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 C (le_of_max_le_left hC)) (c2 C (le_of_max_le_right hC)))
    fun _ _ _ _ _ e d hd => ⟨e.1 d hd, e.2 d hd⟩⟩
theorem LeafConditions.of_noTie {Q : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition Q) (Comparison₂ : TieT) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q :=
  h.mono fun _ _ _ _ _ _ _ => ⟨trivial, id⟩
theorem fun0Fit_of_leaves_alt (Fld : FldT) (Comparison₂ : TieT) (hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition) (hS : _root_.GlobalTheory.BigTop.Fun.ScaleCondition) (hE : _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn Fld Comparison₂) (h1 : _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass Comparison₂) (h2 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap Comparison₂)
    (h3 : _root_.GlobalTheory.BigTop.Fun.LeafKernel Comparison₂) (h4 : _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint Comparison₂) (h5 : _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound Comparison₂) (h6 : _root_.GlobalTheory.BigTop.Fun.LeafInfinitePlaceBound) (h7 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueSquareRoot Comparison₂) (h8 : _root_.GlobalTheory.BigTop.Fun.LeafDensity Comparison₂) (h9 : _root_.GlobalTheory.BigTop.Fun.LeafIntegrality Comparison₂) (h10 : _root_.GlobalTheory.BigTop.Fun.ArchimedeanCondition Comparison₂)
    (h11 : _root_.GlobalTheory.BigTop.Fun.LeafThetaBound Comparison₂) (h12 : _root_.GlobalTheory.BigTop.Fun.LeafWeightBound Comparison₂) (h13 : _root_.GlobalTheory.BigTop.Fun.DescentHeightCondition) (h14 : _root_.GlobalTheory.BigTop.Fun.RankGapBound') (h15 : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound') (h16 : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition) : _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits Fld := by
  obtain ⟨a, hA⟩ := _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h1 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h2 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h3 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h4 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h5 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h6 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h7 <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h8 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h9 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h10 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h11 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h12 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h13 _) <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h14 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h15 _) (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h16 _)
  obtain ⟨b, hE⟩ := hE
  refine ⟨max a b, fun CF hCF => (((hA CF (le_of_max_le_left hCF)).and (hE CF (le_of_max_le_right hCF))).and hS).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1.1 hN
  refine _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 (max C0 1) (le_max_left _ _)) (c.1.2 hN)) c.2) fun x hx i p hp e hG C => ?_
  obtain ⟨⟨e1, e2⟩, s1, s2, s3⟩ := e
  obtain ⟨G, W, g1, g2, g3⟩ := hG
  obtain ⟨d, rfl, hd⟩ := e2 G W g1 g2 g3
  obtain ⟨l1, ⟨ze, z1, z2, l2⟩, l3, ⟨Tf, dF, l4⟩, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16⟩ := e1 d ⟨g2, hd⟩
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have v0 : (d.data ze Tf dF).vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (ze _)⁻¹ • _ = _
    rw [z1, inv_one]
    exact one_smul _ _
  have v1 : ∀ Tf dF t, (d.data (fun _ => 1) Tf dF).vmu t = d.V t := fun _ _ _ => by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  have hRR := R0.RR_spec Formalism.DivisionValues.lattice_gluing wf
  refine functional_lower_bound_of_conditions_numeric wf (p.S false) p.Z C CH (d.data ze Tf dF) (max C0 1) (hR ▸ R0.D_pos) (hR ▸ R0.h0) (hR ▸ R0.l1a)
    (hR ▸ R0.l1c) (hR ▸ R0.frames.1) (hR ▸ hRR.1) (hR ▸ hRR.2) (le_max_right _ _) s1 s2 s3 l1 l2 ?_ ?_ ⟨?_, l6⟩ l7 l8 l9 l10
    l11 l13.1 l13.2 l14 l15.1 l15.2 l12 l16
  · have : LinearMap.ker (d.O.vmu _).mulVecLin = _ := l3
    rw [v1] at this
    show LinearMap.ker ((d.data ze Tf dF).vmu _).mulVecLin = _
    rw [v0]
    exact this
  · have := GlobalTheory.finitePlaceBound_inv_rootOfUnity_smul _ ze _ _ _ z2 l4
    simp only [v1] at this
    exact this
  · intro vb hvb
    exact l5 vb (hvb.trans v0)
end GlobalTheory.BigTop.Fun
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top
namespace GlobalTheory.Fc
structure AllRowsAlt (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop)
    (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) : Prop where
  hn4 : Lg1 KP Q Q' fun S => R0.ClassCountBoundAtConstructedPoints S Lk
  jOn : Lg1 KP Q Q' fun S => R0.JInvariantConditionAtConstructedPoints S Lk
  hInstR : Lg1 KP Q Q' fun S => ClassTwoEntries.InstanceRankAtConstructedPoints S Lk
  aC2 : Lg1 KP Q Q' fun S => ClassTwoEntries.DivisionSecondComplementAtConstructedPoints S Lk
  aP10 : Lg1 KP Q Q' fun S => AllBundlePointProperties.LevelPrimeColumnValuationsAtBundlePoints S Lk
  aAtG : Lg1 KP Q Q' fun S => AllBundlePointProperties.ArithmeticConditionAtBundlePoints S Lk
  aPt0 : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints S Lk
  aPtTw : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.TwistedPointAtBundlePoints S Lk
  aPer0 : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.PeriodAtZeroAtBundlePoints S Lk
  aPerTw : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints S Lk
  tie : Lg1 KP Q Q' fun S => PeriodEntriesOverColumns.Row_tie S Lk
  hRB : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotRowBoundCondition S Lk
  hTw : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTwistCondition S Lk
  hPA : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition S Lk
  hLamP : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLambdaPrimeCondition S Lk
  hDivG : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDivisorCondition S Lk
  hDcPtG : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDecompositionPointCondition S Lk
  selJ : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotSelectionJumpCondition S Lk
  sLp : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLpCondition S Lk
  sO : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotOrderCondition S Lk
  hServ : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotServiceCondition S Lk
  zL : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotZeroLocusCondition S Lk
  hTF : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition S Lk
  c30 : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' S Lk
  rRows : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition DR S Lk
  nRest : Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotNormCondition S Lk N
end GlobalTheory.Fc
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

theorem _root_.GlobalTheory.T.hTu_cTmin_of_genusMass : (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), Row Q Lk fun 𝒜 _ => R1.H_hTu (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) 𝒜 := by
  first | exact @_root_.GlobalTheory.Fc.row_hTu_cTmin_alt | exact _root_.GlobalTheory.Fc.row_hTu_cTmin_alt | (intros; apply _root_.GlobalTheory.Fc.row_hTu_cTmin_alt <;> assumption)
end
end

section



section
open Module NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.Cp
open _root_.Formalism _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Rows
section Col
variable {X : Formalism.L2.Col.Fields} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 X.K G Pl0 I0 Ty T m} {P1 : Subgroup G} {ψ1 : P1 →* X.Kˣ}
end Col
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
@[reducible] def SquareIntegrableColumns.toS {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.GlobalTheory.Cp.SquareIntegrableColumns T P) : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P where
  X := K.X
  e := K.e
  c := K.c.toS
  Sp := K.Sp
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1
@[reducible] def SquareIntegrableColumns.ofS {T : _root_.Formalism.L2.TiedDataSKAlt ex} {P : RowSideFamily ex} (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) : _root_.GlobalTheory.Cp.SquareIntegrableColumns T P where
  X := K.X
  e := K.e
  c := ColRec3.ofS K.c
  Sp := K.Sp
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1
theorem serv_t_iff_formalism_serv_t (𝒞 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒞) : _root_.GlobalTheory.Cp.SelectionServed 𝒞 sel ↔ _root_.Formalism.L2.G.ServT.SelectionServed 𝒞 sel :=
  ⟨fun h => ⟨h.twU, h.pdv⟩, fun h => ⟨h.twU, h.pdv⟩⟩
end GlobalTheory.Cp
end
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem ties_of_tiesB_alt : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b →
    GlobalTheory.FinalJoin2.FieldSmall D O.L → b.RealisedCondition → GlobalTheory.EX.DQ.TwAllAt D O.ex.nch O.ex.xd → b.CompatibilityConditions := by
  intro D O c b h hF hR htw
  obtain ⟨hc, hpb, -, hL, hD⟩ := GlobalTheory.T.pathCoreConditions_of_intrinsicConditions D O c b h hF
  obtain ⟨hT, hRay⟩ := h
  exact
    { real := hR, core := hc, pb := hpb, types := hT.types, series := hT.series, level := hL, data := hD,
      psiVal := hT.psiVal, ray := hT.small.ray, roots := hT.small.roots, rayQ := hRay, twist := htw }
end GlobalTheory.PlugPt
end
end

section



section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
def col0_alt (t : W.P.T) (φ : D.what₂.Mu u) : (f.t t).Col 0 := D.e0Tw u (W.P.I.tup t) (D.eMu u φ).1
def descentToLevelZero (n : ℕ) (h : 2 * n + 2 * 0 + 2 = D.R.m) (t : W.P.T) (F : (f.t t).CT) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h F)).1
def LinkVanishes (d : _root_.GlobalTheory.MiTop.BottomData W u) : Prop :=
  ∀ n (h₀ : 0 + 2 * n + 2 = D.R.m) t φ, _root_.GlobalTheory.MiTop.col0_alt f t φ ∈ (f.t t).Ram 0 ∧
    ∀ G y v, (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t φ) G y v = d.per φ G.1 y v
def LinkTailCondition : Prop :=
  ∀ n (h : 2 * n = D.R.m) t φ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
    (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' →
    (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t φ)) G =
      D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))
def LinkDescends : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m) t (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
    ∃ G : (f.t t).CT, G.1 = _root_.GlobalTheory.Fam.leadingLinearMap W t F' ∧ _root_.GlobalTheory.MiTop.descentToLevelZero f n h t G = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F'
def LinkSurjective : Prop :=
  ∀ n (h : 2 * n + 2 * 0 + 2 = D.R.m), ∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∃ G : (f.t W.P.A3.A.μ0).CT, _root_.GlobalTheory.MiTop.descentToLevelZero f n h W.P.A3.A.μ0 G = T
def LinkCommutes : Prop :=
  ∀ n (h : 2 * n = D.R.m), ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (s : ℂ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ s ≠ 0 ∧
    ∀ t φ F, (f.t t).tail (2 * n) h ((f.t t).up n (_root_.GlobalTheory.MiTop.col0_alt f t φ)) F =
      s * (f.t t).tail (2 * n) h ((f.t t).col (2 * n) (_root_.GlobalTheory.MiTop.col0_alt f t (S φ))) F
variable (W)
def CoveredCondition : Prop :=
  ∀ w (p : ℕ), p.Prime → (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q (W.Q.Rl.mu w), ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal
open Formalism.L2.Host in
theorem served' : _root_.GlobalTheory.MiTop.CoveredCondition W := by
  rintro w p hp ⟨PP, hP, h1⟩ h2
  have lev := W.Q.charW.base.lev
  have hr : ¬ (W.Q.Rl.xiH (W.Q.Rl.mu w)).UnrAt PP := (lev.Q_ram _ PP).2 (Or.inl hP)
  have hl : Formalism.EigenvalueLevelCeiling.plc w = p :=
    (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hp).1
      ((ringChar.spec _ p).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2))
  by_cases hw : w ∈ W.Q.Rl.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := W.Q.charW.tup.mu_on w hw
    have e' : W.Q.Rl.xiH (W.Q.Rl.mu w) = W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have key : ∀ q : ℕ, q.Prime → OverP D.host q PP → q = p := fun q hq ho => by
      by_contra hne
      have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hq hp).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have ho' : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := ho
      exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ ho') (PP.asIdeal.mul_mem_left _ h1)))
    have hd : (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP := by
      unfold CharFrame.delAt
      split_ifs with hh
      · refine W.Q.Rl.C.isDel'.unr PP fun ho => D.host.pde_ne ?_
        rw [← hh, hl, key _ D.host.pde'_prime ho]
      · exact W.Q.Rl.C.isDel.unr PP fun ho => hh (by rw [hl, key _ D.host.pde_prime ho])
    refine hr fun x hx => ?_
    have a1 := hd x hx
    have a2 := hψ.atl PP (hl ▸ h1) x
    rw [e']
    change (W.Q.Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
    rw [a1, a2, mul_one]
  · have e : W.Q.Rl.mu w = W.P.A3.A.μ0 := W.Q.charW.tup.mu_off w hw
    refine hr fun x _ => ?_
    rw [e, show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
    rfl
theorem not_mem_Q_base' (PP : HeightOneSpectrum (𝓞 D.host.E)) : PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 := by
  intro hP
  have lev := W.Q.charW.base.lev
  refine (lev.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [show W.Q.Rl.xiH W.P.A3.A.μ0 = 1 from lev.xi_base]
  rfl
end GlobalTheory.MiTop
end
end
end

section



section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.MiS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdForm
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}
def TwStdAlt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∃ (l0 : I.Law0 l) (t : SymmetricTwistedColumnsAtPrimes W.R.T.n.tp W.R.T.cols (I.tw l l0 Z)),
    ex.tw = I.tw l l0 Z ∧ HEq W.R.T.tw t ∧ I.StdTw l Z l0 t
def FamilyColumnCondition {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : (I.rec7 l Z).what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) : Prop :=
  ∃ c₀, PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ f.g.x f.g.vac c₀ ∧ ∀ t : W.P.T,
    (∃ (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) (ι : ∀ j, (f.col t).Ch j → Ch₀ j) (w : _),
      PinChL (_root_.GlobalTheory.Fam.pk_z W) f.g (f.col t) c₀ A ι w) ∧
    ∃ UT ε, PinTopL (_root_.GlobalTheory.Fam.pk_z W) f.g (_root_.GlobalTheory.Fam.complexLevelStructure W) (t := t) (f.col t) UT ε
end GlobalTheory.AdForm
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {a : XGeo D}
structure SymReadAlt (l : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP.1) (S : ∀ PP, SymData (l PP).k (l PP).s D.R.k) : Prop where
  char : ∀ PP, (ofSplit (l PP).q).IsChar (_root_.GlobalTheory.Fam.pk_z W).ψ (S PP).ψ
  mu : ∀ PP j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1⁻¹ ((S PP).μ j)
  grp : ∀ g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1), g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H ↔ ∀ PP, ∃ x, (l PP).Red (S PP) x (g PP)
  chr : ∀ (g : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP PP.1)) (hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H) (x : ∀ PP, (S PP).P.J),
    (∀ PP, (l PP).Red (S PP) (x PP) (g PP)) → (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = ∏ PP, (S PP).P.lam (x PP)
end GlobalTheory.Fam
end
end
end

section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
noncomputable section
namespace GlobalTheory.DefHalf
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem keeps_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (g : p.P.Gp) :
    ∀ f ∈ CF p i, actLev p.T.Q.c (p.O i).lev2 g f ∈ CF p i := fun f hf => by
  obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1
  obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g
  exact (hO.1 g k hk f hf).1
def groupActionOnCoefficients (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (g : p.P.Gp) : CF p i →ₗ[p.T.Q.c.F] CF p i :=
  (actLev p.T.Q.c (p.O i).lev2 g).restrict (_root_.GlobalTheory.DefHalf.keeps_alt p i hp g)
end GlobalTheory.DefHalf
end
end
end
