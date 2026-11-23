module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumOfPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle536
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle545
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle547
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Formalism.LocalToGlobal.Columns.Bundle015
import Formalism.LocalToGlobal.Columns.RowFormsAdelic
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle616
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move

attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.SideCopy

structure CopyAll (D D' : D7) (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : CopyTw D D' ι e
  jL : HEq D.ntw.jL D'.ntw.jL
  s2 : HEq D.ntw.s2 D'.ntw.s2
  lamG : HEq D.ntw.lamG D'.ntw.lamG
  Xv : HEq D.ntw.Xv D'.ntw.Xv
  qs : HEq D.ntw.qs D'.ntw.qs
  pl : HEq D.naut.plGw D'.naut.plGw

structure SameFrame {D D' : D7} (cf : CharFrame D) (cf' : CharFrame D') : Prop where
  mu0 : HEq cf.mu0 cf'.mu0
  eta : HEq cf.eta cf'.eta
  del : HEq cf.del cf'.del
  del' : HEq cf.del' cf'.del'

structure RingPart (D : D7) (cf : CharFrame D) (low : Finset ℕ) where
  twF : TwFrameC D
  tw : TwistFrameLowIndexCompatibility D twF low
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
  deltaRead : DeltaRead D cf

def RingPart.of {D : D7} {cf : CharFrame D} {Rw low Pq S hL eig θ} (B : SideB D cf Rw low Pq S hL eig θ) : RingPart D cf low :=
  ⟨B.twF, B.tw, B.chiD, B.chi, B.eta_eq, B.ringSpec_normalisedCharacter_eq, B.del_eq, B.iCq_embO, B.embO_star, B.deltaRead⟩

def PsiStd (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ u : Formalism.IndefR.NX.U D.nd, embLL0 D ((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (Complex.exp (2 * Real.pi * Complex.I / (D.host.g kv.1 : ℂ)) ^ (NX.xiRed D kv * NX.supSum D.R.r
      (((u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val)⁻¹

def PsiLaw (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ i b (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      readLL0 S i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)

def SameUnits {D D' : D7} (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ)
    (c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (b : Bool) (P : PlE D.host) (P' : PlE D'.host), HEq i i' → HEq P P' → HEq (c' i' b P') (c i b P)

def RowEig (D : D7) (S : RatDat D.ntw) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) : Prop :=
  ∀ i (s : D.ntw.Sig i) k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
    algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i (D.ntw.side i s) P) ^ k *
        (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) (eig (D.ntw.jS i s) (rowS i s) k P))




set_option maxRecDepth 100000 in
theorem sigSpan_copy {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyAll D D' ι e)
    (hs : D.ntw.SigSpan) : D'.ntw.SigSpan := by
  have transfer {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
      {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
      (g : GlobalTheory.TwistChoice.SameGalois N N')
      (t : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X')
      (b : HEq X.B X'.B) (ab : HEq X.acgB X'.acgB)
      (mb : HEq X.modB X'.modB) (hk : HEq X.hk X'.hk)
      (s : X.SigSpan) : X'.SigSpan := by
    obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := g
    obtain ⟨xcc, xTw, xl, xO0, xcrO0, xalgO0, xtopO0, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, xS0, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := t
    cases D; cases D'
    dsimp only at a1 a2 a3
    subst a1; subst a2; subst a3
    cases N; cases N'
    dsimp only at nOm ninstOm nalgOm nplOm nPlG
    subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
    cases X; cases X'
    dsimp only at xcc xTw xl xO0 xcrO0 xalgO0 xtopO0 xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xS0 xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth b ab mb hk
    subst xcc; subst xTw; subst xl; subst xO0; subst xcrO0; subst xalgO0; subst xtopO0; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xS0; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
    subst b; subst ab; subst mb; subst hk
    exact s
  exact transfer h.cp.gal h.cp.set h.cp.B h.cp.acgB h.cp.modB h.cp.hk hs

end GlobalTheory.HeightCounting.SideCopy

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}




theorem classSumPin_of_read (p : PtAt ex Csz) (Yr : R3.Read (A3 := p.P.A3) p.R.toRealDat p.F.lv2 ex.p0)
    (hjW : ∀ (i : Fin D.R.m) (v : Fin ((p.P.A3.indefDown p.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL), HEq v y →
      Yr.mj.eW i (p.P.I.jW i v) = (p.R.FW i).j (sg0 D p.P.A3.A) (jDL p.R p.F.lv2 i y))
    (hth : GlobalTheory.HeightCounting.EMtTheta Yr p.nexp ex.nch)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    GlobalTheory.ExportPin.ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  subst hx
  apply hth w i hw _ hxT n a f
  rw [hsum, GlobalTheory.ExportPin.Model.theta_cast _ _ _ ht, hD.thTheta, hjW i _ y hy]

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

section Pack

variable {D : D7} {O : Obj D}




end Pack

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX




theorem eMtTheta_of_pack {D : D7} {nch : NChoice D} {X0 : BaseLevelRowSide D} {G G' : Type} {g : Group G} {g' : Group G'} {fi : Fintype G}
    {fi' : Fintype G'} {Pl0 I0 T Pl0' I0' T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {A3' : FamIn3 D.what₂.LL G' Pl0' I0' (List ℕ) T' D.R.m}
    {C C' : CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {al' : Algebra C'.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F}
    {R' : RealDat3 D A3' C'.Q.c.F} {F : Face3 D A3} {F' : Face3 D A3'} {kap : ℝ} {lam : type_of% R'.lam3} {err : type_of% R'.err0}
    {Dc : ∀ Zs : DefSub A3'.fam3.amb3, DefCols (A3'.side3 F'.P1 F'.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
    {Zsc : DefSub A3'.fam3.amb3 → IndefScale A3'.fam3.base3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cG' : G0 R'.Pg D.R.r ≃* G0g D.nd}
    {cG'' : G0 ((R'.updS kap lam).withErr err).Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨G, g, fi, Pl0, I0, T, A3, C, al, R, F, cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨G', g', fi', Pl0', I0', T', A3', C', al', (R'.updS kap lam).withErr err, R3.reFace F' Dc Sp Zsc, cG''⟩)
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Y' : R3.Read (A3 := A3') R'.toRealDat F'.lv2 X0)
    (hW : HEq Y.mj.eW Y'.mj.eW) {S S' : RatDat D.ntw} (hS : S = S')
    (E : NExpRealS R cG S) (E' : NExpRealS R' cG' S') (hF : HEq E.eF E'.eF) (hi : HEq E.fi E'.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta Y' E' nch) : GlobalTheory.HeightCounting.EMtTheta Y E nch := by
  cases pack
  cases hS
  intro w i hw x hx n a f hs
  have e1 : E.eF = E'.eF := eq_of_heq hF
  have e2 : E.fi = E'.fi := eq_of_heq hi
  have e3 : Y.mj.eW = Y'.mj.eW := eq_of_heq hW
  rw [e2, e3] at hs
  rw [e1]
  exact h w i hw x hx n a f hs


end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink


end GlobalTheory.ClassSumPinLink
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2


noncomputable section

namespace GlobalTheory.Mem.R3.RowAd.Inert

theorem conj_heckeFamI_apply {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (hS : (Formalism.L2.Col.formGSD C Λ).Ok) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Formalism.L2.Col.LevOffI ST SG S0 × List ℕ)
    (f : ((Formalism.L2.Col.formGSD C Λ).toCSD hS).Forms) (d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    ((((Formalism.L2.Col.formGSD C Λ).res hS).symm ((((Formalism.L2.Col.formGSD C Λ).res hS).conj
      (Formalism.L2.Col.heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y)) f) : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) d =
      ∑ e ∈ d.inertNb y.1.1.asIdeal y.2, ((((Formalism.L2.Col.formGSD C Λ).res hS).symm f : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) e := by
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Formalism.L2.Col.heckeFamI_formPts_apply]
  rfl

theorem colIn3_heckeRI_apply {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R)
    (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
    (τ : TupF TU) (q : ↑((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).okI τ) × List ℕ)
    (f : ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.MtildeCSD τ).Forms) (d : (Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).D) :
    (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeRI τ q f)).1 d =
      ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb q.1.1.1.asIdeal q.2 d,
        (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm f).1 e :=
  conj_heckeFamI_apply _ _ (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX) S0 (offSubI.lev q.1, q.2) f d

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ)
    (hP : ReadsDeco X I hX Xg tr cX t P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf X.toD7.sp.X'))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ R, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb (q.1.1 : PlI X.B px).1.asIdeal q.2 (decoAd X I t g : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e)
    (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeRI t q f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
        ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
  obtain ⟨m, hm⟩ := hP
  funext g
  have e1 := hm ((famR X I hX U Xg tr).heckeRI t q f) g
  have e2 := colIn3_heckeRI_apply (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I U)
    Xg ∅ (xiValOf I) tr t q f (decoAd X I t g)
  have e3 := hN _ (fun e => m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 e)) g
  refine e1.trans ?_
  refine (congrArg m e2).trans ?_
  refine (map_sum m _ _).trans ?_
  refine e3.symm.trans ?_
  exact (Finset.sum_congr rfl (fun a _ => hm f (g * a))).symm

theorem chi_eq_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Q : Pl D.host.E)
    (hQc : Formalism.L2.Col.conjPrime₂ Q = Q) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q) (j : (levEnv V β L).J)
    (hj : IsLocElt V Q (j : Bridge.Gf V)) : (levEnv V β L).χ j = 1 := by
  have e : (levEnv V β L).χ j = Formalism.L2.DIV.levFn β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) := rfl
  have hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := LiftInertChi.locAt_of_isLocElt V _ _ hj
  have hconj : Formalism.DivisionValues.conjPl Q = Q := GlobalTheory.InertNbr.conjPl_eq_of_conjP hQc
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q →
      Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := fun PP hPP =>
    LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (fun hu => by
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
      · exact hoff PP hPP h
      · exact hoff PP hPP (h.trans hconj))
  have hr1 : Formalism.L2.DIV.rTup β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (Or.inl PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (Or.inr hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (Or.inl hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem gram_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem off_level (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px) :
    ∀ PP, PP ∈ (L.datXt t).Pg ∨ PP ∈ (L.datXt t).Q → PP ≠ Q.1 := by
  rintro PP (h | h) rfl
  · have h' : Q.1 ∈ L.Pg := h
    rw [hL.Pg] at h'
    exact Q.2.2.2 (Or.inr h')
  · refine (hL.is.Q_pl t _ h).2 _ h ?_
    exact GlobalTheory.InertNbr.isConjPl_self (D := X.toD7) Q.2.1

theorem inert_neighbours (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hI : I.Ok) (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px)
    (hQ : Q.1 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (s : List ℕ) (hs : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank s) :
    ∃ (x : Bridge.Gf X.toD7.sp.X') (A : Finset (Bridge.Gf X.toD7.sp.X')), IsLabElt X.toD7.sp.X' Q.1 (labIn X.toD7.sp.X'.rank s) x ∧
      (∀ a ∈ A, IsLocElt X.toD7.sp.X' Q.1 a) ∧ Bridge.IsDC (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J x A ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ A, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb Q.1.asIdeal s (decoAd X I t g : Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e := by
  obtain ⟨m, hm⟩ := hL.is.βX
  rw [one_pow] at hm
  have hβ := hL.beta.2
  rw [hβ] at hm
  have key := GlobalTheory.InertNbr.exists_hecke X.toD7.sp.X' (n := X.B.R.N X.B.R.m - 1) (rank_X' X).symm L.ΛX (L.datXt t) hm Q.1 Q.2.1
    (off_level X I hL t Q) hQ 1 1 (one_mem _)
    (fun x => by
      rw [gram_eq_one X I hI, one_mul, inv_one, mul_one]
      exact (LiftBrg.castGL_mem_UA_one X.toD7.sp.cm (rank_X' X).symm x).symm)
    (one_mem _) (one_mem _) s hs
  simp only [inv_one, one_mul, mul_one] at key
  rw [hβ]
  exact key

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI _ hL _ cX gramR c0R _ _ _ _ t P hP
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2) =>
    inert_neighbours X I hI hL t (q.1.1 : PlI X.B px) (fun h => q.1.2 (Or.inr h)) q.2 hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => chi_eq_one X.toD7.sp.X' L.βX (L.datXt t) (q.1.1 : PlI X.B px).1 (q.1.1 : PlI X.B px).2.1
      (off_level X I hL t (q.1.1 : PlI X.B px)) j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr t cX P hP q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.RowAd.Inert
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.liftHermitianLattices_replacedStages_eq :
    ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T)
      (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
      (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W)
      (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
      (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _)
        (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)),
      r'.z = GlobalTheory.Mem.R3.Rw.Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z →
        HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)),
          MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) :=
  @GlobalTheory.Mem.R3.Rw.Up.mjAre_back
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelChar_eq_one_inert_prime_off_level : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (j : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J),
    IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (j : Bridge.Gf (Vc X.toD7 i)) → (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | exact GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | (intros; apply GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.Level

variable {D : D7}

theorem isLift_one_V {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) 1 1 := by
  have h : (1 : GA D (Vc D i)) ∈ Lev.levG (Vc D i) (L.βV i) (L.datVt i t) := one_mem _
  exact ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩

theorem levChi_flag_one {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β (Lev.flagL L) 1 = 1 := by
  unfold Lev.levChi
  rw [(Lev.finE V).map_one]
  exact congrArg Units.val (Formalism.L2.DIV.levChar D.sp.cm V.gram β (Lev.flagL L)).map_one

theorem om_level_vP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → (∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) → ∀ i t, ∀ k ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv), R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω hv _ i t k hk
  have h := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hL (hv i t).1.2.inf hω hv i t 1 1 k (isLift_one_V R.toLevCh i t)
    ⟨hk.1, hk.2.1, Subgroup.mem_bot.1 hk.2.2⟩
  rw [h, levChi_flag_one, inv_one, one_smul]

end GlobalTheory.DefLift.Level
end
