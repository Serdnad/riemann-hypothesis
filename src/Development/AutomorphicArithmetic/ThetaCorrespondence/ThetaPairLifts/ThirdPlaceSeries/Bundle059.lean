module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle056
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle002
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle016
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle054
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle446
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactRanksAlongTiedFamily
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
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

@[expose] public section

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem finrank_WL_eq_dW (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) = (P.A3.indefDown P.S0).dW i :=
  congrFun (dW_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0) i
def indefiniteDownJoin (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (y : Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) :
    Fin (Q.Rl.nW i) → D.what₂.LL :=
  Formalism.IndefR.NX.jDL Q.Rl Q.F.lv2 i (y ∘ Fin.cast (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRealisationRecursion (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Type 1 where
  tupT : D.what₂.Tup → P.T
  hm : 0 < D.R.m
  hTop : Formalism.IndefR.RecTie.TopMultH Q.Rl.toRealDat
  hinj : ∀ i t, Function.Injective (Q.Rl.toRealDat.extV i t)
  Ish : Formalism.IndefR.RecTie.RowIds (Formalism.BasicNotions.RowSide.sharp D) (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) true
  I0 : Formalism.IndefR.RecTie.RowIds ex.p0.s (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) false
  IL : Formalism.IndefR.RecTie.LiftIds (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj)
  Kc : Formalism.IndefR.RecTie.ColReal D
  E : EigIdx D Y
  labPi : E.Pi → P.A3.A.fam.base.Ix
  PY : Formalism.IndefR.principalLevelFrame.RowPsi (Yc D 0) D.R.r
  PW : ∀ i, Formalism.IndefR.principalLevelFrame.RowPsi (Wc D i) D.R.r
  eFT : D.what₂.FT ≃ Formalism.IndefR.principalLevelFrame.FTR Q.Rl.θ PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b))) (fun _ => Q.Rl.e0)
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  ιW : ∀ i, ↥(Formalism.L2.Theta.GfC (Yc D 0)) →* ↥(Formalism.L2.Theta.GfC (Wc D i))
  Tp : Formalism.L2.Host.TupTied D Q.Rl.C ex.nch
  recR : Formalism.IndefR.RecTie.RecReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj ex.p0 Ish I0 IL Kc E labPi PY PW eFT piOf ιW ex.nch Tp
  tpEq : HEq Tp Rc.T.n.tp
  tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ
  tupT_tup : ∀ t, tupT (P.I.tup t) = t
  muEq : Q.Rl.mu = P.S0.μ
  mtRead : Formalism.IndefR.RecTie.MtRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (twPOf P tupT tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (fun i => (P.A3.indefDown P.S0).dW i)
    (fun i y => P.I.jW i y) (_root_.Formalism.IndefR.indefiniteDownJoin Q)
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupT_inj_used {μ μ' : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (hμ' : Formalism.IndefR.RecTie.Used0 D μ')
    (h : Qr.tupT μ = Qr.tupT μ') : μ = μ' := by
  apply Qr.Tp.xi_inj
  rw [← Qr.recR.tupXi μ hμ, ← Qr.recR.tupXi μ' hμ', h]
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupleRead_baseTuple_eq_family : Qr.tupT D.what₂.mu0 = P.A3.A.μ0 :=
  Q.charW.base.lev.xi_inj (by rw [Qr.recR.tupXi D.what₂.mu0 (Or.inl rfl), Qr.Tp.trueColumnChoices_heckeChar_reference_eq_one, Q.charW.base.lev.xi_base])
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tw_iff (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) (w : D.what₂.places.Pl) : D.plEq w ∈ Q.Rl.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
  have h0 := Qr.tupleRead_baseTuple_eq_family
  constructor
  · intro hw he
    apply Q.charW.tup.mu_ne (D.plEq w) hw
    rw [← Qr.recR.tupAt w, he, h0]
  · intro hne
    by_contra hw
    apply hne
    apply Qr.tupT_inj_used (Or.inr ⟨w, rfl⟩) (Or.inl rfl)
    rw [Qr.recR.tupAt w, Q.charW.tup.mu_off (D.plEq w) hw, h0]
end RealRec
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
def _root_.Formalism.IndefR.IndefiniteRealisationRecursion.PartsRow (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) : Prop :=
  Formalism.IndefR.RecTie.PartsRec Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.PY Qr.PW Qr.eFT Qr.E Qr.labPi Qr.piOf Qr.Ish.prt Qr.IL.prtW
end RealRec
end Formalism.IndefR
end
end
end

section



section
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef
namespace Formalism.L2.SG.JoinSI
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Twist
variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)
end Twist
section SpOf
end SpOf
section At
variable {D : D7}
variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}
end At
section Ties
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
def spectralRowIsometry (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G :=
  Classical.choose (S.rowTie hF)
theorem eHH_sEE_eq_conjHH_isometryOfJoin (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) (F : D.what₂.EE) :
    (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF F) :=
  Classical.choose_spec (S.rowTie hF) F
theorem isometryOfJoin_eq_of_conj_compat (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G)
    (hj : ∀ F, (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (j F)) : _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF = j := by
  ext1 F
  apply (conjHH S.X S.G).injective
  rw [← _root_.Formalism.L2.SG.JoinSI.eHH_sEE_eq_conjHH_isometryOfJoin S hF F, hj F]
theorem colJoinS_of_spectral_ties_real (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : FinX S.Y) : ColJoinS hF (S.hI hF) S.tr :=
  colJoinS_of_pin hF (S.hI hF) S.tr S.into S.bij fun u x =>
    (LinearEquiv.eq_symm_apply (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u))).2 (S.colPin hF u x)
end Ties
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
abbrev complexRealisationJoinData {R : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) :=
  Q.Rl.toCx3 Q.F
structure IndefiniteRealisationJoin (R : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) where
  m : D.what₂.Word → (Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Dc.Mem
  mPin : HEq m P.I.wU
  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Dc.a (m u)) → ℂ)
  cF : (Fin ((Q.F.fc (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs).Df1.nV P.A3.fam3.base3.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0
  eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj (twQ P)] (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).EE
  chainTie : ChainTieT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (σ := D.what₂.embLL) (m := m) (cφ := cφ) (cF := cF)
  v0Surjective : GoodPartHasComplexCoordinates (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (cF := cF)
  rowTie : RowTieT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (eV := Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) (s := twQ P) (σ := D.what₂.embLL) (cF := cF) (eR := eR)
  colNorm : ColNormT (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (s := twQ P) (m := m) (cφ := cφ)
  pairTie : ∀ hF : FinX S.Y, PairTieT (X := S.X) (G := S.G) (j := _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF) (Tr := S.tr) (hK := S.Y.hK) (Dt := S.Y.Dt)
    (P := _root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) (fc := Q.F.fc) (sEE := Q.sEE) (s := twQ P) (m := m) (cφ := cφ) (eR := eR)
variable {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks}
theorem embedding_eq_cj_twQ_embLL (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (a : D.what₂.LL) :
    P.A3.fam3.base3.v0.embedding a = Formalism.IndefR.Links.cj (twQ P) (D.what₂.embLL a) :=
  twist_of_mk D.what₂.embLL P.A3.A.v0 Q.Rl.hv0 a
def IndefiniteRealisationJoin.toJoinAt (J : _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) :
    JoinAt S.X S.G S.Y (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S) S.tr (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q) Q.F.fc (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE (twQ P) D.what₂.embLL where
  m := J.m
  cφ := J.cφ
  cF := J.cF
  eR := J.eR
  twist := _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL Q
  chainTie := J.chainTie
  v0Surjective := J.v0Surjective
  rowTie := J.rowTie
  colNorm := J.colNorm
  pairTie := J.pairTie
end Real
end Formalism.L2.SG.JoinSI
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem ranks_and_frame_of_tied_class_alt : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro hU 𝒞 sel
  have hR : Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hc =>
      _root_.GlobalTheory.exact_ranks_along_tied_family_alt hU _ Fm (sel Fm hc) _ _ _ _ _ _
  exact ⟨hR, GlobalTheory.tFrame_of_ranksRow_three 𝒞 hR⟩
end GlobalTheory
end
end

end

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.ranksF_tFrame_closed_of_mass_ratio : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧ Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  first | exact @_root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | exact _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt | (intros; apply _root_.GlobalTheory.ranks_and_frame_of_tied_class_alt <;> assumption)
end

end
end
