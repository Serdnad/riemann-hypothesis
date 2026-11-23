module

public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.ColFacts
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle056
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle052
public import Formalism.LocalToGlobal.Divisibility.TupUsed
public import Formalism.LocalToGlobal.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.IsFDiagIffDiagonal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Formalism.LocalToGlobal.GroupLattices.Bundle001
public import Formalism.LocalToGlobal.PtKOfReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Formalism.SharpRestriction.GlobalSchurBounds.PlugDgt
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Rows
namespace GlobalTheory.ExportPin
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def IndefiniteClassSumCondition (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop :=
  ∀ (w : D.what₂.places.Pl) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m) (t : P.T)
    (ht : P.I.tup t = D.what₂.muTw w), D.what₂.muAt w ≠ D.what₂.mu0 →
    ∀ (c : Fin (lDim D P.A3.A P.P0 P.ψ0 i t) → D.what₂.LL) (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)),
      x = ht ▸ P.I.eMt i t c → x ∈ Idx.TjV D (D.what₂.muTw w) ((i : ℕ) + 1) →
    ∀ (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL),
      HEq (((P.A3.indefDown P.S0).θ i t).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec c)) y →
    ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx ((i : ℕ) + 1)),
      (Q.nexp.fi i).e (∑ k, a k • (show ↥(Q.Sx.A ((i : ℕ) + 1)).WK from f k).1) = jDL Q.Rl Q.F.lv2 i y →
      NChoice.thPe D ex.nch w ((i : ℕ) + 1) (ex.nch.eMt w ((i : ℕ) + 1) x) =
        ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          (Q.nexp.eF (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w) h1 h2).symm
            ((1 : KB Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[Q.Sx.Ks] f k)
end GlobalTheory.ExportPin
end
end
end

section



section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.RowDataTransport
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
abbrev packageOfPrimitiveLinks [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P Dcf Spf Zscf) Cl CHl) :=
  primitivePackageFullHecke hOk hsep Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl Q.charW hP hI
def InpAtAlt [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1) : Prop :=
  ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.col NuC I →
      HEq I P.I →
      ∃ inp : ∀ u, DivInputs0R (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core
          (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
          (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u),
        ∃ hQ : ∀ u, ChainTie (inp u).ch (c.memQ (I.wU u)), ∀ u, FirstCols c.hE (hQ u)
theorem ptK_of_real_alt [_root_.NumberField.IsTotallyComplex D.what₂.LL] (Rc : _root_.Formalism.L2.RecTAlt ex) (R : _root_.Formalism.L2.DIV.DivisionKernelData ex) (hT : R.T = Rc.T)
    (hpin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Rc.T R.P) (hkap : RowsHoldKap3 R.P) (hPt : RowsHoldDcPt3 R.P)
    (hR : DivRows3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.P.Zs R.P.S0 R.P.S1 ex.p0 R.P.C R.P.NuC R.P.I) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc R.P R.c.face R.Sp R.Zsc S Ks) (hsep : R.P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Q.sEE (hkCan R.P.A3) Cl CHl)
    (hI : PassIn3 Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Cl CHl)
    (C Cabs : ℝ) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : R.P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hInp : _root_.Formalism.L2.RowDataTransport.InpAtAlt R.c Q R.ok1 hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H)
    (hN : NprimeDef D L) (hh : ∀ u, D.div.h u = hExpl6 D L Y Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs).Z.num Cl CHl) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (_root_.Formalism.L2.DIV.DivisionPackageKernel' R C Cabs) := by
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs = R.P.Zs := Q.zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefData R.P.S0 := Q.s0
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.cols.toIndefData R.P.S1 := Q.s1
  have hRows : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefRows (Classical.choose R.hr.rows0) :=
    rows_heq hZs _ _ (hS0.trans (heq_of_eq (Classical.choose_spec R.hr.rows0).symm))
  have hDc : HEq (R.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs) R.P.Dc :=
    (congr_arg_heq R.c.face hZs).trans (heq_of_eq R.colTie.1)
  exact _root_.Formalism.L2.DIV.pkg_of_rowsK_alt R hR C Cabs Cl CHl _ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI) hZs hRows hS1 Q.col
    Del h0 lam0 C0 ce Ch Sw C1 eJ H
    (fun NuC I hT' hI' => ⟨Formalism.L2.G.ServJointF.brTied_of hT' ⟨1, R.ok1.ok2⟩ (dcPt_move hPt hZs hDc hS0 hS1 hI'),
      hInp NuC I hT' hI'⟩)
    hN Y (fun σ => (hkap σ).trans (congrFun (kap_heq hZs hS1) _).symm) (fun u => ⟨rfl, HEq.rfl, rfl, hDel, hh0⟩) hh hF
    hC0 hC1 hC2 hCabs hLa
end Formalism.L2.RowDataTransport
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR.LevelRealisationRankEquality
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefinite_realisation_base_rank_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) :
    D.what₂.D0 = (P.A3.A.fam.R P.A3.A.fam.μ0).dZ (P.A3.A.fam.lvl P.P0 P.ψ0) (P.Zs.Z P.A3.A.fam.μ0) := by
  have hD := D_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
  have hz : (P.A3.side3 P.P0 P.ψ0 (Q.Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).dQ P.A3.fam3.base3.μ0 =
      (P.A3.side3 P.P0 P.ψ0 P.Zs).dQ P.A3.fam3.base3.μ0 := by rw [Q.zs]
  rw [base_rank_eq_of_tied_level P, ← hD]
  exact hz
theorem indefinite_realisation_mu_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Q.Rl.mu = P.S0.μ :=
  mu_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
theorem tup_all_used_of_realisation (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : TupAllUsed P := by
  apply tupAllUsed_of_cover
  intro t
  rcases Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨D.plEq.symm w, ?_⟩
    show t = P.S0.μ (D.plEq (D.plEq.symm w))
    rw [← _root_.Formalism.IndefR.LevelRealisationRankEquality.indefinite_realisation_mu_eq Q, Equiv.apply_symm_apply]
    exact h.symm
end Formalism.IndefR.LevelRealisationRankEquality
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
open Classical in
structure IndefiniteRealisationNormalisation {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  cfEq : Q.Rl.C = Rc.T.n.cf
  qGuard : Formalism.IndefR.FWT.QGuard Q.Rl.toRealDat
  hF : D.host.F = maximalRealSubfield D.host.E
  phsOne : ∀ i, Q.Rl.phs i = 1
  prXunit : Formalism.IndefR.Seed.PrIso Q.Rl.MX Q.Rl.cX Q.Rl.prX
  grpRecPin : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Q.Rl.toRealDat.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : Q.Rl.toRealDat.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf P.A3.A.X).coeff g) = D.ntypes.e0.coeff ((Q.Rl.eG.trans Q.cG) g)) ∧
    (∀ kv, Q.Rl.toRealDat.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, Q.Rl.toRealDat.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((Q.Rl.eG.trans Q.cG) g kv)
  fdiag : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)
  pgEq : Q.Rl.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE)
  tSfin : Q.tS ∈ Formalism.L2.Theta.GfC (Yc D 0)
  tSpin : (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel Q.tS⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq Q.tS
  eGtie : P.I.eG = Q.Rl.eG.trans Q.cG
  betaStd : (∀ i, Q.Rl.βV i = 1) ∧ Q.Rl.βX = 1
  bR_read : ∀ x i, Q.bR x i = D.eMu (Q.wdD x) (D.jN (Q.wdD x) (P.I.eNu (Q.wdD x)
    (Pi.single (Fin.cast (congrArg P.Dc.a (Q.wU_wdD x)).symm i) 1)))
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def IndefiniteRealisationExtends (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop :=
  (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) ∧
    ∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Q.Rl.MY 0) Q.Rl.ν0 Q.Rl.fd0 (Q.Rl.toRealDat.EEat (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G Q.ιS Q.tS c'
end Formalism.IndefR
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
namespace RealT
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks)
theorem _root_.Formalism.IndefR.IndefiniteRealisation.rows_transport {Z Z' : DefSub P.A3.fam3.amb3} (h : Z = Z') (R0 : IndefRows (P.A3.side3 P.P0 P.ψ0 Z))
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Z')) (hS : HEq R0.toIndefData S) :
    ∃ R0' : IndefRows (P.A3.side3 P.P0 P.ψ0 Z'), R0'.toIndefData = S := by
  subst h
  exact ⟨R0, eq_of_heq hS⟩
theorem _root_.Formalism.IndefR.IndefiniteRealisation.rowsHold0 {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (hP : PrimRows3 R.Rl R.F) :
    RowsHold0_3 P := by
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep R.charW hP
  refine ⟨R.zs ▸ hR.stable, R.zs ▸ hR.inBlock, ?_, ⟨s, hOk⟩, hsep⟩
  exact _root_.Formalism.IndefR.IndefiniteRealisation.rows_transport R.zs (primRows3 hOk hsep R.Rl R.F R.charW hP) P.S0 (by
    rw [primRows3_data]
    exact R.s0)
end RealT
end Formalism.IndefR
end
end
end

section



section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.DIV.RatFullPt
section CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
  (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
end CSD
section Forms
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Forms
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefinite_realisation_column_facts (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3)
    (hP : PrimRows3 Q.Rl Q.F) (hS : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE)
    (hM : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE) : ColFacts P.S1 P.C := by
  have hC := complex_data_conditions_base_level_of_primitive_links hOk hsep Q.charW hP
  have hcols := (Q.Rl.toCx3 Q.F).exists_zeta_pairing_factors_through_periods Q.F.cr Q.F.cv (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE (hC.wf true) hC.h4pos (hC.what₂ true).1
    (hC.ratMu true) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1 (hC.levs true).2.2 (definite_coordinates_in_good_part _ true)
    (EvTie.evTie_of_ok hOk Q.F _) hS hM
  have hDc : HEq (Dcf (Q.Rl.toCx3 Q.F).zs) P.Dc :=
    (congr_arg_heq Dcf Q.zs).trans (heq_of_eq Q.dc)
  have hSp : HEq (Spf (Q.Rl.toCx3 Q.F).zs) P.Sp := (congr_arg_heq Spf Q.zs).trans Q.sp
  exact colFacts_transport Q.zs hDc hSp Q.s1 Q.col
    ⟨hC.wf true, hC.h0, fun t => (Q.Rl.toCx3 Q.F).rowMat_bij Q.F.cr true (hC.what₂ true).1 (hC.ratMu true) t,
      (Classical.epsilon_spec hcols).1⟩
end Formalism.L2.DIV.RatFullPt
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem passIn3_at_realT_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (c : ℝ) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf (fun Zs => let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs; { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }) S Ks), IsTotallyComplex D.what₂.LL → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → P.A3.fam3.Ok3 1 → PrimRows3 Q.Rl Q.F → ∀ C CH : ℝ, PassIn3 Q.Rl Q.F C CH := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Del h0 c S Ks _ _ _ Q hTC hadm hOk hP C CH
  haveI : IsTotallyComplex D.what₂.LL := hTC
  exact GlobalTheory.passIn3_of_rows D P.Gp P.Pl0 P.I0 P.T P.A3 Ks Q.Rl Q.F C CH Q.charW hOk hP
    (fun k => ⟨_, Rc.T.n.types.O k, Rc.T.n.types.eSer_def k⟩) hadm rfl rfl
end GlobalTheory
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.closed_family_admissible_twist_link_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (aPt0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u)
    (aPtTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw)
    (aPer0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i))
    (aPerTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw)
    (aP10 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u)
    (aAtG : Closed (D3 3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1)
    (hServ : _root_.Formalism.L2.G.ServT.SelectionServed (D3 3 𝒜) fun Fm hc => sel Fm (d3_a hc)), Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i) := by
  intro 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hDG : Closed (D3 3 𝒜) fun Fm _ => DGamSize Fm := Closed.of_class fun _ _ hc => hc.2.2.2
  have hA2 : Formalism.L2.G.Adm2InU.Adm2InU (D3 3 𝒜) :=
    { pt0 := aPt0, ptTw := aPtTw, per0 := aPer0, perTw := aPerTw,
      serv := _root_.Formalism.L2.G.ServT.closed_servF_of_servT_of_dGamSize (fun Fm hc => sel Fm (d3_a hc)) hDG hServ,
      p10 := aP10, dgt := Formalism.MainNotions.closed_eventually_levelPrimeCoprimeStabiliser (WithChN 𝒜) 3, atG := aAtG }
  exact (Formalism.L2.G.Adm2InU.admissible_family_of_inclusion hA2).imp fun _ _ _ a => a.1
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure RealTBAlt (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) : Type 1 where
  T : CoreJ D
  [alg : Algebra T.Q.c.F D.what₂.LL]
  Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S T.Q.c.F
  κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)
  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Q.Rl.toRealDat.MW i σ).Vec
  fw : FWTie T Q.Rl.toRealDat κ v₀
  bar : BarTie fw
  O : ∀ i, OMDat T.toCore Q.Rl.toRealDat i Unit (fun _ => P.A3.A.μ0)
  pins : ∀ i, OMPins T Q.Rl.toRealDat κ v₀ O i
  rhoGeo : RhoGeo fw O
  equivAll : EquivAll T Q.Rl.toRealDat κ O
  cTie : ∀ i, CTie T Q.Rl.toRealDat κ v₀ O i
  phase : ∀ i, Q.Rl.toRealDat.LUnif → PhaseTie T Q.Rl.toRealDat κ v₀ O (phEff Q.Rl) i
attribute [instance] _root_.Formalism.IndefR.RealTBAlt.alg
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
structure IndefiniteRealisationBoundedRows (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) : Prop where
  ioExt : IoExt B.Q.Rl.toRealDat
  oneMap : ∀ i, OneMapRowR B.T B.Q.Rl.toRealDat B.κ B.v₀ B.O (phEff B.Q.Rl) i
end Formalism.IndefR
end
end
end
