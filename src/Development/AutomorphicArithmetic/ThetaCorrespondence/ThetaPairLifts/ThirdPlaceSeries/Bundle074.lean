module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle928
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle937
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle468
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle581
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle061
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle066
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftInfRef
open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj2
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open GlobalTheory.LiftRef
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem core_data_of_point (D : D7) (cf : CharFrame D) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (chr : CharSide D cf) (M : MtFam D)
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hIn : MtInput D M tup Q) (k : ℕ) (h1 : 1 ≤ k + 1) (h2 : k + 1 ≤ D.R.m)
    (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (k + 1) h1 h2).wt.W))
    (hS : NG.IsIrrRep (M D.what₂.mu0 (k + 1) h1 h2).wt.ρ S) (μ : D.naut.CG 1)
    (hμ : (chr.e1 μ).1 = cf.mu0 ⟨k, by omega⟩) (τ : D.what₂.Tau) :
    D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧
      D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) := by
  set π := autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS with hπ
  obtain ⟨b, hd, -, -⟩ := GlobalTheory.algWt_contragredient D.host.E D.R.nV π.toAlgWt
  have hw := A.wt (k + 1) h1 h2 π b hd
  obtain ⟨lam, hlam⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1.exists
  obtain ⟨lam', hlam'⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ))).1.exists
  have hbar : GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar, ComplexEmbedding.conjugate_coe_eq]
  have hpar : NG.infOf lam = NG.paramV D.R (D.hc τ) ⟨k, by omega⟩ (1 / 2) := hIn.wt D.what₂.mu0 ⟨k, by omega⟩ τ b lam hd hlam
  have hinf1 := A.infW (k + 1) h1 h2 b _ lam hlam
  have hinf2 := A.infW (k + 1) h1 h2 b _ lam' hlam'
  have hconj := infOf_conj hlam hlam'
  have he : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1 = cf.mu0 ⟨k, by omega⟩ * cf.eta⁻¹ := by
    rw [chr.tw, hμ, chr.etaTinv]
  have hI : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1.HasInfQ (embPsi D.host)
      (fun g => -eExp D ⟨k, by omega⟩ g - 1 / 2) := by
    rw [he]
    have h1' := (cf.isMu0 ⟨k, by omega⟩).inf
    have h2' : (cf.eta⁻¹).HasInfQ (embPsi D.host) (-(fun _ => 1 / 2)) :=
      GlobalTheory.BlockCharInf.hasInfQ_inv' ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
    convert GlobalTheory.BlockCharInf.hasInfQ_mul' h1' h2' using 1
    ext g
    change -eExp D ⟨k, by omega⟩ g - 1 / 2 = -eExp D ⟨k, by omega⟩ g + -(1 / 2)
    ring
  obtain ⟨hg1, hg2⟩ := chr.infG _ _ hI (D.eTau τ)
  have hval : eExp D ⟨k, by omega⟩ (D.eTau τ) = (D.hc τ).e ⟨k, by omega⟩ := by simp [eExp]
  have hG1 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {(-((D.hc τ).e ⟨k, by omega⟩ : ℂ) - 1 / 2)} := by
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ = embPsi D.host (D.eTau τ) from rfl, hg1, hval]; push_cast; ring_nf
  have hG2 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)) =
      {(((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2)} := by
    rw [← hbar, show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau τ)) from rfl, hg2, hval]; push_cast; ring_nf
  rw [hw, hinf1, hbar, hinf2, hconj, hpar]
  constructor
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG1, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun c _ => ?_
      push_cast; ring
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG2, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map, Multiset.map_map,
      Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · have hf := range_rev D.R.t (fun c : ℕ => ((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2 - ((D.R.t : ℂ) - 1) / 2 + c)
      refine (Multiset.map_congr rfl fun c _ => ?_).trans (hf.symm.trans (Multiset.map_congr rfl fun c hc => ?_))
      · simp only [Function.comp_apply]; push_cast; ring
      · have hc' := Multiset.mem_range.1 hc
        rw [Nat.cast_sub (show c ≤ D.R.t - 1 by omega), Nat.cast_sub (show 1 ≤ D.R.t by omega)]
        push_cast; ring
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
end GlobalTheory.LiftInfRef
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.TypePlacesCover
variable {D : D7}
end GlobalTheory.TypePlacesCover
open GlobalTheory.TypePlacesCover in
theorem GlobalTheory.TypePlacesCover.gPlaces_all_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GPlaces (Dof x) :=
  fun _ => StepW.of_all fun _ _ _ _ _ _ _ _ _ x _ => gPlaces (Dof x)
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Mem.SJ
namespace GlobalTheory.Mem.KJoinLat
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem joinSI_nonempty_and_V0_spans (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (hPin : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q) (hSee : _root_.Formalism.IndefR.IndefiniteRealisationExtends Q) (n : ℕ)
    (hOk : P.A3.fam3.Ok3 n) (hSep : P.A3.fam3.TypesSep3) (hPrim : PrimRows3 Q.Rl Q.F)
    (hLat : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR)
    (hDc : RowsHoldDcPt3 P) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK) (hJ : _root_.GlobalTheory.Mem.JTop.JoinPinAlt Q) :
    Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  obtain ⟨eE, hRead, hRow⟩ := hJ
  have hι : Q.ιS = (Formalism.L2.SG.RowsJoinPinned.iotaX S.X S.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D S.X S.inst Q.ιS).1 Q.ιS_eq
  have hEv := Q.seeEval (by obtain ⟨-, c', hc'⟩ := hSee; exact ⟨c', hc'⟩)
  rw [hι] at hEv
  have hκ : Q.uS * (Q.κS : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h0
      have := Q.uS_norm
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    · exact_mod_cast Q.seeK.1.ne'
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    core_latTie Q.Rl Q.F n hOk hSep Q.charW hPrim hSchur hSig P.Zs Q.zs P.S0 P.S1 Q.s1 P.Dc Q.dc P.Sp Q.sp ex.p0 P.C P.NuC
      P.I P.tied.div hLat (fun u x y => hDc u P.A3.A.μ0 x y) S.X S.inst S.G S.Y.hK (_root_.Formalism.IndefR.pwOf_alt S Q.hin) Q.wdD Q.bR Q.wdD_wU
      Q.spPin (_root_.GlobalTheory.Mem.JTop.bR_heq_eMu_single Q hPin) Q.tS Q.cS hEv Q.sEE Q.sEEc _ Q.sEEj hκ
      (fun x hx => (Q.seeDef x hx).trans (by rw [hι])) eE hRead
  refine ⟨⟨⟨Rd.wU, hw, M.cφ, M.cF, M.eR, h1, h2, h3, h4, fun hF => ?_⟩⟩, hon⟩
  obtain ⟨v₀, -, a, -, hj⟩ := hRow hF
  exact hT (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF) v₀ a hj
end
theorem join_subspace_real_data_lattice_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), ∀ n : ℕ, SchurAll D → _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y) → Holds x.R x.F → x.A3.fam3.Ok3 n → x.A3.fam3.TypesSep3 → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).XE (divisionPairOfAdelicFormsFaceColumnsData x).I.eRR → RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc (S.toRealSpectralMatching Rc) (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c n hSchur hPins hH hOk hSep hLat hDc hSee hEv hRow
  obtain ⟨hSx, hJ⟩ := _root_.GlobalTheory.Mem.JPin.seeEx_joinPin_alt D L hT Gi Gl K Yd cX ex x Rc P S y c hH hSee hEv hRow
  exact _root_.GlobalTheory.Mem.KJoinLat.joinSI_nonempty_and_V0_spans (_root_.GlobalTheory.Mem.R3.realisationOfInput y) hPins hSx n hOk hSep (Holds.prim hH) hLat hDc hSchur (D.sp.Y_sig 0) hJ
end GlobalTheory.Mem.KJoinLat
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.recursion_local_row_condition_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), ∀ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (∀ hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt Rc.T.n.gal.lp x.R.θ x.Y.PY (x.R.MY 0) (fun b => levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun b => Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun _ => x.R.e0) x.Y.eFT → _root_.Formalism.IndefR.IndefiniteRealisationCompatible hp (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) ∧ (Formalism.IndefR.RecTie.PartsRec x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.PY x.Y.PW x.Y.eFT r.E r.labPi r.piOf x.Y.Ish.prt x.Y.IL.prtW → (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow) ∧ PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG := by
  first | exact @_root_.GlobalTheory.Mem.R3.RecPinsTie.main_alt_alt | exact _root_.GlobalTheory.Mem.R3.RecPinsTie.main_alt_alt | (intros; apply _root_.GlobalTheory.Mem.R3.RecPinsTie.main_alt_alt <;> assumption)
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB
namespace GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {O : Obj D} {c : ℝ}
def BundleCondition.TiePins (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q) : Prop :=
  PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG ∧ _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q ∧ ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q, _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
abbrev BundleCondition.Comparison₂ (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Type 1 := {Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion b.B.Q // b.TiePins Rr}
theorem BundleCondition.Comparison₂.psi {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : PsiPPTie D b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.I.eG := t.2.1
theorem BundleCondition.Comparison₂.pins3 {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree b.B.Q := t.2.2.1
theorem BundleCondition.Comparison₂.pins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := let ⟨h, _⟩ := t.2.2.2; h
theorem BundleCondition.Comparison₂.recPins {b : _root_.GlobalTheory.Fc.BundleCondition D O c} (t : b.Comparison₂) : _root_.Formalism.IndefR.IndefiniteRealisationCompatible t.pins t.1 := let ⟨_, h⟩ := t.2.2.2; h
@[reducible] def BundleCondition.part (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) : _root_.GlobalTheory.Fc.Ind.PointSummands D O c where
  R := b.R
  S := b.S
  P := b.P
  pin := b.pin
  DH := b.DH
  Dcf := b.C.c.face
  Spf := b.C.Sp
  ok1 := b.C.ok1
  B := b.B
  Rr := t.1
  psi := t.psi
  pins := t.pins
  muDef := t.pins3.muDef
  recPins := t.recPins
end Point
def HasCompatibility : BdP _root_.GlobalTheory.Fc.BundleCondition := fun _ _ _ b => Nonempty b.Comparison₂
section Sel
variable {𝒜 : FamClass}
abbrev CompatibleSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Type 1 :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), (σ Fm hc x hx i).Comparison₂
def summandSelection (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) (τ : _root_.GlobalTheory.Fc.CompatibleSelection σ) : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜 :=
  fun Fm hc x hx i => (σ Fm hc x hx i).part (τ Fm hc x hx i)
end Sel
section Construction₂
end Construction₂
end GlobalTheory.Fc
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.series_character_eq_inv_emb_psi0 : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ _ w _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x, (∀ g : Gc B w.px, x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U ↔ g ∈ x.m.z.F.P0) ∧
  ∀ i b (g : x.m.z.F.P0) (h : x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U), l.b.ser.ex.ρ.e i b ((Dof x).nexp.psiU i b ⟨_, h⟩ : (FractionRing ((Dof x).ntw.O i))ˣ) = ((Dof x).what₂.embLL (x.m.z.F.ψ0 g : (Dof x).what₂.LLˣ))⁻¹ := by
  first | exact @_root_.GlobalTheory.StateLevel.level_char_allSt_alt | exact _root_.GlobalTheory.StateLevel.level_char_allSt_alt | (intros; apply _root_.GlobalTheory.StateLevel.level_char_allSt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.isChoice_of_start_of_over : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T}, K.Over B.toPre → GlobalTheory.Mem.Top.Bl.Start K B f T w → ∀ {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x), IsChoice (D := GlobalTheory.HeightCounting.Up.Dof x) (Set.range l.Pq) ∧ (∀ t, ∀ Q ∈ x.m.z.R.Q t, Q ∈ Set.range l.Pq) ∧ (∀ j, FWT.VStd (GlobalTheory.HeightCounting.Up.Dof x) j) ∧ x.m.z.R.C = GlobalTheory.HeightCounting.Up.cfOf x ∧ ∀ (k : Fin 2) (z : ℂ), z ^ ((GlobalTheory.HeightCounting.Up.Dof x).host.g k * ((GlobalTheory.HeightCounting.Up.Dof x).host.g k - 1)) = 1 → z ∈ (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)).fieldRange := by
  first | exact @_root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt | exact _root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
def com_z : Com D where
  θ := (_root_.GlobalTheory.Fam.pk_z W).θ
  ψ := (_root_.GlobalTheory.Fam.pk_z W).ψ
  μ := (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0
  η := (_root_.GlobalTheory.Fam.pk_z W).eta
  Pg := (_root_.GlobalTheory.Fam.pk_z W).Pg
  P := _root_.GlobalTheory.Fam.complexLevelStructure W
  chi := (_root_.GlobalTheory.Fam.pk_z W).chi
def inverseLevelCardinality : ENNReal := ((Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ENNReal))⁻¹
def stageOfSpaceY (j : ℕ) : PiLocalization₂ D where
  V := Yc D j
  par := parB (Ptw D) (min j D.R.m)
  M := (_root_.GlobalTheory.Fam.pk_z W).MY j
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛY j
  β := (_root_.GlobalTheory.Fam.pk_z W).βY j
  L := (_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 j (_root_.GlobalTheory.Fam.complexLevelStructure W)
  ν := _root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νY W.P.A3.A.μ0 j
  fd := (_root_.GlobalTheory.Fam.pk_z W).fdY W.P.A3.A.μ0 j
def stageOfSpaceX : PiLocalization₂ D where
  V := D.sp.X'
  par := parB (Ptw D) D.R.m
  M := (_root_.GlobalTheory.Fam.pk_z W).MX
  Λ := (_root_.GlobalTheory.Fam.pk_z W).ΛX
  β := (_root_.GlobalTheory.Fam.pk_z W).βX
  L := datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0
  ν := _root_.GlobalTheory.BaseChain.inverseLevelCardinality W • (_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0
  fd := (_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
def transitionBetweenSpacesY (j : ℕ) : Step (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)) where
  ω := (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j
  f := (f.row W.P.A3.A.μ0).vP j
  It := (_root_.GlobalTheory.Fam.pk_z W).ItY j
  io := (f.row W.P.A3.A.μ0).io j
def transitionToSpaceX (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : Step (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)) (_root_.GlobalTheory.BaseChain.stageOfSpaceX W) where
  ω := omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h
  f := (f.row W.P.A3.A.μ0).vT j h
  It := f.c.ItT j h
  io := (f.row W.P.A3.A.μ0).ioT j h
end GlobalTheory.BaseChain
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.UpPin
theorem steps_pin_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, (_root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevelExists hL) ∧ (_root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevelExists hL) ∧
    (_root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevelExists hL) ∧ (StepW Start HasBare → _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL → SMt → _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL → _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL → _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep →
      _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep → _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL → _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep → ∀ (S : SExt) (Γ : GeoP), StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL cDep) S Γ).s)) := by
  intro hL cDep
  refine ⟨fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), ?_⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro hB hA hMt hRat hCu hB0 hB1 hB2 hC hFin S Γ
    have h := hB.and (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
    refine h.trans (StepW.of_all ?_)
    intro K B f T w _ _ H
    obtain ⟨⟨P, x, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
    obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
    obtain ⟨imt⟩ := mt P x1
    obtain ⟨irat⟩ := rat P x1 la
    have li : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
    obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
    obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
    obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
    obtain ⟨sc⟩ := c P x4 l2
    obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ (p4 (p3 p2))
    exact ⟨Z, ⟨v⟩⟩
end GlobalTheory.HeightCounting.UpPin
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmARatio
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host
end GlobalTheory.ThmARatio
theorem GlobalTheory.ThmARatio.values_as_toric_sums_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL ((nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) * p.Tp.psi w) Λ → GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    ∃ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ∧
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ ∧ T₀ ≠ 0 ∧ Λd s = T₀ ∧
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) ∧ Λ s = T ψc := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit _ hF hTor w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨_, _, hfd, hb, -⟩ := hF
  have hχ : fam d.G p.P.A3.A.μ0 i j (some (decide (D.what₂.places.resChar w = D.host.pde))) =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    unfold fam GlobalTheory.FunObj.SqNum.delOf Formalism.L2.Host.CharFrame.delAt
    by_cases h : D.what₂.places.resChar w = D.host.pde
    · simp only [h, decide_true, cond_true, if_true]
    · simp only [h, decide_false, cond_false, if_false]
  obtain ⟨T₀, ⟨hv, h0⟩, hne, hL, -⟩ := hTor i j s hs1 hs2 (some (decide (D.what₂.places.resChar w = D.host.pde)))
  rw [hχ] at hv h0 hL
  have hP := p.Tp.psi_is w hw
  obtain ⟨a, ha⟩ := hP.ord
  have hQ := (GlobalTheory.ToricDenom.placesBelow_splitCoprimeConductor_of_admissible (hfit.1.cond w hw) (𝔣 := GlobalTheory.FunObj.SqNum.condF d.G.pl) fun P h =>
    (hfit.1.list _ (hfit.1.setting.inW1 hw)).1 P (GlobalTheory.ThmARatio.dvd_cond0 d.G.pl _ h)).1
  obtain ⟨ψc, T, h1, h2, h3⟩ := GlobalTheory.ThmARatio.twisted_value hfd.2.2.2.2.2.2.1 hfd.2.2.1 hs1 hb hQ hv
    (pow_ne_zero a (D.what₂.places.resChar_prime w).ne_zero) ha hP.triv hP.tame hP.ram hΛ
  exact ⟨T₀, ψc, T, hv, h0, hne, (hL Λd hΛd).symm, h1, h2, h3⟩
end
end
end
