module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle136
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VvCastBVVRepr
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle516
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle487
import Formalism.LocalToGlobal.Columns.Bundle011
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle682
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle518
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem underQ_iff {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)) :
    I.UnderQ a v ↔ ∃ w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v, ¬ (I.xi a).UnrAt w := by
  have hq := GlobalTheory.Mem.ReadTwist.mem_qprime_iff (hI.xi_reads a) v
  have hab : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v ↔ w.under (𝓞 B.host.F) = v := fun w => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]
    rfl
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨w, hw, hu⟩ := hq.1 ((GlobalTheory.TwistPlaces.mem_QE_iff hI.sel_ok (I.tup a)).1 hP).1
    exact ⟨w, (hab w).2 hw, hu⟩
  · rintro ⟨w, hw, hu⟩
    have hv := hq.2 ⟨w, (hab w).1 hw, hu⟩
    exact ⟨I.sel v, (Formalism.L2.Col.mem_QE I.sel (I.tup a) _).2 ⟨v, hv, rfl⟩, GlobalTheory.TwistPlaces.under_eq_iff.2 (hI.sel_ok v)⟩

theorem carH_of_cols {D : D7} (C : ColsTiedSym D) : CarH C.herm.base C.forms := by
  refine ⟨C.eV, ?_, C.car0, C.carC, C.carM, C.sp, C.fr0⟩
  intro u v a
  rw [C.res u]
  exact (C.herm.atT u).res_F v a

theorem colsTwPTiedS_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)), tp.xi = I.xi → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → ∃ t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z), I.StdTw l Z l0 t := by
  intro B X I hI hP l Z l0 nch tp C hxi hC hLv
  have hQ : ∀ a v, tp.InQ' a v ↔ I.UnderQ a v := fun a v => by
    rw [underQ_iff hI a v]
    unfold Formalism.L2.Host.TupTied.InQ'
    rw [hxi]
    exact Iff.rfl
  have hF : ∀ u, I.StdF l Z u (C.forms u) ∧ I.StdLvC l Z u (C.forms u) := fun u => ⟨hC u, hLv u⟩
  obtain ⟨T, J, W, hM, hW, ⟨lvJ⟩, hPt⟩ := GlobalTheory.T.trueColumnChoice_exists_chainData_with_basePoints I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms hQ hF (carH_of_cols C)
  obtain ⟨⟨Lv, hL⟩, ⟨same⟩⟩ := GlobalTheory.T.tupleChains_levelStructure_compatible_at_levelPrime I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms T J W hF hW
  obtain ⟨Pt, E, hG, hS⟩ := GlobalTheory.T.tupleLayerCompatibilities_of_X_prime I hI hP l Z l0 (fun a v => tp.InQ' a v) C.herm.base C.forms T J W Lv hQ hF hW hL hPt
  exact ⟨{ ch := T, chJ := J, chM := hM, forms := W, lv := Lv, same := same, lvJ := lvJ, pt := Pt, ptG := hG, ptE := E }, hW, hL, hS⟩

end GlobalTheory.Mem.Col2.TC

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.exists_liftForms_adelic_decoratedLattices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 → Seed.FrmC.StdLat (Vc X.toD7 i) → ∃ s : ∀ t, Seed.LiftSideT (famR X I hX U Xg tr) L cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) i t, (∀ t,       (∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG ((s t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _))) ∧
      Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef (s t).pres (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) (s t).pres ((famR X I hX U Xg tr).heckeLI i t)
        (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
        (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
        fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1)) ∧ BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (s t).pres.extL φ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.exists_liftSide | exact GlobalTheory.Mem.R3.LiftBrg.exists_liftSide | (intros; apply GlobalTheory.Mem.R3.LiftBrg.exists_liftSide <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
  first | exact @GlobalTheory.HeightCounting.Up.rootsLL_evLgG | exact GlobalTheory.HeightCounting.Up.rootsLL_evLgG | (intros; apply GlobalTheory.HeightCounting.Up.rootsLL_evLgG <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowStd



theorem exists_std_wtCast : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → ∃ c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W,
      (∀ v, c v = c0R (wtCast X v)) ∧
      LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) ∧
      Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ ∧
      (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) ∧
      (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
        Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) ∧
      ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ,
        (∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
          P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (GlobalTheory.Mem.R3.RowAd.decoAd X I t h))) ∧
        Bridge.CoefTie X.toD7.sp.X' cX.coef P (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
          (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hc hgr hM hin hb
  obtain ⟨c, hc0, hInter, hli, hsp, hinn, hT⟩ := exists_coef X px I hX U Xg tr L hI cX gramR c0R hc hgr hM hin
  refine ⟨c, hc0, hli, hsp, hinn, hInter, fun t => ?_⟩
  obtain ⟨P, hPc, hPy, hPe⟩ := GlobalTheory.T.rowsClassSet_presentation_coefficientMap X px I hX U Xg tr L eG hI hV hL hG hb cX c hInter hli hsp hinn t
  exact ⟨P, hPe, hT t P hPc hPy⟩


end GlobalTheory.Mem.R3.RowStd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_spectralObjects_over_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  first | exact @GlobalTheory.Mem.SRe.satOfDiscreteSeries | exact GlobalTheory.Mem.SRe.satOfDiscreteSeries | (intros; apply GlobalTheory.Mem.SRe.satOfDiscreteSeries <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.RowAt

theorem ev_scale {p : ℝ → ℝ → Prop} (h : ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, p eps x₀) :
    Ev fun K => ∃ x₀ : ℝ, x₀ ≤ K.s.x ∧ p K.s.eps x₀ :=
  ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    let ⟨x₀, hx⟩ := h eps h0
    ⟨x₀, fun _ _ _ _ hs hx' => ⟨x₀, hx', hs ▸ hx⟩⟩⟩⟩⟩⟩



theorem atDat_rowTest : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK →
    RatioK → GlobalTheory.RowEx.ExField → StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt →
      GlobalTheory.RealGeo.InGeo z.geo → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  intro hG hC h1 h2 h3 h4 h5 h6 h7 hEF
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.rowTest_at_realisation_of_hilbertModels hC h1 h2 h3 h4 h5 h6 h7
  obtain ⟨CF2, H2⟩ := GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData hEF
  have hCh := H2 (max CF1 CF2) (le_max_right _ _)
  have e1 := ((evG_of_ev (ev_scale fun eps _ => H1 eps (max CF1 CF2) (le_max_left _ _))).inter GlobalTheory.T.eventually_stages_parameterSizeConditions).inter
    (evG_of_ev GlobalTheory.T.hidaSetting_of_sizeRows)
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg hCh)
  refine s1.trans (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨⟨⟨x₀, hx, hH⟩, hLed⟩, hSet⟩ B f T hO - - hch w - Z hX Wt z g1 - hEx -
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hG (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz⟩ := hLed (w.st Z') hO hη hA
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  exact (GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer B w.C Z Z' w.px w.I hX T Wt s z).2 (by
    have hEx' := DatCopy.copy_exAt Z' s hEx
    generalize DatCopy.copy Z' s z = y at hEx' ⊢
    have hS := hSet B f T w Z' hX Wt y hO g1' hEx' L hsz
    exact hH (w.st Z').toD7 L (by rw [hsc]) (by rw [hsc]; exact hx) _ _ _ _ _ _ y.R y.F hS (hch w Z' hX Wt y L hsc hS))

end GlobalTheory.Mem.R3.Rw.RowAt

end
end
