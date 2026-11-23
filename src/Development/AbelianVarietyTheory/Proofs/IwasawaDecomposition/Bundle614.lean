module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle035
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle551
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle572
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle612
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle437
import Formalism.LocalToGlobal.Columns.AdelicLemmas
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumnChoice_exists_standardChainData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch) (C : ColsTiedSym (I.rec7 l Z)), tp.xi = I.xi → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → ∃ t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z), I.StdTw l Z l0 t := by
  first | exact @GlobalTheory.Mem.Col2.TC.colsTwPTiedS_std | exact GlobalTheory.Mem.Col2.TC.colsTwPTiedS_std | (intros; apply GlobalTheory.Mem.Col2.TC.colsTwPTiedS_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowsRead

theorem decoPt_eq_decoAd (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι} (t : TupU I U)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) (hc : CMData X.B.fields.F X.B.fields.E)
    (h : Bridge.Gf X.toD7.sp.X') (x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1))
    (hM : MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1)) :
    Formalism.L2.Col.decoPt hc (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (QuotientGroup.mk x) =
      GlobalTheory.Mem.R3.RowAd.decoAd X I t h := by
  have hx : x.1 = GlobalTheory.Mem.R3.RowAd.ptE X h := by
    ext i j
    have := hM.2 (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i) (Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j) i j rfl rfl
    rw [hβ, matIn, mul_one] at this
    exact this.symm
  rw [Formalism.L2.Col.decoPt_mk, hx]
  rfl

theorem exists_matEq_ptE (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) :
    ∃ hc : CMData X.B.fields.F X.B.fields.E, ∀ h : Bridge.Gf X.toD7.sp.X', ∃ x : Formalism.L2.Col.UAd hc (X.B.R.N X.B.R.m - 1),
      MatEq (matIn X.toD7.sp.X' L.βX h) (show GL (Fin (X.B.R.N X.B.R.m - 1)) (Lev.EAf X.toD7) from x.1) := by
  refine ⟨X.toD7.sp.cm, fun h => ⟨⟨GlobalTheory.Mem.R3.RowAd.ptE X h, GlobalTheory.Mem.R3.RowDeco.ptE_mem_UAd X I hI h⟩, GlobalTheory.Mem.R3.RowAd.rank_X' X, ?_⟩⟩
  intro i j i' j' hi hj
  obtain rfl : i = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm i' := Fin.ext hi
  obtain rfl : j = Fin.cast (GlobalTheory.Mem.R3.RowAd.rank_X' X).symm j' := Fin.ext hj
  rw [hβ, matIn, mul_one]
  rfl



theorem exists_rowSide : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ _
  obtain ⟨c, -, hli, -, -, hcI, hP⟩ := GlobalTheory.Mem.R3.RowStd.exists_std_wtCast X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin hβ
  choose P hPr hCo using hP
  have hRd : ∀ t, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t (P t) := fun t => ⟨c, hPr t⟩
  choose a ha using fun t => GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)
  refine ⟨fun t => { pres := P t, act_tie := a t, hecke := (GlobalTheory.T.splitHecke_rows_eq_doubleCoset_operators X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)).some },
    fun t => ⟨ha t, hCo t, GlobalTheory.Mem.R3.RowAd.Inert.exists_inertTie X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgr hmap hin t (P t) (hRd t)⟩, c, hcI, ?_, hli, exists_matEq_ptE X I hI L hβ⟩
  intro hc t φ h x hM
  refine (hPr t _ h).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (fun d => c (φ.2.1 d)) (decoPt_eq_decoAd X I t L hβ hc h x hM).symm

end GlobalTheory.Mem.R3.RowsRead
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.constructionStartingChoices_of_fine_adelicData : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → WeightCaseCondition → StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G → GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → Fine z → (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) → (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) → ∃ P : Pre2 K w, P.Z₀ = Z ∧ P.Wt = z.W1 (F0K K.s (w.D Z)) ∧ Ext z P.z := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_pre2_of_fine_of_resChar_mem | exact GlobalTheory.Mem.R3.Rw.exists_pre2_of_fine_of_resChar_mem | (intros; apply GlobalTheory.Mem.R3.Rw.exists_pre2_of_fine_of_resChar_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem sizes_host_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine EvG.imp (GlobalTheory.T.eventually_hundred_le_hermitianRank_columnChoices.inter (GlobalTheory.T.eventually_two_mul_rank_le_levelPrime.inter (GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder.inter (GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic.inter (GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices.inter (GlobalTheory.T.eventually_spacesV_definite_columnChoices.inter GlobalTheory.T.eventually_auxiliary_places_split_distinct)))))) fun K _ _ _ _ H => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))).imp fun B f T _ G hk T' w Z =>
    ⟨G.1 hk T' w Z, G.2.1 hk T' w Z, G.2.2.1 hk T' w Z, G.2.2.2.1 hk T' w Z, G.2.2.2.2.1 hk T' w Z, G.2.2.2.2.2.1 hk T' w Z,
      G.2.2.2.2.2.2 hk T' w Z⟩

end GlobalTheory.HeightCounting.Up
end
