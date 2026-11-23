module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle012
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle146
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle157
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle163
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle158
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle114
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle153
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle159
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle155
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UkTermOfMoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle457
public import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorOfPairLift
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colView_of_built {𝒮 : GlobalTheory.Mem.Top.Bl.Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (b : GlobalTheory.Mem.Top.Bl.Built 𝒮 K w Z c) : ColView w Z c.O.tw c.O.nch :=
  { jets := b.pin.jets
    rowInt := b.what₂.rowInt
    tw_eq := congrArg (fun s => s.2.2.1) b.ker_eq
    tup := ⟨b.n.tp, b.n.xi⟩ }

theorem overCols_built : ∀ 𝒮 : Slots, OverCols (IsBuilt 𝒮) ∧ ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) →
    OverCols (positionOf P) := by
  intro 𝒮
  have key : ∀ P : CP, (∀ K B f T w Z c, P K B f T w Z c → BuiltC 𝒮 K B f T w Z c) → OverCols (positionOf P) :=
    fun P hP K X f T c hc =>
      positionOf_mono (fun K B f T w Z c h => let ⟨b⟩ := hP K B f T w Z c h; colView_of_built b) K X f T c hc
  exact ⟨key (BuiltC 𝒮) fun _ _ _ _ _ _ _ h => h, key⟩

end GlobalTheory.Fc.Cv

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.Fc.LabLinked

def Ties (D : D7) : Prop :=
  ∃ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ Formalism.L2.SG.RowDict.RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι


section Rows

open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX


end Rows

theorem lab_of_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
  fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩


end GlobalTheory.Fc.LabLinked
end

section

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem moveStep_fam (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    GlobalTheory.KerT.MoveStep (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := by
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hEq := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  obtain ⟨-, hLat, hTh⟩ := GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hM := GlobalTheory.ThetaMove.moveStep_of_family I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hEq hLat
    (fun a b _ _ => hTh a b) hJa
  rw [← AmbIn.amb_eq_ambOf] at hM
  exact hM

theorem kernelCondition_at_row_family (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    Dat.KerUK (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro b b' d d' P F
  exact UpLaw.kAt_uk B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr
    h.sel_ok (h.T_mem u) (h.idx_ok a) (I.Tp a) I.A (isTerm h u a hi)
    (GlobalTheory.KerT.UK.ukTerm_of_moveStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) I.A u i hX hPr h.sel_ok
      (h.T_mem u) (moveStep_fam h hJ l Z u a hi)) b b' d d' P F

theorem laws_true_fam : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∃ Bd : Built.Dat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u, Bd.ch = tw (I.tw l l0 Z) u a ∧
      (∀ i, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
        letI : NumberField Bd.E := Bd.nE
        Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧
      (∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m → ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧
      Bd = dat I l Z u a := by
  intro B X I h hJ l l0 Z u a
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hE := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hV := (GlobalTheory.T.normalisedThetaFamily_vectors_lattices_thetaZero _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1
  have hth : ∀ (a : I.ι) (u : B.Word), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a)
      (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) := fun a u =>
    GlobalTheory.ChainTheta.chTh_ok_of_colIn' B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ hE hV a u
  refine ⟨dat I l Z u a, dat_ch I l l0 Z u a, fun i _ => split u a h i, sees l Z u a, fun i hi => ?_, rfl⟩
  change i < B.R.m at hi
  have hKerEq : Dat.KerEq (B := dat I l Z u a) (i := i)
      (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
    obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
    refine ⟨fun b b' g g' d d' => ?_,
      GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives B X I h hJ l Z hV u a i hi⟩
    rcases lt_trichotomy (i + 2) B.R.m with hlt | heq | hgt
    · exact GlobalTheory.MatLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) hlt b b' g g' d d'
    · exact GlobalTheory.CoupledLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) heq b b' g g' d d'
    · exact TopEq.kAt_top_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) (by omega) b b' g g' d d'
  exact ⟨_, hKerEq, kerDil h l Z u a hi,
    kernelCondition_at_row_family h hJ l Z u a hi, GlobalTheory.T.trueChainKernels_bound_conjugatePrimePlaces GlobalTheory.T.kernelJets_levelPlace_integralMoments GlobalTheory.T.weylModule_simple_closedLowestAlcove B X I h hJ l Z u a (hth a u) i hi,
    GlobalTheory.T.trueChainKernels_bound_levelPrimePlaces GlobalTheory.T.kernelJets_levelPlace_integralMoments GlobalTheory.T.weylModule_simple_closedLowestAlcove B X I h hJ l Z u a (hth a u) i hi⟩

end GlobalTheory.LvT.Built.TrueLaws
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.KapLinked

section Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}



theorem isot_ne_bot_of_rows (hF : GlobalTheory.Published.HarishChandraFinite) (hG : GlobalTheory.Published.GreenCuspidal) (t : RowsT K w Z Wt p0)
    (hM : GlobalTheory.CuspMult.MultEq t.r.z.R.toRealDat) (σ : Fin (w.D Z).what₂.Drows) (i : Fin (w.D Z).R.m) :
    (w.D Z).what₂.isot ((i : ℕ) + 1) ((w.D Z).what₂.ft σ) ≠ ⊥ := by
  have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
    (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) t.grp).2.1
  have hGS : Formalism.L2.DIV.GoodStable t.r.z.Xg := by
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL t.r.z.Xg t.r.z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [t.r.z.good.2, t.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1
  exact GlobalTheory.KapIsotRead.isot_ne_bot_read hF (w.st Z).toD7 _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.z.pins t.r.intersectionNumber_baseChange hM hGS
    (GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_base_ne_zero t.r.z.R.toRealDat t.r.z.F.lv2 t.r.intersectionNumber_baseChange.ok.ok2 hC.lev hC.grp _ hI) σ i



theorem goodTypes_of_rows (t : RowsT K w Z Wt p0) : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes t.r.z.R.toRealDat := by
  have hT : TypesTrue (w.st Z).toD7.ntypes t.r.z.R.C.P t.r.z.R.C.W := by
    rw [t.r.z.lev.C, w.C_eq]
    exact t.grp
  exact GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue t.r.z.pins.char.base.lev hT

end Rows


end GlobalTheory.Fc.KapLinked

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedPointRow_admissible_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), Formalism.L2.G.Adm2InU.TwistedPointIntegral (I.rec7 l Z) (I.tw l l0 Z) := by
  first | exact @GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok | exact GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok | (intros; apply GlobalTheory.PerQ.twistedPointIntegral_of_TC_ok <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.EX.G4

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem w_of {eps : ℝ} (Fm : FamP eps) (h13 : FirstTheoremAtFamily Fm) (hLa : 0 < Fm.GK.La) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AuxBlock8.WeightVectorExists (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK := by
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨CH, C', b0, b1, b2, b3, b4, b5, b6, hp13⟩ := h13
  obtain ⟨Cm, hCm, h8⟩ := family_first_bound_of_theorem Fm CH C' (kapIDefF Fm) b0 b1 b2 b3 b4 b5 b6 hp13
  obtain ⟨C31, -, h1⟩ := family_first_lemma Fm
  obtain ⟨x0, h⟩ := ((((h1.and (family_orders_bound_of_lemma Fm (TopChoiceBounds.family_band_ratio_holds Fm) hCN)).and
    (family_sizes_bound Fm hLa (eps / 48) (by positivity))).and h8).and (eventually_sizes_admitted Fm)).and (Ev.x1 Fm)
  obtain ⟨x2, H2⟩ := Filter.eventually_atTop.1 (AuxBlock8.Pf.numMean_ev eps Fm.GK Fm.GK_nonneg Cm hCm)
  obtain ⟨x3, H3⟩ := Filter.eventually_atTop.1 (AuxBlock8.Pf.restHypI_ev eps Fm.GK Fm.GK_nonneg Cm C31)
  refine ⟨max x0 (max x2 x3), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_max_left _ _) hx
  have e2 : x ≥ x2 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e3 : x ≥ x3 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨⟨⟨⟨⟨a1, a4⟩, a5⟩, a8⟩, aSz⟩, hx1⟩ := h x e0 i
  have NM := H2 x e2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i hx1) (Fm.L_eps x i) aSz.1 a5
  have HI := H3 x e3 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.L_x x i hx1) (Fm.L_eps x i) aSz a5 a4 a1 NM
  exact AuxBlock8.Pf.weight_condition_of_mean_excess _ _ (AuxBlock8.Pf.meanEx_of (Fm.Gx x i) Fm.GK Fm.GK_nonneg Cm a8 NM HI a4.2.2.1
    (AuxBlock8.Pf.slopeEstimate_of_lemmaB_slopeLine (Fm.Gx x i) Fm.GK Fm.GK_nonneg Cm a8 NM HI a4.2.2.1))

theorem wClosed : DC.WClosed :=
  (((first_theorem_closed_form (fun _ => True) RangeOne.rangeOne_abs).and (signs_closed (fun _ => True))).and
    (TopChoiceBounds.family_log_bound_closed (fun _ => True))).imp fun Fm _ _ h => w_of Fm h.1.1 h.1.2.1 h.2

end GlobalTheory.EX.G4
end
end
