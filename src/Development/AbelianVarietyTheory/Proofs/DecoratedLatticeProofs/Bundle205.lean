module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle197
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle182
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle279
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.holomorphicContinuationValue_eq_div_mul : ∀ (Z L d Y : ℂ → ℂ) (s₀ z l : ℂ) (s₁ : ℝ), 0 < s₀.re → s₁ < s₀.re → AnalyticOnNhd ℂ d (rightOf 0) → (∀ s : ℂ, 0 < s.re → d s ≠ 0) → DifferentiableOn ℂ Y (rightOf s₁) → EqRight Z (fun s => L s / d s * Y s) → HolValueAt Z s₀ z → HolValueAt L s₀ l → z = l / d s₀ * Y s₀ := by
  first | exact @GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul | exact GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul | (intros; apply GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryPair_maps_completedHomLattice_onto_translate : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  first | exact @GlobalTheory.LatMoveStd.latO_moved_onto | exact GlobalTheory.LatMoveStd.latO_moved_onto | (intros; apply GlobalTheory.LatMoveStd.latO_moved_onto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.StdStepsT

theorem stdPair_steps_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → (∀ (i : ℕ), i + 1 ≤ B.R.m → StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ) ∧ (I.rec7 l Z).sp.X'.gram = 1 ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ (∀ τ, I.J.cD τ ≠ 0) ∧ ∀ (V : HSp (I.rec7 l Z)) (g : GA (I.rec7 l Z) V), ∃ x, IsDetRoot V g x := by
  intro B X I hI hP l Z ψ θ hψ hθ
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, GlobalTheory.Mem.Col2.Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact GlobalTheory.Mem.Col2.Crd.ortho_pos hs _
  have oX' : GlobalTheory.Mem.Col2.Crd.Ortho B.sp.X' := by rw [hX']; exact GlobalTheory.Mem.Col2.Crd.ortho_pos hs _
  have gX : ∀ j, (B.sp.X j).gram = 1 := fun j => by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.one_apply]
    exact (oX j).1 a b
  have gX' : B.sp.X'.gram = 1 := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.one_apply]
    exact oX'.1 a b
  have hcc : (I.rec7 l Z).host.ccK = ⊤ := B.toPre.ccK_top
  refine ⟨fun i hi => ?_, gX', fun τ => B.fields_embC τ, GlobalTheory.Mem.Col2.DgenNe.dgen_ne_zero B.host I.J.cD hI.amb_ok.dgen,
    fun V g => GlobalTheory.RecDict.exists_isDetRoot _ V g⟩
  have r1 := rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)
  have r2 := rankN (I.rec7 l Z) (i + 1) hi
  refine ⟨hψ, hθ, gX i, gX (i + 1), (I.rec7 l Z).sp.X_sig i, (I.rec7 l Z).sp.X_sig (i + 1), ?_, hcc, I.J.δ_ne_zero,
    GlobalTheory.AdForm.StdSteps.realPlace_cmTrace_zero_element_eq_I_mul_abs _ hcc, GlobalTheory.AdForm.StdSteps.scale_eq (I.rec7 l Z) I.J.δ_ne_zero⟩
  rw [r1, r2]
  exact ⟨Ranks.N_pos _ _, GlobalTheory.AdForm.StdSteps.N_lt_succ _ _, GlobalTheory.AdForm.StdSteps.even_N _ _, GlobalTheory.AdForm.StdSteps.even_N _ _⟩

end GlobalTheory.AdForm.StdStepsT
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → _root_.GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ T ∈ MultT θ M J χ, ∀ φ : L2X X, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX X := by
  first | exact @GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX | exact GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX | (intros; apply GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → _root_.GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  first | exact @GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv | exact GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv | (intros; apply GlobalTheory.Core.Mi.ConjEquiv.conjMap_equiv <;> assumption)
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
open Formalism.L2.SG.Pf

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scT_sc_genSet {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) :
    (scT X).sc (scT X).genSet = X.one X.genSet := by
  ext p
  simp only [PB.Terms.one, PB.Terms.sc, PB.Terms.allPairs, Set.mem_setOf_eq]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, trivial⟩⟩

theorem rowGen1P_of_steps (hCh : PN.NGChain) (hC : StepClass1) (hN : StepNormals1) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLoc1) (hTB : GlobalTheory.SnPos.StepThmBGP) : RowGen1P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨CB, hCB, a₁, b₁, hTB2⟩ := hTB Cg cb Cw cT CT C0 hcb hcT (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, a₂, b₂, hS2⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  obtain ⟨a₃, b₃, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨a₄, b₄, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨a₅, b₅, hH2⟩ := stepHeightG_of_normOne hO Cg cb Cw cT CT C0
  obtain ⟨a₆, b₆, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨a₇, b₇, hT2⟩ := hTi Cg cb Cw cT CT C0
  obtain ⟨a₈, b₈, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨a₉, b₉, hV2⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh meanAmplitudeGeneric_holds C1 C0n (C1 + C0n + 38) CB CSt Cgs CTs
    hCB hCSt hCg hCT le_rfl
  refine ⟨Cn, hCn, max a₀ (max a₁ (max a₂ (max a₃ (max a₄ (max a₅ (max a₆ (max a₇ (max a₈ a₉)))))))),
    max b₀ (max b₁ (max b₂ (max b₃ (max b₄ (max b₅ (max b₆ (max b₇ (max b₈ b₉)))))))),
    fun C' Cl e1 e2 D large₂ X Y u hTies hH0 hSt hT ha => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := e1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := e2
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hH0, hSt, hT⟩
  obtain ⟨hb, X0, ψ, hTie⟩ := hT2 C' Cl p7 q7 D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl p6 q6 D large₂ X Y u u hc hb X0 ψ hTie
  have hBk' : MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) (Irat * kapU D) (Ire * kapU D) :=
    massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨ν, hν⟩ := hE2 C' Cl p8 q8 D large₂ X Y u u hc
  obtain ⟨s, hs1, hs0, hsb, hLe⟩ :=
    hL2 C' Cl p0 q0 D large₂ X Y u hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  have hSum := hTB2 C' Cl p1 q1 D large₂ X Y u hTies hc hb X0 ψ hTie sd C Th F0 what₂ vR Q i0 i0' νq _ _ hBk' ν hν
  generalize bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq = B at hBk' hLe
  have hSz := hS2 C' Cl p2 q2 D large₂ X Y u u hc
  have hrd : 0 < D.host.rdE := by
    obtain ⟨-, -, hrd, -⟩ := hSz
    have hv : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
    rwa [hv] at hrd
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk'
  set ng : PN.Pts D.host.E D.R.rS → ℝ := fun γ => PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA * 2 *
      HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ PN.eN D.R.rS *
      nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u : ℕ)) γ with hng
  obtain ⟨hPt, -, -, hAmp⟩ := GlobalTheory.Core.One.genericTerms_points_agree_groupSums_corankOne D X Y u (sc s ν) ν ng
  have hVan : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u (sc s ν) (ptPN t) = 0 → (Y.tO u u).vec t = 0 := by
    intro t ht h0
    obtain ⟨g, hg⟩ := J2of_sc Y u u s ν (ptPN t)
    rw [hg] at h0
    have hp : (0 : ℝ) < (s g : ℝ) ^ 2 := by have := hs0 g; positivity
    exact hV2 C' Cl p9 q9 D large₂ X Y u hc ν hν t ht ((mul_eq_zero.1 h0).resolve_left hp.ne')
  have hIn : GenInputs (scT (Y.tO u u)) (NOf1 Y u (sc s ν) ν ng) D.R.f C1 C0n (C1 + C0n + 38) CB large₂.sc.b
      (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
      (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f))
      (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) 2 (Ire * kapU D) := by
    refine ⟨hC D X Y u hT _ _ _, hAmp hVan, hN2 C' Cl p3 q3 D large₂ X Y u hc _ _ _, ?_,
      localInputG_of_le _ _ _ _ _ hLe (fun γ => rfl), ?_, ?_, ?_, ?_⟩
    · exact fun γ hγ => hP2 C' Cl p4 q4 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun γ hγ => measureInputG_sc Y u s ν _ hsb ng γ ((hPt γ).1 hγ)
    · exact fun γ _ => ⟨nPt_nonneg _ hrd _ _ γ, le_rfl⟩
    · exact fun γ hγ => hH2 C' Cl p5 q5 D large₂ X Y u hc (sc s ν) ν ng γ ((hPt γ).1 hγ)
    · exact fun S hS => hSum (sc s ν) ng S (fun γ hγ => (hPt γ).1 (hS γ hγ))
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (scT (Y.tO u u)) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOf1 Y u (sc s ν) ν ng) _ B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    (large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) 2 (Irat * kapU D) (Ire * kapU D)
  rw [hcard] at key
  have r := key ha hG hNI hFI (ngSizes_of hSz hb0 le_rfl zero_le_two le_rfl) hIn
  rw [hdd] at r
  unfold PB.Terms.RowMain at r
  rw [scT_sc_genSet] at r
  exact r

end GlobalTheory.Core.One
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamUnit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def pet (vS : Vol S) (ψ ψ' : Form k n (GA D S → ℂ)) (P : Pair k n) : ℂ :=
  ∫ g in vS.𝓕, ψ P g * star (ψ' P g) ∂vS.μ

theorem rep_apply (β : Frame p S n) (g : GL n k) (f : GA D S → ℂ) (x : GA D S) :
    β.rep g f x = f (x * β.gl g) := rfl

theorem pet_const (vS : Vol S) (β : Frame p S n) {ψ ψ' : Form k n (GA D S → ℂ)} (hψ : ψ ∈ EqForm β.rep)
    (hψ' : ψ' ∈ EqForm β.rep) (hl : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ P (γ * g) = ψ P g)
    (hl' : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ' P (γ * g) = ψ' P g) (P Q : Pair k n) : pet vS ψ ψ' P = pet vS ψ ψ' Q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
  unfold pet
  rw [hψ g P, hψ' g P]
  simp only [rep_apply]
  exact (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund (fun x => ψ P x * star (ψ' P x))
    (fun γ hγ x => by simp only [hl P γ hγ, hl' P γ hγ]) (β.gl g)).symm

theorem sum_pet_FFStar (vS : Vol S) (hS : CoCpt S) (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (hχ : ∀ a, (starRingEnd ℂ) (χ a) = χ (-a))
    {φ ψ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P)) (hψ : ∀ P, IsContAut S (ψ P))
    (L : Submodule 𝒪[k] (n → k)) :
    ∑ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P = ∑ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ := by
  have hint : ∀ P₁ P, IntegrableOn (fun g => φ P₁ g * star (ψ P g)) vS.𝓕 vS.μ := fun P₁ P =>
    (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun g _ => φ P₁ g * star (ψ P g))
      (((hφ P₁).2.mul (hψ P).2.star).comp continuous_fst)
      (fun γ hγ g _ => by simp only [(hφ P₁).1 γ hγ, (hψ P).1 γ hγ])).1 ()
  have e1 : ∀ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P =
      ∑ P₁ ∈ withKer L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P hP
    rw [mem_withLat] at hP
    unfold pet
    rw [FFStar_apply, hP]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun P₁ _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P₁ _ => integral_const_mul _ _
  have e2 : ∀ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ =
      ∑ P ∈ withLat L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P₁ hP₁
    rw [mem_withKer] at hP₁
    unfold pet
    rw [FF_apply, hP₁]
    have : ∀ g, φ P₁ g * star ((∑ P ∈ withLat L, χ (cross q P₁ P) • ψ P) g) =
        ∑ P ∈ withLat L, χ (-cross q P₁ P) * (φ P₁ g * star (ψ P g)) := fun g => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, Finset.mul_sum, star_mul']
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [← hχ]
      change φ P₁ g * ((starRingEnd ℂ) (χ (cross q P₁ P)) * star (ψ P g)) = _
      ring
    simp only [this]
    rw [integral_finsetSum _ (fun P _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P _ => integral_const_mul _ _
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

end GlobalTheory.FinPl.RamUnit

namespace GlobalTheory.FinPl.RamUnit

theorem ramUnitary_holds : ∀ D : D7, GlobalTheory.FinPl.RamUnitary D := by
  intro D k _ _ _ _ p n _ _ q χ hχ ε S hS vS β P φ₀ φ₀' hφ₀ hφ₀'
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨φ', hφ', rfl⟩ := hφ₀'
  have hB := GlobalTheory.FinPl.ramBijective_holds D k p n q χ hχ (resChar χ hχ q) rfl ε S β P
  obtain ⟨hA, eA⟩ := hB.2.1 φ hφ
  obtain ⟨hA', eA'⟩ := hB.2.1 φ' hφ'
  rw [eA, eA']
  have hO : OperatorIdentities k n (GA D S → ℂ) q (resChar χ hχ q) :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ hχ n).1 (GA D S → ℂ)).2
  set X := FFStar q (resChar χ hχ q) φ with hX
  set X' := FFStar q (resChar χ hχ q) φ' with hX'
  have cX : ∀ Q, IsContAut S (X Q) := fun Q => by
    have := hA.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have cX' : ∀ Q, IsContAut S (X' Q) := fun Q => by
    have := hA'.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have eFF : FF q (resChar χ hχ q) X' = ((resCard k : ℂ) ^ Fintype.card n) • φ' := hO.FF_FFStar_ram φ' hφ'.2.1
  have c2 : ∀ Q, IsContAut S ((FF q (resChar χ hχ q) X') Q) := fun Q => by
    rw [eFF]
    exact ⟨fun γ hγ g => by simp only [Pi.smul_apply, smul_eq_mul, (hφ'.2.2 Q).1 γ hγ],
      continuous_const.mul (hφ'.2.2 Q).2⟩
  have hsum := sum_pet_FFStar vS hS q (resChar χ hχ q) (conj_resChar hχ q) hφ.2.2 cX' P.lat
  have k1 : ∀ Q ∈ withLat P.lat, pet vS X X' Q = pet vS X X' (ε • P) := fun Q _ =>
    pet_const vS β (FFStar_mem_EqForm q _ hφ.1) (FFStar_mem_EqForm q _ hφ'.1) (fun Q => (cX Q).1)
      (fun Q => (cX' Q).1) Q (ε • P)
  have k2 : ∀ Q ∈ withKer P.lat, pet vS φ (FF q (resChar χ hχ q) X') Q = pet vS φ (FF q (resChar χ hχ q) X') P :=
    fun Q _ => pet_const vS β hφ.1 (FF_mem_EqForm q _ (FFStar_mem_EqForm q _ hφ'.1)) (fun Q => (hφ.2.2 Q).1)
      (fun Q => (c2 Q).1) Q P
  have hcard : (withLat P.lat).card = (withKer P.lat).card := by
    classical
    have e : Red P.lat ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red P.lat) :=
      (Module.Free.chooseBasis 𝓀[k] (Red P.lat)).toDualEquiv
    have e' : {x : Red P.lat // x ≠ 0} ≃ {f : Module.Dual 𝓀[k] (Red P.lat) // f ≠ 0} :=
      e.toEquiv.subtypeEquiv (fun x => by simp)
    refine Finset.card_eq_of_equiv ?_
    exact (Equiv.subtypeEquivRight (fun P => mem_withLat)).trans
      ((latEquiv P.lat).symm.trans (e'.symm.trans ((kerEquiv P.lat q).trans
        (Equiv.subtypeEquivRight (fun P => mem_withKer.symm)))))
  rw [Finset.sum_congr rfl k1, Finset.sum_congr rfl k2, Finset.sum_const, Finset.sum_const,
    ← hcard] at hsum
  have hN : (withLat P.lat).card ≠ 0 := (Finset.card_pos.2 ⟨P, mem_withLat.2 rfl⟩).ne'
  have hpe : pet vS X X' (ε • P) = pet vS φ (FF q (resChar χ hχ q) X') P := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hsum
    exact smul_right_injective ℂ (Nat.cast_ne_zero.2 hN) hsum
  change pet vS X X' (ε • P) = _
  rw [hpe, eFF]
  unfold pet
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_pow, Complex.star_def, Complex.conj_natCast]
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

end GlobalTheory.FinPl.RamUnit
end
end

section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem famGen1 : CorankOneIsEquivalenceOnRow → FamGen1 := by
  intro hE D X Y u hT
  obtain ⟨hrefl0, hsym, htr⟩ := hE D X Y u u hT
  have hnz : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  have hG : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u).G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ cls1 Y u t :=
    fun t ht => ⟨ht, rfl, hrefl0 t (hnz t ht)⟩
  have hrow : ∀ t t' : TauC Y u u, t' ∈ cls1 Y u t → (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t :=
    fun t t' h => h.2.1
  have hsub : ∀ t ∈ (Y.tO u u).genSet, ∀ t' ∈ (Y.tO u u).genSet,
      (Y.tO u u).rowOf t = (Y.tO u u).rowOf t' → (Y.tO u u).s0 t t' = 1 →
      cls1 Y u t' ⊆ cls1 Y u t := by
    intro t ht t' ht' hr hs x hx
    obtain ⟨hxg, hxr, hxs⟩ := hx
    exact ⟨hxg, hxr.trans hr.symm, htr t (hnz t ht) t' (hnz t' ht') x (hnz x hxg) hr hxr.symm hs hxs⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      have hs := GlobalTheory.Core.OneCoset.corankOne_of_same_flagDoubleCoset D X Y u u t t' (hG t ht) hr hn
      have hs' := hsym t (hnz t ht) t' (hnz t' ht') hr hs
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs') (hsub t ht t' ht' hr hs)
  · intro t ht t' ht' he
    have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.Core.One
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.WittTwo

theorem wittIndex_lt_and_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D c j s hj hs
  refine ⟨?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hpar : ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (s.V.gram.map τ) (sigYD D.R j).1 (sigYD D.R j).2 := by
    intro τ
    have h := hs.sigOK τ
    rw [hs.sig τ] at h
    exact h
  obtain ⟨W, hW, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex (s.V : HSpace D.host.E)).1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) s.V τ (hpar τ) W (fun x hx y hy => by
    have := hW hy
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this x hx)
  have h3 := D.R.three_m_lt_t
  simp only [sigYD] at h1
  omega

end GlobalTheory.ChainOnto.WittTwo
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero : ∀ D : D7, MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  first | exact @GlobalTheory.ChainOnto.val_eq_zero_imp | exact GlobalTheory.ChainOnto.val_eq_zero_imp | (intros; apply GlobalTheory.ChainOnto.val_eq_zero_imp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_injective_placewise : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.ChainOnto.chainPar_inj | exact GlobalTheory.ChainOnto.chainPar_inj | (intros; apply GlobalTheory.ChainOnto.chainPar_inj <;> assumption)
end
