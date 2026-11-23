module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle053
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle504
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle097
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle096
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle089
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle083
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle098
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle467
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle691
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle692
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle698
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle075
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle077
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage4
theorem stage4_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  intro P hHL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O hT hG hM hRow hLv hPos
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := _root_.ResidueKilled.sec_of_dm P.q9
  obtain ⟨hOk, hGU, hGE, hBlk, hA, _hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  obtain ⟨hLT, hLTB, _hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  obtain ⟨hLevW, hPartsW, hHecke, hSep, _hTr⟩ := _root_.GlobalTheory.T.pLevW_and_trISep_of_liftTest_pos P R F hT hM hG.unif hLT hLv hPos
  have hOnto := _root_.GlobalTheory.T.partial_L_function_of_hypotheses_alt P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hHL (s := 1) R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hOk.2 hGE hG.unif
  obtain ⟨fw, hBar⟩ := hG.fw
  have hGal : (R.toCx3 F).GalD F.cr false :=
    _root_.GlobalTheory.T.twisted_scalar_conjugation_invariance hE P.q1 P.q2 P.q13 P.q11 P.q9 P.q14 P.q10 P.q7 P.q4 T R F κ v₀ O 1 hT.ok hSep hT.char hT.ex hT.params
      hT.phs hT.std fw hBar hG.ioExt hG.pins (fun i => (hG.oneMap i).1) hG.phase hOk.1 hOk.2 hHecke hGU hGE hBlk hRow hLT hLTB
      hOnto hPos.1 hPos.2 hG.unif hLevW hA hPartsW
  exact ⟨hGal, GlobalTheory.T.liftScalar_pos_allPlaces_of_conjugateIdentity R F hT.ok hT.char hT.ex hPos hGal hG.unif hLTB hGE⟩
end GlobalTheory.Stage4
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

theorem _root_.GlobalTheory.T.real_data_weight_vector_family_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false ∧ R.PPos := by
  first | exact @_root_.GlobalTheory.Stage4.stage4_alt | exact _root_.GlobalTheory.Stage4.stage4_alt | (intros; apply _root_.GlobalTheory.Stage4.stage4_alt <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
namespace GlobalTheory.RowClaim.JetsAssembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {T : Type}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
theorem twisted_jet_one_of_all : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun ch => JetsOne ch := _root_.GlobalTheory.T.twisted_pairing_identity
theorem twistedJet_succ_eq_assembly : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → StepJets := by
  intro hP hS
  obtain ⟨C0, H⟩ := _root_.GlobalTheory.RowClaim.JetsAssembly.twisted_jet_one_of_all hP hS
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  exact ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j =>
    jetsAt_of_one ch s.core.lev (H D large₂ e hx Γ Pl0 T A Ks R F s ch i j)⟩
end GlobalTheory.RowClaim.JetsAssembly
end
end

section
open GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.twisted_jets_assemble : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → StepJets := by
  first | exact @_root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly | exact _root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly | (intros; apply _root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ConstRatio
theorem bottom_triple_integral_factorization (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : LNe) :
    GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  obtain ⟨c, h⟩ := _root_.GlobalTheory.T.bottom_triple_integral_factorization_of_real hPr hK hM
  obtain ⟨c', h'⟩ := _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero hPr hK hM hL
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hLc G W hW i j A A' WW X hX => ?_⟩
  obtain ⟨Pi, p, p', J, hs, hJ, hlam, hI'⟩ :=
    h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hLc G W hW i j A A' WW X hX
  have hnv := h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hLc G W i j A A' WW X hX
  obtain ⟨P', g', hg'⟩ := (hnv μ).2
  have hP' : p' P' ≠ 0 := fun h0 => hg' (by rw [hI' μ P', h0]; simp)
  choose lam hlam using hlam
  have key : ∀ t, lam t ≠ 0 ∧ Function.Injective (J t) := fun t => by
    obtain ⟨P, g, hPg⟩ := (hnv t).1
    rw [hlam t P] at hPg
    refine ⟨fun h0 => hPg (by simp [h0]), (hJ t).resolve_left fun h0 => hPg (by simp [h0])⟩
  refine ⟨lam, fun t => (key t).1, Pi, p, p', J, hs, fun t => (key t).2, fun t P g => (hX.integrable t).1 P g,
    fun t P => hlam t P, fun t P' _ => hI' t P', P', hP', fun t g => (hX.integrable t).2 P' g⟩
end GlobalTheory.ConstRatio
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  first | exact @_root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization | exact _root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization | (intros; apply _root_.GlobalTheory.ConstRatio.bottom_triple_integral_factorization <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
variable {D : D7}
section Lin
variable {ψ : AddChar (AF D.host.F) ℂ} {T₀ : HSp D}
end Lin
variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
variable (W : G.Weil) (M : Vol G) (t : T)
variable {W M t}
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun GlobalTheory.RowUnf GlobalTheory.RowVal
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
theorem twisted_iterate_eventually_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch := by
  intro hP hL
  obtain ⟨c0, h0⟩ := Big.and (_root_.GlobalTheory.T.flipRun_cusp_transition hL hP) (Big.and (_root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList hP) GlobalTheory.RowClaim.colFn_cont_left)
  refine ⟨c0, fun ε CF hC => ?_⟩
  obtain ⟨x0, hx⟩ := h0 ε CF hC
  refine ⟨x0, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R Fc hS ch hch hsc => ?_⟩
  obtain ⟨hstep, htop, hcol⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R Fc hS ch hch hsc
  choose ρ hρ hρ' using exists_rowMeas ch.G
  choose v hv using exists_vol_row ch.G
  refine ⟨ρ, fun j => (v j).μ, fun j hj => ⟨hρ j (mem_idx hj).2, (v j).haar⟩, ?_⟩
  intro t a τ hτ M hM P y
  obtain ⟨e, he, φm, hw, -⟩ := hτ
  have hu : GlobalTheory.Unf.IsContAut _ (colFn ch a) := ⟨(hcol a).2, (hcol a).1⟩
  have core : ∀ d ∈ τ.support,
      BplusConv ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) ∧
      NIter ρ (fun j => (v j).μ) (fun h => per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h) d.1 P.1 (colFn ch a) (formTop ch t y))
        (idx D) 1 (Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y))) := by
    intro d hd
    have h2 := hw d hd
    obtain ⟨-, h1, h3⟩ := pure_core hP.cuspRapidDecay hch.vol hM (hstep t M hM) he (φm d) d h2.1 h2.2 P (htop t y) hu
    refine ⟨GlobalTheory.RowBplus.bplusConv_col ch.W ch.M hch.vol ch.ξ (ch.col a) (col_mem ch a) _ h1.1.toIsAutFun, ?_⟩
    exact nIter_meas_congr ρ _ _ _ (fun j hj => hv j (mem_idx hj).1 (mem_idx hj).2.le t M hM)
      (nIter_conAt_of_colPer ch.G ch.W t hM (fockD ch.W t d.2 P.2) _ _ _ h3 ρ (fun j => (hρ' j t M hM).1)
        fun j => (hρ' j t M hM).2)
  have e1 : liftT ch.W M (oppPath t D.R.m) (oppTens ch.W t (Finsupp.single P 1) τ) (formTop ch t y) =
      ∑ d ∈ τ.support, τ d • liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y) := by
    rw [GlobalTheory.RowVal.liftT_oppTens, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
      one_smul]
  have e2 : lhs ch t M (Finsupp.single P 1) τ a y = ∑ d ∈ τ.support,
      τ d * Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) := by
    rw [lhs, e1, (bplus_sum_right ch.W ch.M (colFn ch a) τ.support _
      fun d hd => (bplus_smul_right ch.W ch.M (τ d) (core d hd).1).1).2]
    exact Finset.sum_congr rfl fun d hd => (bplus_smul_right ch.W ch.M _ (core d hd).1).2
  rw [e2]
  exact (niter_lin_congr _ _ _ ρ _ (idx D) 1).1 _ τ.support τ _ _ fun d hd => (core d hd).2
theorem twisted_iterate_eq_linear : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch ∧ LinAt ch :=
  fun hP hL => Big.and (_root_.GlobalTheory.RowChain.twisted_iterate_eventually_large hP hL) (_root_.GlobalTheory.RowVal.placeValuation_linAt_large hP hL)
end GlobalTheory.RowChain
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twisted_iterate_chain : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch ∧ LinAt ch := by
  first | exact @_root_.GlobalTheory.RowChain.twisted_iterate_eq_linear | exact _root_.GlobalTheory.RowChain.twisted_iterate_eq_linear | (intros; apply _root_.GlobalTheory.RowChain.twisted_iterate_eq_linear <;> assumption)
end
end
