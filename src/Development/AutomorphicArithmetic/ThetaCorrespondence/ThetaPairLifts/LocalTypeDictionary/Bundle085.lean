module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle082
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle079
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle080
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle083
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageSmallBig
theorem smallStage_thetaIntegral_of_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (_root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q0 A A' WW X hX _ => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, -, -, hD⟩ := hd W i j p q0 A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨P0, hP0⟩ := _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  have key : ∀ t, (∀ h, IntegrableOn (X.ker' W.ψ W.θ t P0 h) X.fd' X.m') ∧ X.I' W.ψ W.θ t P0 ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, hk'⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p q0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    haveI : Nontrivial Pr := nontrivial_left e
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P1, rfl⟩ := hq' x
    obtain ⟨hint, hker⟩ := hP0 _ _ hTr hInf _ _ _ _ _ _ _ hm _ hf'
    have hint' := hint X.m' X.fd' hIs.meas'
    have hne : pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) ≠ 0 := fun h0 => by
      have h1 := hker h0 P1
      rw [hr' _ hf'] at h1
      exact e.map_ne_zero_iff.2 (tmul_ne_zero hx hy) h1
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    refine ⟨fun h => ?_, ?_⟩
    · have h1 := hint' h
      simp only [hk'] at h1
      exact h1
    · rw [← eI']
      exact _root_.GlobalTheory.ConvThetaNe.convergent_theta_integral_ne_zero hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hTr X.m' X.fd' hIs.meas'
        _ _ _ _ _ _ _ hm _ (Submodule.subset_span ⟨_, P0, hf', rfl⟩) hint' hne
  exact ⟨P0, fun t => (key t).1, fun t => (key t).2⟩
end GlobalTheory.StageSmallBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smallStage_thetaIntegral_large_rank_case : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | exact _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | (intros; apply _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KerFin
theorem bottomTheta_kernel_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  intro hPr hTI hLM hInp hBS
  refine gbig_comb (_root_.GlobalTheory.T.theta_parameters_match hPr hTI hLM hInp hBS) GlobalTheory.BotWeights.weights_const ?_
  intro D T Lc sc G μ₀ C x b q2 q3 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨r, rc, κ, hr, hrc, hκ, H2⟩ := q2 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨n₀, H3⟩ := q3 i j δ t0
  obtain ⟨Ω, hΩ, H1⟩ := GlobalTheory.T.bottomTriple_thetaKernel_minors_eq_const_conjJet G W hW i j A A' WW X hX r rc hr hrc n₀
  refine ⟨Ω * starRingEnd ℂ κ, mul_ne_zero hΩ ((map_ne_zero _).2 hκ), fun s Q P P' hB => ?_⟩
  obtain ⟨u, hu0, huQ, huU, hEq⟩ := H2 s Q P P' hB
  refine ⟨u, hu0, huQ, huU, fun ea ed h g x y hg hy Tu => ?_⟩
  have hne : κ * starRingEnd ℂ u ≠ 0 := mul_ne_zero hκ ((map_ne_zero _).2 hu0)
  rw [H1 P.a P.d P.n ea ed (H3 s Q P P' hB) s g y hg.1 hy.1 Tu, hEq ea ed h g x y hg hy,
    GlobalTheory.FunObj.NormUniq.applyAt0_smul _ hne]
  simp only [GlobalTheory.NormSum.Pair.term, map_mul, Complex.conj_conj]
  ring
end GlobalTheory.KerFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottomTheta_kernel_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  first | exact @_root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | exact _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | (intros; apply _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite <;> assumption)
end
end
