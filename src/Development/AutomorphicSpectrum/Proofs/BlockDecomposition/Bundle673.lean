module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle665
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.WeilBound.CoreStatements.ThetaDilations.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFrameLevelTriangular
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_rapid_decay_siegel_set : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ {c : ℝ}, 0 < c → ∀ (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) ((invPt V a ξ).map (finPart D))) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilCount.count_main | exact GlobalTheory.CompanionTheory.WeilCount.count_main | (intros; apply GlobalTheory.CompanionTheory.WeilCount.count_main <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

variable {D : D7}

theorem trM_actW_ratTup (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    trM (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((trM X).map (incA D)) := by
  ext i a
  rfl

def framesEquiv (V : HSp D) {r : ℕ} (T : Matrix (Fin r) (Fin r) D.host.E) :
    framesE D.sp.cm.sig V.gram T ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = T} where
  toFun X := ⟨trM X.1, (trM_mem_framesE_iff V X.1 T).1 X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (trM_mem_framesE_iff V _ T).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem glue : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  intro D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  have hν' : HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν := hν
  have h𝓕' : HeckeCharacterZeroLocus.SiegelWeilU.IsFDH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν 𝓕 := h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hcm (AF D.host.F)
  have := hB r V.rank
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have htr : Continuous (trM : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → Mx D V.rank r) :=
    continuous_pi fun i => continuous_pi fun a =>
      (show Continuous fun X : Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E => X a i from
        (continuous_apply i).comp (continuous_apply a))
  set S := framesE D.sp.cm.sig V.gram β.1 with hS
  set Φ : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => φ (trM X) with hΦdef
  have hΦ : Measurable Φ := (hcont.comp htr).measurable
  have hν0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have hinvtop : (ν 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hν0
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have habs' : ∫⁻ g in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν < ⊤ := by
    have e := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
    simp only [hL.descend_mk] at e
    rw [← e]
    exact habs
  have hle : ∀ g : GA D V, ∑' X : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram g⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) (X : Fin r → Fin V.rank → D.host.E)))‖ₑ ≤
      GlobalTheory.SiegelFormula.absTheta V φ g := fun g => by
    have hinj : Function.Injective fun X : S => trM (X : Fin r → Fin V.rank → D.host.E) :=
      fun X Y h => (framesEquiv V β.1).injective (Subtype.ext h)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V g ξ)‖ₑ))
    simp only [hΦdef, trM_actW_ratTup, GlobalTheory.SiegelFormula.invPt]
  have hint : Integrable Φ (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 S) := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S _ hΦ.enorm]
    exact ENNReal.mul_lt_top hinvtop.lt_top ((lintegral_mono hle).trans_lt habs')
  refine ⟨hint, ?_⟩
  rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_int D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S Φ hΦ hint]
  have hInv := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(Matrix.rank_mul_eq_right_of_isUnit_det _ _
        ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hth : ∀ g : GA D V, HeckeCharacterZeroLocus.SiegelWeilU.thetaS _ _ D.sp.cm.sig V.rank V.gram Φ S g =
      ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V g x.1) := fun g => by
    refine (tsum_congr fun X => ?_).trans ((framesEquiv V β.1).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V g x.1))
    exact congrArg φ (trM_actW_ratTup V g X.1)
  rw [IfrB, average_eq, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕,
    GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
  have e1 : ∀ g : GA D V, descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) (GlobalTheory.AutomorphicL2Unitary.mk (GQ V) g) =
      HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S g :=
    fun g => (hInv.descend_mk g).trans (hth g).symm
  simp only [e1]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Level

variable {D : D7} {r : ℕ}

def eFin (D : D7) : AF D.host.F := 1 - GlobalTheory.FinTranslate.eInf D

theorem eFin_mul (D : D7) (x : AF D.host.F) : eFin D * x = pairA D.host.F 0 (sndA D.host.F x) := by
  show ((1 : Ainf D.host.F × Af D.host.F) - (1, 0)) * (x : Ainf D.host.F × Af D.host.F) =
    ((0 : Ainf D.host.F), (x : Ainf D.host.F × Af D.host.F).2)
  refine Prod.ext ?_ ?_
  · show ((1 : Ainf D.host.F) - 1) * x.1 = 0
    rw [sub_self, zero_mul]
  · show ((1 : Af D.host.F) - 0) * x.2 = x.2
    rw [sub_zero, one_mul]

theorem finPart_eInf (D : D7) : finPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 0 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem infPart_eInf (D : D7) : infPart D (GlobalTheory.FinTranslate.eInf D • (1 : AE D)) = 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      (GlobalTheory.FinTranslate.eInf D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem rs_one {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    rs σ 1 = GlobalTheory.FinTranslate.eInf D • (1 : AE D) := by
  refine sub_eq_zero.mp (hσ.ext _ ?_ ?_)
  · rw [map_sub, finPart_eInf, sub_zero]
    exact hσ.fin _
  · intro τ
    rw [map_sub, map_sub, infPart_eInf, map_one]
    simp only [rs, hσ.comp]
    simp

theorem diff_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1).1 = eFin D • a.1.map (incA D) := by
  show GlobalTheory.MixModel.rat a.1 - rs σ 1 • a.1.map (incA D) = eFin D • a.1.map (incA D)
  rw [rs_one hσ, smul_one_smul, eFin, sub_smul, one_smul]
  rfl

def S (V : HSp D) (A : Mx D r r) (y : Mx D V.rank r) : AF D.host.F :=
  halfTr (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))

theorem halfTr_smul (c : AF D.host.F) (x : AE D) : halfTr (c • x) = c * halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_smul, smul_eq_mul]
  ring

theorem halfTr_nsmul (n : ℕ) (x : AE D) : halfTr (n • x) = n • halfTr x := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA]
  rw [map_nsmul]
  simp only [nsmul_eq_mul]
  ring

theorem halfTr_trace_nsmul (n : ℕ) (M B : Mx D r r) :
    halfTr (Matrix.trace (HMul.hMul (n • M) B : Mx D r r)) = n • halfTr (Matrix.trace (HMul.hMul M B : Mx D r r)) := by
  rw [Matrix.smul_mul, Matrix.trace_smul, halfTr_nsmul]

theorem pow_eq_one_of_compact {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    {C : Set (Af F)} (hC : IsCompact C) : ∃ N : ℕ, 0 < N ∧ ∀ c ∈ C, ψ (pairA F 0 c) ^ N = 1 := by
  obtain ⟨N1, hN1, hK⟩ := GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_mem_Oh_of_isCompact F C hC
  obtain ⟨N2, hN2, hU⟩ :=
    GlobalTheory.CompanionTheory.SW.Core.AfTop.exists_mul_Oh_subset F _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  refine ⟨N2 * N1, Nat.mul_pos hN2 hN1, fun c hc => ?_⟩
  have h1 : ψ (pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c))) = 1 := hU _ (hK c hc)
  have h2 : (N2 * N1) • pairA F 0 c = pairA F 0 ((N2 : Af F) * ((N1 : Af F) * c)) := by
    show (N2 * N1) • ((0 : Ainf F), c) = ((0 : Ainf F), (N2 : Af F) * ((N1 : Af F) * c))
    rw [Prod.smul_mk, smul_zero, ← mul_assoc, ← Nat.cast_mul, ← nsmul_eq_mul]
  rw [← AddChar.map_nsmul_eq_pow, h2, h1]

private theorem supp_lemma_5 {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (hφ : φ ∈ schwartzA θ m n) :
    ∃ K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsCompact K ∧
      ∀ y, φ y ≠ 0 → (fun i j => finPart D (y i j)) ∈ K := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨tsupport g, (show IsLocallyConstant g ∧ HasCompactSupport g from hg).2, fun y hy => subset_tsupport g ?_⟩
    exact right_ne_zero_of_mul hy
  | zero => exact ⟨∅, isCompact_empty, fun y hy => (hy rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨K1, hK1, h1⟩ := hx
    obtain ⟨K2, hK2, h2⟩ := hy
    refine ⟨K1 ∪ K2, hK1.union hK2, fun z hz => ?_⟩
    by_cases hxz : x z = 0
    · right
      apply h2
      simpa [hxz] using hz
    · left
      exact h1 z hxz
  | smul a x _ hx =>
    obtain ⟨K, hK, h⟩ := hx
    refine ⟨K, hK, fun y hy => h y ?_⟩
    intro h0
    apply hy
    simp [h0]

private theorem continuous_sigRf_lemma_7 : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig) := by
  let f : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[Af D.host.F] (Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig
      map_add' := map_add _
      map_smul' := fun c z => by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
        | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap f

private theorem trace_bc_lemma_8 (z : AE D) :
    sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) =
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero] <;> rfl
  | tmul a e =>
    have h1 : (a ⊗ₜ[D.host.F] e : AE D) = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : finPart D (a ⊗ₜ[D.host.F] e) = sndA D.host.F a • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [Formalism.L2.Theta.finPart]
    rw [h2, h1]
    simp only [map_smul, GlobalTheory.CompanionTheory.HermPoisson.trace_one_tmul', smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem level_pow {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (A : Mx D r r)
    {θ : InfFam D} {φ : Mx D V.rank r → ℂ} (hφ : φ ∈ schwartzA θ V.rank r) :
    ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (eFin D * S V A y) ^ N = 1 := by
  obtain ⟨K, hK, hKy⟩ := supp_lemma_5 hφ
  let Φ : (Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → Af D.host.F := fun w =>
    algebraMap D.host.F (Af D.host.F) (1 / 2) *
      Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
        (Matrix.trace (A.map (finPart D) *
          (((Matrix.of w).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
            ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of w))))
  have hΦ : Continuous Φ := by
    have hσc := continuous_sigRf_lemma_7 (D := D)
    have htr : Continuous (Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) := by fun_prop
    have hof : Continuous (fun w : Fin V.rank → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => Matrix.of w) :=
      continuous_id
    exact continuous_const.mul (htr.comp (Continuous.matrix_trace (continuous_const.matrix_mul
      ((hof.matrix_map hσc).matrix_transpose.matrix_mul (continuous_const.matrix_mul hof)))))
  have hS : ∀ y : Mx D V.rank r, sndA D.host.F (S V A y) = Φ (fun i j => finPart D (y i j)) := by
    intro y
    have hM : (HMul.hMul A (inner V y y) : Mx D r r).map (finPart D) =
        A.map (finPart D) * (((Matrix.of fun i j => finPart D (y i j)).map
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig))ᵀ *
          ((GlobalTheory.MixModel.gA V).map (finPart D) * Matrix.of fun i j => finPart D (y i j))) := by
      ext i j

      simp [Matrix.mul_apply, GlobalTheory.MixModel.adj, GlobalTheory.StdUnn.inner, map_sum, GlobalTheory.CompanionTheory.WSum.finPart_cA]
    have ht : ∀ M : Mx D r r, finPart D (Matrix.trace M) = Matrix.trace (M.map (finPart D)) := by
      intro M

      simp [Matrix.trace, map_sum]
    show sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul A (inner V y y) : Mx D r r))) = _
    rw [map_mul, AlgHom.commutes, trace_bc_lemma_8, ht, hM]
  obtain ⟨N, hN, hC⟩ := pow_eq_one_of_compact hψ (hK.image hΦ)
  refine ⟨N, hN, fun y hy => ?_⟩
  rw [eFin_mul, hS y]
  exact hC _ ⟨_, hKy y hy, rfl⟩

theorem level : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) (φ : Mx D V.rank r → ℂ), φ ∈ schwartzA θ V.rank r → ∃ N : ℕ, 0 < N ∧ ∀ y, φ y ≠ 0 → ψ (halfTr (Matrix.trace (HMul.hMul (N • ((GlobalTheory.CompanionTheory.HermPoisson.ofHermE a).1 - path hσ a 1)).1 (inner V y y) : Mx D r r))) = 1 := by
  intro D r V ψ hψ θ σ hσ a φ hφ
  obtain ⟨N, hN, hy⟩ := level_pow hψ V (a.1.map (incA D)) hφ
  refine ⟨N, hN, fun y hy0 => ?_⟩
  rw [AddSubgroup.coe_nsmul, diff_eq hσ a, halfTr_trace_nsmul, Matrix.smul_mul, Matrix.trace_smul, halfTr_smul,
    AddChar.map_nsmul_eq_pow]
  exact hy y hy0

end GlobalTheory.CompanionTheory.WSum.Level
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.archimedean_gram_fibre_measure_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ → ∀ ρ : ℕ → HermR (Ainf F) σ n → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets → (∀ k, Measurable (fun X => φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ)) ∧ Integrable (fun X => φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ)) (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) ∧ Filter.Tendsto (fun k => (∫ X, φ X * (ρ k (c - gramH hCM hJ (Ainf F) X) : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) / ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(minf c))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.avgInfN_tendsto | exact GlobalTheory.CompanionTheory.SiegelND.Coef.avgInfN_tendsto | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.avgInfN_tendsto <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology


theorem _root_.GlobalTheory.T.cone_frame_weight_ratio_bound : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c, ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | exact GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology


theorem _root_.GlobalTheory.T.unipotent_frame_level_triangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (s : Fin r) (m : GAd σ J), m ∈ unipRad σ J (pre X s) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (α β : FrameIx r), frameLev s α ≤ frameLev s β → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * (archMat σ J τ (projArch σ J w m) - 1) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem | exact GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology


theorem _root_.GlobalTheory.T.good_function_line_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | exact GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.good_lineDer <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology


theorem _root_.GlobalTheory.T.siegel_set_uniform_smooth_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (b : Fin m → ℝ → GAd σ J) (Ω₀ : Set (GAd σ J)) (C δ₁ : ℝ), (∀ i, IsRealLine σ J (b i)) ∧ IsCompact Ω₀ ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GAd σ J → ℂ, GlobalTheory.UAut.IsSm σ J ψ → ∀ (g u : GAd σ J) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseInf σ J u δ → ∀ c : Fin m → ℝ, (∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ c i) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ i, c i := by
  exact GlobalTheory.CompanionTheory.RapidDecay.Mean.mean_value
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov

theorem exists_sends_of_rat_mem_minPar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
    ∀ δ ∈ ratPts σ J, δ ∈ minPar σ J X → ∃ e : E, e ≠ 0 ∧ Sends σ J δ (e • Xᵀ 0) (Xᵀ 0) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW δ hδ hp
  have hF := pfrA hcm hJ hW
  have hinc : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a b h =>
    congrFun (ratV_injective (F := F) (n := 1) (a₁ := fun _ => a) (a₂ := fun _ => b) (funext fun _ => h)) 0
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin n) E,
      (matHom _ σ J δ).1 = (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (show (((show ↥(HR (AF F) σ J) from δ) : HR (AF F) σ J) :
      GL (Fin n) (AF F ⊗[F] E)) ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) from hδ)
    exact ⟨g, (congrArg Units.val hg).symm⟩
  set Bq : Matrix (Fin (r + 1)) (Fin (r + 1)) E := cT (σ : E →+* E) Y * J * ((g : Matrix (Fin n) (Fin n) E) * X) with hBq
  have hBm : Bm σ J X Y δ = Bq.map (inclR (F := F) (AF F)) := by
    unfold Bm coefM JR
    rw [hg, hBq, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
  obtain ⟨hbt, he⟩ := (mem_minPar_iff hF).1 hp
  rw [hBm] at hbt he
  have hgX : (g : Matrix (Fin n) (Fin n) E) * X = X * Bq := by
    apply Matrix.map_injective hinc
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, ← hg]
    exact he
  have hlow : ∀ k : Fin (r + 1), k ≠ 0 → Bq k 0 = 0 := fun k hk => by
    apply hinc
    have := hbt (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk)
    simpa using this
  have hcol : (g : Matrix (Fin n) (Fin n) E) *ᵥ Xᵀ 0 = Bq 0 0 • Xᵀ 0 := by
    funext i
    have h1 := congrFun (congrFun hgX i) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (r + 1))
      (fun k _ hk => by rw [hlow k hk, mul_zero]) (fun h => absurd (Finset.mem_univ _) h)] at h1
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h1
  have hx : Xᵀ 0 ≠ 0 := fun h0 => by
    have h1 := congrFun (congrFun hW.xy 0) 0
    rw [GlobalTheory.SiegelSet.gram_apply, h0, map_zero, LinearMap.zero_apply, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  have hb : Bq 0 0 ≠ 0 := fun h0 => hx (by
    rw [h0, zero_smul] at hcol
    have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v) hcol
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h2)
  refine ⟨(Bq 0 0)⁻¹, inv_ne_zero hb, ?_⟩
  have h3 : (g : Matrix (Fin n) (Fin n) E) *ᵥ ((Bq 0 0)⁻¹ • Xᵀ 0) = Xᵀ 0 := by
    rw [Matrix.mulVec_smul, hcol, smul_smul, inv_mul_cancel₀ hb, one_smul]
  unfold Sends
  rw [hg]
  funext i
  have h4 := RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) (g : Matrix (Fin n) (Fin n) E) ((Bq 0 0)⁻¹ • Xᵀ 0) i
  rw [h3] at h4
  exact h4.symm

end GlobalTheory.CompanionTheory.RedCov

end
end
