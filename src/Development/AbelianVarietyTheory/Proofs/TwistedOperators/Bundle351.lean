module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle087
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle331
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open scoped ENNReal
open GlobalTheory.WeilAdm.HaarSplit

private theorem opensMeasurableSpace_pi_mixedSpace (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := by
  haveI : SecondCountableTopology (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  infer_instance

theorem exists_haar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hg0 : g 0 ≠ 0) :
    ∃ μA : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μA ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μA = c * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  classical
  haveI := opensMeasurableSpace_pi_mixedSpace F κ
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → FiniteAdeleRing (𝓞 F) F), ν = Measure.addHaar := ⟨_, rfl⟩
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : SFinite ν := by rw [hν]; infer_instance
  haveI : SFinite μ := inferInstance
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := inferInstance
  let h : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ₜ (κ → AdeleRing (𝓞 F) F) :=
    { toEquiv := (splitE F κ).toEquiv
      continuous_toFun := continuous_splitE F κ
      continuous_invFun := continuous_splitE_symm F κ }
  let m := h.toMeasurableEquiv
  have hm : (m : _ → _) = splitE F κ := rfl
  have hgc : Continuous g := hg.1.continuous
  refine ⟨(μ.prod ν).map m, ?_, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ?_, ?_, ?_⟩
  · rw [hm]
    exact AddEquiv.isAddHaarMeasure_map (μ.prod ν) (splitE F κ) (continuous_splitE F κ) (continuous_splitE_symm F κ)
  · apply ne_of_gt
    have hU : IsOpen {y | g y = g 0} := hg.1.isOpen_fiber _
    have hpos : 0 < ν {y | g y = g 0} := hU.measure_pos ν ⟨0, rfl⟩
    calc (0 : ℝ≥0∞) < ‖g 0‖ₑ ^ 2 * ν {y | g y = g 0} :=
          ENNReal.mul_pos (pow_ne_zero _ (enorm_ne_zero.2 hg0)) hpos.ne'
      _ = ∫⁻ y, {y | g y = g 0}.indicator (fun _ => ‖g 0‖ₑ ^ 2) y ∂ν :=
          (lintegral_indicator_const hU.measurableSet _).symm
      _ ≤ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y => ?_
          by_cases hy : g y = g 0
          · simp [Set.indicator, hy]
          · simp [Set.indicator, hy]
  · have hs : HasCompactSupport fun y => ‖g y‖ ^ 2 := hg.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hint : Integrable (fun y => ‖g y‖ ^ 2) ν := (hgc.norm.pow 2).integrable_of_hasCompactSupport hs
    have h2 := hint.2
    unfold HasFiniteIntegral at h2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
    refine lintegral_congr fun y => ?_
    rw [enorm_pow, enorm_norm]
  · intro f
    rw [lintegral_map_equiv, hm]
    have hpt : ∀ p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F),
        ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [hpt]
    rw [mul_comm]
    exact lintegral_prod_mul (μ := μ) (ν := ν) (f := fun z => ‖f z‖ₑ ^ 2) (g := fun y => ‖g y‖ₑ ^ 2)
      (f.continuous.measurable.enorm.pow_const 2).aemeasurable (hgc.measurable.enorm.pow_const 2).aemeasurable

theorem integral_sq_eq {V : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] (μ : Measure V)
    {f : V → ℂ} (hf : Continuous f) : ∫ x, ‖f x‖ ^ 2 ∂μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  have hc : Continuous fun x => ‖f x‖ ^ 2 := hf.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => by positivity) hc.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem opensMeasurable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := opensMeasurableSpace_pi_mixedSpace F κ

theorem snd_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
      (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
  simpa using h2

theorem integral_norm_sq_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (μ : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ _ T hAct μ hμ t f
  classical
  haveI := hμ
  haveI := opensMeasurable F (Fin a × Fin (a + a'))
  set g : (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.SchANonzero.intPts F (Fin a × Fin (a + a'))).indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB _ := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _
  have h0mem : (0 : Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F _ := by
    intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  have hg0 : g 0 ≠ 0 := by
    rw [hgdef, Set.indicator_of_mem h0mem]
    simp
  obtain ⟨μA, hμA, c, hc0, hctop, hc⟩ := exists_haar F (Fin a × Fin (a + a')) μ g hgSB hg0
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).unit
  let r : (Fin a × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have htens : ∀ φ : SInf F (Fin a × Fin (a + a')), tens (evI F) (φ : _ → ℂ) r = GlobalTheory.WeilM.pureA F φ g :=
    fun φ => rfl
  have hRest : Rest (evI F) (f : _ → ℂ) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero hz i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hA := hAct t f r hRest
  rw [htens, htens] at hA
  have hmem : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) :=
    Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hu := hU μA hμA (1, γ (Multiplicative.ofAdd t)) _ hmem
  rw [hA, hc, hc] at hu
  have hl := (ENNReal.mul_right_inj hc0 hctop).1 hu
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, hl]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.PolMatchConst

def finProd {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)

theorem match_of_polMatch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → Φ' ∈ G.M'.So B.ψ B.τ₁ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hT Φ Φ' hP hSo
  have hP0 := hP
  obtain ⟨T, hXT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', _⟩ := hP
  have hstd : ∀ (κ : Type) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      (∀ v ∉ T, ψ v = vac v) →
      ∀ᶠ v in Filter.cofinite, ψ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    intro κ ψ vac hvac hψ
    filter_upwards [hvac, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [hψ v hvT, hv]
  have hg : ∀ i, finProd (φ i) ∈ GlobalTheory.WeilM.SB _ := fun i =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2)⟩
  have hg' : ∀ j, finProd (φ' j) ∈ GlobalTheory.WeilM.SB _ := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2)⟩
  have e : Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (finProd (φ i)) := hΦ
  have e' : Φ' = ∑ j, GlobalTheory.WeilM.pureA F (f' j) (finProd (φ' j)) := hΦ'
  refine ⟨hSo, m, m', fun i => finProd (φ i), f, fun _ => f, fun j => finProd (φ' j), f', fun _ => f',
    fun i => ⟨hg i, tendsto_const_nhds⟩, fun j => ⟨hg' j, tendsto_const_nhds⟩, e, e', fun _ => ?_⟩
  rw [← e, ← e']
  exact ⟨hSo, hP0⟩

end GlobalTheory.SquareAgree.PolMatchConst
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU

noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDer

theorem schwartz_diffQuotient_eval_mul_eq_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (s : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (y : κ → mixedEmbedding.mixedSpace F) (R : ℂ) (t : ℝ) :
    (t⁻¹ • (s t - s 0)) y * R = slope (fun t => s t y * R) 0 t := by
  simp only [slope_def_module, sub_zero, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_mul_assoc, sub_mul]

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {m : ℕ}
    (Φ : Fin m → (Fin n × Fin d → AF F) → ℂ) (hΦ : ∀ i, Φ i ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, Φ i)) = ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (Φ i)) := by
  have hsum : M.co.rho ψ u (∑ i, Φ i) = ∑ i, M.co.rho ψ u (Φ i) := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]
  have hmem : ∀ i, M.co.rho ψ u (Φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i => GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u (Φ i) (hΦ i)
  rw [hsum]
  have key := map_sum (GlobalTheory.WeilM.thetaLin F (Fin n × Fin d))
    (fun i => (⟨M.co.rho ψ u (Φ i), hmem i⟩ : GlobalTheory.WeilM.schA F (Fin n × Fin d))) Finset.univ
  simpa only [GlobalTheory.WeilM.thetaLin_apply, Submodule.coe_sum] using key

end GlobalTheory.ThetaLineDer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.SBCount

open TopologicalSpace Cardinal

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {K : Set X | IsCompact K ∧ IsOpen K}.Countable := by
  classical
  have hB := isBasis_countableBasis X
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  refine (Set.countable_range fun t : Finset (countableBasis X) => ⋃ b ∈ t, (b : Set X)).mono ?_
  rintro K ⟨hKc, hKo⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun b : {b : countableBasis X // (b : Set X) ⊆ K} => (b.1 : Set X))
    (fun b => hB.isOpen b.1.2) (fun x hx => by
      obtain ⟨b, hbB, hxb, hbK⟩ := hB.exists_subset_of_mem_open hx hKo
      exact Set.mem_iUnion.2 ⟨⟨⟨b, hbB⟩, hbK⟩, hxb⟩)
  refine ⟨t.image (fun c => c.1), ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hb
    exact c.2 hxb
  · intro x hx
    have := ht hx
    rw [Set.mem_iUnion₂] at this
    obtain ⟨c, hc, hxc⟩ := this
    rw [Set.mem_iUnion₂]
    exact ⟨c.1, Finset.mem_image.2 ⟨c, hc, rfl⟩, hxc⟩

theorem finite_range_of_sb {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : (Set.range f).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun w => f ⁻¹' {w}) (fun w => hf _)
    fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩
  refine (t.finite_toSet.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : f x = 0
  · exact Or.inl hx
  · simpa using Or.inr (by simpa using ht (subset_tsupport f hx))

theorem sb_le_span (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun K : Set X => K.indicator (1 : X → ℂ)) '' {K : Set X | IsCompact K ∧ IsOpen K}) := by
  classical
  rintro f ⟨hf, hcs⟩
  have hfin := finite_range_of_sb hf hcs
  have hsum : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : f x = 0
    · rw [hx]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
      have : x ∉ f ⁻¹' {c} := by simp [hx, Ne.symm hc0]
      simp [Set.indicator_of_notMem this]
    · rw [Finset.sum_eq_single (f x)]
      · simp
      · intro c _ hcx
        have : x ∉ f ⁻¹' {c} := by simp [Ne.symm hcx]
        simp [Set.indicator_of_notMem this]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨hx, by simp⟩) h
  rw [hsum]
  refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {c}, ⟨?_, hf _⟩, rfl⟩)
  have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
  refine hcs.isCompact.of_isClosed_subset (hf.isClosed_fiber c) fun x hx => subset_tsupport f ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [Function.mem_support, hx, hc0]

theorem rank_sb_le_aleph0 (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (sb_le_span X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compactOpen X).image _).to_subtype

theorem rank_sb_localField_le : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (κ : Type) [Fintype κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  intro F _ _ v κ _
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI := GlobalTheory.LocAtTopology.secondCountable_localField (Fv F v)
  exact rank_sb_le_aleph0 _

end GlobalTheory.SBCount
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree


open scoped Classical in
theorem GlobalTheory.HeisLineDeriv.exists_actsD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      ∃ g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ :=
  fun M ψ hψ g u hu => by
    obtain ⟨D, hD⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
    exact ⟨D g, hD g⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.LineGroup

theorem archOp_oneParam : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    (∀ (s t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin a × Fin (a + a')), T 0 f = f := by
  intro F E _ _ _ _ _ σ a a' B G X om om' _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin a × Fin (a + a'))
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show ((1 : UA σ G.V.J), γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)) =
        ((1 : UA σ G.V.J), γ (Multiplicative.ofAdd s)) * (1, γ (Multiplicative.ofAdd t)) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

end GlobalTheory.LineGroup
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.complementaryAdelicSchwartz_archimedean_replace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  first | exact @GlobalTheory.TwistRest.restTr | exact GlobalTheory.TwistRest.restTr | (intros; apply GlobalTheory.TwistRest.restTr <;> assumption)
end
