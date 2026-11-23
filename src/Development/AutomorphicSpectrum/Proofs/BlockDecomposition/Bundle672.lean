module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle013
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle625
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle660
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle663
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle664
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integrable_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n → Integrable φ μ := by
  first | exact @GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar | exact GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar | (intros; apply GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.cuspidal_multiplicity_product_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL (k := k)) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) → jhMult ρ.rep (prodIrr x hd) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | exact GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | (intros; apply GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.product_irreducible_finite_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), HasFiniteLength (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.ProdFL.main | exact GlobalTheory.CompanionTheory.ProdFL.main | (intros; apply GlobalTheory.CompanionTheory.ProdFL.main <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.product_langlands_subquotient_segments : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL (k := k)), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  first | exact @GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | (intros; apply GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.size_matrix_permutation_equivs_exist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (e : Fin c ≃ Fin l), (∀ a, y a = x (e a)) → ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)), (∀ i j, b.1 i j = if e j = i then (x i).1 else 0) → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | exact GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | (intros; apply GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

theorem properSpace_completion (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ProperSpace w.Completion := by
  have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hce := hi.isClosedEmbedding
  refine ⟨fun x r => ?_⟩
  have e : Metric.closedBall x r = NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹'
      Metric.closedBall (NumberField.InfinitePlace.Completion.extensionEmbedding w x) r := by
    ext y
    simp [Metric.mem_closedBall, hi.dist_eq]
  rw [e]
  exact hce.isCompact_preimage (isCompact_closedBall _ _)

theorem isCompact_boxF_one (F : Type) [Field F] [NumberField F] : IsCompact (boxF F 1) := by
  have h1 : IsCompact (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) := by
    haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion := fun w => properSpace_completion F w
    exact isCompact_univ_pi fun w => isCompact_closedBall 0 1
  have h2 := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have e : boxF F 1 = (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
    ext a
    simp only [boxF, Set.mem_setOf_eq]
    change _ ↔ (a.1 ∈ (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ∧
      a.2 ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    refine and_congr ⟨fun h => Set.mem_univ_pi.mpr fun w => ?_, fun h w => ?_⟩ Iff.rfl
    · simpa [Metric.mem_closedBall, dist_zero_right] using h w
    · simpa [Metric.mem_closedBall, dist_zero_right] using Set.mem_univ_pi.mp h w
  rw [e]
  exact h1.prod h2

theorem isCompact_boxE_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsCompact (boxE F E 1) := by
  set b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) with hb
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := inferInstance
  have hK : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank F E) => boxF F 1) :=
    isCompact_univ_pi fun _ => isCompact_boxF_one F
  have hc : Continuous
      ((b.equivFun.symm : (Fin (Module.finrank F E) → AF F) →ₗ[AF F] AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have e : boxE F E 1 = b.equivFun.symm '' (Set.univ.pi fun _ => boxF F 1) := by
    ext x
    simp only [boxE, Set.mem_setOf_eq, Set.mem_image, Set.mem_univ_pi, ← hb]
    constructor
    · intro hx
      exact ⟨b.equivFun x, fun k => by rw [Module.Basis.equivFun_apply]; exact hx k,
        b.equivFun.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩ k
      have h : b.repr (b.equivFun.symm y) k = y k := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [h]
      exact hy k
  rw [e]
  exact hK.image hc

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  intro F E _ _ _ _ _
  exact ⟨isCompact_boxF_one F, isCompact_boxE_one F E⟩

end GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem setLIntegral_eq_of_vanish {V : Type} [MeasurableSpace V] (μ : Measure V) {O : Set V}
    (hO : MeasurableSet O) (f : V → ℝ≥0∞) (hf : ∀ v, v ∉ O → f v = 0) :
    ∫⁻ v in O, f v ∂μ = ∫⁻ v, f v ∂μ := by
  rw [← lintegral_indicator hO]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ O
  · rw [indicator_of_mem hv]
  · rw [indicator_of_notMem hv, hf v hv]

theorem lintegral_chart_of_continuous {V Vx Va VY : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace Vx] [MeasurableSpace Va] [MeasurableSpace VY]
    (c : Vx → Va → VY → V) (hc : Measurable fun p : Vx × VY × Va => c p.1 p.2.2 p.2.1)
    (μ : Measure V) (μx : Measure Vx) (μY : Measure VY) (μa : Measure Va)
    [SFinite μx] [SFinite μY] [SFinite μa]
    (O cell : Set V) (Ox : Set Vx) (hO : MeasurableSet O) (hOx : MeasurableSet Ox)
    (hcell : IsOpen cell) (hcO : cell ⊆ O)
    (h1 : ∀ᵐ v ∂μ, v ∈ O → v ∈ cell)
    (h2 : ∀ᵐ y ∂μY, ∀ x ∈ Ox, ∀ a, c x a y ∈ cell)
    (h3 : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ cell → (∀ v, 0 ≤ φ v) →
      Integrable φ μ ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂μ =
        ∫⁻ x, ∫⁻ a, ∫⁻ y, ENNReal.ofReal (φ (c x a y)) ∂μY ∂μa ∂μx)
    (h4 : ∀ x a y, x ∉ Ox → c x a y ∉ O)
    (g : V → ℝ≥0∞) (hg : Measurable g) (hgO : ∀ v, v ∉ O → g v = 0) :
    ∫⁻ v, g v ∂μ = ∫⁻ x, ∫⁻ y, ∫⁻ a, g (c x a y) ∂μa ∂μY ∂μx := by
  let f : Vx × VY × Va → V := fun p => c p.1 p.2.2 p.2.1
  let ρ : Measure (Vx × VY × Va) := (μx.restrict Ox).prod (μY.prod μa)
  have hf : Measurable f := hc
  have key : ∀ G : V → ℝ≥0∞, Measurable G → (∀ v, v ∉ O → G v = 0) →
      ∫⁻ v, G v ∂(ρ.map f) = ∫⁻ x, ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY ∂μx := by
    intro G hG hG0
    have e : ∀ x, ∫⁻ q, G (f (x, q)) ∂(μY.prod μa) = ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY := fun x =>
      lintegral_prod (fun q => G (f (x, q))) ((hG.comp hf).comp measurable_prodMk_left).aemeasurable
    rw [lintegral_map hG hf]
    show ∫⁻ p, G (f p) ∂((μx.restrict Ox).prod (μY.prod μa)) = _
    rw [lintegral_prod (fun p => G (f p)) (hG.comp hf).aemeasurable]
    simp only [e]
    refine setLIntegral_eq_of_vanish μx hOx _ fun x hx => ?_
    have h0 : ∀ y a, G (c x a y) = 0 := fun y a => hG0 _ (h4 x a y hx)
    simp [h0]
  have hmeq : μ.restrict O = ρ.map f := by
    refine GlobalTheory.CompanionTheory.SW.FibreUniq.measure_eq_of_lintegral_eq _ _ cell hcell ?_ ?_ ?_
    · have h : ∀ᵐ v ∂(μ.restrict O), v ∈ cell := (ae_restrict_iff' hO).2 h1
      exact h
    · rw [Measure.map_apply hf hcell.measurableSet.compl]
      have a1 : ∀ᵐ p ∂ρ, p.1 ∈ Ox :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hOx)
      have a2 : ∀ᵐ q ∂(μY.prod μa), ∀ x ∈ Ox, ∀ a, c x a q.1 ∈ cell :=
        Measure.quasiMeasurePreserving_fst.ae h2
      have a3 : ∀ᵐ p ∂ρ, ∀ x ∈ Ox, ∀ a, c x a p.2.1 ∈ cell :=
        Measure.quasiMeasurePreserving_snd.ae a2
      have h : ∀ᵐ p ∂ρ, f p ∈ cell := by
        filter_upwards [a1, a3] with p h h' using h' _ h _
      exact h
    · intro φ hφ hs hsup h0
      obtain ⟨hi, hl⟩ := h3 φ hφ hs hsup h0
      have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
        ENNReal.measurable_ofReal.comp hφ.measurable
      have hv : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hv (hcO (hsup h)), ENNReal.ofReal_zero]
      refine ⟨hi.restrict, ?_⟩
      rw [key _ hm hv, setLIntegral_eq_of_vanish μ hO _ hv, hl]
      refine lintegral_congr fun x => ?_
      have hH : Measurable fun q : VY × Va => ENNReal.ofReal (φ (c x q.2 q.1)) :=
        (hm.comp hf).comp measurable_prodMk_left
      exact (lintegral_lintegral_swap hH.aemeasurable).symm
  rw [← key g hg hgO, ← hmeq, setLIntegral_eq_of_vanish μ hO g hgO]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem stages_zero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(m 0) = ∫⁻ x, ∫⁻ Y, ∫⁻ a, g (chartS R σ J x a 0 Y) ∂(coordW R b lam 1 n) ∂(m' 0) ∂(m₁ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam m m₁ m' hm hm₁ hm' g hg hg0
  obtain ⟨hOpen, hLI, hGr, hCh, hmeas⟩ := GlobalTheory.T.free_cell_open_independent F E σ hCM M J hJ R hR n
  have hOpen0 := (GlobalTheory.T.free_cell_open_independent F E σ hCM M J hJ R hR 0).1
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, -⟩ := hR'
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 (n + 1) (M + 2)
  haveI := t8 1 (M + 2)
  haveI := t8 1 n
  haveI := t8 n M
  haveI : SigmaFinite (m₁ 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM (hypOne J) R hR 1 _ _ m₁ hm₁ 0
  haveI : SigmaFinite (m' 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM J R hR n _ _ m' hm' 0
  haveI : (coordW R b lam 1 n).IsAddHaarMeasure :=
    (GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam).2.1 1 n
  have hOx : MeasurableSet {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} := by
    have e : {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} =
        freeCell (R ⊗[F] E) M 0 := by
      ext x
      exact ⟨fun h => ⟨h, linearIndependent_empty_type⟩, fun h => h.1⟩
    rw [e]
    exact hOpen0.measurableSet
  have hO : MeasurableSet {X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E | IsUnit (X 0 0)} := by
    have hp : Measurable fun (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) (_ : Fin 1) => X 0 :=
      Measurable.of_eval fun _ => measurable_pi_apply 0
    exact hp hOx
  have hc : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) ×
      (Fin 1 → Fin n → R ⊗[F] E) => chartS R σ J p.1 p.2.2 0 p.2.1 :=
    hmeas.comp (measurable_fst.prodMk ((measurable_snd.comp measurable_snd).prodMk
      (measurable_const.prodMk (measurable_fst.comp measurable_snd))))
  have c0 : ∀ᵐ X ∂(m 0), X ∈ (gramR R σ (hypOne J)) ⁻¹' {((0 : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm.1 0
  have c1 : ∀ᵐ Y ∂(m' 0), Y ∈ (gramR R σ J) ⁻¹' {((0 : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm'.1 0
  refine lintegral_chart_of_continuous (fun x a Y => chartS R σ J x a 0 Y) hc (m 0) (m₁ 0) (m' 0)
    (coordW R b lam 1 n) {X | IsUnit (X 0 0)} (freeCell (R ⊗[F] E) M n)
    {x | IsUnit (x 0 0)} hO hOx hOpen (fun X hX => hX.1) ?_ ?_ ?_ ?_ g hg hg0
  · filter_upwards [c0] with X hX hu
    exact hGr X hX.2 hX.1 hu
  · filter_upwards [c1] with Y hY x hx a
    exact hCh x a 0 Y hx hY.2
  · intro φ hφ hs hsup h0
    exact ⟨(hm.2.2 φ hφ hs (hsup.trans fun X hX => hLI X hX)).1 0 (mem_univ _),
      GlobalTheory.T.hyperbolic_fibre_free_extension F E σ hCM M J hJ R hR n d b lam hlam m m₁ m' hm hm₁ hm' φ hφ hs hsup h0⟩
  · intro x a Y hx h
    exact hx (by simpa [chartS] using h)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

theorem _root_.GlobalTheory.T.open_cell_function_compact_support_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ f ∈ openFns d hd ρ, ∃ L : Subgroup (GL (Fin N) k), L ≤ unipU k d hd ∧ IsCompact (L : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L) ∧ ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | exact GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support | (intros; apply GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.test_function_continuous_compact_support : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → Continuous (tst U β) ∧ HasCompactSupport (tst U β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst | exact GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.continuous_hasCompactSupport_tst <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.local_volume_rank_one_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  first | exact @GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero | exact GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero | (intros; apply GlobalTheory.CompanionTheory.SW.AvgZero.avg_zero <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.FoldF.foldF | exact GlobalTheory.CompanionTheory.SW.StageF.FoldF.foldF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.FoldF.foldF <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
theorem _root_.GlobalTheory.T.highest_weight_integral_of_unitary : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → Antitone ν → ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧ (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧ ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  exact @GlobalTheory.CompanionTheory.RealCountG.Isotypic.exists_isotypic_projection
end
