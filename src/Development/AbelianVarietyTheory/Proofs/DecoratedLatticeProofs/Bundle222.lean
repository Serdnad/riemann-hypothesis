module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Corev.EmbAGfC

variable {D : D7}

abbrev finfR (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GfC_iff' (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finfR D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand' {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfR D) = 1) :
    (x ⬝ m ⬝ y).map (finfR D) = (x ⬝ y).map (finfR D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfR D) = x.map (finfR D) ⬝ m.map (finfR D) ⬝ y.map (finfR D) := by
    rw [Matrix.map_mul (f := finfR D), Matrix.map_mul (f := finfR D)]
  have e2 : (x ⬝ y).map (finfR D) = x.map (finfR D) ⬝ y.map (finfR D) := Matrix.map_mul (f := finfR D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GfC' {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff'] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfR D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem wittCoreEmbedding_mem_finiteAdelicUnitaryGroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff'] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finfR D)), Matrix.map_add _ (map_add (finfR D)), map_sand' _ _ _ hg,
    ← Matrix.map_add _ (map_add (finfR D)), ← Matrix.map_add _ (map_add (finfR D)), d.sum_eq_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem embA_mem_GfC_fin : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (κ : GA D A), κ ∈ GfC A → embA d o κ ∈ GfC S := by
  intro D S S₀ A L ρ d o κ hκ
  rw [embA_apply]
  exact wittCoreEmbedding_mem_finiteAdelicUnitaryGroup d (orth_emb_mem_GfC' o hκ)

end GlobalTheory.Corev.EmbAGfC
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CommInt

theorem om_integral_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (m : Measure U) [SFinite m] (F : U → WO S T → ℂ) (p : GA D S × GA D T) (β : U → ℝ), (∀ u, IsThetaFunO ψ S T (F u)) → Continuous (Function.uncurry F) → Continuous (fun q : U × WO S T => om p (F q.1) q.2) → Integrable β m → (∀ u w, ‖F u w‖ ≤ β u ∧ ‖om p (F u) w‖ ≤ β u) → IsThetaFunO ψ S T (fun w => ∫ u, F u w ∂m) → ∀ w, om p (fun w' => ∫ u, F u w' ∂m) w = ∫ u, om p (F u) w ∂m := by
  intro D ψ S T χS χT om hom U _ _ _ _ m _ F p β hF hFc hOc hβ hdom hG w
  have hψ := hom.std
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.Size.exists_isCovolOne S T
  haveI hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  set G : WO S T → ℂ := fun w => ∫ u, F u w ∂m with hGdef
  set H : WO S T → ℂ := fun w => ∫ u, om p (F u) w ∂m with hHdef
  have hHc : Continuous H := by
    refine continuous_of_dominated (bound := β) (fun x => ?_) (fun x => ?_) hβ ?_
    · exact (hOc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => (hdom u x).2
    · exact Filter.Eventually.of_forall fun u => hOc.comp (continuous_const.prodMk continuous_id)
  have hHb : ∀ x, ‖H x‖ ≤ ∫ u, β u ∂m := fun x =>
    norm_integral_le_of_norm_le hβ (Filter.Eventually.of_forall fun u => (hdom u x).2)
  have hOG := hom.om_pres p _ hG
  set q : WO S T → ℂ := fun x => om p G x - H x with hqdef
  have hq : q = 0 := by
    refine GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions D ψ hψ S T μ 𝓕 hμ h𝓕 q (hOG.cont.sub hHc) ?_ ?_
    · intro γ x
      have e1 := hOG.quasi γ x
      have e2 : H (ratW T S γ + x) = ψ (-(symplOH S T (ratW T S γ) x)) * H x := by
        simp only [hHdef]
        rw [← integral_const_mul]
        congr 1
        funext u
        exact (hom.om_pres p _ (hF u)).quasi γ x
      simp only [hqdef]
      rw [e1, e2]
      ring
    · intro f hf

      haveI : SecondCountableTopology (WO S T) := i3
      obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hOG
      have hf0 := hom.om_pres p⁻¹ f hf
      have hff0 : om p (om p⁻¹ f) = f := by
        change (om p * om p⁻¹) f = f
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      set f0 := om p⁻¹ f with hf0def
      obtain ⟨C0, hC0⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf0
      obtain ⟨Cf, hCf⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf
      have hint : ∀ (g h : WO S T → ℂ) (a b : ℝ), Continuous g → Continuous h → (∀ x, ‖g x‖ ≤ a) →
          (∀ x, ‖h x‖ ≤ b) → Integrable (fun x => g x * star (h x)) (μ.restrict 𝓕) := by
        intro g h a b hg hh ha hb
        refine Integrable.mono' (integrable_const (a * b)) (hg.mul hh.star).aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))
      have hprod : ∀ (K : U → WO S T → ℂ) (h : WO S T → ℂ) (b : ℝ), Continuous (fun z : U × WO S T => K z.1 z.2) →
          (∀ u x, ‖K u x‖ ≤ β u) → Continuous h → (∀ x, ‖h x‖ ≤ b) →
          Integrable (Function.uncurry fun x u => K u x * star (h x)) ((μ.restrict 𝓕).prod m) := by
        intro K h b hK hKb hh hb
        refine Integrable.mono' (((integrable_const b).mul_prod hβ)) ?_ (ae_of_all _ fun z => ?_)
        · exact ((hK.comp (continuous_snd.prodMk continuous_fst)).mul (hh.comp continuous_fst).star).aestronglyMeasurable
        · show ‖K z.2 z.1 * star (h z.1)‖ ≤ b * β z.2
          rw [norm_mul, norm_star, mul_comm b]
          exact mul_le_mul (hKb z.2 z.1) (hb z.1) (norm_nonneg _) ((norm_nonneg _).trans (hKb z.2 z.1))
      have hsc := fun g g' (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') =>
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om p) (hom.om_pres p) (hom.om_unit μ 𝓕 hμ h𝓕 p) g g' hg hg'
      have A : ∫ x in 𝓕, om p G x * star (f x) ∂μ = ∫ x in 𝓕, G x * star (f0 x) ∂μ := by
        rw [← hff0]; exact hsc G f0 hG hf0
      have B : ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
        calc ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, ∫ u, F u x * star (f0 x) ∂m ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show (∫ u, F u x ∂m) * star (f0 x) = ∫ u, F u x * star (f0 x) ∂m
              rw [integral_mul_const]
          _ = ∫ u, ∫ x in 𝓕, F u x * star (f0 x) ∂μ ∂m :=
              integral_integral_swap (hprod F f0 C0 hFc (fun u x => (hdom u x).1) hf0.cont hC0)
          _ = ∫ u, ∫ x in 𝓕, om p (F u) x * star (f x) ∂μ ∂m := by
              refine integral_congr_ae (ae_of_all _ fun u => ?_)
              rw [← hff0]; exact (hsc (F u) f0 (hF u) hf0).symm
          _ = ∫ x in 𝓕, ∫ u, om p (F u) x * star (f x) ∂m ∂μ :=
              (integral_integral_swap (hprod (fun u => om p (F u)) f Cf hOc (fun u x => (hdom u x).2) hf.cont hCf)).symm
          _ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show ∫ u, om p (F u) x * star (f x) ∂m = (∫ u, om p (F u) x ∂m) * star (f x)
              rw [integral_mul_const]
      have i1 := hint (om p G) f CG Cf hOG.cont hf.cont hCG hCf
      have i2 := hint H f (∫ u, β u ∂m) Cf hHc hf.cont hHb hCf
      simp only [hqdef, sub_mul]
      rw [integral_sub i1 i2, A, B, sub_self]
  have := congrFun hq w
  simp only [hqdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.CommInt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CommIntBdd

theorem om_integral_comm_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (m : Measure U) [SFinite m] (F : U → WO S T → ℂ) (p : GA D S × GA D T) (β : U → ℝ), (∀ u, IsThetaFunO ψ S T (F u)) → Continuous (Function.uncurry F) → Continuous (fun q : U × WO S T => om p (F q.1) q.2) → Integrable β m → (∀ u w, ‖F u w‖ ≤ β u ∧ ‖om p (F u) w‖ ≤ β u) → IsThetaFunO ψ S T (fun w => ∫ u, F u w ∂m) → ∀ w, om p (fun w' => ∫ u, F u w' ∂m) w = ∫ u, om p (F u) w ∂m := by
  intro D ψ S T χS χT om hom U _ _ _ _ m _ F p β hF hFc hOc hβ hdom hG w
  have hψ := hom.std
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.Size.exists_isCovolOne S T
  haveI hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  set G : WO S T → ℂ := fun w => ∫ u, F u w ∂m with hGdef
  set H : WO S T → ℂ := fun w => ∫ u, om p (F u) w ∂m with hHdef
  have hHc : Continuous H := by
    refine continuous_of_dominated (bound := β) (fun x => ?_) (fun x => ?_) hβ ?_
    · exact (hOc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => (hdom u x).2
    · exact Filter.Eventually.of_forall fun u => hOc.comp (continuous_const.prodMk continuous_id)
  have hHb : ∀ x, ‖H x‖ ≤ ∫ u, β u ∂m := fun x =>
    norm_integral_le_of_norm_le hβ (Filter.Eventually.of_forall fun u => (hdom u x).2)
  have hOG := hom.om_pres p _ hG
  set q : WO S T → ℂ := fun x => om p G x - H x with hqdef
  have hq : q = 0 := by
    refine GlobalTheory.T.eq_zero_of_orthogonal_all_thetaFunctions D ψ hψ S T μ 𝓕 hμ h𝓕 q (hOG.cont.sub hHc) ?_ ?_
    · intro γ x
      have e1 := hOG.quasi γ x
      have e2 : H (ratW T S γ + x) = ψ (-(symplOH S T (ratW T S γ) x)) * H x := by
        simp only [hHdef]
        rw [← integral_const_mul]
        congr 1
        funext u
        exact (hom.om_pres p _ (hF u)).quasi γ x
      simp only [hqdef]
      rw [e1, e2]
      ring
    · intro f hf

      haveI : SecondCountableTopology (WO S T) := i3
      obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hOG
      have hf0 := hom.om_pres p⁻¹ f hf
      have hff0 : om p (om p⁻¹ f) = f := by
        change (om p * om p⁻¹) f = f
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      set f0 := om p⁻¹ f with hf0def
      obtain ⟨C0, hC0⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf0
      obtain ⟨Cf, hCf⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf
      have hint : ∀ (g h : WO S T → ℂ) (a b : ℝ), Continuous g → Continuous h → (∀ x, ‖g x‖ ≤ a) →
          (∀ x, ‖h x‖ ≤ b) → Integrable (fun x => g x * star (h x)) (μ.restrict 𝓕) := by
        intro g h a b hg hh ha hb
        refine Integrable.mono' (integrable_const (a * b)) (hg.mul hh.star).aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))
      have hprod : ∀ (K : U → WO S T → ℂ) (h : WO S T → ℂ) (b : ℝ), Continuous (fun z : U × WO S T => K z.1 z.2) →
          (∀ u x, ‖K u x‖ ≤ β u) → Continuous h → (∀ x, ‖h x‖ ≤ b) →
          Integrable (Function.uncurry fun x u => K u x * star (h x)) ((μ.restrict 𝓕).prod m) := by
        intro K h b hK hKb hh hb
        refine Integrable.mono' (((integrable_const b).mul_prod hβ)) ?_ (ae_of_all _ fun z => ?_)
        · exact ((hK.comp (continuous_snd.prodMk continuous_fst)).mul (hh.comp continuous_fst).star).aestronglyMeasurable
        · show ‖K z.2 z.1 * star (h z.1)‖ ≤ b * β z.2
          rw [norm_mul, norm_star, mul_comm b]
          exact mul_le_mul (hKb z.2 z.1) (hb z.1) (norm_nonneg _) ((norm_nonneg _).trans (hKb z.2 z.1))
      have hsc := fun g g' (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') =>
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om p) (hom.om_pres p) (hom.om_unit μ 𝓕 hμ h𝓕 p) g g' hg hg'
      have A : ∫ x in 𝓕, om p G x * star (f x) ∂μ = ∫ x in 𝓕, G x * star (f0 x) ∂μ := by
        rw [← hff0]; exact hsc G f0 hG hf0
      have B : ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
        calc ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, ∫ u, F u x * star (f0 x) ∂m ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show (∫ u, F u x ∂m) * star (f0 x) = ∫ u, F u x * star (f0 x) ∂m
              rw [integral_mul_const]
          _ = ∫ u, ∫ x in 𝓕, F u x * star (f0 x) ∂μ ∂m :=
              integral_integral_swap (hprod F f0 C0 hFc (fun u x => (hdom u x).1) hf0.cont hC0)
          _ = ∫ u, ∫ x in 𝓕, om p (F u) x * star (f x) ∂μ ∂m := by
              refine integral_congr_ae (ae_of_all _ fun u => ?_)
              rw [← hff0]; exact (hsc (F u) f0 (hF u) hf0).symm
          _ = ∫ x in 𝓕, ∫ u, om p (F u) x * star (f x) ∂m ∂μ :=
              (integral_integral_swap (hprod (fun u => om p (F u)) f Cf hOc (fun u x => (hdom u x).2) hf.cont hCf)).symm
          _ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show ∫ u, om p (F u) x * star (f x) ∂m = (∫ u, om p (F u) x ∂m) * star (f x)
              rw [integral_mul_const]
      have i1 := hint (om p G) f CG Cf hOG.cont hf.cont hCG hCf
      have i2 := hint H f (∫ u, β u ∂m) Cf hHc hf.cont hHb hCf
      simp only [hqdef, sub_mul]
      rw [integral_sub i1 i2, A, B, sub_self]
  have := congrFun hq w
  simp only [hqdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem om_integral_comm_bdd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Ω : Type) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] (m : Measure Ω) [IsFiniteMeasure m] (F : Ω → WO S T → ℂ) (p : GA D S × GA D T), (∀ a, IsThetaFunO ψ S T (F a)) → (Continuous fun q : Ω × WO S T => F q.1 q.2) → (∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C) → (Continuous fun q : Ω × WO S T => om p (F q.1) q.2) → (∃ C : ℝ, ∀ a x, ‖om p (F a) x‖ ≤ C) → IsThetaFunO ψ S T (fun x => ∫ a, F a x ∂m) → ∀ x, om p (fun y => ∫ a, F a y ∂m) x = ∫ a, om p (F a) x ∂m := by
  intro D ψ S T χS χT om hom Ω _ _ _ _ m _ F p hF hFc hFb hOc hOb hG x
  obtain ⟨C1, hC1⟩ := hFb
  obtain ⟨C2, hC2⟩ := hOb
  exact om_integral_comm_dom D ψ S T χS χT om hom Ω m F p (fun _ => max C1 C2) hF hFc hOc
    (integrable_const _) (fun a w => ⟨(hC1 a w).trans (le_max_left _ _), (hC2 a w).trans (le_max_right _ _)⟩) hG x

end GlobalTheory.CommIntBdd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisLineComb

open GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem actO_actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  rw [inv_inv]
  calc HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) x) (mt S g))) (mt S g⁻¹)
      = HMul.hMul (HMul.hMul (HMul.hMul (mt T h) (mt T h⁻¹)) x) (HMul.hMul (mt S g) (mt S g⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = x := by rw [← GlobalTheory.WeilVacMove.mt_mul, ← GlobalTheory.WeilVacMove.mt_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem dLine_apply {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_eq_sum (hψ : IsStdChar D ψ (-1)) {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (h : Chart θ σ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (RW T S)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i))
    (hN0 : ∀ i t, (N i t).map (finPart D) = 0) (hN1 : ∀ i, piW θ T S (N i 1) = b i) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ i, ((b.coord i (piW θ T S (L 1)) : ℝ) : ℂ) • dLine ψ S T (N i) f := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  funext w
  let A : RW T S →+ ℂ := AddMonoidHom.mk' (fun v => lam (symplOH S T w (iotaW σ T S v))) fun u v => by
    rw [map_add (f := _), symplOH_add_right, map_add (f := _)]
  have hA : Continuous A := hl.comp (continuous_symplOH S T continuous_const (h.continuous_iota T S))
  let A' : RW T S →L[ℝ] ℂ := A.toRealLinearMap hA
  let B : RW T S →L[ℝ] ℂ := fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0
  let Φ : RW T S →ₗ[ℝ] ℂ := (LinearMap.mulRight ℝ (f w)).comp A'.toLinearMap + B.toLinearMap
  have key : ∀ (K : ℝ →+ WO S T), Continuous K → (∀ t, (K t).map (finPart D) = 0) →
      dLine ψ S T K f w = Φ (piW θ T S (K 1)) := by
    intro K hK hK0
    rw [dLine_apply h hl hlam hK hK0 hf]
    have e1 : K 1 = iotaW σ T S (piW θ T S (K 1)) := by
      have := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 K ⟨hK, hK0⟩ 1
      rwa [one_smul] at this
    have e2 : lam (symplOH S T w (K 1)) = A (piW θ T S (K 1)) := by
      show _ = lam (symplOH S T w (iotaW σ T S (piW θ T S (K 1))))
      rw [← e1]
    show lam (symplOH S T w (K 1)) * f w + _ = _
    rw [e2]
    rfl
  rw [Finset.sum_apply, key L hL hL0]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [fun i => key (N i) (hN i) (hN0 i), hN1]
  conv_lhs => rw [← b.sum_repr (piW θ T S (L 1))]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, Module.Basis.coord_apply]

theorem dLine_om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  intro D ψ S T χS χT om hW M hM hM0
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let b := Module.finBasis ℝ (RW T S)
  let N : Fin (Module.finrank ℝ (RW T S)) → ℝ →+ WO S T := fun i =>
    (iotaW σ T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).toLinearMap.toAddMonoidHom
  have hN : ∀ i, Continuous (N i) := fun i =>
    (h.continuous_iota T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).continuous
  have hN0 : ∀ i t, (N i t).map (finPart D) = 0 := fun i t => h.real_iota T S _
  have hN1 : ∀ i, piW θ T S (N i 1) = b i := fun i => by
    show piW θ T S (iotaW σ T S ((1 : ℝ) • b i)) = b i
    rw [h.pi_iota, one_smul]
  let Mp : GA D S × GA D T → ℝ →+ WO S T := fun p =>
    AddMonoidHom.mk' (fun s => actO S T p.1⁻¹ p.2⁻¹ (M s)) fun s t => by rw [map_add (f := _), actO_add]
  have hMp : ∀ p, Continuous (Mp p) := fun p =>
    (continuous_const.matrix_mul hM).matrix_mul continuous_const
  have hMp0 : ∀ p t, (Mp p t).map (finPart D) = 0 := fun p t => by
    show (actO S T p.1⁻¹ p.2⁻¹ (M t)).map (finPart D) = 0
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hM0 t, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨_, N, fun i p => ((b.coord i (piW θ T S (Mp p 1)) : ℝ) : ℂ), hN, hN0, fun i => ?_, fun p f hf => ?_⟩
  · have hc : Continuous fun p : GA D S × GA D T => actO S T p.1⁻¹ p.2⁻¹ (M 1) := by
      unfold actO
      exact (((GlobalTheory.MixModel.continuous_mt T).comp (continuous_snd.inv)).matrix_mul continuous_const).matrix_mul
        ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst.inv.inv)
    exact Complex.continuous_ofReal.comp ((LinearMap.continuous_of_finiteDimensional (b.coord i)).comp
      ((continuous_pi' hθ T S).comp hc))
  · obtain ⟨g, k⟩ := p
    have e := om_dLine hW g k (hMp (g, k)) (hMp0 (g, k)) hM hM0 (fun t => (actO_actO_inv g k (M t)).symm) hf

    rw [← e, dLine_eq_sum hψ h b (hMp (g, k)) (hMp0 (g, k)) N hN hN0 hN1 hf, map_sum]
    simp only [map_smul]

end GlobalTheory.HeisLineComb

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesUnimod

theorem besGrp_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
    (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ A L ρ d o μ hμ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨ν, 𝓝, hν⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  obtain ⟨hνH, h𝓝, h𝓝1⟩ := hν
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  let μA : Measure (GA D A) := Measure.haar
  have hHaar := ((GlobalTheory.MixPer.jacGrp_besGrp_haar D V V₀ A L ρ d o ν 𝓝 ⟨hνH, h𝓝, h𝓝1⟩).2.2 μA inferInstance)
  haveI : LocallyCompactSpace (flagN d) := hNc.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  haveI : Countable (NFlagQ V d.e) := hinj.countable
  haveI : ν.IsMulRightInvariant :=
    GlobalTheory.SemiHaar.rightInv_of_fd (NFlagQ V d.e) ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  haveI : μA.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A μA inferInstance
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d n hn (o.emb (h, 1))
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) (embA d o) hNc hcA hnA μA ν
  haveI : LocallyCompactSpace (besGrp d o) := by
    obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) (embA d o) hnA hcA (GlobalTheory.BesProj.exists_continuous_proj D V V₀ A L ρ d o)
    exact e.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (besGrp d o) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨κ, k1, k2⟩ : ∃ κ : Measure (besGrp d o), κ.IsHaarMeasure ∧ κ.IsMulRightInvariant := ⟨_, hHaar, hR⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ κ]
  infer_instance

end GlobalTheory.BesUnimod
end
end
