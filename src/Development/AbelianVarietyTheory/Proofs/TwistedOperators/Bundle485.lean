module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle448
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle449
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThLiftCusp

theorem isCuspFun_of_approx {D : D7} (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (N : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ ψ : GA D V → ℂ, Continuous ψ ∧ (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧
      ∀ g, ‖ψ g - f g‖ ≤ ε * GlobalTheory.Grow.height V g ^ N) : IsCuspFun V f := by
  choose ψ hψ using fun n : ℕ => h (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  refine GlobalTheory.CuspLimit.isCuspFun_of_tendsto D V N ψ f (fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1⟩) hf hl ?_
  have hb : ∀ n : ℕ, GlobalTheory.Size.growthSize V N (ψ n - f) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    (GlobalTheory.Size.growthSize_le_iff Nat.one_div_pos_of_nat.le).2 fun g => by simpa using (hψ n).2.2.2 g
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
  simpa using (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)

end GlobalTheory.ThLiftCusp

namespace GlobalTheory.ThLiftCusp

theorem norm_lift_sub_le {X H : Type} [MeasurableSpace X] (μ : Measure X) (K K' : H → X → ℂ) (φ φ' : X → ℂ)
    (u : H → ℝ) (w : X → ℝ) (C e δ : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e) (hu : ∀ h, 0 ≤ u h)
    (hK : ∀ h x, ‖K h x‖ ≤ C * u h * w x) (hKK : ∀ h x, ‖K' h x - K h x‖ ≤ e * u h * w x)
    (h1 : Integrable (fun x => w x * ‖φ x‖) μ) (h2 : Integrable (fun x => w x * ‖φ' x - φ x‖) μ)
    (hδ : ∫ x, w x * ‖φ' x - φ x‖ ∂μ ≤ δ)
    (hA : ∀ h, Integrable (fun x => K' h x * φ' x) μ) (hB : ∀ h, Integrable (fun x => K h x * φ x) μ) (h : H) :
    ‖∫ x, K' h x * φ' x ∂μ - ∫ x, K h x * φ x ∂μ‖ ≤ u h * (e * ∫ x, w x * ‖φ x‖ ∂μ + (e + C) * δ) := by
  rw [← integral_sub (hA h) (hB h)]
  have hpt : ∀ x, ‖K' h x * φ' x - K h x * φ x‖ ≤
      u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖)) := fun x => by
    have e1 : K' h x * φ' x - K h x * φ x =
        (K' h x - K h x) * φ x + (K' h x - K h x) * (φ' x - φ x) + K h x * (φ' x - φ x) := by ring
    rw [e1]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ x))
    have a2 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ' x - φ x))
    have a3 := mul_le_mul_of_nonneg_right (hK h x) (norm_nonneg (φ' x - φ x))
    nlinarith
  have hint : Integrable (fun x => u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖))) μ :=
    ((h1.const_mul e).add (h2.const_mul (e + C))).const_mul (u h)
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add (h1.const_mul e) (h2.const_mul (e + C)), integral_const_mul,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (hu h)

end GlobalTheory.ThLiftCusp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Size

variable {D : D7}

theorem thetaKO_le_unif {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    {K : Set (GA D W)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h f‖ ≤ C * GlobalTheory.Grow.height V g ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact W hK
  have hs : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal := mul_nonneg hC0 ENNReal.toReal_nonneg
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A, A, mul_nonneg hs (pow_nonneg (by positivity) _),
    fun h hh g => ?_⟩
  have h1 := (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h
  have hW : GlobalTheory.Grow.height W h ≤ max B 1 := (hB h hh).trans (le_max_left _ _)
  have hW0 : 0 ≤ GlobalTheory.Grow.height W h := (GlobalTheory.Grow.height_pos W h).le
  have hV0 : 0 ≤ GlobalTheory.Grow.height V g := (GlobalTheory.Grow.height_pos V g).le
  calc ‖thetaKO ω g h f‖ = ‖ω (g, h) f 0‖ := rfl
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A := h1
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * max B 1) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hV0 hW0)
          (mul_le_mul_of_nonneg_left hW hV0) _) hs
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A * GlobalTheory.Grow.height V g ^ A := by ring

theorem thetaKO_le_quotHeight {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε S) T Φ) {K : Set (GA D T)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.quotHeight S g ^ A := by
  have e : ∀ g h, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((GlobalTheory.Grid.ofSgn ε S).symm g) h Φ := fun g h => by
    show ω (g, h) Φ 0 = ω (GlobalTheory.Grid.ofSgn ε S ((GlobalTheory.Grid.ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  obtain ⟨C, A, hC0, hC⟩ := thetaKO_le_unif hθ hω hΦ hK
  have hC' : ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.height S g ^ A := fun h hh g => by
    simp only [e]
    exact hC h hh _
  exact ⟨C * 2 ^ A, A, by positivity, fun h hh g => GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) (hC' h hh) g⟩

end GlobalTheory.DownApprox
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowConv

theorem thetaKO_toSgn {D : D7} {S T : HSp D} (om : GlobalTheory.Grid.WRep S T) (h : GA D S) (g : GA D T) (f : WO S T → ℂ) :
    thetaKO om h g f = thetaKO (om.toSgn true) ((GlobalTheory.Grid.ofSgn true S).symm h) g f := by
  unfold thetaKO GlobalTheory.Grid.WRep.toSgn
  simp

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    ∀ γ ∈ GQ T, ∀ g, thetaKO om h (γ * g) f = thetaKO om h g f := fun γ hγ g => by
  have e : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) _ hγ _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    Continuous fun g => thetaKO om h g f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_right h)

theorem conj_thetaKO_modGrowth_snd (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) (h : GA D S) :
    GlobalTheory.Grow.ModGrowth T fun g => conj (thetaKO om h g f) := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ S T χS χT om hω f hf
  refine ⟨C * GlobalTheory.Grow.height S h ^ A, A, fun g => ?_⟩
  rw [RCLike.norm_conj, mul_assoc, ← mul_pow]
  exact hC h g

theorem conj_thetaKO_mul_integrableOn (hP : GlobalTheory.Published.CuspRapidDecay)
    {θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Ainf ↥D.host.F) D.host.E →+* ℂ} (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D T)} {𝓕 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ)
    (hc : IsCuspFun T φ) (h : GA D S) :
    IntegrableOn (fun g => conj (thetaKO om h g f) * φ g) 𝓕 ν :=
  (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc).integrableOn_modGrowth_mul hν h𝓕
    (conj_thetaKO_modGrowth_snd hω hf h)
    (fun γ hγ g => by simp only [thetaKO_left_snd hω hf h γ hγ g])
    ((Complex.continuous_conj.comp (thetaKO_continuous_snd hω hf h)).measurable.aestronglyMeasurable)

end GlobalTheory.UpArrowConv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a := by
  first | exact @GlobalTheory.HtWitt.quotHeight_witt | exact GlobalTheory.HtWitt.quotHeight_witt | (intros; apply GlobalTheory.HtWitt.quotHeight_witt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open scoped ContDiff ComplexOrder

namespace GlobalTheory.ColLiftAut

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}

theorem isThetaFunO_smul (hΦ : IsThetaFunO ψ S T Φ) (c : ℂ) : IsThetaFunO ψ S T (c • Φ) := by
  refine ⟨fun γ w => ?_, ?_, continuous_const.mul hΦ.cont, fun k L hL hf w => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hΦ.quasi γ w]; ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu' => ?_⟩
    funext w
    have := congrFun (h u hu hu') w
    simp only [heisO, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]; ring
  · exact contDiff_const.mul (hΦ.smooth k L hL hf w)

theorem kernel_left (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ) (g : GA D S) {γ : GA D T}
    (hγ : γ ∈ GQ T) (h : GA D T) : thetaKO om g (γ * h) Φ = thetaKO om g h Φ := by
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hΦ)

theorem kernel_right (g : GA D S) (h k : GA D T) : thetaKO om g (h * k) Φ = thetaKO om g h (om (1, k) Φ) := by
  have e : ((g, h * k) : GA D S × GA D T) = (g, h) * (1, k) := by simp
  unfold thetaKO
  rw [e, map_mul, Module.End.mul_apply]

theorem lift_continuous (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    Continuous fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  have := GlobalTheory.ThetaIntegralCont.continuous_theta_integral_vector ψ S T χS χT om hW hS ν 𝓕 hν h𝓕 ℂ
    (LinearMap.toSpanSingleton ℂ _ Φ) (fun x => isThetaFunO_smul hΦ x) φ hφ.cont hφ.left
  refine this.congr fun h => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [LinearMap.toSpanSingleton_apply, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end GlobalTheory.ColLiftAut

namespace GlobalTheory.ColLiftAut

theorem posDef_of_nodeIs {D : D7} {N : GlobalTheory.Grid.Node D} {ν q : ℕ} {Sp : D.what₂.Tau → SPar} (h : N.Is ν q Sp) (hq : q = 0) :
    ∀ τ, (gramAt D N.V τ).PosDef := fun τ =>
  GlobalTheory.RepsObj.gramAt_posDef (fun σ => by rw [h.sig σ, h.rank, hq]; simp) h.sigOK τ

end GlobalTheory.ColLiftAut
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpCuspApprox

theorem val_aut_cusp {D : D7} {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {F : N.Maps} (hF : F ∈ N.Cusp θ)
    (v : SmT N.M) : IsAutFunSm θ N.V (F v) ∧ IsCuspFun N.V (F v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 _).1 ((Formalism.IndefR.Mult.mem_multT θ N.M ∅ 1 F).1 hF)
  have e : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [e]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul c (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

end GlobalTheory.UpCuspApprox

namespace GlobalTheory.UpCuspApprox

end GlobalTheory.UpCuspApprox
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnFormApprox

variable {D : D7}

theorem autSm_cusp_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFunSm θ N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hz : IsAutFunSm θ N.V (0 : GA D N.V → ℂ) := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ N.V
  have hU' : ∀ w, IsAutFunSm θ N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨hx.aut w, hx.cusp w⟩
    | zero => exact fun w => ⟨hz, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1.toIsAutFun (hy w).1.toIsAutFun (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hx w).1, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hU' f).1, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem autSm_cusp_sum {V : HSp D} {θ : InfFam D} (K : Finset ℕ) (u : ℕ → GA D V → ℂ)
    (hu : ∀ k ∈ K, IsAutFunSm θ V (u k) ∧ IsCuspFun V (u k)) :
    IsAutFunSm θ V (∑ k ∈ K, u k) ∧ IsCuspFun V (∑ k ∈ K, u k) := by
  induction K using Finset.induction_on with
  | empty =>
    have h0 : IsCuspFun V (0 : GA D V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
    rw [Finset.sum_empty]
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, h0⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hA := hu a (Finset.mem_insert_self a s)
    have hB := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hA.1 hB.1, GlobalTheory.MultMem.isCuspFun_add hA.1.toIsAutFun hB.1.toIsAutFun hA.2 hB.2⟩

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section
namespace GlobalTheory.FrameScale

theorem vecMul_entry {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (x : k) (q r : Fin c) (m : ι)
    (hb : ∀ i, b i m = x * φ (a i r)) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = x * φ ((Formalism.UG.cT σ a * g * a) q r) := by

  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, hb, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
  map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameScale
end

theorem GlobalTheory.FrameScale.clauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m)
  (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
  (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : k) (e : ℕ), ϖ ≠ 0 → Function.Injective j →
  (∀ r i, β.b i (j r) = ϖ ^ (e * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) →
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) →
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1)) •
      (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (j ⟨q.1, by omega⟩) 1) ∧
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (2 * σ + 1 - q.1)) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) *
      (if q.1 = σ then -1 else 1))⁻¹ • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
      Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1) := by
  intro D _ T L _ _ sc G W _ _ F hF σ h' k _ _ _ _ p β j ϖ e hϖ hj hb hout
  have hne : (-D.host.xi0) ≠ 0 := neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hc : p.pr (incA D (-D.host.xi0)) ≠ 0 := ((hne.isUnit.map (incA D)).map p.pr).ne_zero
  have hc' : p.pr (incA D (star (-D.host.xi0))) ≠ 0 :=
    (((star_ne_zero.2 hne).isUnit.map (incA D)).map p.pr).ne_zero
  have hcol : ∀ (q : Fin (σ + 1)) i, xFB F σ h' i q = incA D ((-D.host.xi0) ^ (q.1 + 1)) * incA D ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩) := by
    intro q i
    have := congrFun (GlobalTheory.CharXFB.xFB_col F hF σ h' q) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    rfl
  have key : ∀ m, β.b' *ᵥ (fun i => β.b i m) = Pi.single m 1 := by
    intro m
    have : (fun i => β.b i m) = β.b *ᵥ Pi.single m 1 := by
      funext i; simp [Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have hv : (fun i => p.pr (xFB F σ h' i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * (ϖ ^ (e * (q.1 + 1)))⁻¹) • fun i => β.b i (j ⟨q.1, by omega⟩) := by
      funext i
      rw [hcol]
      simp only [map_mul, map_pow, Pi.smul_apply, smul_eq_mul, hb]
      field_simp
    rw [hv, Matrix.mulVec_smul, key, smul_smul]
    convert one_smul k _
    rw [inv_pow]
    field_simp
  · have hv : (fun i => p.pr (cA D (xFB F σ h' i q))) = p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) •
        fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩))) := by
      funext i
      rw [hcol]
      simp only [map_mul, GlobalTheory.DualPairCheck.cA_incA, star_pow, map_pow, Pi.smul_apply, smul_eq_mul]
    have hsm : ∀ (x : k) (u : Fin (G.V (.grid (2 * σ + 2) 0)).rank → k)
        (M : Matrix (Fin (G.V (.grid (2 * σ + 2) 0)).rank) (Fin (G.V (.grid (2 * σ + 2) 0)).rank) k),
        (x • u) ᵥ* M = x • (u ᵥ* M) := by
      intro x u M
      funext m
      simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hg := (G.colDec (2 * σ + 2) (by omega) h').gram
    have hw : ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩)))) ᵥ*
        (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
        (ϖ ^ (e * (2 * σ + 1 - q.1)) * (if q.1 = σ then -1 else 1)) • Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1 := by
      funext m
      by_cases hm : m ∈ Set.range j
      · obtain ⟨r, rfl⟩ := hm
        refine (GlobalTheory.FrameScale.vecMul_entry (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * σ + 2) (by omega) h').a _ β.b _ ⟨q.1, by omega⟩ r (j r) (hb r)).trans ?_
        rw [hg]
        simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, RingHom.coe_comp, Function.comp_apply]
        by_cases hr : r = ⟨2 * σ - q.1, by omega⟩
        · subst hr
          have e1 : 2 * σ - q.1 + 1 = 2 * σ + 1 - q.1 := by omega
          rw [Pi.single_eq_same, if_pos (by simp only; omega), e1]
          by_cases hq : q.1 = σ
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hq]
            simp
          · rw [if_neg (fun h => hq (by have := congrArg Fin.val h; simp only at this; omega)), if_neg hq]
            simp
        · rw [Pi.single_eq_of_ne (hj.ne hr), if_neg (fun h => hr (Fin.ext (by simp only; omega)))]
          simp
      · rw [hout m hm ⟨q.1, by omega⟩, Pi.smul_apply, Pi.single_eq_of_ne (fun h => hm ⟨_, h.symm⟩), smul_zero]
    have hs : (if q.1 = σ then (-1 : k) else 1) ≠ 0 := by split_ifs <;> norm_num
    rw [hv, hsm, hw, smul_smul, smul_smul]
    refine (congrArg (· • Pi.single (j ⟨2 * σ - q.1, by omega⟩) (1 : k)) ?_).trans (one_smul k _)
    field_simp
end
