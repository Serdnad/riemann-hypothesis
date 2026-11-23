module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle228
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle146
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle231
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle232
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.ConvSmooth

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C) (ball_mem_nhds t₀ one_pos)
    (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W} (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

section Group

open GlobalTheory.AdelicU GlobalTheory.Orb NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {u : P → GAd σ J} {ν μ : Measure (GAd σ J)} {φ : GAd σ J → ℂ} {K : Set (GAd σ J)}


omit [NumberField E] [FiniteDimensional ℝ P] in
theorem infFin_mul_smoothFam (hu : IsSmoothRealFam u) {a : GInf σ J → ℂ} {b : GFin σ J → ℂ}
    {Φ : (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) → ℂ} (e : ∀ x, a x = Φ (infCoord σ J x))
    (z : GAd σ J) (t : P) :
    infFin σ J a b (z * u t) = Φ (fun w τ i j => ∑ k, infCoord σ J (projInf σ J z) w τ i k *
      archMat σ J τ (projArch σ J w (u t)) k j) * b (projFin σ J z) := by
  simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]

theorem integrable_conj_mul_of_mem (hφ : Integrable φ ν) {h : GAd σ J → ℂ}
    (hh : h ∈ CcAd σ J) (g : GAd σ J) (x : GAd σ J) :
    Integrable (fun y => conj (h (y⁻¹ * g * x)) * φ y) ν := by
  obtain ⟨h1, h2⟩ := continuous_of_mem_ccAd hh
  obtain ⟨M, hM⟩ := h1.bounded_above_of_compact_support h2
  refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
  · have hc : Continuous fun y : GAd σ J => conj (h (y⁻¹ * g * x)) :=
      Complex.continuous_conj.comp (h1.comp ((continuous_inv.mul continuous_const).mul continuous_const))
    exact hc.aestronglyMeasurable.mul hφ.1
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

theorem contDiff_integral_of_compact (hu : IsSmoothRealFam u) (hKc : IsCompact K) (hK : ∀ᵐ y ∂ν, y ∈ K)
    (hφ : Integrable φ ν) {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂ν := by
  induction hh using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, hb, rfl⟩ := hf
    have hcc : Continuous fun y : GAd σ J => infCoord σ J (projInf σ J (y⁻¹ * g)) :=
      (continuous_infCoord σ J).comp ((continuous_projInf σ J).comp (continuous_inv.mul continuous_const))
    obtain ⟨M, hM⟩ := hb.1.continuous.bounded_above_of_compact_support hb.2
    have hφ' : Integrable (fun y => conj (b (projFin σ J (y⁻¹ * g))) * φ y) ν := by
      refine Integrable.mono' (hφ.norm.const_mul M) ?_ (.of_forall fun y => ?_)
      · exact (Complex.continuous_conj.comp (hb.1.continuous.comp ((continuous_projFin σ J).comp
          (continuous_inv.mul continuous_const)))).aestronglyMeasurable.mul hφ.1
      · rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    have hΘ : ContDiff ℝ ∞ fun p : P × (∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℂ) =>
        conj (Φ (fun w τ i j => ∑ k, p.2 w τ i k * archMat σ J τ (projArch σ J w (u p.1)) k j)) :=
      Complex.conjCLE.contDiff.comp (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i =>
        contDiff_pi.2 fun j => ContDiff.sum fun k _ =>
          (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_snd w) τ) i) k).mul
            ((hu.2 w τ k j).comp contDiff_fst)))
    have key := GlobalTheory.ConvSmooth.contDiff_integral_smul_param hcc.aestronglyMeasurable (hKc.image hcc)
      (hK.mono fun y hy => mem_image_of_mem _ hy) hφ' hΘ
    convert key using 1
    funext t
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [infFin_mul_smoothFam hu e, map_mul]
    ring
  | zero => simp only [Pi.zero_apply, map_zero, zero_mul, integral_zero]; exact contDiff_const
  | add f f' hf hf' h h' =>
    have e : (fun t => ∫ y, conj ((f + f') (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => (∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν) + ∫ y, conj (f' (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        simp only [Pi.add_apply, map_add (f := _), add_mul]
        exact integral_add (integrable_conj_mul_of_mem hφ hf g _) (integrable_conj_mul_of_mem hφ hf' g _)
    rw [e]
    exact h.add h'
  | smul a f _ h =>
    have e : (fun t => ∫ y, conj ((a • f) (y⁻¹ * g * u t)) * φ y ∂ν) =
        fun t => conj a * ∫ y, conj (f (y⁻¹ * g * u t)) * φ y ∂ν :=
      funext fun t => by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        ring
    rw [e]
    exact contDiff_const.mul h

theorem contDiff_integral_conj_mul (hu : IsSmoothRealFam u) (hcu : Continuous u) (hφ : LocallyIntegrable φ μ)
    {h : GAd σ J → ℂ} (hh : h ∈ CcAd σ J) (g : GAd σ J) :
    ContDiff ℝ ∞ fun t => ∫ y, conj (h (y⁻¹ * g * u t)) * φ y ∂μ := by
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  obtain ⟨-, hs⟩ := continuous_of_mem_ccAd hh
  set K := (fun p : P × GAd σ J => g * u p.1 * p.2⁻¹) '' (closedBall t₀ 1 ×ˢ tsupport h) with hKdef
  have hKc : IsCompact K := ((isCompact_closedBall t₀ 1).prod hs.isCompact).image (by fun_prop)
  have key := contDiff_integral_of_compact (ν := μ.restrict K) hu hKc (ae_restrict_mem hKc.measurableSet)
    (hφ.integrableOn_isCompact hKc) hh g
  refine key.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
  have : y⁻¹ * g * u t ∉ tsupport h := fun hm =>
    hy ⟨(t, y⁻¹ * g * u t), ⟨ball_subset_closedBall ht, hm⟩, by simp [mul_assoc]⟩
  simp [image_eq_zero_of_notMem_tsupport this]

end Group

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem continuous_ofFn_prod {G Q : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Q]
    {k : ℕ} {v : Fin k → Q → G} (hv : ∀ i, Continuous (v i)) :
    Continuous fun t => (List.ofFn fun i => v i t).prod := by
  induction k with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hv 0).mul (ih fun i => hv i.succ)

theorem contDiff_convR_lift_oneP : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g : GA D V, ContDiff ℝ ∞ fun t : Fin k → ℝ => GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  intro D V μ _ _ θ hθ f hf F k τs Xs hX g
  have hu := GlobalTheory.Orb.isSmoothRealFam_prod fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).1.comp (contDiff_apply ℝ (fun _ => ℝ) i)
  have hcu := continuous_ofFn_prod (v := fun i (t : Fin k → ℝ) => oneP θ V (τs i) (Xs i) (t i)) fun i =>
    (GlobalTheory.Orb.isSmoothRealFam_oneP hθ (hX i)).2.1.comp (continuous_apply i)
  have hφ : LocallyIntegrable (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) μ :=
    locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have key := contDiff_integral_conj_mul hu hcu hφ (GlobalTheory.Orb.starFn_mem_ccAd hf) g
  convert key using 1
  funext t
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp [GlobalTheory.AutomorphicL2Unitary.starFn, mul_assoc]

end Record

end GlobalTheory.ConvSmooth
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeConjPart

open Formalism.L2.NTheta GlobalTheory.SplitPlace IsDedekindDomain

variable {D : D7}

theorem le_unif {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
  rw [WithZero.coe_le_coe]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at h
  rw [← Multiplicative.toAdd_le, toAdd_ofAdd]
  omega

theorem ratio_int {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {y : 𝓞 D.host.E} (hy : y ∈ P.asIdeal) :
    ∃ t ∈ intAE D, finPart D e * finPart D (incA D (y : D.host.E)) =
      t * (finPart D e * finPart D (incA D (ϖ : D.host.E))) := by
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    apply hP2
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  set φ : D.host.E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v := (π.comp (finPart D)).comp (incA D) with hφ
  set q : D.host.E := (y : D.host.E) / (ϖ : D.host.E)
  refine ⟨finPart D e * finPart D (incA D q), ?_, ?_⟩
  · rw [h4]
    change Valued.v (φ q) ≤ 1
    rw [map_div₀, map_div₀]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hn := (he.2 y hy0).1 hy
    rw [map_mul, h4] at hn
    change ¬ Valued.v (φ ((y : D.host.E)⁻¹)) ≤ 1 at hn
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 fun h0 => hy0 (RingOfIntegers.coe_eq_zero_iff.1 h0))))] at hn
    have hϖv : Valued.v (φ ϖ) = _ := hu
    have h6 := le_unif hn
    rw [← hϖv] at h6
    rw [div_le_one₀ (by rw [hϖv]; exact zero_lt_iff.2 WithZero.coe_ne_zero)]
    exact h6
  · have hee : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
    have hq : q * (ϖ : D.host.E) = y := div_mul_cancel₀ _ hϖ0
    calc finPart D e * finPart D (incA D (y : D.host.E))
        = (finPart D e * finPart D e) * (finPart D (incA D q) * finPart D (incA D (ϖ : D.host.E))) := by
          rw [hee, ← map_mul (finPart D) (incA D q), ← map_mul (incA D) q, hq]
      _ = _ := mul_mul_mul_comm _ _ _ _

open scoped Matrix



theorem keeps {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ z ∈ LamHat V, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z ∈ LamHat V := by
  intro z hz
  have hee : e * e = e := he.1.1
  have hint : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, x, rfl⟩
  have hc := hecke_conj hee ha
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have h4 := (lower_iff hce V _ a₀⁻¹).1 hc.2.2.2.1
  rw [inv_inv] at h4
  obtain ⟨t, ht, hteq⟩ := ratio_int he hP hP2 ((Formalism.L2.Col.mem_conjP P x).1 hx)
  have hteq' := congrArg (cf D) hteq
  rw [map_mul, map_mul, map_mul, ← fin_cA, ← fin_cA, ← fin_cA, cA_incA, cA_incA] at hteq'
  have hsx : star ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := by
    change star (star (x : D.host.E)) = _
    exact star_star _
  rw [hsx] at hteq'
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀).1 ha.2.1) z
  rw [← fm_eq V a₀] at h6
  rw [h6, RingHom.map_add (f := _), add_smul, smul_sub, smul_add, smul_add]
  have hi1 := idem_mem hee
  have hi2 := idem_mem hce
  refine sub_mem (add_mem (add_mem ?_ ?_) (smul_mem V hint hz))
    (smul_mem V hint (smul_mem V (add_mem hi1 hi2) hz))
  · exact smul_mem V hint (ha.2.2.1 z hz)
  · rw [smul_smul, mul_comm, hteq', mul_smul]
    exact smul_mem V (cf_mem ht) (h4 z hz)

theorem finHom_eq {V : HSp D} (g : GA D V) : (finHom V g).1 = fm V g := rfl

theorem finPart_incA (c : D.host.E) :
    finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl

theorem keeps_one {V : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P)
    {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) {k : ℕ} {a₀ : GA D V}
    (ha : IsHeckeElt V e (ϖ : D.host.E) k a₀) {x : 𝓞 D.host.E} (hx : x ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal) :
    ∀ y ∈ latGHat V 1, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y ∈ latGHat V 1 := by
  intro y hy
  rw [GlobalTheory.LevelActionPinned.latGHat_one] at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, z, hz, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨c, hc, finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ z, ?_, ?_⟩
    · rw [GlobalTheory.StdFrameCong.pj_latHat_eq] at hz ⊢
      exact keeps he hP hP2 ha hx z hz
    · rw [Matrix.mulVec_smul, smul_comm]
  | zero => rw [Matrix.mulVec_zero, smul_zero]; exact zero_mem _
  | add a b _ _ ha' hb' => rw [Matrix.mulVec_add, smul_add]; exact add_mem ha' hb'
  | neg a _ ha' => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem ha'

end GlobalTheory.HeckeConjPart

open scoped Matrix


open GlobalTheory.SplitPlace in
theorem GlobalTheory.HeckeConjPart.conj_part : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E)
    (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g a₀ he hP hP2 ha
  rw [Submodule.smul_le]
  intro x hx v hv
  have spec := GlobalTheory.MarkCoset.latG_spec D V
  rw [(spec (g * a₀)).1, (spec (g * a₀)).2] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  rw [(spec g).1, (spec g).2]
  refine ⟨finPart D (incA D (x : D.host.E)) • fm V a₀ *ᵥ y, GlobalTheory.HeckeConjPart.keeps_one he hP hP2 ha hx y hy, ?_⟩
  rw [GlobalTheory.HeckeConjPart.finHom_eq] at hyv ⊢
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← fm_mul, hyv]
  funext i
  simp only [finVec, Pi.smul_apply, smul_eq_mul, GlobalTheory.HeckeConjPart.finPart_incA,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.testGridRowZero_vertices_agree_weilData : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ j, j ≤ D.R.m → NodeAgree (GlobalTheory.Grid.row0 R j) W (.grid 0 j) := by
  first | exact @GlobalTheory.GridJoin.nodeAgree_grid0_of_weil_over | exact GlobalTheory.GridJoin.nodeAgree_grid0_of_weil_over | (intros; apply GlobalTheory.GridJoin.nodeAgree_grid0_of_weil_over <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∃ X : ProvA, (∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) ∧
      DiscreteSeriesBlattner X ∧ admQ5 X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X ∧ ArchimedeanRallisUpDownLine X ∧ ArchimedeanRallisFifth X := by
  intro hDS hHC

  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam fun p q T lam hl =>
    GlobalTheory.CoverDS.exists_hasParam hDS p q T lam hl
  have hH1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have hH2 : admH2 X := GlobalTheory.FockAlg.fock_structure X
  have hD1 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX
  have hQ5 : admQ5 X := GlobalTheory.Published.HarishChandraModules.admQ5_of_harishChandraModules hHC X
  have hQ6 : CoverHaarIntegration X := GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X
  have hQ7 : admQ7 := TensorHW.highestWeight_tensor
  have hQ8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have hD2 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X hD1 hQ5 hQ7 hQ8
  have hA1 : ArchimedeanRallisFirst X := GlobalTheory.T.doublingIntegral_jointHarmonic_pos X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8
  have hA2 : ArchimedeanRallisSecond X := GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8 hA1
  have hA3 : ArchimedeanRallisUpDownLine X := GlobalTheory.T.theta_correspondence_fock_ds_uniqueness X hH1 hH2 hD1 hQ5 hQ7 hQ8 hA1 hA2
  have hA5 : ArchimedeanRallisFifth X := GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series X hH1 hH2 hD1 hQ5
  exact ⟨X, hX, hD1, hQ5, hA1, hA2, hA3, hA5⟩

end GlobalTheory.RealPlaceTheta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ t ∈ GfC (Yc D 0), ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ EP R F, MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X) ∧ ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  first | exact @GlobalTheory.EvalNormTransfer.evalTranslate_norm | exact GlobalTheory.EvalNormTransfer.evalTranslate_norm | (intros; apply GlobalTheory.EvalNormTransfer.evalTranslate_norm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_unipotentRadical_iff_iota_mem_adelicRadical : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) := by
  first | exact @GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | exact GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | (intros; apply GlobalTheory.SeeOntoCusp.mem_NI_iff_iota <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugatedIntertwiner_hasColumnLevel : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  first | exact @GlobalTheory.ConjRowLevel.conjMap_level | exact GlobalTheory.ConjRowLevel.conjMap_level | (intros; apply GlobalTheory.ConjRowLevel.conjMap_level <;> assumption)
end
