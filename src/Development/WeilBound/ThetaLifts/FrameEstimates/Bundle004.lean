module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ParityOfCoefficients

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem neg_mem_schA {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) : (fun x => Φ (-x)) ∈ schA F κ := by
  classical
  induction h using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f,
      fun y => g (-y), ⟨hg.1.comp_continuous continuous_neg, hg.2.comp_homeomorph (Homeomorph.neg _)⟩, ?_⟩
    funext x
    simp only [pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.neg_apply]
    congr 2
    funext i
    exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem exists_haar : ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure ∧
    ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (κ → AF F)) := inferInstance
  exact ⟨Measure.addHaarMeasure K, inferInstance, fun f => integral_neg_eq_self f _⟩

theorem coef_neg (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F))
    (hμ : ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ) (Φ₁ Φ₂ : (κ → AF F) → ℂ)
    (w : (κ → AF F) × (κ → AF F)) :
    coef F ψ μ Φ₁ Φ₂ (-w) = coef F ψ μ (fun x => Φ₁ (-x)) (fun x => Φ₂ (-x)) w := by
  unfold coef
  rw [← hμ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [schr, Prod.fst_neg, Prod.snd_neg, neg_dotProduct_neg, neg_add]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

def negOne (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J :=
  ⟨-1, by
    change ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J *
      ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J
    rw [Units.val_neg, Units.val_one, Matrix.map_neg _ (map_neg (cA σ)),
      Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    simp⟩

theorem mat_negOne_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (negOne σ J)⁻¹ = -1 := rfl

theorem mat_one_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (1 : UA σ J)⁻¹ = 1 := rfl

end ParityOfCoefficients


open ParityOfCoefficients in
theorem parity_of (hC : CoefEq) (hF : FourierInj) : Parity := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨μ, hμ, hneg⟩ := exists_haar (F := F) (κ := Fin n × Fin d)
  have pres : ∀ Φ ∈ schA F (Fin n × Fin d), om (negOne σ X.J, 1) Φ ∈ schA F (Fin n × Fin d) :=
    fun Φ hΦ => (IsUWeilPair.isUSplitting hp.weil).pres _ Φ hΦ
  have key : ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ x u,
      om (negOne σ X.J, 1) Φ₁ x * (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₂ u) =
        Φ₁ (-x) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro Φ₁ h₁ Φ₂ h₂
    refine hF F _ B.ψ hp.base.std μ hμ _ (pres _ h₁) _ (pres _ h₂) _ (neg_mem_schA h₁) _ (neg_mem_schA h₂) ?_
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂, ← coef_neg B.ψ μ hneg, mat_negOne_inv,
      mat_one_inv, Matrix.transpose_one, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, map_neg]
  by_cases h0 : ∃ Φ₀ ∈ schA F (Fin n × Fin d), ∃ u, Φ₀ (-u) ≠ 0
  · obtain ⟨Φ₀, hΦ₀, u, hu⟩ := h0
    have h1 := congrArg norm (key Φ₀ hΦ₀ Φ₀ hΦ₀ u u)
    simp only [norm_mul, Complex.norm_conj] at h1
    have h2 : ‖om (negOne σ X.J, 1) Φ₀ u‖ = ‖Φ₀ (-u)‖ :=
      (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp h1
    have h3 : ‖Φ₀ (-u)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h4 : (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u) ≠ 0 := by
      rw [← norm_ne_zero_iff, Complex.norm_conj, h2]; exact h3
    refine ⟨negOne σ X.J, (starRingEnd ℂ) (Φ₀ (-u)) / (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u), rfl, ?_,
      fun Φ hΦ => funext fun x => ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_conj, h2, div_self h3]
    · rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key Φ hΦ Φ₀ hΦ₀, mul_comm]
  · refine ⟨negOne σ X.J, 1, rfl, norm_one, fun Φ hΦ => ?_⟩
    have z : ∀ Ψ ∈ schA F (Fin n × Fin d), Ψ = 0 := fun Ψ hΨ => funext fun x => by
      by_contra hx
      exact h0 ⟨Ψ, hΨ, -x, by rwa [neg_neg]⟩
    rw [z _ (pres Φ hΦ), one_smul, z _ (neg_mem_schA hΦ)]

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped NNReal ENNReal
open MeasureTheory Metric

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_sep (Λ : Submodule ℤ V) [DiscreteTopology Λ] :
    ∃ ε : ℝ, 0 < ε ∧ Pairwise (Function.onFun Disjoint fun x : Λ => ball (x : V) ε) := by
  obtain ⟨δ, hδ, h⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set Λ)) 0 rfl
  refine ⟨δ / 2, by positivity, fun x y hxy => ?_⟩
  apply Metric.ball_disjoint_ball
  by_contra hlt
  push Not at hlt
  apply hxy
  have hm : x - y ∈ ball (0 : Λ) δ := by
    rw [mem_ball_zero_iff]
    have : ‖x - y‖ = dist (x : V) (y : V) := by
      rw [dist_eq_norm]; rfl
    linarith
  exact sub_eq_zero.1 (h hm)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_pt {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) (N : ℕ) {x y : V} (hy : y ∈ ball x ε) :
    ((1 + c * ‖x‖) ^ N)⁻¹ ≤ (1 + ε) ^ N * ((1 + ‖c • (1 : ℝ)‖ * ‖y‖) ^ N)⁻¹ := by
  have hcn : ‖c • (1 : ℝ)‖ = c := by simp [abs_of_pos hc]
  rw [hcn]
  have h1 : ‖y‖ ≤ ‖x‖ + ε := by
    have := mem_ball_iff_norm.1 hy
    have h2 := norm_le_norm_add_norm_sub' y x
    linarith
  have hx := norm_nonneg x
  have hy0 := norm_nonneg y
  have h2 : 1 + c * ‖y‖ ≤ (1 + ε) * (1 + c * ‖x‖) := by
    have : c * ‖y‖ ≤ c * (‖x‖ + ε) := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * ε ≤ ε := by nlinarith
    have h4 : 0 ≤ ε * (c * ‖x‖) := by positivity
    nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 N

theorem oneVar_core (Λ : Submodule ℤ V) [DiscreteTopology Λ] (N : ℕ) (hN : Module.finrank ℝ V < N) :
    ∃ K : ℝ≥0, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ K * ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) := by
  borelize V
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  set μ : Measure V := Measure.addHaar with hμ
  obtain ⟨ε, hε, hd⟩ := oneVar_sep Λ
  set f : V → ℝ≥0∞ := fun y => ENNReal.ofReal (((1 + ‖y‖) ^ N)⁻¹) with hf
  have hfm : Measurable f := by
    rw [hf]; fun_prop
  have hI : ∫⁻ y, f y ∂μ < ⊤ := by
    have := finite_integral_one_add_norm (E := V) (μ := μ) (r := (N : ℝ)) (by exact_mod_cast hN)
    refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) this
    rw [hf, Real.rpow_neg (by positivity), Real.rpow_natCast]
  set b : ℝ≥0∞ := μ (ball (0 : V) ε) with hb
  have hb0 : b ≠ 0 := (measure_ball_pos μ _ hε).ne'
  have hbt : b ≠ ⊤ := measure_ball_lt_top.ne
  set A : ℝ≥0∞ := ENNReal.ofReal ((1 + ε) ^ N) with hA
  have hK : b⁻¹ * A * ∫⁻ y, f y ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hb0) ENNReal.ofReal_ne_top) hI.ne
  refine ⟨(b⁻¹ * A * ∫⁻ y, f y ∂μ).toNNReal, fun c hc hc1 => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  have hsc : ∫⁻ y, f (c • y) ∂μ = ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) * ∫⁻ y, f y ∂μ := by
    rw [← lintegral_map hfm (measurable_const_smul c), Measure.map_addHaar_smul μ hc.ne', lintegral_smul_measure,
      abs_of_pos (by positivity), smul_eq_mul]
  have hpt : ∀ x : Λ, b * ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y in ball (x : V) ε, f (c • y) ∂μ := by
    intro x
    have e1 : b = μ (ball (x : V) ε) := (Measure.addHaar_ball_center μ _ _).symm
    rw [e1, mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
    simp only [hf]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := oneVar_pt hc hc1 hε N hy
    simpa [norm_smul] using this
  have hsum : b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y, f (c • y) ∂μ := by
    rw [← ENNReal.tsum_mul_left]
    refine (ENNReal.tsum_le_tsum hpt).trans ?_
    rw [ENNReal.tsum_mul_left, ← lintegral_iUnion (fun _ => measurableSet_ball) hd]
    gcongr
    exact Measure.restrict_le_self
  calc ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)
      = b⁻¹ * (b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, one_mul]
    _ ≤ b⁻¹ * (A * ∫⁻ y, f (c • y) ∂μ) := by gcongr
    _ = _ := by rw [hsc]; ring

end

theorem oneVar_of : OneVar := by
  intro V _ _ _ Λ _ N hN
  obtain ⟨K, hK⟩ := oneVar_core Λ N hN
  refine ⟨K, fun l => ?_⟩
  have h := hK (Real.exp (-max 0 l)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by simp))
  rw [← Real.exp_nat_mul, ← Real.exp_neg, mul_neg, neg_neg] at h
  refine le_trans (ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_) h
  have : Real.exp (-max 0 l) ≤ Real.exp (-l) := Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
  gcongr

end PositivityTheory.ThKEst

end
end

section

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEst.LatArchPf

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mul_realAd {u : AF F} (hu : evI F u = 0) (t : ℝ) : u * realAd F t = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem emb_realAd (hF : IsTotallyReal F) (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F t)) = t := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) with ha
  have h1 : InfiniteAdeleRing.ringEquiv_mixedSpace F a = algebraMap ℝ _ t := by
    rw [ha, RingEquiv.apply_symm_apply]
  have h2 := congrFun (congrArg Prod.fst h1) ⟨w, hw⟩
  have h3 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w) = t := h2
  change InfinitePlace.Completion.extensionEmbedding w (a w) = t
  rw [← h3]
  exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw (a w)).symm

theorem piInf_alg {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]

theorem piInf_rId (hF : IsTotallyReal F) {w : InfinitePlace F} (τ : EmbOver E w) (t : ℝ) :
    piInf τ (algebraMap (AF F) (AE F E) (rId F t)) = (Real.exp t : ℝ) := by
  rw [piInf_alg, rId, map_add (f := _), map_add (f := _), map_one, map_one, emb_realAd hF]
  push_cast
  ring

theorem sz_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (z : Ten F E n d) : 0 ≤ sz τ z := by
  unfold sz
  positivity

theorem sz_mul_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (M : ℝ) (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ M) :
    sz τ (y * Bᵀ) ≤ d * M * sz τ y := by
  unfold sz
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : ∀ j, ‖piInf (τ w) ((y * Bᵀ) i j)‖ ≤ M * ∑ k, ‖piInf (τ w) (y i k)‖ := fun j => by

    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [map_mul, norm_mul, Matrix.transpose_apply, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB w j k) (norm_nonneg _)
  refine (Finset.sum_le_sum fun j _ => h j).trans ?_
  simp [mul_assoc]

theorem incM_mul {n : ℕ} (x y : Matrix (Fin n) (Fin n) E) : incM F (x * y) = incM F x * incM F y :=
  Matrix.map_mul

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem torus (hb : FrameBasis) (hc : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ}
    {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J) (fr : Frame σ J) (hg : fr.IsGood) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Cone fr.r, At (evI F) (mat (fr.a t) - 1) ∧
      ∀ w i j, ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤ K * Real.exp (∑ j, t j) := by
  obtain ⟨b, lam, ix, iy, -, h2, h3, -, h5⟩ := hb F E σ hc d J hJ fr hg
  set P := incM F b.1 with hP
  set Q := incM F (b⁻¹).1 with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← incM_mul, Units.mul_inv, incM_one]
  refine ⟨∑ w, ∑ i, ∑ j, ∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖, by positivity, fun t ht => ?_⟩
  set D : Matrix (Fin d) (Fin d) (AE F E) :=
    Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t)) with hD
  have hB : mat (fr.a t) = P * D * Q := by
    rw [← h5 t, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hlam : ∀ k, lam k t ≤ ∑ j, t j := fun k => by
    have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
    by_cases hk : ∀ i, ix i ≠ k ∧ iy i ≠ k
    · rw [h3 k hk]
      exact h0
    · obtain ⟨i, hi⟩ := not_forall.1 hk
      rcases not_and_or.1 hi with e | e
      · rw [← not_not.1 e, (h2 i t).1]
        exact Finset.single_le_sum (fun j _ => ht.2 j) (Finset.mem_univ i)
      · rw [← not_not.1 e, (h2 i t).2]
        exact (neg_nonpos.2 (ht.2 i)).trans h0
  refine ⟨fun u hu => ?_, fun w i j => ?_⟩
  · have hu' : u • (D - 1) = 0 := by
      ext k l
      by_cases e : k = l
      · subst e
        simp only [hD, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
          Matrix.zero_apply, rId, map_add, map_one, add_sub_cancel_left]
        rw [Algebra.smul_def, ← map_mul, mul_realAd hu, map_zero]
      · simp [hD, Matrix.diagonal_apply_ne _ e, Matrix.one_apply_ne e]
    have e : mat (fr.a t) - 1 = P * (D - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, hB]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.mul_zero, Matrix.zero_mul]
  · have h1 : ‖piInf (τ w) (mat (fr.a t) i j)‖ ≤
        (∑ k, ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) * Real.exp (∑ j, t j) := by

      rw [hB, Matrix.mul_apply, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [hD, Matrix.mul_diagonal, map_mul, map_mul, piInf_rId hc.1, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_right_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hlam k)) (by positivity)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ∑ k,
      ‖piInf (τ w) (P i k)‖ * ‖piInf (τ w) (Q k j)‖) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem maj_le (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (C : Set (Ten F E n d)) (N : ℕ) (y : Ten F E n d)
    (B : Matrix (Fin d) (Fin d) (AE F E)) (K s : ℝ) (hK : 0 ≤ K) (hs : 1 ≤ s) (h1 : At (evI F) (B - 1))
    (hB : ∀ w i j, ‖piInf (τ w) (B i j)‖ ≤ K * s) :
    maj τ C N y ≤ ((1 + d * K) * s) ^ N * maj τ C N (y * Bᵀ) := by
  have hy := sz_nonneg τ y
  have hz := sz_nonneg τ (y * Bᵀ)
  have hs0 : 0 < s := by linarith
  unfold maj
  split_ifs with h2 h3 h3
  · have h4 := sz_mul_le τ y B _ hB
    have h5 : 1 + sz τ (y * Bᵀ) ≤ (1 + d * K) * s * (1 + sz τ y) := by
      have : 0 ≤ d * K * s := by positivity
      have : 0 ≤ s * sz τ y := by positivity
      nlinarith
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h5 N
  · refine absurd ?_ h3
    obtain ⟨c, hc, h⟩ := h2
    refine ⟨c, hc, fun u hu => ?_⟩
    have e : y * Bᵀ - c = (y - c) + y * (B - 1)ᵀ := by
      rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.transpose_one, Matrix.mul_one]
      abel
    rw [e, smul_add, h u hu, zero_add, ← Matrix.mul_smul, ← Matrix.transpose_smul, h1 u hu, Matrix.transpose_zero,
      Matrix.mul_zero]
  · positivity
  · simp

end PositivityTheory.ThKEst.LatArchPf

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK LatArchPf

theorem latArch_of (hb : FrameBasis) : LatArch := by
  intro F E _ _ _ _ _ σ hc τ n d J J' _ hJ' fr hg C N hC
  obtain ⟨K, hK, h⟩ := torus hb hc τ hJ' fr hg
  refine ⟨C, Real.toNNReal ((1 + d * K) ^ N), hC, fun S g t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t ht
  unfold latSum
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have h0 : 0 ≤ ∑ j, t j := Finset.sum_nonneg fun j _ => ht.2 j
  have h3 := maj_le τ C N (mat g⁻¹ * incM F x.1 * (mat (fr.a t)⁻¹)ᵀ) (mat (fr.a t)) K _ hK (Real.one_le_exp h0) h1 h2
  have e : mat (fr.a t) * mat (fr.a t)⁻¹ = mat (1 : UA σ J')⁻¹ := by
    rw [inv_one, ← mul_inv_cancel (fr.a t)]
    rfl
  rw [Matrix.mul_assoc _ _ (mat (fr.a t))ᵀ, ← Matrix.transpose_mul, e] at h3
  change _ ≤ ENNReal.ofReal ((1 + d * K) ^ N) * _ * _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (h3.trans_eq ?_)
  rw [mul_pow, Real.exp_nat_mul]

end PositivityTheory.ThKEst

end
end
