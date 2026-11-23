module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NChart
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Laplace
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

private theorem integrable_one_add_mul_norm_sq_rpow_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] {a s : ℝ} (ha : 0 < a) (hs : (Module.finrank ℝ E : ℝ) < 2 * s) :
    MeasureTheory.Integrable (fun v : E => (1 + a * ‖v‖ ^ 2) ^ (-s)) μ := by
  open MeasureTheory Filter Topology in
  have h := (integrable_rpow_neg_one_add_norm_sq (μ := μ) hs).comp_smul (Real.sqrt_pos.2 ha).ne'
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 ha), mul_pow,
    Real.sq_sqrt ha.le]
  congr 1
  ring

private theorem main_lemma_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] (f : ℕ → E → ℂ)
    (hm : ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.AEStronglyMeasurable (f t) μ) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hlim : ∀ v, Filter.Tendsto (fun t : ℕ => f t ((Real.sqrt t)⁻¹ • v)) Filter.atTop
      (nhds (Complex.exp (-(B v v)))))
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hbd : ∀ᶠ t : ℕ in Filter.atTop, ∀ v, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.Integrable (f t) μ ∧ ∫ v, f t v ∂μ ≠ 0 := by
  open MeasureTheory Filter Topology in
  have hbig : ∀ᶠ t : ℕ in atTop, (Module.finrank ℝ E : ℝ) < 2 * (γ * t) ∧ (1 : ℝ) ≤ t := by
    have h1 : Tendsto (fun t : ℕ => 2 * (γ * (t : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop two_pos (Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop)
    filter_upwards [h1.eventually_gt_atTop (Module.finrank ℝ E : ℝ), eventually_ge_atTop 1]
      with t ht ht1
    exact ⟨ht, by exact_mod_cast ht1⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hbd.and hm).and hbig)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (hN N le_rfl).2.2

  have hmaj : ∀ t : ℕ, N ≤ t → ∀ w : E,
      ‖f t ((Real.sqrt t)⁻¹ • w)‖ ≤ (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N)) := by
    intro t ht w
    have ht' : (N : ℝ) ≤ t := by exact_mod_cast ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos ht'
    have h1 := (hN t ht).1.1 ((Real.sqrt t)⁻¹ • w)
    have hn : ‖(Real.sqrt t)⁻¹ • w‖ ^ 2 = ‖w‖ ^ 2 / t := by
      rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt htpos.le]
      ring
    rw [hn] at h1
    refine h1.trans ?_
    have hx : 0 ≤ c * ‖w‖ ^ 2 := by positivity
    have hmono := ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.mono_pow hx hNpos ht'
    have hA : 0 < 1 + c * ‖w‖ ^ 2 / N := by positivity
    have hB : 0 < 1 + c * ‖w‖ ^ 2 / t := by positivity
    have key : (1 + c * ‖w‖ ^ 2 / N) ^ (γ * N) ≤ (1 + c * ‖w‖ ^ 2 / t) ^ (γ * t) := by
      rw [mul_comm γ (N : ℝ), mul_comm γ (t : ℝ), Real.rpow_mul hA.le, Real.rpow_mul hB.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hmono hγ.le
    have e1 : c * (‖w‖ ^ 2 / t) = c * ‖w‖ ^ 2 / t := by ring
    have e2 : c / N * ‖w‖ ^ 2 = c * ‖w‖ ^ 2 / N := by ring
    rw [e1, e2, Real.rpow_neg hB.le, Real.rpow_neg hA.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hA _) key
  have hbint : Integrable (fun w : E => (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N))) μ :=
    integrable_one_add_mul_norm_sq_rpow_neg μ (div_pos hc hNpos) (hN N le_rfl).2.1
  have hgm : ∀ t : ℕ, N ≤ t → AEStronglyMeasurable (fun w => f t ((Real.sqrt t)⁻¹ • w)) μ := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos (by exact_mod_cast ht)
    have hr : (Real.sqrt t)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 htpos).ne'
    exact (hN t ht).1.2.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul μ hr)
  have hT : Tendsto (fun t : ℕ => ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ) atTop
      (𝓝 (∫ w, Complex.exp (-(B w w)) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence _
      ((eventually_ge_atTop N).mono hgm)
      ((eventually_ge_atTop N).mono fun t ht => Eventually.of_forall (hmaj t ht))
      hbint (Eventually.of_forall hlim)

  have hpos : ∀ v : E, v ≠ 0 → 0 < (B v v).re := by
    intro v hv
    have hle : ‖Complex.exp (-(B v v))‖ ≤ (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) :=
      le_of_tendsto (hlim v).norm (eventually_atTop.2 ⟨N, fun t ht => hmaj t ht v⟩)
    have hlt : (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · have hv' := norm_pos_iff.2 hv
        have : 0 < c / N * ‖v‖ ^ 2 := by positivity
        linarith
      · have := mul_pos hγ hNpos
        linarith
    rw [Complex.norm_exp] at hle
    have h3 : Real.exp (-(B v v)).re < 1 := hle.trans_lt hlt
    have h4 := Real.exp_lt_exp.1 (h3.trans_eq Real.exp_zero.symm)
    rw [Complex.neg_re] at h4
    linarith
  have hev : ∀ᶠ t : ℕ in atTop, ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ ≠ 0 :=
    hT.eventually_ne (ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero μ B hpos)
  filter_upwards [eventually_ge_atTop N, hev] with t ht hgt
  refine ⟨?_, ?_⟩
  · exact Integrable.mono' (integrable_one_add_mul_norm_sq_rpow_neg μ hc (hN t ht).2.1) (hN t ht).1.2
      (Eventually.of_forall (hN t ht).1.1)
  · intro h0
    apply hgt
    rw [Measure.integral_comp_smul μ (f t) (Real.sqrt t)⁻¹, h0, smul_zero]

theorem b6 : GaussianLimitHaar := by
  intro E _ _ _ _ _ μ _ f hm B hlim c γ hc hγ hbd
  exact main_lemma_2 μ f hm B hlim hc hγ hbd

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeDiscreteSeriesExistence (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  change star (if ε a = true then (1 : ℂ) else -1) = _
  split_ifs <;> simp

private theorem Jm_mul_Jm_mul_eq (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Y) = Y := by
  rw [← Matrix.mul_assoc, Jm_mul_selfDiscreteSeriesExistence, Matrix.one_mul]

theorem inv_eq_signature_conjTranspose_conj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem inv_mul_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ * g = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [inv_eq_signature_conjTranspose_conj hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem mul_inv_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (inv_mul_self_of_mem_indefiniteUnitary hg))

theorem isUnit_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : IsUnit g :=
  ⟨⟨g, g⁻¹, mul_inv_self_of_mem_indefiniteUnitary hg, inv_mul_self_of_mem_indefiniteUnitary hg⟩, rfl⟩

theorem inG_conj_unitary {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hX : inG ε X) : inG ε (g * X * g⁻¹) := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  have hX0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hX' : Jm ε * Xᴴ + X * Jm ε = 0 := by
    have e : Jm ε * Xᴴ + X * Jm ε = Jm ε * (Xᴴ * Jm ε + Jm ε * X) * Jm ε := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one,
        Jm_mul_Jm_mul_eq]
    rw [e, hX0, Matrix.mul_zero, Matrix.zero_mul]
  have key : (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) =
      Jm ε * g * (Jm ε * Xᴴ + X * Jm ε) * gᴴ * Jm ε := by
    rw [inv_eq_signature_conjTranspose_conj hg]
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
  show (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) = 0
  rw [key, hX', Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

private theorem Jm_conjTranspose_Jm_eq_neg_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have h0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h0
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, Jm_mul_Jm_mul_eq]

theorem conj_involution_complex_comb {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    stJ ε (A + Complex.I • B) = -A + Complex.I • B := by
  unfold stJ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Jm_conjTranspose_Jm_eq_neg_of_inG hA, Jm_conjTranspose_Jm_eq_neg_of_inG hB]
  simp [Complex.star_def, Complex.conj_I]

theorem actM_add_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    actM E (X + c • Y) = actM E X + c • actM E Y := by
  simp only [actM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

theorem actM_neg {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM E (-X) = -actM E X := by
  simp only [actM, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isometry_inner_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {h : Matrix (Fin n) (Fin n) ℂ}
    (hn : ∀ v : H, ‖σ h v‖ = ‖v‖) (a b : H) : ⟪σ h a, σ h b⟫_ℂ = ⟪a, b⟫_ℂ := by
  exact LinearIsometry.inner_map_map
    ({ toLinearMap := (σ h : H →ₗ[ℂ] H), norm_map' := hn } : H →ₗᵢ[ℂ] H) a b

theorem derived_action_skew_adjoint {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inG ε Y) {u u' : H}
    (hu : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) u) u' 0) :
    ⟪w, u'⟫_ℂ = -⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), u⟫_ℂ := by
  have hd := (isDerivedOn_smE hσ).deriv Y hY ⟨w, hw⟩
  have h3 : HasDerivAt
      (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ)
      (⟪σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) w, u'⟫_ℂ +
        ⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) u⟫_ℂ) 0 :=
    hd.inner ℂ hu
  have h4 : (fun t : ℝ =>
      ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ) =
      fun _ => ⟪w, u⟫_ℂ :=
    funext fun t => isometry_inner_eq (hσ.2.1 _ (exp_smul_mem_UJset hY t)) w u
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0 : ℝ) ⟪w, u⟫_ℂ)
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  rw [h0, hσ.1.1] at h5
  simp only [ContinuousLinearMap.one_apply] at h5
  exact eq_neg_of_add_eq_zero_left h5

theorem hasDerivAt_conj_exp_action {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w))
      (σ g ((actM (smE ε σ) X ⟨w, hw⟩ : smD ε σ) : H)) 0 := by
  have hgX : inG ε (g * X * g⁻¹) := inG_conj_unitary hg hX
  have hd := (isDerivedOn_smE hσ).deriv X hX ⟨w, hw⟩
  have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w)) =
      fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) w) := by
    funext t
    have hm : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g = g * NormedSpace.exp ((t : ℂ) • X) := by
      rw [show (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ by
          rw [Matrix.mul_smul, Matrix.smul_mul],
        Matrix.exp_conj g _ (isUnit_of_mem_indefiniteUnitary hg), Matrix.mul_assoc, inv_mul_self_of_mem_indefiniteUnitary hg, Matrix.mul_one]
    have h1 := hσ.1.2 _ (exp_smul_mem_UJset hgX t) g hg
    have h2 := hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)
    rw [hm] at h1
    exact congrArg (fun L : H →L[ℂ] H => L w) (h1.symm.trans h2)
  rw [hfun]
  exact ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd

end Rep

private theorem inG_of_Jm_conj_eq_neg {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Jm ε * Yᴴ * Jm ε = -Y) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  have e : Yᴴ * Jm ε = Jm ε * (Jm ε * Yᴴ * Jm ε) := by
    rw [Matrix.mul_assoc (Jm ε) Yᴴ, Jm_mul_Jm_mul_eq]
  rw [e, h, Matrix.mul_neg, neg_add_cancel]

private theorem exists_inG_add_I_smul_inG (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inG ε A ∧ inG ε B ∧ X = A + Complex.I • B := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  refine ⟨(1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε), (1 / (2 * Complex.I)) • (X + Jm ε * Xᴴ * Jm ε),
    ?_, ?_, ?_⟩
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.star_def, Complex.conj_I]
    rw [hc, neg_smul, add_comm (Jm ε * (Xᴴ * Jm ε)) X]
  · have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
      rw [mul_one_div, mul_comm 2 Complex.I, ← div_div, div_self Complex.I_ne_zero]
    have h2 : X - Jm ε * Xᴴ * Jm ε + (X + Jm ε * Xᴴ * Jm ε) = (2 : ℂ) • X := by
      rw [two_smul]; abel
    rw [smul_smul, hI, ← smul_add, h2, smul_smul]
    norm_num

theorem b3a : MatrixCoeffConjugationMove := by
  intro n ε H _ _ σ w hσ hw g hg X
  have hφ : ∀ Y, phiW ε σ w Y = ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := fun Y => by
    simp only [phiW, dif_pos hw]
  have hlin : ∀ (Y Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      ((actM (smE ε σ) (Y + c • Z) ⟨w, hw⟩ : smD ε σ) : H) =
        ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) +
          c • ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y Z c
    rw [actM_add_smul]
    simp
  have hneg : ∀ Y, ((actM (smE ε σ) (-Y) ⟨w, hw⟩ : smD ε σ) : H) =
      -((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y
    rw [actM_neg]
    simp
  have key : ∀ Y, inG ε Y → ⟪w, σ g ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H)⟫_ℂ =
      -⟪((actM (smE ε σ) (g * Y * g⁻¹) ⟨w, hw⟩ : smD ε σ) : H), σ g w⟫_ℂ :=
    fun Y hY => derived_action_skew_adjoint hσ hw (inG_conj_unitary hg hY) (hasDerivAt_conj_exp_action hσ hw hg hY)
  obtain ⟨A, B, hA, hB, rfl⟩ := exists_inG_add_I_smul_inG ε X
  have hconj : g * (A + Complex.I • B) * g⁻¹ = g * A * g⁻¹ + Complex.I • (g * B * g⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, conj_involution_complex_comb (inG_conj_unitary hg hA) (inG_conj_unitary hg hB), hφ, hφ, hlin, hlin, hneg,
    map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
    inner_neg_left, key A hA, key B hB]
  simp only [Complex.conj_I]
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base
open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S MeasureTheory

section Generic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {F : ℕ → Submodule ℝ A} {L : ℕ} {st : A →ₗ[ℝ] A}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem haar_of_equiv [MeasurableSpace A] [BorelSpace A] [MeasurableSpace E] [BorelSpace E]
    (hF : IsFil F L) (hst : IsAdj F st) (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃ₗ[ℝ] lieN F st) :
    SigmaFinite (μ.map fun x => NormedSpace.exp (e x : A)) ∧
      (μ.map fun x => NormedSpace.exp (e x : A)) ≠ 0 ∧
      (μ.map fun x => NormedSpace.exp (e x : A)) {x | x ∉ grpN F st} = 0 ∧
      ∀ s ∈ grpN F st, (μ.map fun x => NormedSpace.exp (e x : A)).map (s * ·) =
        μ.map fun x => NormedSpace.exp (e x : A) := by
  let e' := e.toContinuousLinearEquiv
  have : (Measure.map e' μ).IsAddHaarMeasure := e'.isAddHaarMeasure_map μ
  have h := exp_chart_haar hF hst (Measure.map e' μ)
  have he := exp_chart_embedding (st := st) hF
  simp only [] at h
  rw [Measure.map_map he.measurable e'.continuous.measurable] at h
  exact h

omit [FiniteDimensional ℝ A] in
theorem growth_of_equiv (hF : IsFil F L) (U0 : E ≃ₗ[ℝ] A) : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ Y ∈ F 0,
    ‖U0.symm Y‖ ≤ C * ‖U0.symm (NormedSpace.exp Y - 1)‖ *
      (1 + ‖U0.symm (NormedSpace.exp Y - 1)‖) ^ M := by
  obtain ⟨C, M, hC, h⟩ := hF.log_growth
  let U := U0.toContinuousLinearEquiv
  set a := ‖(U.symm : A →L[ℝ] E)‖ with ha
  set b := ‖(U : E →L[ℝ] A)‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have h1 : ∀ X, ‖U0.symm X‖ ≤ a * ‖X‖ := fun X => (U.symm : A →L[ℝ] E).le_opNorm X
  have h2 : ∀ X, ‖X‖ ≤ b * ‖U0.symm X‖ := fun X => by
    have := (U : E →L[ℝ] A).le_opNorm (U.symm X)
    rwa [ContinuousLinearEquiv.coe_coe, U.apply_symm_apply] at this
  refine ⟨a * C * b * (1 + b) ^ M, M, by positivity, fun Y hY => ?_⟩
  set s := ‖U0.symm (NormedSpace.exp Y - 1)‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have h3 := h2 (NormedSpace.exp Y - 1)
  have h4 : 1 + ‖NormedSpace.exp Y - 1‖ ≤ (1 + b) * (1 + s) := by nlinarith
  calc ‖U0.symm Y‖ ≤ a * ‖Y‖ := h1 Y
    _ ≤ a * (C * ‖NormedSpace.exp Y - 1‖ * (1 + ‖NormedSpace.exp Y - 1‖) ^ M) :=
        mul_le_mul_of_nonneg_left (h Y hY) ha0
    _ ≤ a * (C * (b * s) * ((1 + b) * (1 + s)) ^ M) := by gcongr
    _ = _ := by rw [mul_pow]; ring

end Generic

open scoped Matrix.Norms.Operator

noncomputable def unrealL (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := unrealify
  invFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' x y := by ext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by ext i j; apply Complex.ext <;> simp [unrealify]
  left_inv x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [unrealify, realifyFun]
  right_inv X := by ext i j; apply Complex.ext <;> simp [unrealify, realifyFun]

theorem sqrt_hs {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    Real.sqrt (S7.hs X) = ‖(unrealL m).symm X‖ := by
  rw [EuclideanSpace.norm_eq, S7.hs]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show ‖X i j‖ ^ 2 = ‖(X i j).im‖ ^ 2 + ‖(X i j).re‖ ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

variable {k r : ℕ}

theorem lieE_eq : lieE (Nset k r) =
    (lieN (levF (levB k r)) (adjH (Hpk k r))).map (unrealL _).symm.toLinearMap := by
  rw [lieE, lieOf_Nset_eq, ← Submodule.span_eq (Submodule.map _ _)]
  rfl

theorem unipotent_exp_haar_sqrt_bound (k r : ℕ) :
    (∀ Y ∈ lieOf (Nset k r), ∀ Y' ∈ lieOf (Nset k r),
      NormedSpace.exp Y = NormedSpace.exp Y' → Y = Y') ∧
    (∀ g ∈ Nset k r, ∃ Y ∈ lieOf (Nset k r), NormedSpace.exp Y = g) ∧
    (∀ x : lieE (Nset k r), unrealify (x : EuclideanSpace ℝ _) ∈ lieOf (Nset k r)) ∧
    IsHaarOn (Nset k r) (haarLie (Nset k r) 1) ∧
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ Y ∈ lieOf (Nset k r),
      Real.sqrt (S7.hs Y) ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
        (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m := by
  have hmem : ∀ x : lieE (Nset k r),
      unrealL _ (x : EuclideanSpace ℝ _) ∈ lieN (levF (levB k r)) (adjH (Hpk k r)) := by
    rintro ⟨x, hx⟩
    rw [lieE_eq] at hx
    obtain ⟨Y, hY, rfl⟩ := hx
    simpa using hY
  refine ⟨fun Y hY Y' hY' h => ?_, fun g hg => ?_, fun x => ?_, ?_, ?_⟩
  · rw [lieOf_Nset_eq] at hY hY'
    exact exp_injOn isFilB (mem_lieN.mp hY).1 (mem_lieN.mp hY').1 h
  · rw [Nset_eq] at hg
    rw [lieOf_Nset_eq]
    exact ⟨_, lg_spec isFilB isAdjB hg⟩
  · rw [lieOf_Nset_eq]; exact hmem x
  · let e : lieE (Nset k r) ≃ₗ[ℝ] lieN (levF (levB k r)) (adjH (Hpk k r)) :=
      { toFun := fun x => ⟨unrealL _ x, hmem x⟩
        invFun := fun Y => ⟨(unrealL _).symm Y, by rw [lieE_eq]; exact ⟨Y, Y.2, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add (unrealL _) _ _)
        map_smul' := fun c x => Subtype.ext (map_smul (unrealL _) _ _)
        left_inv := fun x => Subtype.ext ((unrealL _).symm_apply_apply _)
        right_inv := fun Y => Subtype.ext ((unrealL _).apply_symm_apply _) }
    have h := @haar_of_equiv (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra _ _ _ _ _ _ _ _
      (inferInstance : MeasurableSpace (Mt k r))
      (inferInstance : BorelSpace (Mt k r)) _ _ isFilB isAdjB volume _ e
    rw [← Nset_eq] at h
    rw [haarLie, one_smul]
    exact h
  · obtain ⟨C, M, hC, h⟩ := growth_of_equiv (isFilB (k := k) (r := r)) (unrealL (2 * r + k + 1))
    refine ⟨C, M, hC, fun Y hY => ?_⟩
    rw [lieOf_Nset_eq] at hY
    rw [sqrt_hs, sqrt_hs]
    exact h Y (mem_lieN.mp hY).1

theorem b4 : NsetExpInjectiveSurjective := unipotent_exp_haar_sqrt_bound

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end
