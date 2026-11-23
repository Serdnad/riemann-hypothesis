module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem primed_lintegral_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a F G : α → ℝ≥0∞) (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (h : ∀ x, a x ^ 2 ≤ F x * G x) :
    (∫⁻ x, a x ∂μ) ^ 2 ≤ (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
  have hpt : ∀ x, a x ≤ F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := by
    intro x
    calc a x = (a x ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ (F x * G x) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (h x) (by norm_num)
      _ = F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hF.pow_const (1 / 2 : ℝ)) (hG.pow_const (1 / 2 : ℝ))
  have hsq : ∀ y : ℝ≥0∞, (y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = y := by
    intro y; rw [← ENNReal.rpow_mul]; norm_num
  simp only [hsq, Pi.mul_apply] at hH
  have hle : ∫⁻ x, a x ∂μ ≤ (∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ) :=
    (lintegral_mono hpt).trans hH
  calc (∫⁻ x, a x ∂μ) ^ 2
      ≤ ((∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (n := 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

theorem primed_ofReal_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hm : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hm]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable hm]
    simp

theorem primed_inner_norm (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (F0 : M → ℂ)
    (g : M → V n) (x : M) :
    ‖⟪dbarF n z F0 x, g x⟫_ℂ‖ = ‖dbarDot n z F0 x (fun j => g x j)‖ := by
  have : ⟪dbarF n z F0 x, g x⟫_ℂ = starRingEnd ℂ (dbarDot n z F0 x (fun j => g x j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dbarF, dbarDot, PiLp.inner_apply, map_sum, mul_comm]
  rw [this, Complex.norm_conj]

theorem primedIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hAP : APStatement n M) : PrimedIneqStatement n M := by
  intro z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hpp hlevi hA g hg
  have cR : ∀ f : M → ℝ, SmoothR n z f → Continuous f := fun f hf => by
    exact (Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)).congr fun x => by simp
  have cph' := cR ph' hph'
  have cψ := cR ψ hψ
  have cg : ∀ j, Continuous fun x => g x j := fun j => Ck.continuous n z hz 2 _ (hg j).1
  have cLevi : ∀ q : M → ℝ, SmoothR n z q →
      Continuous fun x => (Levi n z q x (fun j => g x j)).re := by
    intro q hq
    refine Complex.continuous_re.comp ?_
    unfold Levi
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    exact ((Smooth.continuous n z hz _ (Smooth.d n z j _ (Smooth.db n z k _ hq))).mul
      (cg j)).mul (Complex.continuous_conj.comp (cg k))
  have cdS : Continuous fun x => dSqR n z ψ x := by
    unfold dSqR
    exact continuous_finsetSum _ fun j _ =>
      ((Smooth.continuous n z hz _ (Smooth.d n z j _ hψ)).norm.pow 2)
  have hnorm : ∀ x, ‖g x‖ ^ 2 = ∑ j, ‖g x j‖ ^ 2 := fun x => EuclideanSpace.norm_sq_eq (g x)
  have cgn : Continuous fun x => ‖g x‖ ^ 2 := by
    simp_rw [hnorm]; exact continuous_finsetSum _ fun j _ => (cg j).norm.pow 2
  have hKc : IsCompact (⋃ j, tsupport (fun x => g x j)) :=
    isCompact_iUnion fun j => (hg j).2
  have hgK : ∀ x, x ∉ (⋃ j, tsupport (fun x => g x j)) → g x = 0 := by
    intro x hx
    simp only [mem_iUnion, not_exists] at hx
    ext j
    exact image_eq_zero_of_notMem_tsupport (f := fun x => g x j) (hx j)
  set Q : M → ℝ := fun x => ((Levi n z ph' x (fun j => g x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖g x‖ ^ 2) * Real.exp (-ph' x) with hQ
  have cQ : Continuous Q := ((cLevi ph' hph').sub ((continuous_const.mul cdS).mul cgn)).mul
    (Real.continuous_exp.comp cph'.neg)
  have sQ : HasCompactSupport Q := HasCompactSupport.intro hKc fun x hx => by
    simp [hQ, hgK x hx, Levi]
  have iQ : Integrable Q (vol n z) := integrable_of_continuous_real n z hz Q cQ sQ
  have hL0 : ∀ x, 0 ≤ (Levi n z ph x (fun j => g x j)).re := fun x => hlev x _
  have hLQ : ∀ x, (Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x) ≤ Q x := by
    intro x
    have h1 := hlevi x (fun j => g x j)
    beta_reduce at h1
    rw [← hnorm x] at h1
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hQ0 : ∀ x, 0 ≤ Q x := fun x =>
    (mul_nonneg (hL0 x) (Real.exp_pos _).le).trans (hLQ x)
  have hap := hAP z hz ph' ψ ε g (SmoothR.ckR n z 2 ph' hph') (SmoothR.ckR n z 1 ψ hψ) hε hg
  set Gf : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x)) with hGf
  set Ff : M → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) with hFf
  have hG : ∫⁻ x, Gf x ∂vol n z ≤ ENNReal.ofReal (1 + ε) *
      wint n z (tstar n z (w1 ph' ψ) (w2 ph' ψ) g) (w1 ph' ψ) + n2 n z (sbar n z g) ph' := by
    calc ∫⁻ x, Gf x ∂vol n z ≤ ∫⁻ x, ENNReal.ofReal (Q x) ∂vol n z :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hLQ x)
      _ = ENNReal.ofReal (∫ x, Q x ∂vol n z) :=
          (ofReal_integral_eq_lintegral_ofReal iQ (Eventually.of_forall hQ0)).symm
      _ ≤ ENNReal.ofReal ((1 + ε) * (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) :=
          ENNReal.ofReal_le_ofReal hap
      _ ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ENNReal.ofReal (∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) := by
          rw [← ENNReal.ofReal_mul (by linarith)]; exact ENNReal.ofReal_add_le
      _ ≤ _ := by
          gcongr
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (by unfold sq2; positivity) (Real.exp_pos _).le
  have hF : ∫⁻ x, Ff x ∂vol n z ≤ ∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z :=
    lintegral_mono fun x => by
      simp only [hFf]
      gcongr
      linarith [hpp x]
  have mF : AEMeasurable Ff (vol n z) :=
    (hh.mul (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.mul cψ).sub cph')).measurable)).aemeasurable
  have mG : AEMeasurable Gf (vol n z) :=
    (ENNReal.continuous_ofReal.comp ((cLevi ph hph).mul
      (Real.continuous_exp.comp cph'.neg))).measurable.aemeasurable
  set I : M → ℂ := fun x => ⟪dbarF n z F0 x, g x⟫_ℂ * (Real.exp (-w2 ph' ψ x) : ℂ) with hI
  have hpt : ∀ x, ‖I x‖ₑ ^ 2 ≤ Ff x * Gf x := by
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [hI, hFf, hGf]
    rw [norm_mul, primed_inner_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow]
    have he : Real.exp (-w2 ph' ψ x) ^ 2 = Real.exp (2 * ψ x - ph' x) * Real.exp (-ph' x) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; simp only [w2]; ring
    rw [he, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_mul (hL0 x)]
    calc ENNReal.ofReal (‖dbarDot n z F0 x (fun j => g x j)‖ ^ 2) *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x)))
        ≤ h x * ENNReal.ofReal (Levi n z ph x (fun j => g x j)).re *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x))) := by
          gcongr; exact hdom x _
      _ = _ := by ring
  show ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) ≤ _
  calc ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) = ‖∫ x, I x ∂vol n z‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ (∫⁻ x, ‖I x‖ₑ ∂vol n z) ^ 2 := by
        gcongr; exact enorm_integral_le_lintegral_enorm _
    _ ≤ (∫⁻ x, Ff x ∂vol n z) * ∫⁻ x, Gf x ∂vol n z :=
        primed_lintegral_sq_le _ _ _ _ mF mG hpt
    _ ≤ _ := mul_le_mul' hF hG

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem weakSSmooth (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : WeakSSmoothStatement n M := by
  intro z hz f hf φ hφ j k
  have hφ1 : Ck n z 1 φ := Smooth.ck n z 1 φ hφ.1
  have hcd : ∀ i : Fin n, HasCompactSupport (db n z i φ) := fun i =>
    hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z i φ))
  have hcont : ∀ i : Fin n, Continuous (db n z i φ) := fun i =>
    Ck.continuous n z hz 0 _ (Ck.db n z 0 i φ hφ1)
  have hfc : ∀ i : Fin n, Continuous (fun y => f y i) := fun i => Ck.continuous n z hz 1 _ (hf i)
  have hI1 : ∀ a b : Fin n, Integrable (fun x => f x a * db n z b φ x) (vol n z) := fun a b =>
    integrable_of_continuous n z hz _ ((hfc a).mul (hcont b)) ((hcd b).mul_left)
  have hI2 : ∀ a b : Fin n, Integrable (fun x => db n z b (fun y => f y a) x * φ x) (vol n z) :=
    fun a b => integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 0 _ (Ck.db n z 0 b _ (hf a))).mul (Ck.continuous n z hz 1 _ hφ1))
      hφ.2.mul_left
  have h1 := integral_db_mul n z hz j (fun y => f y k) φ (hf k) hφ1 hφ.2
  have h2 := integral_db_mul n z hz k (fun y => f y j) φ (hf j) hφ1 hφ.2
  have hL : ∫ x, (f x k * db n z j φ x - f x j * db n z k φ x) ∂vol n z
      = ∫ x, f x k * db n z j φ x ∂vol n z - ∫ x, f x j * db n z k φ x ∂vol n z :=
    integral_sub (hI1 k j) (hI1 j k)
  have hR : ∫ x, sbar n z f x j k * φ x ∂vol n z
      = ∫ x, db n z j (fun y => f y k) x * φ x ∂vol n z
        - ∫ x, db n z k (fun y => f y j) x * φ x ∂vol n z := by
    rw [← integral_sub (hI2 k j) (hI2 j k)]
    congr 1
    funext x
    simp only [sbar, sub_mul]
  rw [hL, hR, h1, h2]
  ring

private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[𝓝 (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ 𝓝 (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2

private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[𝓝 (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dite_eq_left hex]
  unfold wdb
  rw [hE.fderiv_eq]

private lemma fderiv_wdb_apply_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) (v : V n) :
    fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hF : fderiv ℝ (wdb n k h) y0 = (2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k))) := by
    rw [heq]
    exact HasFDerivAt.fderiv hW
  rw [hF]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

theorem sbarDbar (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SbarDbarStatement n M := by
  intro z hz g hg x
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ 𝓝 (z x) := e0.open_target.mem_nhds hy0
  have hcd : ContDiffAt ℝ 2 (g ∘ e0.symm) (z x) := by
    have := (hg e0 he0).contDiffAt hnb
    simpa using this
  have hd : DifferentiableAt ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : ∀ v w : V n, fderiv ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcd.isSymmSndFDerivAt (by simp) v w
      | exact hcd.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hloc : ∀ k : Fin n,
      ((fun y => db n z k g y) ∘ e0.symm) =ᶠ[𝓝 (z x)] wdb n k (g ∘ e0.symm) := by
    intro k
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 k g _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  funext j k
  show db n z j (fun y => db n z k g y) x - db n z k (fun y => db n z j g y) x = 0
  rw [db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0, db_eq_wdb_comp_chart_symm z e0 he0 k _ x hx0]
  unfold wdb
  rw [(hloc k).fderiv_eq, (hloc j).fderiv_eq,
    fderiv_wdb_apply_eq k _ _ hd (bas n j), fderiv_wdb_apply_eq k _ _ hd (Complex.I • bas n j),
    fderiv_wdb_apply_eq j _ _ hd (bas n k), fderiv_wdb_apply_eq j _ _ hd (Complex.I • bas n k),
    hsym (bas n k) (bas n j), hsym (bas n k) (Complex.I • bas n j),
    hsym (Complex.I • bas n k) (bas n j), hsym (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem smoothReal_continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous (fun x => (f x : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨e, hxe, rfl⟩ := hz x
    have hch : IsChart n (⇑e) e := fun _ _ => rfl
    have h1 := (hf e hch).continuousOn
    have h2 : ContinuousOn (fun y => (f y : ℂ)) e.source := by
      refine (h1.comp e.continuousOn (fun y hy => e.map_source hy)).congr fun y hy => ?_
      simp [Function.comp, e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  exact (Complex.continuous_re.comp hc).congr fun x => by simp

theorem sSup_image_le_max {M : Type*} (g : M → ℝ) (s : Set M) (B : ℝ)
    (hB : ∀ x ∈ s, g x ≤ B) : sSup (g '' s) ≤ max B 0 := by
  refine Real.sSup_le ?_ (le_max_right _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact (hB x hx).trans (le_max_left _ _)

theorem choice (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hChi : ChiStatement) (hPsi : PsiStatement n M)
    (hShell : ShellStatement n M) (hLZ : LeviNormSqStatement n M) (hChain : ChainStatement n M) :
    ChoiceStatement n M := by
  intro X ph v C ε hph hv hC hε
  have hz := X.isLocalHomeomorph

  have hE : SmoothR n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) :=
    SmoothR.add n X.z _ _ X.smooth_e (hLZ X.z hz).1
  have hEc : Continuous (fun y => X.e y + ‖X.z y‖ ^ 2) := smoothReal_continuous n X.z hz _ hE
  have hExh : ∀ b : ℝ, IsCompact {x | X.e x + ‖X.z x‖ ^ 2 ≤ b} := by
    intro b
    refine (X.isCompact_le b).of_isClosed_subset (isClosed_le hEc continuous_const) ?_
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    nlinarith [sq_nonneg ‖X.z x‖]
  have hLeviE : ∀ x ξ, (∑ j, ‖ξ j‖ ^ 2) ≤ (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re := by
    intro x ξ
    rw [levi_add n X.z X.e (fun y => ‖X.z y‖ ^ 2) (SmoothR.ckR n X.z 2 _ X.smooth_e)
      (SmoothR.ckR n X.z 2 _ (hLZ X.z hz).1) x ξ, (hLZ X.z hz).2 x ξ, Complex.add_re,
      Complex.ofReal_re]
    linarith [X.levi_e x ξ]

  obtain ⟨b0, hb0⟩ := hC.bddAbove_image hEc.continuousOn
  set a : ℝ := b0 + 1 with ha
  have hCa : ∀ x ∈ C, X.e x + ‖X.z x‖ ^ 2 < a := by
    intro x hx
    have := hb0 ⟨x, hx, rfl⟩
    linarith

  obtain ⟨ψ, hψ, hψ0, hcut⟩ := hPsi X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) a hE hExh
  have hψc : Continuous ψ := smoothReal_continuous n X.z hz _ hψ
  have hdc : Continuous (fun x => dSqR n X.z ψ x) := by
    unfold dSqR
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact ((Smooth.continuous n X.z hz _ (Smooth.d n X.z j _ hψ)).norm).pow 2

  obtain ⟨R1, hR1, hR1χ⟩ := hShell X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) ph ψ v a hEc hExh
    (smoothReal_continuous n X.z hz _ hph) hψc hv
  set g : M → ℝ := fun x => max (2 * ψ x) ((1 + 1 / ε) * dSqR n X.z ψ x) with hg
  have hgc : Continuous g := (continuous_const.mul hψc).max (continuous_const.mul hdc)
  set R : ℝ → ℝ := fun t => max (R1 t) (sSup (g '' {x | X.e x + ‖X.z x‖ ^ 2 ≤ t})) with hR
  have hRb : ∀ b : ℝ, BddAbove (R '' Iic b) := by
    intro b
    obtain ⟨B1, hB1⟩ := hR1 b
    obtain ⟨B, hB⟩ := (hExh b).bddAbove_image hgc.continuousOn
    refine ⟨max B1 (max B 0), ?_⟩
    rintro y ⟨t, ht, rfl⟩
    refine max_le_max (hB1 ⟨t, ht, rfl⟩) (sSup_image_le_max g _ B ?_)
    intro x hx
    exact hB ⟨x, (show X.e x + ‖X.z x‖ ^ 2 ≤ b from le_trans hx ht), rfl⟩
  have hgR : ∀ x, g x ≤ R (X.e x + ‖X.z x‖ ^ 2) := by
    intro x
    refine le_max_of_le_right (le_csSup ((hExh _).bddAbove_image hgc.continuousOn) ⟨x, ?_, rfl⟩)
    exact (le_refl (X.e x + ‖X.z x‖ ^ 2))

  obtain ⟨χ, hχ, hχa, hχ0, hχ1, hχ2, hχR⟩ := hChi a R hRb
  have hχs : SmoothR n X.z (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) := SmoothR.comp n X.z χ hχ _ hE
  refine ⟨fun x => ph x + χ (X.e x + ‖X.z x‖ ^ 2), ψ, fun y => X.e y + ‖X.z y‖ ^ 2,
    {x | X.e x + ‖X.z x‖ ^ 2 < a}, SmoothR.add n X.z _ _ hph hχs, hψ, hEc, hcut,
    isOpen_lt hEc continuous_const, hCa, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    refine ⟨?_, (hψ0 x (by linarith)).1⟩
    show ph x + χ (X.e x + ‖X.z x‖ ^ 2) = ph x
    rw [hχa _ hx.le, add_zero]
  · intro x
    have : 2 * ψ x ≤ χ (X.e x + ‖X.z x‖ ^ 2) := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).1, mul_zero]; exact hχ0 _
      · push Not at h
        exact ((le_max_left _ _).trans (hgR x)).trans (hχR _ h.le).1
    linarith
  · intro x ξ
    have hχ2' : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
    rw [levi_add n X.z ph (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) (SmoothR.ckR n X.z 2 _ hph)
      (SmoothR.ckR n X.z 2 _ hχs) x ξ, Complex.add_re,
      hChain X.z hz χ (fun y => X.e y + ‖X.z y‖ ^ 2) hχ2' hE x ξ, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
    have hs : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h1 : (1 + 1 / ε) * dSqR n X.z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).2, mul_zero, zero_mul]
        exact mul_nonneg (hχ1 _) hs
      · push Not at h
        exact mul_le_mul_of_nonneg_right
          (((le_max_right _ _).trans (hgR x)).trans (hχR _ h.le).2) hs
    have h2 : deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) *
          (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re :=
      mul_le_mul_of_nonneg_left (hLeviE x ξ) (hχ1 _)
    have h3 : 0 ≤ deriv (deriv χ) (X.e x + ‖X.z x‖ ^ 2) *
        ‖dDot n X.z (fun y => ((X.e y + ‖X.z y‖ ^ 2 : ℝ) : ℂ)) x ξ‖ ^ 2 :=
      mul_nonneg (hχ2 _) (sq_nonneg _)
    linarith
  · refine ⟨hv.aestronglyMeasurable, ?_⟩
    exact hR1χ χ hχ0 (fun t ht => (hχR t ht).1.trans' (le_max_left _ _))

end

end ReciprocityTheory.L2DbarEstimates.F
end
