module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric

noncomputable section

theorem taylor_two_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun z => f (x + z) - f x - fderiv ℝ f x z - fderiv ℝ (fderiv ℝ f) x z z / 2)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by
  set L := fderiv ℝ f x
  set H := fderiv ℝ (fderiv ℝ f) x with hHdef
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hH : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.1 hH
  have htend : Tendsto (fun z : E => x + z) (𝓝 0) (𝓝 x) := by
    have : Continuous fun z : E => x + z := continuous_const.add continuous_id
    simpa using this.tendsto (0 : E)
  have hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f (x + z) :=
    htend.eventually ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp))
  refine isLittleO_iff.2 fun ε hε => ?_
  have hb := (isLittleO_iff.1 ho hε).and hdiff
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hb
  filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz
  set g : E → ℝ := fun w => f (x + w) - f x - L w - (2 : ℝ)⁻¹ • H w w with hg
  have hderiv : ∀ w ∈ ball (0 : E) δ, HasFDerivAt g (fderiv ℝ f (x + w) - L - H w) w := by
    intro w hw
    have h1 : HasFDerivAt (fun w => f (x + w)) ((fderiv ℝ f (x + w)).comp
        (ContinuousLinearMap.id ℝ E)) w :=
      (hball w hw).2.hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)
    have h2 : HasFDerivAt (fun w => H w w) ((H w).comp (ContinuousLinearMap.id ℝ E) + H.flip w) w :=
      H.hasFDerivAt.clm_apply (hasFDerivAt_id w)
    have h3 := ((h1.sub_const (f x)).sub L.hasFDerivAt).sub (h2.const_smul (2 : ℝ)⁻¹)
    refine h3.congr_fderiv ?_
    ext v
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    have := hsymm v w
    rw [← hHdef] at this
    rw [this]
    ring
  have hz' : ‖z‖ < δ := by simpa using hz
  have hsub : closedBall (0 : E) ‖z‖ ⊆ ball 0 δ := closedBall_subset_ball hz'
  have hbound : ∀ w ∈ closedBall (0 : E) ‖z‖, ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖z‖ := by
    intro w hw
    have hw' := (hball w (hsub hw)).1
    have hwz : ‖w‖ ≤ ‖z‖ := by simpa using hw
    calc ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖w‖ := hw'
      _ ≤ ε * ‖z‖ := by gcongr
  have hz0 : z ∈ closedBall (0 : E) ‖z‖ := by simp
  have hmvt := (convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw => (hderiv w (hsub hw)).hasFDerivWithinAt) hbound
    (mem_closedBall_self (norm_nonneg z)) hz0
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmvt
  have : g z = f (x + z) - f x - L z - H z z / 2 := by
    simp only [hg, smul_eq_mul]; ring
  rw [← this, norm_pow, norm_norm]
  calc ‖g z‖ ≤ ε * ‖z‖ * ‖z‖ := hmvt
    _ = ε * ‖z‖ ^ 2 := by ring

def complexLinearCoeffs {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) : Fin D → ℂ :=
  fun j => (L (Pi.single j 1) : ℂ) - Complex.I * (L (Complex.I • Pi.single j 1) : ℂ)

theorem re_complexLinearCoeffs_dot {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (complexLinearCoeffs L ⬝ᵥ z).re = L z := by
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ))) := by
    ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  conv_rhs => rw [hz]

  simp only [map_sum, map_add (f := _), map_smul, dotProduct, Complex.re_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [complexLinearCoeffs, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

def complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun j k =>
    let ej : Fin D → ℂ := Pi.single j 1
    let ek : Fin D → ℂ := Pi.single k 1
    ((H ej ek - H (Complex.I • ej) (Complex.I • ek) : ℝ) -
      Complex.I * ((H ej (Complex.I • ek) + H (Complex.I • ej) ek : ℝ))) / 4

theorem re_dot_complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (z : Fin D → ℂ) :
    (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re = (H z z - H (Complex.I • z) (Complex.I • z)) / 4 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin D → (Fin D → ℂ), c = fun j => (z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin D → (Fin D → ℂ), d = fun j =>
      (z j).re • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) +
      (-(z j).im) • (Pi.single j 1 : Fin D → ℂ) := ⟨_, rfl⟩
  have hz : z = ∑ j, c j := by
    rw [hc]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have hIz : Complex.I • z = ∑ j, d j := by
    rw [hd]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have expand : ∀ c : Fin D → (Fin D → ℂ),
      H (Finset.sum Finset.univ c) (Finset.sum Finset.univ c) = ∑ i, ∑ k, H (c i) (c k) := by
    intro c

    simp only [map_sum, _root_.sum_apply]
    rw [Finset.sum_comm]
  have e1 : H z z = ∑ i, ∑ k, H (c i) (c k) := by
    calc H z z = H (∑ j, c j) (∑ j, c j) := by rw [← hz]
      _ = _ := expand c
  have e2 : H (Complex.I • z) (Complex.I • z) = ∑ i, ∑ k, H (d i) (d k) := by
    rw [hIz]; exact expand d
  have hR : (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re =
      ∑ i, ∑ k, (z i * (complexQuadMatrix H i k * z k)).re := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
  rw [hR, e1, e2, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  subst hc hd
  simp only [map_add (f := _), map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [complexQuadMatrix, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem ComplexTaylorTwo.proof : ComplexTaylorTwo.Statement := by
  intro D ψ y₀ hψ
  refine ⟨complexLinearCoeffs (fderiv ℝ ψ y₀), complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀), ?_⟩
  refine (taylor_two_isLittleO hψ).congr_left fun z => ?_
  have h1 := re_complexLinearCoeffs_dot (fderiv ℝ ψ y₀) z
  have h2 := re_dot_complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀) z
  have h3 := ReciprocityTheory.AnForm.M.re_star_dot_hessC ψ y₀ (star z)
  rw [star_star] at h3
  rw [Complex.add_re, h1, h2, h3]
  unfold levi
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

lemma gaussDiscMass_pos {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) : 0 < gaussDiscMass lam R := by
  unfold gaussDiscMass
  split_ifs with h
  · positivity
  · have hl : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h)
    have : Real.exp (-lam * R ^ 2) < 1 :=
      (Real.exp_lt_exp.2 (by nlinarith [sq_pos_of_pos hR] : -lam * R ^ 2 < 0)).trans_eq Real.exp_zero
    have : 0 < 1 - Real.exp (-lam * R ^ 2) := by linarith
    positivity

theorem UniformBergmanBound.proof (hP : PolydiscSubmean.Statement)
    (hC : ChartTaylorCover.Statement) : UniformBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV _ _
  obtain ⟨r, hr, M, c, hc, hcov⟩ := hC A L W₀ W₁ dV
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hI : 0 < gaussDiscMass M' r := gaussDiscMass_pos hM'0 hr
  have hK : 0 < c * gaussDiscMass M' r ^ D := by positivity
  refine ⟨(c * gaussDiscMass M' r ^ D)⁻¹, fun n hn t ht V _ hV x => ?_⟩
  have hn0 : 0 < n := hn
  have hnD : 0 < (n : ℝ) ^ D := by positivity
  obtain ⟨j, hxj, hball, hdens, hW⟩ := hcov x
  obtain ⟨ℓ₀, h₀⟩ := hW W₀ (by simp)
  obtain ⟨ℓ₁, h₁⟩ := hW W₁ (by simp)
  set e := A.chart j
  set y := e x
  set ψ : (Fin D → ℂ) → ℝ := (W₀.lerp W₁ t).φ j ∘ e.symm with hψ
  have hψy : ψ y = (W₀.lerp W₁ t).φ j x := by simp [hψ, y, e.left_inv hxj]
  have hsub : Metric.closedBall y r ⊆ e.target ∩ e.symm ⁻¹' e.source :=
    fun w hw => ⟨hball hw, e.map_target (hball hw)⟩

  have hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
      ψ (y + z) ≤ ψ y + (ℓ₀ + t • (ℓ₁ - ℓ₀)) z + M' * ∑ i, ‖z i‖ ^ 2 := by
    intro z hz
    have a₀ := h₀ z hz
    have a₁ := h₁ z hz
    have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
    have hMM : M * ∑ i, ‖z i‖ ^ 2 ≤ M' * ∑ i, ‖z i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    rw [hψy]
    simp only [hψ, Function.comp, Weight.lerp, FunLike.coe_add,
      FunLike.coe_smul, FunLike.coe_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    nlinarith [mul_le_mul_of_nonneg_left a₀ ht1, mul_le_mul_of_nonneg_left a₁ ht0]

  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV s.2
  have hs' : _ ∧ _ ∧ _ := hs
  set F : (Fin D → ℂ) → ℂ := (s : Fin A.n → X → ℂ) j ∘ e.symm with hF
  have hFa : AnalyticOnNhd ℂ F (Metric.closedBall y r) := ((hs'.1 j) j).mono hsub
  have hψc : ContinuousOn ψ (Metric.closedBall y r) :=
    (((W₀.lerp W₁ t).smooth j) j).continuousOn.mono hsub
  have hloc := gauss_local hP hn0 hr hM'0 hFa hψc (ℓ₀ + t • (ℓ₁ - ℓ₀)) hT
  have hρr : r / Real.sqrt n ≤ r := div_le_self hr.le (Real.one_le_sqrt.2 (by exact_mod_cast hn))
  have hBr : Metric.closedBall y (r / Real.sqrt n) ⊆ Metric.closedBall y r :=
    Metric.closedBall_subset_closedBall hρr
  have hlow := le_l2NormSq_of_chart (W₀.lerp W₁ t) dV hs j
    Metric.isClosed_closedBall.measurableSet (hBr.trans hball) hc.le
    (fun w hw => hdens w (hBr hw))
  have hpt : ptNormSq (W₀.lerp W₁ t) n s x = ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) := by
    rw [ptNormSq_eq_of_mem _ hs j hxj, hψy]
    simp [hF, y, e.left_inv hxj]
  have hmain : ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c ≤
      sectionL2NormSq (W₀.lerp W₁ t) dV n s := by
    rw [hpt]
    calc _ = c * (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ *
          gaussDiscMass M' r ^ D) := by ring
      _ ≤ c * ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) :=
          mul_le_mul_of_nonneg_left hloc hc.le
      _ = _ := rfl
      _ ≤ _ := hlow
  have hl0 : 0 ≤ sectionL2NormSq (W₀.lerp W₁ t) dV n s := sectionL2NormSq_nonneg _ _ _ _
  rcases hl0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; positivity
  rw [div_le_iff₀ hpos]
  have hp0 : 0 ≤ ptNormSq (W₀.lerp W₁ t) n s x := ptNormSq_nonneg _ _ _ _
  calc ptNormSq (W₀.lerp W₁ t) n s x
      = (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D *
          (ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c) := by
        field_simp
    _ ≤ (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D * sectionL2NormSq (W₀.lerp W₁ t) dV n s :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem aeval_mul_blockScale_of_isMultiHomog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [CommRing Ω] {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (t : K → Ω)
    (y : (Σ k, ι k) → Ω) :
    aeval (fun p => y p * t p.1) f = aeval y f * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ x, t k ^ d ⟨k, x⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal {K : Type*} [Fintype K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω] {y : (Σ k, ι k) → Ω} {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) (t : K → Ω) : aeval (fun p => y p * t p.1) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have hcomp : ((aeval t).restrictScalars ℤ).comp (mConeMap y) = aeval (fun p => y p * t p.1) :=
    MvPolynomial.algHom_ext fun p => by simp [mConeMap]
  rw [← hcomp, AlgHom.comp_apply, h0, map_zero]

theorem ChartPrimePowerInverse.proof : ChartPrimePowerInverse.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L hhom hL p hp j hj
  obtain ⟨N, hN⟩ := PullConeNull.proof K ι Ω y D L hL
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have key : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ a : ℕ,
      (p : Ω) ^ a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro c hc
    set R := Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) with hR
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hYdef
    have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have hpR : ∀ n : ℕ, (p : Ω) ^ n ∈ R := fun n => R.pow_mem (natCast_mem R p) n

    let G : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ a : ℕ, (p : Ω) ^ a * x ∈ R}
        mul_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x * z) = ((p : Ω) ^ a * x) * ((p : Ω) ^ b * z) := by ring
          rw [this]
          exact R.mul_mem ha hb
        add_mem' := by
          rintro x z ⟨a, ha⟩ ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          have : (p : Ω) ^ (a + b) * (x + z) = (p : Ω) ^ b * ((p : Ω) ^ a * x) + (p : Ω) ^ a * ((p : Ω) ^ b * z) := by
            ring
          rw [this]
          exact R.add_mem (R.mul_mem (hpR b) ha) (R.mul_mem (hpR a) hb)
        algebraMap_mem' := by
          intro q
          obtain ⟨b, d', hd', hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.one_lt.ne'
          refine ⟨b, ?_⟩
          have hden' : (q.den : Ω) = (p : Ω) ^ b * (d' : Ω) := by exact_mod_cast hden
          have hd0 : (d' : Ω) ≠ 0 := by
            intro h0
            have : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
            rw [hden', h0, mul_zero] at this
            exact this rfl
          have : (p : Ω) ^ b * algebraMap ℚ Ω q = (q.num : Ω) * (d' : Ω)⁻¹ := by
            rw [eq_ratCast, Rat.cast_def, hden']
            field_simp
          show (p : Ω) ^ b * algebraMap ℚ Ω q ∈ R
          rw [this]
          exact R.mul_mem (intCast_mem R _) (Subring.subset_closure (Or.inr ⟨d', hd', rfl⟩)) }
    have hmemG : ∀ x ∈ R, x ∈ G := fun x hx => ⟨0, by simpa using hx⟩
    let r : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, c q.1⟩
    let χ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval r
    let t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
    have hχG : ∀ g, χ g ∈ G := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C q => simpa [χ] using G.algebraMap_mem q
      | add f g hf hg => simpa using G.add_mem hf hg
      | mul_X f q hf =>
        simpa [χ] using G.mul_mem hf (hmemG _ (Subring.subset_closure (Or.inl (Or.inl ⟨q, rfl⟩))))
    have hχmap : ∀ f : MRing ι,
        χ (map (Int.castRingHom ℚ) f) = aeval (fun q => y q * t q.1) f := by
      intro f
      rw [← algebraMap_int_eq, aeval_map_algebraMap]
      simp only [r, t, div_eq_mul_inv]

    let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) :=
      { carrier := {f | χ f * (Y / aeval y (L j)) ∈ G}
        add_mem' := by
          intro f g hf hg
          simpa [add_mul] using G.add_mem hf hg
        zero_mem' := by simp
        smul_mem' := by
          intro g f hf
          simpa [smul_eq_mul, mul_assoc] using G.mul_mem (hχG g) hf }
    have hIJ : coneNullIdeal y L ≤ J := by
      refine Ideal.span_le.mpr ?_
      rintro f (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_eq_zero_of_mem_mCoordIdeal hf t, zero_mul]
        exact G.zero_mem
      · show χ _ * _ ∈ G
        rw [hχmap, aeval_mul_blockScale_of_isMultiHomog (hhom i) t]
        have : aeval y (L i) * (∏ k, t k ^ e k) * (Y / aeval y (L j)) =
            aeval y (L i) / aeval y (L j) := by
          have hprod : (∏ k, t k ^ e k) = Y⁻¹ := by
            rw [hYdef, ← Finset.prod_inv_distrib]
            exact Finset.prod_congr rfl fun k _ => inv_pow _ _
          rw [hprod]
          field_simp
        rw [this]
        exact hmemG _ (Subring.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩)))
    have h1 := hIJ (hN c)
    have hone : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) = 1 := by
      simp [χ, r, div_self (hc _)]
    obtain ⟨a, ha⟩ : Y / aeval y (L j) ∈ G := by
      have : χ ((∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N) * (Y / aeval y (L j)) ∈ G := h1
      rwa [hone, one_mul] at this
    exact ⟨a, by rw [mul_div_assoc]; exact ha⟩
  choose! a ha using key
  refine ⟨Finset.univ.sup a, fun c hc => ?_⟩
  have hle : a c ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ c)
  have e1 : (p : Ω) ^ Finset.univ.sup a * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) =
      (p : Ω) ^ (Finset.univ.sup a - a c) * ((p : Ω) ^ a c * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j)) := by
    rw [← Nat.sub_add_cancel hle, pow_add, Nat.add_sub_cancel]
    ring
  rw [e1]
  exact Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ p) _) (ha c hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenNearMul.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (W : Ideal (MRingOver S ι)) (d n : K → ℤ) (f g : MRingOver S ι) (δ γ : K → ℕ),
    KH.IsMGraded S ι 𝓜 → W ≤ Module.annihilator (MRingOver S ι) M → IsMultiHomog f δ → IsMultiHomog g γ →
    GenNear S ι 𝓜 d f δ → GenNear S ι (KH.quotPart S W) n g γ → GenNear S ι 𝓜 (d + n) (f * g) (δ + γ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
