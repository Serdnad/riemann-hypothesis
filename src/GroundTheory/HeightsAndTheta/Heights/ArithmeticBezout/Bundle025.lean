module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SphereMeanLinearBall

theorem std_norm (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

theorem std_dualNorm (n : ℕ) (y : Fin n → ℂ) :
    (HermNorm.std n).dualNorm y = √(∑ j, ‖y j‖ ^ 2) := by
  simp [HermNorm.dualNorm, HermNorm.std]

theorem sum_sq_nrmv_le (n : ℕ) (w : Fin n → ℂ) :
    ∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 ≤ 1 := by
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : ∀ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 = (∑ j, ‖w j‖ ^ 2)⁻¹ * ‖w j‖ ^ 2 := by
    intro j
    rw [nrmv, std_norm, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hS]
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum]
  rcases eq_or_ne (∑ j, ‖w j‖ ^ 2) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem norm_sum_mul_le (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ≤ √(∑ j, ‖a j‖ ^ 2) * √(∑ j, ‖b j‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem sum_sq_pos {n : ℕ} {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < ∑ j, ‖y j‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h => hy ?_
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖y j‖).mp h.symm
  funext j
  simpa using h0 j (Finset.mem_univ j)

theorem fsLog_nrmv_nonpos (n : ℕ) (y w : Fin n → ℂ) :
    fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0 := by
  rw [fsLog, std_dualNorm]
  refine Real.log_nonpos (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) ?_
  refine div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)
  refine (norm_sum_mul_le n _ _).trans ?_
  have h1 : √(∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact sum_sq_nrmv_le n w
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h1

end SphereMeanLinearBall


open SphereMeanLinearBall in
theorem SphereMeanLinearBall.proof (h1 : SphereMeanLinear.Statement) : SphereMeanLinearBall.Statement := by
  intro n y hy
  set g : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y with hg
  have hpos := sum_sq_pos hy
  set r : ℝ := √(∑ j, ‖y j‖ ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos

  let p : Fin n → ℂ := fun j => ((r : ℂ))⁻¹ * star (y j)
  have hp : ∑ j, ‖p j‖ ^ 2 = 1 := by
    have e : ∀ j, ‖p j‖ ^ 2 = (∑ j, ‖y j‖ ^ 2)⁻¹ * ‖y j‖ ^ 2 := by
      intro j
      show ‖((r : ℂ))⁻¹ * star (y j)‖ ^ 2 = _
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_star, mul_pow,
        inv_pow, hr, Real.sq_sqrt hpos.le]
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, inv_mul_cancel₀ hpos.ne']
  have hkey : ∀ a : Fin n → ℂ, Real.log ‖∑ j, a j * star (p j)‖ = fsLog (HermNorm.std n) a y := by
    intro a
    have e : ∑ j, a j * star (p j) = ((r : ℂ))⁻¹ * ∑ j, a j * y j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [p, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e, fsLog, std_dualNorm, ← hr, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr0.le, div_eq_inv_mul]

  let e := (Equiv.uniqueProd (Fin n) (Fin 1)).symm
  let L1 : (Fin 1 × Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL1 : ∀ u, (fun j => u (0, j)) = L1 u := by
    intro u
    funext j
    simp [L1, e]
  have hS : {u : Fin 1 × Fin n → ℂ | ∀ i, (HermNorm.std n).norm (fun j => u (i, j)) < 1} =
      L1 ⁻¹' ballH (HermNorm.std n) := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, ballH, Fin.forall_fin_one, hL1]
  have hmean : ⨍ w in ballH (HermNorm.std n), g w = -(harmonic (n - 1) : ℝ) / 2 := by
    rw [← h1 n p hp, sphereMean, hS,
      ← SphereMean.setAverage_comp_linearEquiv volume volume L1 (ballH (HermNorm.std n)) g]
    congr 1
    funext u
    rw [hkey]
    simp only [hg]
    rw [← hL1 u]
    rfl
  refine ⟨?_, fun w => fsLog_nrmv_nonpos n y w, hmean⟩
  rcases eq_or_ne (harmonic (n - 1)) 0 with hH | hH
  ·
    have hn1 : n - 1 = 0 := by
      by_contra hne
      exact (harmonic_pos hne).ne' hH
    have hn : n = 1 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        exact absurd (Subsingleton.elim y 0) hy
      · omega
    subst hn
    have hz : g = 0 := by
      funext w
      simp only [hg, Pi.zero_apply, fsLog, std_dualNorm, nrmv, std_norm, Fin.sum_univ_one]
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), norm_mul, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      have hy0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
      rcases eq_or_ne (w 0) 0 with hw | hw
      · simp [hw]
      · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), one_mul,
          div_self (norm_ne_zero_iff.mpr hy0), Real.log_one]
    rw [hz]
    exact integrableOn_zero
  ·
    by_contra hni
    have h0 : ⨍ w in ballH (HermNorm.std n), g w = 0 := by
      rw [setAverage_eq, integral_undef hni, smul_zero]
    rw [hmean] at h0
    exact hH (by exact_mod_cast (by linarith : (harmonic (n - 1) : ℝ) = 0))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeAverage.proof (h1 : ConeIntegralMass.Statement) (h2 : ChowDegreePos.Statement)
    (h3 : ConeFubini.Statement) (h4 : FsLogAverage.Statement) (h5 : FsLogMeasurable.Statement) :
    ConeAverage.Statement := by
  intro n e δ h W g hW hg hδ
  set S : Set (EuclideanSpace ℂ (Fin n)) :=
    {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0} with hS
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) with hν
  set D : ℝ := (ν {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal
    with hD
  have hδ1 : 1 ≤ δ := h2 n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have hmass : (ν S).toReal / D = δ := by
    have hm := h1 n e δ h W g hW hg hδ
    unfold coneIntegral at hm
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] at hm
    exact hm
  have hfin : ν S ≠ ⊤ := by
    intro hinf
    rw [hinf, ENNReal.toReal_top, zero_div] at hmass
    have : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
    exact this hmass.symm
  have : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.2 hfin
  have hcone : ∀ φ : (Fin n → ℂ) → ℝ,
      coneIntegral h W e φ = (∫ y, φ (h.pointOf y) ∂(ν.restrict S)) / D := fun _ => rfl
  have hzero : ν.restrict S {(0 : EuclideanSpace ℂ (Fin n))} = 0 := by
    refine nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le S _).trans_eq ?_)
    have hd : (((2 * (e + 1) : ℕ) : ℝ)) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) := by simp
    rw [hν, hd]
    apply hausdorffMeasure_of_dimH_lt
    rw [dimH_singleton]
    exact_mod_cast (by omega : 0 < 2 * (e + 1))
  have hae : ∀ᵐ y ∂(ν.restrict S), y ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  have hF := h3 n h (ν.restrict S) (fun v y => fsLog h (nrmv h v) (h.pointOf y))
    (-(harmonic (n - 1) : ℝ) / 2)
    ((harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal) (h5 n h)
    (hae.mono fun y hy => by
      obtain ⟨hi, habs, hmean⟩ := h4 n h y hy
      exact ⟨hi, habs.le, hmean⟩)
  obtain ⟨hFi, hFm⟩ := hF
  have hfun : (fun v => coneIntegral h W e (fsLog h (nrmv h v))) =
      fun v => (∫ y, fsLog h (nrmv h v) (h.pointOf y) ∂(ν.restrict S)) / D := by
    funext v
    exact hcone _
  rw [hfun]
  refine ⟨hFi.div_const D, ?_⟩
  rw [setAverage_eq, integral_div, ← smul_div_assoc, ← setAverage_eq, hFm,
    Measure.restrict_apply_univ, mul_div_assoc, hmass]
  ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem CycleAverage.proof (h1 : ConeAverage.Statement) : CycleAverage.Statement := by
  intro n e δ h Z f hd
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  have hW : ∀ W ∈ Z.support,
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) =
          -(δW W * (harmonic (n - 1) : ℝ)) / 2 :=
    fun W hm => h1 n e (δW W) h W (g W) (hd.prime W hm) (hg W hm) (hδW W hm)
  have hint : ∀ W ∈ Z.support,
      IntegrableOn (fun v => (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) :=
    fun W hm => (hW W hm).1.const_mul _
  unfold cycleIntegral
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [setAverage_eq, integral_finsetSum _ hint, Finset.smul_sum]
  have hterm : ∀ W ∈ Z.support,
      (volume.real (ballH h))⁻¹ • ∫ v in ballH h, (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v)) =
        (Z W : ℝ) * (-(δW W * (harmonic (n - 1) : ℝ)) / 2) := by
    intro W hm
    rw [integral_const_mul, ← (hW W hm).2, setAverage_eq, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hδ : (δ : ℝ) = ∑ W ∈ Z.support, (Z W : ℝ) * (δW W : ℝ) := by
    rw [← hsum]; push_cast; rfl
  rw [hδ, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartLengthAlgClosed.proof (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegreeAlgClosed.Statement) :
    ChartLengthAlgClosed.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  classical

  have hpt : specFirst f t ∉ p := by
    rw [hp, Ideal.mem_span_singleton]
    exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₃ F n e I f t p hI hf hpt
  rw [h₄ (Localization.AtPrime p) (ChartLoc I t e p)
    (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]
  refine finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_
  · have h := h₅ F n e I f t u q p hI hf hu hq hp hqt
    convert h using 1
    ext W
    simp
  · intro W hW _
    obtain ⟨hWs, hWq⟩ := Finset.mem_filter.mp hW
    have hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
      rw [Finsupp.mem_support_iff] at hWs
      by_contra h
      exact hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
    have hqW : q ∈ incIdeal W e := hWq ▸ Ideal.mem_span_singleton_self q
    have htW : linForm t ∉ W := fun h => by
      have hIW : I ≤ W := le_trans le_sup_left hrel.1.1.2
      have := h₂ F n e I W f t hf hIW h
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    obtain ⟨_, hord⟩ := h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hlen := h₇ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W := by
      simp [divCycle, fundCycle, Finsupp.onFinset_apply, hrel]
    rw [hlen, mul_one, hdiv]
    exact hord

end

end GroundTheory.Heights₂.Heights
end
