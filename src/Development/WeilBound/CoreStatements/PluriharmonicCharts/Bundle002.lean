module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.SecondDerivativeOfEventuallyEq
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_hess

noncomputable def tl (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℝ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℂ) (Fin.succ i)

theorem tl_apply (d : ℕ) (z : Fin (d + 1) → ℂ) : tl d z = Fin.tail z := rfl

theorem tl_cons (d : ℕ) (a : ℂ) (y : Fin d → ℂ) : tl d (Fin.cons a y) = y := by
  ext i; simp [tl]

theorem tl_zero (d : ℕ) : tl d (Pi.single 0 1) = 0 := by
  ext i; simp [tl]

theorem tl_zero' (d : ℕ) : tl d (Complex.I • Pi.single 0 1) = 0 := by
  ext i; simp [tl]

theorem tl_succ (d : ℕ) (j : Fin d) : tl d (Pi.single j.succ 1) = Pi.single j 1 := by
  rw [tl_apply]
  ext i
  simp [Fin.tail, Pi.single_apply]

theorem tl_succ' (d : ℕ) (j : Fin d) :
    tl d (Complex.I • Pi.single j.succ 1) = Complex.I • Pi.single j 1 := by
  rw [tl_apply]
  ext i
  simp [Fin.tail, Pi.single_apply]

theorem xi_eq (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) :
    xiPot G a = -Real.log ((G 0 0).re + a.re * ((G 0 1).re + (G 1 0).re)
        + a.im * ((G 1 0).im + -(G 0 1).im) + (a.re * a.re + a.im * a.im) * (G 1 1).re)
      + (1 / 2) * Real.log ((G 0 0).re * (G 1 1).re + -((G 0 0).im * (G 1 1).im)
        + -((G 0 1).re * (G 1 0).re) + (G 0 1).im * (G 1 0).im) := by
  have h1 : (herm2 G ![1, a] ![1, a]).re = (G 0 0).re + a.re * ((G 0 1).re + (G 1 0).re)
        + a.im * ((G 1 0).im + -(G 0 1).im) + (a.re * a.re + a.im * a.im) * (G 1 1).re := by
    simp [herm2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have h2 : G.det.re = (G 0 0).re * (G 1 1).re + -((G 0 0).im * (G 1 1).im)
        + -((G 0 1).re * (G 1 0).re) + (G 0 1).im * (G 1 0).im := by
    simp [Matrix.det_fin_two]
    ring
  rw [xiPot, h1, h2]

theorem jet (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) (h1 : G y = 1)
    (h0 : ∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) (a : ℂ)
    (A B : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ)
    (hA : ∀ p q, A p q = fderiv ℝ (fderiv ℝ (fun y' => (G y' p q).re)) y)
    (hB : ∀ p q, B p q = fderiv ℝ (fderiv ℝ (fun y' => (G y' p q).im)) y) :
    ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧
    ∀ u v, fderiv ℝ (fderiv ℝ (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)))
        (Fin.cons a y) u v =
      -((1 + (a.re ^ 2 + a.im ^ 2))⁻¹ * (A 0 0 (tl d u) (tl d v)
          + a.re * (A 0 1 (tl d u) (tl d v) + A 1 0 (tl d u) (tl d v))
          + a.im * (B 1 0 (tl d u) (tl d v) - B 0 1 (tl d u) (tl d v))
          + (a.re ^ 2 + a.im ^ 2) * A 1 1 (tl d u) (tl d v)
          + 2 * ((u 0).re * (v 0).re + (u 0).im * (v 0).im))
        - (2 * a.re * (u 0).re + 2 * a.im * (u 0).im) * (2 * a.re * (v 0).re + 2 * a.im * (v 0).im)
          / (1 + (a.re ^ 2 + a.im ^ 2)) ^ 2)
        + (1 / 2) * (A 0 0 (tl d u) (tl d v) + A 1 1 (tl d u) (tl d v)) := by
  have hT : tl d (Fin.cons a y) = y := tl_cons d a y
  have hJ : ∀ (l : ℂ →L[ℝ] ℝ) (p q : Fin 2), J (fun z : Fin (d + 1) → ℂ => l (G (tl d z) p q))
      (Fin.cons a y) (l (G y p q)) (fun _ => 0)
      (fun u w => fderiv ℝ (fderiv ℝ fun y' => l (G y' p q)) y (tl d u) (tl d w)) := by
    intro l p q
    refine J.comp (tl d) (f := fun y' => l (G y' p q)) (v := l (G y p q)) (L := fun _ => 0)
      (B := fun u w => fderiv ℝ (fderiv ℝ fun y' => l (G y' p q)) y u w) ?_
    rw [hT]
    exact J.atom (hC p q) (h0 p q) l
  have hRe : ∀ p q, J (fun z : Fin (d + 1) → ℂ => Complex.reCLM (G (tl d z) p q))
      (Fin.cons a y) (if p = q then 1 else 0) (fun _ => 0) (fun u w => A p q (tl d u) (tl d w)) := by
    intro p q
    refine (hJ Complex.reCLM p q).congr ?_ (fun _ => rfl) ?_
    · rw [h1]
      by_cases h : p = q
      · subst h
        simp
      · simp [h, Matrix.one_apply_ne h]
    · intro u w
      rw [hA]
      rfl
  have hIm : ∀ p q, J (fun z : Fin (d + 1) → ℂ => Complex.imCLM (G (tl d z) p q))
      (Fin.cons a y) 0 (fun _ => 0) (fun u w => B p q (tl d u) (tl d w)) := by
    intro p q
    refine (hJ Complex.imCLM p q).congr ?_ (fun _ => rfl) ?_
    · rw [h1]
      by_cases h : p = q
      · subst h
        simp
      · simp [Matrix.one_apply_ne h]
    · intro u w
      rw [hB]
      rfl
  have hx : J (fun z : Fin (d + 1) → ℂ => (Complex.reCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℂ) 0)) z)
      (Fin.cons a y) a.re (fun u => (u 0).re) (fun _ _ => 0) :=
    (J.clm _ _).congr (by simp) (fun u => by simp) (fun _ _ => rfl)
  have hw : J (fun z : Fin (d + 1) → ℂ => (Complex.imCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℂ) 0)) z)
      (Fin.cons a y) a.im (fun u => (u 0).im) (fun _ _ => 0) :=
    (J.clm _ _).congr (by simp) (fun u => by simp) (fun _ _ => rfl)
  have key := main_jet hx hw (by simpa using hRe 0 0) (by simpa using hRe 0 1)
    (by simpa using hRe 1 0) (by simpa using hRe 1 1) (hIm 0 0) (hIm 0 1) (hIm 1 0) (hIm 1 1)
    (φ := fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (fun z => by
      simp only [tl_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, ContinuousLinearMap.proj_apply]
      exact xi_eq _ _)
  exact key

noncomputable def hm {d : ℕ} (H : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin d) (Fin d) ℂ := fun i j =>
  ((H (Pi.single i 1) (Pi.single j 1)
      + H (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1) : ℝ) +
    Complex.I * ((H (Pi.single i 1) (Complex.I • Pi.single j 1)
      - H (Complex.I • Pi.single i 1) (Pi.single j 1) : ℝ))) / 4

end PositivityTheory.Xgp.fib_hess
end

section

namespace PositivityTheory.Xgp.fib_stereo

open MeasureTheory Set GroundTheory.Heights₂.Heights.FlagBundles
open scoped ENNReal NNReal

noncomputable section

def ht (ρ : ℝ) : ℝ := (1 - ρ ^ 2) / (1 + ρ ^ 2)

def nF (a : ℂ) : Fin 3 → ℝ :=
  fun i => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def nE (a : ℂ) : E3 := WithLp.toLp 2 (nF a)

def wt (a : ℂ) : ℝ := Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2

theorem continuous_nF : Continuous nF := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [nF] <;> fun_prop (disch := (intro x; positivity))

theorem measurable_nE : Measurable nE :=
  ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp continuous_nF).measurable

theorem nE_polar {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    nE (Complex.polarCoord.symm (ρ, θ)) = spherePoint (ht ρ) θ := by
  set a := Complex.polarCoord.symm (ρ, θ) with ha
  have hn : ‖a‖ ^ 2 = ρ ^ 2 := by
    rw [ha, Complex.norm_polarCoord_symm, sq_abs]
  have hre : a.re = ρ * Real.cos θ := by rw [ha]; simp [Complex.cos_ofReal_re]
  have him : a.im = ρ * Real.sin θ := by rw [ha]; simp [Complex.sin_ofReal_re]
  have hpos : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
  have hsq : Real.sqrt (1 - ht ρ ^ 2) = 2 * ρ / (1 + ρ ^ 2) := by
    rw [show 1 - ht ρ ^ 2 = (2 * ρ / (1 + ρ ^ 2)) ^ 2 by unfold ht; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  unfold nE spherePoint
  ext i
  fin_cases i
  · show 2 * a.re / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.cos θ
    rw [hre, hn, hsq]; ring
  · show 2 * a.im / (1 + ‖a‖ ^ 2) = Real.sqrt (1 - ht ρ ^ 2) * Real.sin θ
    rw [him, hn, hsq]; ring
  · show (1 - ‖a‖ ^ 2) / (1 + ‖a‖ ^ 2) = ht ρ
    rw [hn]; rfl

theorem ht_image : ht '' Ioi 0 = Ioo (-1) 1 := by
  ext y
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    have hρ' : (0 : ℝ) < ρ := hρ
    have hp : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
    unfold ht
    constructor
    · rw [lt_div_iff₀ hp]; nlinarith
    · rw [div_lt_one hp]; nlinarith
  · rintro ⟨h1, h2⟩
    have hq : 0 < (1 - y) / (1 + y) := div_pos (by linarith) (by linarith)
    refine ⟨Real.sqrt ((1 - y) / (1 + y)), Real.sqrt_pos.2 hq, ?_⟩
    unfold ht
    rw [Real.sq_sqrt hq.le]
    have : (1 : ℝ) + y ≠ 0 := by linarith
    field_simp
    ring

theorem ht_injOn : InjOn ht (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  unfold ht at hxy
  rw [div_eq_div_iff (by positivity) (by positivity)] at hxy
  have h2 : x ^ 2 = y ^ 2 := by nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

theorem hasDerivAt_ht (ρ : ℝ) : HasDerivAt ht (-(4 * ρ) / (1 + ρ ^ 2) ^ 2) ρ := by
  have hp : (1 : ℝ) + ρ ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * ρ)) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * ρ) ρ := by
    simpa using (hasDerivAt_pow 2 ρ).const_add 1
  have := h1.div h2 hp
  have e : (fun x : ℝ => 1 - x ^ 2) / (fun x : ℝ => 1 + x ^ 2) = ht := by
    funext x; rfl
  rw [e] at this
  exact this.congr_deriv (by ring)

theorem lintegral_ht (G : ℝ → ℝ≥0∞) :
    ∫⁻ c in Ioo (-1 : ℝ) 1, G c =
      ∫⁻ ρ in Ioi 0, ENNReal.ofReal (4 * ρ / (1 + ρ ^ 2) ^ 2) * G (ht ρ) := by
  rw [← ht_image, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun ρ _ => (hasDerivAt_ht ρ).hasDerivWithinAt) ht_injOn G]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ' : (0 : ℝ) < ρ := hρ
  rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]

theorem continuous_ht : Continuous ht := by
  unfold ht
  fun_prop (disch := (intro x; positivity))

theorem lintegral_stereo (g : E3 → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ a : ℂ, ENNReal.ofReal (wt a) * g (nE a) =
      (ENNReal.ofReal (4 * Real.pi))⁻¹ *
        ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ) := by
  have hsp := SphereLongitudeCoordinates.continuous_spherePoint
  set F : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (p.1 * (Real.pi⁻¹ / (1 + p.1 ^ 2) ^ 2)) * g (spherePoint (ht p.1) p.2) with hF
  have hFm : Measurable F := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact hg.comp (hsp.measurable.comp
        ((continuous_ht.measurable.comp measurable_fst).prodMk measurable_snd))
  have hC : (ENNReal.ofReal (4 * Real.pi))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal p.1 •
      (ENNReal.ofReal (wt (Complex.polarCoord.symm p)) * g (nE (Complex.polarCoord.symm p))) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, F p := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
    obtain ⟨ρ, θ⟩ := p
    have hp1 : (0 : ℝ) < ρ := hp.1
    simp only [smul_eq_mul, hF]
    rw [nE_polar hp1.le, ← mul_assoc, ← ENNReal.ofReal_mul hp1.le]
    unfold wt
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hFm.aemeasurable,
    lintegral_lintegral_swap hFm.aemeasurable, ← lintegral_const_mul' _ _ hC]
  refine lintegral_congr fun θ => ?_
  rw [lintegral_ht (fun c => g (spherePoint c θ)), ← lintegral_const_mul' _ _ hC]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ' : (0 : ℝ) < ρ := hρ
  simp only [hF]
  rw [← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem toSphere_univ : (volume : Measure E3).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
  have h := SphereLongitudeCoordinates.toSphere_preimage (s := (univ : Set E3)) MeasurableSet.univ
  rw [preimage_univ] at h
  rw [h]
  simp [Real.volume_Icc, Real.volume_Ioc]
  rw [show (1 : ℝ) + 1 = 2 by norm_num, ENNReal.ofReal_ofNat]
  ring

theorem per_conv (g : E3 → ℝ≥0∞) :
    ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ) =
      ∫⁻ φ in Ioc 0 (2 * Real.pi), ∫⁻ c in Icc (-1 : ℝ) 1, g (spherePoint c φ) := by
  set h : ℝ → ℝ≥0∞ := fun φ => ∫⁻ c in Icc (-1 : ℝ) 1, g (spherePoint c φ) with hh
  have hper : Function.Periodic h (2 * Real.pi) := fun φ => by
    simp only [hh, SphereLongitudeCoordinates.spherePoint_add_two_pi]
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  calc ∫⁻ φ in Ioo (-Real.pi) Real.pi, ∫⁻ c in Ioo (-1 : ℝ) 1, g (spherePoint c φ)
      = ∫⁻ φ in Ioc (-Real.pi) (-Real.pi + 2 * Real.pi), h φ := by
        rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        refine lintegral_congr fun φ => ?_
        simp only [hh]
        rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
    _ = ∫⁻ b : AddCircle (2 * Real.pi), hper.lift b := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi)]
        rfl
    _ = ∫⁻ φ in Ioc 0 (0 + 2 * Real.pi), h φ := by
        rw [← AddCircle.lintegral_preimage (2 * Real.pi) 0]
        rfl
    _ = _ := by rw [zero_add]

theorem map_stereo :
    (volume.withDensity fun a : ℂ => ENNReal.ofReal (wt a)).map nE =
      sphereMeasure.map (fun m : Sphere2 => (m : E3)) := by
  ext s hs
  rw [Measure.map_apply measurable_nE hs, withDensity_apply _ (measurable_nE hs),
    Measure.map_apply measurable_subtype_coe hs, sphereMeasure, Measure.smul_apply, smul_eq_mul,
    SphereLongitudeCoordinates.toSphere_preimage hs, toSphere_univ, ← per_conv,
    ← lintegral_stereo _ (measurable_one.indicator hs), ← lintegral_indicator (measurable_nE hs)]
  refine lintegral_congr fun a => ?_
  by_cases ha : nE a ∈ s <;> simp [Set.indicator, ha]

end

end PositivityTheory.Xgp.fib_stereo
end
