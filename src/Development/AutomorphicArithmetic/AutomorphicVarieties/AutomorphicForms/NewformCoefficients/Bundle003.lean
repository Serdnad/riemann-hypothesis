module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

theorem UpperTheory.V.Af.Nf.places :
    UpperTheory.V.Af.Nf.Places := by
  intro w
  have hq := Rat.HeightOneSpectrum.prime_natGenerator w
  have hspan := Rat.HeightOneSpectrum.span_natGenerator w
  have hN : normV w = Rat.HeightOneSpectrum.natGenerator w := by
    unfold normV
    rw [Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hspan).toEquiv,
      Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv, Nat.card_zmod]
  have hP : w.asIdeal =
      Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
    ext x
    rw [Ideal.mem_span_singleton,
      ← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), ← hspan,
      Ideal.mem_span_singleton,
      ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_natCast]
  refine ⟨by rw [hN]; exact hq, by rw [hN]; exact hP, ?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · intro M hM hndvd
    unfold UpperTheory.V.Af.Nf.lev ordI
    have hne : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (by omega : M ≠ 0)
    by_contra hc
    rw [← Ne, Associates.count_ne_zero_iff_dvd hne w.irreducible, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem] at hc
    apply hndvd
    rw [hN, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
      ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) M, Ideal.apply_mem_of_equiv_iff]
    exact hc
end

section

open UpperHalfPlane hiding I
open scoped Manifold ContDiff

private theorem archSm_eval_eq (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (σ : ℂ)
    (x0 : Fin 2 → Fin 2 → ℝ)
    (hD : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0)
    (hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0)
    (him : 0 < (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im) :
    ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ)) *
        f (ofComplex (σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
          ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))))) x0 := by
  have hre : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => ((x i j : ℝ) : ℂ)) :=
    fun i j => Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have hDd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  have hcd : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) :=
    ((hre 1 0).mul contDiff_const).add (hre 1 1)
  have had : ContDiff ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      (x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) :=
    ((hre 0 0).mul contDiff_const).add (hre 0 1)
  have habs : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      |x 0 0 * x 1 1 - x 0 1 * x 1 0|) x0 :=
    ContDiffAt.comp (g := fun t : ℝ => |t|) x0 (contDiffAt_abs hD) hDd.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((|x 0 0 * x 1 1 - x 0 1 * x 1 0| ^ ((k : ℝ) / 2) : ℝ) : ℂ)) x0 := by
    refine Complex.ofRealCLM.contDiff.contDiffAt.comp x0 ?_
    exact habs.rpow_const_of_ne (abs_ne_zero.mpr hD)
  have h2 : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-(k : ℤ))) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-(k : ℤ)))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-(k : ℤ)) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact (hz.contDiffAt.restrict_scalars ℝ).comp x0 hcd.contDiffAt
  have hinv : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) ^ (-1 : ℤ)) x0 := by
    have hz : AnalyticAt ℂ (fun z : ℂ => z ^ (-1 : ℤ))
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
      (differentiableOn_zpow (-1 : ℤ) _ (by tauto)).analyticOnNhd isOpen_compl_singleton _ hc
    exact ContDiffAt.comp (g := fun z : ℂ => z ^ (-1 : ℤ))
      (f := fun x : Fin 2 → Fin 2 → ℝ =>
        (x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)) x0
      (hz.contDiffAt.restrict_scalars ℝ) hcd.contDiffAt
  have hw : ContDiffAt ℝ ∞ (fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0 := by
    simp only [div_eq_mul_inv, ← zpow_neg_one]
    exact contDiffAt_const.mul (had.contDiffAt.mul hinv)
  have hF : AnalyticAt ℂ (f ∘ ofComplex) (σ * (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) +
      (x0 0 1 : ℂ)) / ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))) :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet _ him
  have h3 := ContDiffAt.comp (g := f ∘ ofComplex) (f := fun x : Fin 2 → Fin 2 → ℝ =>
      σ * (((x 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 0 1 : ℂ)) /
        ((x 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x 1 1 : ℂ)))) x0
    (hF.contDiffAt.restrict_scalars ℝ) hw
  exact (h1.mul h2).mul h3

theorem UpperTheory.V.Af.Nf.archSm :
    UpperTheory.V.Af.Nf.ArchSm := by
  intro k f hf
  have hD : ∀ x : Fin 2 → Fin 2 → ℝ,
      (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    intro x
    simp [Matrix.det_fin_two]
  have hDc : Continuous (fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0) := by
    fun_prop
  intro x0 hx0
  refine ContDiffAt.contDiffWithinAt ?_
  have hx0' : x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0 ≠ 0 := by
    simpa [hD] using hx0
  have hc : ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    apply hx0'
    rw [h1, h2]
    ring
  have hsign : ∀ᶠ x in nhds x0, SignType.sign (x 0 0 * x 1 1 - x 0 1 * x 1 0) =
      SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) := by
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · filter_upwards [hDc.continuousAt.eventually (gt_mem_nhds hneg)] with x hx
      rw [sign_neg hx, sign_neg hneg]
    · filter_upwards [hDc.continuousAt.eventually (lt_mem_nhds hpos)] with x hx
      rw [sign_pos hx, sign_pos hpos]
  have hq : (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
      ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ))).im =
      (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
        Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) := by
    rw [Complex.div_im]
    simp
    ring
  have hn : 0 < Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) :=
    Complex.normSq_pos.mpr hc
  have him : 0 < ((((SignType.sign (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) : ℝ)) : ℂ) *
      (((x0 0 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 0 1 : ℂ)) /
        ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)))).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hq]
    rcases lt_or_gt_of_ne hx0' with hneg | hpos
    · rw [sign_neg hneg]
      have : (x0 0 0 * x0 1 1 - x0 0 1 * x0 1 0) /
          Complex.normSq ((x0 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (x0 1 1 : ℂ)) < 0 :=
        div_neg_of_neg_of_pos hneg hn
      simp only [SignType.coe_neg, SignType.coe_one]
      linarith
    · rw [sign_pos hpos]
      simp only [SignType.coe_one, one_mul]
      exact div_pos hpos hn
  refine (archSm_eval_eq k f hf _ x0 hx0' hc him).congr_of_eventuallyEq ?_
  filter_upwards [hsign] with x hx
  unfold UpperTheory.V.Af.Nf.arch UpperTheory.V.Af.Nf.nsl
  rw [hD, hx]
  simp only [Matrix.of_apply]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem val_one (u : (Af ℚ)ˣ) (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have a1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have a2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have a3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

theorem UpperTheory.V.Af.Nf.absF :
    UpperTheory.V.Af.Nf.AbsF := by
  intro r hr u hu
  obtain ⟨-, h2, h3, h4⟩ := UpperTheory.V.Sd.Hm.absf ℚ
  rw [h2, h3 u (val_one u hu), mul_one]
  have h := h4 r
  have hr' : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  have e : (∏ v, |reAt v (r : ℚ)|) = ((r : ℚ) : ℝ) := by
    rw [Fintype.prod_subsingleton _ Rat.infinitePlace, reAt, eq_ratCast]
    simp [abs_of_pos hr']
  rw [e] at h
  exact eq_inv_of_mul_eq_one_right h
end
