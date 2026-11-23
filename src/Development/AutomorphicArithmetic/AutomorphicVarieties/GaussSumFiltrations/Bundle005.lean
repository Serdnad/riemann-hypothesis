module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QHol

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def lin (ξ : F) : (InfinitePlace F → ℂ) →L[ℂ] ℂ :=
  ∑ v, (reAt v ξ : ℂ) • ContinuousLinearMap.proj v

theorem lin_apply (ξ : F) (z : InfinitePlace F → ℂ) : lin ξ z = ∑ v, (reAt v ξ : ℂ) * z v := by
  simp [lin]

def sm (ξ : F) : ℝ := ∑ v, reAt v ξ

theorem norm_lin_le (ξ : F) (h : ∀ v, 0 ≤ reAt v ξ) : ‖lin ξ‖ ≤ sm ξ := by
  have hs : 0 ≤ sm ξ := Finset.sum_nonneg (fun v _ => h v)
  refine ContinuousLinearMap.opNorm_le_bound _ hs (fun z => ?_)
  rw [lin_apply]
  calc ‖∑ v, (reAt v ξ : ℂ) * z v‖ ≤ ∑ v, ‖(reAt v ξ : ℂ) * z v‖ := norm_sum_le _ _
    _ ≤ ∑ v, reAt v ξ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h v)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z v) (h v)
    _ = sm ξ * ‖z‖ := by rw [sm, Finset.sum_mul]

theorem re_lin (ξ : F) (z : InfinitePlace F → ℂ) :
    (2 * Real.pi * Complex.I * lin ξ z).re = -(2 * Real.pi * ∑ v, reAt v ξ * (z v).im) := by
  rw [lin_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.im_sum, Finset.mul_sum]

theorem ez_ofComplex (ξ : F) (z : InfinitePlace F → ℂ) (hz : ∀ v, 0 < (z v).im) :
    ez ξ (fun v => ofComplex (z v)) = Complex.exp (2 * Real.pi * Complex.I * lin ξ z) := by
  simp only [ez, lin_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro v _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hz v)]

private theorem mul_exp_neg_le_exp_half (m x : ℝ) (hm : 0 < m) (hx : 0 ≤ x) :
    2 * Real.pi * x * Real.exp (-(2 * Real.pi * m * x)) ≤ (2 / m) * Real.exp (-(Real.pi * m * x)) := by
  set t := Real.pi * m * x with ht_def
  have ht : 0 ≤ t := by positivity
  have e : Real.exp (-(2 * Real.pi * m * x)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    rw [ht_def]
    ring
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have key : t * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    nlinarith [Real.exp_pos (-t)]
  have hx2 : 2 * Real.pi * x = (2 / m) * t := by
    rw [ht_def]
    field_simp
  rw [e, hx2]
  have hE : 0 ≤ (2 / m) * Real.exp (-t) := by positivity
  calc 2 / m * t * (Real.exp (-t) * Real.exp (-t)) = (2 / m) * Real.exp (-t) * (t * Real.exp (-t)) := by ring
    _ ≤ (2 / m) * Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left key hE
    _ = (2 / m) * Real.exp (-t) := by ring

theorem hol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a : F → ℂ),
    HasQ f a → Hol f := by
  intro F _ _ _ f a hQ
  obtain ⟨⟨D, hD, hsupp⟩, hsum⟩ := hQ
  have hpos : ∀ ξ, a ξ ≠ 0 → ∀ v, 0 ≤ reAt v ξ := by
    intro ξ hξ v
    rcases (hsupp ξ hξ).1 with h0 | htp
    · subst h0
      simp [reAt]
    · exact (htp v).le
  have hsm : ∀ ξ, a ξ ≠ 0 → 0 ≤ sm ξ := fun ξ hξ => Finset.sum_nonneg (fun v _ => hpos ξ hξ v)
  unfold Hol
  intro z0 hz0
  have hz0' : ∀ v, 0 < (z0 v).im := hz0
  obtain ⟨m, hmz, hm⟩ : ∃ m : ℝ, (∀ v, m < (z0 v).im) ∧ 0 < m := by
    have h1 : ∀ᶠ m in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ v, m < (z0 v).im :=
      Filter.eventually_all.2 (fun v => eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (hz0' v)))
    exact (h1.and self_mem_nhdsWithin).exists
  set s : Set (InfinitePlace F → ℂ) := {z | ∀ v, m < (z v).im} with hs_def
  have hsopen : IsOpen s := by
    rw [hs_def, Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun v => isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply v)))
  have hsconv : Convex ℝ s := by
    intro x hx y hy p q hp hq hpq v
    have h1 := hx v
    have h2 := hy v
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have e : p * (x v).im + q * (y v).im - m = p * ((x v).im - m) + q * ((y v).im - m) := by
      have : m = p * m + q * m := by rw [← add_mul, hpq, one_mul]
      linarith
    by_cases hp0 : p = 0
    · have hq1 : q = 1 := by linarith
      subst hp0 hq1
      linarith
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have := mul_pos hp' (sub_pos.2 h1)
      have := mul_nonneg hq (sub_pos.2 h2).le
      linarith
  have hz0s : z0 ∈ s := hmz
  have hpos_s : ∀ z ∈ s, ∀ v, 0 < (z v).im := fun z hz v => hm.trans (hz v)
  let g : F → (InfinitePlace F → ℂ) → ℂ := fun ξ z => a ξ * Complex.exp (2 * Real.pi * Complex.I * lin ξ z)
  let g' : F → (InfinitePlace F → ℂ) → ((InfinitePlace F → ℂ) →L[ℂ] ℂ) := fun ξ z =>
    a ξ • (Complex.exp (2 * Real.pi * Complex.I * lin ξ z) • ((2 * Real.pi * Complex.I) • lin ξ))
  let u : F → ℝ := fun ξ => ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ)))
  have hderiv : ∀ ξ z, z ∈ s → HasFDerivAt (g ξ) (g' ξ z) z := by
    intro ξ z _
    have h1 : HasFDerivAt (fun z => 2 * Real.pi * Complex.I * lin ξ z) ((2 * Real.pi * Complex.I) • lin ξ) z :=
      (lin ξ).hasFDerivAt.const_mul (2 * Real.pi * Complex.I)
    exact (h1.cexp).const_mul (a ξ)
  have hbound : ∀ ξ z, z ∈ s → ‖g' ξ z‖ ≤ u ξ := by
    intro ξ z hz
    by_cases ha : a ξ = 0
    · simp [g', u, ha]
    have hr := hpos ξ ha
    have hsum_le : m * sm ξ ≤ ∑ v, reAt v ξ * (z v).im := by
      rw [sm, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      have := hz v
      nlinarith [hr v]
    simp only [g', u, norm_smul, Complex.norm_exp, re_lin]
    have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc]
    have hL := norm_lin_le ξ hr
    have hexp : Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) ≤ Real.exp (-(2 * Real.pi * m * sm ξ)) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos]
    have hn : 0 ≤ ‖a ξ‖ := norm_nonneg _
    calc ‖a ξ‖ * (Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) * (2 * Real.pi * ‖lin ξ‖))
        ≤ ‖a ξ‖ * (Real.exp (-(2 * Real.pi * m * sm ξ)) * (2 * Real.pi * sm ξ)) := by
          apply mul_le_mul_of_nonneg_left _ hn
          apply mul_le_mul hexp _ (by positivity) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := by ring
  let w : Hn F := fun _ => UpperHalfPlane.ofComplex (Complex.I * ((m / 2 : ℝ) : ℂ))
  have hw_im : ∀ v : InfinitePlace F, 0 < ((fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) v : ℂ).im := by
    intro v
    simp
    linarith
  have hnw : ∀ ξ, ‖a ξ * ez ξ w‖ = ‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ)) := by
    intro ξ
    have := ez_ofComplex ξ (fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) hw_im
    rw [norm_mul, this, Complex.norm_exp, re_lin]
    congr 2
    simp [sm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hsw : Summable (fun ξ => ‖a ξ * ez ξ w‖) := (summable_norm_iff.2 (hsum w).summable)
  have hu : Summable u := by
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_) (hsw.mul_left (2 / m))
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · have := hsm ξ ha
        positivity
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · rw [hnw ξ]
        have := mul_exp_neg_le_exp_half m (sm ξ) hm (hsm ξ ha)
        calc u ξ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := rfl
          _ ≤ ‖a ξ‖ * ((2 / m) * Real.exp (-(Real.pi * m * sm ξ))) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = 2 / m * (‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ))) := by ring
  have hf0 : Summable (fun ξ => g ξ z0) := by
    refine (hsum (fun v => UpperHalfPlane.ofComplex (z0 v))).summable.congr (fun ξ => ?_)
    simp only [g]
    rw [ez_ofComplex ξ z0 hz0']
  have hT := hasFDerivAt_tsum_of_isPreconnected hu hsopen hsconv.isPreconnected hderiv hbound hz0s hf0 hz0s
  have heq : (fun z : InfinitePlace F → ℂ => f (fun v => UpperHalfPlane.ofComplex (z v))) =ᶠ[nhds z0]
      (fun y => ∑' ξ, g ξ y) := by
    filter_upwards [hsopen.mem_nhds hz0s] with y hy
    rw [← (hsum (fun v => UpperHalfPlane.ofComplex (y v))).tsum_eq]
    apply tsum_congr
    intro ξ
    simp only [g]
    rw [ez_ofComplex ξ y (hpos_s y hy)]
  exact (hT.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory.HilbertThetaSeries.QHol
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

open UpperHalfPlane hiding I

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_eq_rhom {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = rhom x v := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]
  rfl

theorem reAt_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x y : F) :
    reAt v (x * y) = reAt v x * reAt v y := by
  rw [reAt_eq_rhom, reAt_eq_rhom, reAt_eq_rhom, map_mul, Pi.mul_apply]

theorem sum_reAt_eq_trace {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ∑ v, (reAt v x : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have key : ∑ v : InfinitePlace F, reAt v x = ∑ σ : F →+* ℝ, σ x := by
    refine Fintype.sum_bijective (fun v => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      ⟨?_, ?_⟩ _ _ ?_
    · intro v w h
      have hvw : v.embedding = w.embedding := by
        ext y
        rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v),
          ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal w)]
        exact congrArg (fun f : F →+* ℝ => ((f y : ℝ) : ℂ)) h
      rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding w, hvw]
    · intro φ
      have hψ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp φ) := by
        rw [ComplexEmbedding.isReal_iff]
        ext y
        simp
      refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp φ), ?_⟩
      ext y
      apply Complex.ofReal_injective
      rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hψ]
      rfl
    · intro v
      exact reAt_eq_rhom v x
  rw [← Complex.ofReal_sum, key, ← trace_eq_sum_realEmbeddings, Complex.ofReal_ratCast]

theorem cmp_toInf_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) F)
    (v : InfinitePlace F) (i j : Fin 2) :
    ((cmp v (toInf g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = rhom ((g : Matrix (Fin 2) (Fin 2) F) i j) v := rfl

theorem denom_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℂ) :
    denom (cmp v (toInf (aff 1 b))) w = 1 := by
  simp [denom, cmp_toInf_apply, aff]

theorem coe_translate_smul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℍ) :
    ((cmp v (toInf (aff 1 b)) • w : ℍ) : ℂ) = (w : ℂ) + (reAt v b : ℂ) := by
  have e : ∀ i j, ((cmp v (toInf (aff 1 b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      rhom ((aff (1 : Fˣ) b : Matrix (Fin 2) (Fin 2) F) i j) v := fun i j => cmp_toInf_apply _ v i j
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff 1 b)))) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e, e, e, e]
    simp [aff]
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, denom_translate]
  simp only [UpperHalfPlane.num, e]
  simp [aff, reAt_eq_rhom]

theorem ez_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b ξ : F) (z : Hn F) :
    ez ξ (act (toInf (aff 1 b)) z) = et (b * ξ) * ez ξ z := by
  rw [mul_comm b ξ]
  have h := sum_reAt_eq_trace (ξ * b)
  simp only [ez, et, act, coe_translate_smul]
  rw [← Complex.exp_add, ← h]
  congr 1
  simp only [reAt_mul, Complex.ofReal_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem th_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ),
    sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  intro F _ _ _ κ _ _ G k b Φ
  funext z
  simp only [sl0, denom_translate, Finset.prod_const_one, inv_one, one_pow, one_mul, th]
  refine tsum_congr fun x => ?_
  rw [ez_translate]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.thetaSeries_translation_twists_coefficients : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ), sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_translate | exact GlobalTheory.HilbertThetaSeries.th_translate | (intros; apply GlobalTheory.HilbertThetaSeries.th_translate <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.DelGen

variable {F : Type} [Field F] [NumberField F]

theorem exists_pos_val (T : Finset (HeightOneSpectrum (𝓞 F))) (γ : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ))
    (hγ : ∀ w ∈ T, γ w ≠ 0) :
    ∃ a : F, (∀ w ∈ T, w.valuation F a = γ w) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuation_surjective F (γ w)
  set M : ℕ := T.sup (fun w => (WithZero.log (γ w)).natAbs) + 1 with hM
  obtain ⟨a, ha, hpos⟩ := GlobalTheory.FinPlaceApproxPos.approxpos_target F T t M
  refine ⟨a, fun w hw => ?_, hpos⟩
  have hle : (WithZero.log (γ w)).natAbs ≤ T.sup (fun w => (WithZero.log (γ w)).natAbs) :=
    Finset.le_sup (f := fun w => (WithZero.log (γ w)).natAbs) hw
  have hlt : WithZero.exp (-(M : ℤ)) < γ w := by
    conv_rhs => rw [← WithZero.exp_log (hγ w hw)]
    rw [WithZero.exp_lt_exp]
    omega
  rw [← ht w]
  exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt (ha w hw) (by rw [ht w]; exact hlt))

theorem finite_over (p : ℕ) (hp : p ≠ 0) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ w, w ∈ T ↔ ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine ⟨(Ideal.finite_factors h0).toFinset, fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end GlobalTheory.HilbertThetaSeries.DelGen


open GlobalTheory.HilbertThetaSeries.DelGen in
theorem GlobalTheory.HilbertThetaSeries.del_exists_and_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  intro F _ _ _ p hp
  obtain ⟨T, hT⟩ := finite_over (F := F) p hp.ne_zero
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := exists_pos_val T (fun w => WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)))
      (fun w _ => WithZero.exp_ne_zero)
    exact ⟨a, fun w hw => ha w ((hT w).2 hw)⟩
  · intro δ hδ y
    have hne : ∀ w ∈ T, Valued.v (pLoc F w (y : Af F)) * w.valuation F δ ≠ 0 := by
      intro w hw
      refine mul_ne_zero ?_ ?_
      · rw [Ne, map_eq_zero]
        exact ((y.map (pLoc F w).toMonoidHom).ne_zero)
      · rw [hδ w ((hT w).1 hw)]
        exact WithZero.exp_ne_zero
    obtain ⟨a, ha, hpos⟩ := exists_pos_val T (fun w => (Valued.v (pLoc F w (y : Af F)) * w.valuation F δ)⁻¹)
      (fun w hw => inv_ne_zero (hne w hw))
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have ha0 : a ≠ 0 := by
      intro h
      have h1 := hpos (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      rw [h, map_zero] at h1
      exact lt_irrefl _ h1
    refine ⟨Units.mk0 a ha0, fun u => ?_, fun w hw => ?_⟩
    · show 0 < (u.embedding a).re
      rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal u), Complex.ofReal_re]
      exact hpos _
    · have hw' := (hT w).2 hw
      rw [Units.val_mul, Units.coe_map, map_mul]
      show Valued.v ((a : w.adicCompletion F) * pLoc F w (y : Af F)) * w.valuation F δ = 1
      rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ha w hw', mul_assoc, inv_mul_cancel₀ (hne w hw')]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_different_generator_totallyPositive_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.del_exists_and_move | exact GlobalTheory.HilbertThetaSeries.del_exists_and_move | (intros; apply GlobalTheory.HilbertThetaSeries.del_exists_and_move <;> assumption)
end
