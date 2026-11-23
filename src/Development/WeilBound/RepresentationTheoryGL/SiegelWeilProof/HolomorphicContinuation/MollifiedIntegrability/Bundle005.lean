module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

theorem cls_shift {n : ℕ} (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y = cls s z p q R y := by
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul]
  ring

theorem wr_of : Gauss → ClsBound → ClsGain → IBP → Integr → Dens → WRSt := by
  intro hG hB hGain hIBP hI hD m n ε c t hc ht P
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.2 hc.ne'
  have hs' : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left; simp [hc.ne']
    · right; simp [hc.ne']
  generalize ((t / c : ℝ) : ℂ) = s at hR hs'
  have hs := hs'
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hR
  generalize (Finset.univ.filter fun a => ε a = false).card = q at hR
  obtain ⟨-, hint⟩ := hI n
  obtain ⟨g, hgc, hgd, hgv⟩ := hD m n ε c t hc ht P (n ^ 2 + 1) (by
    push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  refine ⟨g, hgc, hgd, fun β hβ => ?_⟩
  have hGN := fun N => hGain n s hs p q N R
  choose J a G hGc hGb hGeq using hGN
  choose CG hCG using hGb
  have hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := fun N j y => by
    have := hCG N j y
    rwa [neg_div] at this
  set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK
  let Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ := fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y
  let WN : ℕ → ℂ → ℂ := fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z
  let U : ℕ → Set ℂ := fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2}
  let orig : ℂ → ℂ := fun z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
  have hUopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N) := by
    intro N
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    exact (a N j).differentiable.differentiableOn.mul
      (holo hI t β (hGc N j) (((p + q + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))

  have hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 →
      ∫ y, (Delta^[N] (cls s z p q R)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z := by
    intro N z hz
    have e : (fun y => (Delta^[N] (cls s z p q R)) y * chr t β y) =
        fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y) := by
      funext y
      rw [hGeq N z y, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z := by
    intro N z hz
    have e1 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => cls s z p q R y * chr t β y := by
      funext y
      rw [hR y, ← cls_shift s z]
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    have good : Good (cls s z p q R) := by
      refine ⟨(hB n s hs p q R z).1, fun L => ?_⟩
      obtain ⟨C, hC⟩ := (hB n s hs p q R z).2 L
      exact ⟨fun y => C * dP y ^ (-(z.re + ((p : ℝ) + q) / 2)), (hint _ (by linarith)).const_mul C, hC⟩
    have hz' : (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    show KK ^ N * _ = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
    rw [e1, ibp_iter hIBP good t β ht0 hβ N, hsum N z hz']
  have agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N) := by
    intro N N' hNN'
    have hsub : U N ⊆ U N' := fun z hz => by
      simp only [U, Set.mem_ofPred_eq] at hz ⊢
      have : ((p + q + N : ℕ) : ℝ) ≤ ((p + q + N' : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have hA : AnalyticOnNhd ℂ (WN N) (U N) := (hWdiff N).analyticOnNhd (hUopen N)
    have hA' : AnalyticOnNhd ℂ (WN N') (U N) := ((hWdiff N').mono hsub).analyticOnNhd (hUopen N)
    have hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((p + q + N : ℕ) : ℝ) / 2 < z.re} := by
      ext z
      simp only [U, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hpre : IsPreconnected (U N) := by
      rw [hU]; exact (convex_halfSpace_re_gt _).isPreconnected
    set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1
    have hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1 := by rw [hz1, Complex.ofReal_re]
    have hz1U : z1 ∈ U N := by
      simp only [U, Set.mem_ofPred_eq, hz1re]
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := by
      simp only [Set.mem_ofPred_eq, hz1re]; linarith
    have hev : WN N =ᶠ[𝓝 z1] WN N' :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm
    exact hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev
  have agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z := by
    intro N N' z hz hz'
    rcases le_total N N' with h | h
    · exact agree N N' h hz
    · exact (agree N' N h hz').symm
  obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1 := ⟨_, fun _ => rfl⟩
  have hNf : ∀ z, z ∈ U (Nf z) := by
    intro z
    show (n : ℝ) ^ 2 / 2 < z.re + ((p + q + Nf z : ℕ) : ℝ) / 2
    rw [hNfdef z]
    have h1 := Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)
    push_cast
    have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
    linarith
  refine ⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · intro z0
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0) :=
      Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz
    exact (((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev
  · have e2 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y * chr t β y := by
      funext y; rw [hR y]
    rw [e2]
    obtain ⟨C, hC⟩ := (hB n s hs p q R 0).2 []
    have hC0 : ∀ y, ‖cls s 0 p q R y‖ ≤ C * dP y ^ (-(((p : ℝ) + q) / 2)) := by
      intro y
      have := hC y
      simp only [List.foldr_nil, Complex.zero_re, zero_add] at this
      exact this
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    exact integ_term hI t β (hB n s hs p q R 0).1.continuous hC0 (by linarith)
  · exact hbig (Nf z) z hz
  · have hN0 : Nf 0 = n ^ 2 + 1 := by
      rw [hNfdef, Complex.zero_re, mul_zero, sub_zero,
        show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
    show WN (Nf 0) 0 = _
    rw [hN0, hgv β hβ]
    have hfun : (fun y => secN ε c t P (herm y)) = cls s 0 p q R := funext hR
    rw [hfun, hsum (n ^ 2 + 1) 0 (by
      simp only [Complex.zero_re, zero_add]
      push_cast
      have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
      linarith)]
    show KK ^ (n ^ 2 + 1) * _ = _
    rw [hKK]
    ring

end PositivityTheory.Rg.Sw.WR.T
end
end

section

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

theorem integP : IntegP := GI.integP

lemma map_smul_volume {m n : ℕ} (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = volume := by
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) :=
    ((ζ • LinearMap.id : (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ))).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq, hζ]
    simp
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → Fin n → ℂ)))
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at this
  calc Measure.map (fun x : Fin m → Fin n → ℂ => ζ • x) volume = Measure.map (⇑L) volume := rfl
    _ = volume := by rw [this]; simp

lemma evX_smul_mono {m n : ℕ} (ζ : ℂ) (d : (Fin m × Fin n × Bool) →₀ ℕ) (hd : ∀ k, k.2.2 = true → d k = 0)
    (x : Fin m → Fin n → ℂ) :
    evX (monomial d 1) (ζ • x) = ζ ^ (d.sum fun _ e => e) * evX (monomial d 1) x := by
  unfold evX
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod,
    Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk2 : k.2.2 = false := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hd k (by simpa using h))
  simp [hk2, mul_pow]

lemma gs_smul {m n : ℕ} (c : ℝ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) : gs c (ζ • x) = gs c x := by
  unfold gs
  simp [hζ]

lemma gramX_smul {m n : ℕ} (ε : Fin m → Bool) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) :
    gramX ε (ζ • x) = gramX ε x := by
  have h1 : (starRingEnd ℂ) ζ * ζ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ]; simp
  have key : ∀ u v : ℂ, (starRingEnd ℂ) (ζ * u) * (ζ * v) = (starRingEnd ℂ) u * v := by
    intro u v
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) u * v) * h1
  ext _i _j

  simp only [gramX, evX, Qp, Qb, map_sub, map_sum, map_mul, MvPolynomial.eval_X]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
    simp only [Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, if_true, if_false] <;>
    exact key _ _

lemma continuous_gramX {m n : ℕ} (ε : Fin m → Bool) : Continuous fun x : Fin m → Fin n → ℂ => gramX ε x :=
  continuous_pi fun i => continuous_pi fun j => GI.continuous_evX _

theorem rot : Rot := by
  intro m n ε c t hc b hb d hd hd0
  set N := d.sum fun _ e => e with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hd0
    ext k
    have := (Finset.sum_eq_zero_iff.mp h) k
    by_cases hk : k ∈ d.support
    · simpa using this hk
    · simpa using hk
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  set ζ : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) with hζdef
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, Complex.norm_exp_ofReal_mul_I]
  have hζN : ζ ^ N = -1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (((Real.pi / N : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  let F : (Fin m → Fin n → ℂ) → ℂ := fun x =>
    evX (monomial d 1) x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace)
  have hcont : Continuous F :=
    ((GI.continuous_evX _).mul (GI.continuous_gs c)).mul (Complex.continuous_exp.comp
      (continuous_const.mul ((continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace)))
  have hcomp : (fun x => F (ζ • x)) = fun x => ζ ^ N * F x := by
    funext x
    simp only [F, evX_smul_mono ζ d hd, gs_smul c ζ hζ, gramX_smul ε ζ hζ]
    ring
  have hint : ∫ x, F (ζ • x) = ∫ x, F x := by
    rw [← integral_map (μ := volume) (φ := fun x : Fin m → Fin n → ℂ => ζ • x)
      (continuous_const_smul ζ).measurable.aemeasurable
      (by rw [map_smul_volume ζ hζ]; exact hcont.aestronglyMeasurable), map_smul_volume ζ hζ]
  have h2 : ∫ x, F x = -∫ x, F x := by
    conv_lhs => rw [← hint, hcomp, integral_const_mul, hζN, neg_one_mul]
  show ∫ x, F x = 0
  linear_combination (1 / 2 : ℂ) * h2

end PositivityTheory.Rg.Sw.WR.G
end
end

section

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ}

def gK (v : E n) : ℝ := ∏ a, ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(v a b) ^ 2)

theorem gK_nonneg (v : E n) : 0 ≤ gK v := by
  unfold gK
  exact Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

theorem integrable_gK : Integrable (gK (n := n)) := by
  have h1 : Integrable (fun s : ℝ => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)) := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).const_mul (Real.sqrt Real.pi)⁻¹
    simpa using this
  have h2 : Integrable (fun w : Fin n → ℝ => ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (s : ℝ) => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)) (fun _ => h1)
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℝ) => ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2))
    (fun _ => h2)

theorem integral_gK : ∫ v, gK (n := n) v = 1 := by
  have h1 : ∫ s : ℝ, (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2) = 1 := by
    rw [integral_const_mul]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  unfold gK
  rw [integral_fintype_prod_volume_eq_prod (f := fun _ (w : Fin n → ℝ) =>
    ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2))]
  simp_rw [integral_fintype_prod_volume_eq_prod (f := fun _ (s : ℝ) => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)), h1,
    Finset.prod_const_one]

theorem gauss_prod (ε : ℝ) (y : E n) :
    Complex.exp (-((ε * ip y y : ℝ) : ℂ)) = ∏ a, ∏ b, Complex.exp (-(ε : ℂ) * ((y a b : ℝ) : ℂ) ^ 2) := by
  simp_rw [← Complex.exp_sum]
  congr 1
  unfold ip
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem integrable_gauss (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun y : E n => Complex.exp (-((ε * ip y y : ℝ) : ℂ))) := by
  simp_rw [gauss_prod]
  have h1 : Integrable (fun s : ℝ => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) :=
    integrable_cexp_neg_mul_sq (by simpa using hε)
  have h2 : Integrable (fun w : Fin n → ℝ => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (s : ℝ) => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) (fun _ => h1)
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℝ) => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2))
    (fun _ => h2)

theorem norm_gauss_le (ε : ℝ) (hε : 0 < ε) (y : E n) : ‖Complex.exp (-((ε * ip y y : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have h : 0 ≤ ip y y := by
    unfold ip
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_self_nonneg _
  have : (-((ε * ip y y : ℝ) : ℂ)).re = -(ε * ip y y) := by simp
  rw [this, Real.exp_le_one_iff]
  nlinarith

theorem kraw_eq (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ≠ 0) (u : E n) :
    (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      (((|t| / (2 * Real.sqrt ε)) ^ (n ^ 2) * gK ((|t| / (2 * Real.sqrt ε)) • u) : ℝ) : ℂ) := by
  set lam : ℝ := |t| / (2 * Real.sqrt ε) with hlam
  have hε' : 0 < (ε : ℂ).re := by simpa using hε

  have hprod : ∀ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((y a b : ℝ) : ℂ) ^ 2)) := by
    intro y
    simp_rw [Finset.prod_mul_distrib, ← gauss_prod, ← Complex.exp_sum]
    rw [mul_comm]
    congr 2
    unfold ip
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hint : ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) * Complex.exp (-((t * u a b : ℝ) : ℂ) ^ 2 / (4 * ε)) := by
    simp_rw [hprod]
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (w : Fin n → ℝ) =>
      ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((w b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun b (s : ℝ) =>
      Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * (s : ℂ)) * Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2))]
    refine Finset.prod_congr rfl fun b _ => ?_
    exact fourierIntegral_gaussian hε' _

  have hsq : ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi / Real.sqrt ε : ℝ) : ℂ) := by
    rw [← Real.sqrt_div' _ hε.le, Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hε.le)]
    push_cast
    ring_nf
  have hcoord : ∀ s : ℝ, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) * (((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) *
      Complex.exp (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε))) =
      ((lam * ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(lam * s) ^ 2)) : ℝ) : ℂ) := by
    intro s
    have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hee : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hpp : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    rw [hsq]
    have hexp : (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε)) = ((-(lam * s) ^ 2 : ℝ) : ℂ) := by
      rw [hlam]
      push_cast
      have : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
      have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
      have hee' : ((Real.sqrt ε : ℝ) : ℂ) ^ 2 = (ε : ℂ) := by exact_mod_cast hee
      field_simp
      rw [this, hee']
      ring
    rw [hexp, ← Complex.ofReal_exp]
    push_cast
    rw [hlam]
    have hpi0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
    have hpp' : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by exact_mod_cast hpp
    have hpi1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
    rw [← hpp']
  rw [hint]
  have hC : (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) = ∏ _a : Fin n, ∏ _b : Fin n, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [← pow_mul, sq]
  rw [hC, ← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, hcoord]
  push_cast
  unfold gK
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [show ((lam : ℂ)) ^ (n ^ 2) = ∏ _a : Fin n, ∏ _b : Fin n, (lam : ℂ) by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, sq]]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end
