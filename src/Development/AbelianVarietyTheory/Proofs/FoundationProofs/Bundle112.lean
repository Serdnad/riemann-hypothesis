module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle085
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle087
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ

theorem _root_.GlobalTheory.T.modularTower_function_slTwoInt_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := by
  first | exact @GlobalTheory.KZ.InvFun.fun_inv | exact GlobalTheory.KZ.InvFun.fun_inv | (intros; apply GlobalTheory.KZ.InvFun.fun_inv <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.modularForm_gamma1InterGamma0_ext_qExpansionCoeff : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k, (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  first | exact @GlobalTheory.Hk.eq_of_coef_eq | exact GlobalTheory.Hk.eq_of_coef_eq | (intros; apply GlobalTheory.Hk.eq_of_coef_eq <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ), GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) + (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  first | exact @GlobalTheory.Hk.coef_heckeT | exact GlobalTheory.Hk.coef_heckeT | (intros; apply GlobalTheory.Hk.coef_heckeT <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem isOpen_Hs_mobt : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem tendsto_mob_codiscreteWithin :
    ∀ g : GQ, Filter.Tendsto (mob g) (Filter.codiscreteWithin Hs) (Filter.codiscreteWithin Hs) := by
  intro g
  obtain ⟨hmaps, hmul, hone, -, hdiff, -⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  have hinj : ∀ x y : ℂ, x ∈ Hs → y ∈ Hs → mob g x = mob g y → x = y := by
    intro x y hx hy hxy
    have ex : mob (g⁻¹ * g) x = x := by rw [inv_mul_cancel, hone]
    have ey : mob (g⁻¹ * g) y = y := by rw [inv_mul_cancel, hone]
    rw [← ex, ← ey, hmul _ _ _ hx, hmul _ _ _ hy, hxy]
  intro S hS
  rw [Filter.mem_map, mem_codiscreteWithin]
  rw [mem_codiscreteWithin] at hS
  intro z hz
  have hw := hS (mob g z) (hmaps g z hz)
  have hHs : Hs ∈ nhds z := isOpen_Hs_mobt.mem_nhds hz
  have hcont : ContinuousAt (mob g) z := (hdiff g).continuousOn.continuousAt hHs
  have htend : Filter.Tendsto (mob g) (nhdsWithin z {z}ᶜ) (nhdsWithin (mob g z) {mob g z}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hHs, self_mem_nhdsWithin] with x hx hxz
    exact fun h => hxz (hinj x z hx hz h)
  rw [Filter.disjoint_principal_right] at hw ⊢
  filter_upwards [htend hw, nhdsWithin_le_nhds hHs] with x hx hxH
  rintro ⟨hx1, hx2⟩
  exact hx ⟨hmaps g x hx1, hx2⟩

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.SiegDist

lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

lemma ee_int_mul (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_int_mul]; ring_nf

lemma ee_nat_mul (n : ℕ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_nat_mul]; ring_nf

lemma ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have h : (2 * Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, ← Real.exp_zero, Real.exp_lt_exp]
  have := mul_pos Real.pi_pos τ.im_pos
  linarith

lemma ee_eq_one (u v : ℚ) (τ : ℍ) (h : ee ((u : ℂ) * τ + v) = 1) : u = 0 ∧ ∃ k : ℤ, v = k := by
  unfold ee at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (u : ℂ) * τ + v = k := by
    apply mul_left_cancel₀ hne
    rw [hk]; ring
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  have hu : u = 0 := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hu
  simp at hre
  exact ⟨rfl, k, by exact_mod_cast hre⟩

theorem sg_distribution : ∀ (c m : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ = sg c x τ := by
  intro c m x τ hA hm hcm
  obtain ⟨hc1, hc6, hnot⟩ := hA
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq0 : ee (τ : ℂ) ≠ 0 := ee_ne_zero _
  have hsplit : ∀ a b : ℕ, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = cth c (ee (τ : ℂ)) (ee ((((x 0 : ℂ) + a) * τ + x 1) / m) * ee ((b : ℂ) / m)) := by
    intro a b
    unfold sg
    rw [← ee_add]
    congr 2
    simp [pt]
    field_simp
    ring
  have hpow : ∀ a : ℕ, ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ m = ee (pt x τ) * ee (τ : ℂ) ^ a := by
    intro a
    rw [← ee_nat_mul, ← ee_nat_mul, ← ee_add]
    congr 1
    simp only [pt]
    field_simp
    ring
  have hND : ∀ n : ℤ, ee (τ : ℂ) ^ n * ee (pt x τ) ^ c ≠ 1 := by
    intro n h
    have h' : ee ((((n : ℚ) + c * x 0 : ℚ) : ℂ) * τ + ((c * x 1 : ℚ) : ℂ)) = 1 := by
      rw [← h, ← ee_int_mul, ← ee_nat_mul, ← ee_add]
      congr 1; simp only [pt]; push_cast; ring
    obtain ⟨h0, k, hk⟩ := ee_eq_one _ _ τ h'
    apply hnot
    refine ⟨⟨-n, ?_⟩, ⟨k, hk.symm⟩⟩
    push_cast; linarith
  have hD1 : ∀ a : ℕ, ∀ n : ℤ, ee (τ : ℂ) ^ n * ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ (c * m) ≠ 1 := by
    intro a n h
    rw [mul_comm c m, pow_mul, hpow a, mul_pow, ← pow_mul] at h
    apply hND (n + ((a * c : ℕ) : ℤ))
    rw [zpow_add₀ hq0, zpow_natCast, ← h]
    ring
  calc ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = ∏ a ∈ Finset.range m, cth c (ee (τ : ℂ) ^ m) (ee (pt x τ) * ee (τ : ℂ) ^ a) := by
        apply Finset.prod_congr rfl
        intro a _
        simp_rw [hsplit a]
        rw [GlobalTheory.T.smoothedThetaQProduct_distribution_relation c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) (hD1 a), hpow a]
    _ = cth c (ee (τ : ℂ)) (ee (pt x τ)) :=
        GlobalTheory.T.prod_smoothedThetaQProduct_distribution c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) hND
    _ = sg c x τ := rfl

end GlobalTheory.SiegDist
end
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerPositivity

theorem periodic_of_dbar : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ), (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → ∀ s : ℂ, 0 < s.im → h (ofComplex (s + T)) = h (ofComplex s) := by
  intro U h w T hd hp s hs
  have hsT : 0 < (s + T).im := by simpa using hs
  obtain ⟨L0, hL0, e0⟩ := hd s hs
  obtain ⟨L1, hL1, e1⟩ := hd (s + T) hsT
  have hshift : HasFDerivAt (fun z : ℂ => U (z + T)) L1 s := by
    have := hL1.comp s ((hasFDerivAt_id (𝕜 := ℝ) s).add_const (T : ℂ))
    simpa [Function.comp_def] using this
  have hev : U =ᶠ[nhds s] fun z : ℂ => U (z + T) :=
    ((Complex.continuous_im.tendsto s).eventually (lt_mem_nhds hs)).mono fun z hz => (hp z hz).symm
  have hL : L0 = L1 := hL0.unique (hshift.congr_of_eventuallyEq hev)
  have hconj : (s + T) - (starRingEnd ℂ) (s + T) = s - (starRingEnd ℂ) s := by
    simp only [map_add (f := _), Complex.conj_ofReal]; ring
  have hne : 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w ≠ 0 := by
    have : s - (starRingEnd ℂ) s ≠ 0 := by
      rw [Complex.sub_conj]
      exact mul_ne_zero (by exact_mod_cast (by positivity : (2 * s.im) ≠ 0)) Complex.I_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero _ this)
  have key := e1
  rw [hconj, ← hL, e0] at key
  exact ((starRingEnd ℂ).injective (mul_left_cancel₀ hne key)).symm

theorem fourier_sub_eq : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ) (n : ℕ) (a b : ℝ), 0 < T → 0 < a → a ≤ b → (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (b : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (b : ℂ) * Complex.I) / T)) - (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (a : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (a : ℂ) * Complex.I) / T)) = 2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  intro U h w T n a b hT ha hab hd hp hh hper hbdd
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  refine (GlobalTheory.T.green_formula_periodic_rectangle_upperHalfPlane (fun z => U z * Complex.exp (2 * Real.pi * Complex.I * n * z / T))
    (fun s => Complex.exp (2 * Real.pi * Complex.I * n * s / T) *
      (2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))))
    T a b hT ha hab ?_ ?_ ?_).trans ?_
  · intro s hs
    obtain ⟨L, hL, e⟩ := hd s hs
    have h1 : HasDerivAt (fun z : ℂ => 2 * Real.pi * Complex.I * n * z / T)
        (2 * Real.pi * Complex.I * n / T) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * Real.pi * Complex.I * n : ℂ)).div_const (T : ℂ)
    refine ⟨_, hL.mul (h1.cexp.hasFDerivAt.restrictScalars ℝ), ?_⟩
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    linear_combination (Complex.exp (2 * Real.pi * Complex.I * n * s / T)) * e
  · have hc : ContinuousOn (h ∘ ofComplex) {s : ℂ | 0 < s.im} :=
      (UpperHalfPlane.mdifferentiable_iff.1 hh).continuousOn
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) (ContinuousOn.mul
      (Continuous.continuousOn ?_) (Complex.continuous_conj.comp_continuousOn hc))
    exact continuous_const.mul ((continuous_id.sub Complex.continuous_conj).pow w)
  · intro s hs
    show U (s + T) * Complex.exp _ = U s * Complex.exp _
    rw [hp s hs]
    congr 1
    rw [show 2 * (Real.pi : ℂ) * Complex.I * n * (s + T) / T =
        2 * Real.pi * Complex.I * n * s / T + n * (2 * Real.pi * Complex.I) by field_simp,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · have inner : ∀ y ∈ Set.uIcc a b,
        (∫ x in (0 : ℝ)..T, Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
        2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) *
          ((y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ)) := by
      intro y hy
      have hy0 : 0 < y := by
        rw [Set.uIcc_of_le hab] at hy
        exact lt_of_lt_of_le ha hy.1
      have hpt : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I) =
          2 * Complex.I * y := by
        intro x
        rw [Complex.sub_conj]
        simp
        ring
      simp_rw [hpt]
      have hfun : (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (2 * Complex.I * (y : ℂ)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
          fun x : ℝ => (2 * Complex.I * (2 * Complex.I) ^ w * (y : ℂ) ^ w) *
            ((starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
              Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) := by
        funext x
        rw [mul_pow]
        ring
      rw [hfun, intervalIntegral.integral_const_mul, GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff h T n y hT hy0 hh hper hbdd]
      ring
    rw [intervalIntegral.integral_congr inner, intervalIntegral.integral_const_mul]

theorem cuspForm_eq_zero_of_periodic_of_bound : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]) (h₀ : ℕ) (C : ℝ), 0 < h₀ → (∀ τ : ℍ, (eichler (k - 2) ⇑f ((h₀ : ℝ) +ᵥ τ) - (eichler (k - 2) ⇑h ((h₀ : ℝ) +ᵥ τ)).map (starRingEnd ℂ) - p).eval (((h₀ : ℝ) +ᵥ τ : ℍ) : ℂ) = (eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)) → (∀ τ : ℍ, ‖(eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)‖ ≤ C * τ.im ^ (((k : ℝ) - 2) / 2)) → h = 0 := by
  intro Γ k hfi hk f h p h₀ C hh₀ hper hbd
  have := hfi
  have hT : (0 : ℝ) < (h₀ : ℝ) := by exact_mod_cast hh₀
  have hcoe : ∀ z : ℂ, 0 < z.im → ((ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [ofComplex_apply_of_im_pos hz]
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑h) := ModularFormClass.holo h
  have hd := GlobalTheory.T.hasFDerivAt_eichler_sub_conj_wirtinger (k - 2) ⇑f ⇑h p (ModularFormClass.holo f) hholo
  have hUper : ∀ s : ℂ, 0 < s.im →
      (eichler (k - 2) ⇑f (ofComplex (s + ((h₀ : ℝ) : ℂ))) -
          (eichler (k - 2) ⇑h (ofComplex (s + ((h₀ : ℝ) : ℂ)))).map (starRingEnd ℂ) - p).eval
          (s + ((h₀ : ℝ) : ℂ)) =
        (eichler (k - 2) ⇑f (ofComplex s) - (eichler (k - 2) ⇑h (ofComplex s)).map (starRingEnd ℂ) - p).eval s := by
    intro s hs
    have hs' : 0 < (s + ((h₀ : ℝ) : ℂ)).im := by simpa using hs
    have e : ofComplex (s + ((h₀ : ℝ) : ℂ)) = ((h₀ : ℝ) +ᵥ ofComplex s) := by
      ext
      rw [UpperHalfPlane.coe_vadd, hcoe _ hs', hcoe _ hs]
      ring
    have key := hper (ofComplex s)
    rw [← e, hcoe _ hs', hcoe _ hs] at key
    exact key
  have hhper := periodic_of_dbar _ ⇑h (k - 2) (h₀ : ℝ) hd hUper
  have hperh : Function.Periodic (⇑h ∘ ofComplex) ((h₀ : ℝ) : ℂ) := by
    intro s
    by_cases hs : 0 < s.im
    · exact hhper s hs
    · rw [not_lt] at hs
      simp only [Function.comp_apply]
      rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hs) hs]
  have hbdd : IsBoundedAtImInfty (⇑h) := ModularFormClass.bdd_at_infty h
  have hzero : IsZeroAtImInfty (⇑h) := CuspFormClass.zero_at_infty h
  have hq : qExpansion (h₀ : ℝ) ⇑h = 0 := by
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    rcases n with _ | n
    · rw [qExpansion_coeff_zero hT (analyticAt_cuspFunction_zero hT hperh hholo hbdd) hperh,
        hzero.valueAtInfty_eq_zero]
    · have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hα : 0 < 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hβ : 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hK : 2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ) ≠ 0 := by
        have : ((h₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
          (pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero))) this
      have hw1 : 1 ≤ k - 2 := by omega
      have hwR : (((k - 2 : ℕ) : ℝ)) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hbound : ∀ y : ℝ, 0 < y →
          ‖∫ x in (0 : ℝ)..(h₀ : ℝ),
              (eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            (C * (h₀ : ℝ)) * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) *
              Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
        intro y hy
        have hpt : ∀ x : ℝ,
            ‖(eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            C * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
          intro x
          have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
          have hb := hbd (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))
          rw [hcoe _ hz] at hb
          have him : (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
            rw [← UpperHalfPlane.coe_im, hcoe _ hz]
            simp
          rw [him, ← hwR] at hb
          rw [norm_mul, Complex.norm_exp]
          have hre : (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) /
              ((h₀ : ℝ) : ℂ)).re = -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y := by
            rw [Complex.div_ofReal_re]
            simp
            ring
          rw [hre]
          exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (h₀ : ℝ))
          (fun x _ => hpt x)
        rw [sub_zero, abs_of_pos hT] at this
        calc _ ≤ _ := this
          _ = _ := by ring
      have hc := GlobalTheory.T.coeff_eq_zero_of_exp_decay_of_integral_identity _ (2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ))
        ((starRingEnd ℂ) ((qExpansion (h₀ : ℝ) ⇑h).coeff (n + 1)))
        (C * (h₀ : ℝ)) _ (4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) (k - 2) hw1 hα hβ hK hbound
        (fun a b ha hab => fourier_sub_eq _ ⇑h (k - 2) (h₀ : ℝ) (n + 1) a b hT ha hab hd hUper
          hholo hperh hbdd)
      simpa using hc
  have hfun : (⇑h : ℍ → ℂ) = 0 := (qExpansion_eq_zero_iff hT hperh hholo hbdd).1 hq
  ext τ
  simpa using congrFun hfun τ

end GlobalTheory.EichlerPositivity
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal → N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_moves | exact GlobalTheory.AlmostEt.almostSep_of_moves | (intros; apply GlobalTheory.AlmostEt.almostSep_of_moves <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummer_carry_coboundary_twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  first | exact @GlobalTheory.NeedB.TwistCochain.twist_cochain | exact GlobalTheory.NeedB.TwistCochain.twist_cochain | (intros; apply GlobalTheory.NeedB.TwistCochain.twist_cochain <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 → (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_top_of_coprime_order | exact GlobalTheory.AlmostEt.moves_top_of_coprime_order | (intros; apply GlobalTheory.AlmostEt.moves_top_of_coprime_order <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.pow_mul_approx_pow_of_almostEtaleSeparatingFamily : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  first | exact @GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | exact GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep | (intros; apply GlobalTheory.AlmostEt.cpow_mul_approx_pow_of_isSep <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
  ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  first | exact @GlobalTheory.norm_surjective_of_is_c1 | exact GlobalTheory.norm_surjective_of_is_c1 | (intros; apply GlobalTheory.norm_surjective_of_is_c1 <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.principalSeriesType_constant_family_det_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  first | exact @GlobalTheory.PsType.const_family_main | exact GlobalTheory.PsType.const_family_main | (intros; apply GlobalTheory.PsType.const_family_main <;> assumption)
end
