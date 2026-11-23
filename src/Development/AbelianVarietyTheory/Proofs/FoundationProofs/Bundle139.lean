module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle136
public import Mathlib.Analysis.Meromorphic.Order
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Convex
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_comp_mul : ∀ (N l : ℕ) (k d e : ℤ) (σ τ ρ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l e τ → GlobalTheory.Hk.IsDia N l (d * e) ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.dia k τ (GlobalTheory.Hk.dia k σ ⇑f) = GlobalTheory.Hk.dia k ρ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_mul | exact GlobalTheory.Hk.dia_mul | (intros; apply GlobalTheory.Hk.dia_mul <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_cuspForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  first | exact @GlobalTheory.Hk.heckeT_cuspForm | exact GlobalTheory.Hk.heckeT_cuspForm | (intros; apply GlobalTheory.Hk.heckeT_cuspForm <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

namespace GlobalTheory.KZ.Germ

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) :
    ∀ τ ∈ Hs, ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  intro τ hτ
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 (Filter.Germ.coe_eq.mp h)) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

theorem eq_zero_or_eq_zero {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (h : ∀ z ∈ Hs, a z * b z = 0) : (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0) := by
  by_cases hA : ∀ z ∈ Hs, a z = 0
  · exact Or.inl hA
  · right
    push Not at hA
    obtain ⟨z₀, hz₀, hne⟩ := hA
    have hcont : ContinuousAt a z₀ := (ha.continuousOn).continuousAt (isOpen_Hs.mem_nhds hz₀)
    have hev : ∀ᶠ z in 𝓝 z₀, a z ≠ 0 := hcont.eventually_ne hne
    have hb0 : b =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hev, isOpen_Hs.mem_nhds hz₀] with z hz1 hz2
      have := h z hz2
      simpa [hz1] using this
    intro z hz
    exact (hb.analyticOnNhd isOpen_Hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hz₀ hb0 hz

theorem exists_eq_zero_of_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) Hs) (h : ∀ z ∈ Hs, ∏ i ∈ s, f i z = 0) :
    ∃ i ∈ s, ∀ z ∈ Hs, f i z = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
    simpa using h _ hI
  | insert j s hj ih =>
    have hP : DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) Hs := by
      exact DifferentiableOn.fun_finsetProd (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rcases eq_zero_or_eq_zero (hf j (Finset.mem_insert_self j s)) hP
        (fun z hz => by have := h z hz; rwa [Finset.prod_insert hj] at this) with h1 | h1
    · exact ⟨j, Finset.mem_insert_self j s, h1⟩
    · obtain ⟨i, hi, hi'⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩

theorem tendsto_mob (g : GQ) {x : ℂ} (hx : x ∈ Hs) : Tendsto (mob g) (𝓝[≠] x) (𝓝[≠] (mob g x)) := by
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · exact ((hdiff g).continuousOn.continuousAt (isOpen_Hs.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hx)] with z hz1 hz2
    intro heq
    apply hz1
    show z = x
    have e1 : mob g⁻¹ (mob g z) = z := by rw [← hmul _ _ z hz2, inv_mul_cancel, hone]
    have e2 : mob g⁻¹ (mob g x) = x := by rw [← hmul _ _ x hx, inv_mul_cancel, hone]
    have : mob g z = mob g x := heq
    rw [← e1, this, e2]

theorem germ_comp (g : GQ) (φ ψ : ℂ → ℂ) (h : (φ : Mero) = (ψ : Mero)) :
    ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero) := by
  obtain ⟨hH, -, -, -, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  apply Filter.Germ.coe_eq.mpr
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.2
  intro x hx
  have h1 := (tendsto_mob g hx).eventually (eventually_of_germ_eq h (mob g x) (hH g x hx))
  filter_upwards [h1] with z hz
  exact Or.inl hz

theorem main : (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (((a : Mero) = (b : Mero)) ↔ ∀ z ∈ Hs, a z = b z)) ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z * b z = 0) → (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0)) ∧ (∀ (g : GQ) (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero)) ∧ (∀ (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ∀ τ ∈ Hs, ∀ᶠ z in nhdsWithin τ {τ}ᶜ, φ z = ψ z) ∧ (∀ (m : ℕ) (a b : ℂ → ℂ), 0 < m → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z ^ m = b z ^ m) → ∃ k : ℕ, ∀ z ∈ Hs, a z = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) * b z) := by
  refine ⟨?_, fun a b ha hb h => eq_zero_or_eq_zero ha hb h, germ_comp, fun φ ψ h => eventually_of_germ_eq h, ?_⟩
  · intro a b ha hb
    constructor
    · intro hab z hz
      have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
      exact (ha.analyticOnNhd isOpen_Hs).eqOn_of_preconnected_of_frequently_eq (hb.analyticOnNhd isOpen_Hs)
        isPreconnected_Hs hI (eventually_of_germ_eq hab _ hI).frequently hz
    · intro h
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
      exact h z hz
  · intro m a b hm ha hb h
    have hm0 : m ≠ 0 := hm.ne'
    have : NeZero m := ⟨hm0⟩
    have hζ := Complex.isPrimitiveRoot_exp m hm0
    obtain ⟨ξ, hξ, hξ'⟩ := exists_eq_zero_of_prod (Polynomial.nthRootsFinset m (1 : ℂ)) (fun ξ z => a z - ξ * b z)
      (fun ξ _ => ha.sub (hb.const_mul ξ))
      (fun z hz => by rw [← hζ.pow_sub_pow_eq_prod_sub_mul (a z) (b z) hm, h z hz, sub_self])
    have hξm : ξ ^ m = 1 := (Polynomial.mem_nthRootsFinset hm (1 : ℂ)).1 hξ
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hξm
    refine ⟨k, fun z hz => ?_⟩
    have e : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) = ξ := by
      rw [← hk, ← Complex.exp_nat_mul]; congr 1; ring
    rw [e]
    exact sub_eq_zero.mp (hξ' z hz)

end GlobalTheory.KZ.Germ
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_modularForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  first | exact @GlobalTheory.Hk.heckeT_modularForm | exact GlobalTheory.Hk.heckeT_modularForm | (intros; apply GlobalTheory.Hk.heckeT_modularForm <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.UHPRoot

noncomputable def cen (k : ℕ) : ℂ := ((k : ℂ) + 2) * Complex.I

noncomputable def rad (k : ℕ) : ℝ := ((k : ℝ) + 2) - 1 / ((k : ℝ) + 2)

theorem rad_pos (k : ℕ) : 0 < rad k := by
  unfold rad
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h : 1 / ((k : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  linarith

theorem cen_im (k : ℕ) : (cen k).im = (k : ℝ) + 2 := by simp [cen]
theorem cen_re (k : ℕ) : (cen k).re = 0 := by simp [cen]

theorem closedBall_sub (k : ℕ) : Metric.closedBall (cen k) (rad k) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := Complex.abs_im_le_norm (z - cen k)
  have h2 : (z - cen k).im = z.im - ((k : ℝ) + 2) := by rw [Complex.sub_im, cen_im]
  rw [h2] at h1
  have h3 : 0 < 1 / ((k : ℝ) + 2) := by positivity
  show 0 < z.im
  unfold rad at hz
  have := neg_abs_le (z.im - ((k : ℝ) + 2))
  linarith

theorem ball_mono : Monotone (fun k : ℕ => Metric.ball (cen k) (rad k)) := by
  refine monotone_nat_of_le_succ fun k => Metric.ball_subset_ball' ?_
  have hd : cen k - cen (k + 1) = -Complex.I := by
    simp only [cen]; push_cast; ring
  rw [dist_eq_norm, hd, norm_neg, Complex.norm_I]
  unfold rad
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 1 / ((k : ℝ) + 1 + 2) ≤ 1 / ((k : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem cover (z : ℂ) (hz : z ∈ Hs) : ∃ k : ℕ, z ∈ Metric.ball (cen k) (rad k) := by
  have hy : 0 < z.im := hz
  obtain ⟨k, hk⟩ := exists_nat_gt ((z.re ^ 2 + z.im ^ 2 + 2) / (2 * z.im))
  refine ⟨k, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  set a : ℝ := (k : ℝ) + 2 with ha
  have hapos : 0 < a := by positivity
  have hka : (k : ℝ) < a := by linarith
  have h1 : z.re ^ 2 + z.im ^ 2 + 2 < 2 * z.im * a := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * z.im)).1 (hk.trans hka)
    linarith
  have hsq : ‖z - cen k‖ ^ 2 = z.re ^ 2 + (z.im - a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, cen_re, cen_im]
    ring
  have hrad : rad k = a - 1 / a := rfl
  have hinv : a * (1 / a) = 1 := by field_simp
  have hlt : ‖z - cen k‖ ^ 2 < rad k ^ 2 := by
    rw [hsq, hrad]
    nlinarith [sq_nonneg (1 / a)]
  exact lt_of_pow_lt_pow_left₀ 2 (rad_pos k).le hlt

theorem eqOn_of_pow_eq {D : Set ℂ} (hD : IsOpen D) (hc : IsPreconnected D) {m : ℕ} (hm : 0 < m)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    {z0 : ℂ} (hz0 : z0 ∈ D) (hfg0 : f z0 = g z0) (hne : f z0 ≠ 0)
    (hpow : ∀ z ∈ D, f z ^ m = g z ^ m) : Set.EqOn f g D := by
  have hfc : ContinuousAt f z0 := (hf.differentiableAt (hD.mem_nhds hz0)).continuousAt
  have hgc : ContinuousAt g z0 := (hg.differentiableAt (hD.mem_nhds hz0)).continuousAt
  set S : ℂ → ℂ := fun z => ∑ i ∈ Finset.range m, f z ^ i * g z ^ (m - 1 - i) with hS
  have hSc : ContinuousAt S z0 := by
    simp only [hS]; fun_prop
  have hS0 : S z0 ≠ 0 := by
    have : S z0 = (m : ℂ) * f z0 ^ (m - 1) := by
      simp only [hS, ← hfg0]
      rw [Finset.sum_congr rfl (g := fun _ => f z0 ^ (m - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [this]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hne)
  have hev : f =ᶠ[nhds z0] g := by
    filter_upwards [hSc.eventually_ne hS0, hD.mem_nhds hz0] with z hz hzD
    have key : S z * (f z - g z) = f z ^ m - g z ^ m := by
      simp only [hS]; exact geom_sum₂_mul (f z) (g z) m
    rw [hpow z hzD, sub_self] at key
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hz)
  exact (hf.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hD) hc hz0 hev

end GlobalTheory.UHPRoot


open GlobalTheory.UHPRoot in
theorem GlobalTheory.KZ.H3.uhp_root : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  classical
  intro h m hm hd hord
  have hHo : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ h Hs := hd.analyticOnNhd hHo
  have hr : ∀ k : ℕ, ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball (cen k) (rad k)) ∧
      ∀ z ∈ Metric.ball (cen k) (rad k), r z ^ m = h z := fun k =>
    GlobalTheory.T.exists_root_ball_of_analyticOrder_dvd h m (cen k) (rad k) hm (rad_pos k) (han.mono (closedBall_sub k))
      (fun τ hτ => hord τ (closedBall_sub k hτ))
  choose r hrd hrp using hr

  have hc0 : cen 0 ∈ Hs := closedBall_sub 0 (Metric.mem_closedBall_self (rad_pos 0).le)
  obtain ⟨k0, hk0⟩ := hord (cen 0) hc0
  have hnt : ¬ ∀ᶠ z in nhds (cen 0), h z = 0 := by
    rw [← analyticOrderAt_eq_top, hk0]; exact ENat.coe_ne_top _
  obtain ⟨z0, hz0h, hz0D⟩ := ((Filter.not_eventually.1 hnt).and_eventually
    (Metric.ball_mem_nhds (cen 0) (rad_pos 0))).exists
  obtain ⟨w0, hw0⟩ := IsAlgClosed.exists_pow_nat_eq (h z0) hm
  have hw0ne : w0 ≠ 0 := by
    rintro rfl; rw [zero_pow hm.ne'] at hw0; exact hz0h hw0.symm
  have hz0k : ∀ k, z0 ∈ Metric.ball (cen k) (rad k) := fun k => ball_mono (Nat.zero_le k) hz0D
  have hrk0 : ∀ k, r k z0 ≠ 0 := by
    intro k h0; have := hrp k z0 (hz0k k); rw [h0, zero_pow hm.ne'] at this; exact hz0h this.symm

  set r' : ℕ → ℂ → ℂ := fun k z => (w0 / r k z0) * r k z with hr'
  have hr'd : ∀ k, DifferentiableOn ℂ (r' k) (Metric.ball (cen k) (rad k)) := fun k =>
    (differentiableOn_const _).mul (hrd k)
  have hr'p : ∀ k, ∀ z ∈ Metric.ball (cen k) (rad k), r' k z ^ m = h z := by
    intro k z hz
    simp only [hr', mul_pow, div_pow, hw0, hrp k z hz, hrp k z0 (hz0k k)]
    rw [div_self hz0h, one_mul]
  have hr'0 : ∀ k, r' k z0 = w0 := by
    intro k; simp only [hr']; rw [div_mul_cancel₀ _ (hrk0 k)]
  have agree_le : ∀ j k, j ≤ k → Set.EqOn (r' j) (r' k) (Metric.ball (cen j) (rad j)) := by
    intro j k hjk
    refine eqOn_of_pow_eq Metric.isOpen_ball (convex_ball _ _).isPreconnected hm (hr'd j)
      ((hr'd k).mono (ball_mono hjk)) (hz0k j) (by rw [hr'0, hr'0]) (by rw [hr'0]; exact hw0ne) ?_
    intro z hz; rw [hr'p j z hz, hr'p k z (ball_mono hjk hz)]
  have agree : ∀ j k w, w ∈ Metric.ball (cen j) (rad j) → w ∈ Metric.ball (cen k) (rad k) →
      r' j w = r' k w := by
    intro j k w hj hk
    rcases le_total j k with hjk | hkj
    · exact agree_le j k hjk hj
    · exact (agree_le k j hkj hk).symm
  choose N hN using cover
  let R : ℂ → ℂ := fun z => if hz : z ∈ Hs then r' (N z hz) z else 0
  refine ⟨R, ?_, ?_⟩
  · intro z hz
    have hzk := hN z hz
    have hev : R =ᶠ[nhds z] r' (N z hz) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzk] with w hw
      have hwH : w ∈ Hs := closedBall_sub _ (Metric.ball_subset_closedBall hw)
      simp only [R, dif_pos hwH]
      exact agree _ _ w (hN w hwH) hw
    exact (((hr'd _).differentiableAt (Metric.isOpen_ball.mem_nhds hzk)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    simp only [R, dif_pos hz]
    exact hr'p _ z (hN z hz)
end

section

open Matrix GlobalTheory.KZ
open Filter Topology

theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  first | exact @GlobalTheory.RootHs.rootHs | exact GlobalTheory.RootHs.rootHs | (intros; apply GlobalTheory.RootHs.rootHs <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.RingMem

theorem inR_const (E : Subring ℂ) (c : ℂ) (hc : c ∈ E) : InR E fun _ => c := by
  refine ⟨1, 0, one_pos, fun _ _ _ => rfl, fun γ => ?_⟩
  have h := GlobalTheory.QFam.QAllSubring.const (R := E) (N := 1) hc
  simpa only [pow_zero, one_mul] using h

theorem lv_lift {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₂ : ℕ) (hN₂ : 0 < N₂) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N * N₂) w' f :=
  GlobalTheory.T.lv_mono_of_dvd_of_le E N (N * N₂) w w' f (Nat.mul_pos hN hN₂) (dvd_mul_right N N₂) hw h

theorem lv_lift' {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₁ : ℕ) (hN₁ : 0 < N₁) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N₁ * N) w' f :=
  GlobalTheory.T.lv_mono_of_dvd_of_le E N (N₁ * N) w w' f (Nat.mul_pos hN₁ hN) (dvd_mul_left N N₁) hw h

theorem inR_add {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f + g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ (max w₁ w₂) (le_max_left _ _) hN₁ hf
  have hg' := lv_lift' N₁ hN₁ (max w₁ w₂) (le_max_right _ _) hN₂ hg
  refine ⟨N₁ * N₂, max w₁ w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.add_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.add (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.add_apply]; ring

theorem inR_mul {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f * g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ w₁ le_rfl hN₁ hf
  have hg' := lv_lift' N₁ hN₁ w₂ le_rfl hN₂ hg
  refine ⟨N₁ * N₂, w₁ + w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.mul_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.mul (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.mul_apply]; ring

theorem inR_neg {E : Subring ℂ} {f : ℍ → ℂ} (hf : InR E f) : InR E (-f) := by
  obtain ⟨N, w, hN, hf⟩ := hf
  refine ⟨N, w, hN, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.neg_apply, hf.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.sub (GlobalTheory.QFam.QAllSubring.const (R := E) (N := N) E.zero_mem) (hf.2 γ)
    refine (congrArg (QAll (· ∈ E) N) (funext fun τ => ?_)).mp h
    simp only [Pi.neg_apply]; ring

def inRSubring (E : Subring ℂ) : Subring (ℍ → ℂ) where
  carrier := {f | InR E f}
  mul_mem' := inR_mul
  one_mem' := inR_const E 1 E.one_mem
  add_mem' := inR_add
  zero_mem' := inR_const E 0 E.zero_mem
  neg_mem' := inR_neg

end GlobalTheory.FN.RingMem

theorem GlobalTheory.FN.mem_ring_iff_inR :
    ∀ E : Subring ℂ, (∀ f : ℍ → ℂ, f ∈ GlobalTheory.FN.ring E ↔ InR E f) ∧ ∀ c ∈ E, InR E fun _ => c := by
  intro E
  refine ⟨fun f => ⟨fun h => ?_, mem_ring_of_inR⟩, fun c hc => GlobalTheory.FN.RingMem.inR_const E c hc⟩
  have hle : GlobalTheory.FN.ring E ≤ GlobalTheory.FN.RingMem.inRSubring E :=
    (Subring.closure_le).mpr fun g hg => hg
  exact hle h
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → ∃ (n : ℕ) (c : Fin n → Polynomial ℂ), (∀ i k, (c i).coeff k ∈ E) ∧ ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0 := by
  first | exact @GlobalTheory.FN.integral_over_jT | exact GlobalTheory.FN.integral_over_jT | (intros; apply GlobalTheory.FN.integral_over_jT <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hs_uniq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  intro Ω _ ε C C' C'' φ φ' h h' hd hd' hs hs' heq
  obtain ⟨hmono, hadd, -, hcongr⟩ := GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε
  set C₀ : ℝ := max C (max C' C'') with hC₀
  have h1 : HS ε C₀ φ h := hmono C C₀ φ h (le_max_left _ _) hs
  have h2 : HS ε C₀ φ' h' := hmono C' C₀ φ' h' (le_trans (le_max_left _ _) (le_max_right _ _)) hs'
  have h3 : HS ε C₀ (φ - φ') (h - h') := ((hadd C₀ φ φ' h h') h1 h2).2
  have h4 : HS ε C₀ (fun _ => (0 : ℂ)) (h - h') := by
    refine hcongr C₀ (φ - φ') (fun _ => 0) (h - h') ?_ h3
    intro z hz
    have : C'' < z.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hz
    simp [heq z this]
  have hdd : Den (h - h') := (((GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω).1 h h' hd hd').2.1)
  by_contra hne
  have hne' : h - h' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_im_gt_ne_zero_of_hs Ω ε C₀ (fun _ => (0 : ℂ)) (h - h') hdd hne' h4
  exact hD ((D + 1 : ℝ) * Complex.I) (by simp) rfl

end GlobalTheory.FN
end
