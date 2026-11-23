module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Convex
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

section

open AlgebraicGeometry CategoryTheory

theorem GlobalTheory.spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
    {X : Scheme} (y y' : Spec (CommRingCat.of K) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom gam) ≫ y = Spec.map (CommRingCat.ofHom gam) ≫ y') :
    y = y' := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
      Spec.map (CommRingCat.ofHom gam) ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
        (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
    intro q ψ
    simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]
  rw [e, e] at h
  have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
  simp only [Sigma.mk.inj_iff] at h2
  obtain ⟨rfl, h3⟩ := h2
  have h4 : φ = φ' := by
    have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
    ext x
    apply gam.injective
    have := congrArg (fun f => f.hom x) h5
    simpa using this
  rw [h4]
end

section

open Filter Topology

namespace GlobalTheory

theorem countable_eq_of_differentiableOn_of_ne {g : ℕ} {U : Set ℂ} {f f' : ℂ → Fin g → ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (hf' : DifferentiableOn ℂ f' U) (hne : ¬ Set.EqOn f f' U) :
    {w | w ∈ U ∧ f w = f' w}.Countable := by
  set T := {w | w ∈ U ∧ f w = f' w} with hT
  have key : ∀ x ∈ T, ({x} : Set ℂ) ∈ 𝓝[T] x := by
    intro x hx
    have h1 : ¬ ∃ᶠ z in 𝓝[≠] x, f z = f' z := fun h =>
      hne ((hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq
        (hf'.analyticOnNhd hU) hc hx.1 h)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff] at h1
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [h1] with z hz hzT
    by_contra hzx
    exact hz hzx hzT.2
  obtain ⟨t, -, ht, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin key
  refine ht.mono fun x hx => ?_
  have := hcov hx
  simpa using this

theorem exists_const_substitution_of_holomorphic_families :
    ∀ (L D : Type) [Countable D] (g : ℕ) (act : D → L → L) (U : Set ℂ) (s s' : ℂ → L → Fin g → ℂ), IsOpen U → IsPreconnected U → U.Nonempty → (∀ a, DifferentiableOn ℂ (fun w => s w a) U) → (∀ a, DifferentiableOn ℂ (fun w => s' w a) U) → (∀ w ∈ U, ∃ δ, ∀ a, s' w a = s w (act δ a)) → ∃ δ, ∀ w ∈ U, ∀ a, s' w a = s w (act δ a) := by
  intro L D _ g act U s s' hU hc hne hs hs' h
  by_contra hcon
  push_neg at hcon
  choose w hw a ha using hcon
  have hcount : ∀ δ, {z | z ∈ U ∧ s' z (a δ) = s z (act δ (a δ))}.Countable := fun δ =>
    countable_eq_of_differentiableOn_of_ne hU hc (hs' (a δ)) (hs (act δ (a δ)))
      (fun hE => ha δ (hE (hw δ)))
  have hUc : U.Countable := by
    refine (Set.countable_iUnion hcount).mono fun z hz => ?_
    obtain ⟨δ, hδ⟩ := h z hz
    exact Set.mem_iUnion.2 ⟨δ, hz, hδ _⟩
  have hd : Dense Uᶜ := hUc.dense_compl ℝ
  obtain ⟨x, hx1, hx2⟩ := hd.inter_open_nonempty U hU hne
  exact hx2 hx1

end GlobalTheory
end

section

namespace GlobalTheory.DifferentiableDet

theorem differentiableAt_det {σ : Type} [Fintype σ] [DecidableEq σ] (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (h : ∀ (i j : σ), DifferentiableAt ℝ (fun (s : ℝ) ↦ M s i j) t) :
    DifferentiableAt ℝ (fun (s : ℝ) ↦ Matrix.det (M s)) t := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun π _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  exact (HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => M s (π i) i)
    (fun i _ => (h (π i) i).hasDerivAt)).differentiableAt

end GlobalTheory.DifferentiableDet
end

section

open Complex MeasureTheory

namespace GlobalTheory

theorem periodic_strip_shift_nonneg (c : ℝ) (f : ℂ → ℂ) (m : ℤ)
    (hf : DifferentiableOn ℂ f {s : ℂ | s.re < c})
    (hper : ∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m)
    (hpos : ∀ s : ℂ, s.re < c → 0 < (f s).im) : 0 ≤ m := by
  have hcont : ContinuousOn f {s : ℂ | s.re < c} := hf.continuousOn
  have hvert : ∀ x : ℝ, x < c → IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume 0 (2 * Real.pi) := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro y _
    simp [hx]
  have hhor : ∀ (x₁ x₂ : ℝ), x₁ ≤ x₂ → x₂ < c → IntervalIntegrable (fun x : ℝ => f (x : ℂ)) volume x₁ x₂ := by
    intro x₁ x₂ h12 h2
    apply ContinuousOn.intervalIntegrable
    refine hcont.comp (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le h12] at hx
    simp only [Set.mem_setOf_eq, ofReal_re]
    linarith [hx.2]
  have hVim : ∀ x : ℝ, x < c → 0 ≤ (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x + y * I)).im := by
    intro x hx
    have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
    have hc := Complex.imCLM.intervalIntegral_comp_comm (hvert x hx)
    simp only [Complex.imCLM_apply] at hc
    rw [← hc]
    apply intervalIntegral.integral_nonneg h2pi
    intro y _
    exact (hpos _ (by simp [hx])).le
  have key : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → x₂ < c →
      (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₁ + y * I)).im
        = (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f (x₂ + y * I)).im + m * (x₂ - x₁) := by
    intro x₁ x₂ h12 h2c
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (x₁ : ℂ)
      ((x₂ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * I) ?_
    · simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add, ofReal_zero] at hrect
      have htop : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
          = (∫ x : ℝ in x₁..x₂, f (x : ℂ)) + (m : ℂ) * ((x₂ - x₁ : ℝ) : ℂ) := by
        have hc : (∫ x : ℝ in x₁..x₂, f (x + ((2 * Real.pi : ℝ) : ℂ) * I))
            = ∫ x : ℝ in x₁..x₂, (f (x : ℂ) + m) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le h12] at hx
          have hxc : (x : ℂ).re < c := by simp; linarith [hx.2]
          simp only
          rw [← hper _ hxc]
          congr 1
          push_cast
          ring
        rw [hc, intervalIntegral.integral_add (hhor x₁ x₂ h12 h2c) intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp [mul_comm]
      rw [htop] at hrect
      have hre := congrArg Complex.re hrect
      simp at hre
      linarith
    · apply hf.mono
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      simp only [ofReal_re, add_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hz
      rw [Set.uIcc_of_le h12] at hz
      show z.re < c
      linarith [hz.1.2]
  by_contra hm
  push_neg at hm
  have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
  set a := (∫ y : ℝ in (0:ℝ)..(2 * Real.pi), f ((c - 1 : ℝ) + y * I)).im with ha
  have ha0 : 0 ≤ a := hVim (c - 1) (by linarith)
  have h1 := key (c - 1 - (a + 1)) (c - 1) (by linarith) (by linarith)
  have h2 := hVim (c - 1 - (a + 1)) (by linarith)
  rw [h1] at h2
  nlinarith [mul_le_mul_of_nonneg_right hm1 (by linarith : (0:ℝ) ≤ a + 1)]

end GlobalTheory
end

section

open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneLocBound

lemma isOpen_offHyperplanes (n a : ℕ) (ρ : ℝ) :
    IsOpen {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
  have : {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      ball 0 ρ ∩ ⋂ k ∈ (Finset.univ.filter fun k : Fin n => (k : ℕ) < a),
        (fun z : Fin n → ℂ => z k) ⁻¹' {0}ᶜ := by
    ext z; simp
  rw [this]
  exact isOpen_ball.inter (isOpen_biInter_finset fun k _ =>
    (continuous_apply k).isOpen_preimage _ isOpen_compl_singleton)

lemma prod_update_eq {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℕ) (k : Fin n) (t : ℂ) :
    ∏ j, ‖Function.update z k t j‖ ^ m j =
      ‖t‖ ^ m k * ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma norm_le_of_circle {n a : ℕ} {ρ r : ℝ} {Φ : (Fin n → ℂ) → ℂ} {m : Fin n → ℕ}
    (hext : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t)
    (hΦ : DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0})
    (hgr : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1)
    {z₀ z : Fin n → ℂ} (hr : 0 < r) (hsub : ball z₀ (2 * r) ⊆ ball 0 ρ)
    (hz : z ∈ closedBall z₀ r) (hgen : ∀ j, z j ≠ 0) {k : Fin n} (hk0 : z₀ k = 0)
    {B : ℝ} (hB : ∀ t : ℂ, ‖t‖ = r → ‖Φ (Function.update z k t)‖ ≤ B) : ‖Φ z‖ ≤ B := by
  set H : ℂ → ℂ := fun t => Φ (Function.update z k t) with hH
  have hmem : ∀ t ∈ ball (0 : ℂ) (2 * r), Function.update z k t ∈ ball z₀ (2 * r) := by
    intro t ht
    rw [mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj; simpa [hk0] using ht
    · rw [Function.update_of_ne hj]
      exact lt_of_le_of_lt ((dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)) (by linarith)
  have hU : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 → Function.update z k t ∈
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    intro t ht ht0
    refine ⟨hsub (hmem t ht), fun j _ => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using ht0
    · rw [Function.update_of_ne hj]; exact hgen j
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) (2 * r) \ {0}) := by
    intro t ht
    have hd := (hΦ _ (hU t ht.1 ht.2)).differentiableAt
      ((isOpen_offHyperplanes n a ρ).mem_nhds (hU t ht.1 ht.2))
    exact (hd.comp t (hasFDerivAt_update z t).differentiableAt).differentiableWithinAt
  set P := ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j with hPdef
  have hP : 0 < P := Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hgen j)) _
  have hHg : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 →
      ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ m k ≤ 1 / P := by
    intro t ht ht0
    have h1 := hgr _ (hU t ht ht0).1 (hU t ht ht0).2
    rw [prod_update_eq, ← mul_assoc] at h1
    exact (le_div_iff₀ hP).2 h1
  obtain ⟨G, hGd, hGH⟩ := hext H (2 * r) (1 / P) (m k) (by linarith) hHd hHg
  have hcl : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hzk : z k ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall]
    have := dist_le_pi_dist z z₀ k
    rw [hk0] at this
    exact this.trans (mem_closedBall.1 hz)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hGd.diffContOnCl_ball hcl) (C := B) ?_ (by rw [closure_ball 0 hr.ne']; exact hzk)
  · rw [hGH _ (hcl hzk) (hgen k)] at key
    simpa [H] using key
  · intro t ht
    rw [frontier_ball 0 hr.ne', mem_sphere, dist_zero_right] at ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; linarith
    have htb : t ∈ ball (0 : ℂ) (2 * r) := by rw [mem_ball, dist_zero_right]; linarith
    rw [hGH t htb ht0]
    exact hB t ht

theorem locally_bounded : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  intro hext n a ρ Φ m hρ hΦ hgr z₀ hz₀
  have hUo := isOpen_offHyperplanes n a ρ
  have hδ : 0 < ρ - ‖z₀‖ := by rw [mem_ball, dist_zero_right] at hz₀; linarith
  obtain ⟨r, hr0, hrδ, hrk⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r < ρ - ‖z₀‖ ∧ ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρ - ‖z₀‖ := by
      apply nhdsWithin_le_nhds
      have : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
      exact this.eventually (gt_mem_nhds hδ)
    have h3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
      rw [eventually_all]; intro k
      by_cases hk : z₀ k = 0
      · exact Eventually.of_forall fun _ h => absurd hk h
      · exact (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ‖z₀ k‖ from
          nhdsWithin_le_nhds (gt_mem_nhds (norm_pos_iff.2 hk))).mono fun r hr _ => hr
    exact (h1.and (h2.and h3)).exists
  have hsub : ball z₀ (2 * r) ⊆ ball 0 ρ := ball_subset_ball' (by rw [dist_zero_right]; linarith)
  set K := closedBall z₀ r ∩ {ζ : Fin n → ℂ | ∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → ‖ζ k‖ = r}
    with hK
  have hKc : IsCompact K := (isCompact_closedBall z₀ r).inter_right (by
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_norm.comp (continuous_apply k)) continuous_const)
  have hKU : K ⊆ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    rintro ζ ⟨hζ, hζc⟩
    refine ⟨hsub (closedBall_subset_ball (by linarith) hζ), fun k hk => ?_⟩
    by_cases h0 : z₀ k = 0
    · intro h; have := hζc k hk h0; rw [h, norm_zero] at this; linarith
    · intro h
      have h1 := dist_le_pi_dist ζ z₀ k
      rw [h, dist_comm, dist_zero_right] at h1
      have := hrk k h0
      linarith [mem_closedBall.1 hζ]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hKU)
  have hind : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, (∀ j, z j ≠ 0) → z ∈ closedBall z₀ r →
      (∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → k ∉ S → ‖z k‖ = r) → ‖Φ z‖ ≤ M := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro z _ hz hc
      exact hM z ⟨hz, fun k hk h0 => hc k hk h0 (by simp)⟩
    · intro k S hkS ih z hgen hz hc
      by_cases hk : (k : ℕ) < a ∧ z₀ k = 0
      · refine norm_le_of_circle hext hΦ hgr hr0 hsub hz hgen hk.2 fun t ht => ?_
        apply ih
        · intro j
          by_cases hj : j = k
          · subst hj; simp only [Function.update_self]; rintro rfl; simp at ht; linarith
          · rw [Function.update_of_ne hj]; exact hgen j
        · rw [mem_closedBall, dist_pi_le_iff hr0.le]
          intro j
          by_cases hj : j = k
          · subst hj; simp [hk.2, ht]
          · rw [Function.update_of_ne hj]
            exact (dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)
        · intro j hj h0 hjS
          by_cases hjk : j = k
          · subst hjk; simpa using ht
          · rw [Function.update_of_ne hjk]; exact hc j hj h0 (by simp [hjk, hjS])
      · apply ih z hgen hz
        intro j hj h0 hjS
        by_cases hjk : j = k
        · subst hjk; exact absurd ⟨hj, h0⟩ hk
        · exact hc j hj h0 (by simp [hjk, hjS])
  refine ⟨ball z₀ r, ball_mem_nhds z₀ hr0, M, fun z hzV hzρ hza => ?_⟩
  have hzU : z ∈ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} :=
    ⟨hzρ, hza⟩
  let w : ℂ → Fin n → ℂ := fun s j => if z j = 0 then s else z j
  have hwc : Continuous w := continuous_pi fun j => by
    by_cases h : z j = 0
    · simp only [w, h, if_true]; exact continuous_id
    · simp only [w, h, if_false]; exact continuous_const
  have hw0 : w 0 = z := funext fun j => by by_cases h : z j = 0 <;> simp [w, h]
  have hΦz : ContinuousAt Φ z := (hΦ.differentiableAt (hUo.mem_nhds hzU)).continuousAt
  have hT : Tendsto (fun s => Φ (w s)) (𝓝[≠] (0 : ℂ)) (𝓝 (Φ z)) := by
    have hc : ContinuousAt (Φ ∘ w) 0 :=
      ContinuousAt.comp (x := 0) (by rw [hw0]; exact hΦz) hwc.continuousAt
    have h := hc.tendsto
    rw [Function.comp_apply, hw0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖Φ (w s)‖ ≤ M := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℂ), w s ∈ ball z₀ r :=
      hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact isOpen_ball.mem_nhds hzV)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
    apply hind Finset.univ (w s)
    · intro j
      simp only [w]
      split_ifs with h
      · exact hs0
      · exact h
    · exact ball_subset_closedBall hs
    · intro k _ _ hk; exact absurd (Finset.mem_univ k) hk
  exact le_of_tendsto hT.norm hev

end GlobalTheory.HyperplaneLocBound
end

section

open Set

namespace GlobalTheory

theorem punctured_unit_disc_eq_exp_image :
    Metric.ball (0:ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by
  ext w
  constructor
  · rintro ⟨hb, h0⟩
    have h0' : w ≠ 0 := h0
    refine ⟨Complex.log w, ?_, Complex.exp_log h0'⟩
    rw [Set.mem_setOf_eq, Complex.log_re]
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact Real.log_neg (norm_pos_iff.mpr h0') hb
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hz
    · exact Complex.exp_ne_zero z

theorem isPreconnected_punctured_unit_disc :
    IsPreconnected (Metric.ball (0:ℂ) 1 \ {0}) := by
  rw [punctured_unit_disc_eq_exp_image]
  exact (convex_halfSpace_re_lt 0).isPreconnected.image _ Complex.continuous_exp.continuousOn

theorem isPreconnected_polydisc_first_coords_ne_zero :
    ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  intro n a ha
  have hS : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
      = Set.pi univ (fun k : Fin n => if (k:ℕ) < a then Metric.ball (0:ℂ) 1 \ {0} else Metric.ball (0:ℂ) 1) := by
    ext z
    rw [ball_pi _ one_pos]
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply]
    constructor
    · rintro ⟨hb, hne⟩ k
      split_ifs with hk
      · exact ⟨hb k, fun h => hne ⟨k, hk⟩ (by simpa using h)⟩
      · exact hb k
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have := h k
        split_ifs at this
        · exact this.1
        · exact this
      · have := h (Fin.castLE ha i)
        rw [if_pos (by simp)] at this
        exact this.2
  rw [hS]
  apply isPreconnected_univ_pi
  intro k
  split_ifs
  · exact isPreconnected_punctured_unit_disc
  · exact (convex_ball (0:ℂ) 1).isPreconnected

end GlobalTheory
end
