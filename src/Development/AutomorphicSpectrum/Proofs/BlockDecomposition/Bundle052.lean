module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle007
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Filter
open scoped Topology

namespace GlobalTheory.CompanionTheory.Param

theorem continuousOn_differentiableOn_integral :
    ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
      [TopologicalSpace T] [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U →
      ∀ F : ℂ → T → Y → ℂ,
      ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
      (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
      (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧
        ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
      ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
        ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  intro Y T _ _ _ _ _ μ U hU F hF hdiff hdom
  have hGat : ∀ z ∈ U, ∀ (t : T) (y : Y),
      ContinuousAt (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (z, t, y) := fun z hz t y =>
    hF.continuousAt ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz (Set.mem_univ _)))
  have hslice : ∀ z ∈ U, ∀ t : T, Continuous (fun y => F z t y) := fun z hz t =>
    hF.comp_continuous (f := fun y : Y => (z, t, y)) (by fun_prop)
      fun y => Set.mk_mem_prod hz (Set.mem_univ _)
  refine ⟨?_, fun t => ?_⟩
  · rintro ⟨z₀, t₀⟩ ⟨hz₀, -⟩
    obtain ⟨V, hV, N, hN, w, hw, hbound⟩ := hdom z₀ hz₀ t₀
    refine ContinuousAt.continuousWithinAt ?_
    refine MeasureTheory.continuousAt_of_dominated (bound := w) ?_ ?_ hw ?_
    · have hmem : U ×ˢ (Set.univ : Set T) ∈ 𝓝 (z₀, t₀) :=
        (hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz₀ (Set.mem_univ _))
      filter_upwards [hmem] with x hx
      exact (hslice x.1 hx.1 x.2).aestronglyMeasurable
    · have hmem : V ×ˢ N ∈ 𝓝 (z₀, t₀) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod hV hN
      filter_upwards [hmem] with x hx
      exact Filter.Eventually.of_forall fun y => hbound x.1 hx.1 x.2 hx.2 y
    · exact Filter.Eventually.of_forall fun y =>
        ContinuousAt.comp_of_eq (f := fun x : ℂ × T => (x.1, x.2, y)) (hGat z₀ hz₀ t₀ y)
          (by fun_prop) rfl
  · obtain ⟨h, -⟩ := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ)
      (F := fun y z => F z t y) hU (fun z hz => (hslice z hz t).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => hdiff t y) (fun z hz => by
        obtain ⟨V, hV, N, hN, w, hw, hb⟩ := hdom z hz t
        exact ⟨V, hV, w, hw, Filter.Eventually.of_forall fun y z' hz' =>
          hb z' hz' t (mem_of_mem_nhds hN) y⟩)
    exact h

end GlobalTheory.CompanionTheory.Param
end

section

open Topology Filter

namespace GlobalTheory.CompanionTheory.HolFamily

theorem continuousOn_deriv_param {G : Type} [TopologicalSpace G] {U : Set ℂ} (hU : IsOpen U)
    {E : ℂ → G → ℂ} (hd : ∀ g, DifferentiableOn ℂ (E · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ)) :
    ContinuousOn (fun y : ℂ × G => deriv (E · y.2) y.1) (U ×ˢ Set.univ) := by
  have hc' : ContinuousOn (fun q : G × ℂ => E q.2 q.1) (Set.univ ×ˢ U) :=
    hc.comp continuous_swap.continuousOn fun q hq => ⟨hq.2, Set.mem_univ _⟩
  have h := continuousOn_deriv_family G U hU (fun g z => E z g) hc' hd
  exact h.comp continuous_swap.continuousOn fun y hy => ⟨Set.mem_univ _, hy.1⟩

theorem deriv_param_invariant {G : Type} [Group G] (Γ : Subgroup G) {U : Set ℂ} (hU : IsOpen U)
    {E : ℂ → G → ℂ} (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) :
    ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, deriv (E · (γ * g)) z = deriv (E · g) z := by
  intro z hz γ hγ g
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw using hinv w hw γ hγ g

theorem hasDerivAt_functional {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (Lf : (G → ℂ) → ℂ)
    (hlin : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' →
      (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) →
      Lf (a • f + f') = a * Lf f + Lf f')
    {C : Set G} (hC : IsCompact C)
    (hb : ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    {U : Set ℂ} {E : ℂ → G → ℂ} (hU : IsOpen U) (hd : ∀ g, DifferentiableOn ℂ (E · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ))
    (hinv : ∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun w => Lf (E w)) (Lf fun g => deriv (E · g) z) z := by
  obtain ⟨D, hD⟩ : ∃ D : G → ℂ, D = fun g => deriv (E · g) z := ⟨_, rfl⟩
  rw [← hD]
  have hD' := continuousOn_deriv_param hU hd hc
  have hslice : ∀ w ∈ U, Continuous (E w) := fun w hw =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hw, Set.mem_univ _⟩
  have hDc : Continuous D := by
    rw [hD]
    exact hD'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hz, Set.mem_univ _⟩
  have hDinv : ∀ γ ∈ Γ, ∀ g, D (γ * g) = D g := by
    rw [hD]
    intro γ hγ g
    exact deriv_param_invariant Γ hU hinv z hz γ hγ g
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hcpos
  have hunif : ∀ᶠ ζ in 𝓝 z, ∀ g ∈ C, ‖deriv (E · g) ζ - deriv (E · g) z‖ ≤ c := by
    apply hC.eventually_forall_of_forall_eventually
    intro g _
    have hcont : ContinuousAt (fun y : ℂ × G => deriv (E · y.2) y.1) (z, g) :=
      hD'.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, Set.mem_univ _⟩)
    have hcont2 : ContinuousAt (fun y : ℂ × G => deriv (E · y.2) z) (z, g) :=
      hcont.comp_of_eq (continuous_const.prodMk continuous_snd).continuousAt rfl
    have h1 := Metric.tendsto_nhds.mp hcont (c / 2) (by positivity)
    have h2 := Metric.tendsto_nhds.mp hcont2 (c / 2) (by positivity)
    filter_upwards [h1, h2] with y hy1 hy2
    rw [dist_eq_norm] at hy1 hy2
    calc ‖deriv (E · y.2) y.1 - deriv (E · y.2) z‖
        = ‖(deriv (E · y.2) y.1 - deriv (E · g) z) - (deriv (E · y.2) z - deriv (E · g) z)‖ := by
          congr 1
          ring
      _ ≤ ‖deriv (E · y.2) y.1 - deriv (E · g) z‖ + ‖deriv (E · y.2) z - deriv (E · g) z‖ :=
          norm_sub_le _ _
      _ ≤ c := by linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hunif.and (hU.mem_nhds hz))
  filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
  have hwU : w ∈ U := (hball w hw).2
  have hbound : ∀ g ∈ C, ‖E w g - E z g - (w - z) * D g‖ ≤ c * ‖w - z‖ := by
    intro g hg
    rw [hD]
    have hφ : ∀ ζ ∈ Metric.ball z δ, HasDerivAt (fun ζ => E ζ g - ζ * deriv (E · g) z)
        (deriv (E · g) ζ - 1 * deriv (E · g) z) ζ := by
      intro ζ hζ
      have hdiff : DifferentiableAt ℂ (E · g) ζ := (hd g).differentiableAt (hU.mem_nhds (hball ζ hζ).2)
      exact hdiff.hasDerivAt.sub ((hasDerivAt_id ζ).mul_const _)
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun ζ hζ => (hφ ζ hζ).differentiableAt)
      (fun ζ hζ => by rw [(hφ ζ hζ).deriv, one_mul]; exact (hball ζ hζ).1 g hg)
      (convex_ball z δ) (Metric.mem_ball_self hδ) hw
    calc ‖E w g - E z g - (w - z) * deriv (E · g) z‖
        = ‖(E w g - w * deriv (E · g) z) - (E z g - z * deriv (E · g) z)‖ := by
          congr 1
          ring
      _ ≤ c * ‖w - z‖ := hmv
  have hEw := hslice w hwU
  have hEz := hslice z hz
  set F : G → ℂ := fun g => E w g - E z g - (w - z) * D g with hF
  have hFc : Continuous F := (hEw.sub hEz).sub (continuous_const.mul hDc)
  have hFi : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g := by
    intro γ hγ g
    simp only [hF, hinv w hwU γ hγ g, hinv z hz γ hγ g, hDinv γ hγ g]
  have hGc : Continuous ((w - z) • D + E z) := (hDc.const_smul _).add hEz
  have hGi : ∀ γ ∈ Γ, ∀ g, ((w - z) • D + E z) (γ * g) = ((w - z) • D + E z) g := by
    intro γ hγ g
    simp only [Pi.add_apply, Pi.smul_apply, hDinv γ hγ g, hinv z hz γ hγ g]
  have hsplit : E w = (1 : ℂ) • F + ((w - z) • D + E z) := by
    funext g
    simp only [hF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 := hlin 1 F ((w - z) • D + E z) hFc hGc hFi hGi
  have h2 := hlin (w - z) D (E z) hDc hEz hDinv (hinv z hz)
  have hLF : ‖Lf F‖ ≤ c * ‖w - z‖ := hb F _ hFc hFi hbound
  rw [hsplit, h1, h2, smul_eq_mul]
  have hring : 1 * Lf F + ((w - z) * Lf D + Lf (E z)) - Lf (E z) - (w - z) * Lf D = Lf F := by ring
  rw [hring]
  exact hLF

theorem iteratedDeriv_functional {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
    (Lf : (G → ℂ) → ℂ)
    (hlin : ∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' →
      (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) →
      Lf (a • f + f') = a * Lf f + Lf f')
    {C : Set G} (hC : IsCompact C)
    (hb : ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) →
      (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M)
    {U : Set ℂ} (hU : IsOpen U) (j : ℕ) :
    ∀ E : ℂ → G → ℂ, (∀ g, DifferentiableOn ℂ (E · g) U) →
      ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ) →
      (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) →
      ∀ z ∈ U, iteratedDeriv j (fun z => Lf (E z)) z = Lf fun g => iteratedDeriv j (E · g) z := by
  induction j with
  | zero =>
    intro E _ _ _ z _
    simp
  | succ j ih =>
    intro E hd hc hinv z hz
    have key := ih (fun z g => deriv (E · g) z) (fun g => (hd g).deriv hU)
      (continuousOn_deriv_param hU hd hc) (deriv_param_invariant Γ hU hinv) z hz
    have hloc : deriv (fun z => Lf (E z)) =ᶠ[𝓝 z] fun z => Lf (fun g => deriv (E · g) z) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact (hasDerivAt_functional Γ Lf hlin hC hb hU hd hc hinv hw).deriv
    rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq j hloc, key]
    congr 1
    funext g
    rw [iteratedDeriv_succ']

theorem functional_commutes_iteratedDeriv :
    ∀ {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ), (∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f') → (∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M) → ∀ (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) → DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧ ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z := by
  intro G _ _ Γ Lf hlin hCex U Ê hU hd hc hinv
  obtain ⟨C, hC, hb⟩ := hCex
  exact ⟨fun z hz => (hasDerivAt_functional Γ Lf hlin hC hb hU hd hc hinv hz).differentiableAt.differentiableWithinAt,
    fun z hz j => iteratedDeriv_functional Γ Lf hlin hC hb hU j Ê hd hc hinv z hz⟩

end GlobalTheory.CompanionTheory.HolFamily
end

section

open Topology Filter

theorem _root_.GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family : ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | exact GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | (intros; apply GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family <;> assumption)
end

section


theorem _root_.GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment : ∀ (f g : ℂ → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ f (Metric.ball 0 ρ) → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ s : ℝ, |s| < ρ → f s = g s) → ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0 := by
  first | exact @GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | exact GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | (intros; apply GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points <;> assumption)
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian

lemma integrable_gauss_complex :
    Integrable (fun w : ℂ => Real.exp (-Real.pi * ‖w‖ ^ 2)) := by
  have hb : 0 < ((Real.pi : ℂ)).re := by simpa using Real.pi_pos
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, Complex.norm_exp]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma integrable_gauss (m n : ℕ) :
    Integrable (fun v : Fin m → Fin n → ℂ =>
      Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin n) (w : ℂ) => Real.exp (-Real.pi * ‖w‖ ^ 2))
      (μ := fun _ => volume) (fun _ => integrable_gauss_complex)
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-Real.pi * ‖v a j‖ ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin m) (u : Fin n → ℂ) => ∏ j, Real.exp (-Real.pi * ‖u j‖ ^ 2))
      (μ := fun _ => volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

noncomputable def dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (z : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

lemma differentiable_dilated (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Differentiable ℂ (dilated m n X v) := by
  unfold dilated
  fun_prop

lemma continuous_dilated (m n : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    Continuous (fun v : Fin m → Fin n → ℂ => dilated m n X v z) := by
  unfold dilated
  first
  | fun_prop
  | exact continuous_const.mul (Continuous.cexp (continuous_const.mul
      (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun j _ => continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_norm.comp ((continuous_apply j).comp (continuous_apply a))).pow 2)))))

lemma eventually_small (m n : ℕ) (X : Fin n → ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, (∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re) ∧
      ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
  have hre : ∀ j, ∀ᶠ z : ℂ in 𝓝 0, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re := by
    intro j
    have hc : Continuous fun z : ℂ => (Complex.exp (2 * z * X j)).re := by fun_prop
    have h0 : (1 / 2 : ℝ) < (Complex.exp (2 * 0 * X j)).re := by norm_num
    exact ((hc.tendsto 0).eventually (lt_mem_nhds h0)).mono fun z hz => hz.le
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
    have hc : Continuous fun z : ℂ => ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ := by fun_prop
    have h0 : ‖Complex.exp ((m : ℂ) * 0 * ∑ j, (X j : ℂ))‖ < 2 := by norm_num
    exact ((hc.tendsto 0).eventually (gt_mem_nhds h0)).mono fun z hz => hz.le
  exact (Filter.eventually_all.2 hre).and hn

lemma norm_dilated_le (m n : ℕ) (X : Fin n → ℝ) (z : ℂ)
    (h1 : ∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re)
    (h2 : ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2) (v : Fin m → Fin n → ℂ) :
    ‖dilated m n X v z‖ ≤ 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  unfold dilated
  rw [norm_mul]
  have hre : (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)).re
      = -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 := by
    have e : (-(2 * Real.pi : ℂ)) = ((-(2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Complex.re_sum, Complex.re_mul_ofReal]
  have hS : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 ≤
      ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (h1 j) (sq_nonneg _)
  have hT : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 = (1 / 2) * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    simp only [Finset.mul_sum]
  have key : -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 ≤
      -Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    rw [hT] at hS
    nlinarith [Real.pi_pos]
  refine mul_le_mul h2 ?_ (norm_nonneg _) (by norm_num)
  rw [Complex.norm_exp, hre]
  exact Real.exp_le_exp.2 key

theorem holomorphic_integral (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ)
    (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  have hcm : ∀ (c : ℂ) (f : ℂ → ℂ) (r : ℕ),
      iteratedDeriv r (fun w => c * f w) = fun w => c * iteratedDeriv r f w := by
    intro c f r
    induction r with
    | zero => simp only [iteratedDeriv_zero]
    | succ r ih => rw [iteratedDeriv_succ, ih, deriv_const_mul_field', iteratedDeriv_succ]
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_small m n X)
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have hd : ∀ v : Fin m → Fin n → ℂ,
      DifferentiableOn ℂ (fun z => K v * dilated m n X v z) (Metric.ball (0 : ℂ) ρ) :=
    fun v => ((differentiable_dilated m n X v).const_mul (K v)).differentiableOn
  have hm : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      AEStronglyMeasurable (fun v : Fin m → Fin n → ℂ => K v * dilated m n X v z) volume :=
    fun z _ => (hK.mul (continuous_dilated m n X z)).aestronglyMeasurable
  have hb : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ 𝓝 z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v,
        ‖K v * dilated m n X v z‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem,
      fun v => 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2),
      (integrable_gauss m n).const_mul 2, ?_⟩
    intro z hz v
    obtain ⟨h1, h2⟩ := hsmall z hz.2
    rw [norm_mul]
    calc ‖K v‖ * ‖dilated m n X v z‖
        ≤ 1 * (2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) :=
          mul_le_mul (hK1 v) (norm_dilated_le m n X z h1 h2 v) (norm_nonneg _) zero_le_one
      _ = 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := one_mul _
  have hstep := integral_step (μ := volume) hU (fun z v => K v * dilated m n X v z) hd hm hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro z hz
    exact (hstep.1 z hz).differentiableAt.differentiableWithinAt
  · intro r
    have h := iteratedDeriv_integral (μ := volume) hU r (fun z v => K v * dilated m n X v z)
      hd hm hb 0 (Metric.mem_ball_self hρ)
    refine h.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact congrFun (hcm (K v) _ r) 0

end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
end

section

open MeasureTheory
open scoped Matrix

namespace GlobalTheory.CompanionTheory.HolMean.GaussianFamily

lemma integrable_gauss_complex {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun w : ℂ => Real.exp (-δ * ‖w‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
    (b := (δ : ℂ)) (by simpa using hδ) 0 0
  have h2 := h.norm
  refine h2.congr (ae_of_all _ fun w => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  have : (-(δ : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) = ((-δ * ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

lemma integrable_gauss (m n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2))
      (volume : Measure (Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℂ))
      (f := fun _ (w : ℂ) => Real.exp (-δ * ‖w‖ ^ 2)) fun _ => integrable_gauss_complex hδ
    exact this
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2))
      (volume : Measure (Fin m → Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure (Fin n → ℂ)))
      (f := fun _ (u : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) fun _ => h1
    exact this
  refine h2.congr (ae_of_all _ fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]

theorem main : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ →
    (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) →
    ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2)
      (Metric.ball 0 ρ ×ˢ Set.univ) →
    (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) →
    ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) →
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 =
          ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤
          C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  intro m n Φ ρ C δ hρ hδ hd hc hb K hK hK1
  let G : ℂ → (Fin m → Fin n → ℂ) → ℂ := fun z v => K v * Φ z v
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hcv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Continuous (fun v => Φ z v) := fun z hz =>
    hc.comp_continuous (f := fun v : Fin m → Fin n → ℂ => (z, v)) (by fun_prop)
      (fun v => ⟨hz, Set.mem_univ _⟩)
  have hdG : ∀ v, DifferentiableOn ℂ (fun z => G z v) (Metric.ball 0 ρ) := fun v =>
    (hd v).const_mul (K v)
  have hmG : ∀ z ∈ Metric.ball (0 : ℂ) ρ, AEStronglyMeasurable (G z) volume := fun z hz =>
    (hK.mul (hcv z hz)).aestronglyMeasurable
  have hg : Integrable (fun v : Fin m → Fin n → ℂ =>
      C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := (integrable_gauss m n hδ).const_mul C
  have hbG : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ nhds z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v, ‖G z v‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem, _, hg, fun z hz v => ?_⟩
    calc ‖G z v‖ = ‖K v‖ * ‖Φ z v‖ := norm_mul _ _
      _ ≤ 1 * ‖Φ z v‖ := mul_le_mul_of_nonneg_right (hK1 v) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb z hz.2 v
  have hjoint : ∀ r : ℕ, ContinuousOn
      (fun q : (Fin m → Fin n → ℂ) × ℂ => iteratedDeriv r (fun z => Φ z q.1) q.2)
      (Set.univ ×ˢ Metric.ball 0 ρ) := by
    refine GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family (Fin m → Fin n → ℂ)
      (Metric.ball 0 ρ) hU (fun v z => Φ z v) ?_ hd
    exact hc.comp (f := fun q : (Fin m → Fin n → ℂ) × ℂ => (q.2, q.1)) (by fun_prop)
      (fun q hq => ⟨hq.2, Set.mem_univ _⟩)
  refine ⟨ρ, hρ, ?_, fun r => ⟨?_, ?_, ?_⟩⟩
  · intro z hz
    exact ((GlobalTheory.CompanionTheory.HolMean.integral_step hU G hdG hmG hbG).1 z hz).differentiableAt.differentiableWithinAt
  · have key := GlobalTheory.CompanionTheory.HolMean.iteratedDeriv_integral hU r G hdG hmG hbG 0 h0
    refine key.trans (integral_congr_ae (ae_of_all _ fun v => ?_))
    exact iteratedDeriv_const_mul_field (K v) (fun z => Φ z v)
  · exact (hjoint r).comp_continuous (f := fun v : Fin m → Fin n → ℂ => (v, (0 : ℂ)))
      (by fun_prop) (fun v => ⟨Set.mem_univ _, h0⟩)
  · refine ⟨r.factorial * C / (ρ / 2) ^ r, fun v => ?_⟩
    have hR : 0 < ρ / 2 := by positivity
    have hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball 0 ρ :=
      Metric.closedBall_subset_ball (by linarith)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0)
      (C := C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) (f := fun z => Φ z v) r hR
      ((hd v).diffContOnCl_ball hsub)
      (fun z hz => hb z (hsub (Metric.sphere_subset_closedBall hz)) v)
    refine h.trans (le_of_eq ?_)
    ring

end GlobalTheory.CompanionTheory.HolMean.GaussianFamily
end
