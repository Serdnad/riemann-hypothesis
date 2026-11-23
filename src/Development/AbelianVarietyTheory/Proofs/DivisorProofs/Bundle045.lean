module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory
namespace SchwartzIntegralExchange

theorem exists_factor {S X : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (J : S →ₗ[ℂ] X) (Λ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ w, ‖Λ w‖ ≤ C * ‖J w‖) :
    ∃ g : X →L[ℂ] ℂ, ∀ w, g (J w) = Λ w := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective J.rangeRestrict
    J.range_rangeRestrict
  have hr' : ∀ y : LinearMap.range J, J (r y) = y := fun y => by
    have := congrArg (fun φ : LinearMap.range J →ₗ[ℂ] LinearMap.range J => (φ y : X)) hr
    simpa using this
  let f : LinearMap.range J →L[ℂ] ℂ := (Λ ∘ₗ r).mkContinuous C (fun y => by
    have := h (r y)
    rw [hr'] at this
    simpa using this)
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨g, fun w => ?_⟩
  have h1 := hg ⟨J w, w, rfl⟩
  have h2 := h (r ⟨J w, w, rfl⟩ - w)
  rw [map_sub J, hr'] at h2
  simp only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, map_sub, sub_eq_zero] at h2
  rw [← h2]
  simpa [f] using h1

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x)
    ((continuous_norm.pow k).smul ((w.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k n w)
    (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact SchwartzMap.le_seminorm ℂ k n w x)

theorem wtFun_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wtFun k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl

theorem norm_wtFun_le (k n : ℕ) (w : SchwartzMap E ℂ) :
    ‖wtFun k n w‖ ≤ SchwartzMap.seminorm ℂ k n w :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _

theorem le_norm_wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℂ k n w ≤ ‖wtFun k n w‖ := by
  refine SchwartzMap.seminorm_le_bound ℂ k n w (norm_nonneg _) (fun x => ?_)
  have := (wtFun k n w).norm_coe_le_norm x
  rwa [wtFun_apply, norm_smul, Real.norm_of_nonneg (by positivity)] at this

noncomputable def wt (k n : ℕ) : SchwartzMap E ℂ →L[ℂ]
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (wtFun k n)
    (fun f g => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      have hg : ContDiffAt ℝ n g x := ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.add_apply, wtFun_apply, wtFun_apply, wtFun_apply, ← smul_add,
        ← iteratedFDeriv_add_apply hf hg]
      rfl)
    (fun a f => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.smul_apply, wtFun_apply, wtFun_apply, RingHom.id_apply,
        smul_comm a, ← iteratedFDeriv_const_smul_apply hf]
      rfl)
    ⟨{(k, n)}, 1, zero_le_one, fun f => by
      simpa using norm_wtFun_le k n f⟩

theorem wt_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wt k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl

theorem continuous_iteratedFDeriv_at (n : ℕ) (x : E) :
    Continuous (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) := by
  have : (fun w : SchwartzMap E ℂ => iteratedFDeriv ℝ n w x) = fun w => wt 0 n w x := by
    funext w; simp [wt_apply]
  rw [this]
  exact (continuous_eval_const x).comp (wt 0 n).continuous

variable {P : Type} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {ν : Measure P} {Φ : P → SchwartzMap E ℂ} {c : P → ℂ}

theorem integrable_iteratedFDeriv (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (n : ℕ) (x : E) : Integrable (fun ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x) ν := by
  refine (hi 0 n).mono' (hc.smul
    ((continuous_iteratedFDeriv_at n x).comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ n x)
    (norm_nonneg _)

theorem iteratedFDeriv_integral (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (u : E → ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (n : ℕ) :
    ∀ x, iteratedFDeriv ℝ n u x = ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν := by
  induction n with
  | zero =>
    intro x
    ext m
    rw [ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv hΦ hc hi 0 x)]
    simp [hu]
  | succ n ih =>
    intro x
    set L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ with hL
    have hfun : iteratedFDeriv ℝ n u = fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν :=
      funext ih
    have hd : HasFDerivAt (fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν)
        (∫ ξ, L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x) ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
        (F := fun x ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x)
        (F' := fun x ξ => L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x))
        (bound := fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ 0 (n + 1) (Φ ξ))
        Filter.univ_mem
        (Filter.Eventually.of_forall fun y =>
          (integrable_iteratedFDeriv hΦ hc hi n y).aestronglyMeasurable)
        (integrable_iteratedFDeriv hΦ hc hi n x)
        (L.continuous.comp_aestronglyMeasurable
          (integrable_iteratedFDeriv hΦ hc hi (n + 1) x).aestronglyMeasurable)
        (ae_of_all _ fun ξ y _ => ?_) (hi 0 (n + 1)) (ae_of_all _ fun ξ y _ => ?_)
      · rw [LinearIsometryEquiv.norm_map, norm_smul]
        exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ _ y)
          (norm_nonneg _)
      · have h1 : DifferentiableAt ℝ (iteratedFDeriv ℝ n (Φ ξ)) y :=
          ((Φ ξ).smooth ⊤).differentiable_iteratedFDeriv
            (by exact_mod_cast ENat.coe_lt_top n) y
        have h2 := h1.hasFDerivAt.const_smul (c ξ)
        rw [fderiv_iteratedFDeriv] at h2
        exact h2
    have h3 := hd.fderiv
    rw [← hfun, fderiv_iteratedFDeriv] at h3
    apply L.injective
    exact h3.trans (L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (integrable_iteratedFDeriv hΦ hc hi (n + 1) x))

theorem integrable_wt (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (k n : ℕ) : Integrable (fun ξ => c ξ • wt k n (Φ ξ)) ν := by
  refine (hi k n).mono' (hc.smul
    ((wt k n).continuous.comp hΦ).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_wtFun_le k n _) (norm_nonneg _)

theorem wt_integral (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (u : SchwartzMap E ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (k n : ℕ) :
    wt k n u = ∫ ξ, c ξ • wt k n (Φ ξ) ∂ν := by
  ext1 x
  have := (BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm
    (integrable_wt hΦ hc hi k n)
  simp only [BoundedContinuousFunction.evalCLM_apply] at this
  rw [← this, wt_apply, iteratedFDeriv_integral hΦ hc hi u hu n x, ← integral_smul]
  congr 1
  funext ξ
  rw [BoundedContinuousFunction.smul_apply, wt_apply, smul_comm]

end SchwartzIntegralExchange


open SchwartzIntegralExchange in
theorem schwartz_clm_integral_comm :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by
  intro E _ _ P _ _ _ _ ν Φ hΦ c hc hi u hu Λ
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp Λ.toLinearMap) (continuous_norm.comp Λ.continuous)
  let J : SchwartzMap E ℂ →L[ℂ] (∀ i : s, BoundedContinuousFunction E
      (ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)) :=
    ContinuousLinearMap.pi fun i => wt i.1.1 i.1.2
  obtain ⟨g, hg⟩ := exists_factor J.toLinearMap Λ.toLinearMap C (fun w => by
    have h1 : ‖Λ w‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) w := hC w
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    exact (le_norm_wtFun i.1 i.2 w).trans (norm_le_pi_norm (J w) ⟨i, hi⟩))
  have hg' : ∀ w, g (J w) = Λ w := hg
  have hint : Integrable (fun ξ => c ξ • J (Φ ξ)) ν :=
    integrable_pi_iff.2 fun i => integrable_wt hΦ hc hi i.1.1 i.1.2
  have hJ : J u = ∫ ξ, c ξ • J (Φ ξ) ∂ν := by
    funext i
    rw [eval_integral (integrable_pi_iff.1 hint)]
    exact wt_integral hΦ hc hi u hu i.1.1 i.1.2
  rw [← hg', hJ, ← g.integral_comp_comm hint]
  simp [hg']

end GlobalTheory
end

section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.GaussTransport

theorem iteratedDeriv_cexp_mul (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_expI : Function.HasTemperateGrowth (fun t : ℝ => Complex.exp (Complex.I * t)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, ‖Complex.I‖ ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_mul, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (Complex.I * x)‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_chirp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (s : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp (Complex.I * ((s * (Q x x).im : ℝ) : ℂ))) := by
  have h1 : Function.HasTemperateGrowth (fun x : V => Q x x) :=
    Q.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' Function.HasTemperateGrowth.id'
  have h2 : Function.HasTemperateGrowth (fun x : V => s * (Q x x).im) := by
    have := ((s • Complex.imCLM : ℂ →L[ℝ] ℝ)).hasTemperateGrowth.comp h1
    simpa [Function.comp_def] using this
  exact hasTemperateGrowth_expI.comp h2

end GlobalTheory.GaussTransport

namespace GlobalTheory.GaussTransport


open LineDeriv in
theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  intro V _ _ _ E _ _ _ A Q N hQ hD hL
  set χ : V → ℂ := fun x => Complex.exp (Complex.I * ((-1 * (Q x x).im : ℝ) : ℂ)) with hχdef
  set χi : V → ℂ := fun x => Complex.exp (Complex.I * ((1 * (Q x x).im : ℝ) : ℂ)) with hχidef
  have hχ : χ.HasTemperateGrowth := hasTemperateGrowth_chirp Q (-1)
  have hχi : χi.HasTemperateGrowth := hasTemperateGrowth_chirp Q 1
  have hχχi : ∀ x, χ x * χi x = 1 := by
    intro x
    simp only [hχdef, hχidef, ← Complex.exp_add]
    rw [← Complex.exp_zero]; congr 1; push_cast; ring
  let Ψ : SchwartzMap E ℂ →L[ℂ] SchwartzMap V ℂ :=
    (SchwartzMap.smulLeftCLM ℂ χ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A)
  have hΨ : ∀ f x, Ψ f x = χ x * f (A x) := by
    intro f x
    simp [Ψ, SchwartzMap.smulLeftCLM_apply_apply hχ]
  refine ⟨N.comap (Ψ : SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap V ℂ), ?_, ?_, ?_, ?_⟩
  · intro w f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    set v : V := A.symm w with hv
    let lam : V →L[ℝ] ℝ := Complex.imCLM.comp (Q.flip v + Q v)
    have hlam : ∀ x, lam x = (Q x v).im + (Q v x).im := by intro x; simp [lam]
    have hlamT : (fun x : V => ((lam x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp lam).hasTemperateGrowth
    have h1N : ∂_{v} (Ψ f) ∈ N := hD v (Ψ f) _ hf (fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv v (Ψ f) x)
    have h2N : SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) ∈ N :=
      hL lam (Ψ f) _ hf (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hlamT, smul_eq_mul])
    have hder : ∀ x, fderiv ℝ (⇑(Ψ f)) x v =
        χ x * fderiv ℝ (⇑f) (A x) w - Complex.I * ((lam x : ℂ) * (χ x * f (A x))) := by
      intro x
      have hfun : (⇑(Ψ f)) = χ * (fun y => f (A y)) := funext (hΨ f)
      let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp ((-1 : ℝ) • Complex.imCLM)
      have hq := Q.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
      have hu := ((L.hasFDerivAt).comp x hq).const_mul Complex.I
      have hχd : HasFDerivAt χ (Complex.exp (Complex.I * L (Q x x)) • (Complex.I • (L.comp
          (((ContinuousLinearMap.precompR V Q) (id x)) (ContinuousLinearMap.id ℝ V) +
            ((ContinuousLinearMap.precompL V Q) (ContinuousLinearMap.id ℝ V)) (id x))))) x := by
        refine hu.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp [χ, L]
      have hfA : HasFDerivAt (fun y => f (A y)) ((fderiv ℝ (⇑f) (A x)).comp (A : V →L[ℝ] E)) x :=
        (f.differentiableAt.hasFDerivAt).comp x A.hasFDerivAt
      rw [hfun, (hχd.mul hfA).fderiv]
      have hχx : χ x = Complex.exp (-(Complex.I * ((Q x x).im : ℂ))) := by simp [χ]
      simp [L, v, hlam]
      rw [hχx]
      ring
    have hsum : Ψ f₁ = ∂_{v} (Ψ f) + Complex.I • SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) := by
      ext x
      rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hlamT,
        SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hΨ, hΨ, hf₁, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsum]
    exact N.add_mem h1N (N.smul_mem _ h2N)
  · intro ℓ f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    refine hL (ℓ.comp (A : V →L[ℝ] E)) (Ψ f) (Ψ f₁) hf (fun x => ?_)
    rw [hΨ, hΨ, hf₁]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    ring
  · intro g G hg hgN hG
    rw [Submodule.mem_comap]
    simp only [ContinuousLinearMap.coe_coe]
    have hΨG : Ψ G = g := by
      ext x
      rw [hΨ, hG, hg, hχdef]
      simp only
      rw [← Complex.exp_add]
      congr 1
      conv_rhs => rw [← Complex.re_add_im (Q x x)]
      rw [← hQ x]
      push_cast
      ring
    rw [hΨG]; exact hgN
  · intro hd
    have hsurj : Function.Surjective Ψ := by
      intro k
      refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (SchwartzMap.smulLeftCLM ℂ χi k), ?_⟩
      ext x
      rw [hΨ]
      simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hχi, smul_eq_mul]
      rw [← mul_assoc, hχχi, one_mul]
    refine (hsurj.denseRange.dense_image Ψ.continuous hd).mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hf

end GlobalTheory.GaussTransport
end

section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem topologicalClosure_stable_of_continuousLinearMap {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by
  intro f hf
  have h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W := by
    rintro _ ⟨g, hg, rfl⟩
    exact hT g hg
  have h2 := Submodule.topologicalClosure_map T W
  exact Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)

theorem schwartz_closure_stable_linearForm_fourier :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  intro E _ _ _ _ _ W hmul hF
  constructor
  · intro ℓ f f₁ hf hf₁
    have hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.comp ℓ).hasTemperateGrowth
    set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef
    have hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x := by
      intro g x
      rw [hTdef, SchwartzMap.smulLeftCLM_apply hg]
      rfl
    have hTW : ∀ g ∈ W, T g ∈ W := fun g hg' => hmul ℓ g (T g) hg' (hTapp g)
    have hf₁T : f₁ = T f := by
      ext x
      rw [hf₁ x, hTapp f x]
    rw [hf₁T]
    exact topologicalClosure_stable_of_continuousLinearMap W T hTW f hf
  · intro f hf
    have hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W := by
      intro g hg
      rw [SchwartzMap.fourierTransformCLM_apply]
      exact hF g hg
    have := topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf
    rwa [SchwartzMap.fourierTransformCLM_apply] at this

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_basis_of_discrete_of_span_eq_top_complex_pi :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ b : Module.Basis (Fin (2 * g)) ℤ Λ,
        LinearIndependent ℝ (fun i => (b i : Fin g → ℂ)) ∧
          Submodule.span ℝ (Set.range fun i => (b i : Fin g → ℂ)) = ⊤ := by
  intro g Λ hd h
  haveI : IsZLattice ℝ Λ := ⟨h⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hr : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex]
    simp [mul_comm]
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hr
  have e : (fun i => (b i : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ) := by
    funext i
    exact (Module.Basis.ofZLatticeBasis_apply ℝ Λ b i).symm
  refine ⟨b, ?_, ?_⟩
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).linearIndependent
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).span_eq

end GlobalTheory
end
