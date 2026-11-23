module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.CharDeriv

theorem hasDerivAt_of_continuous_hom :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ 0 = 1 → (∀ s t, χ (s + t) = χ s * χ t) →
      ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t := by
  intro χ hc h0 hadd
  have hP : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) (χ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  obtain ⟨δ, hI⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, χ s) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) = fun _ => (0 : ℂ) := funext h
    have h1 := hP 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have key : ∀ t : ℝ, χ t = ((∫ s in (0 : ℝ)..(t + δ), χ s) - ∫ s in (0 : ℝ)..t, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s) := by
    intro t
    rw [eq_div_iff hI, ← intervalIntegral.integral_const_mul]
    have h1 : (∫ s in (0 : ℝ)..δ, χ t * χ s) = ∫ u in t..(t + δ), χ u := by
      have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) (fun u => χ u) t
      rw [add_zero] at h2
      rw [← h2]
      exact intervalIntegral.integral_congr fun s _ => (hadd t s).symm
    rw [h1]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine ⟨(χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s), fun t => ?_⟩
  have hD : HasDerivAt (fun y : ℝ => ((∫ s in (0 : ℝ)..(y + δ), χ s) - ∫ s in (0 : ℝ)..y, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s)) ((χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s)) t := by
    have h3 : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..(y + δ), χ s) (χ (t + δ)) t := by
      simpa using (hP (t + δ)).comp_add_const t δ
    exact (h3.sub (hP t)).div_const _
  have hval : (χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s) * χ t =
      (χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s) := by
    rw [hadd t δ]
    ring
  rw [hval]
  exact hD.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

end GlobalTheory.CompanionTheory.CharDeriv
end

section

namespace GlobalTheory.CompanionTheory.Unitary

theorem wirtinger_combination_ne_zero : ∀ (χ : ℂ → ℂ), Continuous χ → (∀ z w, χ (z + w) = χ z * χ w) →
    (∀ z, ‖χ z‖ = 1) → (∃ z, χ z ≠ 1) → ∀ (D : ℂ → ℂ),
    (∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) →
    ∀ β : ℂ, β ≠ 0 → D β - Complex.I * D (β * Complex.I) ≠ 0 := by
  intro χ _ hmul hnorm hnt D hD β hβ
  have χ0 : χ 0 = 1 := by
    have h1 := hmul 0 0
    rw [add_zero] at h1
    have hne : χ 0 ≠ 0 := by
      intro h
      have h2 := hnorm 0
      rw [h, norm_zero] at h2
      exact zero_ne_one h2
    exact mul_left_cancel₀ hne (h1.symm.trans (mul_one (χ 0)).symm)
  have hf0 : ∀ z, χ (((0 : ℝ) : ℂ) * z) = 1 := by
    intro z
    simp [χ0]
  have hre : ∀ w, (D w).re = 0 := by
    intro w
    have h1 := (hD w).mul (hD w).star
    have hconst : ((fun t : ℝ => χ (t * w)) * fun t : ℝ => star (χ (t * w))) = fun _ => (1 : ℂ) := by
      funext t
      simp only [Pi.mul_apply]
      rw [← starRingEnd_apply, RCLike.mul_conj, hnorm]
      simp
    rw [hconst] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
    rw [hf0] at h2
    simp only [star_one, mul_one, one_mul] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h3
    linarith
  have hadd : ∀ z w, D (z + w) = D z + D w := by
    intro z w
    have h1 := (hD z).mul (hD w)
    have hfun : ((fun t : ℝ => χ (t * z)) * fun t : ℝ => χ (t * w)) = fun t : ℝ => χ (t * (z + w)) := by
      funext t
      simp only [Pi.mul_apply]
      rw [mul_add, hmul]
    rw [hfun, hf0, hf0, mul_one, one_mul] at h1
    exact (hD (z + w)).unique h1
  have hsmul : ∀ (r : ℝ) (z : ℂ), D (r * z) = r * D z := by
    intro r z
    have hr : HasDerivAt (fun t : ℝ => r * t) r 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
    have hz : HasDerivAt (fun t : ℝ => χ (t * z)) (D z) ((fun t : ℝ => r * t) 0) := by
      simp only [mul_zero]
      exact hD z
    have h1 := HasDerivAt.scomp (h := fun t : ℝ => r * t) (0 : ℝ) hz hr
    have hfun : ((fun t : ℝ => χ (t * z)) ∘ fun t : ℝ => r * t) = fun t : ℝ => χ (t * (r * z)) := by
      funext t
      simp only [Function.comp]
      congr 1
      push_cast
      ring
    rw [hfun] at h1
    rw [(hD (r * z)).unique h1, Complex.real_smul]
  have hzero : (∀ z, D z = 0) → False := by
    intro h0
    obtain ⟨z, hz⟩ := hnt
    apply hz
    have hder : ∀ s : ℝ, HasDerivAt (fun t : ℝ => χ (t * z)) 0 s := by
      intro s
      have h1 : HasDerivAt (fun t : ℝ => χ (((t - s : ℝ) : ℂ) * z)) (D z) s :=
        HasDerivAt.comp_sub_const (f := fun t : ℝ => χ (t * z)) s s (by rw [sub_self]; exact hD z)
      have h2 := h1.const_mul (χ (s * z))
      have hfun : (fun t : ℝ => χ (s * z) * χ (((t - s : ℝ) : ℂ) * z)) = fun t : ℝ => χ (t * z) := by
        funext t
        rw [← hmul]
        congr 1
        push_cast
        ring
      rw [hfun, h0, mul_zero] at h2
      exact h2
    have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) 1 0
    simp only [Complex.ofReal_one, one_mul] at hc
    rw [hc, hf0]
  intro hcomb
  have ha : D β = Complex.I * D (β * Complex.I) := sub_eq_zero.mp hcomb
  have hb0 : D (β * Complex.I) = 0 := by
    apply Complex.ext
    · exact hre _
    · have h1 := congrArg Complex.re ha
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, hre] at h1
      simp only [Complex.zero_im]
      linarith
  have ha0 : D β = 0 := by rw [ha, hb0, mul_zero]
  apply hzero
  intro z
  have hz : z = ((z / β).re : ℂ) * β + ((z / β).im : ℂ) * (β * Complex.I) := by
    have e : z = (z / β) * β := by field_simp
    conv_lhs => rw [e, ← Complex.re_add_im (z / β)]
    ring
  rw [hz, hadd, hsmul, hsmul, ha0, hb0, mul_zero, mul_zero, add_zero]

end GlobalTheory.CompanionTheory.Unitary
end

section

open Polynomial

namespace GlobalTheory.CompanionTheory.ConstCoeffODE

noncomputable def op (c : ℂ) (y : ℝ → ℂ) : ℝ → ℂ := deriv y - c • y

theorem op_add (c : ℂ) {a b : ℝ → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    op c (a + b) = op c a + op c b := by
  funext t
  have h : deriv (a + b) t = deriv a t + deriv b t :=
    ((ha t).hasDerivAt.add (hb t).hasDerivAt).deriv
  simp only [op, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]
  ring

theorem op_smul (c k : ℂ) {a : ℝ → ℂ} (ha : Differentiable ℝ a) :
    op c (k • a) = k • op c a := by
  funext t
  have h : deriv (k • a) t = k • deriv a t :=
    ((ha t).hasDerivAt.const_smul k).deriv
  simp only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]
  ring

noncomputable def step (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) : Submodule ℂ (ℝ → ℂ) where
  carrier := {y | Differentiable ℝ y ∧ op c y ∈ S}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, by rw [op_add c ha hb]; exact S.add_mem ha' hb'⟩
  zero_mem' := by
    refine ⟨differentiable_const (0 : ℂ), ?_⟩
    have : op c (0 : ℝ → ℂ) = 0 := by
      funext t
      simp [op]
    rw [this]
    exact S.zero_mem
  smul_mem' := by
    rintro k a ⟨ha, ha'⟩
    exact ⟨ha.const_smul k, by rw [op_smul c k ha]; exact S.smul_mem k ha'⟩

noncomputable def stepMap (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) : step c S →ₗ[ℂ] S × ℂ where
  toFun y := (⟨op c y.1, y.2.2⟩, y.1 0)
  map_add' a b := by
    ext1
    · exact Subtype.ext (op_add c a.2.1 b.2.1)
    · rfl
  map_smul' k a := by
    ext1
    · exact Subtype.ext (op_smul c k a.2.1)
    · rfl

theorem eq_zero_of_op_eq_zero (c : ℂ) {y : ℝ → ℂ} (hy : Differentiable ℝ y)
    (h : op c y = 0) (h0 : y 0 = 0) : y = 0 := by
  have hd : ∀ t, deriv y t = c * y t := by
    intro t
    have := congrFun h t
    simp only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  have he : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-c * (s : ℂ)))
      (Complex.exp (-c * (t : ℂ)) * (-c)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-c)
    exact h1.cexp
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => y s * Complex.exp (-c * (s : ℂ))) 0 t := by
    intro t
    have h2 := (hy t).hasDerivAt.mul (he t)
    have h3 : deriv y t * Complex.exp (-c * (t : ℂ)) + y t * (Complex.exp (-c * (t : ℂ)) * (-c)) = 0 := by
      rw [hd]; ring
    rw [h3] at h2
    exact h2
  have hc := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv)
  funext t
  have := hc t 0
  simp only [h0, zero_mul] at this
  simpa [Complex.exp_ne_zero] using this

theorem stepMap_injective (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) :
    Function.Injective (stepMap c S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : op c y.1 = 0 := congrArg (fun p : S × ℂ => (p.1 : ℝ → ℂ)) hy
  have h2 : y.1 0 = 0 := congrArg Prod.snd hy
  exact Subtype.ext (eq_zero_of_op_eq_zero c y.2.1 h1 h2)

theorem step_finite (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (step c S) :=
  FiniteDimensional.of_injective (stepMap c S) (stepMap_injective c S)

theorem step_finrank_le (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    Module.finrank ℂ (step c S) ≤ Module.finrank ℂ S + 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (stepMap_injective c S)
  rw [Module.finrank_prod, Module.finrank_self] at h
  exact h

theorem solutions_mem_finite :
    ∀ l : List ℂ, ∃ S : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ l.length ∧
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (D : Module.End ℂ X) (ev : X →ₗ[ℂ] (ℝ → ℂ)),
        (∀ x t, HasDerivAt (ev x) (ev (D x) t) t) →
          ∀ x, ev ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod x) = 0 → ev x ∈ S := by
  intro l
  induction l with
  | nil =>
    refine ⟨⊥, inferInstance, by simp, ?_⟩
    intro X _ _ D ev _ x hx
    simpa using hx
  | cons c l ih =>
    obtain ⟨S, hfin, hrank, hS⟩ := ih
    refine ⟨step c S, step_finite c S, ?_, ?_⟩
    · have := step_finrank_le c S
      simp only [List.length_cons]
      omega
    · intro X _ _ D ev hD x hx
      set Q : Module.End ℂ X := D - c • (1 : Module.End ℂ X) with hQ
      set P : Module.End ℂ X := (l.map fun c => D - c • (1 : Module.End ℂ X)).prod with hP
      have hcomm : Commute Q P := by
        refine Commute.list_prod_right _ _ ?_
        intro z hz
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hz
        have hD1 : Commute D (1 : Module.End ℂ X) := Commute.one_right D
        exact ((Commute.refl D).sub_right (hD1.smul_right b)).sub_left
          ((hD1.symm.sub_right ((Commute.one_left _).smul_right b)).smul_left c)
      have h1 : ev (P (Q x)) = 0 := by
        have h2 : (Q * P) x = (P * Q) x := by rw [hcomm.eq]
        have h3 : ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod) = P := rfl
        simp only [List.map_cons, List.prod_cons] at hx
        rw [h3] at hx
        have h4 : (P * Q) x = P (Q x) := rfl
        rw [← h4, ← h2]
        exact hx
      have h5 : ev (Q x) ∈ S := hS X D ev hD (Q x) h1
      have hdiff : Differentiable ℝ (ev x) := fun t => (hD x t).differentiableAt
      refine ⟨hdiff, ?_⟩
      have h6 : op c (ev x) = ev (Q x) := by
        funext t
        simp [op, hQ, (hD x t).deriv]
      rw [h6]
      exact h5

end GlobalTheory.CompanionTheory.ConstCoeffODE
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.Analysis.OscPhase

private lemma norm_exp_two_pi_I_mul_real (r : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_integral_oscillating_phase
    (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ)
    (hM : Measurable M) (hg : Integrable g μ)
    (hMg : Integrable (fun y => (M y : ℂ) * g y) μ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ)
      (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  have hnorm : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := norm_exp_two_pi_I_mul_real
  have hmeasE : ∀ t : ℝ,
      Measurable fun y => Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) :=
    fun t => by fun_prop
  have hdiff : ∀ (y : X) (t : ℝ), HasDerivAt
      (fun t : ℝ => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
      (2 * Real.pi * Complex.I *
        ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))) t := by
    intro y t
    have h1 : HasDerivAt (fun t : ℝ => ((t * M y : ℝ) : ℂ)) ((M y : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).mul_const (M y)).ofReal_comp
    have h2 := ((h1.const_mul (2 * Real.pi * Complex.I)).cexp).const_mul (g y)
    exact h2.congr_deriv (by ring)
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
    (F := fun (t : ℝ) y => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
    (F' := fun (t : ℝ) y => 2 * Real.pi * Complex.I *
      ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ))))
    (bound := fun y => ‖2 * Real.pi * Complex.I‖ * ‖(M y : ℂ) * g y‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      hg.aestronglyMeasurable.mul (hmeasE t).aestronglyMeasurable)
    (hg.mono (hg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable)
      (ae_of_all _ fun y => by rw [norm_mul, hnorm, mul_one]))
    ((hMg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable).const_mul _)
    (ae_of_all _ fun y t _ => by simp only [norm_mul, hnorm, mul_one, le_refl])
    (hMg.norm.const_mul _)
    (ae_of_all _ fun y t _ => hdiff y t)
  rwa [integral_const_mul] at hd

end GlobalTheory.CompanionTheory.Analysis.OscPhase
end

section

open Topology Filter

namespace GlobalTheory.CompanionTheory.HolFamily

theorem continuous_iteratedDeriv_family :
    ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U →
      (∀ g, DifferentiableOn ℂ (Ê · g) U) →
      ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
      ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  intro G _ U E hU hd hc z hz j
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hU z hz
  have hr : 0 < R / 2 := by positivity
  have hcl : Metric.closedBall z (R / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  rw [continuous_iff_continuousAt]
  intro g0
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hrj : 0 < (R / 2) ^ j := pow_pos hr j
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε * (R / 2) ^ j / (2 * (j.factorial : ℝ)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have htube : ∀ᶠ g in 𝓝 g0, ∀ w ∈ Metric.sphere z (R / 2), ‖E w g - E w g0‖ < δ := by
    refine (isCompact_sphere z (R / 2)).eventually_forall_of_forall_eventually
      (P := fun g w => ‖E w g - E w g0‖ < δ) ?_
    intro w hw
    have hwU : w ∈ U := hcl (Metric.sphere_subset_closedBall hw)
    have hcont : ContinuousAt (fun y : ℂ × G => E y.1 y.2) (w, g0) :=
      hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hwU, trivial⟩)
    have hA : ContinuousAt (fun p : G × ℂ => E p.2 p.1) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, p.1))
        (g := fun y : ℂ × G => E y.1 y.2) hcont continuous_swap.continuousAt
    have hB : ContinuousAt (fun p : G × ℂ => E p.2 g0) (g0, w) :=
      ContinuousAt.comp (f := fun p : G × ℂ => (p.2, g0))
        (g := fun y : ℂ × G => E y.1 y.2) hcont (by fun_prop)
    have hN : ContinuousAt (fun p : G × ℂ => ‖E p.2 p.1 - E p.2 g0‖) (g0, w) := (hA.sub hB).norm
    have hlt : ‖E w g0 - E w g0‖ < δ := by simpa using hδ
    exact hN.eventually_lt continuousAt_const hlt
  filter_upwards [htube] with g hg
  have hzn : U ∈ 𝓝 z := hU.mem_nhds hz
  have h1 : ContDiffAt ℂ j (E · g) z := ((hd g).analyticAt hzn).contDiffAt
  have h2 : ContDiffAt ℂ j (E · g0) z := ((hd g0).analyticAt hzn).contDiffAt
  rw [dist_eq_norm, ← iteratedDeriv_fun_sub h1 h2]
  have hdc : DiffContOnCl ℂ (fun x => E x g - E x g0) (Metric.ball z (R / 2)) :=
    ((hd g).sub (hd g0)).diffContOnCl_ball hcl
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := δ) j hr hdc
    (fun w hw => (hg w hw).le)
  refine hb.trans_lt ?_
  have : (j.factorial : ℝ) * δ / (R / 2) ^ j = ε / 2 := by
    rw [hδdef]; field_simp
  rw [this]
  linarith

end GlobalTheory.CompanionTheory.HolFamily
end
