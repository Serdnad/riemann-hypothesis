module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.OsgoodA
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.AnForm.Osgood

open Complex Metric MeasureTheory Set Filter Topology

open scoped Real

def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U

variable {n : ℕ}

abbrev Cube (n : ℕ) : Type := Icc (0 : Fin n → ℝ) (fun _ => 2 * π)

instance : CompactSpace (Cube n) := isCompact_iff_compactSpace.mp isCompact_Icc

def cubeProj (θ : Fin n → ℝ) : Cube n :=
  ⟨fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ),
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.1,
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.2⟩

theorem continuous_cubeProj : Continuous (cubeProj (n := n)) := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  exact continuous_subtype_val.comp (continuous_projIcc.comp (continuous_apply i))

theorem cubeProj_of_mem {θ : Fin n → ℝ} (hθ : θ ∈ Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :
    (cubeProj θ : Fin n → ℝ) = θ := by
  funext i
  show ((projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ)) = θ i
  have hi : θ i ∈ Icc (0 : ℝ) (2 * π) := ⟨hθ.1 i, hθ.2 i⟩
  rw [projIcc_of_mem _ hi]

def cubeCoord (c : Fin n → ℂ) (r : ℝ) (i : Fin n) : C(Cube n, ℂ) :=
  ⟨fun θ => torusMap c (fun _ => r) θ.1 i,
    ((continuous_apply i).comp (continuous_torusMap c r)).comp continuous_subtype_val⟩

def kern (c : Fin n → ℂ) (r : ℝ) (z : Fin n → ℂ) : C(Cube n, ℂ) :=
  ∏ i, Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ)))

private theorem cubeCoord_sub_smul_one_apply (c z : Fin n → ℂ) (r : ℝ) (i : Fin n) (θ : Cube n) :
    (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ = torusMap c (fun _ => r) θ.1 i - z i := by
  simp [cubeCoord]

private theorem cubeCoord_sub_smul_one_ne_zero_of_mem_ball {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (i : Fin n)
    (θ : Cube n) : (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ ≠ 0 := by
  rw [cubeCoord_sub_smul_one_apply]
  exact torusMap_sub_ne hr hz θ.1 i

private theorem continuousMap_isUnit_of_forall_ne_zero {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) :
    IsUnit g :=
  ⟨⟨g, ⟨fun x => (g x)⁻¹, g.continuous.inv₀ hg⟩, by ext x; simp [hg x], by ext x; simp [hg x]⟩, rfl⟩

private theorem continuousMap_ring_inverse_apply {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)
    (x : X) : Ring.inverse g x = (g x)⁻¹ := by
  obtain ⟨u, rfl⟩ := continuousMap_isUnit_of_forall_ne_zero g hg
  rw [Ring.inverse_unit]
  exact eq_inv_of_mul_eq_one_right (by rw [← ContinuousMap.mul_apply, Units.mul_inv, ContinuousMap.one_apply])

theorem kern_apply {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (θ : Cube n) :
    kern c r z θ = ∏ i, (torusMap c (fun _ => r) θ.1 i - z i)⁻¹ := by
  unfold kern
  simp only [ContinuousMap.coe_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [continuousMap_ring_inverse_apply _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr hz i) θ, cubeCoord_sub_smul_one_apply]

theorem kern_analyticAt (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) : AnalyticAt ℂ (kern c r) c := by
  have hK : kern c r = ∏ i ∈ Finset.univ,
      fun z : Fin n → ℂ => Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) := by
    funext z
    rw [Finset.prod_apply]
    rfl
  rw [hK]
  refine Finset.analyticAt_prod _ fun i _ => ?_
  have hlin : AnalyticAt ℂ (fun z : Fin n → ℂ => z i • (1 : C(Cube n, ℂ))) c :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).smulRight
      (1 : C(Cube n, ℂ))).analyticAt c
  obtain ⟨u, hu⟩ := continuousMap_isUnit_of_forall_ne_zero _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr (mem_ball_self hr) i)
  exact (analyticAt_inverse (𝕜 := ℂ) u).comp_of_eq (analyticAt_const.sub hlin) hu.symm

def jac (r : ℝ) (θ : Fin n → ℝ) : ℂ := ∏ i, (r : ℂ) * exp (θ i * I) * I

def fctl (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ) (g : C(Cube n, ℂ)) : ℂ :=
  ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π), jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ)

theorem continuous_jac (r : ℝ) : Continuous (jac (n := n) r) := by
  unfold jac
  exact continuous_finsetProd _ fun i _ => by fun_prop

theorem integrableOn_fctl {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :=
  (((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul
    (continuous_comp_torusMap hr.le hf)).integrableOn_Icc

def fctlCLM (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (f : (Fin n → ℂ) → ℂ)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl hr hf g) (integrableOn_fctl hr hf g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul (continuous_comp_torusMap hr.le hf)).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctlCLM_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    fctlCLM c hr f hf (kern c r z) = (2 * π * I) ^ n * f z := by
  have hcauchy : ∀ (m : ℕ) (g : (Fin m → ℂ) → ℂ) (a : Fin m → ℂ),
      (∀ ζ ∈ closedBall a r, DifferentiableAt ℂ g ζ) → ∀ w ∈ ball a r,
      (∯ ζ in T(a, fun _ => r), (∏ i, (ζ i - w i)⁻¹) * g ζ) = (2 * π * I) ^ m * g w := by
    intro m
    induction m with
    | zero =>
      intro g a _ w _
      rw [torusIntegral_dim0]
      simp [Subsingleton.elim w a]
    | succ m ih =>
      intro g a hg w hw
      rw [torusIntegral_succ (torusIntegrable_kernel hr hg hw)]
      have hw₀ : w 0 ∈ ball (a 0) r := (mem_ball_pi_iff hr).mp hw 0
      have hwTail : Fin.tail w ∈ ball (a ∘ Fin.succ) r :=
        (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hw i.succ
      have hcons : ∀ x ∈ closedBall (a 0) r, ∀ y ∈ closedBall (a ∘ Fin.succ) r,
          Fin.cons x y ∈ closedBall a r := by
        intro x hx y hy
        refine (mem_closedBall_pi_iff hr.le).mpr (Fin.cases ?_ fun j => ?_)
        · simpa using hx
        · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
      have hslice : EqOn (fun x => ∯ y in T(a ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
            (∏ i, (Fin.cons x y i - w i)⁻¹) * g (Fin.cons x y))
          (fun x => (2 * π * I) ^ m * ((x - w 0)⁻¹ * g (Fin.cons x (Fin.tail w))))
          (sphere (a 0) r) := by
        intro x hx
        have hxc := sphere_subset_closedBall hx
        have htail := ih (fun y => g (Fin.cons x y)) (a ∘ Fin.succ)
          (fun ζ hζ => (hg _ (hcons x hxc ζ hζ)).comp ζ (differentiable_cons_right x ζ))
          (Fin.tail w) hwTail
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
        rw [torusIntegral_const_mul]
        simp only [Fin.tail, Function.comp_def] at htail
        rw [htail]
        ring
      rw [circleIntegral.integral_congr hr.le hslice, circleIntegral.integral_const_mul]
      have hd : DifferentiableOn ℂ (fun x => g (Fin.cons x (Fin.tail w))) (closedBall (a 0) r) :=
        fun x hx => ((hg _ (hcons x hx _ (ball_subset_closedBall hwTail))).comp x
          (differentiable_cons_left (Fin.tail w) x)).differentiableWithinAt
      have hcircle := hd.circleIntegral_sub_inv_smul hw₀
      simp only [smul_eq_mul] at hcircle
      rw [hcircle, Fin.cons_self_tail, pow_succ]
      ring
  rw [← hcauchy n f c hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  dsimp only
  rw [kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul, jac]
  ring

theorem osgood : OsgoodStatement := by
  intro e U f hU hf x hx
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hfd : ∀ ζ ∈ closedBall x r, DifferentiableAt ℂ f ζ := fun ζ hζ =>
    hf.differentiableAt (hU.mem_nhds (hrU hζ))
  have hne : ((2 * π * I) ^ e : ℂ) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero)
  have hA : AnalyticAt ℂ
      (fun z => ((2 * π * I) ^ e)⁻¹ * fctlCLM x hr f hfd (kern x r z)) x :=
    analyticAt_const.mul (((fctlCLM x hr f hfd).analyticAt _).comp (kern_analyticAt x hr))
  refine hA.congr ?_
  filter_upwards [ball_mem_nhds x hr] with z hz
  rw [fctlCLM_kern hr hfd hz, inv_mul_cancel_left₀ hne]

end ReciprocityTheory.AnForm.Osgood
end
end

section

namespace ReciprocityTheory.AnForm

open Complex Filter Topology
open scoped Matrix

noncomputable section

def leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a b : Fin e → ℂ) : ℂ :=
  ((H a b + H (I • a) (I • b) : ℝ) + I * ((H a (I • b) - H (I • a) b : ℝ))) / 4

theorem hessC_eq_leviC {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (i j : Fin e) :
    hessC f z i j = leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl

theorem leviC_add {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a a' b : Fin e → ℂ) :
    leviC H (a + a') b = leviC H a b + leviC H a' b := by
  unfold leviC
  simp only [smul_add, map_add (f := _), ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem leviC_smul {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin e → ℂ) :
    leviC H (c • a) b = c * leviC H a b := by
  have hc : c • a = (c.re : ℝ) • a + (c.im : ℝ) • (I • a) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hc' : I • (c • a) = (c.re : ℝ) • (I • a) + (-c.im : ℝ) • a := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_neg]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination (↑c.im * a k) * Complex.I_sq
  unfold leviC
  rw [hc', hc]
  simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  push_cast
  conv_rhs => rw [← Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem sum_mul_leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (v b : Fin e → ℂ) :
    ∑ i, v i * leviC H (Pi.single i 1) b = leviC H v b := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin e → ℂ) := by
    funext k
    simp [Pi.single_apply]
  have key : ∀ s : Finset (Fin e), leviC H (∑ i ∈ s, v i • (Pi.single i 1 : Fin e → ℂ)) b =
      ∑ i ∈ s, v i * leviC H (Pi.single i 1) b := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using leviC_smul H 0 0 b
    · intro i s hi ih
      rw [Finset.sum_insert hi, Finset.sum_insert hi, leviC_add, leviC_smul, ih]
  rw [← key, ← hv]

theorem hess_comp_of_ker {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (w b : Fin e → ℂ) (hw : fderiv ℂ τ z w = 0) :
    fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b =
      fderiv ℝ φ (τ z) (fderiv ℂ (fun x => fderiv ℂ τ x b) z w) := by
  have hτev : ∀ᶠ x in 𝓝 z, AnalyticAt ℂ τ x := hτ.eventually_analyticAt
  have hφev : ∀ᶠ y in 𝓝 (τ z), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hφev' : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ φ (τ x) :=
    hτ.continuousAt.tendsto.eventually hφev
  have heq : (fun x => fderiv ℝ (φ ∘ τ) x b) =ᶠ[𝓝 z]
      (fun x => fderiv ℝ φ (τ x) (fderiv ℂ τ x b)) := by
    filter_upwards [hτev, hφev'] with x hx hφx
    have hxR : DifferentiableAt ℝ τ x := hx.differentiableAt.restrictScalars ℝ
    rw [fderiv_comp x hφx hxR, hx.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hf2 : ContDiffAt ℝ 2 (φ ∘ τ) z :=
    hφ.comp z ((hτ.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hD : DifferentiableAt ℝ (fderiv ℝ (φ ∘ τ)) z :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b = fderiv ℝ (fun x => fderiv ℝ (φ ∘ τ) x b) z w := by
    rw [fderiv_clm_apply hD (differentiableAt_const b)]
    simp
  rw [h1, heq.fderiv_eq]
  have hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (τ z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hτR : DifferentiableAt ℝ τ z := hτ.differentiableAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun x => fderiv ℝ φ (τ x))
      ((fderiv ℝ (fderiv ℝ φ) (τ z)).comp (fderiv ℝ τ z)) z :=
    hφ2.hasFDerivAt.comp z hτR.hasFDerivAt
  have hg : DifferentiableAt ℂ (fun x => fderiv ℂ τ x b) z :=
    hτ.fderiv.differentiableAt.clm_apply (differentiableAt_const b)
  have hu : HasFDerivAt (fun x => fderiv ℂ τ x b)
      ((fderiv ℂ (fun x => fderiv ℂ τ x b) z).restrictScalars ℝ) z :=
    hg.hasFDerivAt.restrictScalars ℝ
  rw [(hc.clm_apply hu).fderiv]
  have hwR : fderiv ℝ τ z w = 0 := by
    rw [hτ.differentiableAt.fderiv_restrictScalars ℝ]
    exact hw
  simp [hwR]

theorem vecMul_hessC_comp_eq_zero {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (v : Fin e → ℂ) (hv : fderiv ℂ τ z v = 0) :
    v ᵥ* hessC (φ ∘ τ) z = 0 := by
  have hH : ∀ b, leviC (fderiv ℝ (fderiv ℝ (φ ∘ τ)) z) v b = 0 := by
    intro b
    have hIv : fderiv ℂ τ z (Complex.I • v) = 0 := by rw [map_smul, hv, smul_zero]
    have hdiff : DifferentiableAt ℂ (fun x => fderiv ℂ τ x b) z :=
      (hτ.fderiv.differentiableAt).clm_apply (differentiableAt_const b)
    have hB : fderiv ℂ (fun x => fderiv ℂ τ x (Complex.I • b)) z =
        Complex.I • fderiv ℂ (fun x => fderiv ℂ τ x b) z := by
      have h0 : (fun x => fderiv ℂ τ x (Complex.I • b)) = fun x => Complex.I • fderiv ℂ τ x b := by
        funext x
        rw [map_smul]
      rw [h0]
      exact fderiv_const_smul hdiff Complex.I
    unfold leviC
    rw [hess_comp_of_ker φ τ z hτ hφ v b hv, hess_comp_of_ker φ τ z hτ hφ v _ hv,
      hess_comp_of_ker φ τ z hτ hφ _ b hIv, hess_comp_of_ker φ τ z hτ hφ _ _ hIv, hB]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
      map_neg]
    simp
  funext j
  show ∑ i, v i * hessC (φ ∘ τ) z i j = 0
  simp_rw [hessC_eq_leviC]
  rw [sum_mul_leviC, hH]

theorem maDens_comp_eq_zero_of_rank_lt {N e : ℕ} (φ : Fin e → (Fin N → ℂ) → ℝ)
    (τ : (Fin e → ℂ) → (Fin N → ℂ)) (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z)
    (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z))
    (hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ z).toLinearMap) < e) :
    maDens (fun k => φ k ∘ τ) z = 0 := by
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin e → ℂ, v ≠ 0 ∧ fderiv ℂ τ z v = 0 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ τ z).toLinearMap
    rw [Module.finrank_fin_fun] at h1
    have h2 : 0 < Module.finrank ℂ (LinearMap.ker (fderiv ℂ τ z).toLinearMap) := by omega
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
    exact ⟨x, fun h => hx (Subtype.ext h), x.2⟩
  have hvm : ∀ S : Finset (Fin e), v ᵥ* (∑ k ∈ S, hessC (φ k ∘ τ) z) = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp
    · intro k S hk ih
      rw [Finset.sum_insert hk, Matrix.vecMul_add, ih,
        vecMul_hessC_comp_eq_zero (φ k) τ z hτ (hφ k) v hv, add_zero]
  have hdet : ∀ S : Finset (Fin e), (∑ k ∈ S, hessC (φ k ∘ τ) z).det = 0 := fun S =>
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv0, hvm S⟩
  unfold maDens mdisc
  simp [hdet]

end

end ReciprocityTheory.AnForm
end
