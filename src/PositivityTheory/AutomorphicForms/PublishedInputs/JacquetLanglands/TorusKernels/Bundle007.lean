module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle071
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
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
import ReciprocityTheory.AnalyticForms.AnalyticCharts.OsgoodA

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.OrbitCoverLemmas

variable {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]


omit [Countable G] [MeasurableSpace Y] in
theorem orbit_tsum_smul (u : Y → ℝ) (g : G) (y : Y) :
    ∑' h : G, u (h • g • y) = ∑' h : G, u (h • y) := by
  simp only [smul_smul]
  exact (Equiv.mulRight g).tsum_eq (fun h => u (h • y))

theorem exists_cut (hm : ∀ g : G, Measurable fun y : Y => g • y) (u : Y → ℝ) (hu : Measurable u)
    (h0 : ∀ y, 0 ≤ u y) (hpos : ∀ y, ∃ g : G, 0 < u (g • y))
    (hs : ∀ y, Summable fun g : G => u (g • y)) : ∃ b : Y → ℝ, IsCut G b := by
  have hsE : (fun y => ∑' g : G, u (g • y)) =
      fun y => (∑' g : G, ENNReal.ofReal (u (g • y))).toReal := by
    funext y
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun g => h0 _) (hs y), ENNReal.toReal_ofReal]
    exact tsum_nonneg fun g => h0 _
  have hsm : Measurable fun y => ∑' g : G, u (g • y) := by
    rw [hsE]
    exact (Measurable.tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal
  have hspos : ∀ y, 0 < ∑' g : G, u (g • y) := by
    intro y
    obtain ⟨g, hg⟩ := hpos y
    exact lt_of_lt_of_le hg ((hs y).le_tsum g fun h _ => h0 _)
  refine ⟨fun y => u y / ∑' g : G, u (g • y),
    ⟨hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le, fun y => ?_⟩⟩
  have : (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) =
      fun g => u (g • y) / ∑' h : G, u (h • y) := by
    funext g; rw [orbit_tsum_smul]
  show HasSum (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) 1
  rw [this, ← div_self (hspos y).ne']
  exact (hs y).hasSum.div_const _

theorem cover (μ : Measure Y) (hP : Pres G μ) (b : Y → ℝ) (hb : IsCut G b) (S : Set Y)
    (hS : MeasurableSet S) (hc : ∀ y : Y, ∃ g : G, g • y ∈ S) :
    ∫⁻ y, ENNReal.ofReal (b y) ∂μ ≤ μ S :=
  _root_.UpperTheory.Reformulated.B.Qf46.cover μ hP b hb S hS hc

end UpperTheory.Esk.OrbitCoverLemmas

theorem UpperTheory.Esk.orbit_cover_proof : UpperTheory.Esk.C2 := by
  intro G Y _ _ _ _
  exact ⟨fun hm u hu h0 hpos hs => UpperTheory.Esk.OrbitCoverLemmas.exists_cut hm u hu h0 hpos hs,
    fun μ hP b hb S hS hc => UpperTheory.Esk.OrbitCoverLemmas.cover μ hP b hb S hS hc⟩
end
end

section

noncomputable section

namespace UpperTheory.Esk.OrbitalSingularIntegrals

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood

open scoped Real

def SepHol {n : ℕ} (f : (Fin n → ℂ) → ℂ) (S : Set (Fin n → ℂ)) : Prop :=
  ContinuousOn f S ∧ ∀ ζ ∈ S, ∀ i, DifferentiableAt ℂ (fun t => f (Function.update ζ i t)) (ζ i)

theorem continuous_comp_torusMap' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall c r)) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) :=
  hf.comp_continuous (continuous_torusMap c r) (torusMap_mem_closedBall c hr)

theorem torusIntegrable_kernel' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall c r)) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  refine Continuous.mul ?_ (continuous_comp_torusMap' hr.le hf)
  refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr hz θ i
  exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const

theorem cauchy' : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    SepHol f (closedBall c r) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z := by
  intro n
  induction n with
  | zero =>
    intro f c r _ _ z _
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | succ n ih =>
    intro f c r hr hf z hz
    rw [torusIntegral_succ (torusIntegrable_kernel' hr hf.1 hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (fun i => c (Fin.succ i)) r :=
      (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have hS : SepHol (fun y => f (Fin.cons x y)) (closedBall (fun i => c (Fin.succ i)) r) := by
        refine ⟨?_, fun ζ hζ j => ?_⟩
        · exact hf.1.comp (differentiable_cons_right x).continuous.continuousOn
            (fun y hy => hcons x hxc y hy)
        · have h1 := hf.2 (Fin.cons x ζ) (hcons x hxc ζ hζ) j.succ
          have e : (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) =
              fun t => f (Function.update (Fin.cons x ζ : Fin (n + 1) → ℂ) j.succ t) := by
            funext t
            rw [Fin.cons_update]
          show DifferentiableAt ℂ (fun t => f (Fin.cons x (Function.update ζ j t) : Fin (n + 1) → ℂ)) (ζ j)
          rw [e]
          simpa only [Fin.cons_succ] using h1
      have htail := ih (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr hS (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at htail
      rw [htail]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) := by
      intro x hx
      have h1 := hf.2 (Fin.cons x (Fin.tail z)) (hcons x hx _ (ball_subset_closedBall hz')) 0
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h1
      exact h1.differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

variable {n : ℕ}

theorem integrableOn_fctl' {c : Fin n → ℂ} {r : ℝ} {f : (Fin n → ℂ) → ℂ}
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
  exact ((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul hc

def fctlCLM' (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ)
    (hc : Continuous fun θ => f (torusMap c (fun _ => r) θ)) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl' hc g) (integrableOn_fctl' hc g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul hc).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctlCLM'_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : SepHol f (closedBall c r)) (hz : z ∈ ball c r) :
    fctlCLM' c r f (continuous_comp_torusMap' hr.le hf.1) (kern c r z) = (2 * π * I) ^ n * f z := by
  rw [← cauchy' n f c r hr hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [jac, kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul]
  ring

theorem osgFin (U : Set (Fin n → ℂ)) (hU : IsOpen U) (f : (Fin n → ℂ) → ℂ) (hf : SepHol f U) :
    AnalyticOnNhd ℂ f U := by
  intro z0 hz0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z0 hz0
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : closedBall z0 (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hS : SepHol f (closedBall z0 (ε / 2)) :=
    ⟨hf.1.mono hsub, fun ζ hζ i => hf.2 ζ (hsub hζ) i⟩
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ *
      fctlCLM' z0 (ε / 2) f (continuous_comp_torusMap' hr.le hS.1) (kern z0 (ε / 2) z)) z0 :=
    analyticAt_const.mul (((fctlCLM' z0 (ε / 2) f _).analyticAt _).comp (kern_analyticAt z0 hr))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  rw [fctlCLM'_kern hr hS hz, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end UpperTheory.Esk.OrbitalSingularIntegrals

open UpperTheory.Esk.OrbitalSingularIntegrals in
theorem UpperTheory.Esk.pf_Osg : UpperTheory.Esk.Osg := by
  intro I _ _ U hU f hf hsep
  set n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let Φ : (Fin n → ℂ) → (I → ℂ) := fun w i => w (e i)
  have hΦ : Continuous Φ := continuous_pi fun i => continuous_apply (e i)
  let g : (Fin n → ℂ) → ℂ := fun w => f (Φ w)
  let V : Set (Fin n → ℂ) := Φ ⁻¹' U
  have hV : IsOpen V := hU.preimage hΦ
  have hupd : ∀ (w : Fin n → ℂ) (j : Fin n) (t : ℂ), Φ (Function.update w j t) = Function.update (Φ w) (e.symm j) t := by
    intro w j t
    funext i
    by_cases h : i = e.symm j
    · subst h
      simp [Φ]
    · have h' : e i ≠ j := fun h' => h (by rw [← h']; simp)
      simp [Φ, h, h']
  have hg : UpperTheory.Esk.OrbitalSingularIntegrals.SepHol g V := by
    refine ⟨hf.comp hΦ.continuousOn (fun w hw => hw), fun w hw j => ?_⟩
    have h1 := hsep (Φ w) hw (e.symm j)
    have e1 : (fun t => g (Function.update w j t)) = fun t => f (Function.update (Φ w) (e.symm j) t) := by
      funext t
      simp only [g, hupd]
    rw [e1]
    simpa [Φ] using h1
  have hA := osgFin V hV g hg
  let Ψ : (I → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)
  have hΨ : ∀ z, Φ (Ψ z) = z := by
    intro z
    funext i
    simp [Φ, Ψ]
  intro z hz
  have hmem : Ψ z ∈ V := by
    show Φ (Ψ z) ∈ U
    rw [hΨ]
    exact hz
  have h2 := (hA (Ψ z) hmem).comp (Ψ.analyticAt z)
  have hfe : g ∘ Ψ = f := by
    funext w
    simp only [Function.comp, g, hΨ]
  rwa [hfe] at h2
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

namespace KappaPackingLemmas

variable {F I Gf : Type} [Field F] [Group Gf]

theorem kap_smul (hb : B1b) (D : Dat F I Gf) (δ : PG F) (a b : D.Xs) (v : I) :
    kap ((δ • a : D.Xs) v) ((δ • b : D.Xs) v) = kap (a v) (b v) := by
  induction δ using QuotientGroup.induction_on with
  | H g =>
    rw [Dat.mk_smulX, Dat.mk_smulX]
    exact hb.2.2.2.1 (D.r v g) (a v) (b v)

theorem near_sixteenth (hb : B1b) (hc : B1c) (D : Dat F I Gf) (γ₁ γ : PG F) (z w : D.Xs)
    (h₁ : Near (1 / 2) (γ₁ • z : D.Xs) w) (h : Near (1 / 2) (γ • z : D.Xs) w) :
    Near (1 / 16) z ((γ₁⁻¹ * γ) • z : D.Xs) := by
  intro v
  have e : kap (z v) (((γ₁⁻¹ * γ) • z : D.Xs) v) = kap ((γ₁ • z : D.Xs) v) ((γ • z : D.Xs) v) := by
    rw [← kap_smul hb D γ₁ z ((γ₁⁻¹ * γ) • z) v, smul_smul, mul_inv_cancel_left]
  rw [e]
  have a1 := h₁ v
  have a2 := h v
  have s := (hc.1 ((γ • z : D.Xs) v) (w v)).2.2
  have t := hc.2.2.1 ((γ₁ • z : D.Xs) v) (w v) ((γ • z : D.Xs) v)
  rw [← s] at t
  nlinarith

end KappaPackingLemmas

end UpperTheory.Esk

open UpperTheory.Esk UpperTheory.Esk.KappaPackingLemmas in
theorem UpperTheory.Esk.pf_Pack : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.Pack := by
  intro hb hc hE F I Gf _ _ _ D hax
  obtain ⟨hcnt, -, -, -, -, -, -, hnear⟩ := hE F I Gf D hax
  obtain ⟨c, hc0, hcz⟩ := hnear (1 / 2) (by norm_num)
  have := hcnt
  refine ⟨c⁻¹, ?_⟩
  intro y ω' h A hh hA hfin
  set S0 : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)} with hS0
  set N : ℝ≥0∞ := (S0.ncard : ℝ≥0∞) with hN
  let Sg : {γ : PG F // γ • y.1 = ω'} → Set D.Xs := fun γ => {w | Near (1 / 2) (γ.1 • y.2 : D.Xs) w}
  have hSm : ∀ γ, MeasurableSet (Sg γ) := fun γ => (hcz (γ.1 • y.2)).1

  have one : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ A * ∫⁻ w, (Sg γ).indicator h w := by
    intro γ
    have hv : (c : ℝ≥0∞) ≤ volume (Sg γ) := (hcz (γ.1 • y.2)).2
    calc (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ h (γ.1 • y.2) * volume (Sg γ) := by
          rw [mul_comm]; gcongr
      _ = ∫⁻ _ in Sg γ, h (γ.1 • y.2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Sg γ, (A : ℝ≥0∞) * h w := setLIntegral_mono' (hSm γ) fun w hw => hA _ _ hw
      _ = A * ∫⁻ w in Sg γ, h w := lintegral_const_mul _ hh
      _ = A * ∫⁻ w, (Sg γ).indicator h w := by rw [lintegral_indicator (hSm γ)]

  have cnt : ∀ w : D.Xs, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ N * h w := by
    intro w
    by_cases hT : ∃ γ₁ : {γ : PG F // γ • y.1 = ω'}, w ∈ Sg γ₁
    · obtain ⟨γ₁, hγ₁⟩ := hT
      let f : {γ : PG F // γ • y.1 = ω'} → PG F := fun γ => γ₁.1⁻¹ * γ.1
      have finj : Function.Injective f := fun a b hab => Subtype.ext (mul_left_cancel hab)
      let g : PG F → ℝ≥0∞ := S0.indicator fun _ => h w
      have le1 : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ g (f γ) := by
        intro γ
        by_cases hw : w ∈ Sg γ
        · rw [Set.indicator_of_mem hw]
          have hmem : f γ ∈ S0 := by
            refine ⟨?_, near_sixteenth hb hc D γ₁.1 γ.1 y.2 w hγ₁ hw⟩
            change (γ₁.1⁻¹ * γ.1) • y.1 = y.1
            rw [mul_smul, γ.2, inv_smul_eq_iff]; exact γ₁.2.symm
          simp [g, Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hw]; exact bot_le
      calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ ∑' γ, g (f γ) := ENNReal.tsum_le_tsum le1
        _ ≤ ∑' x, g x := ENNReal.tsum_comp_le_tsum_of_injective finj g
        _ = ∑' x : S0, h w := (tsum_subtype S0 fun _ => h w).symm
        _ = N * h w := by
          have : Fintype S0 := hfin.fintype
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, ← Nat.card_coe_set_eq,
            Nat.card_eq_fintype_card]
    · simp only [not_exists] at hT
      have : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w = 0 := fun γ => Set.indicator_of_notMem (hT γ) _
      simp [this]

  have key : (c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2) ≤ A * (N * ∫⁻ w, h w) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2)
        ≤ ∑' γ : {γ : PG F // γ • y.1 = ω'}, (A : ℝ≥0∞) * ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_le_tsum one
      _ = A * ∑' γ : {γ : PG F // γ • y.1 = ω'}, ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_mul_left
      _ = A * ∫⁻ w, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w := by
          rw [lintegral_tsum fun γ => (hh.indicator (hSm γ)).aemeasurable]
      _ ≤ A * ∫⁻ w, N * h w := by gcongr with w; exact cnt w
      _ = A * (N * ∫⁻ w, h w) := by rw [lintegral_const_mul _ hh]
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)
      = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)) := by
        rw [ENNReal.inv_mul_cancel_left hc' ENNReal.coe_ne_top]
    _ ≤ (c : ℝ≥0∞)⁻¹ * (A * (N * ∫⁻ w, h w)) := by gcongr
    _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * A * N * ∫⁻ w, h w := by
        rw [ENNReal.coe_inv hc0.ne']; ring
end
end

section

open Matrix

namespace UpperTheory.Esk.CentralTermsContribution

theorem trace_conj {F : Type} [Field F] (γ δ : GL (Fin 2) F) :
    ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end UpperTheory.Esk.CentralTermsContribution

theorem UpperTheory.Esk.pf_Fcen : UpperTheory.Esk.Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) = (γ : UpperTheory.Esk.PG F) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact h
  rw [QuotientGroup.eq] at h'
  set c := (δ * γ * δ⁻¹)⁻¹ * γ with hc
  obtain ⟨h1, h2, h3⟩ := UpperTheory.Esk.center_entries h'
  have hcv : (c : Matrix (Fin 2) (Fin 2) F) = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by rw [hc]; group
  have hv : (γ : Matrix (Fin 2) (Fin 2) F) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    conv_lhs => rw [hγ]
    rw [Units.val_mul]
  have htr2 : c 0 0 * (γ : Matrix (Fin 2) (Fin 2) F).trace = 1 * (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    conv_rhs => rw [hv, hcv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, UpperTheory.Esk.CentralTermsContribution.trace_conj]
    ring
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr htr2
  have hc1 : c = 1 := by
    ext : 1
    rw [hcv, ht, one_smul, Units.val_one]
  rw [hc1, mul_one] at hγ
  calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]
end

section

open MeasureTheory

namespace UpperTheory.Esk.CentralTermsContribution

open Classical in
theorem split_tsum {G : Type} (P : G → Prop) (f : G → ℂ) (hf : Summable fun g => ‖f g‖) :
    ∑' g, f g = (∑' g, if P g then f g else 0) + ∑' g, if P g then 0 else f g := by
  have h1 : Summable fun g => if P g then f g else 0 :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  have h2 : Summable fun g => if P g then 0 else f g :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  rw [← Summable.tsum_add h1 h2]
  congr 1; funext g; split_ifs <;> simp

end UpperTheory.Esk.CentralTermsContribution

open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_TF : UpperTheory.Esk.E2 → UpperTheory.Esk.Ecut → UpperTheory.Esk.E6 → UpperTheory.Esk.Fell → UpperTheory.Esk.Fhyp → UpperTheory.Esk.TF := by
  intro hE2 hcut hE6 hFell hFhyp F I Gf _ _ _ D hAx ι _ a
  obtain ⟨S, hFam, hS⟩ := hFell F I Gf D hAx ι a
  refine ⟨S, hFam, fun k hH hfd h => ?_⟩
  obtain ⟨⟨b, hb⟩, -⟩ := hcut F I Gf D hAx
  obtain ⟨hi, htr⟩ := hE6 F I Gf ι D k a hH hfd h b hb
  obtain ⟨hie, hge⟩ := hS k hH b hb
  have hsplit : ∀ y, (∑' γ : PG F, D.kk k a γ y) = (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y :=
    fun y => CentralTermsContribution.split_tsum _ _ ((hE2 F I Gf ι D k a hH).1 y)
  have hfun : (fun y => b y • ∑' γ : PG F, D.kk k a γ y) = fun y => b y • (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y := by
    funext y; rw [hsplit y, smul_add]
  have hih : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY := by
    have := hi.sub hie
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit y, smul_add, add_sub_cancel_left]
  have h0 := hFhyp F I Gf ι D k a hH b hb hih
  rw [htr, ← hge, hfun, integral_add hie hih, h0, add_zero]
end
