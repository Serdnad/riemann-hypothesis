module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MatInv

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_restrict_of_zero (ν : Measure (GR n)) {C : Set (GR n)} (_hCm : MeasurableSet C) {F : GR n → ℂ}
    (hF : ∀ u ∉ C, F u = 0) : ∫ u, F u ∂ν = ∫ u, F u ∂(ν.restrict C) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

theorem holInt (ν : Measure (GR n)) [ν.IsHaarMeasure] {C : Set (GR n)} (hC : IsCompact C) {U : Set ℂ} (hU : IsOpen U)
    (F : GR n → ℂ → ℂ) (hF0 : ∀ u ∉ C, ∀ z, F u z = 0)
    (hcont : ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ u ∈ C, DifferentiableOn ℂ (F u) U) :
    DifferentiableOn ℂ (fun z => ∫ u, F u z ∂ν) U ∧
      ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ u, F u z ∂ν) z = ∫ u, iteratedDeriv r (F u) z ∂ν := by
  classical
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  haveI : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hdF : ∀ u, DifferentiableOn ℂ (F u) U := by
    intro u
    by_cases hu : u ∈ C
    · exact hd u hu
    · have h0 : F u = fun _ => 0 := funext (hF0 u hu)
      rw [h0]
      exact differentiableOn_const 0
  have key : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨(ε / 2).toNNReal, Real.toNNReal_pos.mpr (half_pos hε), ?_⟩
    rw [Real.coe_toNNReal _ (half_pos hε).le]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hint : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      Integrable (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod (ν.restrict C)) := by
    intro z R hzR a ha
    rw [Measure.prod_restrict]
    have hc2 : ContinuousOn (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        (Set.Icc 0 (2 * Real.pi) ×ˢ C) := by
      apply ContinuousOn.smul (ha.comp continuous_fst).continuousOn
      have h1 : ContinuousOn (fun p : ℝ × GR n => (p.2, circleMap z R p.1)) (Set.Icc 0 (2 * Real.pi) ×ˢ C) :=
        (continuous_snd.prodMk ((continuous_circleMap z R).comp continuous_fst)).continuousOn
      refine hcont.comp h1 ?_
      rintro ⟨θ, u⟩ ⟨_, hu⟩
      exact ⟨hu, hzR (circleMap_mem_closedBall z R.coe_nonneg θ)⟩
    exact (hc2.integrableOn_compact (isCompact_Icc.prod hC)).mono_set
      (Set.prod_mono (Set.uIoc_subset_uIcc.trans (Set.uIcc_of_le (by positivity)).subset) subset_rfl)
  have hfub : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • ∫ u, F u (circleMap z R θ) ∂ν)
        = ∫ u, (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • F u (circleMap z R θ)) ∂ν := by
    intro z R hzR a ha
    have e1 : ∀ θ, a θ • ∫ u, F u (circleMap z R θ) ∂ν
        = ∫ u, a θ • F u (circleMap z R θ) ∂(ν.restrict C) := by
      intro θ
      rw [integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu (circleMap z R θ)), integral_smul]
    simp_rw [e1]
    rw [intervalIntegral_integral_swap (hint z R hzR a ha)]
    exact (integral_restrict_of_zero ν hCm (fun u hu => by simp [hF0 u hu])).symm
  have hcirc : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ k : ℂ → ℂ,
      Continuous (fun θ => k (circleMap z R θ)) →
      (∮ ζ in C(z, R), k ζ • ∫ u, F u ζ ∂ν) = ∫ u, (∮ ζ in C(z, R), k ζ • F u ζ) ∂ν := by
    intro z R hzR k hk
    simp only [circleIntegral, deriv_circleMap, smul_smul]
    exact hfub z R hzR (fun θ => circleMap 0 R θ * Complex.I * k (circleMap z R θ))
      (((continuous_circleMap 0 R).mul continuous_const).mul hk)
  have hps : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U ∧
      HasFPowerSeriesOnBall (fun w => ∫ u, F u w ∂ν) (cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R) z R := by
    intro z hz
    obtain ⟨R, hR, hzR⟩ := key z hz
    refine ⟨R, hR, hzR, ?_⟩
    have hci : CircleIntegrable (fun w => ∫ u, F u w ∂ν) z R := by
      have h := (hint z R hzR (fun _ => 1) continuous_const).integral_prod_left
      rw [CircleIntegrable, intervalIntegrable_iff]
      refine h.congr (Eventually.of_forall fun θ => ?_)
      simp only [one_smul]
      exact (integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu _)).symm
    refine (hasFPowerSeriesOn_cauchy_integral hci hR).congr ?_
    intro w hw
    rw [Metric.eball_coe] at hw
    have hk : Continuous (fun θ => (circleMap z R θ - w)⁻¹) :=
      ((continuous_circleMap z R).sub continuous_const).inv₀
        (fun θ => sub_ne_zero.mpr (circleMap_ne_mem_ball hw θ))
    show (2 * ↑Real.pi * Complex.I)⁻¹ • (∮ ζ in C(z, R), (ζ - w)⁻¹ • ∫ u, F u ζ ∂ν) = ∫ u, F u w ∂ν
    rw [hcirc z R hzR (fun ζ => (ζ - w)⁻¹) hk, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw ((hdF u).continuousOn.mono hzR)
      (fun x hx => (hdF u).differentiableAt (hU.mem_nhds (hzR (Metric.ball_subset_closedBall hx.1))))
  constructor
  · intro z hz
    obtain ⟨R, -, -, h⟩ := hps z hz
    exact h.analyticAt.differentiableAt.differentiableWithinAt
  · intro z hz r
    obtain ⟨R, hR, hzR, h⟩ := hps z hz
    have hFu : ∀ u, iteratedDeriv r (F u) z = r.factorial • cauchyPowerSeries (F u) z R r (fun _ => 1) := by
      intro u
      rw [iteratedDeriv_eq_iteratedFDeriv, ← (((hdF u).mono hzR).hasFPowerSeriesOnBall hR).factorial_smul]
    have hne : ∀ θ, circleMap z R θ - z ≠ 0 := fun θ =>
      sub_ne_zero.mpr (fun h' => hR.ne' (by exact_mod_cast circleMap_eq_center_iff.mp h'))
    have hG : cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R r (fun _ => 1)
        = ∫ u, cauchyPowerSeries (F u) z R r (fun _ => 1) ∂ν := by
      simp only [cauchyPowerSeries_apply, smul_smul]
      rw [hcirc z R hzR (fun ζ => (1 / (ζ - z)) ^ r * (ζ - z)⁻¹)
        (((continuous_const.div ((continuous_circleMap z R).sub continuous_const) hne).pow r).mul
          (((continuous_circleMap z R).sub continuous_const).inv₀ hne)), integral_smul]
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h.factorial_smul, integral_congr_ae (Eventually.of_forall hFu), hG]
    simp only [nsmul_eq_mul]
    rw [integral_const_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_function_eq_weighted (m : ℕ) (e : ℤ) (y : GR n) : F0 m 0 e y = holomorphicScalarSection m e (mR y) := by
  simp [F0, f0, holomorphicScalarSection]

def Nm (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂

def Nm' (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂

private theorem Cm_mul_Cmi_eq_one : Cm n * Cmi n = 1 := by
  simp only [Cm, Cmi, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

private theorem Cm_inv_eq_Cmi : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv Cm_mul_Cmi_eq_one

private theorem Cmi_mul_Cm_eq_one : Cmi n * Cm n = 1 := by
  rw [← Cm_inv_eq_Cmi]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse Cm_mul_Cmi_eq_one)

private theorem u1_eq_mul_Cm_toBlocks₂₁ (g : M2 n) : u1 g = (g * Cm n).toBlocks₂₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u1, Cm, Matrix.fromBlocks_multiply]

private theorem u2_eq_mul_Cm_toBlocks₂₂ (g : M2 n) : u2 g = (g * Cm n).toBlocks₂₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [u2, Cm, Matrix.fromBlocks_multiply]

private theorem Nm_eq_mul_Cm_toBlocks₁₁ (g : M2 n) : Nm g = (g * Cm n).toBlocks₁₁ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm, Cm, Matrix.fromBlocks_multiply]

private theorem Nm'_eq_mul_Cm_toBlocks₁₂ (g : M2 n) : Nm' g = (g * Cm n).toBlocks₁₂ := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks g]
  simp [Nm', Cm, Matrix.fromBlocks_multiply]

private theorem toBlocks11_mul_fromBlocks (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₁₁ = A.toBlocks₁₁ * P + A.toBlocks₁₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_fromBlocks_toBlocks₂₁ (A : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    (A * fromBlocks P Q R S).toBlocks₂₁ = A.toBlocks₂₁ * P + A.toBlocks₂₂ * R := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  simp [Matrix.fromBlocks_multiply]

private theorem mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    x * mX P Q R S * Cm n = x * Cm n * fromBlocks P Q R S := by
  simp only [mX, Cm_inv_eq_Cmi, Matrix.mul_assoc, Cmi_mul_Cm_eq_one, Matrix.mul_one]

theorem zOfE_eq (x : M2 n) : zOfE x = Nm x * (u1 x)⁻¹ := rfl

theorem first_cayley_block_mul_block (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX P Q R S) = u1 x * P + u2 x * R := by
  rw [u1_eq_mul_Cm_toBlocks₂₁, u1_eq_mul_Cm_toBlocks₂₁, u2_eq_mul_Cm_toBlocks₂₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, mul_fromBlocks_toBlocks₂₁]

theorem Nm_mX (x : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    Nm (x * mX P Q R S) = Nm x * P + Nm' x * R := by
  rw [Nm_eq_mul_Cm_toBlocks₁₁, Nm_eq_mul_Cm_toBlocks₁₁, Nm'_eq_mul_Cm_toBlocks₁₂, mul_mX_mul_Cm_eq_mul_Cm_mul_fromBlocks, toBlocks11_mul_fromBlocks]

theorem da_entry (i j : Fin n ⊕ Fin n) (x : M2 n) : DifferentiableAt ℂ (fun y : M2 n => y i j) x := by
  exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_id (x := x)) i) j

theorem da_matrix {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n}
    (h : ∀ i j, DifferentiableAt ℂ (fun y => f y i j) x) : DifferentiableAt ℂ f x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x :=
    differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j
  exact h1

theorem da_apply {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (h : DifferentiableAt ℂ f x) (i j : Fin n) :
    DifferentiableAt ℂ (fun y => f y i j) x := by
  have h1 : DifferentiableAt ℂ (fun y => (f y : Fin n → Fin n → ℂ)) x := h
  exact differentiableAt_pi.1 (differentiableAt_pi.1 h1 i) j

theorem da_mul {f g : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x)
    (hg : DifferentiableAt ℂ g x) : DifferentiableAt ℂ (fun y => f y * g y) x := by
  refine da_matrix fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (da_apply hf i k).mul (da_apply hg k j)

theorem differentiableAt_first_cayley_block (x : M2 n) : DifferentiableAt ℂ u1 x := by
  refine da_matrix fun i j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

theorem da_Nm (x : M2 n) : DifferentiableAt ℂ Nm x := by
  refine da_matrix fun i j => ?_
  simp only [Nm, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, smul_eq_mul]
  exact ((da_entry _ _ x).const_mul _).add (da_entry _ _ x)

private theorem differentiableAt_det_of_differentiableAt_entries {ι : Type} [Fintype ι] [DecidableEq ι] {f : M2 n → Matrix ι ι ℂ}
    {x : M2 n} (hf : ∀ a b, DifferentiableAt ℂ (fun y => f y a b) x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  have hp : ∀ (s : Finset ι) (σ : Equiv.Perm ι),
      DifferentiableAt ℂ (fun y => ∏ i ∈ s, f y (σ i) i) x := by
    intro s σ
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      simp only [Finset.prod_insert ha]
      exact (hf _ _).mul ih
  have e : (fun y => (f y).det) =
      fun y => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e]
  exact DifferentiableAt.fun_sum fun σ _ => (hp _ σ).const_mul _

theorem da_det {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun y => (f y).det) x := by
  exact differentiableAt_det_of_differentiableAt_entries (da_apply hf)

theorem da_inv {f : M2 n → Matrix (Fin n) (Fin n) ℂ} {x : M2 n} (hf : DifferentiableAt ℂ f x) (h : (f x).det ≠ 0) :
    DifferentiableAt ℂ (fun y => (f y)⁻¹) x := by
  have hadj : ∀ i j, DifferentiableAt ℂ (fun y => (f y).adjugate i j) x := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_det_of_differentiableAt_entries fun a b => ?_
    simp only [Matrix.updateRow_apply]
    by_cases hab : a = j
    · simp only [hab, if_true]
      exact differentiableAt_const _
    · simp only [hab, if_false]
      exact da_apply hf a b
  have hd : DifferentiableAt ℂ (fun y => ((f y).det)⁻¹) x := (differentiableAt_det_of_differentiableAt_entries (da_apply hf)).inv h
  refine da_matrix fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.mul (hadj i j)

theorem da_zOfE (x : M2 n) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ zOfE x := by
  have e : zOfE = fun y : M2 n => Nm y * (u1 y)⁻¹ := funext zOfE_eq
  rw [e]
  exact da_mul (da_Nm x) (da_inv (differentiableAt_first_cayley_block x) h)

theorem da_F0E (m : ℕ) (e : ℤ) (x : M2 n) (h0 : x.det ≠ 0) (h : (u1 x).det ≠ 0) : DifferentiableAt ℂ (holomorphicScalarSection m e) x := by
  show DifferentiableAt ℂ (fun y : M2 n => y.det ^ e * (u1 y).det ^ (-(m : ℤ))) x
  exact ((differentiableAt_det_of_differentiableAt_entries (f := fun y => y) fun a b => da_entry a b x).zpow (Or.inl h0)).mul
    ((da_det (differentiableAt_first_cayley_block x)).zpow (Or.inl h))

theorem lowQ_eq (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ Q = Cm n * fromBlocks 0 Q 0 0 * Cmi n := by
  have h1 : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) Q 0 1 : M2 n) = 1 + fromBlocks 0 Q 0 0 := by
    rw [← fromBlocks_one, fromBlocks_add]; simp
  rw [lowQ, mX, h1, cm_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, cm_mul_cmi, add_sub_cancel_left]

theorem lowQ_smul (c : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) : lowQ (c • Q) = c • lowQ Q := by
  rw [lowQ_eq, lowQ_eq, show (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) 0 0 : M2 n) = c • fromBlocks 0 Q 0 0 by
    rw [fromBlocks_smul]; simp]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q 0 1 = 1 + lowQ Q := by
  rw [lowQ]; abel

theorem det_mX_low (Q : Matrix (Fin n) (Fin n) ℂ) : (mX 1 Q 0 1 : M2 n).det = 1 := by
  simp only [mX, Cm_inv_eq_Cmi]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, mul_one]
  rw [← Matrix.det_mul, Cm_mul_Cmi_eq_one, Matrix.det_one]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous JJ_conjTranspose)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := PositivityTheory.Rg.Sw.LVs.HolB.JJ_sq

theorem JJ_inv : (JJ n)⁻¹ = -JJ n :=
  Matrix.inv_eq_right_inv (by rw [mul_neg, JJ_mul_self, neg_neg])

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  simp only [sig, JJ_inv, neg_mul, neg_neg]

def IsLie (X : M2 n) : Prop := Xᴴ = JJ n * X * JJ n

theorem isLie_first_direction (Z : M2 n) : IsLie (dir1 Z) := by
  unfold IsLie dir1
  rw [sig_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, JJ_mul_self]
  simp only [Matrix.mul_assoc, JJ_mul_self, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_one, Matrix.one_mul]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2, add_comm]

theorem isLie_second_direction (Z : M2 n) : IsLie (dir2 Z) := by
  unfold IsLie dir2
  rw [sig_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, JJ_mul_self]
  simp only [Matrix.mul_assoc, JJ_mul_self, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_one, Matrix.one_mul]
  have h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.conj_I]
  rw [h2, neg_smul, ← smul_neg, neg_sub]

theorem lie_dir (Z : M2 n) (b : Bool) : IsLie (if b then dir1 Z else dir2 Z) := by
  cases b
  · exact isLie_second_direction Z
  · exact isLie_first_direction Z

def Ju (n : ℕ) : (M2 n)ˣ where
  val := JJ n
  inv := -JJ n
  val_inv := by rw [mul_neg, JJ_mul_self, neg_neg]
  inv_val := by rw [neg_mul, JJ_mul_self, neg_neg]

theorem cE_conjTranspose {X : M2 n} (hX : IsLie X) (s : ℝ) : (cE X s)ᴴ = JJ n * cE X (-s) * -JJ n := by
  unfold cE
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hX]
  have h : s • (JJ n * X * JJ n) = (Ju n : M2 n) * ((-s) • X) * ((Ju n)⁻¹ : (M2 n)ˣ) := by
    simp only [Ju, Units.inv_mk, Units.val_mk, Matrix.mul_neg, Matrix.mul_smul, neg_smul]
    rw [Matrix.neg_mul, neg_neg, Matrix.smul_mul]
  rw [h, Matrix.exp_units_conj]
  rfl

theorem inG_cE {X : M2 n} (hX : IsLie X) (s : ℝ) : InG (cE X s) := by
  unfold InG
  rw [cE_conjTranspose hX]
  calc JJ n * cE X (-s) * -JJ n * JJ n * cE X s = JJ n * (cE X (-s) * cE X s) := by
        simp only [Matrix.mul_assoc, Matrix.neg_mul, JJ_mul_self, neg_neg, Matrix.one_mul, Matrix.mul_neg]
    _ = JJ n := by rw [← cE_add, neg_add_cancel, cE_zero, Matrix.mul_one]

theorem cE_eq_exp (X : M2 n) (s : ℝ) : NormedSpace.exp ((s : ℂ) • X) = cE X s := by
  unfold cE; rw [Complex.coe_smul]

def gam {X : M2 n} (hX : IsLie X) (t : ℝ) : GR n :=
  ⟨⟨cE X t, cE X (-t), by rw [← cE_add, add_neg_cancel, cE_zero], by rw [← cE_add, neg_add_cancel, cE_zero]⟩,
    inG_cE hX t⟩

theorem curveGR' {X : M2 n} (hX : IsLie X) : Continuous (gam hX) ∧ gam hX 0 = 1 ∧
    (∀ s t, gam hX (s + t) = gam hX s * gam hX t) ∧ ∀ t, mR (gam hX t) = cE X t := by
  refine ⟨?_, ?_, ?_, fun t => rfl⟩
  · refine Continuous.subtype_mk ?_ _
    rw [Units.continuous_iff]
    exact ⟨cE_continuous X, (cE_continuous X).comp continuous_neg⟩
  · apply Subtype.ext; apply Units.ext; exact cE_zero X
  · intro s t; apply Subtype.ext; apply Units.ext; exact cE_add X s t

end PositivityTheory.Rg.Sw.HSt.FL

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt.FL

theorem curveGR : CurveGR := by
  intro n Z b
  obtain ⟨h1, h2, h3, h4⟩ := curveGR' (lie_dir Z b)
  exact ⟨gam (lie_dir Z b), h1, h2, h3, fun t => by rw [h4, cE_eq_exp]⟩

end PositivityTheory.Rg.Sw.HSt
end
end
