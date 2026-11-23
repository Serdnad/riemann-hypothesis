module

public import ReciprocityTheory.SemistableReduction.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.SemistableReduction.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

theorem integral_volumeIoiPow (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k * g r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ k * g r)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k)]

theorem integrable_volumeIoiPow {k : ℕ} {g : ℝ → ℝ}
    (h : IntegrableOn (fun r ↦ r ^ k * g r) (Ioi 0)) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ g r) (Measure.volumeIoiPow k) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h2 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h
  refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k), mul_comm]

theorem finrank_euclidean_complex (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

private theorem homeomorphUnitSphereProd_smul_eq {n : ℕ} (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) :
    ((homeomorphUnitSphereProd _ x).2 : ℝ) •
      ((homeomorphUnitSphereProd _ x).1 : EuclideanSpace ℂ (Fin n)) = x := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [homeomorphUnitSphereProd, homeomorphSphereProd, smul_smul, hx]

theorem integral_polar {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ x, f x = ∫ p : UnitSphereC n × Ioi (0 : ℝ), f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integral_comp
      (homeomorphUnitSphereProd _).measurableEmbedding
      (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))]
  simp only [homeomorphUnitSphereProd_smul_eq]
  rw [integral_subtype_comap (measurableSet_singleton 0).compl
    (fun x : EuclideanSpace ℂ (Fin n) ↦ f x)]
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  rw [Measure.restrict_congr_set (show ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[volume] univ from
    ae_eq_univ.mpr (by rw [compl_compl]; exact measure_singleton 0)), Measure.restrict_univ]

theorem integrable_polar (n : ℕ) {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : Integrable f) :
    Integrable (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integrable_comp_emb
      (homeomorphUnitSphereProd _).measurableEmbedding]
  have h2 := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton
    (0 : EuclideanSpace ℂ (Fin n))).compl).mp hf.integrableOn
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, homeomorphUnitSphereProd_smul_eq]

def conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ star (WithLp.ofLp c i))

theorem inner_conjVec {n : ℕ} (c x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (conjVec c) x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
  simp [conjVec, PiLp.inner_apply, mul_comm]

theorem norm_conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : ‖conjVec c‖ = ‖c‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]

theorem sphere_linear_zero_null {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} = 0 := by
  let K : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    (LinearMap.ker (innerₛₗ ℂ (conjVec c))).restrictScalars ℝ
  have hK : K ≠ ⊤ := by
    intro h
    have hm : conjVec c ∈ K := h ▸ Submodule.mem_top
    have hm' : inner ℂ (conjVec c) (conjVec c) = 0 := hm
    rw [inner_self_eq_zero] at hm'
    exact hc (by rw [← norm_eq_zero, ← norm_conjVec c, hm', norm_zero])
  have hset : {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} =
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, spherePoint, inner_conjVec]
  have hs : MeasurableSet
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [hset, Measure.toSphere_apply' _ hs,
    measure_mono_null ?_ (Measure.addHaar_submodule _ K hK), mul_zero]
  rintro _ ⟨t, -, _, ⟨z, hz, rfl⟩, rfl⟩
  exact K.smul_mem t hz

def gaussLogC (a : ℝ) : ℝ := ∫ z : ℂ, log (a * ‖z‖) * exp (-‖z‖ ^ 2)

def gaussOneC : ℝ := ∫ z : ℂ, exp (-‖z‖ ^ 2)

private theorem integrableOn_rpow_mul_exp_neg_sq_Ioi (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ ↦ y ^ s * exp (-1 * y ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs

theorem integrable_gaussOneC : Integrable (fun z : ℂ ↦ exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  refine (integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).congr_fun
    (fun y _ ↦ by simp [Real.rpow_one]) measurableSet_Ioi

private theorem mul_abs_log_mul_le {a : ℝ} (ha : 0 < a) (y : ℝ) (hy : 0 < y) :
    y * |log (a * y)| ≤ |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
  have h1 : log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  have h2 : -log y ≤ 2 * y ^ (-1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (inv_pos.mpr hy).le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at this
    have e : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    rw [e] at this
    linarith
  have p1 := Real.rpow_nonneg hy.le (1 / 2 : ℝ)
  have p2 := Real.rpow_nonneg hy.le (-1 / 2 : ℝ)
  have habs : |log y| ≤ 2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hlog : |log (a * y)| ≤ |log a| + |log y| := by
    rw [Real.log_mul ha.ne' hy.ne']; exact abs_add_le _ _
  have e1 : y * y ^ (1 / 2 : ℝ) = y ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one]
  have e2 : y * y ^ (-1 / 2 : ℝ) = y ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hy, Real.rpow_one]
  calc y * |log (a * y)| ≤ y * (|log a| + (2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ))) := by
        gcongr; exact hlog.trans (by linarith)
    _ = |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]; linear_combination 2 * e1 + 2 * e2

theorem integrable_gaussLogC {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ log (a * ‖z‖) * exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume
    (f := fun y : ℝ ↦ log (a * y) * exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  have hg : IntegrableOn (fun y : ℝ ↦ (|log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) +
      2 * y ^ (1 / 2 : ℝ)) * exp (-1 * y ^ 2)) (Ioi 0) := by
    have := (((integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).const_mul |log a|).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (3 / 2) (by norm_num)).const_mul 2)).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (1 / 2) (by norm_num)).const_mul 2)
    refine this.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine Integrable.mono' hg (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦ ?_
  have hy' : (0 : ℝ) < y := hy
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hy', abs_of_pos (exp_pos _), neg_one_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_abs_log_mul_le ha y hy') (exp_pos _).le

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric
open scoped Pointwise

private theorem toSphere_univ_ne_zero_of_pos {n : ℕ} (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
  have : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    ⟨⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ), 0, fun h => by
        simpa using congrArg norm h⟩⟩
  rw [Measure.toSphere_apply_univ]
  refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
  exact_mod_cast (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℂ (Fin n))).ne'

private theorem toSphere_univ_ne_top' {n : ℕ} :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
  exact measure_ne_top _ _

theorem isProbabilityMeasure_sphereProb {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (sphereProb n) := by
  constructor
  simp only [sphereProb, ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (toSphere_univ_ne_zero_of_pos hn) toSphere_univ_ne_top'

private theorem volume_preimage_linearIsometryEquiv {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (X : Set (EuclideanSpace ℂ (Fin n))) : volume (A ⁻¹' X) = volume X :=
  A.measurePreserving.measure_preimage_emb A.toHomeomorph.measurableEmbedding X

private theorem Ioo_smul_image_preimage_sphere_eq_preimage {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) (s : Set (UnitSphereC n)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((fun z : UnitSphereC n =>
        (⟨A z, by simp⟩ : UnitSphereC n)) ⁻¹' s)) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨r, hr, _, ⟨⟨A z, by simp⟩, hz, rfl⟩, ?_⟩
    exact (map_smul A r (z : EuclideanSpace ℂ (Fin n))).symm
  · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨A.symm w, by simp⟩, ?_, rfl⟩, ?_⟩
    · have hw' : (⟨A (A.symm (w : EuclideanSpace ℂ (Fin n))), by simp⟩ : UnitSphereC n) = w :=
        Subtype.ext (by simp)
      exact (congrArg (· ∈ s) hw').mpr hw
    · show r • A.symm (w : EuclideanSpace ℂ (Fin n)) = x
      calc r • A.symm (w : EuclideanSpace ℂ (Fin n))
          = A.symm (r • (w : EuclideanSpace ℂ (Fin n))) :=
            (map_smul A.symm r (w : EuclideanSpace ℂ (Fin n))).symm
        _ = x := by rw [hx, LinearIsometryEquiv.symm_apply_apply]

theorem measurePreserving_toSphere_isometry {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n))
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hcont : Continuous (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n)) :=
    (A.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨hcont.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hcont.measurable hs, Measure.toSphere_apply' (μ := volume) (hcont.measurable hs),
    Measure.toSphere_apply' (μ := volume) hs, Ioo_smul_image_preimage_sphere_eq_preimage A s,
    volume_preimage_linearIsometryEquiv]

def rotLIE {n : ℕ} (u : Fin n → Circle) : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j => rotation (u j)

theorem rotLIE_apply {n : ℕ} (u : Fin n → Circle) (x : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (rotLIE u x).ofLp j = (u j : ℂ) * x.ofLp j := by
  rfl

def sphereRot {n : ℕ} (u : Fin n → Circle) (z : UnitSphereC n) : UnitSphereC n :=
  ⟨rotLIE u z, by simp⟩

private theorem measurePreserving_sphereProb_of_toSphere {n : ℕ} {f : UnitSphereC n → UnitSphereC n}
    (hf : MeasurePreserving f (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere) :
    MeasurePreserving f (sphereProb n) (sphereProb n) := by
  refine ⟨hf.measurable, ?_⟩
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ]
  rw [Measure.map_smul _ hf.aemeasurable, hf.map_eq]

theorem measurePreserving_sphereRot {n : ℕ} (u : Fin n → Circle) :
    MeasurePreserving (sphereRot u) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereProb_of_toSphere (f := sphereRot u)
    (measurePreserving_toSphere_isometry (rotLIE u))

def blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) : BlockSphere B n :=
  fun b => sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b)

private theorem coe_circle_exp_two_pi_mul (t : ℝ) :
    ((Circle.exp (2 * Real.pi * t) : Circle) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem blockPoint_blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) :
    blockPoint (blockRot θ z) = fun p => blockPoint z p * torusPoint θ p := by
  funext p
  obtain ⟨b, j⟩ := p
  show WithLp.ofLp (rotLIE (fun j' => Circle.exp (2 * Real.pi * θ (b, j')))
      (z b : EuclideanSpace ℂ (Fin n))) j =
    WithLp.ofLp (z b : EuclideanSpace ℂ (Fin n)) j * torusPoint θ (b, j)
  rw [rotLIE_apply]
  simp only [coe_circle_exp_two_pi_mul, torusPoint]
  ring

theorem measurePreserving_blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) :
    MeasurePreserving (blockRot θ) (blockSphereProb B n) (blockSphereProb B n) := by
  have h : ∀ b : Fin B, MeasurePreserving
      (sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))))
      (sphereProb n) (sphereProb n) := fun b => measurePreserving_sphereRot _
  show MeasurePreserving (fun (z : BlockSphere B n) (b : Fin B) =>
      sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b))
    (Measure.pi fun _ => sphereProb n) (Measure.pi fun _ => sphereProb n)
  exact measurePreserving_pi (hf := h)

theorem sphereProb_coord_zero {n : ℕ} (j : Fin n) :
    sphereProb n {z | spherePoint z j = 0} = 0 := by
  let W : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ).toLinearMap
  have hW : W ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ W := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at hmem
    change WithLp.ofLp (EuclideanSpace.single j (1 : ℂ)) j = 0 at hmem
    simp at hmem
  have hW0 : (volume : Measure (EuclideanSpace ℂ (Fin n))) (W : Set (EuclideanSpace ℂ (Fin n))) = 0 :=
    Measure.addHaar_submodule _ W hW
  have hmeas : MeasurableSet {z : UnitSphereC n | spherePoint z j = 0} := by
    have hc : Continuous fun z : UnitSphereC n => spherePoint z j := by
      exact (continuous_apply j).comp ((EuclideanSpace.equiv (Fin n) ℂ).continuous.comp
        continuous_subtype_val)
    exact (isClosed_singleton.preimage hc).measurableSet
  have hS : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | spherePoint z j = 0} = 0 := by
    rw [Measure.toSphere_apply' (μ := volume) hmeas]
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ hW0)
    rintro x ⟨r, -, _, ⟨z, hz, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, spherePoint] at hz
    show ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ)
      (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    show r • WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) j = 0
    rw [hz, smul_zero]
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, hS, mul_zero]

theorem blockSphereProb_coord_zero {B n : ℕ} :
    blockSphereProb B n {z | ∃ p : Fin B × Fin n, blockPoint z p = 0} = 0 := by
  rw [Set.ofPred_exists]
  refine measure_iUnion_null fun p => ?_
  show (Measure.pi fun _ : Fin B => sphereProb n)
    (Function.eval p.1 ⁻¹' {w : UnitSphereC n | spherePoint w p.2 = 0}) = 0
  exact Measure.pi_eval_preimage_null _ (sphereProb_coord_zero p.2)

theorem norm_blockPoint_le {B n : ℕ} (z : BlockSphere B n) (p : Fin B × Fin n) :
    ‖blockPoint z p‖ ≤ 1 := by
  have h1 : ‖((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
  have h2 := EuclideanSpace.norm_eq ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))
  rw [h1] at h2
  have h3 : ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) p.2‖ ^ 2 ≤
      ∑ i, ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖WithLp.ofLp ((z p.1 : UnitSphereC n) :
      EuclideanSpace ℂ (Fin n)) i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ _)
  have h4 := Real.sqrt_le_sqrt h3
  rw [← h2, Real.sqrt_sq (norm_nonneg _)] at h4
  exact h4

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

theorem unip_normSq_pow_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (u : Fin r → ℂ) :
    normSq ((A ^ n) *ᵥ u) ≤ c ^ n * normSq u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ']
    calc normSq (A *ᵥ (A ^ n *ᵥ u)) ≤ c * normSq (A ^ n *ᵥ u) := hA _
      _ ≤ c * (c ^ n * normSq u) := mul_le_mul_of_nonneg_left ih hc
      _ = c * c ^ n * normSq u := by ring

theorem unip_normSq_col {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    normSq (M *ᵥ Pi.single j 1) = ∑ i, ‖M i j‖ ^ 2 := by
  unfold normSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_single_one]
  rfl

theorem unip_normSq_single {r : ℕ} (j : Fin r) : normSq (Pi.single j (1 : ℂ)) = 1 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem unip_diag_sq_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (i : Fin r) :
    ‖(A ^ n) i i‖ ^ 2 ≤ c ^ n := by
  have h1 := unip_normSq_pow_le A c hc hA n (Pi.single i 1)
  rw [unip_normSq_col, unip_normSq_single, mul_one] at h1
  refine le_trans ?_ h1
  exact Finset.single_le_sum (f := fun k => ‖(A ^ n) k i‖ ^ 2) (fun k _ => by positivity)
    (Finset.mem_univ i)

theorem unip_hs_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) :
    ∑ a, ∑ b, ‖A a b‖ ^ 2 ≤ r * c := by
  rw [Finset.sum_comm]
  calc ∑ b, ∑ a, ‖A a b‖ ^ 2 = ∑ b : Fin r, normSq (A *ᵥ Pi.single b 1) :=
        Finset.sum_congr rfl fun b _ => (unip_normSq_col A b).symm
    _ ≤ ∑ _b : Fin r, c := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h := hA (Pi.single b 1)
        rwa [unip_normSq_single, mul_one] at h
    _ = r * c := by simp

theorem unip_hs_sub_one {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ∑ a, ∑ b, ‖(A - 1) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 - 2 * A.trace.re + r := by
  have key : ∀ a b, ‖(A - 1) a b‖ ^ 2 =
      ‖A a b‖ ^ 2 - (if a = b then 2 * (A a b).re - 1 else 0) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, if_true, Complex.sq_norm,
        Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    · simp [Matrix.sub_apply, Matrix.one_apply_ne h, h]
  simp_rw [key, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.trace, Complex.re_sum]
  simp [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem unip_exp_bound (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) * (Real.exp (2 / (3 * r)) - 1) < 1 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : 0 < 2 / (3 * (r : ℝ)) := by positivity
  set x : ℝ := 2 / (3 * (r : ℝ)) with hx
  have hxr : (r : ℝ) * x = 2 / 3 := by rw [hx]; field_simp
  have hx1 : x ≤ 2 / 3 := by nlinarith
  have hb := Real.exp_bound (x := x) (by rw [abs_of_pos hx0]; linarith) (n := 4) (by norm_num)
  rw [abs_of_pos hx0] at hb
  have hup := (abs_le.mp hb).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hup
  norm_num at hup
  have hmain : Real.exp x - 1 < 3 / 2 * x := by
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4, mul_le_mul_of_nonneg_left hx1 (le_of_lt (pow_pos hx0 3))]
  have hr0 : (0 : ℝ) < r := by linarith
  calc (r : ℝ) * (Real.exp x - 1) < r * (3 / 2 * x) := mul_lt_mul_of_pos_left hmain hr0
    _ = 1 := by rw [show (r : ℝ) * (3 / 2 * x) = 3 / 2 * (r * x) by ring, hxr]; norm_num

end ReciprocityTheory.MultiplicativeHeights
end
