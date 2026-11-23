module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import Mathlib.Algebra.Module.StablyFree.Basic
public import Lemmata.CurryModusPonens.CurryMp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem matrix_space_volume_isAddHaar (N : ℕ) : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := by
  haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by infer_instance
  haveI hS : SigmaFinite (volume : Measure ℂ) := by infer_instance
  haveI h1 : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  haveI hS1 : SigmaFinite (volume : Measure (Fin N → ℂ)) := by infer_instance
  rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _

def leftMulLinearMap (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (g * Matrix.of Z)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

def rightMulLinear (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (Matrix.of Z * g)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]; ring_nf

theorem right_mul_map_eq_pi_toLin (g : Matrix (Fin N) (Fin N) ℂ) :
    rightMulLinear g = LinearMap.pi (fun i : Fin N => (Matrix.toLin' gᵀ).comp (LinearMap.proj i)) := by
  apply LinearMap.ext; intro Z; funext i j
  simp [rightMulLinear, Matrix.mul_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem det_right_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (rightMulLinear g) = g.det ^ N := by
  rw [right_mul_map_eq_pi_toLin, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]

def transposeLinearEquivAlt : (Fin N → Fin N → ℂ) ≃ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z i j := Z j i
  invFun Z i j := Z j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem left_mul_map_eq_transpose_conj (g : Matrix (Fin N) (Fin N) ℂ) :
    leftMulLinearMap g = (transposeLinearEquivAlt (N := N)).toLinearMap ∘ₗ rightMulLinear gᵀ ∘ₗ
      (transposeLinearEquivAlt (N := N)).symm.toLinearMap := by
  apply LinearMap.ext; intro Z; funext i j
  show (∑ k, g i k * Z k j) = ∑ k, Z k j * g i k
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem det_left_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (leftMulLinearMap g) = g.det ^ N := by
  rw [left_mul_map_eq_transpose_conj, LinearMap.det_conj, det_right_mul_map_eq_det_pow, Matrix.det_transpose]

theorem real_det_restrictScalars (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ)
    (hf : LinearMap.det f = d ^ N) :
    LinearMap.det (f.restrictScalars ℝ) = (‖d‖ ^ 2) ^ N := by
  rw [LinearMap.det_restrictScalars, hf, map_pow, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

theorem zpow_neg_two_mul_eq_inv_sq_pow (x : ℝ) : x ^ (-(2 * (N : ℤ))) = ((x ^ 2) ^ N)⁻¹ := by
  rw [_root_.zpow_neg, ← pow_mul, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

theorem map_volume_of_det_eq_pow (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ) (hd : d ≠ 0)
    (hf : LinearMap.det f = d ^ N) :
    Measure.map (f.restrictScalars ℝ) volume = ENNReal.ofReal (‖d‖ ^ (-(2 * (N : ℤ)))) • volume := by
  have hdet := real_det_restrictScalars f d hf
  have hne : LinearMap.det (f.restrictScalars ℝ) ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))
  haveI := matrix_space_volume_isAddHaar N
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, hdet, zpow_neg_two_mul_eq_inv_sq_pow,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))]

private theorem fdV0_det_cont_lemma (N : ℕ) :
    Continuous (fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det) :=
  Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))

theorem measurable_gl_density : Measurable (gmDens N) := by
  have h : gmDens N = fun Z => ENNReal.ofReal (((‖(Matrix.of Z).det‖ ^ 2) ^ N)⁻¹) := by
    funext Z; simp only [gmDens, zpow_neg_two_mul_eq_inv_sq_pow]
  rw [h]
  exact ENNReal.measurable_ofReal.comp
    (((fdV0_det_cont_lemma N).norm.measurable.pow_const 2).pow_const N).inv

theorem gl_density_left_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (g * Matrix.of Z)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

theorem gl_density_right_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (Matrix.of Z * g)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, mul_comm (Matrix.of Z).det, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

theorem map_gaussian_measure_eq {φ : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)} (hφ : Measurable φ) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hmap : Measure.map φ volume = c • volume)
    (hd : ∀ Z, gmDens N (φ Z) = c * gmDens N Z) : Measure.map φ (gmMeas N) = gmMeas N := by
  ext s hs
  have hD := measurable_gl_density (N := N)
  have key : ∀ Z, gmDens N Z = c⁻¹ * gmDens N (φ Z) := by
    intro Z; rw [hd, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have h1 : ∫⁻ Z in φ ⁻¹' s, gmDens N Z = c⁻¹ * ∫⁻ Z in φ ⁻¹' s, gmDens N (φ Z) := by
    rw [← lintegral_const_mul c⁻¹ (f := fun Z => gmDens N (φ Z)) (hD.comp hφ)]
    exact lintegral_congr fun Z => key Z
  simp only [gmMeas]
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs, h1,
    ← setLIntegral_map hs hD hφ, hmap, Measure.restrict_smul, lintegral_smul_measure]
  try simp only [smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem ofReal_norm_det_zpow_ne_zero (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (zpow_pos (norm_pos_iff.mpr hg) _)).ne'

theorem map_volume_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (leftMulLinearMap g) g.det hg (det_left_mul_map_eq_det_pow g)

theorem map_volume_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (rightMulLinear g) g.det hg (det_right_mul_map_eq_det_pow g)

theorem gmMeas_map_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) :=
    (leftMulLinearMap g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_left g hg)
    (gl_density_left_mul g)

theorem gmMeas_map_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) :=
    (rightMulLinear g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_right g hg)
    (gl_density_right_mul g)

theorem gmMeas_compact_lt_top (K : Set (Fin N → Fin N → ℂ)) (hK : IsCompact K)
    (hK0 : ∀ Z ∈ K, (Matrix.of Z).det ≠ 0) : gmMeas N K < ⊤ := by
  have hcont : ContinuousOn
      (fun Z : Fin N → Fin N → ℂ => ‖(Matrix.of Z).det‖ ^ (-(2 * (N : ℤ)))) K :=
    ((fdV0_det_cont_lemma N).norm.continuousOn).zpow₀ _
      fun Z hZ => Or.inl (norm_ne_zero_iff.mpr (hK0 Z hZ))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hDle : ∀ Z ∈ K, gmDens N Z ≤ ENNReal.ofReal C := fun Z hZ =>
    ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC Z hZ))
  simp only [gmMeas]
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ Z in K, gmDens N Z ≤ ∫⁻ _ in K, ENNReal.ofReal C :=
        lintegral_mono_ae (ae_restrict_of_forall_mem hK.measurableSet hDle)
    _ = ENNReal.ofReal C * volume K := setLIntegral_const K _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

theorem mp_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.curry : (ι × κ → ℂ) → ι → κ → ℂ) volume volume := by
  first | exact Bl.CurryModusPonens.goal1 .. | (apply Bl.CurryModusPonens.goal1 <;> assumption) | (intros; apply Bl.CurryModusPonens.goal1 <;> assumption)

theorem mp_perm4 {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SigmaFinite μa] [SigmaFinite μb] [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.2.1, p.1.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μc.prod μa).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm _)
  have h3 := (MeasurePreserving.id μa).prod
    (((Measure.measurePreserving_swap (μ := μb) (ν := μc))).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm _
  have h6 := (Measure.measurePreserving_swap (μ := μa) (ν := μc)).prod (MeasurePreserving.id (μb.prod μd))
  have h := h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))
  convert h using 1
  funext p
  rfl

abbrev Lo (N : ℕ) : Type := {ab : Fin N × Fin N // ab.2 < ab.1}

abbrev Up (N : ℕ) : Type := {ab : Fin N × Fin N // ab.1 < ab.2}

variable {N : ℕ}

local instance volTri : (volume : Measure (TriCo N)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

def idx (N : ℕ) : Fin N ⊕ (Lo N ⊕ Up N) ≃ Fin N × Fin N where
  toFun i := match i with
    | Sum.inl a => (a, a)
    | Sum.inr (Sum.inl ab) => ab.1
    | Sum.inr (Sum.inr ab) => ab.1
  invFun ab := if h : ab.1 = ab.2 then Sum.inl ab.1 else if h' : ab.2 < ab.1 then Sum.inr (Sum.inl ⟨ab, h'⟩)
    else Sum.inr (Sum.inr ⟨ab, lt_of_le_of_ne (not_lt.1 h') h⟩)
  left_inv := by
    rintro (a | ⟨ab, h⟩ | ⟨ab, h⟩)
    · simp
    · simp [h.ne', h]
    · simp [h.ne, not_lt.2 h.le]
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only
    split_ifs with h h'
    · simp [h]
    · rfl
    · rfl

def rho (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := fun a b =>
  if a = b then ((p.2.1 a : ℝ) : ℂ) + ((p.1.1 a : ℝ) : ℂ) * Complex.I
  else if h : b < a then p.1.2 ⟨(a, b), h⟩ else if h' : a < b then p.2.2 ⟨(a, b), h'⟩ else 0

def e2 (q : (Fin N → ℝ) × (Fin N → ℝ)) : Fin N → ℂ := fun a => ⟨q.1 a, q.2 a⟩

theorem measurePreserving_second_reorder : MeasurePreserving (e2 (N := N)) volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm _
  have h2 := volume_preserving_pi (fun _ : Fin N => (Complex.volume_preserving_equiv_real_prod).symm _)
  exact h2.comp h1

def rho0 (p : UCo N × TriCo N) : Fin N → Fin N → ℂ :=
  Function.curry (MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
      (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2))))

theorem measurePreserving_rho_reorder : MeasurePreserving (rho0 (N := N)) volume volume := by
  have h1 := mp_perm4 (volume : Measure (Fin N → ℝ)) (volume : Measure (Lo N → ℂ))
    (volume : Measure (Fin N → ℝ)) (volume : Measure (Up N → ℂ))
  have h2 := (measurePreserving_second_reorder (N := N)).prod (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Lo N ⊕ Up N => ℂ))
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)
  have h4 := volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
  have h5 := mp_curry (Fin N) (Fin N)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem rho_reorder_eq_rho : rho0 (N := N) = rho := by
  funext p a b
  have key : ∀ i, rho0 p (idx N i).1 (idx N i).2 =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
        (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2)) i :=
    fun i => MeasurableEquiv.piCongrLeft_apply_apply (idx N) (β := fun _ => ℂ) _ i
  rcases lt_trichotomy a b with h | rfl | h
  · have k := key (Sum.inr (Sum.inr ⟨(a, b), h⟩))
    simp only [rho, h.ne, not_lt.2 h.le, h, if_false, dif_neg, dif_pos, not_false_eq_true]
    exact k
  · have k := key (Sum.inl a)
    simp only [rho, if_true]
    refine k.trans ?_
    apply Complex.ext <;> simp <;> rfl
  · have k := key (Sum.inr (Sum.inl ⟨(a, b), h⟩))
    simp only [rho, h.ne', h, if_false, dif_pos]
    exact k

theorem mp_rho : MeasurePreserving (rho (N := N)) volume volume := by
  rw [← rho_reorder_eq_rho]; exact measurePreserving_rho_reorder

def sh (p : UCo N × TriCo N) : UCo N × TriCo N :=
  (p.1, (p.2.1, fun ab => p.2.2 ab - star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)))

theorem mp_sh : MeasurePreserving (sh (N := N)) volume volume := by
  have hc : Continuous (fun q : UCo N × TriCo N =>
      ((0 : Fin N → ℝ), fun ab : Up N => -star (q.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + q.2) := by
    refine (continuous_const.prodMk (continuous_pi fun ab => ?_)).add continuous_snd
    exact ((continuous_apply _).comp (continuous_snd.comp continuous_fst)).star.neg
  have h := (MeasurePreserving.id (volume : Measure (UCo N))).skew_product
    (g := fun x (t : TriCo N) => ((0 : Fin N → ℝ), fun ab : Up N => -star (x.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + t)
    (μc := (volume : Measure (TriCo N))) (μd := (volume : Measure (TriCo N)))
    hc.measurable (Filter.Eventually.of_forall fun x => map_add_left_eq_self (volume : Measure (TriCo N)) _)
  have e : sh (N := N) = fun p => (id p.1,
      ((0 : Fin N → ℝ), fun ab : Up N => -star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + p.2) := by
    funext p
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp [sh]
    · funext ab
      simp [sh, sub_eq_add_neg, add_comm]
  rw [e]; exact h

def lam (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := Matrix.of.symm (skMat p.1 + upMat p.2)

theorem lam_eq : lam (N := N) = rho ∘ sh := by
  funext p a b
  simp only [lam, Function.comp_apply, rho, sh, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]; ring
  · simp; ring
  · simp [h.ne', h, not_lt.2 h.le]

theorem mp_lam : MeasurePreserving (lam (N := N)) volume volume := by
  rw [lam_eq]; exact mp_rho.comp mp_sh

def lamInv (Z : Fin N → Fin N → ℂ) : UCo N × TriCo N :=
  ((fun a => (Z a a).im, fun ab => Z ab.1.1 ab.1.2),
   (fun a => (Z a a).re, fun ab => Z ab.1.1 ab.1.2 + star (Z ab.1.2 ab.1.1)))

theorem lamInv_lam (p : UCo N × TriCo N) : lamInv (lam p) = p := by
  obtain ⟨⟨x1, x2⟩, ⟨t1, t2⟩⟩ := p
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne', h, not_lt.2 h.le]
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne, h.ne', h, not_lt.2 h.le]

theorem lam_lamInv (Z : Fin N → Fin N → ℂ) : lam (lamInv Z) = Z := by
  funext a b
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]
  · apply Complex.ext <;> simp
  · simp [h.ne', h, not_lt.2 h.le]

def lamL : (UCo N × TriCo N) →ₗ[ℝ] (Fin N → Fin N → ℂ) where
  toFun := lam
  map_add' p q := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.fst_add, Prod.snd_add,
      Pi.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { lamL with invFun := lamInv, left_inv := lamInv_lam, right_inv := lam_lamInv }

theorem lamE_apply (p : UCo N × TriCo N) : lamE p = lam p := rfl

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS
end
end
