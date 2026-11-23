module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudyConjugationInvariant

theorem fsMetric_conj {n : Type*} [Fintype n] (w : n → ℂ) :
    (fsMetric (ι := n)).ρ (fun i => (starRingEnd ℂ) (w i)) = (fsMetric (ι := n)).ρ w := by
  simp [fsMetric, EuclideanSpace.norm_eq]

end FubiniStudyConjugationInvariant

theorem FsConjInvariant.proof : FsConjInvariant.Statement := by
  intro K _ ι _ z
  simp only [fsMulti, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudySmooth

theorem contDiffAt_blockNorm {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k : K)
    (z : (Σ k, ι k) → ℂ) (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => ‖WithLp.toLp 2 (fun i => w ⟨k, i⟩)‖) z := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => WithLp.toLp 2 (fun i => w ⟨k, i⟩)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))
  have hne : WithLp.toLp 2 (fun i => z ⟨k, i⟩) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    intro h0
    exact hi (by simpa using congrArg (fun v : WithLp 2 (ι k → ℂ) => v.ofLp i) h0)
  exact (contDiffAt_norm ℂ hne).comp z hL.contDiffAt

end FubiniStudySmooth

theorem FsLineSmooth.proof : FsLineSmooth.Statement := by
  intro K _ ι _
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : (Σ k, ι k) → ℂ => ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ ^ ((1 : K → ℤ) k)) _
  refine contDiffOn_prod fun k _ => ?_
  intro z hz
  simp only [Pi.one_apply, zpow_one]
  exact (FubiniStudySmooth.contDiffAt_blockNorm ι k z (hz k)).contDiffWithinAt

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace FubiniStudyLeviForm

variable {ι : Type} [Fintype ι]

theorem levi_sum_nonneg {K : Type} {z : ι → ℂ} (f : K → (ι → ℂ) → ℝ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ ReciprocityTheory.AnForm.levi (f k) z w)
    (w : ι → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, f k y) z ∧
      0 ≤ ReciprocityTheory.AnForm.levi (fun y => ∑ k ∈ s, f k y) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, by simp [ReciprocityTheory.AnForm.levi]⟩
  | insert a s ha ih =>
    have heq : (fun y => ∑ k ∈ insert a s, f k y) =
        fun y => (fun y' => ∑ k ∈ s, f k y') y + 1 * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩
    rw [ReciprocityTheory.AnForm.levi_add_smul (f := fun y' => ∑ k ∈ s, f k y') (g := f a) 1 ih.1 (hf a) w]
    have h1 := hl a w
    have h2 := ih.2
    linarith

noncomputable def blockProj {K : Type} (ι : K → Type) (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

end FubiniStudyLeviForm


open FubiniStudyLeviForm in
theorem FsLineLevi.proof : FsLineLevi.Statement := by
  intro K _ ι _ z w hz
  classical
  set F : K → ((Σ k, ι k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti ι).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric (ι := ι k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := by
    intro k
    have hk0 : (fun i => z ⟨k, i⟩) ≠ 0 := by
      obtain ⟨i, hi⟩ := hz k
      exact fun h0 => hi (congrFun h0 i)
    have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
      (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0
    have hFk : F k = (fun u => Real.log ((fsMetric (ι := ι k)).ρ u)) ∘ blockProj ι k := rfl
    refine ⟨hFk ▸ hφ.comp z ((blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt, fun v => ?_⟩
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj ι k).analyticAt z) hφ]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  exact (levi_sum_nonneg F (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GrassLinesProj.Statement : Prop :=
  ∀ (m : ℕ) (II : IntersectionSystem), IsIntersectionSystem II →
    II (Fin 1) (plBlocks 1 1 m) (grassIdeal 1 1 m) (1 * 1 * m + 1) (fun _ => fsMulti (plBlocks 1 1 m)) =
      II Unit (PBlk (m + 1)) ⊥ (m + 1) (fun _ => fsMulti (PBlk (m + 1)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartDensityIntegrableAlt

theorem exists_conjTranspose_mul_self {e : ℕ} {N : Matrix (Fin e) (Fin e) ℂ} (hN : N.PosDef) :
    ∃ C : Matrix (Fin e) (Fin e) ℂ, N = Cᴴ * C ∧ C.det ≠ 0 := by
  obtain ⟨U, l, hl, hspec⟩ : ∃ (U : Matrix (Fin e) (Fin e) ℂ) (l : Fin e → ℝ), (∀ k, 0 ≤ l k) ∧
      N = U * diagonal (fun k => (l k : ℂ)) * star U := by
    refine ⟨(hN.1.eigenvectorUnitary : Matrix (Fin e) (Fin e) ℂ), hN.1.eigenvalues,
      fun k => (hN.eigenvalues_pos k).le, ?_⟩
    have h := hN.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set s : Fin e → ℂ := fun k => ((Real.sqrt (l k) : ℝ) : ℂ) with hs
  have hss : (fun i => star s i * s i) = fun k => (l k : ℂ) := by
    funext k
    simp only [hs, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hl k)]
  have hNC : N = (diagonal s * star U)ᴴ * (diagonal s * star U) := by
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, diagonal_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (star s)), diagonal_mul_diagonal, hss, hspec,
      star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨diagonal s * star U, hNC, fun h => ?_⟩
  have hdet := (hN.det_pos).ne'
  rw [hNC, det_mul, h, mul_zero] at hdet
  exact hdet rfl

theorem chart_quad_eq {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hH : M.IsHermitian)
    {C : Matrix (Fin e) (Fin e) ℂ} (hNC : M.submatrix Fin.succ Fin.succ = Cᴴ * C) {d : Fin e → ℂ}
    (hd : Cᴴ *ᵥ d = fun i => M i.succ 0) (y : Fin e → ℂ) :
    star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (M 0 0 - star d ⬝ᵥ d) + star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) := by
  have h1 : star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) =
      star y ⬝ᵥ ((Cᴴ * C) *ᵥ y) + star y ⬝ᵥ (Cᴴ *ᵥ d) + star (Cᴴ *ᵥ d) ⬝ᵥ y + star d ⬝ᵥ d := by
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec, dotProduct_mulVec (star d) C y]
    ring
  rw [h1, ← hNC, hd]
  have hw : ∀ j : Fin e, M 0 j.succ = star (M j.succ 0) := fun j => (hH.apply 0 j.succ).symm
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.star_apply, star_one,
    one_mul, mul_one, submatrix_apply, hw, mul_add, Finset.sum_add_distrib]
  ring

theorem re_star_dotProduct_self {e : ℕ} (z : Fin e → ℂ) : (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem hermChartPot_eq_gbPot_affine {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ∃ (c : Fin e → ℂ) (P : Matrix (Fin e) (Fin e) ℂ) (κ : ℝ), P.det ≠ 0 ∧
      hermChartPot M = fun y => gbPot (c + P *ᵥ y) + κ := by
  obtain ⟨C, hNC, hC⟩ := exists_conjTranspose_mul_self (hM.submatrix (Fin.succ_injective e))
  have hCH : Cᴴ.det ≠ 0 := by rw [det_conjTranspose]; exact star_ne_zero.mpr hC
  set w : Fin e → ℂ := fun i => M i.succ 0 with hw
  set d : Fin e → ℂ := (Cᴴ)⁻¹ *ᵥ w with hd'
  have hd : Cᴴ *ᵥ d = w := by
    rw [hd', mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hCH), one_mulVec]
  have hq := fun y => chart_quad_eq hM.1 hNC hd y
  set s : ℝ := (M 0 0 - star d ⬝ᵥ d).re with hs
  have hspos : 0 < s := by
    have hy0 : C *ᵥ (-(C⁻¹ *ᵥ d)) + d = 0 := by
      rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC), one_mulVec, neg_add_cancel]
    have hx : (Fin.cons 1 (-(C⁻¹ *ᵥ d)) : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
      have := congr_fun h 0
      simp at this
    have hpos := hM.re_dotProduct_pos hx
    rw [hq, hy0] at hpos
    simpa [hs] using hpos
  set r : ℝ := Real.sqrt s with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hspos
  refine ⟨((r⁻¹ : ℝ) : ℂ) • d, ((r⁻¹ : ℝ) : ℂ) • C, Real.log r, ?_, ?_⟩
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (inv_pos.mpr hrpos).ne')) hC
  · funext y
    have hX : 0 ≤ ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hcy : ((r⁻¹ : ℝ) : ℂ) • d + (((r⁻¹ : ℝ) : ℂ) • C) *ᵥ y = ((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d) := by
      rw [smul_mulVec, smul_add, add_comm]
    have hnorm : ∑ i, ‖(((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d)) i‖ ^ 2 = (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hrpos), mul_pow]
    have hsq : s = r ^ 2 := (Real.sq_sqrt hspos.le).symm
    have h1pos : 0 < 1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hsplit : s + ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 = r ^ 2 * (1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2) := by
      rw [hsq]; field_simp
    simp only [hermChartPot, gbPot]
    rw [hq, Complex.add_re, ← hs, re_star_dotProduct_self, hcy, hnorm, hsplit,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hrpos.le,
      Real.log_mul hrpos.ne' (Real.sqrt_pos.mpr h1pos).ne']
    ring

theorem integrable_fsDens (D : ℕ) :
    Integrable (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
  have hcont : Continuous (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun y => ?_
    have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
    positivity
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by
    simp only [Pi.zero_apply]; positivity)]
  have h := gaM_lintegral_pi D 1 one_pos 0
  simp only [add_zero] at h
  rw [h]
  exact ENNReal.ofReal_lt_top

theorem integrable_comp_affine {D : ℕ} {f : (Fin D → ℂ) → ℝ} (hf : Integrable f) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : Integrable (fun y => f (c + P *ᵥ y)) := by
  set L := ChartMongeAmpereAffineInvariance.realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)))
    (by rw [ChartMongeAmpereAffineInvariance.det_realCLE]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe] at hmap
  have hg : Integrable (fun w => f (c + w)) (Measure.map L volume) := by
    rw [hmap]
    exact (hf.comp_add_left c).smul_measure ENNReal.ofReal_ne_top
  exact L.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hg

end ChartDensityIntegrableAlt


open ChartDensityIntegrableAlt in
theorem ChartDensityIntegrable.proof : ChartDensityIntegrable.Statement := by
  intro e M hM
  obtain ⟨c, P, κ, hP, hpot⟩ := hermChartPot_eq_gbPot_affine M hM
  have h : (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y) = fun y =>
      (Complex.normSq P.det * ((e.factorial : ℝ) / Real.pi ^ e)) *
        ((1 + ∑ i, ‖(c + P *ᵥ y) i‖ ^ 2) ^ (e + 1))⁻¹ := by
    funext y
    rw [hpot, ChartMongeAmpereAffineInvariance.maDensity_comp_affine gbPot c P hP κ y, maDensity_gbPot]
    ring
  rw [h]
  exact (integrable_comp_affine (integrable_fsDens e) c P hP).const_mul _

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveRing (y : (Σ k, ι k) → Ω) : Subring Ω :=
  ⨅ (c : ∀ k, ι k) (_ : ∀ k, y ⟨k, c k⟩ ≠ 0), (chartRingZ y c).toSubring

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_curveRing {y : (Σ k, ι k) → Ω} {b : Ω} :
    b ∈ curveRing y ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ y c := by
  simp [curveRing, Subring.mem_iInf]

def curveMul (y : (Σ k, ι k) → Ω) (x : Ω) : AddSubgroup Ω :=
  (curveRing y).toAddSubgroup.map (AddMonoidHom.mulLeft x)

end Objects

def CurveCharts.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      Module.Finite ℤ (curveRing y) ∧
      Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) ∧
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a

def VertRIndex.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) s =
        Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s)))

def SectionIndexNorm.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      (Module.finrank (blockFnField y) K' : ℝ) *
          Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s))) =
        Real.log |(Algebra.norm ℚ (aeval y s) : ℝ)| +
          Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
            (1 : Submodule (𝓞 K') K').toAddSubgroup)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial

noncomputable section

def GrassFibreDegree.Statement : Prop :=
  ∀ (n p : ℕ), p.Prime →
    vertR (grassIdeal 1 1 n) (fun _ : Fin n => fsMulti (plBlocks 1 1 n)) (C (p : ℤ)) = Real.log p

end

end GroundTheory.Heights₂.Heights
end
