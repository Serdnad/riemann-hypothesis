module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
public import Mathlib.NumberTheory.NumberField.EquivReindex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RSubMean
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex Metric

noncomputable section

variable {ι : Type} [Fintype ι]

lemma lemS_finrank : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  first
  | rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]
  | rw [← FiniteDimensional.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace]
  | (rw [(WithLp.linearEquiv 2 ℝ (ι → ℂ)).finrank_eq, Module.finrank_pi_fintype]
     simp [Complex.finrank_real_complex, mul_comm])
  | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]

theorem lemS_local (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ) (hF : Differentiable ℂ F)
    (v0 : EuclideanSpace ℂ ι) :
    ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) ≤
      2 * (q : ℝ) ^ Fintype.card ι *
        ∫ u in closedBall v0 (Real.sqrt (2 * Fintype.card ι) / Real.sqrt (q * Real.pi)),
          ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
  set s := Real.sqrt (q * Real.pi) with hs
  set ρ := Real.sqrt (2 * Fintype.card ι) with hρ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q * Real.pi := mul_pos (by linarith) Real.pi_pos
  have hs0 : 0 < s := Real.sqrt_pos.mpr hqpos
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt hqpos.le
  let eC : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  let eR : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (Fintype.equivFin ι)
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℂ (Fin (Fintype.card ι)) → EuclideanSpace ℂ ι,
      w = fun z => s⁻¹ • eC.symm z := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℂ (Fin (Fintype.card ι)) → ℂ,
      G = fun z => F (v0 + w z) * Complex.exp (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)) :=
    ⟨_, rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ Hf : EuclideanSpace ℂ ι → ℝ,
      Hf = fun u => ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := ⟨_, rfl⟩
  have hwd : Differentiable ℂ w := by
    rw [hw]
    exact (eC.symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiable).const_smul s⁻¹
  have hGd : Differentiable ℂ G := by
    rw [hG]
    refine (hF.comp ((differentiable_const v0).add hwd)).mul ?_
    refine Differentiable.cexp ?_
    refine (differentiable_const _).mul ?_
    exact (innerSL ℂ v0).differentiable.comp hwd
  have hwn : ∀ z, ‖w z‖ = s⁻¹ * ‖z‖ := by
    intro z
    rw [hw]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, LinearIsometryEquiv.norm_map]
  have hw0 : w 0 = 0 := by rw [hw]; simp
  have hexp2 : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [sq, ← Real.exp_add, two_mul]
  have key : ∀ z, ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Hf (v0 + w z) := by
    intro z
    have hz : ‖z‖ ^ 2 = q * Real.pi * ‖w z‖ ^ 2 := by
      rw [hwn, mul_pow, ← hs2, inv_pow]
      field_simp
    have hadd : ‖v0 + w z‖ ^ 2 = ‖v0‖ ^ 2 + 2 * (inner ℂ v0 (w z)).re + ‖w z‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ)]
      first | rfl | simp
    have hre : (-((q * Real.pi : ℝ) : ℂ) * inner ℂ v0 (w z)).re =
        -(q * Real.pi) * (inner ℂ v0 (w z)).re := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have e1 : Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2) =
        Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0 + w z‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, hz, hadd]
      congr 1
      ring
    calc ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ‖F (v0 + w z)‖ ^ 2 *
            (Real.exp (2 * (-(q * Real.pi) * (inner ℂ v0 (w z)).re)) * Real.exp (-‖z‖ ^ 2)) := by
          rw [hG]
          simp only [norm_mul, Complex.norm_exp, mul_pow, hre, hexp2]
          ring
      _ = _ := by rw [e1, hHf]; ring
  have hmem : ∀ z, v0 + w z ∈ Metric.closedBall v0 (ρ / s) ↔
      z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ := by
    intro z
    have hsub : v0 + w z - v0 = w z := by abel
    rw [Metric.mem_closedBall, Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, hsub, sub_zero, hwn,
      div_eq_inv_mul]
    exact ⟨fun h => le_of_mul_le_mul_left h (inv_pos.mpr hs0),
      fun h => mul_le_mul_of_nonneg_left h (inv_pos.mpr hs0).le⟩
  have hA : ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
      ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
      Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) := by
    rw [← integral_indicator measurableSet_closedBall, ← integral_const_mul]
    congr 1
    funext z
    by_cases hzb : z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ
    · rw [Set.indicator_of_mem hzb, Set.indicator_of_mem ((hmem z).2 hzb), key z]
    · have h2 : v0 + w z ∉ Metric.closedBall v0 (ρ / s) := fun h => hzb ((hmem z).1 h)
      simp [Set.indicator_apply, hzb, h2]
  have hC : ∫ z, (Metric.closedBall v0 (ρ / s)).indicator Hf (v0 + w z) =
      s ^ (2 * Fintype.card ι) * ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u := by
    set h := (Metric.closedBall v0 (ρ / s)).indicator Hf
    have h1 : ∫ z, h (v0 + w z) = ∫ y, h (v0 + s⁻¹ • y) := by
      rw [hw]
      exact (eR.symm.measurePreserving).integral_comp eR.symm.toHomeomorph.measurableEmbedding
        (fun y => h (v0 + s⁻¹ • y))
    rw [h1, MeasureTheory.Measure.integral_comp_smul (μ := volume) (fun y => h (v0 + y)) s⁻¹,
      lemS_finrank, integral_add_left_eq_self, inv_pow, inv_inv, abs_of_pos (pow_pos hs0 _),
      smul_eq_mul]
  have L : ‖G 0‖ ^ 2 ≤ 2 / Real.pi ^ Fintype.card ι *
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℂ (Fin (Fintype.card ι))) ρ,
        ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := sq_norm_zero_le_gauss_ball G hGd
  have hG0 : G 0 = F v0 := by rw [hG]; simp [hw0]
  have hsn : s ^ (2 * Fintype.card ι) = (q * Real.pi) ^ Fintype.card ι := by rw [pow_mul, hs2]
  have hJ : ∫ u, (Metric.closedBall v0 (ρ / s)).indicator Hf u =
      ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2) := by
    rw [integral_indicator measurableSet_closedBall, hHf]
  rw [hA, hC, hG0, hsn, hJ] at L
  have hE : Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hpi : Real.pi ^ Fintype.card ι ≠ 0 := pow_ne_zero _ Real.pi_pos.ne'
  set J := ∫ u in Metric.closedBall v0 (ρ / s), ‖F u‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2)
  calc ‖F v0‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)
      ≤ 2 / Real.pi ^ Fintype.card ι *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * ((q * Real.pi) ^ Fintype.card ι * J)) *
          Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2) := mul_le_mul_of_nonneg_right L (Real.exp_pos _).le
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J * (Real.pi ^ Fintype.card ι / Real.pi ^ Fintype.card ι) *
          (Real.exp (q * Real.pi * ‖v0‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v0‖ ^ 2)) := by
        rw [mul_pow]; ring
    _ = 2 * (q : ℝ) ^ Fintype.card ι * J := by rw [hE, div_self hpi]; ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable section

theorem unfold_Zn {d : ℕ} (g : (Fin d → ℝ) → ENNReal) :
    ∫⁻ x, g x = ∑' n : Fin d → ℤ, ∫⁻ x in cubeIco (Fin d), g (x + fun i => (n i : ℝ)) := by
  classical
  set b := Pi.basisFun ℝ (Fin d) with hb
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) (Fin d → ℝ) volume :=
    ⟨fun c s _ => by
      show volume ((fun x => (c : Fin d → ℝ) + x) ⁻¹' s) = volume s
      exact measure_preimage_add _ _ _⟩
  have hF := ZSpan.isAddFundamentalDomain b (volume : Measure (Fin d → ℝ))
  have hdom : ZSpan.fundamentalDomain b = cubeIco (Fin d) := by
    ext x; simp [ZSpan.fundamentalDomain, cubeIco, b]
  rw [hF.lintegral_eq_tsum'', hdom]
  have hmem : ∀ n : Fin d → ℤ, (fun i => (n i : ℝ)) ∈ Submodule.span ℤ (Set.range b) := by
    intro n
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro i; simp [b]
  let e : (Fin d → ℤ) → Submodule.span ℤ (Set.range b) := fun n => ⟨_, hmem n⟩
  have he : Function.Bijective e := by
    constructor
    · intro n m h
      funext i
      have := congrFun (congrArg Subtype.val h) i
      have h2 : (n i : ℝ) = m i := by simpa [e] using this
      exact_mod_cast h2
    · rintro ⟨y, hy⟩
      have hy' := hy
      rw [Module.Basis.mem_span_iff_repr_mem] at hy'
      choose n hn using hy'
      refine ⟨n, Subtype.ext ?_⟩
      funext i
      simpa [b, e] using hn i
  rw [← (Equiv.ofBijective e he).tsum_eq]
  congr 1; funext n
  congr 1; funext x
  show g ((fun i => (n i : ℝ)) + x) = _
  rw [add_comm]

theorem gauss_lin {d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (ob : OrthonormalBasis (Fin d) ℝ W) (u b : Fin d → W)
    (hub : ∀ j i, inner ℝ (u j) (b i) = if j = i then (1 : ℝ) else 0) :
    ∫⁻ a : Fin d → ℝ, ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • u j‖ ^ 2)) =
      ENNReal.ofReal (|ob.toBasis.det b| * (2 : ℝ) ^ (-(d : ℝ) / 2)) := by
  classical
  set M : Matrix (Fin d) (Fin d) ℝ := fun i j => ob.repr (u j) i with hM
  set B : Matrix (Fin d) (Fin d) ℝ := ob.toBasis.toMatrix b with hB
  have hMB : M.transpose * B = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hM, hB,
      Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [← hub j k, ← ob.sum_inner_mul_inner (u j) (b k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show inner ℝ (ob i) (u j) * _ = _
    rw [real_inner_comm (u j) (ob i)]
  have hdet : M.det * B.det = 1 := by
    have := congrArg Matrix.det hMB
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hdetB : ob.toBasis.det b = B.det := by rw [Module.Basis.det_apply]
  have hM0 : M.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hnorm : ∀ a : Fin d → ℝ,
      ‖∑ j, a j • u j‖ = ‖(WithLp.toLp 2 (M.mulVec a) : EuclideanSpace ℝ (Fin d))‖ := by
    intro a
    rw [← ob.repr.norm_map]
    congr 1
    ext i

    simp [hM, Matrix.mulVec, dotProduct, map_sum, mul_comm]
  set G : (Fin d → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ ^ 2))
    with hG
  have hGm : Measurable G := by
    refine (Continuous.measurable ?_)
    exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((PiLp.continuous_toLp 2 _).norm.pow 2)))
  have hL : (fun a : Fin d → ℝ =>
      ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • u j‖ ^ 2))) =
      fun a => G (Matrix.toLin' M a) := by
    funext a; simp only [hG, hnorm, Matrix.toLin'_apply]
  rw [hL, ← lintegral_map hGm (Matrix.toLin' M).continuous_of_finiteDimensional.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rwa [LinearMap.det_toLin']),
    lintegral_smul_measure, LinearMap.det_toLin']
  have hE : ∫⁻ y, G y =
      ∫⁻ v : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)) := by
    have hp := MeasurePreserving.symm _
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d))
    exact hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun v : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)))
  have hI : ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2) =
      (2 : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity), finrank_euclideanSpace,
      Fintype.card_fin]
    have h2 : Real.pi / (2 * Real.pi) = (2 : ℝ)⁻¹ := by field_simp
    rw [h2, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_div]
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hI]; positivity
  rw [hE, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), hI, smul_eq_mul,
    ← ENNReal.ofReal_mul (abs_nonneg _), hdetB, eq_inv_of_mul_eq_one_right hdet]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem so_prod_norm (x : E) : ∏ σ : E →+* ℂ, ‖σ x‖ = |(Algebra.norm ℚ x : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun σ => rfl),
    ← norm_prod, ← h, eq_ratCast, Complex.norm_ratCast]

theorem so_norm_ge (w : E) (hw0 : w ≠ 0)
    (hw : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n) :
    1 ≤ |Algebra.norm ℚ w| * |((discr E : ℤ) : ℚ)| := by
  classical
  set B := RingOfIntegers.basis E
  set b := NumberField.integralBasis E
  have hb : ∀ i, b i = (B i : E) := fun i => NumberField.integralBasis_apply E i
  choose N0 hN using fun i j => hw (B i * B j)
  set N : Matrix _ _ ℤ := Matrix.of N0 with hNdef
  have hTA : Algebra.traceMatrix ℚ b * Algebra.leftMulMatrix b w = (N.map (Int.cast : ℤ → ℚ)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.map_apply, hNdef, Matrix.of_apply, ← hN i j]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have e : w * (b i * b j) = b i * (w * b j) := by ring
    rw [show ((B i * B j : 𝓞 E) : E) = b i * b j by rw [hb, hb]; push_cast; ring, e]
    conv_rhs => rw [← b.sum_repr (w * b j)]

    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet := congrArg Matrix.det hTA
  rw [Matrix.det_mul, ← Algebra.discr_def, ← Algebra.norm_eq_matrix_det, ← NumberField.coe_discr,
    ← Int.cast_det] at hdet
  have hne : N.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hdet
    rcases mul_eq_zero.1 hdet with h1 | h1
    · exact NumberField.discr_ne_zero E (by exact_mod_cast h1)
    · exact hw0 ((Algebra.norm_eq_zero_iff).1 h1)
  have h1 : (1 : ℚ) ≤ |(N.det : ℚ)| := by exact_mod_cast Int.one_le_abs hne
  calc (1 : ℚ) ≤ |(N.det : ℚ)| := h1
    _ = |Algebra.norm ℚ w| * |((discr E : ℤ) : ℚ)| := by
      rw [← hdet, abs_mul, mul_comm]

theorem so_sum_sq_ge [IsCMField E] (w : E) (hw0 : w ≠ 0)
    (hw : ∀ y : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (w * y) = n) :
    2 ≤ PT.rd E ^ 2 * ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := by
  haveI := NumberField.IsCMField.isTotallyComplex E
  have hcard : (Finset.univ : Finset (E →+* ℂ)).card = Module.finrank ℚ E := by
    rw [Finset.card_univ, NumberField.Embeddings.card]
  have hn2 : 2 ≤ Module.finrank ℚ E := by
    have h1 := NumberField.IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hnR : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast (by omega : 0 < Module.finrank ℚ E)
  have hwt : ∑ _σ ∈ (Finset.univ : Finset (E →+* ℂ)), (1 / (Module.finrank ℚ E : ℝ)) = 1 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  have amgm := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Module.finrank ℚ E : ℝ))
    (fun σ : E →+* ℂ => ‖σ w‖ ^ 2) (fun _ _ => by positivity) hwt (fun _ _ => by positivity)
  rw [Real.finsetProd_rpow Finset.univ (fun σ : E →+* ℂ => ‖σ w‖ ^ 2) (fun _ _ => by positivity),
    Finset.prod_pow, so_prod_norm, ← Finset.mul_sum] at amgm
  have hX : 0 ≤ |(Algebra.norm ℚ w : ℝ)| := abs_nonneg _
  have hY : 0 ≤ |(discr E : ℝ)| := abs_nonneg _
  have key : (1 : ℝ) ≤ |(Algebra.norm ℚ w : ℝ)| * |(discr E : ℝ)| := by
    have h := so_norm_ge w hw0 hw
    exact_mod_cast h
  have hrd : PT.rd E ^ 2 = (|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
    unfold PT.rd
    rw [← Real.rpow_natCast, ← Real.rpow_natCast (|(discr E : ℝ)|) 2, ← Real.rpow_mul hY,
      ← Real.rpow_mul hY, mul_comm]
  have hprodge : 1 ≤ (|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) *
      (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.one_le_rpow _ (by positivity)
    nlinarith [key, mul_nonneg hX hY]
  have hS : (Module.finrank ℚ E : ℝ) * (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) ≤
      ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left amgm hnR.le
    rwa [← mul_assoc, mul_one_div_cancel hnR.ne', one_mul] at h
  calc (2 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by exact_mod_cast hn2
    _ ≤ (Module.finrank ℚ E : ℝ) * ((|(discr E : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ)) *
        (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ))) := le_mul_of_one_le_right hnR.le hprodge
    _ = PT.rd E ^ 2 * ((Module.finrank ℚ E : ℝ) *
        (|(Algebra.norm ℚ w : ℝ)| ^ 2) ^ (1 / (Module.finrank ℚ E : ℝ))) := by rw [hrd]; ring
    _ ≤ PT.rd E ^ 2 * ∑ σ : E →+* ℂ, ‖σ w‖ ^ 2 := mul_le_mul_of_nonneg_left hS (sq_nonneg _)

theorem so_emb_inj (v : (E →+* ℂ) → ℂ)
    (h : ∀ i, ∑ σ : E →+* ℂ, v σ * σ (RingOfIntegers.basis E i : E) = 0) : v = 0 := by
  classical
  have hM : (NumberField.basisMatrix E).mulVec v = 0 := by
    ext i
    rw [NumberField.basisMatrix_eq_embeddingsMatrixReindex]
    simp only [Matrix.mulVec, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply,
      NumberField.integralBasis_apply, Pi.zero_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm]
    rw [← h (NumberField.equivReindex E i)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [mul_comm]
    rfl
  have h2 := congrArg (fun u => (⅟(NumberField.basisMatrix E)).mulVec u) hM
  simp only [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact h2

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsTorusAt (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (T : PT E) : Prop :=
  ∃ φ : (Fin r → E) →+ Vsp T.dim, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    (∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y) ∧
    (∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)) ∧
    (∀ v ∈ X.Λ, ‖φ v‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∧
    (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
      s * ((Algebra.trace ℚ E (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ))

def phiFD (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : ℝ :=
  if X.la1 x < th then 2 * PT.f E / (PT.rd E ^ 2 * X.la1 x ^ 2) else 0

def TorusAtLa1Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), x ∈ X.dom → ∀ T : PT E, IsTorusAt X x T →
      T.la1 = X.la1 x ∧ ∀ th : ℝ, T.ph th = phiFD X th x

end

end ReciprocityTheory.ChartRestriction.G.I2
end
