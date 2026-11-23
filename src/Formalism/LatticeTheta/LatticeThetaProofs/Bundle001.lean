module

public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open MeasureTheory Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

lemma covolDual_nondegenerate : (innerₗ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

lemma covolDual_det_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ V) (e : Module.Basis ι ℝ V) :
    o.toBasis.det (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) * o.toBasis.det e = 1 := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  set P := o.toBasis.toMatrix e with hP
  set Q := o.toBasis.toMatrix (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) with hQ
  have hM : Qᵀ * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hsum : ∑ k, Qᵀ i k * P k j =
        ⟪LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e i, e j⟫ := by
      simp only [hP, hQ, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [← o.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_comm (o k)]
    rw [hsum]
    have h := LinearMap.BilinForm.apply_dualBasis_left covolDual_nondegenerate e i j
    simp only [innerₗ_apply_apply] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hM, Matrix.det_one]

lemma covolDual_vol_fd {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ V) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [MeasureTheory.measureReal_def,
    MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, o.volume_parallelepiped, ENNReal.toReal_one]

end Formalism.H
end
end

section

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

abbrev boxIco (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1

theorem volume_boxIco : volume (boxIco ι) = 1 := by
  rw [volume_pi_pi]
  simp [Real.volume_Ico]

theorem fundamentalDomain_eq_preimage (e : Module.Basis ι ℝ V) :
    ZSpan.fundamentalDomain e = e.equivFunL ⁻¹' boxIco ι := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, boxIco, Set.mem_pi]

theorem integral_fundamentalDomain_eq (e : Module.Basis ι ℝ V) (H : V → ℂ) :
    ∫ y in ZSpan.fundamentalDomain e, H y =
      (volume.real (ZSpan.fundamentalDomain e) : ℂ) * ∫ t in boxIco ι, H (e.equivFunL.symm t) := by
  let ψ : V ≃ᵐ (ι → ℝ) := e.equivFunL.toHomeomorph.toMeasurableEquiv
  have hψ : (ψ : V → ι → ℝ) = e.equivFunL := rfl
  set ν : Measure (ι → ℝ) := Measure.map ψ (volume : Measure V) with hνdef
  haveI : ν.IsAddHaarMeasure := by
    rw [hνdef, hψ]; exact e.equivFunL.isAddHaarMeasure_map volume
  have hν : ν = ν.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hbox : ν (boxIco ι) = volume (ZSpan.fundamentalDomain e) := by
    rw [hνdef, MeasurableEquiv.map_apply, hψ, fundamentalDomain_eq_preimage]
  have hc : ((ν.addHaarScalarFactor volume : ℝ≥0) : ℝ≥0∞) = volume (ZSpan.fundamentalDomain e) := by
    rw [← hbox]
    conv_rhs => rw [hν]
    simp [volume_boxIco]
  have hint : ∫ y in ZSpan.fundamentalDomain e, H y = ∫ t in boxIco ι, H (e.equivFunL.symm t) ∂ν := by
    rw [hνdef, MeasurableEquiv.restrict_map, integral_map_equiv, fundamentalDomain_eq_preimage]
    simp only [hψ, ContinuousLinearEquiv.symm_apply_apply]
  rw [hint, hν, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_def, ← hc,
    ENNReal.coe_toReal, NNReal.smul_def, Complex.real_smul]

end Formalism.H
end
end
