module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ContinuousNormMulOneAddAbsLogPow
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Complex
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem prod_fin_ite_lt {R : Type*} [CommMonoid R] (a b : R) (m N : ℕ) (h : m ≤ N) :
    (∏ r : Fin N, (if (r : ℕ) < m then a else b)) = a ^ m * b ^ (N - m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < m then a else b) (m + j),
    Finset.prod_range_add]
  have h1 : (∏ x ∈ Finset.range m, (if x < m then a else b)) = a ^ m := by
    rw [Finset.prod_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))]
    simp
  have h2 : (∏ x ∈ Finset.range j, (if m + x < m then a else b)) = b ^ j := by
    rw [Finset.prod_congr rfl (fun x _ => if_neg (by omega))]
    simp
  rw [h1, h2, Nat.add_sub_cancel_left]

theorem rowW_ite (c : Prop) [Decidable c] :
    rowW ![if c then 1 else 0, 0] (if c then 0 else 1) =
      if c then (X (some 0) : MvPolynomial (Option (Fin 2)) ℝ) else X none := by
  split_ifs <;> simp [rowW]

theorem evalW_X_some_zero (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X (some 0)) = rename some (lin3 n₀) := by
  simp [evalW, lin4]

theorem evalW_X_none (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X none) = X none := by
  simp [evalW]

theorem evalW_pderiv_prod_rowW : ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ n : Fin 3 → ℝ,
    evalW n n (pderiv (some 0) (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * k - 1 then 1 else 0, 0] (if (r : ℕ) < 2 * k - 1 then 0 else 1))) =
    C (2 * (k : ℝ) - 1) * rename some (lin3 n ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k) := by
  intro d k hk hkd n
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hm : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hm2 : 2 * (t + 1) - 2 = 2 * t := by omega
  have hj : d + 2 - 2 * (t + 1) = d + 1 - (2 * t + 1) := by omega
  have hprod : (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * (t + 1) - 1 then 1 else 0, 0]
        (if (r : ℕ) < 2 * (t + 1) - 1 then 0 else 1)) =
      X (some 0) ^ (2 * t + 1) * X none ^ (d + 1 - (2 * t + 1)) := by
    simp only [rowW_ite, hm]
    exact prod_fin_ite_lt _ _ _ _ (by omega)
  rw [hprod, hm2, hj, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
  have hne : (none : Option (Fin 2)) ≠ some 0 := by simp
  simp only [pderiv_X_self, pderiv_X_of_ne hne, smul_eq_mul, smul_zero, zero_add, mul_zero,
    add_zero, mul_one, Nat.add_sub_cancel, nsmul_eq_mul]
  simp only [map_mul, map_pow, map_natCast, evalW_X_some_zero, evalW_X_none]
  have hc : (C (2 * ((t + 1 : ℕ) : ℝ) - 1) : MvPolynomial (Option (Fin 3)) ℝ) =
      ((2 * t + 1 : ℕ) : MvPolynomial (Option (Fin 3)) ℝ) := by
    rw [← map_natCast (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ)]
    congr 1
    push_cast
    ring
  rw [hc]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def dom : Set ℂ := {a | den g a ≠ 0}

def cod : Set ℂ := {b | g 1 1 - g 0 1 * b ≠ 0}

variable {g}

theorem det_eq : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

theorem isOpen_dom : IsOpen (dom g) := by
  have hc : Continuous fun a : ℂ => GlobalTheory.CompanionTheory.Ar.PB.FibPt.den g a := by
    show Continuous fun a : ℂ => g 0 0 + g 0 1 * a
    fun_prop
  exact isOpen_ne_fun hc continuous_const

theorem hasDerivAt_mob {a : ℂ} (ha : a ∈ dom g) : HasDerivAt (mob g) (mobD g a) a := by
  have hden : g 0 0 + g 0 1 * a ≠ 0 := ha
  have h1 : HasDerivAt (fun z : ℂ => g 1 0 + g 1 1 * z) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun z : ℂ => g 0 0 + g 0 1 * z) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  have h := h1.div h2 hden
  have heq : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g
      = (fun z : ℂ => g 1 0 + g 1 1 * z) / (fun z : ℂ => g 0 0 + g 0 1 * z) := by
    funext z
    rfl
  have hval : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a
      = (g 1 1 * (g 0 0 + g 0 1 * a) - (g 1 0 + g 1 1 * a) * g 0 1) / (g 0 0 + g 0 1 * a) ^ 2 := by
    rw [show GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a = g.det / (g 0 0 + g 0 1 * a) ^ 2 from rfl,
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    ring
  rw [heq, hval]
  exact h

theorem injOn_mob (hg : IsUnit g.det) : Set.InjOn (mob g) (dom g) := by
  intro a ha b hb hab
  have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
  have hb' : g 0 0 + g 0 1 * b ≠ 0 := hb
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  have h : (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)
      = (g 1 0 + g 1 1 * b) / (g 0 0 + g 0 1 * b) := hab
  rw [div_eq_div_iff ha' hb'] at h
  have h2 : (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (a - b) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hdet
  · exact sub_eq_zero.1 h3

theorem image_mob (hg : IsUnit g.det) : mob g '' dom g = cod g := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
    show g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) ≠ 0
    have hval : g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 0 0 + g 0 1 * a) := by
      field_simp
      ring
    rw [hval]
    exact div_ne_zero hdet ha'
  · intro hb
    have hb' : g 1 1 - g 0 1 * b ≠ 0 := hb
    have hx : (g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b) * (g 1 1 - g 0 1 * b)
        = g 0 0 * b - g 1 0 := div_mul_cancel₀ _ hb'
    have hden : g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 0 1 * hx
    have hnum : g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = b * (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 1 1 * hx
    refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b), ?_, ?_⟩
    · show g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b)) ≠ 0
      rw [hden]
      exact div_ne_zero hdet hb'
    · show (g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) /
          (g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) = b
      rw [hnum, hden, div_div_div_cancel_right₀ hb', mul_div_assoc, div_self hdet, mul_one]

theorem null_affine {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) : volume {a : ℂ | c + d * a = 0} = 0 := by
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  have hx' : c + d * x = 0 := hx
  have hy' : c + d * y = 0 := hy
  have hd : d ≠ 0 := by
    rintro rfl
    rcases h with hc | hd
    · exact hc (by simpa using hx')
    · exact hd rfl
  have hxy : d * (x - y) = 0 := by
    linear_combination hx' - hy'
  exact sub_eq_zero.1 ((mul_eq_zero.1 hxy).resolve_left hd)

theorem ae_prod_self {V : Set ℂ} (hV : volume Vᶜ = 0) :
    (V ×ˢ V : Set (ℂ × ℂ)) =ᵐ[(volume : Measure (ℂ × ℂ))] (Set.univ : Set (ℂ × ℂ)) := by
  rw [ae_eq_univ]
  have h1 : (volume : Measure (ℂ × ℂ)) (Prod.fst ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.preimage_null hV
  have h2 : (volume : Measure (ℂ × ℂ)) (Prod.snd ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.preimage_null hV
  refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
  simpa only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff] using hp

theorem null_dom (hg : IsUnit g.det) : volume (dom g)ᶜ = 0 := by
  have hne : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h.2]
    ring
  refine measure_mono_null (fun a ha => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have ha' : ¬ (g 0 0 + g 0 1 * a ≠ 0) := ha
  exact not_not.1 ha'

theorem null_cod (hg : IsUnit g.det) : volume (cod g)ᶜ = 0 := by
  have hne : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have h01 : g 0 1 = 0 := neg_eq_zero.1 h.2
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h01]
    ring
  refine measure_mono_null (fun b hb => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have hb' : ¬ (g 1 1 - g 0 1 * b ≠ 0) := hb
  show g 1 1 + -g 0 1 * b = 0
  linear_combination not_not.1 hb'

theorem det_smul_one (z : ℂ) :
    LinearMap.det ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq z := by
  have hmul : ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ z := by
    refine LinearMap.ext fun w => ?_
    rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    simp
  rw [hmul, ← Algebra.norm_apply, Algebra.norm_complex_apply]

theorem det_prodMap (z w : ℂ) :
    ((z • (1 : ℂ →L[ℝ] ℂ)).prodMap (w • (1 : ℂ →L[ℝ] ℂ))).det
      = Complex.normSq z * Complex.normSq w := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one]

theorem integral_mob_sq (hg : IsUnit g.det) (f : ℂ × ℂ → ℝ) :
    ∫ p : ℂ × ℂ, (Complex.normSq (mobD g p.1) * Complex.normSq (mobD g p.2)) * f (mob g p.1, mob g p.2)
      = ∫ q : ℂ × ℂ, f q := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure (ℂ × ℂ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hUo : IsOpen (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.isOpen_dom
  have hUm : MeasurableSet (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) :=
    hUo.measurableSet.prod hUo.measurableSet
  have hderiv : ∀ p ∈ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g,
      HasFDerivWithinAt (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
        ((GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1 • (1 : ℂ →L[ℝ] ℂ)).prodMap
          (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2 • (1 : ℂ →L[ℝ] ℂ)))
        (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) p := by
    intro p hp
    exact (HasFDerivAt.prodMap p
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.1).complexToReal_fderiv
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.2).complexToReal_fderiv).hasFDerivWithinAt
  have hinj : Set.InjOn (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := by
    intro p hp q hq hpq
    exact Prod.ext (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.1 hq.1 (congrArg Prod.fst hpq))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.2 hq.2 (congrArg Prod.snd hpq))
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f
  rw [Set.prodMap_image_prod, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.image_mob hg,
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_cod hg)),
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_dom hg)),
    setIntegral_univ, setIntegral_univ] at hcv
  rw [hcv]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_prodMap, Prod.map_apply, smul_eq_mul]
  rw [abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main :
    ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ × ℂ → ℝ, ∫ p : ℂ × ℂ, (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2)) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.1, GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.2) = ∫ q : ℂ × ℂ, f q :=
  fun _ hg f => GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.integral_mob_sq hg f
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem oldIdx_injective {K : Type} {ι : K → Type} :
    Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change (⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h
  cases h
  rfl

theorem isMultiHomog_inc {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (inc f : MRing (Tb ι)) (fun o => o.elim 0 a) := by
  classical
  intro m hm o
  have hinj : Function.Injective (oldIdx (ι := ι)) := oldIdx_injective
  change m ∈ (MvPolynomial.rename oldIdx f).support at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases o with
  | none =>
    simp only [Option.elim_none]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq
    simp [oldIdx] at h0
  | some k =>
    simp only [Option.elim_some]
    refine (Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _
      (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨k, i⟩

theorem sum_single_none {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (j : Fin 2) (o : Option K) :
    ∑ i, (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨o, i⟩ = o.elim 2 (fun _ => 0) := by
  classical
  cases o with
  | none =>
    simp only [Option.elim_none]
    refine (Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _
      (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp [Finsupp.single_apply] <;>
      (intro h
       have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
       have h3 := congrArg (fun t : Fin 2 => (t : ℕ)) h2
       exact absurd h3 (by decide))
  | some k =>
    simp only [Option.elim_some]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) h
    simp at h0

theorem isMultiHomog_quad {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) :
    IsMultiHomog (quad p : MRing (Tb ι)) (fun o => o.elim 2 (fun _ => 0)) := by
  classical
  intro m hm o
  have h1 : (xN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) := by
    simp only [xN, MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    simp only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hq : (quad p : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) +
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    unfold quad
    rw [h1, h2]
  rw [hq] at hm
  have hm2 := Finset.mem_union.mp (MvPolynomial.support_add hm)
  rcases hm2 with h | h
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 0 o
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 1 o

theorem isMultiHomogIdeal_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) : IsMultiHomogIdeal (twist p W) := by
  obtain ⟨S, hS, rfl⟩ := hW
  refine ⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩
  · rintro f (⟨g, hg, rfl⟩ | hf)
    · obtain ⟨a, ha⟩ := hS g hg
      exact ⟨_, isMultiHomog_inc ha⟩
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨_, isMultiHomog_quad p⟩
  · rw [twist, Ideal.map_span, Ideal.span_union]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_holomorphic_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | exact GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame <;> assumption)
end

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.log_det_gram_subharmonic : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | exact GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_logDet_fderiv_norm_le <;> assumption)
end

section

open Complex Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_extension_polydisc_of_log_growth :
    ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ →
      DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} →
      (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) →
        ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) →
      ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧
        ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  intro n S φ ρ C N _ hφ hb
  have hg : HasLogGrowth S id (ball (0 : Fin n → ℂ) ρ) φ := fun K hK _ =>
    ⟨C, N, fun z hz hB => hb z (hK hz) (notMem_coordDivisor.1 hB)⟩
  obtain ⟨ψ, hψ, he⟩ := HasLogGrowth.exists_differentiableOn_extension isOpen_ball
    (hφ.mono fun z hz => ⟨hz.1, notMem_coordDivisor.1 hz.2⟩) hg
  exact ⟨ψ, hψ, fun z hz h0 => he ⟨hz, notMem_coordDivisor.2 h0⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.hermitian_restriction_orthonormal_coords : ∀ (g m : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ W : Submodule ℂ (Fin g → ℂ), Module.finrank ℂ W = m → ∃ c : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W, z' ⬝ᵥ Hm *ᵥ star z = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | exact GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords <;> assumption)
end
