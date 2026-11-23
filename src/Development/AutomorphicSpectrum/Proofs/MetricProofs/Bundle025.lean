module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle005
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle017
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.ComplexPlace

theorem exists_ringHom_of_finiteType {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (v : A →+* ℂ) (hv : (RingHom.ker v).IsMaximal) (M : Ideal B)
    (hMm : M.IsMaximal) (hM : ∀ a, v a = 0 → algebraMap A B a ∈ M) :
    ∃ ψ : B →+* ℂ, ∀ a, ψ (algebraMap A B a) = v a := by
  letI κF : Field (A ⧸ RingHom.ker v) := Ideal.Quotient.field _
  letI KF : Field (B ⧸ M) := Ideal.Quotient.field _
  let φ : A ⧸ RingHom.ker v →+* B ⧸ M :=
    Ideal.quotientMap M (algebraMap A B) (fun a ha => hM a (RingHom.mem_ker.mp ha))
  letI : Algebra (A ⧸ RingHom.ker v) (B ⧸ M) := φ.toAlgebra
  haveI : IsScalarTower A (A ⧸ RingHom.ker v) (B ⧸ M) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (B ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M) (Ideal.Quotient.mkₐ_surjective A M)
  haveI : Algebra.FiniteType (A ⧸ RingHom.ker v) (B ⧸ M) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ RingHom.ker v) (B ⧸ M)
  haveI : Module.Finite (A ⧸ RingHom.ker v) (B ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  letI : Algebra (A ⧸ RingHom.ker v) ℂ := (RingHom.kerLift v).toAlgebra
  let g : (B ⧸ M) →ₐ[A ⧸ RingHom.ker v] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g.toRingHom.comp (Ideal.Quotient.mk M), fun a => ?_⟩
  exact g.commutes (Ideal.Quotient.mk (RingHom.ker v) a)

theorem isLocalRing_and_ker {L : Type} [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ _ : IsLocalRing O, RingHom.ker v = IsLocalRing.maximalIdeal O := by
  have hunit : ∀ s : O, IsUnit s ↔ v s ≠ 0 := by
    intro s
    constructor
    · intro h
      exact (h.map v).ne_zero
    · intro h
      have hs : (s : L) ≠ 0 := by
        intro h0
        apply h
        have : s = 0 := Subtype.ext h0
        simp [this]
      refine IsUnit.of_mul_eq_one (⟨(s : L)⁻¹, hv s h⟩ : O) ?_
      exact Subtype.ext (mul_inv_cancel₀ hs)
  have hloc : IsLocalRing O := by
    refine IsLocalRing.of_nonunits_add ?_
    intro a b ha hb
    have ha' : v a = 0 := by
      by_contra h
      exact ha ((hunit a).2 h)
    have hb' : v b = 0 := by
      by_contra h
      exact hb ((hunit b).2 h)
    intro hab
    exact (hunit _).1 hab (by simp [ha', hb'])
  refine ⟨hloc, ?_⟩
  ext s
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  simp

theorem exists_valuationSubring_place (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) →
      ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧
        (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  obtain ⟨hloc, hker⟩ := isLocalRing_and_ker O v hv
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing O.subtype
  refine ⟨V, fun s hs => hV ⟨s, hs⟩, fun T hT => ?_⟩
  let S : Finset L := T ∪ (T.filter (fun t => t⁻¹ ∈ V)).image (fun t => t⁻¹)
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hT x h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ht).2
  let B : Subalgebra O L := Algebra.adjoin O (S : Set L)
  let VA : Subalgebra O L :=
    { V.toSubring with algebraMap_mem' := fun s => hV s }
  have hBV : B ≤ VA := Algebra.adjoin_le (fun x hx => hSV x hx)
  haveI : Algebra.FiniteType O B :=
    (Subalgebra.fg_iff_finiteType B).1 (Subalgebra.fg_adjoin_finset S)
  let f : B →+* V :=
    { toFun := fun x => ⟨x.1, hBV x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  have hn : n ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ n := h ▸ Submodule.mem_top
    have h2 : f 1 ∈ IsLocalRing.maximalIdeal V := h1
    rw [map_one] at h2
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal V).ne_top h2
  obtain ⟨M, hMm, hnM⟩ := Ideal.exists_le_maximal n hn
  have hM : ∀ a : O, v a = 0 → algebraMap O B a ∈ M := by
    intro a ha
    apply hnM
    have ha' : a ∈ IsLocalRing.maximalIdeal O := hker ▸ RingHom.mem_ker.mpr ha
    show f (algebraMap O B a) ∈ IsLocalRing.maximalIdeal V
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha' ⊢
    intro hu
    apply ha'
    exact hlocal.map_nonunit a hu
  have hvm : (RingHom.ker v).IsMaximal := by
    rw [hker]
    exact IsLocalRing.maximalIdeal.isMaximal O
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_finiteType v hvm M hMm hM
  have hO : O ≤ B.toSubring := fun s hs => B.algebraMap_mem (⟨s, hs⟩ : O)
  refine ⟨B.toSubring, hO, ψ, ?_, ?_, ?_⟩
  · intro t ht
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ ht))
  · intro s
    exact hψ s
  · intro t ht _ hi
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨ht, hi⟩, rfl⟩)))

end GlobalTheory.CompanionTheory.Ar.ComplexPlace
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_conj_invariant_mollifier : ∀ n : ℕ, ∃ ρ : ReciprocityTheory.AnForm.A.Mollifier n, ∀ v, ρ.toFun (star v) = ρ.toFun v := by
  intro n
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hmp : MeasureTheory.MeasurePreserving (fun v : Fin n → ℂ => star v) :=
    MeasureTheory.volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)
  have hme : MeasurableEmbedding (fun v : Fin n → ℂ => star v) :=
    (starLinearEquiv ℝ (A := Fin n → ℂ)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v : Fin n → ℂ => star v) :=
    contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)
  have hI : MeasureTheory.Integrable ρ.toFun :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [ρ.integral_eq_one]; norm_num)
  have hcomp : ∫ w : Fin n → ℂ, ρ.toFun (star w) = 1 := by
    rw [hmp.integral_comp hme ρ.toFun, ρ.integral_eq_one]
  have hI2 : MeasureTheory.Integrable (fun w : Fin n → ℂ => ρ.toFun (star w)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hcomp]; norm_num)
  refine ⟨⟨fun v => (ρ.toFun v + ρ.toFun (star v)) / 2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (ρ.contDiff.add (ρ.contDiff.comp hsm)).div_const 2
  · intro w
    exact div_nonneg (add_nonneg (ρ.nonneg _) (ρ.nonneg _)) two_pos.le
  · intro w hw
    by_contra h
    have h1 : ρ.toFun w = 0 := by
      by_contra h'
      exact h (ρ.support_subset h')
    have h2 : ρ.toFun (star w) = 0 := by
      by_contra h'
      have hb := ρ.support_subset h'
      rw [Metric.mem_ball, dist_zero_right, norm_star] at hb
      exact h (by rw [Metric.mem_ball, dist_zero_right]; exact hb)
    exact hw (by simp [h1, h2])
  · show ∫ w : Fin n → ℂ, (ρ.toFun w + ρ.toFun (star w)) / 2 = 1
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add hI hI2, ρ.integral_eq_one, hcomp]
    norm_num
  · intro c w hc
    show (ρ.toFun (c • w) + ρ.toFun (star (c • w))) / 2 = (ρ.toFun w + ρ.toFun (star w)) / 2
    rw [star_smul, ρ.circle_inv c w hc, ρ.circle_inv (star c) (star w) (by rw [norm_star]; exact hc)]
  · intro v
    show (ρ.toFun (star v) + ρ.toFun (star (star v))) / 2 = (ρ.toFun v + ρ.toFun (star v)) / 2
    rw [star_star, add_comm]
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open ReciprocityTheory.AnForm.R

def chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (g : MvPolynomial (Fin m) ℂ) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  (Ideal.span {algebraMap _ (locRing I t) g}).comap (algebraMap _ (locRing I t))

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt IsLocalRing

variable {m : ℕ}

theorem span_eq_top_of_forall_dot_eq_zero (S : Set (Fin m → ℂ))
    (hS : ∀ v : Fin m → ℂ, (∀ w ∈ S, ∑ j, v j * w j = 0) → v = 0) :
    Submodule.span ℂ S = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hv : (fun j => f (fun k => if j = k then (1 : ℂ) else 0)) = 0 := by
    apply hS
    intro w hw
    have h1 : f w = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hw))
    rw [LinearMap.pi_apply_eq_sum_univ f w] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm]
  apply hf0
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ f x, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun hv j
  simp only [Pi.zero_apply] at this
  rw [this, smul_zero]

theorem lin_mem_of_eval_eq_zero (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ J) (h0 : eval t a = 0) :
    ∑ i, C (gradP t a i) * (X i - C (t i)) ∈ J := by
  have h := hJ (ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor t a)
  rw [h0, map_zero, sub_zero] at h
  have h2 := J.sub_mem ha h
  rwa [sub_sub_cancel] at h2

theorem ptI_le_of_span_grad_eq_top (t : Fin m → ℂ) (J : Ideal (MvPolynomial (Fin m) ℂ))
    (hJ : ptI t ^ 2 ≤ J) (A : Set (MvPolynomial (Fin m) ℂ)) (hAJ : A ⊆ J)
    (hA0 : ∀ a ∈ A, eval t a = 0) (hA : Submodule.span ℂ (gradP t '' A) = ⊤) :
    ptI t ≤ J := by
  let φ : (Fin m → ℂ) →ₗ[ℂ] MvPolynomial (Fin m) ℂ :=
    { toFun := fun v => ∑ i, C (v i) * (X i - C (t i))
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          MvPolynomial.smul_eq_C_mul, mul_assoc] }
  have hφ : ∀ v, φ v = ∑ i, C (v i) * (X i - C (t i)) := fun v => rfl
  have hspan : Submodule.span ℂ (gradP t '' A) ≤ Submodule.comap φ (J.restrictScalars ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, haA, rfl⟩
    show φ (gradP t a) ∈ J
    rw [hφ]
    exact lin_mem_of_eval_eq_zero t J hJ (hAJ haA) (hA0 a haA)
  have key : ∀ i, X i - C (t i) ∈ J := by
    intro i
    have hmem : (Pi.single i 1 : Fin m → ℂ) ∈ Submodule.comap φ (J.restrictScalars ℂ) :=
      hspan (by rw [hA]; exact Submodule.mem_top)
    have h2 : φ (Pi.single i 1) ∈ J := hmem
    rw [hφ, Finset.sum_eq_single i] at h2
    · simpa using h2
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact key i

private theorem gradP_eq_eval_pderiv (t : Fin m → ℂ) (a : MvPolynomial (Fin m) ℂ) (j : Fin m) :
    gradP t a j = eval t (pderiv j a) := by
  induction a using MvPolynomial.induction_on
  next c =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, pderiv_C, map_zero, Pi.zero_apply]
  next p q hp hq =>
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, Pi.add_apply, hp, hq, map_add (f := _), map_add (f := _)]
  next p i hp =>
    have hX : gradP t (X i) = Pi.single i 1 := by
      have h2 : (X i : MvPolynomial (Fin m) ℂ) = (X i - C (t i)) + C (t i) := by ring
      rw [h2, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin,
        ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_C, add_zero]
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_mul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, hp, hX, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
      map_mul, eval_X]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]

theorem span_algebraMap_eq_map_ptIdeal (e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : Fin e → MvPolynomial (Fin m) ℂ) (hI : ∀ h ∈ I, eval t h = 0) (hr : ∀ l, eval t (r l) = 0)
    (hv : ∀ v : Fin m → ℂ, (∀ h ∈ I, ∑ j, v j * eval t (pderiv j h) = 0) →
      (∀ l, ∑ j, v j * eval t (pderiv j (r l)) = 0) → v = 0) :
    Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) := by
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  have hpt : ptI t = ptIdeal t := by
    ext a
    rw [ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    unfold ptIdeal
    rw [RingHom.mem_ker]
  have hmemPt : ∀ a, eval t a = 0 → a ∈ ptIdeal t := fun a ha => by
    rw [← hpt, ReciprocityTheory.AnForm.R.JacobianCriterionAlt.mem_ptIdeal]
    exact ha
  have hφ : ∀ a, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)
        (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t) a) := fun a => rfl
  have hI0 : ∀ a ∈ I, algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a = 0 := by
    intro a ha
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  set N : Ideal (locRing I t) := Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l))
    with hN
  set M : Ideal (locRing I t) := Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) with hM
  have hNM : N ≤ M := by
    rw [hN, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact Ideal.mem_map_of_mem _ (hmemPt _ (hr l))
  have key : ptI t ≤ Ideal.comap (algebraMap _ (locRing I t)) (N ⊔ M ^ 2) := by
    refine ptI_le_of_span_grad_eq_top t _ ?_ ((I : Set (MvPolynomial (Fin m) ℂ)) ∪ Set.range r)
      ?_ ?_ ?_
    · intro a ha
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_right
      rw [hM, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (by rw [← hpt]; exact ha)
    · rintro a (ha | ⟨l, rfl⟩)
      · rw [SetLike.mem_coe, Ideal.mem_comap, hI0 a ha]
        exact Submodule.zero_mem _
      · rw [SetLike.mem_coe, Ideal.mem_comap]
        exact Ideal.mem_sup_left (Ideal.subset_span ⟨l, rfl⟩)
    · rintro a (ha | ⟨l, rfl⟩)
      · exact hI a ha
      · exact hr l
    · apply span_eq_top_of_forall_dot_eq_zero
      intro v hvS
      apply hv v
      · intro h hh
        have h3 := hvS _ ⟨h, Or.inl hh, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
      · intro l
        have h3 := hvS _ ⟨r l, Or.inr ⟨l, rfl⟩, rfl⟩
        simpa only [gradP_eq_eval_pderiv] using h3
  have hMle : M ≤ N ⊔ M ^ 2 := Ideal.map_le_iff_le_comap.mpr (hpt.symm.le.trans key)
  haveI := hloc
  haveI := hnoeth
  have hMtop : M ≠ ⊤ := by
    haveI : (ptIdeal t).IsPrime := ptIdeal_isPrime t
    intro htop
    have hmax : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) =
        IsLocalRing.maximalIdeal (Localization.AtPrime (ptIdeal t)) :=
      Localization.AtPrime.map_eq_maximalIdeal
    have hMeq : M = Ideal.map
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
        (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t)) := by
      rw [hM, Ideal.map_map]
      exact congrArg (fun f => Ideal.map f (ptIdeal t)) (RingHom.ext fun a => rfl)
    have hc := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I))
      Ideal.Quotient.mk_surjective (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t))
    rw [← hMeq, htop, Ideal.comap_top] at hc
    have hb : Ideal.comap
        (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) I)) ⊥ ≤
        Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt t)) (ptIdeal t) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
      exact Ideal.map_mono (fun a ha => hmemPt a (hI a ha)) hx
    rw [sup_eq_left.mpr hb, hmax] at hc
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (ptIdeal t))).ne_top hc.symm
  have hMj : M ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hMtop
  have hle : M ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian M) hMj ?_
    rw [Ideal.smul_eq_mul, ← pow_two]
    exact hMle
  exact le_antisymm hNM hle

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_smooth_conj_invariant_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (a : K → ℤ), ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric | exact GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric <;> assumption)
end
