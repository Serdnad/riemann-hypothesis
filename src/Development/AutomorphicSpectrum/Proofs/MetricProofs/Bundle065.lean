module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle026
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrame
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle056
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle026
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GluedLocalRegularizationsOnAtlas
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.alternating_form_lattice_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, Function.Bijective form → ∀ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 → (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) → e.range.relIndex (dualLattice h e.range) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.latEmb_relIndex_dual_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.latEmb_relIndex_dual_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.latEmb_relIndex_dual_ne_zero <;> assumption)
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def setChartSet (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def setChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setChartSet S σ Ψ)

def setSegChartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def setSegChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setSegChartSet S σ i)

def setSegreCone (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, x = fun a => segre z (σ a)}

theorem isMultiHomogIdeal_toR {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal Q) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ

theorem cone_scale {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : (fun p => c p.1 * z p) ∈ conePts Q := by
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ c z hz.2⟩
  obtain ⟨i, hi⟩ := hz.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem exists_segre_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) {c : ℂ} (hc : c ≠ 0) :
    ∃ z' ∈ conePts Q, segre z' = c • segre z := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, cone_scale hQ (c := fun k => if k = k0 then c else 1) (fun k => ?_) hz, ?_⟩
  · split_ifs
    · exact hc
    · exact one_ne_zero
  · exact GoodChartZeroSet.segre_scaleBlock k0 c z

end Defs

section ZeroSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ)) f

theorem eval_liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (f : MRingOver ℂ ι) :
    eval x (liftPolyC σ i f) = eval (chartLift σ i x) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [liftPolyC]
  | add f g hf hg =>
    simp only [liftPolyC, map_add (f := _)] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [liftPolyC, map_mul] at hf ⊢
    rw [hf]
    simp [chartLift]

theorem segChart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    zeroSet (setSegChartIdeal (conePts Q) σ i) = setSegChartSet (conePts Q) σ i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setSegChartSet (conePts Q) σ i, eval y q = 0) →
        eval x q = 0 :=
      fun q hq => hx q (by rw [setSegChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [ReciprocityTheory.ChartRestriction.G.Geo.segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ Q, eval (chartLift σ i x) f = 0 := by
      intro f hf
      rw [← eval_liftPolyC]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPolyC]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (cone_scale hQ (c := fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

theorem chart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ := by
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [setChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setChartSet (conePts Q) σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [setChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (GoodChartZeroSet.linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, GoodChartZeroSet.eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, GoodChartZeroSet.eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have hzero : (x a)⁻¹ • x ∈ zeroSet (setSegChartIdeal (conePts Q) σ (σ a)) := by
    intro f hf
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ Finset.range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [GoodChartZeroSet.eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul hQ hz (inv_ne_zero h0)
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [GoodChartZeroSet.eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [segChart_zeroSet hQ σ (σ a)] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul hQ hz' ha
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end ZeroSet

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.holomorphic_coefficients_in_frame : ∀ (n m g : ℕ) (U : Set (Fin n → ℂ)) (d : Fin m → (Fin n → ℂ) → Fin g → ℂ) (x : (Fin n → ℂ) → Fin g → ℂ) (w : (Fin n → ℂ) → Fin m → ℂ), IsOpen U → (∀ b, DifferentiableOn ℂ (d b) U) → DifferentiableOn ℂ x U → (∀ t ∈ U, LinearIndependent ℂ (fun b => d b t)) → (∀ t ∈ U, x t = ∑ b, w t b • d b t) → DifferentiableOn ℂ w U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.lattice_rational_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ], ∃ N : ℕ, Module.finrank ℚ E * N = Module.finrank ℤ Λ ∧ ∃ e : Λ →+ (Fin N → E), Function.Injective e ∧ (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) ∧ ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.alternating_form_hermitian_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, (∀ x, form x x = 0) → Function.Bijective form → (∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, form (a • x) y = form x (a' • y)) → ∃ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) ∧ (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) ∧ (∀ u v, B u v = - B v u) ∧ ∀ u, (∀ v, B v u = 0) → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil.exists_rat_bilin | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil.exists_rat_bilin | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil.exists_rat_bilin <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem flat_weight_extends : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : LocPot X) (u : X → ℝ) (C₁ : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ C₁ * Real.log (rW L s y)) → ∃ u' : X → ℝ, A.Smooth u' ∧ (∀ y ∉ bdry s, u' y = u y) ∧ IsPsh A (th + LocPot.ofFun u') ∧ IsPsh A ((th + LocPot.ofFun u').rsmul (-1)) := by
  intro e X _ _ _ A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hp' hb
  have hthm : IsPotential A (th.rsmul (-1)) := isPotentialRsmul A (-1) th hth
  have hum : A.SmoothOn (bdry s)ᶜ (fun y => -u y) := fun j => (hu j).neg
  have hpm : IsPshOn A (bdry s)ᶜ (th.rsmul (-1) + LocPot.ofFun (fun y => -u y)) := by
    intro x j y hy w
    have hf : (((th.rsmul (-1) + LocPot.ofFun (fun y => -u y)).φ x) ∘ (A.chart j).symm) =
        (((th + LocPot.ofFun u).rsmul (-1)).φ x) ∘ (A.chart j).symm := by
      funext z
      simp only [Function.comp, LocPot.rsmul]
      show -1 * th.φ x _ + -u _ = -1 * (th.φ x _ + u _)
      ring
    rw [hf]
    exact hp' x j y hy w
  obtain ⟨C5, h5⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hb
  obtain ⟨C6, h6⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn (th.rsmul (-1)) (fun y => -u y) C₁ hthm hum hpm
    (fun y hy => by simpa using hb y hy)
  have hM : ∀ y ∉ bdry s, |u y| ≤ max C5 C6 := by
    intro y hy
    have a := (h5.2.2.2 y hy).2
    have b := (h6.2.2.2 y hy).2
    rw [abs_le]
    constructor
    · have := le_max_right C5 C6; linarith
    · exact a.trans (le_max_left _ _)
  obtain ⟨hcl, hde⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  obtain ⟨u', hu', heq⟩ := GlobalTheory.T.smooth_extension_across_closed_dense e X A (bdry s) u hcl hde
    (GlobalTheory.T.bounded_psh_correction_locally_smooth e X A L s nb m W hs hsnc th u _ hth hu hp hp' hM)
  have hsm : ∀ x, A.SmoothOn ((th + LocPot.ofFun u').U x) ((th + LocPot.ofFun u').φ x) := by
    intro x j
    have h1 : ContDiffOn ℝ ∞ (th.φ x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
    have h2 : ContDiffOn ℝ ∞ (u' ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hu' j).mono fun y hy => ⟨hy.1, trivial⟩
    exact h1.add h2
  refine ⟨u', hu', heq, ?_, ?_⟩
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) (th + LocPot.ofFun u) (th + LocPot.ofFun u') hcl hde
      (fun _ => rfl) hsm ?_ hp
    intro x y _ hy
    show th.φ x y + u' y = th.φ x y + u y
    rw [heq y hy]
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) ((th + LocPot.ofFun u).rsmul (-1))
      ((th + LocPot.ofFun u').rsmul (-1)) hcl hde (fun _ => rfl) ?_ ?_ hp'
    · intro x j
      have := (hsm x j).const_smul (-1 : ℝ)
      refine this.congr fun y _ => ?_
      simp [LocPot.rsmul]
    · intro x y _ hy
      show -1 * (th.φ x y + u' y) = -1 * (th.φ x y + u y)
      rw [heq y hy]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.pullback_statement_holds : PullbackStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | exact GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.local_psh_regularization_log_bound : ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D), ContinuousOn u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) u → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) → ∃ (C t₀ : ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ t₀ ≤ 1 / 8 ∧ ∀ t, 0 < t → t ≤ t₀ → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, w t z = max (u z) (-C * Real.log (Real.log (1 / t)))) ∧ ContDiffOn ℝ ∞ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (ReciprocityTheory.AnForm.A.molli ρ t (w t)) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, u z ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z) ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z t ∧ polyMaxOff S u z t - epsT C t ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ∧ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ≤ polyMaxOff S u z t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.molli_trunc_near_polyMax | exact GlobalTheory.CompanionTheory.Ar.Giv.molli_trunc_near_polyMax | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.molli_trunc_near_polyMax <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.local_regularization_gradient_bound : ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → DifferentiableOn ℝ u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ u z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, rLoc S m z ≤ Real.log (1 / t) + K → polyMaxOff S u z t ≤ u z + t ^ ((1 : ℝ) / 3) / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_le_of_rLoc_le | exact GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_le_of_rLoc_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_le_of_rLoc_le <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.mInt_eq_integral_maMeasure : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → IsPsh A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ i, IsPshOn A U (P i + LocPot.ofFun (f i) + Θ)) → ∀ g : X → ℝ, ContinuousOn g U → Integrable g (maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) → MIntegrable A (fun i => P i + LocPot.ofFun (f i) + Θ) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i) + Θ) g = ∫ y, g y ∂(maMeasure A fun i => P i + LocPot.ofFun (f i) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null | exact GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mInt_eq_integral_maMeasure_off_null <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.mixed_energy_regularization_bound : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail | exact GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.limit_measure_tail <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.glued_local_regularizations_on_atlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ M : ℝ) (x : Fin B.n → X) (S : Fin B.n → Finset (Fin e)) (m : Fin B.n → Fin e → ℕ), A.Compatible B → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) → (∀ j, (B.chart j).source ⊆ th.U (x j)) → (∀ y, logNormSec L s y ≤ 0) → IsClosed (bdry s) → (∀ j, ∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S j, y i = 0)) → (∀ j, ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s → |rW L s ((B.chart j).symm y) - rLoc (S j) (m j) y| ≤ M) → IsSingWeight A L s th ph C₅ → ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |(polyMaxOff (S j) (fun z => th.φ (x j) ((B.chart j).symm z) + ph ((B.chart j).symm z)) (B.chart j y) t - th.φ (x j) y) - (polyMaxOff (S k) (fun z => th.φ (x k) ((B.chart k).symm z) + ph ((B.chart k).symm z)) (B.chart k y) t - th.φ (x k) y)| ≤ epsT C t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare | exact GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare <;> assumption)
end
