module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle096
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle002
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle205
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Finiteness.Nakayama

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.MBLow.coords_integral_of_closed_indep :
  ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W), (∀ c : Λ → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0) → ∀ (w : I → W) (z : Λ → K₀), (∀ i, i₀ (w i) = ∑ l, z l * i₀ (u i l)) → ∃ z₀ : Λ → W, (∀ l, i₀ (z₀ l) = z l) ∧ ∀ i, w i = ∑ l, z₀ l * u i l := by
  first
  | exact @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
  | (apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients ..)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowEval

noncomputable def absConv (u : ℂ) : Subring (PowerSeries ℂ) where
  carrier := {Φ | Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖}
  zero_mem' := by simp
  one_mem' := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_one, Finset.notMem_singleton.1 hn]
  add_mem' := by
    intro f g hf hg
    refine (Summable.add hf hg).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add (f := _), add_mul]
    exact norm_add_le _ _
  neg_mem' := by
    intro f hf
    simpa [map_neg, neg_mul, norm_neg] using hf
  mul_mem' := by
    intro f g hf hg
    have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
      rw [PowerSeries.coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun kl h => ?_
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
      ring
    show Summable fun n => ‖PowerSeries.coeff n (f * g) * u ^ n‖
    simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => PowerSeries.coeff n f * u ^ n) (g := fun n => PowerSeries.coeff n g * u ^ n) hf hg

noncomputable def evalAt (u : ℂ) : absConv u →+* ℂ where
  toFun Φ := ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n
  map_one' := by
    rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
    simp
  map_zero' := by simp
  map_add' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    simp only [Subring.coe_add, map_add (f := _), add_mul]
    exact hf.of_norm.tsum_add hg.of_norm
  map_mul' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    refine tsum_congr fun n => ?_
    simp only [Subring.coe_mul]
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring

theorem countable_closure {A : Type} [CommRing A] (S : Set A) (hS : S.Countable) :
    Countable (Subring.closure S) := by
  have : Countable S := hS.to_subtype
  have : Countable (MvPolynomial S ℤ) :=
    (MvPolynomial.basisMonomials S ℤ).repr.injective.countable
  let φ : MvPolynomial S ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) Subtype.val
  have hle : Subring.closure S ≤ φ.range := Subring.closure_le.2 fun s hs =>
    ⟨MvPolynomial.X ⟨s, hs⟩, by simp [φ]⟩
  have hc : (φ.range : Set A).Countable := by
    rw [RingHom.coe_range]; exact Set.countable_range _
  exact (hc.mono hle).to_subtype

theorem radius_ge (ε : ℝ) (Φ : PowerSeries ℂ)
    (h : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) :
    ENNReal.ofReal ε ≤ (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrε : (r : ℝ) < ε := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 hr
  refine FormalMultilinearSeries.le_radius_of_summable _ ?_
  have hs := h (r : ℂ) (by exact_mod_cast hr0) (by simpa using hrε)
  refine hs.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
  simp

end GlobalTheory.PowEval


open GlobalTheory.PowEval in
theorem GlobalTheory.exists_injective_evalAt_closure : ∀ (ε : ℝ) (S : Set (PowerSeries ℂ)), 0 < ε → S.Countable → (∀ Φ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) → ∃ (u : ℂ) (i : Subring.closure S →+* ℂ), u ≠ 0 ∧ ‖u‖ < ε ∧ Function.Injective i ∧ ∀ Φ : Subring.closure S, i Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n := by
  intro ε S hε hS h
  have : Countable (Subring.closure S) := countable_closure S hS
  let p : PowerSeries ℂ → FormalMultilinearSeries ℂ ℂ ℂ := fun Φ =>
    FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ
  have hsum : ∀ (Φ : PowerSeries ℂ) (u : ℂ), (p Φ).sum u = ∑' n, PowerSeries.coeff n Φ * u ^ n := by
    intro Φ u
    show FormalMultilinearSeries.ofScalarsSum _ u = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp [smul_eq_mul]
  have hcl : ∀ Φ ∈ Subring.closure S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖ := by
    intro Φ hΦ u hu0 hu
    have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hu
    exact hle hΦ
  have hrad : ∀ Φ ∈ Subring.closure S, ENNReal.ofReal ε ≤ (p Φ).radius := fun Φ hΦ =>
    radius_ge ε Φ (hcl Φ hΦ)
  have hpos : ∀ Φ ∈ Subring.closure S, 0 < (p Φ).radius := fun Φ hΦ =>
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) (hrad Φ hΦ)
  have hball : ∀ Φ ∈ Subring.closure S, Metric.ball (0 : ℂ) ε ⊆ Metric.eball 0 (p Φ).radius := by
    intro Φ hΦ
    rw [← Metric.eball_ofReal]
    exact Metric.eball_subset_eball (hrad Φ hΦ)
  let J := Option {Φ : Subring.closure S // Φ ≠ 0}
  let f : J → ℂ → ℂ := fun i => match i with
    | none => id
    | some Φ => (p (Φ.1 : PowerSeries ℂ)).sum
  have han : ∀ i, AnalyticOnNhd ℂ (f i) (Metric.ball 0 ε) := by
    intro i
    cases i with
    | none => exact analyticOnNhd_id
    | some Φ =>
      exact ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).analyticOnNhd.mono (hball _ Φ.1.2)
  have hnz : ∀ i, ∃ x ∈ Metric.ball (0 : ℂ) ε, f i x ≠ 0 := by
    intro i
    cases i with
    | none =>
      refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · show ((ε / 2 : ℝ) : ℂ) ≠ 0
        exact_mod_cast (by linarith : ε / 2 ≠ 0)
    | some Φ =>
      by_contra hcon
      push Not at hcon
      have hev : (p (Φ.1 : PowerSeries ℂ)).sum =ᶠ[nhds 0] 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with y hy
        exact hcon y hy
      have h0 := ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).hasFPowerSeriesAt.eq_zero_of_eventually hev
      apply Φ.2
      apply Subtype.ext
      ext n
      have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n) h0
      simpa using (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := fun n => PowerSeries.coeff n (Φ.1 : PowerSeries ℂ)) n).1 this
  obtain ⟨u, hu, hx⟩ := GlobalTheory.exists_forall_ne_zero_of_countable_analytic ℂ (Metric.ball 0 ε)
    Metric.isOpen_ball (convex_ball 0 ε).isPreconnected (Metric.nonempty_ball.2 hε) J f han hnz
  have hu0 : u ≠ 0 := hx none
  have hun : ‖u‖ < ε := mem_ball_zero_iff.1 hu
  have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hun
  let i : Subring.closure S →+* ℂ := (evalAt u).comp (Subring.inclusion hle)
  refine ⟨u, i, hu0, hun, ?_, fun Φ => rfl⟩
  refine (injective_iff_map_eq_zero i).2 fun Φ hΦ => ?_
  by_contra hne
  apply hx (some ⟨Φ, hne⟩)
  show (p (Φ : PowerSeries ℂ)).sum u = 0
  rw [hsum]
  exact hΦ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem regroup_fib_tsum {X M : Type} [AddCommMonoid M] [TopologicalSpace M] (n : X → ℕ) (i : ℕ)
    (h : {α | n α = i}.Finite) (f : X → M) :
    ∑' b : n ⁻¹' {i}, f b = ∑ α ∈ h.toFinset, f α := by
  have hs : n ⁻¹' {i} = (h.toFinset : Set X) := by ext; simp
  rw [← Finset.tsum_subtype', ← hs]

theorem lattice_series_regroup : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) (n : X → ℕ) (π : C) (a : X → C) (b : ℝ), π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ α, ‖a α‖ ≤ b * ‖π‖ ^ n α) → ∃ Θ : PowerSeries C, (∀ i, ‖PowerSeries.coeff i Θ‖ ≤ max b 0) ∧ ∑' i, PowerSeries.coeff i Θ * π ^ i = ∑' α, a α ∧ ∀ (e : C →+* ℂ) (u : ℂ), (Summable fun α => ‖e (a α) * (u / e π) ^ n α‖) → (Summable fun i => ‖e (PowerSeries.coeff i Θ) * u ^ i‖) ∧ ∑' i, e (PowerSeries.coeff i Θ) * u ^ i = ∑' α, e (a α) * (u / e π) ^ n α := by
  intro C _ _ _ X n π a b hπ0 hπ1 hfin hb
  classical
  have hmem : ∀ i α, α ∈ (hfin i).toFinset ↔ n α = i := fun i α => by simp
  have hn : Filter.Tendsto n Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun N => Filter.eventually_cofinite.2 ?_
    refine ((Set.finite_lt_nat N).biUnion fun i _ => hfin i).subset ?_
    intro α hα
    simp only [Set.mem_setOf_eq, not_le] at hα
    exact Set.mem_biUnion (x := n α) hα rfl
  have hpow : Filter.Tendsto (fun α => b * ‖π‖ ^ n α) Filter.cofinite (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1).comp hn).const_mul b
  have ha0 : Filter.Tendsto a Filter.cofinite (nhds 0) := squeeze_zero_norm hb hpow
  have ha : Summable a := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha0
  refine ⟨PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i, ?_, ?_, ?_⟩
  · intro i
    rw [PowerSeries.coeff_mk]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun α hα => ?_
    have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.2 hπ0) _
    rw [norm_div, norm_pow, div_le_iff₀ hpi]
    have := hb α
    rw [(hmem i α).1 hα] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpi.le)
  · rw [← ((ha.hasSum.tsum_fiberwise n).tsum_eq)]
    refine tsum_congr fun i => ?_
    rw [PowerSeries.coeff_mk, regroup_fib_tsum n i (hfin i), Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => div_mul_cancel₀ _ (pow_ne_zero _ hπ0)
  · intro e u hsum
    have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
    have hkey : ∀ i, e (PowerSeries.coeff i (PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i)) * u ^ i
        = ∑ α ∈ (hfin i).toFinset, e (a α) * (u / e π) ^ n α := by
      intro i

      rw [PowerSeries.coeff_mk, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmem i α).1 hα, map_div₀, map_pow, div_pow]
      field_simp
    simp_rw [hkey]
    have hf : Summable fun α => e (a α) * (u / e π) ^ n α := hsum.of_norm
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_sum_le _ _) ?_
      have := (hsum.hasSum.tsum_fiberwise n).summable
      exact this.congr fun i => regroup_fib_tsum n i (hfin i) (fun α => ‖e (a α) * (u / e π) ^ n α‖)
    · rw [← ((hf.hasSum.tsum_fiberwise n).tsum_eq)]
      exact tsum_congr fun i => (regroup_fib_tsum n i (hfin i) _).symm

end GlobalTheory.MBLow
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns : (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n), ‖(u.1.submatrix I J).det‖ ≤ 1) ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ), ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
  first | exact @GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | exact GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | (intros; apply GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard <;> assumption)
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.Neat

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma apply_mem_smul_top (I : Ideal R) (T : Module.End R M) {y : M}
    (hy : y ∈ I • (⊤ : Submodule R M)) : T y ∈ I • (⊤ : Submodule R M) := by
  have h : (I • (⊤ : Submodule R M)).map T ≤ I • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
  exact h ⟨y, hy, rfl⟩

lemma pow_add_sub_pow_mem (I : Ideal R) (A B : Module.End R M)
    (hB : ∀ x, B x ∈ I • (⊤ : Submodule R M)) (n : ℕ) :
    ∀ x, ((A + B) ^ n - A ^ n) x ∈ I • (⊤ : Submodule R M) := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have : (A + B) ^ (n + 1) - A ^ (n + 1) = ((A + B) ^ n - A ^ n) * A + (A + B) ^ n * B := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [this, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply]
    exact Submodule.add_mem _ (ih _) (apply_mem_smul_top I _ (hB x))

lemma pow_prime_pow_unipotent (I : Ideal R) (α : Module.End R M) {p : ℕ} (hp : p.Prime)
    (hpI : (p : R) ∈ I) (a r : ℕ) (h : ∀ x, ((α - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) :
    ∀ x, ((α ^ p ^ a - 1) ^ r) x ∈ I • (⊤ : Submodule R M) := by
  obtain ⟨F, hF⟩ := (Commute.one_right (α - 1)).exists_add_pow_prime_pow_eq hp a
  have hγ : α ^ p ^ a - 1 = (α - 1) ^ p ^ a + (p : Module.End R M) * ((α - 1) * (1 * F)) := by
    rw [sub_add_cancel, one_pow] at hF; rw [hF, mul_assoc, mul_assoc]; abel
  have hB : ∀ x, ((p : Module.End R M) * ((α - 1) * (1 * F))) x ∈ I • (⊤ : Submodule R M) := by
    intro x
    rw [Module.End.mul_apply, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul R]
    exact Submodule.smul_mem_smul hpI trivial
  intro x
  have h1 := pow_add_sub_pow_mem I ((α - 1) ^ p ^ a) _ hB r x
  rw [← hγ, LinearMap.sub_apply] at h1
  have hle : r ≤ p ^ a * r := Nat.le_mul_of_pos_left r (pow_pos hp.pos a)
  have h2 : (((α - 1) ^ p ^ a) ^ r) x ∈ I • (⊤ : Submodule R M) := by
    rw [← pow_mul, ← Nat.add_sub_cancel' hle, pow_add, Module.End.mul_apply]
    exact h _
  have := Submodule.add_mem _ h1 h2
  simpa using this

end GlobalTheory.Neat

namespace GlobalTheory.Neat

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma eq_one_of_unipotent_mod_of_unit [IsDomain R] [IsNoetherianRing R] [Module.Finite R M]
    [Module.IsTorsionFree R M] (I : Ideal R) (hI : I ≠ ⊤) (γ : Module.End R M) (b r : ℕ)
    (hb : γ ^ b = 1) (c : R) (hc : 1 - c * (b : R) ^ (r + 1) ∈ I)
    (h : ∀ x, ((γ - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) : γ = 1 := by
  have hSN : (∑ i ∈ Finset.range b, γ ^ i) * (γ - 1) = 0 := by
    rw [geom_sum_mul, hb, sub_self]
  have hE : (b : Module.End R M) - ∑ i ∈ Finset.range b, γ ^ i
      = (γ - 1) * -∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j := by
    rw [mul_neg, Finset.mul_sum]
    simp only [mul_geom_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    abel
  have hcomm : Commute (γ - 1) (-∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j) := by
    refine Commute.neg_right (Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_)
    exact ((Commute.refl γ).sub_left (Commute.one_left γ)).pow_right j
  set Q := -∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j with hQ
  set e : Module.End R M := (b : Module.End R M) - ∑ i ∈ Finset.range b, γ ^ i with he
  set P : Submodule R M := LinearMap.range (γ - 1) with hP
  have hPI : P ≤ I • P := by
    rintro y ⟨z, rfl⟩
    have he1 : ∀ w ∈ P, e w = (b : R) • w := by
      rintro w ⟨v, rfl⟩
      rw [he, LinearMap.sub_apply, Module.End.natCast_apply, ← Module.End.mul_apply, hSN,
        LinearMap.zero_apply, sub_zero, Nat.cast_smul_eq_nsmul]
    have hek : ∀ k : ℕ, (e ^ k) ((γ - 1) z) = (b : R) ^ k • (γ - 1) z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, he1 _ ⟨z, rfl⟩, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have hrange : LinearMap.range e ≤ P := by
      rw [hE, Module.End.mul_eq_comp]; exact LinearMap.range_comp_le_range _ _
    have hmap : ∀ w ∈ I • (⊤ : Submodule R M), e w ∈ I • P := by
      intro w hw
      have : (I • (⊤ : Submodule R M)).map e ≤ I • P := by
        rw [Submodule.map_smul'', Submodule.map_top]; exact Submodule.smul_mono le_rfl hrange
      exact this ⟨w, hw, rfl⟩
    have hr : (e ^ r) ((γ - 1) z) ∈ I • (⊤ : Submodule R M) := by
      rw [hE, hcomm.mul_pow, Module.End.mul_apply]; exact h _
    have hbig : (b : R) ^ (r + 1) • (γ - 1) z ∈ I • P := by
      rw [← hek, pow_succ', Module.End.mul_apply]; exact hmap _ hr
    have hsplit : (γ - 1) z = (1 - c * (b : R) ^ (r + 1)) • (γ - 1) z
        + c • ((b : R) ^ (r + 1) • (γ - 1) z) := by
      rw [smul_smul, ← add_smul, sub_add_cancel, one_smul]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hc ⟨z, rfl⟩) (Submodule.smul_mem _ c hbig)
  obtain ⟨t, ht1, ht0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I P
    (IsNoetherian.noetherian P) hPI
  have htne : t ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem ht1
  ext x
  have hx := ht0 _ (LinearMap.mem_range_self (γ - 1) x)
  rw [smul_eq_zero_iff_right htne, LinearMap.sub_apply, sub_eq_zero] at hx
  simpa using hx

end GlobalTheory.Neat

theorem GlobalTheory.eq_one_of_finite_order_unipotent_mod_two_primes : ∀ (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Finite (𝓞 E) Λ] [Module.IsTorsionFree (𝓞 E) Λ] (α : Λ →ₗ[𝓞 E] Λ) (m r g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 0 < m → α ^ m = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → (∀ x, ((α - 1) ^ r) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Λ)) → (∀ x, ((α - 1) ^ r) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Λ)) → α = 1 := by
  intro E _ _ Λ _ _ _ _ α m r g₁ g₂ I₁ I₂ hm hαm hg₁ hg₂ hne hI₁ hI₂ hg₁I hg₂I h₁ h₂
  have key : ∀ (p : ℕ) (I : Ideal (𝓞 E)), p.Prime → I ≠ ⊤ → (p : 𝓞 E) ∈ I →
      (∀ x, ((α - 1) ^ r) x ∈ I • (⊤ : Submodule (𝓞 E) Λ)) → ∃ a : ℕ, α ^ p ^ a = 1 := by
    intro p I hp hI hpI h
    obtain ⟨a, b, hpb, hmab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.one_lt.ne'
    refine ⟨a, ?_⟩
    have hcop : Nat.Coprime p (b ^ (r + 1)) :=
      Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd).2 hpb)
    obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := 𝓞 E) hcop
    refine GlobalTheory.Neat.eq_one_of_unipotent_mod_of_unit I hI (α ^ p ^ a) b r ?_ v ?_
      (GlobalTheory.Neat.pow_prime_pow_unipotent I α hp hpI a r h)
    · rw [← pow_mul, ← hmab, hαm]
    · have : 1 - v * (b : 𝓞 E) ^ (r + 1) = u * p := by
        rw [← huv]; push_cast; ring
      rw [this]; exact I.mul_mem_left u hpI
  obtain ⟨a, ha⟩ := key g₁ I₁ hg₁ hI₁ hg₁I h₁
  obtain ⟨c, hc⟩ := key g₂ I₂ hg₂ hI₂ hg₂I h₂
  have hcop : Nat.Coprime (g₁ ^ a) (g₂ ^ c) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hg₁ hg₂).2 hne)
  have hd : orderOf α ∣ Nat.gcd (g₁ ^ a) (g₂ ^ c) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hc)
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one hd)
end
