module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle089
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit (TailLogBound tail tailLogBound_dim_zero)

theorem tailLogBound_of_phi_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (CE : ℝ)
    (H : TailLogBound A Yo r Φ CE) : TailLogBound A Yo r Ψ CE := by
  have hD : locDens A Φ = locDens A Ψ := by
    funext j y
    simp only [locDens, h]
  intro R₀ hR
  obtain ⟨h1, h2⟩ := H R₀ hR
  refine ⟨?_, ?_⟩
  · unfold MIntegrable at h1 ⊢
    rw [← hD]
    exact h1
  · unfold mInt integralWith at h2 ⊢
    rw [← hD]
    exact h2

theorem tailLogBound_of_tailBound : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (C₁ : ℝ), (∀ i, IsPotential A (Θ i)) → (∀ i, IsPosPot A (Θ i)) → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₁ → ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (u : Fin e → X → ℝ) (T : Fin e → LocPot X), (∀ i, A.Smooth (u i)) → (∀ i, IsPsh A (Θ i + LocPot.ofFun (u i))) → (∀ i, ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ u i y ∧ u i y ≤ 0) → (∀ i x y, (T i).φ x y = (Θ i).φ x y + u i y) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A (bdry s)ᶜ (rW L s) T CE := by
  intro tb e X _ _ _ A Θ L s n m W C₁ hΘ hΘp hL hS hsnc hle hC₁
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain ⟨CE, hCE⟩ := tailLogBound_dim_zero A (bdry s)ᶜ (rW L s) (fun i => i.elim0)
    refine ⟨max CE 0, le_max_right _ _, fun u T _ _ _ _ R₀ hR₀ => ?_⟩
    have hTe : T = fun i => i.elim0 := funext fun i => i.elim0
    rw [hTe]
    obtain ⟨h1, h2⟩ := hCE R₀ hR₀
    refine ⟨h1, h2.trans ?_⟩
    have hpos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
    have hlog : 0 ≤ Real.log R₀ := by
      have h := Real.log_le_log (Real.exp_pos 1) hR₀
      rw [Real.log_exp] at h
      linarith
    have hk : 0 ≤ Real.log R₀ ^ (0 + 1) := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hk) hpos.le
  · letI : MeasurableSpace X := borel X
    haveI : BorelSpace X := ⟨rfl⟩
    obtain ⟨C, hC⟩ := tb A Θ L s m W hΘ hΘp hL hS hsnc hle
    obtain ⟨hbm, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
    have hCp : 0 ≤ max C 0 * (C₁ + 3) :=
      mul_nonneg (le_max_right _ _) (by linarith)
    refine ⟨max C 0 * (C₁ + 3), hCp, fun u T hu hpsh hb hT => ?_⟩
    refine tailLogBound_of_phi_eq A _ _ (Φ := fun i => Θ i + LocPot.ofFun (u i))
      (fun i => funext fun x => funext fun y => (hT i x y).symm) _ ?_
    intro R₀ hR₀
    have hΦ : ∀ i, IsPotential A (Θ i + LocPot.ofFun (u i)) := fun i =>
      isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hu i))
    obtain ⟨hfin, hint⟩ := maMeasure_thm A (fun i => Θ i + LocPot.ofFun (u i)) hΦ hpsh
    have hpos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
    have hlog1 : 1 ≤ Real.log R₀ := by
      have h := Real.log_le_log (Real.exp_pos 1) hR₀
      rwa [Real.log_exp] at h
    have hSm : MeasurableSet (tail (bdry s)ᶜ (rW L s) R₀) :=
      hbm.compl.inter (measurableSet_le measurable_const hrm)
    have hgm : Measurable ((tail (bdry s)ᶜ (rW L s) R₀).indicator fun x => Real.log (rW L s x)) :=
      (Real.measurable_log.comp hrm).indicator hSm
    have hg0 : ∀ x, 0 ≤ (tail (bdry s)ᶜ (rW L s) R₀).indicator
        (fun x => Real.log (rW L s x)) x := by
      intro x
      refine Set.indicator_apply_nonneg fun hx => Real.log_nonneg ?_
      have h1 : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      exact h1.trans (hR₀.trans hx.2)
    have hlin : ∫⁻ x, ENNReal.ofReal ((tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => Real.log (rW L s x)) x) ∂maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) =
        ∫⁻ y in (bdry s)ᶜ ∩ {y | R₀ ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y))
          ∂maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) := by
      have hfun : (fun x => ENNReal.ofReal ((tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => Real.log (rW L s x)) x)) = (tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => ENNReal.ofReal (Real.log (rW L s x))) := by
        funext x
        by_cases hx : x ∈ tail (bdry s)ᶜ (rW L s) R₀
        · simp only [Set.indicator_of_mem hx]
        · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
      rw [hfun, lintegral_indicator hSm]
      rfl
    have hK : 0 ≤ max C 0 * (C₁ + 3) * Real.log R₀ ^ 2 / R₀ := by
      have : 0 ≤ Real.log R₀ ^ 2 := by positivity
      exact div_nonneg (mul_nonneg hCp this) hpos.le
    have hle1 : ∫⁻ x, ENNReal.ofReal ((tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => Real.log (rW L s x)) x) ∂maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) ≤
        ENNReal.ofReal (max C 0 * (C₁ + 3) * Real.log R₀ ^ 2 / R₀) := by
      rw [hlin]
      refine (hC C₁ u hC₁ hu hpsh hb R₀ hR₀).2.trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : 0 ≤ Real.log R₀ ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ C₁ + 3 := by linarith
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) h3) h2) hpos.le
    have hI : Integrable ((tail (bdry s)ᶜ (rW L s) R₀).indicator fun x => Real.log (rW L s x))
        (maMeasure A (fun i => Θ i + LocPot.ofFun (u i))) :=
      ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall hg0)).2 (hle1.trans_lt ENNReal.ofReal_lt_top)⟩
    have hMI := ((hint _ hgm).1).2 hI
    refine ⟨hMI, ?_⟩
    rw [(hint _ hgm).2 hMI, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hg0) hgm.aestronglyMeasurable]
    refine (ENNReal.toReal_le_of_le_ofReal hK hle1).trans ?_
    have hpow : Real.log R₀ ^ 2 ≤ Real.log R₀ ^ (e + 1) :=
      pow_le_pow_right₀ hlog1 (by omega)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCp) hpos.le

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open GroundTheory.Heights₂.Heights (chartLift chartLiftDom contDiff_chartLift chartLift_blockNonzero segre_chartLift
  chartWeight_of_coord)

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

theorem eval_chartSection (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRingOver ℂ ι)
    (x : Fin m → ℂ) : MvPolynomial.eval x (chartSection σ i s) = MvPolynomial.eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add p q hp hq =>
    have : chartSection σ i (p + q) = chartSection σ i p + chartSection σ i q := by
      simp [chartSection]
    rw [this, map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p q hp =>
    have : chartSection σ i (p * X q) =
        chartSection σ i p * X (σ.symm (Function.update i q.1 q.2)) := by
      simp [chartSection]
    rw [this, map_mul, map_mul, hp]
    simp [chartLift]

theorem mem_closedBall_of_lift_mem_domCell {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {x : Fin m → ℂ} (hx : x ∈ chartSet S σ i) (hd : chartLift σ i x ∈ domCell i) :
    x ∈ Metric.closedBall (0 : Fin m → ℂ) 1 := by
  obtain ⟨z, -, hzi, rfl⟩ := hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro a
  have h := hd (σ a)
  rw [segre_chartLift σ i z hzi, hzi, norm_one] at h
  exact h

theorem abs_log_div_le {t h c : ℝ} (ht : 0 ≤ t) (hh : 0 < h) (hc : |Real.log h| ≤ c) (hc0 : 0 ≤ c) :
    |Real.log (t / h)| ≤ |Real.log t| + c := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hc0
  · rw [Real.log_div ht.ne' hh.ne']
    exact (abs_sub _ _).trans (by gcongr)

end

theorem integrable_chartAbsDens_cellWeight : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  intro K _ _ ι _ Q e m σ i Ψ N A s a J hA _ _ hmeas hzero hJ hproj hint
  classical
  set T : Set (Fin m → ℂ) := Metric.closedBall 0 1 ∩ {x | x (σ.symm i) = 1} with hT
  have hTc : IsCompact T :=
    (isCompact_closedBall (0 : Fin m → ℂ) 1).inter_right
      (isClosed_eq (continuous_apply _) continuous_const)
  have hcont : ContinuousOn (fun x => Real.log (A.h (chartLift σ i x))) T := by
    have h1 : ContinuousOn (fun x => A.h (chartLift σ i x)) T :=
      hA.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn
        fun x hx => chartLift_blockNonzero σ i hx.2
    exact h1.log fun x hx => (A.pos _ (chartLift_blockNonzero σ i hx.2)).ne'
  obtain ⟨C, hC⟩ := hTc.exists_bound_of_continuousOn hcont
  have hchart : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J, x ∈ chartSet (conePts Q) σ i := by
    intro x hx
    rw [← hzero]
    intro q hq
    exact hx q ((mem_chartComponents.1 hJ).1.2 hq)
  have hcoord : ∀ x ∈ chartSet (conePts Q) σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hmeasW : Measurable (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) := by
    unfold chartWeight
    exact (hmeas.comp (contDiff_chartLift σ i (n := 0)).continuous.measurable).piecewise
      (GroundTheory.Heights₂.Heights.isOpen_chartLiftDom σ i).measurableSet measurable_const
  have hmeasD : Measurable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) :=
    GroundTheory.Heights₂.Heights.SheetSumMeasurable.measurable_sheetSum hproj (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) hmeasW _
  refine (hint 1 (max C 0)).mono' hmeasD.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (GroundTheory.Heights₂.Heights.chartAbsDens_nonneg _ _ _ _ _)]
  have key : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J,
      |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x| ≤
        |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
          (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x| := by
    intro x hx
    have hxc := hchart x hx
    have h1 := hcoord x hxc
    rw [chartWeight_of_coord _ h1]
    by_cases hd : chartLift σ i x ∈ domCell i
    · have hb := mem_closedBall_of_lift_mem_domCell hxc hd
      have hC' : |Real.log (A.h (chartLift σ i x))| ≤ max C 0 :=
        (hC x ⟨hb, h1⟩).trans (le_max_left _ _)
      have hnz := chartLift_blockNonzero σ i h1
      have habs : absLogNorm A s (chartLift σ i x) = |logNormC A s (chartLift σ i x)| := by
        simp only [absLogNorm]
        rw [if_pos hnz]
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem hb, habs, abs_abs, logNormC,
        ← eval_chartSection]
      exact (abs_log_div_le (norm_nonneg _) (A.pos _ hnz) hC' (le_max_right _ _)).trans
        (le_abs_self _)
    · rw [Set.indicator_of_notMem hd, abs_zero]
      exact abs_nonneg _
  have h := GroundTheory.Heights₂.Heights.sheetSum_le_mul (J := J) (A := chartProjMatrix σ Ψ) (y := y)
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hproj y) 1
    (fun x t => |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x t => |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
      (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x hx t _ => by
      rw [one_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (key x hx.1) (abs_nonneg _))
  exact h.trans_eq (one_mul _)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.PshBack

theorem smoothOn_isPshOn_chartBack : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (x₀ : X) (j : Fin B.n) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → ℝ),
    A.Compatible B → IsPotential A th → (B.chart j).source ⊆ th.U x₀ → IsOpen V →
    V ⊆ (B.chart j).target → ContDiffOn ℝ ∞ g V →
    (∀ z ∈ V, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z' => th.φ x₀ ((B.chart j).symm z') + g z') z w) →
    A.SmoothOn ((B.chart j).source ∩ B.chart j ⁻¹' V) (g ∘ B.chart j) ∧
      IsPshOn A ((B.chart j).source ∩ B.chart j ⁻¹' V) (th + LocPot.ofFun (g ∘ B.chart j)) := by
  intro e X _ A B th x₀ j V g hAB hth hsrc hV hVt hg hlevi
  have hτ : ∀ (k : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart k).target →
      (A.chart k).symm y ∈ (B.chart j).source →
      AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := fun k y hy hp => hAB.1 k j y ⟨hy, hp⟩
  refine ⟨fun k y hy => ?_, fun x k y hy w => ?_⟩
  · obtain ⟨hyt, hp, hpV⟩ := hy
    have h1 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hpV)
    have h2 : ContDiffAt ℝ ∞ (B.chart j ∘ (A.chart k).symm) y :=
      ((hτ k y hyt hp).contDiffAt (n := ∞)).restrict_scalars ℝ
    exact (h1.comp y h2).contDiffWithinAt
  · obtain ⟨hyt, ⟨hpx, -⟩, hp, hpV⟩ := hy
    have hτy : AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := hτ k y hyt hp
    obtain ⟨W, hW, hpW, G, hG, hGe⟩ := hth.2 x x₀ ((A.chart k).symm y) ⟨hpx, hsrc hp⟩
    have hGa : AnalyticAt ℂ (G ∘ (A.chart k).symm) y := hG k y ⟨hyt, hpW⟩
    let h : (Fin e → ℂ) → ℝ := fun z' => th.φ x₀ ((B.chart j).symm z') + g z'
    have hB : B.SmoothOn (th.U x₀) (th.φ x₀) :=
      smoothOn_of_compatible hAB (th.isOpen_U x₀) (hth.1 x₀)
    have hτyV : (B.chart j ∘ (A.chart k).symm) y ∈ V := hpV
    have hh : ContDiffAt ℝ 2 h ((B.chart j ∘ (A.chart k).symm) y) := by
      have hmem : (B.chart j ∘ (A.chart k).symm) y ∈
          (B.chart j).target ∩ (B.chart j).symm ⁻¹' th.U x₀ := by
        refine ⟨hVt hτyV, ?_⟩
        show (B.chart j).symm (B.chart j ((A.chart k).symm y)) ∈ th.U x₀
        rw [(B.chart j).left_inv hp]
        exact hsrc hp
      have h1 : ContDiffAt ℝ ∞ (th.φ x₀ ∘ (B.chart j).symm) ((B.chart j ∘ (A.chart k).symm) y) :=
        (hB j).contDiffAt
          (((B.chart j).isOpen_inter_preimage_symm (th.isOpen_U x₀)).mem_nhds hmem)
      have h2 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hτyV)
      exact (h1.add h2).of_le (by norm_cast)
    have hhτ : ContDiffAt ℝ 2 (h ∘ (B.chart j ∘ (A.chart k).symm)) y :=
      hh.comp y ((hτy.contDiffAt).restrict_scalars ℝ)
    have hGre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart k).symm) y').re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y ((hGa.contDiffAt).restrict_scalars ℝ)
    have hopen : IsOpen ((A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source)) :=
      (A.chart k).isOpen_inter_preimage_symm
        (((hW.inter (th.isOpen_U x)).inter (th.isOpen_U x₀)).inter (B.chart j).open_source)
    have hymem : y ∈ (A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source) :=
      ⟨hyt, ⟨⟨hpW, hpx⟩, hsrc hp⟩, hp⟩
    have hev : ((th + LocPot.ofFun (g ∘ B.chart j)).φ x ∘ (A.chart k).symm) =ᶠ[𝓝 y]
        (fun y' => (h ∘ (B.chart j ∘ (A.chart k).symm)) y' +
          1 * ((G ∘ (A.chart k).symm) y').re) := by
      filter_upwards [hopen.mem_nhds hymem] with y' hy'
      obtain ⟨-, ⟨⟨hW', hx'⟩, hx0'⟩, hs'⟩ := hy'
      have hd := hGe _ ⟨⟨hW', hx'⟩, hx0'⟩
      change th.φ x ((A.chart k).symm y') + g (B.chart j ((A.chart k).symm y')) =
        th.φ x₀ ((B.chart j).symm (B.chart j ((A.chart k).symm y'))) +
          g (B.chart j ((A.chart k).symm y')) + 1 * (G ((A.chart k).symm y')).re
      rw [(B.chart j).left_inv hs']
      linarith
    have e1 := levi_add_smul (f := h ∘ (B.chart j ∘ (A.chart k).symm))
      (g := fun y' => ((G ∘ (A.chart k).symm) y').re) (z := y) 1 hhτ hGre w
    rw [levi_congr hev w, e1, levi_re_analytic hGa w, levi_comp w hτy hh]
    have := hlevi _ hτyV (fderiv ℂ (B.chart j ∘ (A.chart k).symm) y w)
    simp only [mul_zero, add_zero]
    exact this

end GlobalTheory.CompanionTheory.Metric.PshBack
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem locDens_add_ofFun_continuousOn : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ContinuousOn (locDens A (fun i => P i + LocPot.ofFun (f i) + Θ) j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := by
  intro e X _ A U P f Θ hU hP hΘ hf j
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hm : Continuous (mdisc : (Fin e → Matrix (Fin e) (Fin e) ℂ) → ℂ) := by
    unfold mdisc; fun_prop
  have hf2 : ∀ k, ContDiffOn ℝ 2 (f k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := fun k =>
    (hf k j).of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ContinuousOn (fun y => fun k =>
      (hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
        hessC (f k ∘ (A.chart j).symm) y +
        hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y :
          Matrix (Fin e) (Fin e) ℂ))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    continuousOn_pi.2 fun k =>
      (((hessC_base_continuousOn A (P k) (hP k) j).mono Set.inter_subset_left).add
        (hessC_continuousOn _ _ hVo (hf2 k))).add
        ((hessC_base_continuousOn A Θ hΘ j).mono Set.inter_subset_left)
  have hc := (continuousOn_const (c := (e.factorial : ℝ) * (2 / Real.pi) ^ e)
    (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U)).mul
    (Complex.continuous_re.comp_continuousOn (hm.comp_continuousOn hH))
  refine hc.congr fun y hy => ?_
  unfold locDens maDens
  simp only [Function.comp_apply, Pi.mul_apply]
  congr 3
  funext k
  have hP' := potential_contDiffAt A (P k) (hP k) j hy.1
  have hΘ' := potential_contDiffAt A Θ hΘ j hy.1
  have hf' : ContDiffAt ℝ 2 (f k ∘ (A.chart j).symm) y :=
    (hf2 k).contDiffAt (hVo.mem_nhds hy)
  rw [show (fun y' => (P k + LocPot.ofFun (f k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
    fun y' => ((fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y' +
      (f k ∘ (A.chart j).symm) y') + (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y'
    from rfl]
  rw [hessC_add' _ _ _ (hP'.add hf') hΘ', hessC_add' _ _ _ hP' hf']

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.AtlasSmooth

theorem continuous_of_atlas_smooth :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (f : X → ℝ),
      A.Smooth f → Continuous f :=
  fun _ _ _ A _ hf => ReciprocityTheory.AnForm.M.st_smooth_continuous A hf

end GlobalTheory.CompanionTheory.Ar.AtlasSmooth
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.points_integral_zero_of_locally_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e), (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.intersection_number_metric_change : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (A B : HermLine J), IsFullIntersectionSystem II → IsArithVar P (n + 1) → IsSmoothHerm A → IsSmoothHerm B → B.a = A.a → II K J P (n + 1) (fun _ => B) = II K J P (n + 1) (fun _ => A) - ∑ i ∈ Finset.range (n + 1), ptsIntegral P (pot fun j : Fin n => if (j : ℕ) < i then B else A) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tele.telescope | exact GlobalTheory.CompanionTheory.Ar.Tele.telescope | (intros; apply GlobalTheory.CompanionTheory.Ar.Tele.telescope <;> assumption)
end
