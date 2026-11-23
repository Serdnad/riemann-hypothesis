module

public import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle027
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCGradAtlas
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Bdry

theorem bdry_isClosed_dense_compl (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hs : IsSection A L s) (hn : IsSNC A L s m W) : IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  have key := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hn
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨ψ, -, hyψ, S, hS⟩ := key y
    have hopen : IsOpen (ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0}) := by
      apply ψ.continuousOn.isOpen_inter_preimage ψ.open_source
      have : {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z : Fin e → ℂ | z i ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_biInter_finset fun i _ =>
        isOpen_ne_fun (continuous_apply i) continuous_const
    have hmem : y ∈ ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} := by
      refine ⟨hyψ, fun i hi h0 => hy ((hS y hyψ).2 ⟨i, hi, h0⟩)⟩
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
    rintro y' ⟨h1, h2⟩ hb
    obtain ⟨i, hi, h0⟩ := (hS y' h1).1 hb
    exact h2 i hi h0
  · rw [dense_iff_inter_open]
    intro V hV ⟨x, hx⟩
    obtain ⟨ψ, -, hxψ, S, hS⟩ := key x
    have hsub : V ∩ ψ.source ⊆ ψ.source := Set.inter_subset_right
    have himg : IsOpen (ψ '' (V ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source (hV.inter ψ.open_source) hsub
    have hne : (ψ '' (V ∩ ψ.source)).Nonempty := ⟨ψ x, x, ⟨hx, hxψ⟩, rfl⟩
    obtain ⟨z, hz, hz0⟩ := (GlobalTheory.T.dense_coordinate_torus e).inter_open_nonempty _ himg hne
    obtain ⟨y, ⟨hyV, hyψ⟩, rfl⟩ := hz
    refine ⟨y, hyV, fun hb => ?_⟩
    obtain ⟨i, -, h0⟩ := (hS y hyψ).1 hb
    exact hz0 i h0

end GlobalTheory.CompanionTheory.Ar.Bdry
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.singular_weight_monotone_regularization : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧ (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) → IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th → IsRegFamily A Θ L s th ph phT C' t₀') ∧ ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) → ∃ C₀, IsSingWeight A L s th u C₀ ∧ IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧ IsRegFamilyC2 A s u (fun _ => u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | exact GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.regular_family_eventually_smooth_psh : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsRegFamily A Θ L s th ph phT C t₀ → ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot | exact GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.EvPsh.eventually_isPsh_add_pot <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.zero_weight_regular_family : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (C₅ C t₁ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₅ → 0 ≤ C → 0 < t₁ → t₁ ≤ Real.exp (-Real.exp 1) → IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧ IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.zeroMember_isRegFamily | exact GlobalTheory.CompanionTheory.Ar.Giv.zeroMember_isRegFamily | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.zeroMember_isRegFamily <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.isClosed_section_boundary : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | exact GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.snc_adapted_chart_section_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ (x : X) (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ → Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target → φ.source ⊆ L.U x → (∀ i ∈ S, 1 ≤ μ i) → A.HoloOn φ.source v → (∀ y ∈ φ.source, v y ≠ 0) → (∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i) → (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧ ∃ M : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s → |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.LocalModel.zero_set_and_bound | exact GlobalTheory.CompanionTheory.Ar.PB.LocalModel.zero_set_and_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.LocalModel.zero_set_and_bound <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.epsilon_schedule_properties : (∀ a b : ℝ, Real.exp 1 ≤ a → a ≤ b → Real.log b / b ≤ Real.log a / a) ∧ (∀ C t t' : ℝ, 0 ≤ C → 0 < t → t ≤ t' → t' ≤ Real.exp (-Real.exp 1) → epsT C t ≤ epsT C t') ∧ (∀ C t : ℝ, 1 ≤ C → 0 < t → t ≤ Real.exp (-Real.exp 1) → t ≤ epsT C t) ∧ (∀ C : ℝ, Tendsto (epsT C) (𝓝[>] 0) (𝓝 0)) ∧ (∀ C : ℝ, ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1) ∧ (∀ (n : ℕ) (a : Fin n → ℝ), (∀ j, 0 < a j) → ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics | exact GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gradBound_of_local_bounds : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → ∀ ph : X → ℝ, A.SmoothOn (bdry s)ᶜ ph → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ), IsCompatChart A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry s → ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) → ∃ C₅, ∀ C, C₅ ≤ C → IsGradBound B L s ph C :=
  @PositivityTheory.Xgp.t_c_grad_atlas

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.RegFin

theorem isPsh_of_posPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw; rw [levi_zero]
  · exact (h x j y hy w hw).le

theorem quot_mem_unit {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) ∧
      Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤ 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  have hl : 0 < Real.log (1 / t) := lt_of_lt_of_le (Real.exp_pos 1) h1
  refine ⟨div_nonneg (by linarith) hl.le, ?_⟩
  rw [div_le_one hl]
  have := Real.log_le_sub_one_of_pos hl
  linarith

theorem quot_mono {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') (hte : t' ≤ Real.exp (-Real.exp 1)) :
    Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤
      Real.log (Real.log (1 / t')) / Real.log (1 / t') := by
  have ht' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht' hte).1
  have hle : Real.log (1 / t') ≤ Real.log (1 / t) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le ht htt)
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (h1.trans hle)) hle

theorem isRegFamily_of_glue : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (Θ L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ K Cl t₀ : ℝ) (f : ℝ → Fin B.n → X → ℝ) (F : ℝ → X → ℝ), IsPotential A Θ → IsPosPot A Θ → IsPotential A th → (∀ y, logNormSec L s y ≤ 0) → (∀ y, ∃ j, y ∈ chartBall B j 1) → (∀ y ∉ bdry s, -C₅ * Real.log (rW L s y) ≤ ph y) → 0 < K → 1 ≤ Cl → 0 < t₀ → t₀ ≤ Real.exp (-Real.exp 1) → (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * epsT Cl t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * epsT Cl t) → (∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ f t j y ∧ (y ∉ bdry s → ph y ≤ f t j y ∧ (rW L s y ≤ Real.log (1 / t) → f t j y ≤ ph y + t ^ ((1 : ℝ) / 3)))) → (∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ f t' j y + epsT Cl t') → ∃ C : ℝ, IsRegFamily A Θ L s th ph F C t₀ := by
  intro e X _ A B Θ L th s ph C₅ K Cl t₀ f F hΘ hΘp hth hs hcov hph hK hCl ht₀ ht₀e hF hf hmono
  have hΘpsh := isPsh_of_posPot A Θ hΘp
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Cl * (1 + K) + |C₅| + 1 := ⟨_, rfl⟩
  have hC5 := abs_nonneg C₅
  have hClK : 0 ≤ Cl * K := by positivity
  have hC1 : 1 ≤ C := by nlinarith
  have hCK : Cl * (1 + K) ≤ C := by linarith
  have hCl' : Cl ≤ C := by nlinarith
  have hKCl : K * Cl ≤ C := by nlinarith
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpt : ∀ y, ∃ j, y ∈ chartBall B j (5 / 4) := fun y => by
    obtain ⟨j, hj⟩ := hcov y
    exact ⟨j, chartBall_mono B j (by norm_num) hj⟩
  have ht₀1 : t₀ < 1 :=
    lt_of_le_of_lt ht₀e (by
      have := Real.exp_lt_exp.2 (show -Real.exp 1 < 0 by linarith [Real.exp_pos 1])
      rwa [Real.exp_zero] at this)
  refine ⟨C, ht₀, ht₀1, fun t ht htt => ?_⟩
  have hte := htt.trans ht₀e
  obtain ⟨hl1, hll⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  obtain ⟨hg0, hg1⟩ := quot_mem_unit ht hte
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = Real.log (Real.log (1 / t)) / Real.log (1 / t) := ⟨_, rfl⟩
  rw [← hgdef] at hg0 hg1
  have hεC : epsT C t = C * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  have hεl : epsT Cl t = Cl * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  obtain ⟨hsm, hpsh, hFf⟩ := hF t ht htt
  have hKg : K * (Cl * g) ≤ K * Cl := by
    have := mul_le_mul_of_nonneg_left hg1 (by linarith : (0 : ℝ) ≤ Cl)
    nlinarith
  have hKg0 : 0 ≤ K * (Cl * g) := by positivity
  have hFC : ∀ y, F t y ≤ Cl * (1 + K) := fun y => by
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := (hf t ht htt j y hj).1
    rw [hεl] at h1
    nlinarith
  refine ⟨hsm, fun y => (hFC y).trans hCK, fun y hy => ?_, fun y => ?_, ?_,
    fun y hy hyr => ?_, fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · obtain ⟨j, hj⟩ := hpt y
    exact ((hf t ht htt j y hj).2.2 hy).1.trans (hFf j y hj).1
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).1
    have h2 := (hf t ht htt j y hj).2.1
    have : Cl * Real.log (Real.log (1 / t)) ≤ C * Real.log (Real.log (1 / t)) :=
      mul_le_mul_of_nonneg_right hCl' (by linarith)
    linarith
  · refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (F t) hΘ hΘpsh hth hsm ?_ hpsh
    rw [hεl, hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := ((hf t ht htt j y hj).2.2 hy).2 hyr
    rw [hεl] at h1
    rw [hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have hfj := hf t ht htt j y hj
    rw [hεl] at h1
    rw [hεC]
    have hry := hr y
    have hrpos : 0 < rW L s y := by linarith
    have ht3 : 0 ≤ t ^ ((1 : ℝ) / 3) := by positivity
    have hCg0 : 0 ≤ C * g := by positivity
    by_cases hyr : rW L s y ≤ Real.log (1 / t)
    · have h2 := (hfj.2.2 hy).2 hyr
      have h3 : C * g ≤ C * g * rW L s y := le_mul_of_one_le_right hCg0 (by linarith)
      have := mul_le_mul_of_nonneg_right hKCl hg0
      nlinarith
    · push_neg at hyr
      have hlog : Real.log (rW L s y) / rW L s y ≤ g := by
        rw [hgdef]
        exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 hl1) (Set.mem_Ici.2 hry) hyr.le
      have hlog' : Real.log (rW L s y) ≤ g * rW L s y := by
        rw [div_le_iff₀ hrpos] at hlog
        linarith
      have hlpos : 0 < Real.log (1 / t) := by linarith [Real.exp_pos 1]
      have hgr : 1 ≤ g * rW L s y := by
        have e1 : g * rW L s y = Real.log (Real.log (1 / t)) * (rW L s y / Real.log (1 / t)) := by
          rw [hgdef]; ring
        have e2 : 1 ≤ rW L s y / Real.log (1 / t) := by
          rw [le_div_iff₀ hlpos]; linarith
        rw [e1]
        nlinarith
      have hlr0 : 0 ≤ Real.log (rW L s y) := Real.log_nonneg (by linarith)
      have hph1 := hph y hy
      have hph2 : -|C₅| * Real.log (rW L s y) ≤ -C₅ * Real.log (rW L s y) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₅]) hlr0
      have h4 : |C₅| * Real.log (rW L s y) ≤ |C₅| * (g * rW L s y) :=
        mul_le_mul_of_nonneg_left hlog' hC5
      have h5 : Cl * (1 + K) ≤ Cl * (1 + K) * (g * rW L s y) :=
        le_mul_of_one_le_right (by positivity) hgr
      have hCg : C * g * rW L s y = (Cl * (1 + K) + |C₅| + 1) * (g * rW L s y) := by
        rw [hCdef]; ring
      have := hFC y
      nlinarith
  · have ht'0 : 0 < t' := ht.trans_le htt'
    have hte' := ht'.trans ht₀e
    obtain ⟨hg0', hg1'⟩ := quot_mem_unit ht'0 hte'
    have hgm := quot_mono ht htt' hte'
    obtain ⟨g', hgdef'⟩ : ∃ g' : ℝ, g' = Real.log (Real.log (1 / t')) / Real.log (1 / t') :=
      ⟨_, rfl⟩
    rw [← hgdef'] at hg0' hg1'
    rw [← hgdef, ← hgdef'] at hgm
    have hεC' : epsT C t' = C * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    have hεl' : epsT Cl t' = Cl * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := hmono t t' ht htt' ht' j y hj
    have h3 := ((hF t' ht'0 ht').2.2 j y hj).1
    rw [hεl] at h1
    rw [hεl'] at h2
    rw [hεC']
    have h4 : K * (Cl * g) ≤ K * (Cl * g') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgm (by linarith)) hK.le
    have h5 : Cl * (1 + K) * g' ≤ C * g' := mul_le_mul_of_nonneg_right hCK hg0'
    have h6 : C * g' ≤ C * (C * g') := le_mul_of_one_le_left (by positivity) hC1
    linarith

end GlobalTheory.CompanionTheory.Ar.RegFin
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem exists_family_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  rintro ⟨II, hII, -⟩
  exact ⟨II, hII⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end
