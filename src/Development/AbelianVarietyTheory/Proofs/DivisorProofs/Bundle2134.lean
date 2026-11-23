module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle081
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem exists_shell_of_le_one {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    ∃ j : ℕ, Real.exp (-(j + 1 : ℝ)) < t ∧ t ≤ Real.exp (-(j : ℝ)) := by
  have hl : 0 ≤ -Real.log t := by
    have := Real.log_nonpos h0.le h1
    linarith
  refine ⟨⌊-Real.log t⌋₊, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (-Real.log t)
    rw [← Real.lt_log_iff_exp_lt h0]
    linarith
  · have := Nat.floor_le hl
    rw [← Real.log_le_iff_le_exp h0]
    linarith

theorem le_two_mul_one_sub_exp_neg {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ε ≤ 2 * (1 - Real.exp (-ε)) := by
  have h2 : ε + 1 ≤ Real.exp ε := Real.add_one_le_exp ε
  have h3 : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-ε) := Real.exp_pos _
  have h5 : Real.exp (-ε) * (ε + 1) ≤ 1 := by nlinarith
  by_contra hc
  push Not at hc
  nlinarith

theorem mul_lintegral_rpow_le_of_shell_bound :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (h : X → ℝ) (d : ℝ) (B : ℝ≥0∞), Measurable h → (∀ x, 0 < h x) → 0 < d → (∀ j : ℕ, μ {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (d * j))) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ ≤ 2 * B := by
  intro X _ μ h d B hm hpos hd hB ε hε0 hε1
  set S : ℕ → Set X := fun j =>
    {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} with hS
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_lt measurable_const hm).inter (measurableSet_le hm measurable_const)
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (-((d + ε) * j))) with hc
  have hpt : ∀ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0)
      ≤ ∑' j, (S j).indicator (fun _ => c j) x := by
    intro x
    split_ifs with hx
    · obtain ⟨j, hj⟩ := exists_shell_of_le_one (hpos x) hx
      refine le_trans ?_ (ENNReal.le_tsum j)
      have hxS : x ∈ S j := hj
      rw [Set.indicator_of_mem hxS]
      apply ENNReal.ofReal_le_ofReal
      calc h x ^ (d + ε) ≤ (Real.exp (-(j : ℝ))) ^ (d + ε) :=
            Real.rpow_le_rpow (hpos x).le hj.2 (by linarith)
        _ = Real.exp (-((d + ε) * j)) := by
            rw [← Real.exp_mul]; congr 1; ring
    · exact zero_le
  set r : ℝ := Real.exp (-ε) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; linarith
  have hint : ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ
      ≤ B * (1 - ENNReal.ofReal r)⁻¹ := by
    calc _ ≤ ∫⁻ x, ∑' j, (S j).indicator (fun _ => c j) x ∂μ := lintegral_mono hpt
      _ = ∑' j, ∫⁻ x, (S j).indicator (fun _ => c j) x ∂μ :=
          lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable
      _ ≤ ∑' j, B * (ENNReal.ofReal r) ^ j := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          rw [lintegral_indicator_const (hSm j)]
          calc c j * μ (S j) ≤ c j * (B * ENNReal.ofReal (Real.exp (d * j))) := by
                gcongr
                exact hB j
            _ = B * (c j * ENNReal.ofReal (Real.exp (d * j))) := by ring
            _ = B * (ENNReal.ofReal r) ^ j := by
                congr 1
                rw [hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_pow hr0.le,
                  hr, ← Real.exp_add, ← Real.exp_nat_mul]
                congr 2; ring
      _ = B * (1 - ENNReal.ofReal r)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hkey : ENNReal.ofReal ε * (1 - ENNReal.ofReal r)⁻¹ ≤ 2 := by
    have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := by
      rw [ENNReal.ofReal_sub _ hr0.le, ENNReal.ofReal_one]
    have hp : 0 < 1 - r := by linarith
    rw [e1, ← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul hε0.le,
      ← ENNReal.ofReal_ofNat 2]
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    exact le_two_mul_one_sub_exp_neg hε0 hε1
  calc _ ≤ ENNReal.ofReal ε * (B * (1 - ENNReal.ofReal r)⁻¹) := by gcongr
    _ = (ENNReal.ofReal ε * (1 - ENNReal.ofReal r)⁻¹) * B := by ring
    _ ≤ 2 * B := by gcongr

end GlobalTheory.ResLine
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine.RightUnfold

theorem isMulRightInvariant_of_lattice {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Λ : Subgroup G)
    [Countable Λ] (𝓑 : Set G) (h𝓑 : IsFundamentalDomain Λ 𝓑 ν) (hfin : ν 𝓑 ≠ ⊤) :
    ν.IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  haveI : (ν.map (· * x)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν x
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map (· * x)) ν
  set c := Measure.haarScalarFactor (ν.map (· * x)) ν
  have h𝓑' : IsFundamentalDomain Λ ((· * x) ⁻¹' 𝓑) ν := by
    refine h𝓑.preimage_of_equiv (quasiMeasurePreserving_mul_right ν x) (e := id)
      Function.bijective_id ?_
    intro g y
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ν ((· * x) ⁻¹' 𝓑) = ν 𝓑 := h𝓑'.measure_eq h𝓑
  have h0 : ν 𝓑 ≠ 0 := h𝓑.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map (· * x)) 𝓑 = ν ((· * x) ⁻¹' 𝓑) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x) 𝓑
  have h1 : (c : ENNReal) * ν 𝓑 = 1 * ν 𝓑 := by
    calc (c : ENNReal) * ν 𝓑 = (c • ν) 𝓑 := by simp [Measure.smul_apply]
      _ = (ν.map (· * x)) 𝓑 := by rw [hc]
      _ = 1 * ν 𝓑 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem unimodular_and_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) (Λ : Subgroup G) [Countable Λ] (𝓑 : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ 𝓑 ν → ν 𝓑 ≠ ⊤ → ν.IsMulRightInvariant ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ b in 𝓑, ∑' γ : Λ, f (b⁻¹ * γ) ∂ν := by
  intro G _ _ _ _ _ _ _ _ ν Λ _ 𝓑 hν h𝓑 hfin
  haveI hR := isMulRightInvariant_of_lattice ν Λ 𝓑 h𝓑 hfin
  haveI := isInvInvariant_of_right ν
  refine ⟨hR, fun f hf => ?_⟩
  rw [← lintegral_inv_eq_self f, h𝓑.lintegral_eq_tsum' (fun x => f x⁻¹), lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    refine lintegral_congr fun b => ?_
    simp [Subgroup.smul_def]
  · intro γ
    exact (hf.comp (measurable_inv.mul_const _)).aemeasurable

end GlobalTheory.ResLine.RightUnfold
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine

theorem setLIntegral_tsum_unfold (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) (Γ Λ : Subgroup G) [Countable Γ] (T : Set Γ) (𝓕 D : Set G)
    (hμ : μ.IsHaarMeasure) (hle : Λ ≤ Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hD : IsFundamentalDomain Λ D μ)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Λ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, ∑' t : T, f (t.1.1 * g) ∂μ = ∫⁻ g in D, f g ∂μ := by
  haveI : Countable Λ := (Subgroup.inclusion_injective hle).countable
  let e0 : T × Λ → Γ := fun p => Subgroup.inclusion hle p.2 * p.1.1
  have hbij : Function.Bijective e0 := by
    constructor
    · rintro ⟨⟨t, ht⟩, l⟩ ⟨⟨s, hs⟩, m⟩ h
      simp only [e0] at h
      have hts : t = s := by
        refine (hT (Subgroup.inclusion hle l * t)).unique ⟨ht, ?_⟩ ⟨hs, ?_⟩
        · simp
        · rw [h]; simp
      subst hts
      have := Subgroup.inclusion_injective hle (mul_right_cancel h)
      subst this
      rfl
    · intro γ
      obtain ⟨t, ⟨ht, hm⟩, -⟩ := hT γ
      refine ⟨(⟨t, ht⟩, ⟨_, hm⟩), ?_⟩
      apply Subtype.ext
      simp [e0]
  have h1 : ∀ t : T, ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ
      = ∑' l : Λ, ∫⁻ g in D ∩ (e0 (t, l)) • 𝓕, f g ∂μ := by
    intro t
    have h2 : ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ = ∫⁻ g in t.1 • 𝓕, f g ∂μ :=
      (measurePreserving_smul t.1 μ).setLIntegral_comp_emb (measurableEmbedding_const_smul t.1) f 𝓕
    rw [h2, hD.setLIntegral_eq_tsum' f]
    refine tsum_congr fun l => ?_
    have h3 : l • t.1 • 𝓕 = (e0 (t, l)) • 𝓕 := by
      simp only [e0, mul_smul]
      rfl
    rw [h3, Set.inter_comm]
    refine lintegral_congr fun x => ?_
    exact hinv _ (l⁻¹).2 x
  rw [lintegral_tsum (f := fun (t : T) g => f (t.1.1 * g)) (fun t : T => (hf.comp (measurable_const_mul t.1.1)).aemeasurable),
    hF.setLIntegral_eq_tsum f D, ← (Equiv.ofBijective e0 hbij).tsum_eq, ENNReal.tsum_prod']
  exact tsum_congr h1

end GlobalTheory.ResLine
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.chartBall_weightPotential_density_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x ∧ |phla X la (cpt X x z)| ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| ∧ |rhF X x z| ≤ (X.Ψ.card : ℝ) ∧ |Real.log (densF X x z)| ≤ (X.Ψ.card : ℝ) * r ∧ 0 < densF X x z := by
  first | exact @GlobalTheory.WeightSizes.chart_ball_sizes | exact GlobalTheory.WeightSizes.chart_ball_sizes | (intros; apply GlobalTheory.WeightSizes.chart_ball_sizes <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHPos

theorem smoothOfRelativeDimension_of_holUnif {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (u : HolUnif A L g) : SmoothOfRelativeDimension g A.hom := by
  obtain ⟨D, hD⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ A hA
  obtain ⟨c, hc⟩ := GlobalTheory.AlgChart.exists_mem_source (p := A.hom) (σ := RingHom.id ℂ) (D := D)
    (GlobalTheory.HolUnifSec.pt u 0)
  have h1 : D ≤ g := GlobalTheory.HolUnifSec.dim_le u c hc
  have h2 : g ≤ D := by
    have hi : Function.Injective (fderiv ℂ (c.e ∘ GlobalTheory.HolUnifSec.pt u) 0).toLinearMap := by
      rw [ContinuousLinearMap.coe_coe]
      exact GlobalTheory.HolUnifSec.injective_fderiv u c hc
    have := LinearMap.finrank_le_finrank_of_injective hi
    simpa using this
  obtain rfl : D = g := le_antisymm h1 h2
  exact hD

end GlobalTheory.AHPos

theorem GlobalTheory.AHPos.exists_lb_of_posDef : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ u.IsAH Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hpos hint
  obtain ⟨A', _, hA', hsm, L', u', χ', hL', hΛ, hAH'⟩ :=
    GlobalTheory.T.riemann_theorem_nonprincipal_polarised_torus g u₀.Λ Hm u₀.discrete u₀.full hHm hpos hint
  obtain ⟨f, -, hf⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A A' g hA hA'
    (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u₀) hsm L₀ L' u₀ u' LinearMap.id
    (fun x hx => (hΛ x).2 hx)
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A A' L₀ L' g g u₀ u' PUnit (fun _ => f)
    (fun _ => LinearMap.id) (fun _ => 1) (fun _ z => hf z)
  have hmem : ∀ l : u₁.Λ, (l : Fin g → ℂ) ∈ u'.Λ := fun l => (hΛ _).2 (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, fun l => χ' ⟨l.1, hmem l⟩, LB.isLB_linComb hL' _ _, hex, hHm, hpos,
    fun l => hAH'.2.2.1 _, ?_⟩
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U (j PUnit.unit) := by
    rw [← LinearMap.id_apply (R := ℂ) z, hf z]
    exact (CubeValues.le_preimage_wchart (u₀.ex z).left L' (fun _ => f.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = u'.fr (j PUnit.unit) z := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = u'.fr (j PUnit.unit) (z + l) := by simpa using hfr j (z + l)
  rw [e1, e2]
  exact hAH'.2.2.2 ⟨l.1, hmem l⟩ (j PUnit.unit) z hz'
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isIntegral_baseChange_rationalFunctionField_finiteVars : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → IsIntegral X' := by
  first | exact @GlobalTheory.PureTransc.isIntegral_of_isPullback | exact GlobalTheory.PureTransc.isIntegral_of_isPullback | (intros; apply GlobalTheory.PureTransc.isIntegral_of_isPullback <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibreGen

theorem exists_sec_of_closed {X : Scheme.{0}} [CompactSpace X] (M : LB X)
    (h : ∀ z : X, IsClosed ({z} : Set X) → ∃ s : LB.Sec M, z ∈ nonzeroLocus s) (z : X) :
    ∃ s : LB.Sec M, z ∈ nonzeroLocus s := by
  by_contra hz
  push_neg at hz
  let C : Set X := ⋂ s : LB.Sec M, ((nonzeroLocus s : X.Opens) : Set X)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s => (nonzeroLocus s).isOpen.isClosed_compl
  obtain ⟨w, hw, hcl⟩ := hC.exists_closed_singleton ⟨z, Set.mem_iInter.2 fun s => hz s⟩
  obtain ⟨s, hs⟩ := h w hcl
  exact Set.mem_iInter.1 hw s hs

theorem compactSpace_fibre {S : Scheme.{0}} (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) : CompactSpace (Over.mk t ⊗ P.A).left := by
  have := P.isAb.proper
  have : QuasiCompact (pullback.fst t P.A.hom) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst t P.A.hom)

theorem exists_sec_algClosed {S : Scheme.{0}} (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (z : (Over.mk t ⊗ P.A).left) :
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), z ∈ nonzeroLocus s := by
  have := compactSpace_fibre P K t
  refine exists_sec_of_closed _ (fun z hz => ?_) z
  have := P.isAb.smooth
  have : LocallyOfFiniteType (fst (Over.mk t) P.A).left :=
    (inferInstance : LocallyOfFiniteType (pullback.fst t P.A.hom))
  let f := (fst (Over.mk t) P.A).left
  let p₀ := pointOfClosedPoint f z hz
  have hw : p₀ ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t).hom := by
    rw [← Over.w (fst (Over.mk t) P.A), ← Category.assoc, pointOfClosedPoint_comp]
    exact Category.id_comp _
  let q : Over.mk t ⟶ Over.mk t ⊗ P.A := Over.homMk p₀ hw
  have hq : q ≫ fst (Over.mk t) P.A = 𝟙 _ := by
    ext1
    exact pointOfClosedPoint_comp f z hz
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint S P K t c (q ≫ snd _ _) (IsLocalRing.closedPoint _)
  refine ⟨s, ?_⟩
  have e : lift (𝟙 (Over.mk t)) (q ≫ snd (Over.mk t) P.A) = q := by
    rw [← hq, lift_comp_fst_snd]
  rw [e] at hs
  have h2 : q.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply f z hz _
  rw [← h2]
  exact hs

theorem exists_sec_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k]
    (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left),
    ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  intro S P k _ t c y
  exact GlobalTheory.T.nonvanishing_twistedSections_descend_fieldExtension S P k (AlgebraicClosure k) t c (fun z => exists_sec_algClosed P _ _ _ z) y

end GlobalTheory.TwistFibreGen
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FibreUnifComb

theorem exists_unif_isDiff_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ₀ : c.F →+* ℂ) (U : Unf Xo c σ₀ r), 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (w : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W) (ρ : E →+* ℂ) (z : FrPt Xo c (CAt σ₀)), z.x = (U.un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt σ₀), (∀ i, IsCombAt (U.un k w).x ((U.un k w).u ρ) (C i) (z.u ρ i)) → ∃ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x) (u' : HolUnif T.pol.A T.pol.L W.g) (χ' : u'.Λ → ℂ), u'.IsAH Wu.Hm χ' ∧ ∀ i, ∃ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i ∧ u'.IsDiff (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) w' := by
  intro E _ _ _ H Dw l Xo c r σ₀ U hpq k x W Wu ρ z hz C hC
  rcases z with ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩
  dsimp only at hz ztan hC ⊢
  subst hz
  obtain ⟨Φ₀⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : GlobalTheory.LamT.FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, -, hA, -, -, -, hD⟩ := GlobalTheory.OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos
    Wu.c2 Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  refine ⟨Φ.T, Φ.m, u, χ, hA, fun i => ?_⟩
  have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per (Dw.mult ρ)
    ((U.un k x).u ρ) (fun l => Pi.single (W.e.symm ⟨ρ, l⟩) 1) (W.der ρ) (fun l => toC (C i l)) (zu ρ i)).1
    (by rw [← W.pt]; exact hC i)
  exact hD _ _ (ztan ρ i) hd

end GlobalTheory.FibreUnifComb
end
