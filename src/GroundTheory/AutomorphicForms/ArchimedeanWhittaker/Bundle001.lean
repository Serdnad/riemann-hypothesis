module

public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ContinuousMultilinearOfFiniteDimensional
public import GroundTheory.AutomorphicForms.GKModules.Garding
public import GroundTheory.AutomorphicForms.Bundle004
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.FiltrationCocycleLiftCriterion
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

section

namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped ContDiff InnerProductSpace

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)

theorem hasDerivAt_orbit_smul {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) (t : ℝ) :
    HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v) (π (h.expG (t • X)) (h.derivOp π X v)) t := by
  have h0 := h.hasDerivAt_derivOp π hv X
  have h0' : HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v) (h.derivOp π X v) (t - t) := by
    rw [sub_self]; exact h0
  have h1 : HasDerivAt (fun s : ℝ => π (h.expG ((s - t) • X)) v) (h.derivOp π X v) t :=
    h0'.comp_sub_const t t
  have h2 := ((π (h.expG (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [← BanachRep.map_mul_apply, ← h.expG_add_smul, add_sub_cancel]

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem derivOp_integral (hπ : ∀ g, ‖π g‖ ≤ 1) {f : G → ℂ} (hf : h.IsTestFunction f)
    {u : G → E} (hu : Continuous u) (hus : ∀ g, h.IsSmoothVector π (u g)) (X : 𝔤)
    (hdu : Continuous fun g => h.derivOp π X (u g))
    (hz : h.IsSmoothVector π (∫ g, f g • u g ∂μ)) :
    h.derivOp π X (∫ g, f g • u g ∂μ) = ∫ g, f g • h.derivOp π X (u g) ∂μ := by
  have := secondCountableTopology_subgroup_units G
  have hfc := hf.continuous h
  have hint : Integrable (fun g => f g • u g) μ :=
    (hfc.smul hu).integrable_of_hasCompactSupport hf.2.smul_right
  set F : ℝ → G → E := fun t g => f g • π (h.expG (t • X)) (u g) with hF
  set F' : ℝ → G → E := fun t g => f g • π (h.expG (t • X)) (h.derivOp π X (u g)) with hF'
  have hcontF : ∀ t, Continuous (F t) := fun t =>
    hfc.smul ((π (h.expG (t • X))).continuous.comp hu)
  have hcontF' : ∀ t, Continuous (F' t) := fun t =>
    hfc.smul ((π (h.expG (t • X))).continuous.comp hdu)
  have hbound_int : Integrable (fun g => ‖f g‖ * ‖h.derivOp π X (u g)‖) μ :=
    ((continuous_norm.comp hfc).mul (continuous_norm.comp hdu)).integrable_of_hasCompactSupport
      (hf.2.norm.mul_right)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (x₀ := 0)
    (bound := fun g => ‖f g‖ * ‖h.derivOp π X (u g)‖) (univ_mem)
    (Eventually.of_forall fun t => (hcontF t).aestronglyMeasurable)
    ((hcontF 0).integrable_of_hasCompactSupport (by
      simp only [hF]; exact hf.2.smul_right))
    (F' := F') (hcontF' 0).aestronglyMeasurable
    (Eventually.of_forall fun g t _ => by
      simp only [hF', norm_smul]
      gcongr
      calc ‖π (h.expG (t • X)) (h.derivOp π X (u g))‖
          ≤ ‖π (h.expG (t • X))‖ * ‖h.derivOp π X (u g)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖h.derivOp π X (u g)‖ := by gcongr; exact hπ _
        _ = _ := one_mul _) hbound_int
    (Eventually.of_forall fun g t _ => (h.hasDerivAt_orbit_smul π (hus g) X t).const_smul (f g))
  have e1 : (fun t : ℝ => ∫ g, F t g ∂μ) = fun t => π (h.expG (t • X)) (∫ g, f g • u g ∂μ) := by
    funext t
    rw [← (π (h.expG (t • X))).integral_comp_comm hint]
    simp [hF]
  have e2 : (∫ g, F' 0 g ∂μ) = ∫ g, f g • h.derivOp π X (u g) ∂μ := by
    simp [hF']
  rw [e1, e2] at key
  exact (h.hasDerivAt_derivOp π hz X).unique key.2

theorem wordOp_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) {w : E} (hw : h.IsSmoothVector π w)
    {f : G → ℂ} (hf : h.IsTestFunction f) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤),
      h.wordOp π Y (π.integrated μ f w) = ∫ g, f g • h.wordOp π Y (π g w) ∂μ := by
  intro k
  induction k with
  | zero =>
    intro Y
    rfl
  | succ k ih =>
    intro Y
    rw [wordOp_succ, ih (Fin.tail Y)]
    have hus : ∀ g, h.IsSmoothVector π (h.wordOp π (Fin.tail Y) (π g w)) := fun g =>
      h.isSmoothVector_wordOp π (h.isSmoothVector_map π hw g) _
    have hz : h.IsSmoothVector π (∫ g, f g • h.wordOp π (Fin.tail Y) (π g w) ∂μ) := by
      rw [← ih (Fin.tail Y)]
      exact h.isSmoothVector_wordOp π (h.isSmoothVector_integrated π μ hf w) _
    simpa only [wordOp_succ] using
      h.derivOp_integral π μ hπ hf (h.continuous_wordOp_map π hπ hw (Fin.tail Y)) hus (Y 0)
        (by simpa only [wordOp_succ] using h.continuous_wordOp_map π hπ hw Y) hz

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped ContDiff InnerProductSpace

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem norm_integrated_le (hπ : ∀ g, ‖π g‖ ≤ 1) {f : G → ℂ} (hf : h.IsTestFunction f) (x : E) :
    ‖π.integrated μ f x‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖x‖ := by
  have := secondCountableTopology_subgroup_units G
  rw [BanachRep.integrated]
  calc ‖∫ g, f g • π g x ∂μ‖ ≤ ∫ g, ‖f g • π g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ g, ‖f g‖ * ‖x‖ ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (((hf.continuous h).norm.mul continuous_const).integrable_of_hasCompactSupport
            hf.2.norm.mul_right) (Eventually.of_forall fun g => ?_)
        show ‖f g • π g x‖ ≤ ‖f g‖ * ‖x‖
        rw [norm_smul]
        gcongr
        calc ‖π g x‖ ≤ ‖π g‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖x‖ := by gcongr; exact hπ _
          _ = ‖x‖ := one_mul _
    _ = (∫ g, ‖f g‖ ∂μ) * ‖x‖ := integral_mul_const _ _

end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped ContDiff InnerProductSpace Manifold

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)

theorem integrated_add [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ] {f : G → ℂ} (hf : h.IsTestFunction f) (x y : E) :
    π.integrated μ f (x + y) = π.integrated μ f x + π.integrated μ f y := by
  have := secondCountableTopology_subgroup_units G
  have hi : ∀ z : E, Integrable (fun g => f g • π g z) μ := fun z =>
    ((hf.continuous h).smul (π.continuous_orbit z)).integrable_of_hasCompactSupport hf.2.smul_right
  simp only [BanachRep.integrated, map_add (f := _), smul_add]
  exact integral_add (hi x) (hi y)

theorem integrated_smul [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    (f : G → ℂ) (c : ℂ) (x : E) :
    π.integrated μ f (c • x) = c • π.integrated μ f x := by
  simp only [BanachRep.integrated, map_smul, smul_comm _ c]
  exact integral_smul c _

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

section

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral
open scoped Matrix.Norms.L2Operator Real InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

theorem continuous_kMat : Continuous kMat := by
  have : kMat = fun θ : ℝ => hGL2.expG (θ • lW) := funext fun θ => (expG_lW θ).symm
  rw [this]
  exact hGL2.continuous_expG.comp (continuous_id.smul continuous_const)

theorem kMat_add_two_pi (θ : ℝ) : kMat (θ + 2 * π) = kMat θ := by
  rw [kMat_add, kMat_two_pi, mul_one]

noncomputable def chi (j : ℤ) (θ : ℝ) : ℂ := Complex.exp ((j : ℂ) * θ * I)

theorem chi_add (j : ℤ) (a b : ℝ) : chi j (a + b) = chi j a * chi j b := by
  simp only [chi, ofReal_add, ← Complex.exp_add]; ring_nf

theorem chi_neg (j : ℤ) (a : ℝ) : chi j (-a) = (chi j a)⁻¹ := by
  simp only [chi, ofReal_neg, ← Complex.exp_neg]; ring_nf

theorem chi_mul_chi_neg (j : ℤ) (a : ℝ) : chi j a * chi j (-a) = 1 := by
  rw [chi_neg, mul_inv_cancel₀ (by simp [chi, Complex.exp_ne_zero])]

theorem chi_two_pi (j : ℤ) : chi j (2 * π) = 1 := by
  simp only [chi]
  have := Complex.exp_int_mul_two_pi_mul_I j
  rw [← this]; congr 1; push_cast; ring

theorem continuous_chi (j : ℤ) : Continuous (chi j) := by
  unfold chi; fun_prop

theorem norm_chi (j : ℤ) (a : ℝ) : ‖chi j a‖ = 1 := by
  rw [chi, Complex.norm_exp]
  simp

theorem conj_chi (j : ℤ) (a : ℝ) : (starRingEnd ℂ) (chi j a) = chi j (-a) := by
  rw [chi, chi, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

def weightSpace (j : ℤ) : Submodule ℂ H where
  carrier := {v | ∀ θ : ℝ, σ (kMat θ) v = chi j θ • v}
  add_mem' {v w} hv hw θ := by simp [map_add (f := _), hv θ, hw θ, smul_add]
  zero_mem' θ := by simp
  smul_mem' c v hv θ := by simp [hv θ, smul_comm c]

noncomputable def wProj (j : ℤ) (x : H) : H :=
  ((2 * π : ℝ)⁻¹ : ℂ) • ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x

theorem continuous_orbit_kMat (x : H) : Continuous fun θ : ℝ => σ (kMat θ) x :=
  (σ.continuous_orbit x).comp continuous_kMat

theorem continuous_wIntegrand (j : ℤ) (x : H) :
    Continuous fun θ : ℝ => chi j (-θ) • σ (kMat θ) x :=
  ((continuous_chi j).comp continuous_neg).smul (continuous_orbit_kMat σ x)

theorem wProj_mem (j : ℤ) (x : H) : wProj σ j x ∈ weightSpace σ j := by
  intro φ
  have hper : Function.Periodic (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) (2 * π) := by
    intro θ
    simp only [kMat_add_two_pi, neg_add, chi_add, chi_neg j (2 * π), chi_two_pi, inv_one, mul_one]
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have h1 : σ (kMat φ) (∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j φ • (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) := by
    rw [← (σ (kMat φ)).intervalIntegral_comp_comm hint]
    congr 1; funext θ
    simp only [map_smul, ← UnitaryRep.map_mul_apply, ← kMat_add, smul_smul, neg_add, chi_add]
    congr 1
    rw [← mul_assoc, chi_mul_chi_neg, one_mul]
  have h2 : ∫ θ in (0 : ℝ)..(2 * π), (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x := by
    rw [intervalIntegral.integral_comp_add_left (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) φ, add_zero]
    have := hper.intervalIntegral_add_eq φ 0
    rw [zero_add] at this
    exact this
  unfold wProj
  rw [map_smul, h1, intervalIntegral.integral_smul, h2, smul_comm]

theorem inner_wProj (j : ℤ) (x y : H) :
    ⟪y, wProj σ j x⟫_ℂ = ((2 * π : ℝ)⁻¹ : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) * ⟪y, σ (kMat θ) x⟫_ℂ := by
  rw [wProj, inner_smul_right]
  congr 1
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have := (innerSL ℂ y).intervalIntegral_comp_comm hint
  simp only [innerSL_apply_apply, inner_smul_right] at this
  exact this.symm

theorem norm_wProj_le (j : ℤ) (x : H) : ‖wProj σ j x‖ ≤ ‖x‖ := by
  rw [wProj, norm_smul]
  have hb : ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖ ≤ ‖x‖ * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_chi, one_mul, UnitaryRep.norm_map]
  rw [sub_zero, abs_of_pos (by positivity)] at hb
  have hn : ‖((2 * π : ℝ)⁻¹ : ℂ)‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖
      ≤ (2 * π)⁻¹ * (‖x‖ * (2 * π)) := by gcongr
    _ = ‖x‖ := by field_simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

end GroundTheory.Automorphic.ArchWhittaker
end
