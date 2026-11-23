module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle040
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdSmallBallAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DyadicSummationWithDecay
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle136
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle135
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
import Formalism.FormalDegreeBessel.StatementWR
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exp_injective_strictUpperTriangular : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ), (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) → NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  first | exact @GlobalTheory.ExpStrictUpper.exp_inj_strictUpper | exact GlobalTheory.ExpStrictUpper.exp_inj_strictUpper | (intros; apply GlobalTheory.ExpStrictUpper.exp_inj_strictUpper <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal

noncomputable section

namespace GlobalTheory.CircleArc

local instance factTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def par (x : AddCircle (2 * Real.pi)) : ℂ := (AddCircle.toCircle x : Circle)

theorem continuous_par : Continuous par :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

theorem par_injective : Function.Injective par := fun _ _ h =>
  AddCircle.injective_toCircle Real.two_pi_pos.ne' (Circle.ext h)

theorem par_coe (s : ℝ) : par (s : AddCircle (2 * Real.pi)) = Complex.exp (s * Complex.I) := by
  rw [par, AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul, Circle.coe_exp]

theorem par_add (x y) : par (x + y) = par x * par y := by
  rw [par, AddCircle.toCircle_add, Circle.coe_mul]; rfl

theorem norm_par (x) : ‖par x‖ = 1 := Circle.norm_coe _

theorem range_par : Set.range par = {z | ‖z‖ = 1} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact norm_par x
  · intro hz
    refine ⟨(z.arg : ℝ), ?_⟩
    rw [par_coe]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [show ‖z‖ = 1 from hz] at this
    simpa using this

theorem image_ball (r : ℝ) :
    par '' Metric.ball 0 r = (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 r := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff] at hx
    obtain ⟨s, rfl, hs⟩ := hx
    exact ⟨s, mem_ball_zero_iff.2 hs, (par_coe s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, ?_, par_coe s⟩
    rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff]
    exact ⟨s, rfl, mem_ball_zero_iff.1 hs⟩

theorem measure_arc : ∀ (τ : Measure ℂ) (ρ : ℝ), τ Set.univ < ⊤ → τ {z | ‖z‖ ≠ 1} = 0 →
    (∀ u : ℂ, ‖u‖ = 1 → τ.map (fun z => u * z) = τ) → 0 < ρ → ρ ≤ Real.pi →
    τ ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) =
      τ Set.univ * ENNReal.ofReal (ρ / Real.pi) := by
  intro τ ρ hfin hsupp hinv hρ hρπ
  haveI : IsFiniteMeasure τ := ⟨hfin⟩
  have hm : MeasurableEmbedding par :=
    (continuous_par.isClosedEmbedding par_injective).measurableEmbedding
  set ν : Measure (AddCircle (2 * Real.pi)) := τ.comap par with hν
  have hνa : ∀ S, ν S = τ (par '' S) := fun S => hm.comap_apply τ S
  haveI : IsFiniteMeasure ν := ⟨by rw [hνa]; exact measure_lt_top _ _⟩
  haveI : ν.IsAddLeftInvariant := by
    constructor
    intro a
    ext S hS
    rw [Measure.map_apply (measurable_const_add a) hS, hνa, hνa]
    conv_rhs => rw [← hinv (par a) (norm_par a)]
    rw [Measure.map_apply (measurable_const_mul _) (hm.measurableSet_image.2 hS)]
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨a + x, hx, par_add a x⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨-a + y, by simpa using hy, ?_⟩
      have h0 : par a ≠ 0 := by
        intro h0
        have := norm_par a
        rw [h0] at this
        simp at this
      apply mul_left_cancel₀ h0
      rw [← par_add, add_neg_cancel_left]
      exact h
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, ν = t • (volume : Measure (AddCircle (2 * Real.pi))) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hu : τ Set.univ = t * ENNReal.ofReal (2 * Real.pi) := by
    have h1 := hνa Set.univ
    rw [ht, Measure.smul_apply, AddCircle.measure_univ, Set.image_univ, range_par,
      ENNReal.smul_def, smul_eq_mul] at h1
    rw [h1]
    apply measure_congr
    exact (ae_eq_univ.2 hsupp).symm
  rw [← image_ball, ← hνa, hu, ht, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ← measure_congr AddCircle.closedBall_ae_eq_ball, AddCircle.volume_closedBall,
    min_eq_right (by linarith), mul_assoc, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
  congr 2
  have := Real.pi_pos
  field_simp

end GlobalTheory.CircleArc
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellDens.ScaledVol

theorem measurePreserving_inv_sqrt_two_smul (r : ℕ) :
    MeasurePreserving (fun y : Fin r → ℂ => (√2 : ℝ)⁻¹ • y) volume
      (((2 : ℝ≥0∞) ^ r) • volume) := by
  have hs : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_addHaar_smul _ hs, hfin, inv_pow, inv_inv, pow_mul, Real.sq_sqrt (by norm_num),
    abs_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

theorem volume_image_eq (A B F : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (r : ℕ) (L : ((A × A) × ((Fin r → ℂ) × B)) ≃L[ℝ] F)
    (hL : ∀ v, ‖L v‖ ^ 2 =
      ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2)
    (s : Set ((A × A) × ((Fin r → ℂ) × B))) (hs : MeasurableSet s) :
    volume (L '' s) = 2 ^ r * volume s := by
  have hc : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  let Ψ : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗ[ℝ]
      ((A × A) × ((Fin r → ℂ) × B)) :=
    (WithLp.linearEquiv 2 ℝ _).trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (A × A))
        ((WithLp.linearEquiv 2 ℝ _).trans
          (LinearEquiv.prodCongr
            ((WithLp.linearEquiv 2 ℝ (Fin r → ℂ)).trans
              (LinearEquiv.smulOfNeZero ℝ (Fin r → ℂ) (√2 : ℝ)⁻¹ hc))
            (LinearEquiv.refl ℝ B))))
  have hΨ : ∀ x, Ψ x = (x.ofLp.1.ofLp, ((√2 : ℝ)⁻¹ • x.ofLp.2.ofLp.1.ofLp, x.ofLp.2.ofLp.2)) :=
    fun _ => rfl
  let G : WithLp 2 (WithLp 2 (A × A) × WithLp 2 (EuclideanSpace ℂ (Fin r) × B)) ≃ₗᵢ[ℝ] F :=
    { Ψ.trans L.toLinearEquiv with
      norm_map' := fun x => by
        change ‖L (Ψ x)‖ = ‖x‖
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hL, hΨ, WithLp.prod_norm_sq_eq_of_L2,
          WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
        simp [norm_smul, mul_pow, Finset.mul_sum, ← mul_assoc, add_assoc] }
  have h0 := (measurePreserving_inv_sqrt_two_smul r).comp
    (GlobalTheory.volume_preserving_ofLp_complex (Fin r))
  haveI : SFinite (((2 : ℝ≥0∞) ^ r) • (volume : Measure (Fin r → ℂ))) := inferInstance
  have h1 := (h0.prod (MeasurePreserving.id (volume : Measure B))).comp
    (WithLp.volume_preserving_ofLp (EuclideanSpace ℂ (Fin r)) B)
  have h2 := ((WithLp.volume_preserving_ofLp A A).prod h1).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (A × A)) (WithLp 2 (EuclideanSpace ℂ (Fin r) × B)))
  have h3 := h2.measure_preimage hs.nullMeasurableSet
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul,
    ← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h3
  have hm : MeasurableSet (L '' s) :=
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs
  rw [← h3, ← G.measurePreserving.measure_preimage hm.nullMeasurableSet]
  congr 1
  ext x
  change L (Ψ x) ∈ L '' s ↔ Ψ x ∈ s
  exact L.injective.mem_set_image

end GlobalTheory.CellDens.ScaledVol
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball : ∀ (d : ℕ) (N : (Fin d → ℝ) → ℝ), ContinuousAt N 0 → N 0 = 0 → (∀ x, ∑ i, x i ^ 2 ≤ N x) → (∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) → Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  first | exact @GlobalTheory.tendsto_volume_sublevel_div_pow | exact GlobalTheory.tendsto_volume_sublevel_div_pow | (intros; apply GlobalTheory.tendsto_volume_sublevel_div_pow <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.tendsto_prod_smallBall_asymptotics : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (ν₁ : Measure X) (ν₂ : Measure Y) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (ρ₁ : X → ℝ) (ρ₂ : Y → ℝ) (d₁ d₂ : ℕ) (C₁ C₂ : ℝ), Measurable ρ₁ → Measurable ρ₂ → (∀ x, 0 ≤ ρ₁ x) → (∀ y, 0 ≤ ρ₂ y) → 0 < C₁ → 0 < C₂ → Filter.Tendsto (fun r : ℝ => ν₁ {x | Real.sqrt (ρ₁ x) ≤ r} / ENNReal.ofReal (r ^ (d₁))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁))) 1))) → Filter.Tendsto (fun r : ℝ => ν₂ {x | Real.sqrt (ρ₂ x) ≤ r} / ENNReal.ofReal (r ^ (d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₂))) 1))) → Filter.Tendsto (fun r : ℝ => (ν₁.prod ν₂) {x | Real.sqrt (ρ₁ x.1 + ρ₂ x.2) ≤ r} / ENNReal.ofReal (r ^ (d₁ + d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁ * C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1))) := by
  first | exact @GlobalTheory.SmallBallProd.tendsto_prod_smallBall | exact GlobalTheory.SmallBallProd.tendsto_prod_smallBall | (intros; apply GlobalTheory.SmallBallProd.tendsto_prod_smallBall <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.AmpArith

theorem v_part (k r f j : ℕ) (v : ℝ) (hr : 1 ≤ r) (hv : 1 ≤ v) :
    v ^ (k * (r - j) * f) *
        ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f
      ≤ 2 ^ (r ^ 2 * f) := by
  have hv0 : v ≠ 0 := by positivity
  have h2v : 0 ≤ 2 * v := by positivity
  have hexp : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  have hneg : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have key : ((2 * v) ^ (r * k))⁻¹ * 1 * (2 : ℝ) ^ (r * k + r ^ 2) = 2 ^ (r ^ 2) / v ^ (r * k) := by
    rw [mul_pow, pow_add]
    field_simp
  have hle : v ^ (k * (r - j) * f) ≤ v ^ (r * k * f) := by
    apply pow_le_pow_right₀ hv
    have : r - j ≤ r := Nat.sub_le r j
    calc k * (r - j) * f ≤ k * r * f := by gcongr
    _ = r * k * f := by ring
  rw [hneg, hexp, key, div_pow, ← pow_mul, ← pow_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
  calc v ^ (k * (r - j) * f) * 2 ^ (r ^ 2 * f) ≤ v ^ (r * k * f) * 2 ^ (r ^ 2 * f) := by gcongr
  _ = 2 ^ (r ^ 2 * f) * v ^ (r * k * f) := by ring

theorem exponent_bound (CH C R F : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (hR : 1 ≤ R)
    (hF : 0 ≤ F) :
    R ^ 2 * F + 3 * (2 * (R + 1) ^ 2 * F) + 3 * (2 * (R + 1) ^ 2 * F)
        + ((2 * R + 2) + 3 + CH * (2 * R + 2)) * (80 * R ^ 4 * F)
      ≤ C * (2 * R + 2) ^ 2 * F * (C * R ^ 4) := by
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR4 : R ^ 2 ≤ R ^ 4 := by nlinarith
  have hR41 : 1 ≤ R ^ 4 := le_trans hR2 hR4
  have hS : 1 ≤ (R + 1) ^ 2 := by nlinarith
  have hP0 : 0 ≤ R ^ 4 * (R + 1) ^ 2 := by positivity
  have e1 : R ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc R ^ 2 ≤ R ^ 4 := hR4
    _ = R ^ 4 * 1 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e2 : (R + 1) ^ 2 ≤ R ^ 4 * (R + 1) ^ 2 := by
    calc (R + 1) ^ 2 = 1 * (R + 1) ^ 2 := by ring
    _ ≤ R ^ 4 * (R + 1) ^ 2 := by gcongr
  have e3 : R ^ 4 * (2 * R + 5) ≤ 5 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 5 ≤ 5 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 5) ≤ R ^ 4 * (5 * (R + 1) ^ 2) := by gcongr
    _ = 5 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have e4 : R ^ 4 * (2 * R + 2) ≤ 2 * (R ^ 4 * (R + 1) ^ 2) := by
    have : 2 * R + 2 ≤ 2 * (R + 1) ^ 2 := by nlinarith
    calc R ^ 4 * (2 * R + 2) ≤ R ^ 4 * (2 * (R + 1) ^ 2) := by gcongr
    _ = 2 * (R ^ 4 * (R + 1) ^ 2) := by ring
  have hC1 : 1000 ≤ C := by linarith
  have hCC : 413 + 160 * CH ≤ 4 * C ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hF, mul_le_mul_of_nonneg_left e2 hF,
    mul_le_mul_of_nonneg_left e3 hF, mul_le_mul_of_nonneg_left e4 (mul_nonneg hF hCH),
    mul_le_mul_of_nonneg_left hCC (mul_nonneg hF hP0)]

theorem b_part (CH C : ℝ) (hCH : 0 ≤ CH) (hC : 100 * (CH + 10) ≤ C) (r m f : ℕ) (b v : ℝ)
    (hm : m = 2 * r + 2) (hr : 1 ≤ r) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) :
    2 ^ (r ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)
        * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hmR : (m : ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have f1 : (2 : ℝ) ^ (r ^ 2 * f) ≤ b ^ ((r : ℝ) ^ 2 * f) := by
    rw [show ((r : ℝ) ^ 2 * f) = ((r ^ 2 * f : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hb _
  have h8v : 8 * v ≤ b ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h4 : 4 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hb0.le]
  have f2 : (8 * v) ^ (2 * (r + 1) ^ 2 * f) ≤ b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) := by
    rw [show (3 * (2 * ((r : ℝ) + 1) ^ 2 * f)) = 3 * ((2 * (r + 1) ^ 2 * f : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_mul_natCast hb0.le]
    exact pow_le_pow_left₀ (by linarith) h8v _
  have hn : 8 * r ≤ 2 ^ (m + 3) := by
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : 2 ^ r ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add]
    omega
  have h8r : 8 * (r : ℝ) ≤ b ^ ((m : ℝ) + 3) := by
    rw [show ((m : ℝ) + 3) = ((m + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    calc 8 * (r : ℝ) = ((8 * r : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (m + 3) : ℕ) : ℝ) := by exact_mod_cast hn
    _ = (2 : ℝ) ^ (m + 3) := by push_cast; ring
    _ ≤ b ^ (m + 3) := pow_le_pow_left₀ (by norm_num) hb _
  have h3 : 8 * (r : ℝ) * b ^ (CH * m) ≤ b ^ ((m : ℝ) + 3 + CH * m) := by
    rw [Real.rpow_add hb0]
    exact mul_le_mul_of_nonneg_right h8r (Real.rpow_nonneg hb0.le _)
  have f3 : (8 * (r : ℝ) * b ^ (CH * m)) ^ (80 * r ^ 4 * f)
      ≤ b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
    rw [Real.rpow_mul_natCast hb0.le ((m : ℝ) + 3 + CH * m) (80 * r ^ 4 * f)]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) h3 _
  have p2 : 0 ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := pow_nonneg (by linarith) _
  have hE := exponent_bound CH C (r : ℝ) (f : ℝ) hCH hC hr1 (Nat.cast_nonneg f)
  calc
    _ ≤ b ^ ((r : ℝ) ^ 2 * f) * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (3 * (2 * ((r : ℝ) + 1) ^ 2 * f))
        * b ^ (((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      apply mul_le_mul _ f3 (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
          (Real.rpow_nonneg hb0.le _))
      apply mul_le_mul _ f2 p2 (mul_nonneg (Real.rpow_nonneg hb0.le _) (Real.rpow_nonneg hb0.le _))
      exact mul_le_mul f1 f2 p2 (Real.rpow_nonneg hb0.le _)
  _ = b ^ ((r : ℝ) ^ 2 * f + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f) + 3 * (2 * ((r : ℝ) + 1) ^ 2 * f)
        + ((m : ℝ) + 3 + CH * m) * ((80 * r ^ 4 * f : ℕ) : ℝ)) := by
      rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
  _ ≤ b ^ (C * (m : ℝ) ^ 2 * f * (C * (r : ℝ) ^ 4)) := by
      apply Real.rpow_le_rpow_of_exponent_le hb1
      rw [hmR]; push_cast; linarith [hE]
  _ = _ := Real.rpow_mul hb0.le _ _

theorem regroup {A B D G Pi H T G' Y U : ℝ} (hA : 0 ≤ A * D) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hG0 : 0 ≤ G) (hPi : 0 ≤ Pi) (hT : 0 ≤ T) (hU : A * D ≤ U) (hY : U * B * B * H ≤ Y)
    (hG : G ≤ G') : A * B * B * D * (G * Pi * H * T) ≤ G' * Pi * Y * T := by
  have hU0 : 0 ≤ U := le_trans hA hU
  have hBBH : 0 ≤ B * B * H := mul_nonneg (mul_nonneg hB hB) hH
  have hGPT : 0 ≤ G * Pi * T := mul_nonneg (mul_nonneg hG0 hPi) hT
  have hY0 : 0 ≤ Y := le_trans (mul_nonneg (mul_nonneg (mul_nonneg hU0 hB) hB) hH) hY
  calc A * B * B * D * (G * Pi * H * T) = (A * D) * (B * B * H) * (G * Pi * T) := by ring
  _ ≤ U * (B * B * H) * (G * Pi * T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hU hBBH) hGPT
  _ = (U * B * B * H) * (G * Pi * T) := by ring
  _ ≤ Y * (G * Pi * T) := mul_le_mul_of_nonneg_right hY hGPT
  _ ≤ Y * (G' * Pi * T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG hPi) hT) hY0
  _ = G' * Pi * Y * T := by ring

end GlobalTheory.AmpArith


open GlobalTheory.AmpArith in
theorem GlobalTheory.amplitude_arithmetic : ∀ CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (k r m f j : ℕ) (b v Del S Cs P : ℝ), m = 2 * r + 2 → 1 ≤ j → j ≤ r → r + 2 ≤ k → 1 ≤ f → 2 ≤ b → 1 ≤ v → 2 * v ≤ b → 0 < P → Del = P ^ 2 → 1 ≤ S → (v ^ (k * (r - j) * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) * (8 * v) ^ (2 * (r + 1) ^ 2 * f) * ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * ((16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f) * (P ^ (k - 1 - j))⁻¹ * (8 * r * b ^ (CH * m)) ^ (80 * r ^ 4 * f) * S ^ (-(Cs * k))) ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) * Del ^ (-(((k : ℝ) - 1 - j) / 2)) * (b ^ (C * (m : ℝ) ^ 2 * f)) ^ (C * (r : ℝ) ^ 4) * S ^ (-(Cs * k)) := by
  intro CH hCH
  refine ⟨100 * (CH + 10), ?_⟩
  intro C hC k r m f j b v Del S Cs P hm hj1 hjr hrk hf hb hv hvb hP hDel hS
  have hv0 : 0 ≤ v := by linarith
  have hb0 : 0 < b := by linarith
  have hr : 1 ≤ r := le_trans hj1 hjr
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hcast : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
    rw [Nat.cast_sub (by omega : j ≤ k - 1), Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hPi : Del ^ (-(((k : ℝ) - 1 - j) / 2)) = (P ^ (k - 1 - j))⁻¹ := by
    rw [hDel, ← Real.rpow_natCast P 2, ← Real.rpow_mul hP.le,
      show ((2 : ℕ) : ℝ) * (-(((k : ℝ) - 1 - j) / 2)) = -(((k - 1 - j : ℕ) : ℝ)) by
        rw [hcast]; push_cast; ring,
      Real.rpow_neg hP.le, Real.rpow_natCast]
  have hG : (16 * Real.pi * Real.exp 1 / k) ^ (j * (k - 1 - j) * f)
      ≤ (C / k) ^ ((j : ℝ) * ((k : ℝ) - 1 - j) * f) := by
    rw [show ((j : ℝ) * ((k : ℝ) - 1 - j) * f) = ((j * (k - 1 - j) * f : ℕ) : ℝ) by
      rw [Nat.cast_mul, Nat.cast_mul, hcast], Real.rpow_natCast]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    have hpe : Real.pi * Real.exp 1 < 3.15 * 2.7182818286 :=
      mul_lt_mul'' h1 h2 Real.pi_pos.le (Real.exp_pos 1).le
    nlinarith
  rw [hPi]
  exact GlobalTheory.AmpArith.regroup
    (mul_nonneg (pow_nonneg hv0 _) (pow_nonneg (mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (by positivity) _) zero_le_one) (by positivity)) _))
    (pow_nonneg (by linarith) _)
    (pow_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hb0.le _)) _)
    (pow_nonneg (by positivity) _)
    (inv_nonneg.mpr (pow_nonneg hP.le _))
    (Real.rpow_nonneg (by linarith) _)
    (GlobalTheory.AmpArith.v_part k r f j v hr hv)
    (GlobalTheory.AmpArith.b_part CH C hCH hC r m f b v hm hr hb hv hvb)
    hG
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.dyadic_summation_with_decay : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  first | exact @GlobalTheory.Amp.dyadic_summation | exact GlobalTheory.Amp.dyadic_summation | (intros; apply GlobalTheory.Amp.dyadic_summation <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.threeBoxesVolumeProduct_le_explicitPower : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  first | exact @GlobalTheory.Amp.volume_product_le | exact GlobalTheory.Amp.volume_product_le | (intros; apply GlobalTheory.Amp.volume_product_le <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_orthonormal_frame_of_flag_alt : ∀ (n a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ → Monotone W → (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) → ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  first | exact @GlobalTheory.exists_orthonormal_frame_of_flag | exact GlobalTheory.exists_orthonormal_frame_of_flag | (intros; apply GlobalTheory.exists_orthonormal_frame_of_flag <;> assumption)
end
