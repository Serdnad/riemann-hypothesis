module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMassOfFibre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle066
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle069
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped Matrix

noncomputable section

theorem exists_mem_zeroSet_mulVec_eq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {B : Matrix (Fin d) (Fin n) ℂ} (hB : ComplexSets.IsFiniteProjection J B) (x : Fin d → ℂ) :
    ∃ z ∈ ComplexSets.zeroSet J, B *ᵥ z = x := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (ComplexSets.projHom J B).toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨fun y => hB.finite.to_isIntegral y⟩
  have _ : (RingHom.ker (eval x)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (eval x)) (by
      intro q hq
      have hq0 : q = 0 := hB.injective (by rw [RingHom.mem_ker] at hq; exact hq.trans (map_zero _).symm)
      rw [hq0]; exact Ideal.zero_mem _)
  have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'
  have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q ↔ eval z q = 0 := fun q => by
    rw [← Ideal.mem_comap, hz, mem_vanishingIdeal_singleton_iff]; rfl
  refine ⟨z, fun q hq => (hmem q).1 ?_, funext fun i => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hq]; exact Q.zero_mem
  · have hi : X i - C (x i) ∈ RingHom.ker (eval x) := by simp [RingHom.mem_ker]
    rw [← hQP, Ideal.mem_comap] at hi
    change ComplexSets.projHom J B (X i - C (x i)) ∈ Q at hi
    have h1 : ComplexSets.projHom J B (X i - C (x i)) =
        Ideal.Quotient.mk J (ComplexSets.linPoly B i - C (x i)) := by
      simp [ComplexSets.projHom, ComplexSets.pullback]
    rw [h1, hmem, map_sub, eval_C, sub_eq_zero] at hi
    rw [← hi]
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem ConeFiniteFibreDim.proof : ConeFiniteFibreDim.Statement := by
  intro n m h J hJ _ _ hae
  have _ := hJ.isPrime

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ n := by
    have := ringKrullDim_le_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    rwa [ComplexSets.ringKrullDim_mvPolynomial_complex] at this
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = D at h0 hle
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (not_le.2 (WithBot.coe_lt_coe.2 (ENat.coe_lt_top n)))
      | coe d => exact ⟨d, rfl⟩
  rw [hd]
  by_contra hlt
  have hmd : m < d := by push_neg at hlt; exact_mod_cast hlt
  obtain ⟨k, rfl⟩ : ∃ k, d = m + k := ⟨d - m, by omega⟩
  have hk : 0 < k := by omega

  obtain ⟨W, ⟨S, rfl⟩, ⟨A₀, p, hpS, hp⟩, hW⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (m + k) J inferInstance hd

  set N : Matrix (Fin n) (Fin n) ℂ := (h.mat)ᵀ⁻¹
  have hdet : IsUnit (h.mat)ᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hMN : (h.mat)ᵀ * N = 1 := Matrix.mul_nonsing_inv _ hdet

  let blk : ((Fin m × Fin n) ⊕ (Fin k × Fin n) → ℂ) → Matrix (Fin (m + k)) (Fin n) ℂ :=
    fun v i j => Fin.addCases (motive := fun _ => ℂ) (fun a => v (.inl (a, j))) (fun b => v (.inr (b, j))) i
  let g : Fin (m + k) × Fin n → MvPolynomial ((Fin m × Fin n) ⊕ (Fin k × Fin n)) ℂ := fun ij =>
    ∑ l, Fin.addCases (motive := fun _ => MvPolynomial ((Fin m × Fin n) ⊕ (Fin k × Fin n)) ℂ)
      (fun a => X (.inl (a, l))) (fun b => X (.inr (b, l))) ij.1 * C (N l ij.2)
  have heval : ∀ v, eval v (bind₁ g p) = eval (fun ij => (blk v * N) ij.1 ij.2) p := by
    intro v
    change eval₂Hom (RingHom.id ℂ) v (bind₁ g p) = eval₂Hom (RingHom.id ℂ) _ p
    rw [eval₂Hom_bind₁]
    refine congrArg (fun f => eval₂Hom (RingHom.id ℂ) f p) (funext fun ij => ?_)
    obtain ⟨i, j⟩ := ij
    change eval v (g (i, j)) = (blk v * N) i j

    simp only [g, blk, Matrix.mul_apply, map_sum, map_mul, eval_C]
    refine Finset.sum_congr rfl fun l _ => ?_
    induction i using Fin.addCases <;> simp
  have hP0 : bind₁ g p ≠ 0 := by
    intro h0'
    let v₀ : (Fin m × Fin n) ⊕ (Fin k × Fin n) → ℂ :=
      Sum.elim (fun aj => (A₀ * (h.mat)ᵀ) (Fin.castAdd k aj.1) aj.2)
        (fun bj => (A₀ * (h.mat)ᵀ) (Fin.natAdd m bj.1) bj.2)
    have hv₀ : blk v₀ = A₀ * (h.mat)ᵀ := by
      ext i j
      induction i using Fin.addCases <;> simp [blk, v₀]
    have := heval v₀
    rw [h0', map_zero, hv₀, Matrix.mul_assoc, hMN, Matrix.mul_one] at this
    exact hp this.symm

  have h1 := ConeFibreDegree.ae_eval_ne_zero_univ _ hP0
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin m × Fin n) ⊕ (Fin k × Fin n) => ℂ)).quasiMeasurePreserving.ae h1
  have h3 := Measure.ae_ae_of_ae_prod h2
  have h4 : ∀ᵐ a : Fin m × Fin n → ℂ, ∃ b : Fin k × Fin n → ℂ,
      eval ((MeasurableEquiv.sumPiEquivProdPi _).symm (a, b)) (bind₁ g p) ≠ 0 :=
    h3.mono fun a ha => ha.exists
  have h5 := (measurePreserving_curry_matrix m n).symm.quasiMeasurePreserving.ae h4
  have _ : (ae (volume : Measure (Fin m → Fin n → ℂ))).NeBot := by
    refine ae_neBot.2 (Measure.measure_univ_ne_zero.1 ?_)
    rw [volume_pi, Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Measure.measure_univ_ne_zero.2 (NeZero.ne _)
  obtain ⟨π, hπ, b, hb⟩ := (hae.and h5).exists
  set v := (MeasurableEquiv.sumPiEquivProdPi fun _ : (Fin m × Fin n) ⊕ (Fin k × Fin n) => ℂ).symm
    ((MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm π, b)
  have hrow : ∀ (u : Fin n → ℂ) (i : Fin m), (blk v *ᵥ u) (Fin.castAdd k i) = ∑ j, π i j * u j := by
    intro u i
    simp [blk, v, Matrix.mulVec, dotProduct, MeasurableEquiv.coe_curry_symm]
    rfl
  have hfin : ComplexSets.IsFiniteProjection J (blk v * N) := hW ⟨p, hpS, by rw [← heval]; exact hb⟩

  obtain ⟨w, hw⟩ := hπ.exists
  apply hw
  have key : ∀ c : ℂ, ∃ y : EuclideanSpace ℂ (Fin n), (y ∈ coneSet h J ∧ linProj π y = w) ∧
      (blk v *ᵥ fun j => y j) (Fin.natAdd m ⟨0, hk⟩) = c := by
    intro c
    obtain ⟨z, hz, hBz⟩ := exists_mem_zeroSet_mulVec_eq hfin
      (Fin.addCases (motive := fun _ => ℂ) (fun a => w a) (fun _ => c))
    rw [← Matrix.mulVec_mulVec] at hBz
    have hpt : h.pointOf (WithLp.toLp 2 (N *ᵥ z)) = z := by
      simp [HermNorm.pointOf, Matrix.mulVec_mulVec, hMN]
    refine ⟨WithLp.toLp 2 (N *ᵥ z), ⟨fun q hq => ?_, ?_⟩, ?_⟩
    · rw [hpt]; exact hz q hq
    · ext i
      have := congrFun hBz (Fin.castAdd k i)
      rw [hrow] at this
      simpa [linProj] using this
    · have := congrFun hBz (Fin.natAdd m ⟨0, hk⟩)
      rw [Fin.addCases_right] at this
      exact this
  choose y hy hyc using key
  have hinj : Function.Injective y := fun c₁ c₂ he => by
    rw [← hyc c₁, ← hyc c₂, he]
  exact (Set.infinite_of_injective_forall_mem hinj hy).encard_eq

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointOfₗ (h : HermNorm n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun y := WithLp.toLp 2 (h.pointOf y)
  map_add' v w := by rw [HermNorm.pointOf_add']; rfl
  map_smul' c v := by rw [HermNorm.pointOf_smul']; rfl

theorem HermNorm.pointOfₗ_injective (h : HermNorm n) : Function.Injective h.pointOfₗ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  apply h.pointOf_eq_zero
  have := congrArg WithLp.ofLp hy
  simpa [HermNorm.pointOfₗ] using this

def HermNorm.pointOfL (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearEquiv.ofInjectiveEndo h.pointOfₗ h.pointOfₗ_injective).toContinuousLinearEquiv

theorem mem_coneSet_iff_pointOfL (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : y ∈ coneSet h J ↔ h.pointOfL y ∈ zeroSetEuc J :=
  Iff.rfl

theorem hausdorffMeasure_coneSet_ball_le (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (R : ℝ) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J ∩ Metric.ball 0 R) ≤
      ((‖(h.pointOfL.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖₊ : ℝ≥0∞) ^
          ((2 * d : ℕ) : ℝ)) *
        Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J ∩
          Metric.ball 0 (‖(h.pointOfL : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
  set e := h.pointOfL
  have hsub : coneSet h J ∩ Metric.ball 0 R ⊆ e.symm '' (zeroSetEuc J ∩
      Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
    rintro y ⟨hy, hyR⟩
    refine ⟨e y, ⟨(mem_coneSet_iff_pointOfL h J y).1 hy, ?_⟩, e.symm_apply_apply y⟩
    rw [mem_ball_zero_iff] at hyR ⊢
    calc ‖e y‖ = ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) y‖ := rfl
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R := by
        gcongr
      _ < _ := lt_add_one _
  calc _ ≤ Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (e.symm '' (zeroSetEuc J ∩
        Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1))) :=
        measure_mono hsub
    _ ≤ _ := e.symm.lipschitzWith.hausdorffMeasure_image_le (by positivity) _

theorem ConeLocalMass.proof (hDim : ConeFiniteFibreDim.Statement) (hMass : MassFinite.Statement)
    (hNull : NullSmaller.Statement) : ConeLocalMass.Statement := by
  intro n m h J hJ hm hmn hfib R
  have hle := hDim n m h J hJ hm hmn hfib
  refine lt_of_le_of_lt (hausdorffMeasure_coneSet_ball_le h J m R) ?_
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_
  rcases hle.lt_or_eq with hlt | heq
  · rw [measure_mono_null Set.inter_subset_left (hNull n m J hlt)]
    exact ENNReal.zero_lt_top
  · exact hMass n m J hJ.isPrime heq _

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def ConeJacMeasurable.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      AEMeasurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => coneJac h J p.1 p.2)
        ((volume : Measure (Fin m → Fin n → ℂ)).prod
          ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def ConeTangentDim.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
      ∀ᵐ y ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)),
        finrank ℂ (coneTangent h J y) = m

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def TangentGaussInvariant.Statement : Prop :=
  ∀ (n m : ℕ), 0 < m → m ≤ n → ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin n)), finrank ℂ T = m →
    ∀ y ∈ T,
      ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (tangentJac π T) =
        tangentGaussProfile n m ‖y‖

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

open scoped ENNReal Pointwise

noncomputable section

theorem ConeRadialIntegral.proof : ConeRadialIntegral.Statement := by
  intro n m hm C hC hfin f hf
  set d : ℝ := ((2 * m : ℕ) : ℝ) with hd_def
  set c := Measure.hausdorffMeasure d {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ C} with hc_def
  have hd : 0 ≤ d := Nat.cast_nonneg _
  set D : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hD_def
  have hDm : Measurable D := ENNReal.measurable_ofReal.comp (by fun_prop)
  set ν : Measure ℝ := Measure.map (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖)
    ((Measure.hausdorffMeasure d).restrict C) with hν_def
  set ρ : Measure ℝ := c • (volume.restrict (Ioi (0 : ℝ))).withDensity D with hρ_def
  have h2m : 2 * m ≠ 0 := by omega

  have hνIio : ∀ r : ℝ, ν (Iio r) = ENNReal.ofReal (max r 0 ^ (2 * m)) * c := by
    intro r
    rw [hν_def, Measure.map_apply continuous_norm.measurable measurableSet_Iio,
      Measure.restrict_apply (measurableSet_Iio.preimage continuous_norm.measurable)]
    rcases le_or_gt r 0 with hr | hr
    · have hempty : (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖) ⁻¹' Iio r ∩ C = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd (lt_of_lt_of_le h hr) (not_lt.2 (norm_nonneg y))
      rw [hempty, measure_empty, max_eq_right hr, zero_pow h2m, ENNReal.ofReal_zero, zero_mul]
    · have hset : (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖) ⁻¹' Iio r ∩ C =
          r • {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ C} := by
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_smul_set, mem_ofPred_eq]
        constructor
        · rintro ⟨hy, hyC⟩
          refine ⟨r⁻¹ • y, ⟨?_, hC y hyC r⁻¹ (inv_pos.2 hr)⟩, smul_inv_smul₀ hr.ne' y⟩
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
          exact hy
        · rintro ⟨z, ⟨hz, hzC⟩, rfl⟩
          refine ⟨?_, hC z hzC r hr⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          calc r * ‖z‖ < r * 1 := mul_lt_mul_of_pos_left hz hr
            _ = r := mul_one r
      rw [hset, Measure.hausdorffMeasure_smul₀ hd hr.ne', max_eq_left hr.le, ENNReal.smul_def,
        smul_eq_mul]
      congr 1
      rw [hd_def, NNReal.rpow_natCast, ENNReal.ofReal_pow hr.le, ENNReal.coe_pow]
      congr 1
      rw [Real.nnnorm_of_nonneg hr.le, ENNReal.ofReal_eq_coe_nnreal hr.le]

  have hρIio : ∀ r : ℝ, ρ (Iio r) = ENNReal.ofReal (max r 0 ^ (2 * m)) * c := by
    intro r
    rw [hρ_def, Measure.smul_apply, smul_eq_mul, withDensity_apply _ measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, mul_comm]
    congr 1
    rcases le_or_gt r 0 with hr | hr
    · have hempty : Iio r ∩ Ioi (0 : ℝ) = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        linarith
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure, max_eq_right hr, zero_pow h2m,
        ENNReal.ofReal_zero]
    · rw [max_eq_left hr.le, inter_comm, Ioi_inter_Iio]
      have hcont : Continuous (fun t : ℝ => 2 * (m : ℝ) * t ^ (2 * m - 1)) := by fun_prop
      rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)]
      · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
          intervalIntegral.integral_const_mul, integral_pow]
        congr 1
        obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 1 := ⟨2 * m - 1, by omega⟩
        have hk' : 2 * m - 1 = k := by omega
        have hkR : 2 * (m : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hk
        rw [hk', hkR, hk, zero_pow (Nat.succ_ne_zero k), sub_zero]
        field_simp
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_nonneg (by positivity) (pow_nonneg ht.1.le _)
  have hfinG : ∀ r : ℝ, ENNReal.ofReal (max r 0 ^ (2 * m)) * c ≠ ⊤ := fun r =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hνρ : ν = ρ := by
    refine Measure.ext_of_Ico' ν ρ (fun a b _ => ?_) (fun a b hab => ?_)
    · exact ne_top_of_le_ne_top (by rw [hνIio b]; exact hfinG b)
        (measure_mono Ico_subset_Iio_self)
    · have hsub : Iio a ⊆ Iio b := Iio_subset_Iio hab.le
      have hIco : Ico a b = Iio b \ Iio a := by
        ext t
        simp only [mem_Ico, mem_sdiff, mem_Iio, not_lt]
        tauto
      rw [hIco, measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hνIio a]; exact hfinG a),
        measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hρIio a]; exact hfinG a),
        hνIio, hνIio, hρIio, hρIio]
  calc ∫⁻ y in C, f ‖y‖ ∂(Measure.hausdorffMeasure d) = ∫⁻ r, f r ∂ν := by
        rw [hν_def, lintegral_map hf continuous_norm.measurable]
    _ = ∫⁻ r, f r ∂ρ := by rw [hνρ]
    _ = c * ∫⁻ r in Ioi 0, f r * D r := by
        rw [hρ_def, lintegral_smul_measure, smul_eq_mul,
          lintegral_withDensity_eq_lintegral_mul _ hDm hf]
        congr 1
        refine lintegral_congr fun r => ?_
        simp only [Pi.mul_apply]
        exact mul_comm _ _

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def TangentJacComp.Statement : Prop :=
  ∀ (d n : ℕ) (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin d → Fin n → ℂ),
    tangentJac π (LinearMap.range L) * areaJacobian (L.restrictScalars ℝ) =
      |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)|

end

end GroundTheory.Heights₂.Heights
end
