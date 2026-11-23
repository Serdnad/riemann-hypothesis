module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

theorem realGraphPt_injective {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)) :
    Function.Injective (realGraphPt F) := by
  intro x y hxy
  ext i
  simpa [realGraphPt] using congrArg (fun z : EuclideanSpace ℝ (Fin k ⊕ Fin m) => z (Sum.inl i)) hxy

theorem realGraphPt_continuousOn {k m : ℕ} {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin k))} (hF : ContinuousOn F s) : ContinuousOn (realGraphPt F) s := by
  unfold realGraphPt
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  rcases i with i | i
  · exact (PiLp.continuous_apply 2 _ i).continuousOn
  · exact (PiLp.continuous_apply 2 _ i).comp_continuousOn hF

theorem AreaGraphBound.proof (h₁ : AreaGraphPiece.Statement) (h₂ : AreaGraphPartition.Statement)
    (h₃ : GraphJacContinuous.Statement) : AreaGraphBound.Statement := by
  intro k m U F hU hF A hAU hA δ hδ0 hδ1
  set J : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0∞ := fun B =>
    ENNReal.ofReal (graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) with hJ
  set c : ℝ≥0∞ := ((1 + δ : ℝ≥0) : ℝ≥0∞) with hc

  choose r₃ hr₃0 hr₃ using fun B => h₃ k m B δ (by exact_mod_cast hδ0)
  obtain ⟨t, An, hdisj, htm, -, hcov, happrox, hder⟩ :=
    h₂ k m U F hU hF (fun B => min δ (r₃ B).toNNReal)
      (fun B => (lt_min hδ0 (Real.toNNReal_pos.2 (hr₃0 B))).ne')
  set p : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => A ∩ t n with hp
  have hpm : ∀ n, MeasurableSet (p n) := fun n => hA.inter (htm n)
  have hpd : Pairwise (Function.onFun Disjoint p) := fun i j hij =>
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hAp : A = ⋃ n, p n := by
    rw [← Set.inter_iUnion]
    exact (Set.inter_eq_left.2 (hAU.trans hcov)).symm

  have hcmp : ∀ n, ∀ x ∈ p n, J (fderiv ℝ F x) ≤ c * J (An n) ∧ J (An n) ≤ c * J (fderiv ℝ F x) := by
    intro n x hx
    have hle : ‖fderiv ℝ F x - An n‖ ≤ r₃ (An n) := by
      have := (hder n x hx.2).trans (min_le_right _ _)
      have h' : ((‖fderiv ℝ F x - An n‖₊ : ℝ≥0) : ℝ) ≤ ((r₃ (An n)).toNNReal : ℝ) := by exact_mod_cast this
      simpa [Real.coe_toNNReal _ (hr₃0 (An n)).le] using h'
    obtain ⟨h1, h2⟩ := hr₃ (An n) (fderiv ℝ F x) hle
    have e : ∀ y : ℝ, ENNReal.ofReal ((1 + δ) * y) = c * ENNReal.ofReal y := fun y => by
      rw [ENNReal.ofReal_mul (by positivity), hc]; congr 1
      rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
    exact ⟨(ENNReal.ofReal_le_ofReal h1).trans (e _).le, (ENNReal.ofReal_le_ofReal h2).trans (e _).le⟩

  have hpiece : ∀ n, μH[(k : ℝ)] (realGraphPt F '' p n) ≤ c ^ (k + 1) * ∫⁻ x in p n, J (fderiv ℝ F x)
      ∂(μH[(k : ℝ)]) ∧ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
        c * μH[(k : ℝ)] (realGraphPt F '' p n) := by
    intro n
    obtain ⟨u, l⟩ := h₁ k m F (An n) δ (p n) hδ1
      (((happrox n).mono_set Set.inter_subset_right).mono_num (min_le_left _ _))
    have i₁ : J (An n) * μH[(k : ℝ)] (p n) ≤ c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).2
    have i₂ : ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤ c * (J (An n) * μH[(k : ℝ)] (p n)) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).1
    constructor
    · calc _ ≤ c ^ k * (J (An n) * μH[(k : ℝ)] (p n)) := by rw [← mul_assoc]; exact u
        _ ≤ c ^ k * (c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)])) := by gcongr
        _ = _ := by rw [pow_succ, mul_assoc]
    · calc _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * (c * (J (An n) * μH[(k : ℝ)] (p n))) := by gcongr
        _ = c * (((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * J (An n) * μH[(k : ℝ)] (p n)) := by ring
        _ ≤ _ := by gcongr

  have hG : ∀ n, MeasurableSet (realGraphPt F '' p n) := fun n =>
    (hpm n).image_of_continuousOn_injOn
      (realGraphPt_continuousOn (hF.continuousOn.mono (Set.inter_subset_left.trans hAU)))
      (realGraphPt_injective F).injOn
  have hGd : Pairwise (Function.onFun Disjoint fun n => realGraphPt F '' p n) := fun i j hij =>
    (Set.disjoint_image_iff (realGraphPt_injective F)).2 (hpd hij)
  have hS : μH[(k : ℝ)] (realGraphPt F '' A) = ∑' n, μH[(k : ℝ)] (realGraphPt F '' p n) := by
    rw [hAp, Set.image_iUnion, measure_iUnion hGd hG]
  have hI : ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) =
      ∑' n, ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
    rw [hAp, lintegral_iUnion hpm hpd]
  change μH[(k : ℝ)] (realGraphPt F '' A) ≤ c ^ (k + 1) * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ∧
    ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
      c * μH[(k : ℝ)] (realGraphPt F '' A)
  rw [hS, hI, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun n => (hpiece n).1, ENNReal.tsum_le_tsum fun n => (hpiece n).2⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem graphPt_injective {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) : Function.Injective (graphPt e F) := by
  intro x y h
  ext i
  have := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z (e.symm (Sum.inl i))) h
  simpa [graphPt] using this

theorem differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℂ F x) : DifferentiableAt ℂ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases hj : e j with i | i
  · simp only [Sum.elim_inl]
    exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · simp only [Sum.elim_inr]
    exact (differentiableAt_piLp 2).1 hF i

theorem continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem ProjectionFormula.proof (h1 : AreaMultiplicity.Statement) (h2 : FrameJacobianSum.Statement)
    (h3 : GraphAreaHolomorphic.Statement) : ProjectionFormula.Statement := by
  classical
  intro d m n e Ω F hΩ hF b B hB
  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ (graphPt e F) x := fun x hx =>
    differentiableAt_graphPt e (hF.differentiableAt (hΩ.mem_nhds hx))
  set A := Ω ∩ graphPt e F ⁻¹' B with hAdef
  have hAΩ : A ⊆ Ω := Set.inter_subset_left
  have hA : MeasurableSet A := by
    have hc : ContinuousOn (graphPt e F) Ω := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    have hm := (hc.measurable_piecewise (continuousOn_const (c := (0 : EuclideanSpace ℂ (Fin n))))
      hΩ.measurableSet) hB
    have hEq : A = Ω ∩ (Ω.piecewise (graphPt e F) fun _ => 0) ⁻¹' B := by
      ext x
      simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx'⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx] at hx'; exact hx'⟩
    rw [hEq]
    exact hΩ.measurableSet.inter hm

  let πR : ∀ I : Finset (Fin n), EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ I := fun I =>
    (LinearMap.toContinuousLinearMap (frameProjLin b I)).restrictScalars ℝ
  have hpt : ∀ x ∈ A, ENNReal.ofReal (areaJacobian
      (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) =
      ∑ I ∈ Finset.univ.powersetCard d, ENNReal.ofReal (areaJacobian
        ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)) := by
    intro x hx
    set L := fderiv ℂ (graphPt e F) x with hL
    have e0 : ((L.restrictScalars ℝ : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
        (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
      LinearMap.ext fun v => rfl
    have eI : ∀ I : Finset (Fin n), (((πR I).comp (L.restrictScalars ℝ)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I) =
        (frameProjLin b I ∘ₗ (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).restrictScalars ℝ :=
      fun I => LinearMap.ext fun v => rfl
    rw [(hGd x (hAΩ hx)).fderiv_restrictScalars ℝ, ← hL, e0, ← ENNReal.ofReal_sum_of_nonneg]
    · simp only [eI]
      exact congrArg ENNReal.ofReal (h2 d n _ b)
    · exact fun I _ => Real.sqrt_nonneg _
  have hmeas : ∀ I : Finset (Fin n), AEMeasurable (fun x => ENNReal.ofReal (areaJacobian
      ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)))
      ((μH[((2 * d : ℕ) : ℝ)]).restrict A) := fun I =>
    ((ENNReal.continuous_ofReal.comp (continuous_areaJacobian.comp
      (continuous_const.clm_comp continuous_id))).measurable.comp
        (measurable_fderiv ℝ (graphPt e F))).aemeasurable
  rw [(Set.image_inter_preimage (graphPt e F) Ω B).symm, h3 d m n e Ω F hΩ hF A hAΩ hA,
    setLIntegral_congr_fun hA hpt, lintegral_finsetSum' _ fun I _ => hmeas I]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hcard : I.card = d := (Finset.mem_powersetCard.1 hI).2
  have hfr1 : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
  have hfr2 : finrank ℝ (EuclideanSpace ℂ I) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe, hcard]
  have hder : ∀ x ∈ A, HasFDerivWithinAt (fun x => frameProjLin b I (graphPt e F x))
      ((πR I).comp (fderiv ℝ (graphPt e F) x)) A x := fun x hx =>
    ((πR I).hasFDerivAt.comp x ((hGd x (hAΩ hx)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  rw [h1 _ _ (2 * d) hfr1 hfr2 A _ _ hA hder]
  refine lintegral_congr fun y => ?_
  have hset : {z ∈ graphPt e F '' A | frameProj b I z = WithLp.ofLp y} =
      graphPt e F '' {x ∈ A | frameProjLin b I (graphPt e F x) = y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, WithLp.ofLp_injective 2 (by rw [frameProjLin_apply]; exact hz)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← frameProjLin_apply, hxy]⟩
  unfold frameFibreCount
  rw [hset, (graphPt_injective e F).injOn.encard_image]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace AreaGraphPiece

variable {k m : ℕ}

def pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => u i) (fun i => w i))

def firstPart (p : EuclideanSpace ℝ (Fin k ⊕ Fin m)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => p (Sum.inl i))

theorem realGraphPt_eq (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : realGraphPt F x = pairPt x (F x) := rfl

theorem firstPart_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    firstPart (pairPt u w) = u := by
  ext i
  simp [firstPart, pairPt]

theorem pairPt_add (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w + pairPt u' w' = pairPt (u + u') (w + w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_sub (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w - pairPt u' w' = pairPt (u - u') (w - w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    c • pairPt u w = pairPt (c • u) (c • w) := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem inner_pairPt (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    ⟪pairPt u w, pairPt u' w'⟫ = ⟪u, u'⟫ + ⟪w, w'⟫ := by
  simp [pairPt, PiLp.inner_apply, Fintype.sum_sum_type]

theorem norm_pairPt_sq (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt u w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_pairPt]

theorem norm_le_norm_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖u‖ ≤ ‖pairPt u w‖ := by
  have h := norm_pairPt_sq u w
  nlinarith [norm_nonneg u, norm_nonneg (pairPt u w), sq_nonneg ‖w‖]

theorem norm_pairPt_zero (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt (0 : EuclideanSpace ℝ (Fin k)) w‖ = ‖w‖ := by
  have h := norm_pairPt_sq (0 : EuclideanSpace ℝ (Fin k)) w
  rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

def graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k ⊕ Fin m) where
  toFun x := pairPt x (A x)
  map_add' x y := by rw [map_add (f := _), pairPt_add]
  map_smul' c x := by rw [map_smul, pairPt_smul]; rfl

theorem graphLin_apply (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : graphLin A x = pairPt x (A x) := rfl

theorem adjoint_graphLin_comp (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    LinearMap.adjoint (graphLin A) ∘ₗ graphLin A =
      (1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
        LinearMap.adjoint (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
          (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply, inner_add_left,
    Module.End.one_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_left, graphLin_apply,
    graphLin_apply, inner_pairPt]
  rfl

theorem normDet_graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (graphLin A).normDet =
      graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  unfold graphJac
  rw [← adjoint_graphLin_comp, ← LinearMap.normDet_sq (graphLin A)]
  push_cast
  exact (Real.sqrt_sq (LinearMap.normDet_nonneg _)).symm

end AreaGraphPiece


open AreaGraphPiece in
theorem AreaGraphPiece.proof : AreaGraphPiece.Statement := by
  intro k m F A δ t hδ hF
  set L := graphLin A with hLdef
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) ≤ δ := δ.2

  have hsub : ∀ x y, realGraphPt F x - realGraphPt F y - L (x - y) =
      pairPt (0 : EuclideanSpace ℝ (Fin k)) (F x - F y - A (x - y)) := by
    intro x y
    rw [realGraphPt_eq, realGraphPt_eq, hLdef, graphLin_apply, pairPt_sub, pairPt_sub]
    simp
  have hL : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => norm_le_norm_pairPt v (A v)
  have hclose : ∀ x ∈ t, ∀ y ∈ t,
      |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖| ≤ δ * ‖L (x - y)‖ := by
    intro x hx y hy
    calc |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖|
        ≤ ‖realGraphPt F x - realGraphPt F y - L (x - y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖F x - F y - A (x - y)‖ := by rw [hsub, norm_pairPt_zero]
      _ ≤ δ * ‖x - y‖ := hF x hx y hy
      _ ≤ δ * ‖L (x - y)‖ := mul_le_mul_of_nonneg_left (hL _) hδ0

  have himG : realGraphPt F '' t = (fun p => realGraphPt F (firstPart p)) '' (L '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hLdef, graphLin_apply, firstPart_pairPt]
  have hlipG : LipschitzOnWith (1 + δ) (fun p => realGraphPt F (firstPart p)) (L '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [hLdef, graphLin_apply, firstPart_pairPt, dist_eq_norm]
    rw [← graphLin_apply, ← graphLin_apply, ← map_sub, ← hLdef]
    have h := (abs_le.1 (hclose x hx y hy)).2
    push_cast
    linarith

  have himL : L '' t = (fun p => L (firstPart p)) '' (realGraphPt F '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [realGraphPt_eq, firstPart_pairPt]
  have hlipL : LipschitzOnWith (1 - δ)⁻¹ (fun p => L (firstPart p)) (realGraphPt F '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [realGraphPt_eq, firstPart_pairPt, dist_eq_norm]
    rw [← realGraphPt_eq, ← realGraphPt_eq, ← map_sub]
    have h := (abs_le.1 (hclose x hx y hy)).1
    rw [NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one, inv_mul_eq_div,
      le_div_iff₀ (by linarith)]
    nlinarith

  have harea : μH[(k : ℝ)] (L '' t) =
      ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
        μH[(k : ℝ)] t := by
    have h := LinearMap.hausdorffMeasure_image L t
    rw [finrank_euclideanSpace_fin] at h
    rw [h, hLdef, normDet_graphLin]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · calc μH[(k : ℝ)] (realGraphPt F '' t)
        = μH[(k : ℝ)] ((fun p => realGraphPt F (firstPart p)) '' (L '' t)) := by rw [← himG]
      _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (L '' t) :=
          hlipG.hausdorffMeasure_image_le hk
      _ = _ := by rw [harea, ENNReal.rpow_natCast, mul_assoc]
  · have hle : μH[(k : ℝ)] (L '' t) ≤
        (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t) := by
      calc μH[(k : ℝ)] (L '' t)
          = μH[(k : ℝ)] ((fun p => L (firstPart p)) '' (realGraphPt F '' t)) := by rw [← himL]
        _ ≤ (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (realGraphPt F '' t) :=
            hlipL.hausdorffMeasure_image_le hk
        _ = _ := by rw [ENNReal.rpow_natCast]
    have hne : (1 - δ : ℝ≥0) ≠ 0 := (tsub_pos_of_lt hδ).ne'
    calc ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
            μH[(k : ℝ)] t
        = ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (L '' t) := by rw [harea, mul_assoc]
      _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t)) := by gcongr
      _ = μH[(k : ℝ)] (realGraphPt F '' t) := by
          rw [← mul_assoc, ← mul_pow, ← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one,
            one_pow, one_mul]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem WeierstrassDivision.proof (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassPolynomialDivision.Statement) : WeierstrassDivision.Statement := by
  intro σ _ d f g hf hg hord
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d f hf hord
  obtain ⟨q, a, hq, ha, hgq⟩ := hD σ d c g hc hc0 hg
  refine ⟨fun x => q x / e x, a, hq.div he he0, ha, ?_⟩
  filter_upwards [hfe, hgq, he.continuousAt.eventually_ne he0] with x hfx hgx hex
  rw [hgx, hfx, div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hex]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def CMRingUnmixed.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsCohenMacaulayLocalRing A],
    ∀ p ∈ associatedPrimes A A, p ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ p) = ringKrullDim A

end GroundTheory.Heights₂.Heights
end
