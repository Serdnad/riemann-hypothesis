module

import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralBallPow
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle014
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormIrreducible
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle030
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
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre mcPts)

theorem integral_indicator_ball_norm_pow (e : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t : ℂ, (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) t =
      Real.pi * R ^ (2 * (e + 1)) / (e + 1) := by
  apply ChowFormHeightComparison₂.CF.C.integral_ball_pow <;> assumption

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem specFirstVar_isWeightedHomogeneous' {R : Type*} [CommSemiring R] {k n : ℕ} (u : Fin n → R)
    (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X R (groupWeight k n) (i', j)

theorem isMultiHomog_specFirst {R : Type*} [CommSemiring R] {k n δ : ℕ}
    {f : MvPolynomial (Fin (k + 1) × Fin n) R} (u : Fin n → R) (hf : IsMultiHomog δ f) :
    IsMultiHomog δ (specFirst f u) := by
  unfold IsMultiHomog specFirst

  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous' u ij).pow _

theorem ChowDegreeSection.proof (h : ChowFormSectionPerfect.Statement) : ChowDegreeSection.Statement := by
  intro F _ _ n e I u hI hdim hu
  obtain ⟨f, hf⟩ := chowFormExists F n (e + 2) I hI hdim
  have hfδ : IsMultiHomog (chowDegree I (e + 2)) f := Vertical.ChowFormHomog.proof F n (e + 2) I f hf
  obtain ⟨c, hc, g, hg, hfu⟩ := h F n (e + 1) I f u hI hf hu
  have hsδ : IsMultiHomog (chowDegree I (e + 2)) (specFirst f u) := isMultiHomog_specFirst u hfδ
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 := by
    refine mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW => ?_)
    exact pow_ne_zero _ (hg W hW).1
  rw [hfu] at hsδ
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hsδ hne
  rw [← hsum, Finsupp.sum]
  refine Finset.sum_congr rfl fun W hW => ?_
  congr 1
  exact Vertical.chowForm_degree_unique (Nat.succ_pos e) (hg W hW) (hg W hW) (hδW W hW)
    (Vertical.ChowFormHomog.proof F n (e + 1) W (g W) (hg W hW))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial Vertical Vertical.NormFormIrreducible

theorem aeval_smul_of_isHomogeneous {F K : Type*} [Field F] [Field K] [Algebra F K] {n d : ℕ}
    {g : MvPolynomial (Fin n) F} (hg : g.IsHomogeneous d) (c : K) (y : Fin n → K) :
    aeval (fun j => c * y j) g = c ^ d * aeval y g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hg (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  rw [aeval_monomial, aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem ChowDegreeClosedPoint.proof (hField : ClosedPointChartField.Statement)
    (hCone : ClosedPointConeCoord.Statement) : ChowDegreeClosedPoint.Statement := by
  classical
  intro F _ _ n I i hI hdim hXi
  obtain ⟨hfield, hfin⟩ := hField F n I i hI hdim hXi
  set J : Ideal (MvPolynomial (Fin n) F) := I ⊔ Ideal.span {X i - 1} with hJ
  let _ : Field (MvPolynomial (Fin n) F ⧸ J) := hfield.toField
  let L := MvPolynomial (Fin n) F ⧸ J
  have _ : FiniteDimensional F L := hfin
  have _ : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  let K := AlgebraicClosure F
  let ξ : Fin n → L := fun j => Ideal.Quotient.mk J (X j)
  have hξ : ∀ g : MvPolynomial (Fin n) F, aeval ξ g = Ideal.Quotient.mk J g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp; rfl
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X]
  have hξi : ξ i = 1 := by
    have : X i - 1 ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  set t : Fin n → F := Pi.single i 1 with ht_def
  have ht : ∑ j, algebraMap F L (t j) * ξ j = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [ht_def, hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [ht_def, hξi]
  have hgen : Algebra.adjoin F (Set.range ξ) = ⊤ := by
    have hr : Set.range ξ = Ideal.Quotient.mkₐ F J '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [hr, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective F J

  obtain ⟨f, hf⟩ := chowFormExists F n 1 I hI hdim
  have hhom : IsMultiHomog (chowDegree I 1) f := chowFormHomog F n 1 I f hf
  have hfH : f.IsHomogeneous (chowDegree I 1) := by
    intro m hm
    have h := congrFun (hhom hm) 0
    rw [← h, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq0 : q.1 = 0 := Subsingleton.elim _ _
    simp [groupWeight, hq0]
  let ι : Fin n → Fin 1 × Fin n := fun j => (0, j)
  have hsnd : ∀ p : MvPolynomial (Fin 1 × Fin n) F, rename ι (rename Prod.snd p) = p := by
    intro p
    rw [rename_rename]
    convert rename_id_apply p
    funext q
    exact Prod.ext (Subsingleton.elim _ _) rfl
  set f₀ := rename Prod.snd f with hf₀
  set N : MvPolynomial (Fin n) F := Vertical.normForm (R := F) L ξ with hN
  have hprod : N.map (algebraMap F K) = ∏ σ : L →ₐ[F] K, embForm σ ξ := normForm_map_eq_prod ξ

  have hdvd1 : f ∣ rename ι N := by
    refine (hf.2 _).1 fun u hu => ?_
    obtain ⟨y, hy0, hyI, hyu⟩ := hu
    have hyi : y i ≠ 0 := hCone F n I i hI hdim hXi K y hy0 hyI
    let ys : Fin n → K := fun j => (y i)⁻¹ * y j
    have hker : J ≤ RingHom.ker (aeval (R := F) ys).toRingHom := by
      refine sup_le (fun g hg => ?_) ((Ideal.span_le).mpr ?_)
      · set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          ← sum_homogeneousComponent g, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d g),
          hyI _ (hI.isHomog g hg d), mul_zero]
      · rintro _ rfl
        simp [ys, hyi]
    let σ : L →ₐ[F] K := Ideal.Quotient.liftₐ J (aeval ys) fun g hg => hker hg
    have hσ : ∀ j, σ (ξ j) = ys j := fun j =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp [ys])
    rw [aeval_rename, aeval_def, ← eval_map, hprod, eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
    rw [eval_embForm]
    simp only [hσ, ys, Function.comp_apply, ι]
    have := hyu 0
    calc ∑ j, u (0, j) * ((y i)⁻¹ * y j) = (y i)⁻¹ * ∑ j, u (0, j) * y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]

  have hdvd2 : ∀ σ : L →ₐ[F] K, embForm σ ξ ∣ f₀.map (algebraMap F K) := by
    intro σ
    have hprime : Prime (embForm σ ξ) := (irreducible_embForm σ ht).prime
    have hspan : (Ideal.span {embForm σ ξ}).IsPrime :=
      (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    rw [← Ideal.mem_span_singleton, ← hspan.radical,
      ← vanishingIdeal_zeroLocus_eq_radical (K := K), mem_vanishingIdeal_iff]
    intro u hu
    have hu0 : ∑ j, u j * σ (ξ j) = 0 := by
      have := hu _ (Ideal.mem_span_singleton_self _)
      rwa [aeval_eq_eval, eval_embForm] at this
    rw [aeval_eq_eval, eval_map, ← aeval_def, hf₀, aeval_rename]
    refine (hf.2 f).2 dvd_rfl _ ⟨fun j => σ (ξ j), fun h => ?_, fun g hg => ?_, fun k => ?_⟩
    · have := congrFun h i
      simp [hξi] at this
    · rw [← comp_aeval_apply, hξ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg),
        map_zero]
    · rw [Subsingleton.elim k 0]
      simpa using hu0
  have hdvd3 : N.map (algebraMap F K) ∣ f₀.map (algebraMap F K) := by
    rw [hprod]; exact prod_embForm_dvd hgen ht hdvd2
  have hdvd4 : f₀ ∣ N := by
    have := map_dvd (rename Prod.snd) hdvd1
    rwa [rename_rename, show Prod.snd ∘ ι = id from rfl, rename_id_apply] at this

  have hf0 : f₀ ≠ 0 := fun h => hf.1 (by rw [← hsnd f, ← hf₀, h, map_zero])
  have hmap0 : f₀.map (algebraMap F K) ≠ 0 :=
    fun h => hf0 (map_injective _ (algebraMap F K).injective (by rw [h, map_zero]))
  obtain ⟨h, hh⟩ := hdvd4
  obtain ⟨q, hq⟩ := hdvd3
  have hq1 : q * h.map (algebraMap F K) = 1 := by
    apply mul_left_cancel₀ hmap0
    calc f₀.map (algebraMap F K) * (q * h.map (algebraMap F K))
        = (f₀.map (algebraMap F K) * h.map (algebraMap F K)) * q := by ring
      _ = N.map (algebraMap F K) * q := by rw [hh, map_mul]
      _ = f₀.map (algebraMap F K) * 1 := by rw [← hq, mul_one]
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp (isUnit_iff_exists_inv.mpr ⟨_, hq1⟩)
  have hlin : ∀ σ : L →ₐ[F] K, (embForm σ ξ).IsHomogeneous 1 := fun σ =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X K j).mul (isHomogeneous_C _ (σ (ξ j)))
  have h1 : (f₀.map (algebraMap F K)).IsHomogeneous (∑ _σ : L →ₐ[F] K, 1 + 0) := by
    rw [hq, hprod, hc]
    exact (IsHomogeneous.prod _ _ _ fun σ _ => hlin σ).mul (isHomogeneous_C _ c)
  have h2 : (f₀.map (algebraMap F K)).IsHomogeneous (chowDegree I 1) :=
    hfH.rename_isHomogeneous.map _
  rw [h2.inj_right h1 hmap0]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, add_zero]
  exact AlgHom.card F L K

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointEquiv (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (Matrix.toLinearEquiv' h.mat.transpose
      (Matrix.invertibleOfIsUnitDet _ (by rw [Matrix.det_transpose]; exact h.isUnit_det)))

theorem HermNorm.pointEquiv_apply (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.pointEquiv y = h.pointOf y := rfl

theorem hausdorffMeasure_pointOf_preimage_null (h : HermNorm n) {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : μH[d] S = 0) :
    μH[d] {y | WithLp.toLp 2 (h.pointOf y) ∈ S} = 0 := by
  let E : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    h.pointEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let F := LinearMap.toContinuousLinearMap E.symm.toLinearMap
  refine measure_mono_null (t := F '' S) (fun y hy => ⟨E y, hy, ?_⟩) ?_
  · simp [F]
  · exact le_zero_iff.1 ((F.lipschitz.hausdorffMeasure_image_le hd S).trans (by rw [hS, mul_zero]))

theorem frameDeriv_basisFun (j : Fin n) (g : MvPolynomial (Fin n) ℂ) :
    frameDeriv (EuclideanSpace.basisFun (Fin n) ℂ) j g = pderiv j g := by
  simp [frameDeriv, EuclideanSpace.basisFun_apply, PiLp.single_apply, apply_ite C, ite_mul]

theorem finrank_coneTangent_of_jacobian (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ)
    (hf : ∀ k, f k ∈ J) (hs : ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f))
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ coneSet h J) (hsy : eval (h.pointOf y) s ≠ 0)
    (hD : eval (h.pointOf y) (frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f) ≠ 0) :
    finrank ℂ (coneTangent h J y) = I₀.card := by
  set x := h.pointOf y with hx
  let a : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun k j => eval x (pderiv j (f k))

  have hT : coneTangent h J y = (LinearMap.ker a.mulVecLin).comap h.pointEquiv.toLinearMap := by
    ext v
    simp only [coneTangent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, HermNorm.pointEquiv_apply]
    constructor
    · intro hv
      funext k
      simpa [Matrix.mulVec, dotProduct, a] using hv (f k) (hf k)
    · intro hv q hq
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hs q hq)
      have hq0 : eval x q = 0 := hy q hq
      have hf0 : ∀ k, eval x (f k) = 0 := fun k => hy _ (hf k)
      have hder : ∀ j, eval x s * eval x (pderiv j q) = ∑ k, eval x (c k) * a k j := by
        intro j
        have := congrArg (fun P => eval x (pderiv j P)) hc

        simp only [map_sum, pderiv_mul, map_add (f := _), map_mul, hq0, hf0, mul_zero, zero_add] at this
        simpa [a, mul_comm] using this.symm
      have hk : ∀ k, ∑ j, a k j * h.pointOf v j = 0 := fun k => by
        simpa [Matrix.mulVec, dotProduct] using congrFun hv k
      have : eval x s * ∑ j, eval x (pderiv j q) * h.pointOf v j = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, hder, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc, ← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]
      exact (mul_eq_zero.1 this).resolve_left hsy

  let M : Matrix {j // j ∉ I₀} {j // j ∉ I₀} ℂ := Matrix.of fun k j => a k j
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    convert hD using 1
    rw [frameJacobianDet, RingHom.map_det]
    congr 1
    ext k j
    simp [M, a, frameDeriv_basisFun]
  have hsurj : Function.Surjective a.mulVecLin := by
    intro t
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM t
    refine ⟨fun j => if hj : j ∉ I₀ then v ⟨j, hj⟩ else 0, ?_⟩
    rw [← hv]
    funext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ I₀ᶜ) (fun j _ hj => by
      simp only [Finset.mem_compl, not_not] at hj; simp [hj]),
      Finset.sum_subtype I₀ᶜ (p := fun j => j ∉ I₀) (fun j => Finset.mem_compl)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hrank := LinearMap.finrank_range_add_finrank_ker a.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin] at hrank
  rw [hT, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hle : I₀.card ≤ n := by simpa using Finset.card_le_univ I₀
  omega

theorem ConeTangentDim.proof (hDim : ConeKrullDimLe.Statement) (hNull : NullSmaller.Statement)
    (hJac : FrameJacobianGeneric.Statement) : ConeTangentDim.Statement := by
  intro n m h J hJ hm hmn hfin
  have := hJ.isPrime
  rw [ae_restrict_iff' (isClosed_coneSet h J).measurableSet, ae_iff]
  rcases (hDim n m h J hJ hm hmn hfin).lt_or_eq with hlt | heq
  · refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m J hlt))
    exact fun q hq => (Classical.not_imp.1 hy).1 q hq
  · obtain ⟨I₀, f, s, hcard, hf, hsJ, hDJ, hspan⟩ :=
      hJac n m J hJ.isPrime heq (EuclideanSpace.basisFun (Fin n) ℂ)
    set D := frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f
    have hsD : s * D ∉ J := fun h' => (hJ.isPrime.mem_or_mem h').elim hsJ hDJ
    have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {s * D})) < m := by
      rw [← ringKrullDim_eq_of_ringEquiv
          (R := (MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) (Ideal.span {s * D}))
          (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {s * D})),
        Ideal.map_span, Set.image_singleton]
      have hnz : Ideal.Quotient.mk J (s * D) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
        mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      rw [heq] at h1
      by_contra hge
      have h2 : ((m : ℕ) : WithBot ℕ∞) + 1 ≤
          ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J (s * D)}) + 1 := by
        gcongr; exact not_lt.1 hge
      have h3 := h2.trans h1
      exact absurd h3 (by exact_mod_cast (by omega : ¬ m + 1 ≤ m))
    refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m _ hdim))
    obtain ⟨hyC, hyT⟩ := Classical.not_imp.1 hy
    have hsD0 : eval (h.pointOf y) (s * D) = 0 := by
      by_contra hne
      rw [map_mul] at hne
      exact hyT (hcard ▸ finrank_coneTangent_of_jacobian h J I₀ f s hf hspan y hyC
        (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    change eval (h.pointOf y) (a + c * (s * D)) = 0
    rw [map_add (f := _), map_mul, hsD0, mul_zero, add_zero]
    exact hyC a ha

end

end GroundTheory.Heights₂.Heights
end
