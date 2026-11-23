module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle066
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

namespace GoodChartModel

theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : projChartIdeal P σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := segre_rel hP.2.1.2.1 Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [projChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0

    simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
    eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by

    simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
    homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

end GoodChartModel

theorem GoodChartModel.proof (hZ : GoodChartZeroSet.Statement) (hD : GoodChartDim.Statement) :
    GoodChartModel.Statement := by
  intro K _ ι _ P e m σ Ψ hP hΨ
  refine ⟨hZ K ι P e m σ Ψ hP.2.1.2.1, fun J hJ => ?_⟩
  have hdim := hD K ι P e m σ Ψ hP J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GoodChartModel.pow_mem hP hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartSet chartLift segre_chartLift chartLift_segre_apply)

theorem ChartDehomIdeal.proof : ChartDehomIdeal.Statement := by
  intro K _ _ ι _ P m σ i hP
  classical
  set Q : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hQ
  set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := Q ⊔ dehomIdeal i with hJ
  set G : Fin m → MvPolynomial (Σ k, ι k) ℂ := fun a => ∏ k, X ⟨k, σ a k⟩ with hG

  have hseg : ∀ f, segreDehom σ i f = dehom i (aeval G f) := by
    intro f
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl

  have hcomap : ((Q.map (dehom i)).radical).comap (dehom i) = J.radical := by
    have hd : (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) = Ideal.Quotient.mk (dehomIdeal i) := rfl
    rw [← Ideal.comap_coe (dehom i), ← Ideal.map_coe (dehom i), Ideal.comap_radical, hd,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

  have hval : ∀ (y : (Σ k, ι k) → ℂ) (f : MvPolynomial (Fin m) ℂ),
      aeval (R := ℂ) y (aeval G f) = aeval (R := ℂ) (fun a => segre y (σ a)) f := by
    intro y f
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext a
    simp [hG, segre]

  have hzero : ∀ y : (Σ k, ι k) → ℂ, y ∈ zeroLocus ℂ J ↔ y ∈ mcPts P ∧ ∀ k, y ⟨k, i k⟩ = 1 := by
    intro y
    constructor
    · intro hy
      have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
        have := hy _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
        simpa [sub_eq_zero] using this
      refine ⟨⟨fun k => ⟨i k, by simp [h1 k]⟩, fun f hf => ?_⟩, h1⟩
      have := hy _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
      exact this
    · rintro ⟨hy, h1⟩
      have hle : J ≤ RingHom.ker (aeval (R := ℂ) y : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by
        refine sup_le ?_ ?_
        · rw [hQ, Ideal.map_le_iff_le_comap]
          intro f hf
          exact hy.2 f hf
        · rw [dehomIdeal, Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          simp [RingHom.mem_ker, h1 k]
      exact fun p hp => hle hp
  ext f
  rw [Ideal.mem_comap, hseg, ← Ideal.mem_comap, hcomap, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    segreChartIdeal, mem_vanishingIdeal_iff, mem_vanishingIdeal_iff]
  constructor
  · intro hf y hy
    rw [hval]
    obtain ⟨hym, h1⟩ := (hzero y).1 hy
    refine hf _ ⟨y, hym, ?_, rfl⟩
    simp [segre, h1]
  · rintro hf x ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have h := Finset.prod_eq_zero (f := fun k => z ⟨k, i k⟩) (Finset.mem_univ k) h0
      exact one_ne_zero ((show segre z i = 1 from hzi).symm.trans h)
    set y := chartLift σ i (fun a => segre z (σ a)) with hy
    have hyz : y = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
      funext p
      rw [hy, chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]
    have hym : y ∈ mcPts P := by
      rw [hyz]
      exact SegreChartZeroSet.scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz
    have h1 : ∀ k, y ⟨k, i k⟩ = 1 := fun k => by
      rw [hyz]
      exact inv_mul_cancel₀ (hne k)
    have := hf y ((hzero y).2 ⟨hym, h1⟩)
    rwa [hval, hy, segre_chartLift σ i z hzi] at this

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk fsLine)

def PtsSemiPosMassFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (N j)) → (∀ j, Inter.IsSemiPosHerm (N j)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) < ⊤

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk oneLine isSmoothHerm_oneLine)

def PtsPosDensIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
      Integrable (ptsPosDens P Ψ (pot L) g)

end GroundTheory.Heights₂.Heights
end
end
