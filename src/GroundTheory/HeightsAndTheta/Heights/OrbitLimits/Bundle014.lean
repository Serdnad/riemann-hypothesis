module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace CoordRatioDeg

def ratioField {S M : Type*} [Field M] [CharZero M] (R : S → S → Prop) (z : S → M) : IntermediateField ℚ M :=
  IntermediateField.adjoin ℚ {t | ∃ p q, R p q ∧ t = z p / z q}

theorem ratioField_map {S M N : Type*} [Field M] [CharZero M] [Field N] [CharZero N] (R : S → S → Prop)
    (z : S → M) (f : M →ₐ[ℚ] N) : (ratioField R z).map f = ratioField R (f ∘ z) := by
  rw [ratioField, IntermediateField.adjoin_map, ratioField]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp⟩
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp⟩

theorem ratioField_congr {S M : Type*} [Field M] [CharZero M] {R : S → S → Prop} {z w : S → M}
    (h : ∀ p q, R p q → z p / z q = w p / w q) : ratioField R z = ratioField R w := by
  unfold ratioField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, h p q hpq⟩
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, (h p q hpq).symm⟩

theorem proof : CoordRatioDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y Φ' _ _ x' hv hker
  let I : Ideal (MRing ι') := mCoordIdeal y
  let L := FractionRing (MvPolynomial K' Ω)
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K' Ω) L)
  have h₁ : ∀ a ∈ I, (aeval x' : MRing ι' →ₐ[ℤ] Φ').toRingHom a = 0 := fun a ha => by
    rw [show I = _ from hker.symm] at ha
    exact RingHom.mem_ker.mp ha
  have h₂ : ∀ a ∈ I, (mConeMap y).toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp ha
  let g₁ : MRing ι' ⧸ I →+* Φ' := Ideal.Quotient.lift I _ h₁
  have hg₁ : Function.Injective g₁ :=
    RingHom.lift_injective_of_ker_le_ideal I h₁ fun a ha => by
      change a ∈ mCoordIdeal y
      rw [← hker]
      exact ha
  let g₂ : MRing ι' ⧸ I →+* L := (algebraMap _ L).comp (Ideal.Quotient.lift I _ h₂)
  have hg₂ : Function.Injective g₂ :=
    (IsFractionRing.injective _ L).comp (RingHom.lift_injective_of_ker_le_ideal I h₂ fun a ha => ha)
  have : IsDomain (MRing ι' ⧸ I) := hg₁.isDomain g₁
  let F := FractionRing (MRing ι' ⧸ I)
  let f₁ : F →+* Φ' := IsFractionRing.lift hg₁
  have : CharZero F := ⟨fun m n h => by
    have h' := congrArg f₁ h
    rw [map_natCast, map_natCast] at h'
    exact_mod_cast h'⟩
  let f₂ : F →+* L := IsFractionRing.lift hg₂
  let xb : (Σ k', ι' k') → F := fun p => algebraMap _ F (Ideal.Quotient.mk I (X p))
  have e₁ : f₁.toRatAlgHom ∘ xb = x' := funext fun p => by
    simp [xb, f₁, g₁, IsFractionRing.lift_algebraMap]
  have e₂ : ∀ p, f₂ (xb p) = algebraMap _ L (C (y p) * X p.1) := fun p => by
    simp [xb, f₂, g₂, IsFractionRing.lift_algebraMap, mConeMap]
  let c : Ω →ₐ[ℚ] L := ((algebraMap (MvPolynomial K' Ω) L).comp C).toRatAlgHom
  have hT : ∀ k, algebraMap (MvPolynomial K' Ω) L (X k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (X_ne_zero k)
  have hr : ∀ p q : Σ k', ι' k', p.1 = q.1 → f₂ (xb p) / f₂ (xb q) = c (y p) / c (y q) := by
    intro p q h
    rw [e₂, e₂, h, map_mul, map_mul, mul_div_mul_right _ _ (hT _)]
    rfl
  change IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (x' ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) x') =
    IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (y ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) y)
  rw [← IntermediateField.relfinrank_map_map _ _ c, ratioField_map, ratioField_map, ← e₁,
    Function.comp_assoc, ← ratioField_map, ← ratioField_map,
    IntermediateField.relfinrank_map_map,
    ← IntermediateField.relfinrank_map_map _ _ f₂.toRatAlgHom, ratioField_map, ratioField_map]
  congr 1
  · refine ratioField_congr fun p q h => ?_
    simpa using hr (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h])
  · exact ratioField_congr fun p q h => by simpa using hr p q h

end CoordRatioDeg

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets

namespace SegreChartZeroSet

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem scaleAll_mem (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : (fun p => c p.1 * z p) ∈ mcPts P := by
  have key : ∀ s : Finset K,
      (fun p : Σ k, ι k => (if p.1 ∈ s then c p.1 else 1) * z p) ∈ mcPts P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hz
    | insert k s hk ih =>
      have h := scaleBlock_mem_zeroLocus P hP k (hc k) ih
      convert h using 1
      funext ⟨j, a⟩
      by_cases hpk : j = k
      · subst j
        simp [scaleBlock, hk]
      · simp [scaleBlock, hpk]
  simpa using key Finset.univ

def liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (f : MRing ι) :
    MvPolynomial (Fin m) ℂ :=
  eval₂ (algebraMap ℤ (MvPolynomial (Fin m) ℂ)) (fun p => X (σ.symm (Function.update i p.1 p.2))) f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ)
    (f : MRing ι) :
    eval x (liftPoly σ i f) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) := by
  rw [liftPoly, hom_eval₂, eval_map]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp [chartLift]

end Lemmas

theorem proof : Statement := by
  intro K _ ι _ P m σ i hP
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ segreChartSet P σ i, eval y q = 0) → eval x q = 0 :=
      fun q hq => hx q (by rw [segreChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ P, eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      rw [← eval_liftPoly]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPoly]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (scaleAll_mem P hP (fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

end SegreChartZeroSet

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem GenFibreChartDeg.isMultiHomogIdeal_ker_rat {K' : Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (x' : (Σ k', ι' k') → Ω)
    (h : IsMultiHomogIdeal (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω)) := by
  have hmap : ∀ g : MRing ι', aeval x' (qmap g) = aeval x' g := fun g => by
    rw [qmap, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have hker : RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω) =
      (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
    apply le_antisymm
    · intro f hf
      obtain ⟨N, hN, g, hg⟩ := exists_int_mul_eq_qmap f
      have hg0 : g ∈ RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) := by
        rw [RingHom.mem_ker, ← hmap, ← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]
      have hmem : (N : MRingOver ℚ ι') * f ∈ (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
        rw [hg]
        exact Ideal.mem_map_of_mem _ hg0
      have hu : IsUnit (N : MRingOver ℚ ι') := by
        rw [show (N : MRingOver ℚ ι') = C (N : ℚ) by simp]
        exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C
      have h2 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MRingOver ℚ ι') hmem
      rwa [← mul_assoc, hu.val_inv_mul, one_mul] at h2
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hmap]
      exact RingHom.mem_ker.mp hg
  rw [hker]
  obtain ⟨T, hT, hTe⟩ := h
  refine ⟨qmap '' T, ?_, by rw [hTe, Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ f hm) k⟩

theorem GenFibreChartDeg.proof (hT : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement)
    (hC : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement) : GenFibreChartDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G _ c i hv hP hc hi
  have : CharZero G.Φ := (algebraMap G.Φ G.Φ').charZero
  have hx'0 : ∀ k, G.x' (v ⟨k, c k⟩) ≠ 0 := fun k => by
    rw [G.compat]
    exact (map_ne_zero _).2 (hc k)

  have hex : ∀ k', ∃ j : ι' k', G.x' ⟨k', j⟩ ≠ 0 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      have key : ∀ q : Σ k', ι' k', q.1 = κ k → G.x' q ≠ 0 → ∃ j : ι' (κ k), G.x' ⟨κ k, j⟩ ≠ 0 := by
        rintro ⟨a, j⟩ rfl h
        exact ⟨j, h⟩
      exact key _ (hv.2.2.1 _) (hx'0 k)
    · exact ⟨i ⟨k', hk⟩, hi ⟨k', hk⟩⟩
  choose i' hi' using hex

  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom ℚ G.Φ G.Φ').fieldRange
  let F₁ := blockFnField G.x'
  let F₀ := blockFnField (G.x' ∘ v)
  let E := IntermediateField.adjoin ℚ (Set.range t)
  let S := Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩
  have hF : ∀ p q : Σ k', ι' k', p.1 = q.1 → G.x' p / G.x' q ∈ F₁ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF0 : ∀ p q : Σ k, ι k, p.1 = q.1 → G.x' (v p) / G.x' (v q) ∈ F₀ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF01 : F₀ ≤ F₁ := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨p, q, h, rfl⟩
    exact hF (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h]))
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩

  have hchart : ∀ k, ∃ p₀ : Σ k, ι k, p₀.1 = k ∧ v p₀ = ⟨κ k, i' (κ k)⟩ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    exact ⟨p₀, hv.1 ((hv.2.2.1 p₀).symm.trans (congrArg Sigma.fst h)), h⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, -, h⟩ := hchart k
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hrat : ∀ p : Σ k, ι k, G.x' (v p) / t p.1 ∈ F₀ := fun p => by
    obtain ⟨p₀, h1, h⟩ := hchart p.1
    show G.x' (v p) / G.x' ⟨κ p.1, i' (κ p.1)⟩ ∈ F₀
    rw [← h]
    exact hF0 p p₀ h1.symm

  have hΦ₁ : F₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨p, q, -, rfl⟩
      show G.x' (v p) / G.x' (v q) ∈ Φ₁
      rw [G.compat, G.compat]
      exact div_mem (hmem _) (hmem _)
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ F₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          rw [← div_mul_cancel₀ (G.x' (v q)) (hi' (κ q.1))]
          exact mul_mem ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hrat q))
            ((le_sup_right : E ≤ F₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom ℚ G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ F₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)

  have hΦS : Φ₁ ⊔ IntermediateField.adjoin ℚ S = F₁ ⊔ E := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [← hΦ₁]
      exact sup_le_sup_right hF01 E
    · refine (IntermediateField.adjoin_le_iff.2 ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      by_cases ha : a ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := ha
        obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, l⟩ ⟨k, rfl⟩
        have hpq : p.1 = q.1 := hv.1 ((hv.2.2.1 p).symm.trans
          ((congrArg Sigma.fst hp).trans ((congrArg Sigma.fst hq).symm.trans (hv.2.2.1 q))))
        rw [← hp, ← hq]
        exact (le_sup_left : Φ₁ ≤ _) (hΦ₁.le ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hF0 p q hpq)))
      · rw [← div_div_div_cancel_right₀ (hi ⟨a, ha⟩) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
        refine (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (div_mem ?_ ?_)
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, l⟩, rfl⟩
    · rw [← hΦ₁]
      exact le_sup_right.trans le_sup_left

  have hy : IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) = F₁ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      rw [← div_div_div_cancel_right₀ (hi' a) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
      exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨a, j⟩, rfl⟩)
        (IntermediateField.subset_adjoin _ _ ⟨⟨a, l⟩, rfl⟩)
  have hker := GenFibreChartDeg.isMultiHomogIdeal_ker_rat G.x' (by rw [G.genericFibre_ker_target]; exact hP)
  have hindep : AlgebraicIndependent F₁ t := by
    have key : ∀ L : IntermediateField ℚ G.Φ', L = F₁ → AlgebraicIndependent L t →
        AlgebraicIndependent F₁ t := by
      rintro L rfl h
      exact h
    exact key _ hy ((hT ℚ G.Φ' K' ι' G.x' i' hi' hker).comp κ hv.1)

  refine (GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof ℚ G.Φ G.Φ' S).trans ?_
  change IntermediateField.relfinrank Φ₁ (Φ₁ ⊔ IntermediateField.adjoin ℚ S) = _
  rw [hΦS, ← hΦ₁]
  exact hC ℚ G.Φ' F₀ F₁ K t hF01 hindep

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter

theorem chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := fun _ hs c hc =>
  (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩))

theorem MoriwakiBigCurve.proof (hL : CurveCountLower.Statement)
    (hPk : HilbertSamuel.SmallPacking.Statement) : MoriwakiBigCurve.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII hP hB _ hS hC _ _
  set Q := IsSmallH (mCoordIdeal y) y A
  set La := chartLat y A.a
  set T := II K ι (mCoordIdeal y) (0 + 1) (fun _ => A)
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII hP hB hS.1 hC
  obtain ⟨C', hC'⟩ := (hPk K ι Ω y 0 A La hP hB hS.1 fun τ => chartLat_le_chartLatNm y A.a τ).2
  have h0 : ∀ τ, 0 ≤ smallSectionCount Q La τ := fun τ => Real.log_natCast_nonneg _
  have hf : (fun k : ℕ => smallSectionCount Q La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (0 + 1) / ((0 + 1).factorial : ℝ))) =
      fun k : ℕ => smallSectionCount Q La k / k := by
    funext k
    simp
  unfold arVolP
  rw [hf]
  have hC'0 : 0 ≤ C' := by simpa using (h0 0).trans (hC' 0)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun k : ℕ => smallSectionCount Q La k / k := by
    refine ⟨2 * C', eventually_map.mpr ((eventually_ge_atTop 1).mono fun k hk => ?_)⟩
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    show smallSectionCount Q La k / k ≤ 2 * C'
    rw [div_le_iff₀ (by linarith)]
    have h1 : smallSectionCount Q La k ≤ C' * ((k : ℝ) + 1) := by simpa using hC' k
    nlinarith
  refine le_of_forall_sub_le fun ε hε => le_limsup_of_frequently_le ?_ hbdd
  refine Eventually.frequently ((eventually_ge_atTop (⌈C / ε⌉₊ + 1)).mono fun k hk => ?_)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_left 1 _).trans hk
  have hkC : C ≤ ε * k := by
    have h1 : C / ε ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hk)
    rwa [div_le_iff₀ hε, mul_comm] at h1
  have hτ : (k : ℝ) * T - C ≤ smallSectionCount Q La k := hC k ((Nat.le_add_left 1 _).trans hk)
  rw [le_div_iff₀ (by linarith)]
  show (T - ε) * k ≤ _
  nlinarith

end GroundTheory.Heights₂.Heights.Targets
end
