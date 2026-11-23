module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle007
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle076
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle041
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
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KrullDimMatAct

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

def coneAdjoinQ (x : J → Ω) : Subalgebra ℚ (Polynomial Ω) :=
  Algebra.adjoin ℚ (Set.range fun j => Polynomial.C (x j) * Polynomial.X)

theorem mem_coneAdjoinQ_matAct (A : Matrix J J ℚ) (x : J → Ω) (i : J) :
    Polynomial.C (matAct A x i) * Polynomial.X ∈ coneAdjoinQ x := by
  have h : Polynomial.C (matAct A x i) * Polynomial.X =
      ∑ j, A i j • (Polynomial.C (x j) * Polynomial.X) := by

    simp only [matAct, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast, Polynomial.C_mul, mul_assoc]
  rw [h]
  exact Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _

theorem coneAdjoinQ_matAct_le (A : Matrix J J ℚ) (x : J → Ω) :
    coneAdjoinQ (matAct A x) ≤ coneAdjoinQ x :=
  Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => mem_coneAdjoinQ_matAct A x i)

theorem coneAdjoinQ_matAct_eq {B : Matrix J J ℚ} (hB : IsInvMat B) (x : J → Ω) :
    coneAdjoinQ (matAct B x) = coneAdjoinQ x := by
  classical
  obtain ⟨B', _, hB'B⟩ := isInvMat_mul hB
  refine le_antisymm (coneAdjoinQ_matAct_le B x) ?_
  have h := coneAdjoinQ_matAct_le B' (matAct B x)
  rwa [matAct_matAct hB'B] at h

theorem ringKrullDim_quot_coordIdeal (x : J → Ω) :
    ∃ s : ℕ, Algebra.trdeg ℚ (coneAdjoinQ x) = s ∧
      ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x) = (s : WithBot ℕ∞) + 1 := by
  obtain ⟨s, h1, h2⟩ := GroundTheory.Heights₂.Heights.TrdegAdjoin.ringKrullDim_quotient_ker
    (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω)
  have hX : (fun v => (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) (X v)) =
      fun j => Polynomial.C (x j) * Polynomial.X :=
    funext fun v => by simp [coneMap]
  rw [hX] at h1
  exact ⟨s, h1, h2⟩

theorem proof : KrullDimMatAct.Statement := by
  intro Ω _ _ J _ x B hB
  obtain ⟨s, hs, hds⟩ := ringKrullDim_quot_coordIdeal (matAct B x)
  obtain ⟨t, ht, hdt⟩ := ringKrullDim_quot_coordIdeal x
  rw [coneAdjoinQ_matAct_eq hB, ht] at hs
  have hst : s = t := by exact_mod_cast hs.symm
  rw [hds, hdt, hst]

end KrullDimMatAct

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Module

noncomputable section

namespace TwoBlockStepBound

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem relIndex_le_pow {H K : Submodule ℤ Ω} [Module.Finite ℤ K] {N : ℕ} (hN : 0 < N)
    (hNK : ∀ u ∈ K, (N : Ω) * u ∈ H) :
    H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 ∧
      H.toAddSubgroup.relIndex K.toAddSubgroup ≤ N ^ finrank ℤ K := by
  have : Module.Finite ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := ‹Module.Finite ℤ K›
  have : Module.Free ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := Module.free_of_finite_type_torsion_free'
  have key := AddSubgroup.relIndex_map_nsmul N K.toAddSubgroup
  have hsub : K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N) ≤ H.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [nsmul_eq_mul] using hNK y hy
  have hne : (K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N)).relIndex K.toAddSubgroup ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hN.ne'
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hsub h0), ?_⟩
  calc H.toAddSubgroup.relIndex K.toAddSubgroup ≤ _ := AddSubgroup.relIndex_le_of_le_left hsub hne
    _ = N ^ finrank ℤ K := key

theorem pow_mul_mem_sec {x x' : Ix κ → Ω} {M : ℕ} (hM : ∀ s ∈ sec ℤ x' 1, (M : Ω) * s ∈ sec ℤ x 1) :
    ∀ n : ℕ, ∀ s ∈ sec ℤ x' n, (M : Ω) ^ n * s ∈ sec ℤ x n
  | 0, s, hs => by
    rw [sec_zero'] at hs ⊢
    simpa using hs
  | n + 1, s, hs => by
    rw [← sec_mul_sec] at hs ⊢
    induction hs using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      have := Submodule.mul_mem_mul (pow_mul_mem_sec hM n u hu) (hM v hv)
      convert this using 1
      ring
    | add u _ v _ hu hv =>
      rw [mul_add]
      exact add_mem hu hv

theorem exists_finrank_sec_le (hRank : RankOfSections.Statement) {x : Ix κ → Ω} {D : ℕ}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ m : ℕ, 1 ≤ m → (finrank ℤ (sec ℤ x m) : ℝ) ≤ R * (m : ℝ) ^ D := by
  obtain ⟨hqP, hqd⟩ := GenericFibre.proof Ω κ x D hX
  obtain ⟨C, hC⟩ := hRank κ _ D hqP hqd
  set δ : ℝ := (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
    ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ)
  refine ⟨|δ| + |C| * 2 ^ D, by positivity, fun m hm => ?_⟩
  have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
      ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (m : ℤ)) : ℝ) =
      (finrank ℤ (sec ℤ x m) : ℝ) := by exact_mod_cast SectionsRank.proof Ω κ x m
  have h := (abs_le.mp (hC m)).2
  rw [e] at h
  have ht : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) ≤ (m : ℝ) ^ D := by positivity
  have h1 : ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ ((m : ℝ) + 1) ^ D := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((m : ℝ) + 1) ^ D ≤ 2 ^ D * (m : ℝ) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  have h3 : δ * (m : ℝ) ^ D / D.factorial ≤ |δ| * (m : ℝ) ^ D := by
    have hf : (1 : ℝ) ≤ D.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero D)
    rw [div_le_iff₀ (by linarith)]
    calc δ * (m : ℝ) ^ D ≤ |δ| * (m : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self δ) hp
      _ ≤ |δ| * (m : ℝ) ^ D * D.factorial := le_mul_of_one_le_right (by positivity) hf
  have h4 : C * ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ |C| * (2 ^ D * (m : ℝ) ^ D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C))
  nlinarith

end TwoBlockStepBound


open TwoBlockStepBound in
theorem TwoBlockStepBound.proof (hRank : RankOfSections.Statement) : TwoBlockStepBound.Statement := by
  intro D Ω _ _ κ _ x B hX _ _ hsp
  set x' := matAct B x
  obtain ⟨M, hM0, hM⟩ := ChangeOfLatticeNested.exists_mul_mem_sec_one x B
  obtain ⟨R, hR0, hR⟩ := exists_finrank_sec_le hRank hX
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM0)
  refine ⟨R * Real.log M, fun a b => ?_⟩
  have hsp1 : sec ℤ x 1 ≤ sec ℤ x' 1 := by
    rw [sec_one', sec_one']
    exact hsp
  have eH : sec ℤ x (a + 1) * sec ℤ x' b = sec ℤ x a * sec ℤ x' b * sec ℤ x 1 := by
    rw [← sec_mul_sec x a 1, mul_right_comm]
  have eK : sec ℤ x a * sec ℤ x' (b + 1) = sec ℤ x a * sec ℤ x' b * sec ℤ x' 1 := by
    rw [← sec_mul_sec x' b 1, mul_assoc]
  have hKQ : sec ℤ x a * sec ℤ x' (b + 1) ≤ sec ℤ x' (a + b + 1) := by
    rw [add_assoc, ← sec_mul_sec x' a (b + 1)]
    exact mul_le_mul' (ChangeOfLattice.sec_mono hsp a) le_rfl
  have : Module.Finite ℤ (sec ℤ x a * sec ℤ x' (b + 1)) :=
    Module.Finite.iff_fg.mpr ((sec_fg x a).mul (sec_fg x' (b + 1)))
  obtain ⟨hne, hle⟩ := relIndex_le_pow (H := sec ℤ x (a + 1) * sec ℤ x' b)
    (K := sec ℤ x a * sec ℤ x' (b + 1)) hM0 (by rw [eH, eK]; exact mul_mem_of_forall hM _)
  have hMn : ((M : Ω) ^ (a + b + 1)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM0.ne')
  let f := (LinearMap.mulLeft ℤ ((M : Ω) ^ (a + b + 1))).restrict (pow_mul_mem_sec hM (a + b + 1))
  have hf : Function.Injective f := fun s t hst =>
    Subtype.ext (mul_left_cancel₀ hMn (congrArg Subtype.val hst))
  have hrk : finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) ≤ finrank ℤ (sec ℤ x (a + b + 1)) :=
    (Submodule.finrank_mono hKQ).trans (LinearMap.finrank_le_finrank_of_injective hf)
  have hpos : (0 : ℝ) ≤ twoBlockStep x x' a b :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne)
  have ht : ((a + b : ℝ) + 1) = ((a + b + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [abs_of_nonneg hpos, ht]
  unfold twoBlockStep
  calc Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)
      ≤ Real.log ((M ^ finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hne) (by exact_mod_cast hle)
    _ = finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) * Real.log M := by
        push_cast
        rw [Real.log_pow]
    _ ≤ finrank ℤ (sec ℤ x (a + b + 1)) * Real.log M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrk) hlogM
    _ ≤ R * ((a + b + 1 : ℕ) : ℝ) ^ D * Real.log M :=
        mul_le_mul_of_nonneg_right (hR _ (by omega)) hlogM
    _ = R * Real.log M * ((a + b + 1 : ℕ) : ℝ) ^ D := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace FibreNormDehomCharpoly

theorem finiteDimensional_pullField (hR : PullRatiosAlgebraic.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ}
    {L : Fin (D + 1) → MRing ι} (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hB : Birational y) (he : ∀ k, 1 ≤ e k)
    (hL : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    FiniteDimensional (pullField y L) Ω := by
  classical
  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  set P := pullField y L
  set S : Set Ω := {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = y p / y q} with hS
  have hSf : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) => y pq.1 / y pq.2).subset
    (by rintro _ ⟨p, q, -, rfl⟩; exact ⟨(p, q), rfl⟩)
  have : Finite S := hSf.to_subtype
  have hSi : ∀ x ∈ S, IsIntegral P x := by
    rintro _ ⟨p, q, hpq, rfl⟩
    exact (hR K ι Ω y D e L hrel' he hL hz p q hpq).isIntegral
  have hfd : FiniteDimensional P (IntermediateField.adjoin P S) := IntermediateField.finiteDimensional_adjoin hSi
  have htop : IntermediateField.adjoin P S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ blockFnField y := (PullFormsGeneric.blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top
    have hle : blockFnField y ≤ (IntermediateField.adjoin P S).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      exact fun t ht => IntermediateField.subset_adjoin P S ht
    exact hle hx
  have hfd' : FiniteDimensional P (⊤ : IntermediateField P Ω) := htop ▸ hfd
  exact (IntermediateField.topEquiv (F := P) (E := Ω)).toLinearEquiv.finiteDimensional

end FibreNormDehomCharpoly


open FibreNormDehomCharpoly in
theorem FibreNormDehomCharpoly.proof (hG : PullFormsGeneric.Statement) (hR : PullRatiosAlgebraic.Statement)
    (hI : PullSectionIntegral.Statement) (hC : DehomCharpolyForms.Statement) : FibreNormDehomCharpoly.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz
  classical
  have hfin : FiniteDimensional (pullField y L) Ω := finiteDimensional_pullField hR hA hB he hL hz
  refine ⟨hfin, fun τ s hs j hj => ?_⟩
  set l : Fin (D + 1) → Ω := fun i => aeval y (L i) with hl
  have hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0 :=
    hG K ι Ω y D e L hA hB he hL hz
  have hne : ∀ k, l k ≠ 0 := fun k h0 =>
    X_ne_zero (R := ℚ) k (hgen 1 (X k) (isHomogeneous_X ℚ k) (by rw [aeval_X]; exact h0))
  have hint : ∀ k, s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) ∈
      integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω := by
    intro k
    have h : s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) = s / l k ^ (q * τ) := by
      rw [div_pow, div_mul_div_comm, mul_comm (l j ^ (q * τ)), mul_div_mul_right _ _ (pow_ne_zero _ (hne j))]
    rw [h]
    exact hI K ι Ω y D e L q hA hB he hL hz τ s hs k (hne k)
  obtain ⟨c, hc0, hch, hcp, hcn⟩ := hC Ω D l (pullField y L) rfl hgen j (q * τ) (s / l j ^ (q * τ)) hint
  exact ⟨c, ⟨hj, hfin, hc0, hch, hcp⟩, fun hs0 => hcn (div_ne_zero hs0 (pow_ne_zero _ hj))⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem FibreNormGoodPrimeIntegral.proof (hN : PullConeNullModP.Statement) (hD : PullConeDegreeInt.Statement)
    (hI : PullSectionIntegralInt.Statement) (hP : DehomNormPIntegral.Statement) :
    FibreNormGoodPrimeIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz p hp hgood τ s hs j c hc μ
  classical
  obtain ⟨N, M, hpM, hrel⟩ := hN K ι Ω y D L hz p hp hgood
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    obtain ⟨_, ⟨_, _, hrv⟩, _, _⟩ := hA
    obtain ⟨c', hc'⟩ := CoordArithOfFnField.nonzero_of_relevant y hrv
    exact fun k => ⟨c' k, hc' k⟩
  have hM : (M : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hpM (dvd_zero p))
  obtain ⟨hj, hfin, -, hch, hcp⟩ := hc
  have := hfin
  have hint := hI K ι Ω y D e L q N M hy he hL hM (hD K ι Ω y D e L N M hy hL hrel) τ s hs j hj
  have hgen := PullFormsGeneric.proof
    (PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof)
    K ι Ω y D e L hA hB he hL hz
  exact hP Ω D (fun i => aeval y (L i)) (pullField y L) rfl hgen p hp M hpM j (q * τ) _ hint c
    (hch _ le_rfl) hcp μ

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply)

noncomputable section

namespace ShiftIntersectionPolynomial

theorem prod_weights {n : ℕ} (q : ℝ) (s : Fin n → Fin 2) :
    ∏ j, (![q, 1] : Fin 2 → ℝ) (s j) = q ^ (Finset.univ.filter fun j => s j = 0).card := by
  have h : ∀ j, (![q, 1] : Fin 2 → ℝ) (s j) = if s j = 0 then q else 1 := by
    intro j
    rcases Fin.exists_fin_two.mp ⟨s j, rfl⟩ with h | h <;> rw [h] <;> simp
  simp only [h, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]

theorem proof : ShiftIntersectionPolynomial.Statement := by
  intro K _ ι _ II P n A B hII hP hA hB
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ![A, B] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with h | h <;> rw [h] <;> simpa [e]
  refine ⟨∑ s : Fin n → Fin 2, Polynomial.C (II K ι P n (e ∘ s)) *
      Polynomial.X ^ (Finset.univ.filter fun j => s j = 0).card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (fun _ => 0)]
    · rw [Polynomial.coeff_C_mul_X_pow]
      have hc : (Finset.univ.filter fun j : Fin n => (fun _ : Fin n => (0 : Fin 2)) j = 0).card = n := by simp
      rw [if_pos hc.symm]
      rfl
    · intro s _ hs
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro hc
      apply hs
      have hu : (Finset.univ.filter fun j => s j = 0) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [← hc, Fintype.card_fin])
      funext j
      have := Finset.filter_eq_self.mp hu j (Finset.mem_univ j)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q
    set Z := HermLine.zcomb A B (q : ℤ) 1 with hZ_def
    have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hA hB _ _
    have hposition : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        II K ι P n (Function.update L a Z) =
          (![(q : ℝ), 1] : Fin 2 → ℝ) 0 * II K ι P n (Function.update L a (e 0)) +
            (![(q : ℝ), 1] : Fin 2 → ℝ) 1 * II K ι P n (Function.update L a (e 1)) := by
      intro L a hL
      cases n with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hA hB (q : ℤ) 1
        simp only [Int.cast_natCast, Int.cast_one, one_mul] at h
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := II K ι) (P := P) IsSmoothHerm e Z ![(q : ℝ), 1] he hZ hposition
      Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, famExt_apply, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_weights, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

end ShiftIntersectionPolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem isProjVarF_map_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

section Basis

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


end Basis

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
