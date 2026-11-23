module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets

namespace GoodChartZeroSet

section Lemmas

theorem eval_smul_of_isHomogeneous {τ : Type*} {φ : MvPolynomial τ ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (c : ℂ) (w : τ → ℂ) : eval (c • w) φ = c ^ n * eval w φ :=
  _root_.UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous hφ c w

theorem eval_homogenize {m : ℕ} (f : MvPolynomial (Fin m) ℂ) {D : ℕ} (hD : f.totalDegree ≤ D) (a : Fin m)
    (w : Fin m → ℂ) (hw : w a ≠ 0) :
    eval w (X a * ∑ d ∈ range (D + 1), X a ^ (D - d) * homogeneousComponent d f) =
      w a ^ (D + 1) * eval ((w a)⁻¹ • w) f := by
  have hf : f = ∑ d ∈ range (D + 1), homogeneousComponent d f := by
    conv_lhs => rw [← sum_homogeneousComponent f]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun d _ hd' => ?_
    exact homogeneousComponent_eq_zero (n := d) (φ := f) (by simp at hd'; omega)
  conv_rhs => rw [hf]

  rw [map_mul, map_sum, map_sum, eval_X, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdD : d ≤ D := by simp at hd; omega
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d f), map_mul, map_pow, eval_X]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdD
  rw [Nat.add_sub_cancel_left]
  have hinv : w a ^ d * (w a)⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  linear_combination (-(w a * w a ^ k * eval w (homogeneousComponent d f))) * hinv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem segre_scaleBlock [DecidableEq K] (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (scaleBlock k0 c z) = c • segre z := by
  funext j
  show ∏ k, (if k = k0 then c else 1) * z ⟨k, j k⟩ = c * ∏ k, z ⟨k, j k⟩
  rw [Finset.prod_mul_distrib]
  simp


open Classical in
def linForm {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : MvPolynomial (Fin m) ℂ :=
  ∑ a, C (Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0) * X a

theorem eval_linForm {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : Fin m → ℂ) :
    eval x (linForm σ Ψ) = Ψ (fun i' => x (σ.symm i')) 0 := by
  classical
  rw [linForm]
  have hv : (fun i' => x (σ.symm i')) = ∑ a, x a • fun i' => if σ a = i' then (1 : ℂ) else 0 := by
    rw [pi_eq_sum_univ (fun i' => x (σ.symm i'))]
    exact (Equiv.sum_comp σ _).symm.trans (by simp)
  rw [hv]

  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, eval_C, eval_X]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem exists_segre_smul (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) {c : ℂ} (hc : c ≠ 0) (hK : IsEmpty K → c = 1) :
    ∃ z' ∈ mcPts P, segre z' = c • segre z := by
  classical
  by_cases h : IsEmpty K
  · exact ⟨z, hz, by rw [hK h, one_smul]⟩
  · obtain ⟨k0⟩ := not_isEmpty_iff.1 h
    exact ⟨scaleBlock k0 c z, scaleBlock_mem_zeroLocus P hP k0 hc hz, segre_scaleBlock k0 c z⟩


omit [∀ k, Fintype (ι k)] in
theorem segre_of_isEmpty (hK : IsEmpty K) (z : (Σ k, ι k) → ℂ) (j : (k : K) → ι k) : segre z j = 1 := by
  simp [segre]

end Lemmas

theorem proof : Statement := by
  intro K _ ι _ P e m σ Ψ hP
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [projChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ projChartSet P σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [projChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have ha1 : IsEmpty K → x a = 1 := fun hK => by
    have h := hv (X a - 1) (by
      rintro _ ⟨z, -, -, rfl⟩
      simp [segre_of_isEmpty hK])
    simpa [sub_eq_zero] using h

  have hzero : (x a)⁻¹ • x ∈ zeroSet (segreChartIdeal P σ (σ a)) := by
    intro f hf
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul P hP hz (inv_ne_zero h0)
          (fun hK => by rw [segre_of_isEmpty hK, inv_one])
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [SegreChartZeroSet.proof K ι P m σ (σ a) hP] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul P hP hz' ha ha1
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end GoodChartZeroSet

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u v w

theorem ExistsUnique.of_found (hN : IntNumIsFieldIntersection.Statement.{u})
    (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ExistsUniqueStatement F ι := by
  classical
  exact Numbers.existsUnique hN hUq (IntNumPoint.proof hBase) hBase

theorem ExistsUnique.full (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] : ExistsUniqueStatement F ι :=
  ExistsUnique.of_found IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full F ι

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

namespace GeoNumTarget

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoIsMultiProjPrime {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : NumbersDVR.IsMultiProjPrime P) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P :=
  ⟨hP.isPrime, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι P).2 hP.multiHomog,
    hP.relevant⟩

theorem dvrIsMultiProjPrime {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P) : NumbersDVR.IsMultiProjPrime P :=
  ⟨hP.1, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι P).1 hP.2.1, hP.2.2⟩

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem isIntersectionTheory {F : Type} [Field F] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) :
    IsIntersectionTheory F (fun P n L => I P n L) := by
  constructor
  · intro P hP hdim
    have hd : ringKrullDim (NumbersDVR.MRing ι F ⧸ P) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      (CutRegular.relDim_eq_natCast_iff P 0).mp (by rw [hdim]; rfl)
    have hi : ∀ k, (X ⟨k, (hP.relevant k).choose⟩ : NumbersDVR.MRing ι F) ∉ P :=
      fun k => (hP.relevant k).choose_spec
    rw [hI.1 P ![] (fun k => (hP.relevant k).choose) ⟨geoIsMultiProjPrime hP, hd⟩ hi,
      ← NumbersDVR.IntNumPoint.proof IntNumBase.full F K ι P _ hP hd hi]
    obtain ⟨-, h⟩ := IntNumBase.full F K ι P hP hdim
    rw [h]
    have := hP.isPrime
    simp [resDeg, hP.isPrime]
  · intro P n hP hdim bf bg f g hf hg hfP hgP bs
    have hd := (CutRegular.relDim_eq_natCast_iff P (n + 1)).mp hdim
    have key := hI.2 P n bs (fun k => (bf k : ℤ) - bg k) f g ⟨geoIsMultiProjPrime hP, hd⟩
      ⟨bf, bg, (VocabMultiHomog.proof F K ι f bf).2 hf, (VocabMultiHomog.proof F K ι g bg).2 hg,
        hfP, hgP, fun k => rfl⟩
    refine key.trans ?_
    have hD : ∀ W, NumbersDVR.ratDiv P f g W = ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv P f g W := by
      intro W
      simp only [NumbersDVR.ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply,
        Finsupp.mapRange_apply]
      rw [VocabDivCycle.proof F K ι P f W, VocabDivCycle.proof F K ι P g W]
    simp only [NumbersDVR.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, hD]
    exact (finsum_mul_eq_sum _ _).symm

theorem isFieldIntersection_intNum (p : ℕ) [Fact p.Prime] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := ZMod p) (ι := ι)
      (fun V _ L => NumbersDVR.intNum (ZMod p) V L) :=
  IntNumIsFieldIntersection.full (ZMod p) K ι

end GeoNumTarget


open GeoNumTarget Bridge.GeoNum in
theorem geoNumStatement {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι := by
  classical
  intro p _ I hI V n a hV hpV hproj
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    rw [map_natCast]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have hdim : ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι ⧸ V) =
      ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hproj.2]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this
  have hC : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
    rw [map_natCast]
    exact hpV
  rw [← Bridge.intNum_map_eq_geoNum p n V hV hC hdim a]
  exact (IntNumUnique.full (ZMod p) K ι _ (isIntersectionTheory I hI) _
    (dvrIsMultiProjPrime hproj.1) n ((CutRegular.relDim_eq_natCast_iff _ n).mpr hproj.2) a).symm

end

end GroundTheory.Heights₂.Heights
end
