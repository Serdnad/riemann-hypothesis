module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle003
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Lean.Meta.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.Algebra.CharP.Algebra
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (IsMultiHomog IsArithVar mCoordIdeal secM MRing MRingOver)

noncomputable section

section Values

variable {K : Type} [Field K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ)

end Values

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumbersDVR

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace WeightedDegree

section Localization

variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']


include M₀ in
theorem ringKrullDim_quotient_map_le (I : Ideal (MRing ι R)) :
    ringKrullDim (MRing ι R' ⧸ I.map (algebraMap (MRing ι R) (MRing ι R'))) ≤
      ringKrullDim (MRing ι R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let f : PrimeSpectrum.zeroLocus (R := MRing ι R') (I.map (algebraMap (MRing ι R) (MRing ι R'))) →
      PrimeSpectrum.zeroLocus (R := MRing ι R) I :=
    fun Q ↦ ⟨PrimeSpectrum.comap (algebraMap (MRing ι R) (MRing ι R')) Q.1, by
      have h := Q.2
      simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at h ⊢
      exact Ideal.map_le_iff_le_comap.mp h⟩
  refine Order.krullDim_le_of_strictMono f (Monotone.strictMono_of_injective ?_ ?_)
  · intro Q₁ Q₂ h
    exact Ideal.comap_mono (f := algebraMap (MRing ι R) (MRing ι R')) h
  · intro Q₁ Q₂ h
    apply Subtype.ext
    apply PrimeSpectrum.localization_comap_injective (MRing ι R') (M₀.map (C (σ := Σ k, ι k)))
    exact congrArg Subtype.val h

theorem weightedHomogeneousComponent_map [DecidableEq K] (b : K → ℕ) (y : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) b (map (algebraMap R R') y) =
      map (algebraMap R R') (weightedHomogeneousComponent (blockWeight ι) b y) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp


include M₀ in
theorem isMultiHomogIdeal_map [DecidableEq K] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (algebraMap (MRing ι R) (MRing ι R'))) := by
  classical
  intro z hz b
  obtain ⟨⟨x, m⟩, hxm⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M₀.map (C (σ := Σ k, ι k))) (MRing ι R')).mp hz
  obtain ⟨r, hr, hrm⟩ := Submonoid.mem_map.mp m.2
  have hu : IsUnit (C (algebraMap R R' r) : MRing ι R') :=
    (IsLocalization.map_units R' (⟨r, hr⟩ : M₀)).map C
  have hm : algebraMap (MRing ι R) (MRing ι R') (m : MRing ι R) = C (algebraMap R R' r) := by
    rw [← hrm]
    exact map_C _ _
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, mul_comm, ← weightedHomogeneousComponent_C_mul, mul_comm,
    ← hm, hxm]
  change weightedHomogeneousComponent _ b (map (algebraMap R R') (x : MRing ι R)) ∈ _
  rw [weightedHomogeneousComponent_map]
  exact Ideal.mem_map_of_mem _ (hI x x.2 b)


include M₀ in
theorem cycEval_divCycle_map (P : Ideal (MRing ι R)) (f : MRing ι R)
    (hdisj : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
      Disjoint ((M₀.map (C (σ := Σ k, ι k)) : Submonoid (MRing ι R)) : Set (MRing ι R)) W)
    (n : Ideal (MRing ι R') → ℤ) :
    cycEval (fun W ↦ n (W.map (algebraMap (MRing ι R) (MRing ι R')))) (divCycle P f) =
      cycEval n (divCycle (P.map (algebraMap (MRing ι R) (MRing ι R')))
        (algebraMap (MRing ι R) (MRing ι R') f)) := by
  classical
  set M : Submonoid (MRing ι R) := M₀.map (C (σ := Σ k, ι k)) with hM
  set φ := algebraMap (MRing ι R) (MRing ι R') with hφ
  set J := P ⊔ Ideal.span {f} with hJdef
  have hJ : P.map φ ⊔ Ideal.span {φ f} = J.map φ := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hcorr : ∀ W ∈ J.minimalPrimes, (W.map φ).IsPrime ∧ (W.map φ).comap φ = W := fun W hW ↦
    ⟨IsLocalization.isPrime_of_isPrime_disjoint M _ W hW.1.1 (hdisj W hW),
      IsLocalization.under_map_of_isPrime_disjoint M (MRing ι R') hW.1.1 (hdisj W hW)⟩
  have hmin : ∀ W ∈ J.minimalPrimes, W.map φ ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes := by
    intro W hW
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (W.map φ).comap φ ∈ J.minimalPrimes
    rw [(hcorr W hW).2]
    exact hW
  have hkey : ∀ W ∈ J.minimalPrimes, divCycle P f W = divCycle (P.map φ) (φ f) (W.map φ) := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨hWp', hcomap⟩ := hcorr W hW
    have hrel : IsRelevant (W.map φ) ↔ IsRelevant W := by
      refine forall_congr' fun k ↦ exists_congr fun i ↦ not_congr ?_
      have hX : (X ⟨k, i⟩ : MRing ι R') = φ (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
      rw [hX, ← Ideal.mem_comap, hcomap]
    have hl : ∀ (h₁ : W.IsPrime) (h₂ : (W.map φ).IsPrime),
        @multAt _ _ _ _ J W h₁ = @multAt _ _ _ _ (P.map φ ⊔ Ideal.span {φ f}) (W.map φ) h₂ := by
      intro h₁ h₂
      have := h₂
      unfold multAt
      rw [hJ]
      exact GenericCycleCorresp.length_eq M J W (hdisj W hW)
    unfold divCycle
    by_cases hr : IsRelevant W
    · rw [dite_eq_left ⟨hW, hr⟩, dite_eq_left ⟨hmin W hW, hrel.mpr hr⟩, hl]
    · rw [dite_eq_right (fun h ↦ hr h.2), dite_eq_right (fun h ↦ hr (hrel.mp h.2))]
  have hsupp : ∀ (Q : Ideal (MRing ι R')) (x) (W : Ideal (MRing ι R')),
      divCycle Q x W ≠ 0 → W ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    intro Q x W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  have hsupp0 : ∀ W : Ideal (MRing ι R), divCycle P f W ≠ 0 → W ∈ J.minimalPrimes := by
    intro W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  unfold cycEval
  have hA : (∑ᶠ W, divCycle P f W * n (W.map φ)) =
      ∑ᶠ W ∈ J.minimalPrimes, divCycle P f W * n (W.map φ) := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : divCycle P f W = 0 := by
      by_contra h
      exact hW (hsupp0 W h)
    rw [this, zero_mul]
  have hB : (∑ᶠ W, divCycle (P.map φ) (φ f) W * n W) =
      ∑ᶠ W ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes, divCycle (P.map φ) (φ f) W * n W := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : divCycle (P.map φ) (φ f) W = 0 := by
      by_contra h
      exact hW (hsupp _ _ W h)
    rw [this, zero_mul]
  rw [hA, hB]
  refine finsum_mem_eq_of_bijOn (fun W ↦ W.map φ) ⟨fun W hW ↦ hmin W hW, ?_, ?_⟩ ?_
  · intro W₁ hW₁ W₂ hW₂ h
    rw [← (hcorr W₁ hW₁).2, ← (hcorr W₂ hW₂).2]
    exact congrArg _ h
  · intro W' hW'
    have hW'm := hW'
    rw [hJ, IsLocalization.minimalPrimes_map M] at hW'm
    exact ⟨W'.comap φ, hW'm, IsLocalization.map_under M (MRing ι R') W'⟩
  · intro W hW
    rw [hkey W hW]

end Localization

theorem charZero_fractionRing (O : Type) [CommRing O] [IsDomain O]
    (h : Function.Injective (Int.castRingHom O)) : CharZero (FractionRing O) := by
  apply charZero_of_injective_algebraMap (R := ℤ)
  rw [RingHom.ext_int (algebraMap ℤ (FractionRing O))
    ((algebraMap O (FractionRing O)).comp (Int.castRingHom O))]
  exact (IsFractionRing.injective O (FractionRing O)).comp h

end WeightedDegree

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.injEq, heq_eq_eq, true_and] at h
  subst h; rfl




end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem prod_zpow_single {M : Type*} [CommGroupWithZero M] (f : ι → M) (k₀ : ι) :
    ∏ k, f k ^ ((Pi.single k₀ 1 : ι → ℤ) k) = f k₀ := by
  rw [Finset.prod_eq_single k₀ (fun k _ hk ↦ by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (fun h ↦ absurd (Finset.mem_univ k₀) h), Pi.single_eq_same, zpow_one]

omit [Fintype ι] in
theorem single_cast (k₀ k : ι) : (((Pi.single k₀ 1 : ι → ℕ) k : ℕ) : ℤ) = (Pi.single k₀ 1 : ι → ℤ) k := by
  by_cases h : k = k₀
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

namespace ArithVariety

variable (n : ι → ℕ)


omit [Fintype ι] in
theorem whole_mkF_X_ne_zero (v : Coord n) : (whole (n := n)).mkF (X v) ≠ 0 := fun h ↦
  X_ne_zero v (Ideal.mem_bot.mp (((whole (n := n)).mkF_eq_zero_iff _).mp h))



end ArithVariety

variable (n : ι → ℕ) (k₀ : ι)

def blockAddData : AddBlockData (ArithVariety.whole (n := n)) where
  deg := Pi.single k₀ 1
  size := n k₀
  elt j := (ArithVariety.whole (n := n)).mkF (X ⟨k₀, j⟩)
  elt_deg j := ⟨X ⟨k₀, j⟩, 1, (Pi.single k₀ 1 : ι → ℕ), 0, isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k₀, j⟩,
    isWeightedHomogeneous_one ℤ (coordDeg n), fun k ↦ by simp [single_cast],
    (Ideal.ne_top_iff_one _).mp (ArithVariety.whole (n := n)).isPrime.ne_top,
    by rw [map_one, div_one]⟩
  chart_mem c _ j := by
    rw [ArithVariety.chartPow, prod_zpow_single]
    exact Subring.subset_closure ⟨⟨k₀, j⟩, rfl⟩
  generating c _ := by
    refine ⟨Pi.single (c k₀) 1, fun j ↦ ?_, ?_⟩
    · by_cases h : j = c k₀
      · subst h; rw [Pi.single_eq_same]; exact Subring.one_mem _
      · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _
    · rw [Finset.sum_eq_single (c k₀) (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul])
        (fun h ↦ absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
        ArithVariety.chartPow, prod_zpow_single]
      exact div_self (ArithVariety.whole_mkF_X_ne_zero n _)

def blockForms : ((k : ι) → Fin (n k + 1)) → Fin ((blockAddData n k₀).size + 1) →
    MvPolynomial (Coord n) ℤ :=
  fun c j ↦ chartMonomial c 1 * X ⟨k₀, j⟩

def blockLine : HermLine n where
  deg := Pi.single k₀ 1
  metric z := l2Norm (z k₀)
  metric_pos z hz := vectorL2Norm_pos (hz k₀)
  metric_smul c z _ _ := by
    rw [vectorL2Norm_const_mul, prod_zpow_single (fun k ↦ ‖c k‖) k₀]
  metric_smooth := contDiffOn_l2Norm_block k₀

def blockVal : Coord (blockAddData n k₀).extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => X ⟨k₀, j⟩
  | ⟨some k, i⟩ => X ⟨k, i⟩

def blockSubst :
    MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ →+* MvPolynomial (Option ι) (MvPolynomial (Coord n) ℤ) :=
  eval₂Hom (Int.castRingHom _) fun v ↦ C (blockVal n k₀ v) * X v.1





end

end GroundTheory.Heights₂.Heights
end
