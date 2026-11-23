module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Sections

theorem exists_section_fibre {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom)
    (y : ↥(pullback X.hom (spMap (IsLocalRing.residue R)))) (hy : IsClosed {y}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) =
      pullback.fst X.hom (spMap (IsLocalRing.residue R)) y := by
  let x₀ := pointOfClosedPoint (pullback.snd X.hom (spMap (IsLocalRing.residue R))) y hy
  obtain ⟨⟨s, hs⟩, e⟩ := GlobalTheory.reducePoint_residue_surjective X.hom R (𝟙 _)
    ⟨x₀ ≫ pullback.fst _ _, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e' : spMap (IsLocalRing.residue R) ≫ s = x₀ ≫ pullback.fst _ _ := congrArg Subtype.val e
  refine ⟨Over.homMk s hs, ?_⟩
  have e2 : s (PrimeSpectrum.comap (IsLocalRing.residue R) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      pullback.fst X.hom (spMap (IsLocalRing.residue R)) (x₀ (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    congr($e' (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)))
  rw [IsLocalRing.comap_closedPoint] at e2
  exact e2.trans (congrArg _ (pointOfClosedPoint_apply _ y hy _))

theorem exists_section_closed {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom) {z : X.left}
    (hz : X.hom z = IsLocalRing.closedPoint R) (hc : IsClosed {z}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst X.hom (spMap (IsLocalRing.residue R))) := by
    rw [GlobalTheory.range_fst_residue]; exact hz
  refine exists_section_fibre X hX y ?_
  have := hc.preimage (pullback.fst X.hom (spMap (IsLocalRing.residue R))).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _
    (pullback.fst X.hom (spMap (IsLocalRing.residue R))).isClosedEmbedding.injective] at this

theorem exists_section_open {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom)
    {U : Set X.left} (hU : IsOpen U) {z : X.left} (hzU : z ∈ U)
    (hz : X.hom z = IsLocalRing.closedPoint R) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst X.hom (spMap (IsLocalRing.residue R))) := by
    rw [GlobalTheory.range_fst_residue]; exact hz
  have : JacobsonSpace ↥(pullback X.hom (spMap (IsLocalRing.residue R))) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd X.hom (spMap (IsLocalRing.residue R)))
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints
    (Z := pullback.fst X.hom (spMap (IsLocalRing.residue R)) ⁻¹' U) ⟨y, hzU⟩
    (hU.preimage (pullback.fst X.hom (spMap (IsLocalRing.residue R))).continuous).isLocallyClosed
  obtain ⟨s, hs⟩ := exists_section_fibre X hX c hc'
  exact ⟨s, hs ▸ hc⟩

theorem exists_section :
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)), Smooth X.hom →
    (∀ z : X.left, IsClosed {z} → X.hom z = IsLocalRing.closedPoint R →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z) ∧
    (∀ U : X.left.Opens, (∃ z ∈ U, X.hom z = IsLocalRing.closedPoint R) →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U) := by
  intro R _ _ _ X hX
  refine ⟨fun z hc hz => exists_section_closed X hX hz hc, ?_⟩
  rintro U ⟨z, hzU, hz⟩
  exact exists_section_open X hX U.isOpen hzU hz

end GlobalTheory.CompanionTheory.Sections
end
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin

theorem integers_valuationRing_dimensionLEOne_isFractionRing :
    ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    ∃ (_ : IsDomain R), ValuationRing R ∧ Ring.DimensionLEOne R ∧ IsFractionRing R C := by
  intro C _ _ v R _ _ hv
  haveI hdom : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI hval : ValuationRing R := ValuationRing.of_integers v hv
  refine ⟨hdom, hval, ⟨?_⟩, ?_⟩
  · intro p hp0 hp
    have hle : IsLocalRing.maximalIdeal R ≤ p := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact p.zero_mem
      obtain ⟨y, hyp, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
      have hxu : ¬ IsUnit x := by
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
      have hvx : v (algebraMap R C x) < 1 :=
        lt_of_le_of_ne (hv.map_le_one x) fun e => hxu (hv.isUnit_iff_valuation_eq_one.2 e)
      have hvy : 0 < v (algebraMap R C y) := by
        rw [zero_lt_iff, Valuation.ne_zero_iff]
        exact fun e => hy0 (hv.hom_inj (by rw [e, map_zero]))
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hvy hvx
      have hdvd : y ∣ x ^ n := by
        rw [hv.dvd_iff_le, map_pow, map_pow]
        exact hn.le
      exact hp.mem_of_pow_mem n (p.mem_of_dvd hdvd hyp)
    have heq : p = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hle
    rw [heq]
    exact IsLocalRing.maximalIdeal.isMaximal R
  · haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hv.hom_inj
    refine IsFractionRing.of_field R C fun z => ?_
    by_cases hz0 : z = 0
    · exact ⟨0, 1, by simp [hz0]⟩
    rcases le_total (v z) 1 with h | h
    · obtain ⟨a, ha⟩ := hv.exists_of_le_one h
      exact ⟨a, 1, by simp [ha]⟩
    · have h' : v z⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ h
      obtain ⟨a, ha⟩ := hv.exists_of_le_one h'
      exact ⟨1, a, by simp [ha]⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.CommAlg.Hens

open Polynomial IsLocalRing

theorem exists_isRoot_of_monic {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C]
    {f : R[X]} (hf : f.Monic) (hd : 0 < f.natDegree) : ∃ r : R, f.IsRoot r := by
  have hinj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  have hdeg : (f.map (algebraMap R C)).degree ≠ 0 := by
    rw [hf.degree_map]
    exact (natDegree_pos_iff_degree_pos.mp hd).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap R C)) hdeg
  have hxa : aeval x f = 0 := by
    rw [aeval_def, ← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral R x := ⟨f, hf, by rw [← aeval_def]; exact hxa⟩
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, hinj ?_⟩
  have hr0 : algebraMap R C (f.eval r) = aeval (algebraMap R C r) f :=
    (aeval_algebraMap_apply_eq_algebraMap_eval r f).symm
  rw [hr0, hxa, map_zero]

theorem exists_root_near {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C] (n : ℕ) :
    ∀ (f : R[X]), f.Monic → f.natDegree = n → ∀ a₀ : R, f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  induction n with
  | zero =>
    intro f hf hn a₀ h
    have : f = 1 := hf.natDegree_eq_zero.mp hn
    subst this
    rw [eval_one] at h
    exact absurd h (Ideal.ne_top_iff_one _ |>.mp (maximalIdeal.isMaximal R).ne_top)
  | succ n ih =>
    intro f hf hn a₀ h
    obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hf (by omega)
    have hfac : (X - Polynomial.C r) * (f /ₘ (X - Polynomial.C r)) = f :=
      mul_divByMonic_eq_iff_isRoot.mpr hr
    have hgm : (f /ₘ (X - Polynomial.C r)).Monic := (monic_X_sub_C r).of_mul_monic_left (hfac.symm ▸ hf)
    have hgd : (f /ₘ (X - Polynomial.C r)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]; rfl
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h with h1 | h1
    · refine ⟨r, hr, ?_⟩
      have := (maximalIdeal R).neg_mem h1
      simpa using this
    · obtain ⟨a, ha, ham⟩ := ih _ hgm hgd a₀ h1
      refine ⟨a, ?_, ham⟩
      rw [IsRoot.def, ← hfac, eval_mul, ha.eq_zero, mul_zero]

theorem henselian_and_residueField_isAlgClosed : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C],
    HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  intro C _ _ R _ _ _ _ _
  refine ⟨⟨fun f hf a₀ h _ => exists_root_near (C := C) _ f hf rfl a₀ h⟩, ?_⟩
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hlift : p ∈ lifts (residue R) :=
    (lifts_iff_coeff_lifts p).mpr fun n => residue_surjective (p.coeff n)
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hp
  have hpos : 0 < q.natDegree := by
    rw [hqd]; exact hirr.natDegree_pos
  obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hqm hpos
  refine ⟨residue R r, ?_⟩
  rw [← hq, eval_map_apply, hr.eq_zero, map_zero]

end GlobalTheory.CompanionTheory.CommAlg.Hens
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ValGeneric

theorem exists_pow_mem_of_ne_zero (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] :
    ∃ π : R, π ≠ 0 ∧ ∀ b : R, b ≠ 0 → ∃ (n : ℕ) (c : R), π ^ n = b * c := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · refine ⟨1, one_ne_zero, fun b hb => ?_⟩
    have hu : IsUnit b := by
      by_contra h
      have hbm : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal b).2 h
      rw [hm] at hbm
      exact hb (by simpa using hbm)
    obtain ⟨u, rfl⟩ := hu
    exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
  · obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    refine ⟨π, hπ0, fun b hb => ?_⟩
    by_cases hu : IsUnit b
    · obtain ⟨u, rfl⟩ := hu
      exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
    have hrad : π ∈ (Ideal.span {b}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨hbJ, hJ⟩
      have hbJ' : b ∈ J := hbJ (Ideal.mem_span_singleton_self b)
      have hJ0 : J ≠ ⊥ := fun h => hb (by simpa [h] using hbJ')
      have hmax := Ring.DimensionLEOne.maximalOfPrime hJ0 hJ
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact hπ
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    exact ⟨n, c, by rw [← hc, mul_comm]⟩

theorem isOpenImmersion_spMap_fraction :
    ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  intro C _ R _ _ _ _ _ _
  obtain ⟨π, hπ0, h⟩ := exists_pow_mem_of_ne_zero R
  have inj := IsFractionRing.injective R C
  haveI : IsLocalization.Away π C := by
    refine IsLocalization.Away.mk π ?_ ?_ ?_
    · exact ((map_ne_zero_iff _ inj).2 hπ0).isUnit
    · intro s
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
      obtain ⟨n, c, hc⟩ := h b (nonZeroDivisors.ne_zero hb)
      refine ⟨n, a * c, ?_⟩
      have hb' : algebraMap R C b ≠ 0 :=
        (map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero hb)
      rw [← map_pow, hc, map_mul, map_mul]
      field_simp
    · intro a b hab
      exact ⟨0, by rw [inj hab]⟩
  exact IsOpenImmersion.of_isLocalization π

end GlobalTheory.CompanionTheory.ValGeneric
end
