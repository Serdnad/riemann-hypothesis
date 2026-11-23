module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory

theorem exists_intCast_mem_of_isMaximal (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R]
    (m : Ideal R) [m.IsMaximal] : ∃ p : ℤ, p ≠ 0 ∧ algebraMap ℤ R p ∈ m := by
  let := Ideal.Quotient.field m
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ _
  by_contra h
  push Not at h
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ m)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply h a ha0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  have hF : IsField ℤ :=
    (Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (R ⧸ m))
  exact Int.not_isField hF

theorem exists_horizontal_prime_le_of_isMaximal :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [CharZero R] (𝔪 : Ideal R),
      𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ q : Ideal R, q.IsPrime ∧ q ≤ 𝔪 ∧ g ∉ q ∧
        CharZero (R ⧸ q) ∧ Algebra.IsAlgebraic ℤ (R ⧸ q) := by
  intro R _ _ _ _ m hm g hg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨p₀, hp₀, hp₀m⟩ := exists_intCast_mem_of_isMaximal R m
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (m.comap (algebraMap ℤ R))).principal
  have hp' : m.comap (algebraMap ℤ R) = Ideal.span {p} := hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have : p₀ ∈ m.comap (algebraMap ℤ R) := hp₀m
    rw [hp'] at this
    exact hp₀ (by simpa using this)
  have hpprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    infer_instance
  have hpm : algebraMap ℤ R p ∈ m := by
    have : p ∈ m.comap (algebraMap ℤ R) := hp' ▸ Ideal.mem_span_singleton_self p
    exact this
  set x : R := algebraMap ℤ R p * g with hx
  have hx0 : x ≠ 0 := mul_ne_zero (by simpa using hp0) hg
  obtain ⟨q, ⟨hqp, hqm, hxq⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ q ≤ m ∧ x ∉ q}
    ⟨⊥, Ideal.isPrime_bot, bot_le, by simpa using hx0⟩
  change Ideal R at q
  have hpq : algebraMap ℤ R p ∉ q := fun h => hxq (q.mul_mem_right _ h)
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ q)) := by
    have hq' : (q.comap (algebraMap ℤ R)).IsPrime := inferInstance
    have hbot : q.comap (algebraMap ℤ R) = ⊥ := by
      by_contra hne
      have hM : (q.comap (algebraMap ℤ R)).IsMaximal := IsPrime.to_maximal_ideal hne
      have := hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono (f := algebraMap ℤ R) hqm)
      apply hpq
      have h2 : p ∈ q.comap (algebraMap ℤ R) := this ▸ hpm
      exact h2
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ q.comap (algebraMap ℤ R) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      simpa using ha
    rwa [hbot, Ideal.mem_bot] at this
  have hsurj := Ideal.Quotient.mk_surjective (I := q)
  refine ⟨q, hqp, hqm, fun h => hxq (q.mul_mem_left _ h), charZero_of_injective_algebraMap hinj, ?_⟩
  have hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have hcm : (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have h1 : (m.map (Ideal.Quotient.mk q)).height ≤ 1 := by
    refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q x)
      (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq) ?_
    intro P hP hP0 hPm
    by_contra hxP
    refine hmax (P.comap (Ideal.Quotient.mk q)) ⟨inferInstance, ?_, hxP⟩ ?_
    · exact hcm ▸ Ideal.comap_mono hPm
    · refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact P.zero_mem
      · intro e
        apply hP0
        rw [eq_bot_iff]
        intro b hb
        obtain ⟨a, rfl⟩ := hsurj b
        have : a ∈ q := e ▸ hb
        exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have : Algebra.QuasiFiniteAt ℤ (m.map (Ideal.Quotient.mk q)) :=
    quasiFiniteAt_of_height_le_one _ h1 p (fun e => hp0 (hinj (by simpa using e)))
      (Ideal.mem_map_of_mem _ hpm)
  have : FaithfulSMul ℤ (R ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact isAlgebraic_of_quasiFiniteAt ℤ (R ⧸ q) (m.map (Ideal.Quotient.mk q))

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncComponents

theorem fromSpecStalk_mem_zeroLocus_iff {Y : Scheme.{0}} (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1)
    (f : Γ(Y, U.1)) (q : PrimeSpectrum (Y.presheaf.stalk x)) :
    Y.fromSpecStalk x q ∈ Y.zeroLocus {f} ↔ Y.presheaf.germ U.1 x hx f ∈ q.asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have e : Y.fromSpecStalk x q =
      hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [Scheme.mem_zeroLocus_iff, e]
  simp only [Set.mem_singleton_iff, forall_eq]
  have h := hU.fromSpec_preimage_basicOpen f
  have h2 : hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) ∈ Y.basicOpen f ↔
      PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ PrimeSpectrum.basicOpen f :=
    iff_of_eq (congrArg (fun V => PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ V) h)
  exact (not_congr h2).trans not_not

theorem effCartier_of_mem_comps {Y : Scheme.{0}} [IsNoetherian Y] {Z : Y.IdealSheafData}
    (hZ : FinalTheorems.Snc Z) (C : Closeds Y) (hC : (C : Set Y) ∈ comps (Z.support : Set Y)) :
    FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C) := by
  refine effCartier_of_stalkId _ fun x => ?_
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hZ x
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have hO' := hO _ hC
  have hq : ∀ q : PrimeSpectrum (Y.presheaf.stalk x), Y.fromSpecStalk x q ∈ (C : Set Y) ↔
      ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C ∧
        Y.presheaf.germ U.1 x hx (f i) ∈ q.asIdeal := by
    intro q
    have hqO : Y.fromSpecStalk x q ∈ (O : Set Y) := by
      have h : Y.fromSpecStalk x q ∈ Set.range (Y.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at h
      exact Specializes.mem_open h O.isOpen hxO
    have h := Set.ext_iff.1 hO' (Y.fromSpecStalk x q)
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
      fromSpecStalk_mem_zeroLocus_iff U x hx] at h
    exact h
  have hCC : C.compl.compl = C := SetLike.coe_injective (compl_compl _)
  by_cases hb : ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C
  · obtain ⟨i, hi, hbi⟩ := hb
    have hp : Prime (Y.presheaf.germ U.1 x hx (f i)) :=
      prime_of_regular_params (fun i => Y.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 i
    haveI : IsDomain (Y.presheaf.stalk x) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
    refine ⟨_, mem_nonZeroDivisors_of_ne_zero hp.ne_zero, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x
      (Y.presheaf.germ U.1 x hx (f i)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨i, hi, hbi, h⟩⟩)
        rintro ⟨j, hj, hbj, h⟩
        by_cases hij : i = j
        · exact hij ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hi hj hij hbi hbj)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  · refine ⟨1, one_mem _, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x 1 fun q => by
      refine not_congr ((hq q).trans ⟨?_, fun h => ?_⟩)
      · rintro ⟨j, hj, hbj, -⟩
        exact absurd ⟨j, hj, hbj⟩ hb
      · exact absurd ((Ideal.eq_top_iff_one _).2 h) q.isPrime.ne_top
    rw [hCC] at h
    rw [h, Ideal.span_singleton_one, Ideal.radical_top]

theorem exists_compList_effCartier (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p] [QuasiCompact p] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) :
    ∃ (m : ℕ) (C : Fin m → Closeds Y), FinalTheorems.CompList (B : Set Y) C ∧
      ∀ i, FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal (C i)) := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian Y := {}
  haveI : Finite (comps (B : Set Y)) := (comps_finite _).to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (comps (B : Set Y))
  refine ⟨m, fun i => ⟨(e.symm i).1, isClosed_of_mem_comps B.isClosed (e.symm i).2⟩,
    ⟨fun i => (e.symm i).2.1.1, ?_, fun i j hij => ?_⟩, fun i => ?_⟩
  · conv_rhs => rw [← sUnion_comps (B : Set Y), Set.sUnion_eq_iUnion]
    exact e.symm.surjective.iUnion_comp (fun c => (c.1 : Set Y))
  · have hi : Maximal (fun C => IsIrreducible C ∧ C ⊆ (B : Set Y)) (e.symm i).1 := (e.symm i).2
    exact e.symm.injective (Subtype.ext (Set.Subset.antisymm hij (hi.2 (e.symm j).2.1 hij)))
  · refine effCartier_of_mem_comps hB _ ?_
    have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set Y) = B := by simp
    rw [hs]
    exact (e.symm i).2

end GlobalTheory.SncComponents
end
