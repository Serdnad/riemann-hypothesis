module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle001
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.Lie.OfAssociative
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem FinrankAdjoinRange.proof : FinrankAdjoinRange.Statement := by
  intro F Φ Ω _ _ _ _ _ _ _ S
  set f := IsScalarTower.toAlgHom F Φ Ω
  set Φ₁ : IntermediateField F Ω := f.fieldRange
  let i : Φ ≃ₐ[F] Φ₁ := AlgEquiv.ofInjectiveField f
  have hi : (algebraMap Φ Ω : Φ → Ω) = (algebraMap Φ₁ Ω) ∘ i := by
    funext x; rfl

  have hres : (IntermediateField.adjoin Φ S).restrictScalars F =
      (IntermediateField.adjoin Φ₁ S).restrictScalars F :=
    IntermediateField.restrictScalars_adjoin_of_algEquiv i hi S

  have hle : Φ₁ ≤ Φ₁ ⊔ IntermediateField.adjoin F S := le_sup_left
  have hext : IntermediateField.extendScalars hle = IntermediateField.adjoin Φ₁ S := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_adjoin_eq_sup]
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext]

  let j : IntermediateField.adjoin Φ S ≃+* IntermediateField.adjoin Φ₁ S :=
    (IntermediateField.equivOfEq hres).toRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv j ?_
  ext x
  rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem RankFracDegree.isFractionRing_of_closure {F Ω A : Type} [Field F] [Field Ω] [Algebra F Ω] [CommRing A]
    (K : IntermediateField F Ω) (f : A →+* Ω) (hf : Function.Injective f) (hK : ∀ a, f a ∈ K)
    (hcl : K.toSubfield ≤ Subfield.closure (Set.range f)) :
    @IsFractionRing A _ K _ (f.codRestrict K hK).toAlgebra := by
  let _ : Algebra A K := (f.codRestrict K hK).toAlgebra
  have hmap : ∀ a, ((algebraMap A K a : K) : Ω) = f a := fun _ => rfl
  have hnz : ∀ a : A, a ∈ nonZeroDivisors A → f a ≠ 0 := by
    intro a ha h0
    have h10 : (1 : A) = 0 :=
      mem_nonZeroDivisors_iff_right.mp ha 1 (by rw [one_mul]; exact hf (by rw [h0, map_zero]))
    exact one_ne_zero (by simpa using congrArg f h10 : (1 : Ω) = 0)
  show IsLocalization (nonZeroDivisors A) K
  rw [isLocalization_iff]
  refine ⟨fun y => IsUnit.mk0 _ fun h => hnz y y.2 (by rw [← hmap, h]; rfl), fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨y, hy, w, hw, hyw⟩ := Subfield.mem_closure_iff.mp (hcl z.2)
    rw [← RingHom.coe_range, Subring.closure_eq] at hy hw
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hw
    by_cases h0 : f a' = 0
    · refine ⟨(0, 1), Subtype.ext ?_⟩
      simp only [OneMemClass.coe_one, map_zero, map_one, mul_one, ZeroMemClass.coe_zero]
      rw [← hyw, h0, div_zero]
    · have ha' : a' ∈ nonZeroDivisors A :=
        mem_nonZeroDivisors_of_injective hf (mem_nonZeroDivisors_of_ne_zero h0)
      refine ⟨(a, ⟨a', ha'⟩), Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, hmap]
      rw [← hyw, div_mul_cancel₀ _ h0]
  · refine ⟨1, ?_⟩
    have hxy : x = y := hf (by rw [← hmap x, ← hmap y, h])
    rw [hxy]

theorem RankFracDegree.proof : RankFracDegree.Statement := by
  intro F Ω A B _ _ _ _ _ _ L₀ L f g hf hg hfg hfL₀ hgL hL₀ hL _
  have hle : L₀ ≤ L := by
    intro x hx
    have h1 : x ∈ Subfield.closure (Set.range g) := by
      refine Subfield.closure_mono ?_ (hL₀ hx)
      rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap A B a, hfg a⟩
    exact (Subfield.closure_le (t := L.toSubfield)).mpr (by rintro _ ⟨b, rfl⟩; exact hgL b) h1
  let L' := IntermediateField.extendScalars hle
  let _ : Algebra A L₀ := (f.codRestrict L₀ hfL₀).toAlgebra
  let _ : Algebra B L' := (g.codRestrict L' hgL).toAlgebra
  let _ : Algebra A L' := ((algebraMap L₀ L').comp (algebraMap A L₀)).toAlgebra
  have _ : IsScalarTower A L₀ L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hfg a).symm
  have _ : IsFractionRing A L₀ := RankFracDegree.isFractionRing_of_closure L₀ f hf hfL₀ hL₀
  have _ : IsFractionRing B L' := RankFracDegree.isFractionRing_of_closure L' g hg hgL hL
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact (IsFractionRing.finrank_eq A L₀ B L').symm

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Module IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace RankAdjoinFrac

theorem finrank_algebraAdjoin_eq_finrank_adjoin {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (T : Set Ω) :
    finrank K (Algebra.adjoin K T) = finrank K (IntermediateField.adjoin K T) := by
  by_cases hT : ∀ x ∈ T, IsAlgebraic K x
  · rw [← IntermediateField.finrank_eq_finrank_subalgebra, adjoin_toSubalgebra_of_isAlgebraic hT]
  · push Not at hT
    obtain ⟨x, hx, hnx⟩ := hT
    have h1 : finrank K (Algebra.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin K T)).algHom (Algebra.adjoin K T).val)
    have h2 : finrank K (IntermediateField.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, subset_adjoin K T hx⟩ : IntermediateField.adjoin K T)).algHom (IntermediateField.adjoin K T).val)
    rw [h1, h2]

theorem exists_mul_mem_of_mem {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) {y : Ω}
    (hy : y ∈ Algebra.adjoin (IntermediateField.adjoin F S) T) :
    ∃ a ∈ Algebra.adjoin F S, a ≠ 0 ∧ a * y ∈ Algebra.adjoin F T := by
  have hST := Algebra.adjoin_mono (R := F) h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_mem _, one_ne_zero, by rw [one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap k =>
    obtain ⟨r, hr, s, hs, hk⟩ := mem_adjoin_iff_div.mp k.2
    by_cases hs0 : s = 0
    · refine ⟨1, one_mem _, one_ne_zero, ?_⟩
      have : (algebraMap (IntermediateField.adjoin F S) Ω k) = 0 := by
        change (k : Ω) = 0
        rw [hk, hs0, div_zero]
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨s, hs, hs0, ?_⟩
      change s * (k : Ω) ∈ _
      rw [hk, mul_div_cancel₀ _ hs0]
      exact hST hr
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x + y) = b * (a * x) + a * (b * y) := by ring
    rw [this]
    exact add_mem (mul_mem (hST hb) hax) (mul_mem (hST ha) hby)
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x * y) = (a * x) * (b * y) := by ring
    rw [this]
    exact mul_mem hax hby

theorem finrank_eq_finrank_algebraAdjoin {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω}
    (h : S ⊆ T) :
    letI := adjoinInclAlgebra F h
    finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
  let _ := adjoinInclAlgebra F h
  let _ : Algebra (Algebra.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    ((algebraMap (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T)).comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S)
      (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hle : Algebra.adjoin F T ≤ (Algebra.adjoin (IntermediateField.adjoin F S) T).restrictScalars F :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := IntermediateField.adjoin F S))
  let f : Algebra.adjoin F T →ₗ[Algebra.adjoin F S] Algebra.adjoin (IntermediateField.adjoin F S) T :=
    { toFun := fun m => ⟨m.1, hle m.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        apply Subtype.ext
        simp only [Algebra.smul_def, RingHom.id_apply, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_inclusion] }
  have : IsLocalizedModule (nonZeroDivisors (Algebra.adjoin F S)) f := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
    · rw [Module.End.isUnit_iff]
      have hx0 : algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (Algebra.adjoin F S) (IntermediateField.adjoin F S))).mpr
          (nonZeroDivisors.coe_ne_zero x)
      refine ⟨fun u v huv => ?_, fun v => ?_⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) u,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) v] at huv
        calc u = (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ •
              (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x • u) := by
                rw [smul_smul, inv_mul_cancel₀ hx0, one_smul]
          _ = v := by rw [huv, smul_smul, inv_mul_cancel₀ hx0, one_smul]
      · refine ⟨(algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ • v, ?_⟩
        rw [Module.algebraMap_end_apply, ← algebraMap_smul (IntermediateField.adjoin F S), smul_smul,
          mul_inv_cancel₀ hx0, one_smul]
    · obtain ⟨a, ha, ha0, hay⟩ := exists_mul_mem_of_mem h y.2
      refine ⟨(⟨a * y, hay⟩, ⟨⟨a, ha⟩, mem_nonZeroDivisors_of_ne_zero ?_⟩), ?_⟩
      · exact fun h0 => ha0 (congrArg Subtype.val h0)
      · apply Subtype.ext
        simp only [Submonoid.smul_def, Algebra.smul_def, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply]
        rfl
    · refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      exact Subtype.ext (congrArg (fun z : Algebra.adjoin (IntermediateField.adjoin F S) T => (z : Ω)) hx)
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (Algebra.adjoin F S)) f le_rfl,
    IsLocalization.finrank_eq (IntermediateField.adjoin F S) (nonZeroDivisors (Algebra.adjoin F S)) le_rfl]

theorem proof : RankAdjoinFrac.Statement := by
  intro F Ω _ _ _ S T h
  have hKL : IntermediateField.adjoin F S ≤ IntermediateField.adjoin F T := adjoin.mono F S T h
  have hE : extendScalars hKL = IntermediateField.adjoin (IntermediateField.adjoin F S) T :=
    restrictScalars_injective F (by
      rw [extendScalars_restrictScalars, adjoin_adjoin_left, Set.union_eq_self_of_subset_left h])
  have key : IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
    rw [relfinrank_eq_finrank_of_le hKL, hE, finrank_algebraAdjoin_eq_finrank_adjoin]
  exact (finrank_eq_finrank_algebraAdjoin h).trans key.symm

end RankAdjoinFrac

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter


open Classical in
theorem LocAwaySpec.proof : LocAwaySpec.Statement := by
  intro R _ Φ _ φ S hrep
  choose f g hg hfg using hrep
  have hE0 : IsUnit (φ (∏ c ∈ S, g c)) := by
    rw [map_prod]
    exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
  refine ⟨∏ c ∈ S, g c, hE0, ?_, ?_⟩
  · intro c hc
    set E := ∏ d ∈ S, g d with hEdef
    have hE : IsUnit (φ E) := by
      rw [hEdef, map_prod]
      exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
    have hunitE : IsUnit (algebraMap R (Localization.Away E) E) :=
      IsLocalization.Away.algebraMap_isUnit E
    have hu : IsUnit (algebraMap R (Localization.Away E) (g c)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hc)) hunitE
    refine ⟨algebraMap R (Localization.Away E) (f c) * ↑hu.unit⁻¹, ?_⟩
    have h1 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit = φ (g c) := by
      rw [IsUnit.unit_spec, IsLocalization.Away.lift_eq]
    have h2 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit⁻¹ = (φ (g c))⁻¹ := by
      rw [← h1, ← map_units_inv]
    rw [map_mul, IsLocalization.Away.lift_eq, h2, ← div_eq_mul_inv]
    exact (hfg c).symm
  · intro B _ ψ hψ hker z hz
    rw [RingHom.mem_ker] at hz ⊢
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (∏ c ∈ S, g c)) z
    have hsφ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hE0 : Localization.Away (∏ c ∈ S, g c) →+* Φ) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, hz, zero_mul] at hsφ
    have ha : ψ a = 0 := hker (RingHom.mem_ker.mpr hsφ.symm)
    have hsψ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hψ :
      Localization.Away (∏ c ∈ S, g c) →+* B) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, ha] at hsψ
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hsu : IsUnit (ψ (s : R)) := by
      rw [← hn, map_pow]
      exact hψ.pow n
    exact (hsu.mul_left_eq_zero).mp hsψ

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

theorem ChartPrimElt.proof : ChartPrimElt.Statement := by
  intro Φ _ _ Φ' _ _ Q _ r hfin
  set L := IntermediateField.adjoin Φ (Set.range r) with hL
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Φ L
  have hint : IsIntegral Φ α := IsIntegral.of_finite Φ α
  have hmemL : ∀ q, r q ∈ L := fun q => IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
  have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
    rintro _ ⟨q, rfl⟩
    exact (IntermediateField.isAlgebraic_iff (x := (⟨r q, hmemL q⟩ : L))).1
      (Algebra.IsAlgebraic.isAlgebraic _)
  have hmem : (α : Φ') ∈ Algebra.adjoin Φ (Set.range r) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact α.2
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  obtain ⟨τ, hτ0⟩ := hmem
  have hτ : MvPolynomial.aeval r τ = (α : Φ') := hτ0
  have hm : minpoly Φ (MvPolynomial.aeval r τ) = minpoly Φ α := by
    rw [hτ]
    exact minpoly.algHom_eq L.val Subtype.val_injective α
  have hg : ∀ q, ∃ p : Φ[X], aeval α p = (⟨r q, hmemL q⟩ : L) := by
    intro q
    have h1 : (⟨r q, hmemL q⟩ : L) ∈ IntermediateField.adjoin Φ ({α} : Set L) := by rw [hα]; trivial
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨p, hp⟩ := h1
    exact ⟨p, hp⟩
  choose g hg using hg
  have hgθ : ∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q := by
    intro q
    rw [hτ, show (α : Φ') = L.val α from rfl, Polynomial.aeval_algHom_apply, hg q]
    rfl
  have hirr : Irreducible (minpoly Φ (MvPolynomial.aeval r τ)) := by
    rw [hm]
    exact minpoly.irreducible hint
  refine ⟨τ, g, ?_⟩
  have hsep : IsCoprime (minpoly Φ (MvPolynomial.aeval r τ))
      (derivative (minpoly Φ (MvPolynomial.aeval r τ))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨b, ?_, hgθ, ⟨-a, by linear_combination hab⟩, ?_, ?_⟩
  · rw [hm]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq Φ α).1 hα
  · apply minpoly.dvd
    have hfun : (fun q => aeval (MvPolynomial.aeval r τ) (g q)) = r := funext hgθ
    rw [map_sub, aeval_X, MvPolynomial.comp_aeval_apply, hfun, sub_self]
  · intro q hq
    have hnd : ¬ minpoly Φ (MvPolynomial.aeval r τ) ∣ g q := by
      rintro ⟨c, hc⟩
      apply hq
      rw [← hgθ q, hc, map_mul, minpoly.aeval, zero_mul]
    obtain ⟨a', b', hab'⟩ := (hirr.coprime_iff_not_dvd).2 hnd
    exact ⟨b', ⟨-a', by linear_combination hab'⟩⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IntermediateField.algebraAdjoinAdjoin

theorem RelAlgClosureFinite.linearIndependent_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) {σ : Type*} {x : σ → L} (hx : AlgebraicIndependent M x)
    {ι : Type*} {m : ι → M} (hm : LinearIndependent K m) :
    LinearIndependent (Algebra.adjoin K (Set.range x)) (fun i => (m i : L)) := by
  rw [linearIndependent_iff'] at hm ⊢
  intro s g hg i hi
  have hp : ∀ j, ∃ p : MvPolynomial σ K, aeval x p = (g j : L) := fun j => by
    have h : (g j : L) ∈ (aeval x : MvPolynomial σ K →ₐ[K] L).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (g j).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hp
  have hP : (∑ j ∈ s, C (m j) * map (algebraMap K M) (p j) : MvPolynomial σ M) = 0 := by
    apply hx.eq_zero_of_aeval_eq_zero
    rw [← hg]

    simp only [map_sum, map_mul, aeval_C, aeval_map_algebraMap, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  have hcoeff : ∀ d, ∀ j ∈ s, AddMonoidAlgebra.coeff (p j) d = 0 := fun d => by
    apply hm s (fun j => AddMonoidAlgebra.coeff (p j) d)
    have := congrArg (AddMonoidAlgebra.coeff · d) hP
    simp only [coeff_sum, coeff_C_mul, coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := MvPolynomial.ext _ _ fun d => by simp [hcoeff d i hi, AddMonoidAlgebra.coeff_zero]
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl

theorem RelAlgClosureFinite.proof : RelAlgClosureFinite.Statement := by
  intro K L _ _ _ S hS
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  set M := algebraicClosure K L
  have hM : AlgebraicIndependent M ((↑) : t → L) := ht.1.algebraicClosure
  set E := IntermediateField.adjoin K (Set.range ((↑) : t → L))
  have halg : Algebra.IsAlgebraic E L := ht.isAlgebraic_field
  have htop : IntermediateField.adjoin E (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin K (S : Set L) := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K (S : Set L) ≤
        (IntermediateField.adjoin E (S : Set L)).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin E _ hy
    exact hle hz
  have hfin : FiniteDimensional E L := by
    have h := IntermediateField.finiteDimensional_adjoin (K := E) (S := (S : Set L))
      fun y _ => (halg.isAlgebraic y).isIntegral
    rw [htop] at h
    exact (IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv.finiteDimensional
  let b := Module.Basis.ofVectorSpace K M
  have hli : LinearIndependent E (fun i => ((b i : M) : L)) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin K (Set.range ((↑) : t → L))) E).1
      (RelAlgClosureFinite.linearIndependent_adjoin M hM b.linearIndependent)
  have : Finite (Module.Basis.ofVectorSpaceIndex K M) := hli.finite
  exact Module.Finite.of_basis b

end GroundTheory.Heights₂.Heights.Inter
end
end
