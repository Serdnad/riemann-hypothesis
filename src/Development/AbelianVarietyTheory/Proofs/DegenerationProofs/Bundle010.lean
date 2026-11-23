module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle004
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle004
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle006
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Module
open TensorProduct

namespace GlobalTheory

namespace GenericFreeness

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem IsBasisAway.exists_basis_apply_eq {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) :
    ∃ b : Module.Basis s (Localization.Away a) (Localization.Away a ⊗[R] M),
      ∀ x : s, b x = 1 ⊗ₜ (x : M) := by
  let f := TensorProduct.mk R (Localization.Away a) M 1
  refine ⟨Module.Basis.mk (v := f ∘ fun x : s => (x : M))
    (LinearIndependent.of_isLocalizedModule (Localization.Away a) (.powers a) f h.linearIndepOn)
    ?_, fun x => Module.Basis.mk_apply _ _ x⟩
  intro y _
  induction y with
  | add y z hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | tmul c m =>
    obtain ⟨n, hn⟩ := h.2.2 m trivial
    rw [bot_sup_eq] at hn
    have h1 := Submodule.mem_map_of_mem (f := f) hn
    rw [Submodule.map_span] at h1
    have h2 := Submodule.span_subset_span R (Localization.Away a) _ h1
    obtain ⟨u, hu⟩ :=
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).pow n).exists_left_inv
    have e : c ⊗ₜ[R] m = (c * u) • f (a ^ n • m) := by
      simp only [f, TensorProduct.mk_apply, ← smul_tmul, smul_tmul', smul_eq_mul,
        Algebra.smul_def, map_pow, mul_one, mul_assoc, hu]
    rw [e, Set.range_comp, Subtype.range_coe]
    exact Submodule.smul_mem _ _ h2

theorem IsBasisAway.one_tmul_ne_zero {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) (K : Type*) [CommRing K] [Nontrivial K]
    [Algebra R K] (ha : IsUnit (algebraMap R K a)) {x : M} (hx : x ∈ s) :
    (1 : K) ⊗ₜ[R] x ≠ 0 := by
  obtain ⟨b, hb⟩ := h.exists_basis_apply_eq
  letI : Algebra (Localization.Away a) K := (IsLocalization.Away.lift a ha).toAlgebra
  haveI : IsScalarTower R (Localization.Away a) K :=
    .of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq a ha r).symm
  have := ((b.baseChange K).map (AlgebraTensorModule.cancelBaseChange R _ K K M)).ne_zero ⟨x, hx⟩
  simpa [hb] using this

end GenericFreeness

open GenericFreeness

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {A₀ : Type*} [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
  {A : Type*} [CommRing A] [Algebra R A] (φ : A₀ →ₐ[R] A)

theorem exists_pow_smul_ker_eq_zero_of_dense {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ y : A₀, φ y = 0 → ∃ n : ℕ, a ^ n • y = 0 := by
  haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R A₀
  let J : Ideal A₀ := RingHom.ker φ
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_of_finiteType (R := R) (A := A₀) J
  obtain ⟨b, hb0, hb⟩ := exists_hasBasisAway_quotient R A₀ A₀ J (IsNoetherian.noetherian J)
  have ha1 := HasBasisAway.map (a := a) (J.subtype.restrictScalars R) ⊥ (by
    have : Submodule.comap (J.subtype.restrictScalars R) ⊥ = ⊥ :=
      LinearMap.ker_eq_bot.2 Subtype.val_injective
    rwa [this])
  have e : (⊥ : Submodule R A₀) ⊔ LinearMap.range (J.subtype.restrictScalars R) =
      J.restrictScalars R := by
    rw [bot_sup_eq]
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [e] at ha1
  obtain ⟨s, hs⟩ := ha1.of_dvd (dvd_mul_right a b)
  obtain ⟨t, ht⟩ := hb.of_dvd (dvd_mul_left b a)
  have hst := hs.union bot_le le_top ht
  have hab := mul_ne_zero ha0 hb0
  obtain ⟨x, hxD, hxa⟩ := hD.exists_mem_open (PrimeSpectrum.basicOpen (a * b)).isOpen
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hab⟩
  have hu : IsUnit (algebraMap R x.asIdeal.ResidueField (a * b)) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hxa
  obtain rfl : s = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
    refine hst.one_tmul_ne_zero _ hu (Or.inl hy) (h x hxD ?_)
    have : φ y = 0 := hs.1 hy
    rw [Algebra.TensorProduct.map_tmul, this, tmul_zero, map_zero]
  refine ⟨a * b, hab, fun y hy => ?_⟩
  simpa using hs.2.2 y hy

theorem exists_baseChange_injective_of_dense.{w} {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type w) [CommRing R'] [Algebra R R'] [Module.Flat R R'],
      IsUnit (algebraMap R R' a) →
        Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R') φ) := by
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense φ hD h
  refine ⟨a, ha0, fun R' _ _ _ hu => (injective_iff_map_eq_zero _).2 fun z hz => ?_⟩
  have hex := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map φ.toLinearMap)
  obtain ⟨w, rfl⟩ := (hex z).1 hz
  clear hz
  induction w with
  | add y z hy hz => rw [map_add (f := _), hy, hz, add_zero]
  | tmul c y =>
    obtain ⟨n, hn⟩ := ha y y.2
    obtain ⟨u, hu⟩ := (hu.pow n).exists_left_inv
    have e : c = a ^ n • (c * u) := by
      rw [Algebra.smul_def, map_pow, mul_comm, mul_assoc, hu, mul_one]
    rw [LinearMap.lTensor_tmul, e, smul_tmul, Submodule.subtype_apply, hn, tmul_zero]

end

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem interior_closure_eq_empty_of_isConstructible_of_disjoint_dense
    {Y : Type*} [TopologicalSpace Y] {D Sg : Set Y} (hD : Topology.IsConstructible D)
    (hSg : Dense Sg) (h : Disjoint D Sg) : interior (closure D) = ∅ := by
  have h1 : interior (frontier D) = ∅ :=
    interior_frontier_preimage_of_isConstructible (f := id) continuous_id hD
  have h2 : interior D = ∅ :=
    interior_eq_empty_iff_dense_compl.2 (hSg.mono h.subset_compl_left)
  rwa [frontier, h2, Set.diff_empty] at h1

theorem exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (C : Set X) (Sg : Set S), Topology.IsConstructible C → Dense Sg → Disjoint (f '' C) Sg → ∃ V : S.Opens, (V : Set S).Nonempty ∧ IsAffineOpen V ∧ Disjoint (f '' C) V := by
  intro X S _ _ f _ _ C Sg hC hSg h
  have hD : Topology.IsConstructible (f '' C) := f.isConstructible_image hC
  have h1 := interior_closure_eq_empty_of_isConstructible_of_disjoint_dense hD hSg h
  obtain ⟨x, hx⟩ : ((closure (f '' C))ᶜ).Nonempty :=
    (interior_eq_empty_iff_dense_compl.1 h1).nonempty
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx isClosed_closure.isOpen_compl
  refine ⟨V, ⟨x, hxV⟩, hV, ?_⟩
  exact Set.disjoint_left.2 fun y hy hyV => hVU hyV (subset_closure hy)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_notMem_of_ncard_lt_card {H : Type} [Finite H] (S : Set H)
    (h : S.ncard < Nat.card H) : ∃ x : H, x ∉ S := by
  by_contra hx
  have hS : S = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx'
    exact hx ⟨x, hx'⟩
  rw [hS, Set.ncard_univ] at h
  exact lt_irrefl _ h

theorem exists_pair_avoiding_small_sets :
    ∀ (H : Type) [CommGroup H] [Finite H] (B₀ B₁ : Set H), 6 * Nat.card B₀ < Nat.card H →
      6 * Nat.card B₁ < Nat.card H →
      ∃ b c : H, b ∉ B₀ ∧ c ∉ B₀ ∧ b * c ∉ B₀ ∧ b ∉ B₁ ∧ c ∉ B₁ ∧ b * c ∉ B₁ := by
  intro H _ _ B₀ B₁ h₀ h₁
  rw [Nat.card_coe_set_eq] at h₀ h₁
  have hS : (B₀ ∪ B₁).ncard ≤ B₀.ncard + B₁.ncard := Set.ncard_union_le _ _
  obtain ⟨b, hb⟩ := exists_notMem_of_ncard_lt_card (B₀ ∪ B₁) (by omega)
  have hT : ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤ (B₀ ∪ B₁).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hU : ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤
      (B₀ ∪ B₁).ncard + ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard := Set.ncard_union_le _ _
  obtain ⟨c, hc⟩ := exists_notMem_of_ncard_lt_card
    ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)) (by omega)
  have hbc : b * c ∉ B₀ ∪ B₁ := fun h => hc (Or.inr ⟨b * c, h, by simp⟩)
  exact ⟨b, c, fun h => hb (Or.inl h), fun h => hc (Or.inl (Or.inl h)), fun h => hbc (Or.inl h),
    fun h => hb (Or.inr h), fun h => hc (Or.inl (Or.inr h)), fun h => hbc (Or.inr h)⟩

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory.ArcAvoid

theorem exists_ringEquiv_powerSeries_of_complete {k O : Type*} [Field k] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ι : k →+* O)
    (hι : Function.Surjective ((residue O).comp ι)) :
    ∃ e : PowerSeries k ≃+* O, ∀ a, e (PowerSeries.C a) = ι a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ev, hev⟩ := exists_algHom_powerSeries_apply_X_of_isAdicComplete (maximalIdeal O)
    (π := π) (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π)
  let ψ : PowerSeries k →+* O := (ev : PowerSeries O →+* O).comp (PowerSeries.map ι)
  have hX : ψ PowerSeries.X = π := by simp [ψ, hev]
  have hC : ∀ a, ψ (PowerSeries.C a) = ι a := fun a => by
    simpa [ψ] using ev.commutes (ι a)
  have hmap : (Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ = maximalIdeal O := by
    rw [Ideal.map_span, Set.image_singleton, hX, hπ.maximalIdeal_eq]
  have hH : IsHausdorff ((Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ) O := by
    rw [hmap]; infer_instance
  have hs : Function.Surjective ψ := by
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span {PowerSeries.X}) ψ ?_
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hι (residue O y)
    refine ⟨PowerSeries.C a, ?_⟩
    rw [RingHom.comp_apply, hC, Ideal.Quotient.eq, hmap]
    exact Ideal.Quotient.eq.mp ha
  have hi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    rw [map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero, hX] at ha
    exact hπ.ne_zero (eq_zero_of_pow_eq_zero ha)
  exact ⟨RingEquiv.ofBijective ψ ⟨hi, hs⟩, hC⟩

theorem exists_ringHom_powerSeries_of_dvr {k V : Type*} [Field k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : k →+* V) (hι : Function.Surjective ((residue V).comp ι)) :
    ∃ φ : V →+* PowerSeries k, Function.Injective φ ∧ (∀ a, φ (ι a) = PowerSeries.C a) ∧
      ∀ v, v ∈ maximalIdeal V ↔ PowerSeries.constantCoeff (φ v) = 0 := by
  let O := AdicCompletion (maximalIdeal V) V
  obtain ⟨e, he⟩ := exists_ringEquiv_powerSeries_of_complete ((algebraMap V O).comp ι) (by
    intro y
    obtain ⟨z, rfl⟩ := (AdicCompletion.residueField_map_bijective V).2 y
    obtain ⟨a, rfl⟩ := hι z
    exact ⟨a, rfl⟩)
  refine ⟨(e.symm : O →+* PowerSeries k).comp (algebraMap V O),
    e.symm.injective.comp (algebraMap_adicCompletion_injective_of_dvr V), fun a => ?_, fun v => ?_⟩
  · exact e.symm_apply_eq.mpr (he a).symm
  · rw [mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (algebraMap V O),
      ← isUnit_map_iff e.symm, PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
    rfl


open Polynomial in
theorem surjective_residue_of_isAlgebraic {k V : Type*} [Field k] [IsAlgClosed k] [CommRing V]
    [IsDomain V] [IsLocalRing V] [Algebra k[X] V] [Algebra.IsAlgebraic k[X] V]
    [FaithfulSMul k[X] V] (hX : algebraMap k[X] V X ∈ maximalIdeal V) :
    Function.Surjective ((residue V).comp ((algebraMap k[X] V).comp C)) := by
  classical
  letI : Algebra k (ResidueField V) := ((residue V).comp ((algebraMap k[X] V).comp C)).toAlgebra
  have hc : (algebraMap k (ResidueField V)).comp (constantCoeff : k[X] →+* k) =
      (residue V).comp (algebraMap k[X] V) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [RingHom.algebraMap_toAlgebra]
    · simpa using ((residue_eq_zero_iff _).mpr hX).symm
  have : Algebra.IsAlgebraic k (ResidueField V) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := k[X]) x
    have h1 := aeval_primPart_eq_zero hp0 hp
    refine ⟨p.primPart.map constantCoeff, fun h => ?_, ?_⟩
    · refine Polynomial.not_isUnit_X (R := k) (p.isPrimitive_primPart X ?_)
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun q => q.coeff i) h
      simpa [X_dvd_iff] using this
    · rw [aeval_def, eval₂_map, hc, ← hom_eval₂, ← aeval_def, h1, map_zero]⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := ResidueField V)).2


open Polynomial in
theorem exists_injective_of_height_le_one {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) [hm : m.IsMaximal]
    (h1 : m.height ≤ 1) :
    ∃ φ : B →ₐ[k] PowerSeries k, Function.Injective φ ∧
      ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  rcases eq_or_ne m ⊥ with rfl | hne
  · letI : Field B := (Ring.isField_iff_maximal_bot.mpr hm).toField
    have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
    let e : k ≃ₐ[k] B :=
      .ofBijective (Algebra.ofId k B) IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(Algebra.ofId k (PowerSeries k)).comp e.symm, RingHom.injective _, fun b => ?_⟩
    simp [Algebra.ofId_apply]
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have hal : ∀ p : k[X], algebraMap k[X] B p = aeval t p := fun _ => rfl
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun a => by simp [hal]
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k k[X] B
  have hinj : Function.Injective (algebraMap k[X] B) := by
    refine transcendental_iff_injective.mp fun halg => hm.ne_top ?_
    exact m.eq_top_of_isUnit_mem htm (halg.isIntegral.isUnit ht0)
  obtain ⟨K', _, _, _, V, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one
    (O := k[X]) (K := FractionRing k[X]) hinj m h1 X X_ne_zero (by simpa [hal] using htm)
  letI : Algebra k[X] V := (φ.comp (algebraMap k[X] B)).toAlgebra
  letI : Algebra k[X] K' :=
    ((algebraMap (FractionRing k[X]) K').comp (algebraMap k[X] (FractionRing k[X]))).toAlgebra
  have : IsScalarTower k[X] (FractionRing k[X]) K' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k[X] V K' := .of_algebraMap_eq fun a => (hφ a).symm
  have : FaithfulSMul k[X] V := (faithfulSMul_iff_algebraMap_injective _ _).mpr (hφi.comp hinj)
  have halg : Algebra.IsAlgebraic k[X] K' :=
    (IsFractionRing.comap_isAlgebraic_iff (A := k[X]) (K := FractionRing k[X]) (C := K')).mpr
      inferInstance
  have : Algebra.IsAlgebraic k[X] V :=
    .of_injective (IsScalarTower.toAlgHom k[X] V K') Subtype.val_injective
  have hXV : algebraMap k[X] V X ∈ maximalIdeal V := by
    change algebraMap k[X] B X ∈ (maximalIdeal V).comap φ
    simpa [hal, hφm] using htm
  let W : Subalgebra k[X] K' :=
    { V.toSubring with algebraMap_mem' := fun r => (hφ r) ▸ (φ (algebraMap k[X] B r)).2 }
  have hVn : IsNoetherianRing V := (krullAkizuki (FractionRing k[X]) W).1
  have hnf : ¬ IsField V := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    rw [h] at hXV
    exact X_ne_zero ((FaithfulSMul.algebraMap_eq_zero_iff k[X] V).mp hXV)
  have hval : ValuationRing V := inferInstance
  have : IsDiscreteValuationRing V := ((IsDiscreteValuationRing.TFAE V hnf).out 2 1).mp hval
  obtain ⟨ψ, hψi, hψC, hψm⟩ :=
    exists_ringHom_powerSeries_of_dvr _ (surjective_residue_of_isAlgebraic hXV)
  refine ⟨{ ψ.comp φ with commutes' := fun a => ?_ }, hψi.comp hφi, fun b => ?_⟩
  · have := hψC a
    rw [IsScalarTower.algebraMap_apply k k[X] B]
    exact this
  · rw [← hφm]
    exact hψm (φ b)

theorem exists_algHom_powerSeries_ne_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B), m.IsMaximal → ∀ f : B, f ≠ 0 →
      ∃ φ : B →ₐ[k] PowerSeries k, φ f ≠ 0 ∧
        ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  intro k _ _ B _ _ _ _ m hm f hf
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨q, hqf, hqm, hht⟩ := exists_mem_height_map_le_one m (PrimeSpectrum.basicOpen f).isOpen
    ⟨⊥, hf, bot_le⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  obtain ⟨φ, hφi, hφm⟩ := exists_injective_of_height_le_one (k := k) _ hht
  refine ⟨φ.comp (Ideal.Quotient.mkₐ k q.asIdeal), fun h => hqf ?_, fun b => ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hφi (h.trans (map_zero φ).symm))
  · conv_lhs => rw [← hcomap]
    exact hφm _

end GlobalTheory.ArcAvoid
end

section

open TensorProduct

namespace GlobalTheory

theorem powerSeries_extend_finite_free (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K]
    [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K)
    (io : O₁ →+* K) (h : ∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧
      Φ PowerSeries.X = i PowerSeries.X ∧
      ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  first
  | exact @_root_.GlobalTheory.PowerSeriesCompositionMap.main
  | exact _root_.GlobalTheory.PowerSeriesCompositionMap.main
  | (apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerSeriesCompositionMap.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerSeriesCompositionMap.main ..)

end GlobalTheory
end

section

namespace GlobalTheory.PadicVal

theorem _root_.GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff : ∀ (p : ℕ) [Fact p.Prime] (π : PadicAlgCl p),
    0 < ‖π‖ → ‖π‖ < 1 → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ),
      (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔
        ‖c‖ ≤ Real.exp (-(-Real.log ‖π‖ * r))) ∧
      ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔
        ‖c‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by
  intro p _ π h0 h1
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PadicVal.exists_addValuation π h0 h1
  refine ⟨v, fun c r => ?_, fun c r => ?_⟩
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).le]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_le_coe, neg_mul, neg_neg,
      ← Real.log_le_iff_le_exp (norm_pos_iff.2 hc), hlog, mul_comm (Real.log ‖π‖),
      mul_le_mul_right_of_neg hL]
    exact_mod_cast Iff.rfl
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).ne]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_inj, neg_mul, neg_neg]
    constructor
    · rintro rfl
      rw [mul_comm, ← hlog, Real.exp_log (norm_pos_iff.2 hc)]
    · intro h
      have h2 := congrArg Real.log h
      rw [Real.log_exp, hlog, mul_comm (Real.log ‖π‖)] at h2
      exact Rat.cast_injective (mul_right_cancel₀ hL.ne h2)

end GlobalTheory.PadicVal
end
