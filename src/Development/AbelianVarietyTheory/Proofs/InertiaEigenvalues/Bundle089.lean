module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle043
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle047
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle045
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

theorem residueField_map_adicCompletion_surjective (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] :
    Function.Surjective (ResidueField.map (algebraMap W (AdicCompletion (maximalIdeal W) W))) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal W) 1 x)
  refine ⟨residue W w, ?_⟩
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff]
  intro hu
  have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal W) 1)
  rw [map_sub, AlgHom.commutes, ← hw, Ideal.Quotient.algebraMap_eq, sub_self] at h1
  haveI : Nontrivial (W ⧸ maximalIdeal W ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal W).ne_top)
  exact not_isUnit_zero h1

theorem finite_residueField_of_dominating (D : Type*) [CommRing D] [IsDomain D] [IsLocalRing D]
    [IsNoetherianRing D] [Ring.DimensionLEOne D] (hD : ¬ IsField D) [Finite (ResidueField D)]
    (V : ValuationSubring (FractionRing D))
    (h1 : ∀ r, algebraMap D (FractionRing D) r ∈ V)
    [IsLocalHom ((algebraMap D (FractionRing D)).codRestrict V h1)] :
    Finite (ResidueField V) := by
  set f := (algebraMap D (FractionRing D)).codRestrict V h1 with hf
  letI : Algebra D V := f.toAlgebra
  haveI : IsLocalHom (algebraMap D V) := ‹IsLocalHom f›
  haveI : FaithfulSMul D V := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  have hB : ∀ x : V, ∃ c : D, c ≠ 0 ∧ ∃ b : D, algebraMap D V c * x = algebraMap D V b := by
    intro x
    obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors D) (x : FractionRing D)
    refine ⟨c, nonZeroDivisors.coe_ne_zero c, b, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_mul] at hbc ⊢
    change algebraMap D (FractionRing D) c * x = algebraMap D (FractionRing D) b
    rw [mul_comm]; exact hbc
  have hm : maximalIdeal D ≠ ⊥ := fun h => hD (isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  haveI := finite_quotient_span_of_birational hB ha0
  have hle : Ideal.span {algebraMap D V a} ≤ maximalIdeal V := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact map_nonunit (algebraMap D V) a ha
  have hsurj : Function.Surjective (Ideal.Quotient.factorₐ D hle).toLinearMap := by
    intro y
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ v, rfl⟩
  haveI : Module.Finite D (ResidueField V) := Module.Finite.of_surjective _ hsurj
  haveI : Module.Finite (ResidueField D) (ResidueField V) :=
    Module.Finite.of_restrictScalars_finite D _ _
  exact Module.finite_of_finite (ResidueField D)

theorem exists_complete_dvr_finite_residueField : ∀ (D : Type) [CommRing D] [IsDomain D] [IsLocalRing D], IsNoetherianRing D → ringKrullDim D = 1 → Finite (ResidueField D) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (maximalIdeal V) V) (g : D →+* V), Function.Injective g ∧ IsLocalHom g ∧ Finite (ResidueField V) := by
  intro D _ _ _ hN hdim hF
  have hD : ¬ IsField D := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hdim; exact zero_ne_one hdim
  haveI : Ring.KrullDimLE 1 D := Ring.krullDimLE_iff.mpr (by simp [hdim])
  haveI : Ring.DimensionLEOne D :=
    ⟨fun hp hpr => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp this _ hp hpr⟩
  obtain ⟨V, hV, h⟩ :=
    exists_discreteValuationSubring_dominating D (FractionRing D) (FractionRing D) hD
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hfin : Finite (ResidueField V) := finite_residueField_of_dominating D hD V h1
  obtain ⟨hi, hl⟩ := injective_and_isLocalHom_adicCompletion_comp
      ((algebraMap D (FractionRing D)).codRestrict V h1)
      fun a b hab => IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val hab)
  exact ⟨AdicCompletion (maximalIdeal V) V, inferInstance, inferInstance, inferInstance,
    inferInstance, _, hi, hl,
    Finite.of_surjective _ (residueField_map_adicCompletion_surjective V)⟩

end GlobalTheory
end

section

open Polynomial

theorem _root_.GlobalTheory.T.map_trace_adjoinRoot_eq_trace_map : ∀ (R S : Type) [CommRing R] [CommRing S] (g : R →+* S) (h : R[X]), h.Monic → ∀ x : AdjoinRoot h, g (Algebra.trace R (AdjoinRoot h) x) = Algebra.trace S (AdjoinRoot (h.map g)) (AdjoinRoot.map g h (h.map g) dvd_rfl x) := by
  first | exact @GlobalTheory.trace_adjoinRoot_map | exact GlobalTheory.trace_adjoinRoot_map | (intros; apply GlobalTheory.trace_adjoinRoot_map <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B), IsOpen (f.ker : Set (v.adicCompletion F)ˣ) → IsOpen (g.ker : Set (v.adicCompletion F)ˣ) → (∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) → ∀ x, f x = g x := by
  first | exact @GlobalTheory.units_adicCompletion_hom_ext | exact GlobalTheory.units_adicCompletion_hom_ext | (intros; apply GlobalTheory.units_adicCompletion_hom_ext <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.comap_eq_of_continuous_adicCompletion_iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by
  first | exact @GlobalTheory.PlaceOver.comap_eq_of_continuous_iso | exact GlobalTheory.PlaceOver.comap_eq_of_continuous_iso | (intros; apply GlobalTheory.PlaceOver.comap_eq_of_continuous_iso <;> assumption)
end

section

open NumberField IsDedekindDomain TensorProduct

theorem _root_.GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E) (e : w.adicCompletion E ⊗[E] E'), e * e = e → ψ e = 1 → ∀ (p q : w.adicCompletion E ⊗[E] E') (n : ℕ), ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧ Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) - Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_global_near_idempotent | exact GlobalTheory.exists_global_near_idempotent | (intros; apply GlobalTheory.exists_global_near_idempotent <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_equiv_dvr_fg_module_structure : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M], ∃ (n m : ℕ) (e : Fin m → ℕ), Nonempty (M ≃ₗ[O] (Fin n → O) × ((i : Fin m) → O ⧸ IsLocalRing.maximalIdeal O ^ e i)) := by
  first | exact @GlobalTheory.dvr_fg_module_structure | exact GlobalTheory.dvr_fg_module_structure | (intros; apply GlobalTheory.dvr_fg_module_structure <;> assumption)
end

section

open Module

theorem _root_.GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t → (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤ C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  first | exact @GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | exact GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | (intros; apply GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.dvr_matrix_proj_preimage_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n] (S : Submodule K (n → K)), ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧ ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  first | exact @GlobalTheory.dvr_matrix_proj_preimage | exact GlobalTheory.dvr_matrix_proj_preimage | (intros; apply GlobalTheory.dvr_matrix_proj_preimage <;> assumption)
end

section

open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem unit_mul_pow_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ 0) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  first
  | exact @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | (apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit ..)

theorem dvr_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) (hreg : ∀ a : S, π * a = 0 → a = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  have hpow : ∀ (k : ℕ) (a : S), π ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a h; simpa using h
    | succ k ih => intro a h; exact ih a (hreg _ (by rw [← h, pow_succ]; ring))
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨a, u, hu, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.1
    obtain ⟨b, v, hv, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.2
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy, pow_add]; ring
    exact (hu.mul hv).ne_zero (hpow _ _ this)
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hnf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hπ0
  have hpr : (maximalIdeal S).IsPrincipal := ⟨⟨π, hm⟩⟩
  have hdvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 1 5).2 hpr
  exact ⟨inferInstance, hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hm⟩

end GlobalTheory.Pat
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ N : ℕ, ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K), ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) → ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.GenUnr.finite_classes_mod_pow | exact GlobalTheory.GenUnr.finite_classes_mod_pow | (intros; apply GlobalTheory.GenUnr.finite_classes_mod_pow <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  first | exact @GlobalTheory.finite_submodules_between_smul_and_self | exact GlobalTheory.finite_submodules_between_smul_and_self | (intros; apply GlobalTheory.finite_submodules_between_smul_and_self <;> assumption)
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem finite_residueField_of_compact_isAdic :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  intro O _ _ _ _ _ _ h
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
    have := (isAdic_iff.mp h).1 1
    simpa using this
  have hfin : Finite (O ⧸ (IsLocalRing.maximalIdeal O).toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact hfin

end GlobalTheory.ShapeNeg
end
