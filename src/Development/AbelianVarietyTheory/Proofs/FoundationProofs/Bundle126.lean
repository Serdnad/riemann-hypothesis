module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle106
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
public import Mathlib.FieldTheory.KummerExtension
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.Algebra.Group.Subgroup.Order
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.mod_l_three_cocycle_condition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (ρ1 : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g x, PadicInt.toZModPow 1 (ρ g x) = ρ1 g (PadicInt.toZModPow 1 x)) → (∀ c : Γ × Γ × Γ → ZMod (l ^ 1), Continuous c → (∀ g h k m, ρ1 g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → ZMod (l ^ 1), Continuous u ∧ ∀ g h k, ρ1 g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k)) → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ y ∈ Z2 ρr, ∃ z ∈ Z2 ρ, ∀ p, PadicInt.toZModPow r (z p) = y p := by
  first | exact @GlobalTheory.PadicCocycleLift.twoCocycle_lift | exact GlobalTheory.PadicCocycleLift.twoCocycle_lift | (intros; apply GlobalTheory.PadicCocycleLift.twoCocycle_lift <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.padic_coboundary_of_divisible : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (ρr : ∀ r : ℕ, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x)) → (∀ r, 0 < r → Finite (H1 (ρr r))) → ∀ z ∈ Z2 ρ, (∀ r : ℕ, ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ) → z ∈ B2 ρ := by
  first | exact @GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow | exact GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow | (intros; apply GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.exists_z2_sub_pow_smul_mem_b2_of_reduction : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ z ∈ Z2 ρ, (fun p => PadicInt.toZModPow r (z p)) ∈ B2 ρr → ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ := by
  first | exact @GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary | exact GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary | (intros; apply GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.PsRoot

theorem mem_of_isAlgebraic_of_isAlgClosed (E : Subfield ℂ) [IsAlgClosed E] {x : ℂ}
    (hx : IsAlgebraic E x) : x ∈ E := by
  have hi : IsIntegral E x := hx.isIntegral
  have h1 : (minpoly E x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

theorem coeff_mem_range_of_isRoot : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 →
    (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 →
    ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  intro Ω _ _ ε b Q hQ hcoef hb k
  let E : Subfield ℂ := ε.fieldRange
  haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv
  have hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E := fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, rfl⟩

  have hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b) := by
    intro g
    have hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q := by
      ext i j
      rw [Polynomial.coeff_map, PowerSeries.coeff_map]
      obtain ⟨y, hy⟩ := hE _ (hcoef i j)
      rw [← hy]
      exact g.commutes ⟨_, ⟨y, rfl⟩⟩
    have h2 := Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b
    show Q.eval _ = 0
    rw [hfix, hb, map_zero] at h2
    exact h2
  have hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite := by
    refine ((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩
    simp [PowerSeries.coeff_map]
  obtain ⟨y, hy⟩ := mem_of_isAlgebraic_of_isAlgClosed E (GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit E _ hfin)
  exact ⟨y, hy⟩

end GlobalTheory.PsRoot
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory

theorem isPGroup_coatom_normal_index_eq {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (K : Subgroup P) (hK : IsCoatom K) :
    K.Normal ∧ K.index = p := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK
  have hQ : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hidx : K.index ≠ 1 := fun h => hK.1 (Subgroup.index_eq_one.1 h)
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hidx (by rw [Subgroup.index_eq_card, hn, pow_zero])
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have htop : (Subgroup.zpowers x).comap (QuotientGroup.mk' K) = ⊤ := by
    apply hK.2
    refine lt_of_le_of_ne ?_ ?_
    · intro k hk
      have : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      rw [Subgroup.mem_comap, this]
      exact one_mem _
    · intro h
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
      have : y ∈ K := by
        rw [h, Subgroup.mem_comap]
        exact Subgroup.mem_zpowers _
      exact hx1 ((QuotientGroup.eq_one_iff y).2 this)
  have hz : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K z
    have : y ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← hx, ← Nat.card_zpowers, hz, Subgroup.card_top]
  exact ⟨hN, by rw [Subgroup.index_eq_card, hcard]⟩

theorem valuationSubring_galois_stable_of_kummer : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  intro l hl F L _ _ _ _ _ hP hζ W hW
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  let D : Subgroup (L ≃ₐ[F] L) :=
    { carrier := {σ | ∀ x, σ x ∈ W ↔ x ∈ W}
      mul_mem' := by
        intro a b ha hb x
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AlgEquiv.mul_apply, ha, hb]
      one_mem' := by intro x; simp
      inv_mem' := by
        intro a ha x
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (a⁻¹ x)]
        simp }
  suffices hD : D = ⊤ by
    intro τ x
    have hτ : τ ∈ D := hD ▸ Subgroup.mem_top τ
    exact hτ x
  by_contra hD
  obtain ⟨H, hH, hDH⟩ := (eq_top_or_exists_le_coatom D).resolve_left hD
  obtain ⟨hHn, hHi⟩ := isPGroup_coatom_normal_index_eq hP H hH
  haveI : IsGalois F (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  have hfr : Module.finrank F (IntermediateField.fixedField H) = l := by
    have h1 := (letI : Module.Free (IntermediateField.fixedField H) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank F (IntermediateField.fixedField H) L)
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F L,
      ← H.card_mul_index, hHi, mul_comm (Nat.card H)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  haveI : IsCyclic (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H) :=
    isCyclic_of_prime_card (p := l) (by rw [IsGalois.card_aut_eq_finrank, hfr])
  obtain ⟨ζ, hζ⟩ := hζ
  have hK : (primitiveRoots (Module.finrank F (IntermediateField.fixedField H)) F).Nonempty :=
    ⟨ζ, by rw [hfr, mem_primitiveRoots hl.pos]; exact hζ⟩
  obtain ⟨α, ⟨δ, hδ⟩, hα⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic F (IntermediateField.fixedField H) hK
  rw [hfr] at hδ
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h1 : (⊤ : IntermediateField F (IntermediateField.fixedField H)) = ⊥ := by
      rw [← hα]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 (zero_mem _)
    have h2 := congrArg
      (fun E : IntermediateField F (IntermediateField.fixedField H) => Module.finrank F E) h1
    simp only [IntermediateField.finrank_top', IntermediateField.finrank_bot] at h2
    exact hl.one_lt.ne' (hfr ▸ h2)
  have hθ0 : (α : L) ≠ 0 := fun h => hα0 (Subtype.ext h)
  have hθl : (α : L) ^ l ∈ (algebraMap F L).range := by
    refine ⟨δ, ?_⟩
    have := congrArg (fun y : IntermediateField.fixedField H => (y : L)) hδ
    simpa using this
  have hKθ : ∀ x ∈ IntermediateField.fixedField H, x ∈ IntermediateField.adjoin F {(α : L)} := by
    intro x hx
    have hm : x ∈ (IntermediateField.adjoin F {α}).map (IntermediateField.fixedField H).val :=
      ⟨⟨x, hx⟩, by rw [hα]; trivial, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at hm
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∉ H := by
    by_contra h
    exact hH.1 (eq_top_iff.2 fun g _ => by_contra fun hg => h ⟨g, hg⟩)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (IntermediateField.fixedField H) L W (W.comap (τ : L →+* L))
    (fun a => (hW α hθ0 hθl τ a (hKθ a a.2)).symm)
  have hη : σ.restrictScalars F ∈ H := by
    refine (IntermediateField.fixingSubgroup_fixedField H).le ?_
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have hτη : τ * σ.restrictScalars F ∈ D := fun x => hσ x
  exact hτ ((H.mul_mem_cancel_right hη).1 (hDH hτη))

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory
namespace GenericSpecial

theorem ext_unit_ne {k R : Type} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (S : Subalgebra k R) (L : R →ₗ[k] k) (hone : L 1 = 1)
    (hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z) (x : R) (hx : x ∈ S) (hu : IsUnit x)
    (hi : Ring.inverse x ∈ S) : L x ≠ 0 := by
  intro h
  have e := hmul x hx _ hi
  rw [Ring.mul_inverse_cancel x hu, hone, h, zero_mul] at e
  exact one_ne_zero e

theorem lin_eq_of_zero_iff {k A : Type} [Field k] [CommRing A] [Algebra k A]
    (g h : A →ₗ[k] k) (hg : g 1 = 1) (hh : h 1 = 1) (hk : ∀ u, g u = 0 ↔ h u = 0) (u : A) :
    g u = h u := by
  have h1 : g (u - g u • 1) = 0 := by simp [hg]
  have h2 := (hk _).1 h1
  rw [map_sub, map_smul, hh, smul_eq_mul, mul_one, sub_eq_zero] at h2
  exact h2.symm

end GenericSpecial

theorem specialise_generic_solution : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (R : Type) [CommRing R] [IsDomain R] [Algebra k R] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D : Ideal A), 2 ≤ N → (∃ (ξ : A →ₐ[k] R) (Δ : I → ℕ → A →ₗ[k] R) (m : ℕ) (v : Fin m → A) (y : Fin m → R),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u))) → ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∃ (Q' : I → Ideal A) (f : A), (∀ i, (Q' i).IsMaximal) ∧ Function.Injective Q' ∧ (∀ i, Q' i ≠ P) ∧ (∀ i, ¬ D ≤ Q' i) ∧ ¬ D ≤ P ∧ f ∈ V ∧ f ≠ 0 ∧ f ∈ P ∧ ∀ i, f ∈ Q' i ^ N := by
  intro k A _ _ _ _ _ _ _ R _ _ _ N I _ V D hN hex
  classical
  obtain ⟨ξ, Δ, m, v, y, hinj, h01, hleib, hπ, hvV, hli, ⟨j0, hj0⟩, heq0, heqΔ, hsep, hsepξ,
    hD, hDξ⟩ := hex
  have hsep' : ∀ p : I × I, ∃ u : A, p.1 ≠ p.2 → IsUnit (Δ p.1 0 u - Δ p.2 0 u) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨0, fun h => absurd hp h⟩
    · obtain ⟨u, hu⟩ := hsep p.1 p.2 hp
      exact ⟨u, fun _ => hu⟩
  choose us hus using hsep'
  choose uξ huξ using hsepξ
  choose uD huDmem huD using hD
  obtain ⟨u0, hu0D, hu0⟩ := hDξ
  choose TJ hTJ using fun i => GlobalTheory.T.jets_mem_subalgebra_of_finiteType_algebra k A R N (Δ i) (h01 i) (hleib i)
  let T : Finset R := Finset.univ.biUnion TJ ∪ Finset.univ.image y ∪
    Finset.univ.image (fun p : I × I => Ring.inverse (Δ p.1 0 (us p) - Δ p.2 0 (us p))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uξ i) - ξ (uξ i))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uD i))) ∪
    {Ring.inverse (ξ u0), Ring.inverse (y j0)}
  obtain ⟨a, S, hξS, ha0, hTS, hspec⟩ := GlobalTheory.T.exists_ne_zero_point_extends_to_subalgebra k A R ξ hinj T
  refine ⟨a, ha0, ?_⟩
  intro P hPmax haP
  obtain ⟨-, φ, hφ⟩ := (GlobalTheory.T.dedekind_finiteType_ideal_codimension k A).2.1 P hPmax
  obtain ⟨ψ, hψ⟩ := hspec φ (fun h => haP ((hφ a).2 h))
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (ψ.toLinearMap.comp
    (LinearEquiv.refl k (Subalgebra.toSubmodule S)).toLinearMap)
  have hLS : ∀ x (hx : x ∈ S), L x = ψ ⟨x, hx⟩ := by
    intro x hx
    exact LinearMap.congr_fun hL ⟨x, hx⟩
  have hone : L 1 = 1 := by rw [hLS 1 S.one_mem]; exact map_one ψ
  have hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z := by
    intro x hx z hz
    rw [hLS _ (S.mul_mem hx hz), hLS x hx, hLS z hz, ← map_mul]; rfl
  have hLξ : ∀ u, L (ξ u) = φ u := fun u => by rw [hLS _ (hξS u), hψ]
  have hSΔ : ∀ i l, l < N → ∀ u, Δ i l u ∈ S := fun i =>
    hTJ i S (fun t ht => hTS t (by simp only [T, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, Finset.mem_univ _, ht⟩))))))
  have hy : ∀ j, y j ∈ S := fun j => hTS _ (by simp [T])
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  let Δ' : I → ℕ → A →ₗ[k] k := fun i l => if l < N then L ∘ₗ Δ i l else 0
  have hΔ' : ∀ i l, l < N → ∀ u, Δ' i l u = L (Δ i l u) := by
    intro i l h u; simp [Δ', h]
  have hjet : ∀ i, ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ' i 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ' i l f = 0) → f ∈ Q ^ N := by
    intro i
    apply GlobalTheory.T.mem_maximal_pow_of_jets_vanish k A N (Δ' i) hN
    · rw [hΔ' i 0 hN0, h01 i, hone]
    · intro l hl u w

      rw [hΔ' i l hl, hleib i l u w, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < l + 1 := Finset.mem_range.1 hp
      rw [map_nsmul, hmul _ (hSΔ i p (by omega) u) _ (hSΔ i (l - p) (by omega) w),
        hΔ' i p (by omega), hΔ' i (l - p) (by omega)]
    · obtain ⟨π, hπ'⟩ := hπ i
      exact ⟨π, by rw [hΔ' i 1 hN1, hπ', hone]⟩
  choose Q' hQmax hQmem hQpow using hjet
  have hunit : ∀ x ∈ S, IsUnit x → Ring.inverse x ∈ S → L x ≠ 0 :=
    fun x hx hu hi => GenericSpecial.ext_unit_ne S L hone hmul x hx hu hi
  let f : A := ∑ j, L (y j) • v j
  refine ⟨Q', f, hQmax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i i' hii'
    by_contra hne
    have hu := hus (i, i') hne
    set u := us (i, i')
    have heqv := GenericSpecial.lin_eq_of_zero_iff (Δ' i 0) (Δ' i' 0)
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (by rw [hΔ' i' 0 hN0, h01 i', hone])
      (fun w => by rw [← hQmem, ← hQmem, hii']) u
    rw [hΔ' i 0 hN0, hΔ' i' 0 hN0] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 u) (hSΔ i' 0 hN0 u)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i'), Finset.mem_univ _, rfl⟩))))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hiP
    have hu := huξ i
    have heqv := GenericSpecial.lin_eq_of_zero_iff (Δ' i 0) φ.toLinearMap
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (map_one φ)
      (fun w => by rw [← hQmem, hiP, hφ]; rfl) (uξ i)
    rw [hΔ' i 0 hN0, AlgHom.toLinearMap_apply, ← hLξ] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 _) (hξS _)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩)))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hDQ
    have h0 : Δ' i 0 (uD i) = 0 := (hQmem i _).1 (hDQ (huDmem i))
    rw [hΔ' i 0 hN0] at h0
    exact hunit _ (hSΔ i 0 hN0 _) (huD i)
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩))) h0
  · intro hDP
    have h0 : φ u0 = 0 := (hφ u0).1 (hDP hu0D)
    rw [← hLξ] at h0
    exact hunit _ (hξS _) hu0 (hTS _ (by simp [T])) h0
  · exact Submodule.sum_mem _ fun j _ => V.smul_mem _ (hvV j)
  · intro hf
    have := (Fintype.linearIndependent_iff.1 hli) (fun j => L (y j)) hf j0
    exact hunit _ (hy j0) hj0 (hTS _ (by simp [T])) this
  · apply (hφ f).2
    have : φ f = L (∑ j, y j * ξ (v j)) := by

      simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hξS _), hLξ]
    rw [this, heq0, map_zero]
  · intro i
    apply hQpow i
    intro l hl
    have : Δ' i l f = L (∑ j, y j * Δ i l (v j)) := by

      simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hSΔ i l hl _), hΔ' i l hl]
    rw [this, heqΔ i l hl, map_zero]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.natCard_coker_ker_padic_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (X P : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup P] [Module ℤ_[l] P] (f : X →ₗ[ℤ_[l]] P) (R : Type) [CommRing R] (X' P' : Type) [AddCommGroup X'] [Module R X'] [AddCommGroup P'] [Module R P'] (f' : X' →ₗ[R] P') (πX : X →+ X') (πP : P →+ P'), Function.Surjective πX → Function.Surjective πP → (∀ x, πX x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP (f x) = f' (πX x)) → Nat.card ((P ⧸ LinearMap.range f) ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) ((l : ℤ_[l]) ^ r))) = Nat.card (P' ⧸ LinearMap.range f') ∧ ((∀ x p, f x = (l : ℤ_[l]) ^ r • p → ∃ x', f x = (l : ℤ_[l]) ^ r • f x') → Nat.card (LinearMap.ker f ⧸ (LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ r))).comap (LinearMap.ker f).subtype) = Nat.card (LinearMap.ker f')) := by
  first | exact @GlobalTheory.natCard_coker_ker_mod_pow | exact GlobalTheory.natCard_coker_ker_mod_pow | (intros; apply GlobalTheory.natCard_coker_ker_mod_pow <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

theorem _root_.GlobalTheory.T.padicInt_length_eq_of_card_quotient_eq : ∀ (l : ℕ) [Fact l.Prime] (X Y : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y] (N : ℕ → Submodule ℤ_[l] X) (P : ℕ → Submodule ℤ_[l] Y) (c : ℕ), Antitone N → (∀ x, (∀ r, x ∈ N r) → x = 0) → Monotone P → (∀ y, ∃ r, y ∈ P r) → (∀ r, c ≤ r → Finite (P r) ∧ Nat.card (X ⧸ N r) = Nat.card (P r)) → Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  first | exact @GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule | exact GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule | (intros; apply GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem exists_coboundary_of_subsingleton_Hn_three :
    ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), Subsingleton (Hn ρ 3) → ∀ c : Γ × Γ × Γ → M, Continuous c → (∀ g h k m, ρ g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → M, Continuous u ∧ ∀ g h k, ρ g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k) := by
  intro R _ Γ _ _ M _ _ _ _ ρ hs c hc hcoc
  let f : (Fin 3 → Γ) → M := fun x => c (x 0, x 1, x 2)
  have hf : Continuous f := hc.comp (by fun_prop)
  have hd : dn ρ 3 f = 0 := by
    funext g
    rw [dn_apply, Fin.sum_univ_four]
    have e := hcoc (g 0) (g 1) (g 2) (g 3)
    have e0 : (f fun i => g i.succ) = c (g 1, g 2, g 3) := rfl
    have e1 : f (Fin.contractNth 0 (· * ·) g) = c (g 0 * g 1, g 2, g 3) := rfl
    have e2 : f (Fin.contractNth 1 (· * ·) g) = c (g 0, g 1 * g 2, g 3) := rfl
    have e3 : f (Fin.contractNth 2 (· * ·) g) = c (g 0, g 1, g 2 * g 3) := rfl
    have e4 : f (Fin.contractNth 3 (· * ·) g) = c (g 0, g 1, g 2) := rfl
    rw [e0, e1, e2, e3, e4, Pi.zero_apply, ← e]
    norm_num [pow_succ]
    abel
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff] at hs
  obtain ⟨w, hw, hwf⟩ : ∃ w : (Fin 2 → Γ) → M, Continuous w ∧ dn ρ 2 w = f :=
    hs (x := ⟨f, hf, hd⟩) trivial
  refine ⟨fun p => w ![p.1, p.2], hw.comp (by fun_prop), fun g h k => ?_⟩
  have e := congrFun hwf ![g, h, k]
  rw [dn_apply, Fin.sum_univ_three] at e
  have e0 : (fun i : Fin 2 => (![g, h, k] : Fin 3 → Γ) i.succ) = ![h, k] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g * h, k] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h * k] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h] := by
    funext i; fin_cases i <;> rfl
  have e4 : f ![g, h, k] = c (g, h, k) := rfl
  rw [e0, e1, e2, e3, e4] at e
  rw [← e]
  norm_num [pow_succ]
  abel

end GlobalTheory
end
