module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductFixedSubmoduleRestrictDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq

theorem cob_of_perp_transport {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ D : Type} [Group Γ] [Group D] [TopologicalSpace D]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (μ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ) (J : Subgroup D)
    (h : ContAction (rho.comp φ)) (h' : ContAction ((rho.comp φ).comp (MonoidHom.id D)))
    (key : ∀ y : H1 (twDual (μ.comp φ) (rho.comp φ)),
      (∀ x ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual (μ.comp φ) (rho.comp φ) (MonoidHom.id D) h' y x = 0) →
        y ∈ H1ur (twDual (μ.comp φ) (rho.comp φ)) J)
    (f : Z1 ((twDual μ rho).comp φ))
    (hf : ∀ a ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual μ rho φ h (Submodule.mkQ _ f) a = 0) :
    ∃ m : TDual R M, ∀ s ∈ J, f.1 s = twDual μ rho (φ s) m - m := by
  have heq : twDual (μ.comp φ) (rho.comp φ) = (twDual μ rho).comp φ := by
    refine MonoidHom.ext fun s => LinearMap.ext fun ψ => LinearMap.ext fun x => ?_
    change ((μ (φ s) : Rˣ) : R) * ψ (rho (φ s⁻¹) x) =
      ((μ (φ s) : Rˣ) : R) * ψ (rho (φ s)⁻¹ x)
    rw [map_inv]
  have hf' : f.1 ∈ Z1 (twDual (μ.comp φ) (rho.comp φ)) := by rw [heq]; exact f.2
  have hy := key (Submodule.Quotient.mk ⟨f.1, hf'⟩) (by
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H a =>
    have e := hf _ hx
    have e' := (Submodule.Quotient.mk_eq_zero _).1 e
    exact (Submodule.Quotient.mk_eq_zero _).2 e')
  rw [H1ur, LinearMap.mem_ker] at hy
  change Submodule.Quotient.mk (restrictCocycles1 _ J.subtype continuous_subtype_val ⟨f.1, hf'⟩) = 0 at hy
  rw [Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
  refine ⟨m, fun s hs => ?_⟩
  have e := hm ⟨s, hs⟩
  change f.1 s = twDual (μ.comp φ) (rho.comp φ) s m - m at e
  rw [e, heq]
  rfl

theorem dual_cocycle_cob_on_inertia : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  intro hL l _ Ω _ _ _ n hn S M _ _ _ _ _ rho hrho μ hμ B q hq hl f hf
  have hχ : (cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype = μ.comp (locHom (S : Set Pl) B) := by
    rw [← hμ]; rfl
  have hc := hrho.comp' (continuous_locHom (S : Set Pl) B)
  have key := GlobalTheory.Ord2.unramified_h1_dual_iff_perp hL ℚ Ω l n M B q (rho.comp (locHom (S : Set Pl) B)) hc
    hq hn hl
  rw [hχ] at key
  obtain ⟨m, hm⟩ := cob_of_perp_transport μ rho (locHom (S : Set Pl) B) _ hc _
    (fun y hy => (key y).2 hy) f hf
  exact ⟨m, fun s hs => hm s (Subgroup.mem_subgroupOf.2 hs)⟩

end GlobalTheory.Ord2.GwIneq
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaFieldUnram

theorem valuation_eq_zpow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : Ω, x ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s x = x) → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k :=
  GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed

end GlobalTheory.InertiaFieldUnram
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

theorem _root_.GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) → ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | exact GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | (intros; apply GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

open Polynomial IsLocalRing

theorem exists_residue_pow_pow_eq (l : ℕ) [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hl1 : A.valuation (l : Ω) < 1) (xA : A) :
    ∃ N : ℕ, 0 < N ∧ residue A xA ^ (l ^ N) = residue A xA := by
  first
  | exact @_root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed
  | exact _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed
  | (apply _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed ..)

theorem fixA_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ a : fixA A, ∃ (b : fixA A) (z : A), (a : A) = (b : A) ^ l + (l : A) * z := by
  intro l _ Ω _ _ _ A hO a
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl1 : A.valuation (l : Ω) < 1 := GlobalTheory.Ord2.VanishNarrow.valuation_lt_one hO
  obtain ⟨N, hN, hr⟩ := exists_residue_pow_pow_eq l A hl1 (a : A)
  refine ⟨a ^ (l ^ (N - 1)), ?_⟩
  have hb : ((a ^ (l ^ (N - 1)) : fixA A) : A) ^ l = (a : A) ^ (l ^ N) := by
    rw [SubmonoidClass.coe_pow, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hN]
  rw [hb]
  set cA : A := (a : A) - (a : A) ^ (l ^ N) with hcA
  have hcfix : cA ∈ fixA A := (fixA A).sub_mem a.2 ((fixA A).pow_mem a.2 _)
  have hcm : cA ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, hcA, map_sub, map_pow, hr, sub_self]
  have hcv : A.valuation (cA : Ω) < 1 := by
    have := (A.valuation_lt_one_iff _).1 hcm
    simpa using this
  suffices h : ∃ z : A, cA = (l : A) * z by
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    rw [← hz, hcA]
    ring
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hvl0 : A.valuation (l : Ω) ≠ 0 := (_root_.map_ne_zero _).2 hl0
  by_cases hc0 : (cA : Ω) = 0
  · exact ⟨0, by rw [mul_zero]; exact Subtype.ext hc0⟩
  obtain ⟨k, hk⟩ := GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed l Ω A hO (cA : Ω) hc0 (mem_fixA.1 hcfix)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast] at hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero] at hk; exact absurd hk hcv.ne
    have hz : A.valuation ((cA : Ω) / (l : Ω)) ≤ 1 := by
      rw [map_div₀, hk, ← Nat.sub_add_cancel hn, pow_succ, mul_div_assoc, div_self hvl0, mul_one]
      exact pow_le_one' hl1.le _
    refine ⟨⟨(cA : Ω) / (l : Ω), (A.valuation_le_one_iff _).1 hz⟩, Subtype.ext ?_⟩
    change (cA : Ω) = (l : Ω) * ((cA : Ω) / (l : Ω))
    rw [mul_div_cancel₀ _ hl0]
  · exfalso
    rw [zpow_neg, zpow_natCast] at hk
    have e : A.valuation (cA : Ω) * A.valuation (l : Ω) ^ n = 1 := by
      rw [hk, inv_mul_cancel₀ (pow_ne_zero _ hvl0)]
    have : A.valuation (cA : Ω) * A.valuation (l : Ω) ^ n ≤ A.valuation (cA : Ω) :=
      mul_le_of_le_one_right' (pow_le_one' hl1.le _)
    rw [e] at this
    exact absurd hcv (not_lt.2 this)

end GlobalTheory.RecOne
end
end
