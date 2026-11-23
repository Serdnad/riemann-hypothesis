module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle045
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle046
public import Mathlib.Topology.Algebra.MulAction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle043
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle047
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle027
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle048
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Submodule

namespace GlobalTheory

theorem exists_nonZeroDivisor_smul_mem_of_span_eq_top_finlen {O K V : Type} [CommRing O] [IsDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (L : Submodule O V) (hspan : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ a ∈ nonZeroDivisors O, a • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, Submonoid.one_mem _, by simpa using hy⟩
  | zero => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, Submonoid.mul_mem _ ha hb, ?_⟩
    rw [smul_add, mul_comm a b, mul_smul, mul_comm b a, mul_smul a b z]
    exact L.add_mem (L.smul_mem b hay) (L.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
    dsimp only at hnd
    subst hnd
    refine ⟨a * d, Submonoid.mul_mem _ ha d.2, ?_⟩
    have key : ((d : O) : O) • (IsLocalization.mk' K n d • y) = n • y := by
      rw [← algebraMap_smul K (d : O), smul_smul, mul_comm, IsLocalization.mk'_spec,
        algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact L.smul_mem n hay

theorem finiteLength_projection_quotient :
    ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) (G B : Submodule K V), L.FG → Disjoint G B → Module.length O (↥(G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)) ⧸ (L ⊓ G.restrictScalars O).comap (G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)).subtype) ≠ ⊤ ∨ ¬ (Submodule.span K (L : Set V) = ⊤ ∧ G ⊔ B = ⊤) := by
  intro O K V _ _ _ _ _ _ _ _ _ _ L G B hL hdisj
  by_cases h : Submodule.span K (L : Set V) = ⊤ ∧ G ⊔ B = ⊤
  swap
  · exact Or.inr h
  left
  obtain ⟨hspan, hsup⟩ := h
  have hc : IsCompl G B := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  set π : V →ₗ[O] V := (G.projection B hc).restrictScalars O
    with hπ
  set up := G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O) with hup
  have hπfix : ∀ v ∈ G, π v = v := fun v hv =>
    Submodule.projection_apply_of_mem_left hc hv
  have hπzero : ∀ v ∈ B, π v = 0 := fun v hv =>
    Submodule.projection_apply_of_mem_right hc hv
  have hπG' : ∀ v : V, π v ∈ G := fun v => Submodule.projection_apply_mem hc v
  have hπB : ∀ v : V, v - π v ∈ B := by
    intro v
    have hv : v ∈ G ⊔ B := hsup ▸ Submodule.mem_top
    obtain ⟨g, hg, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _), hπfix g hg, hπzero b hb, add_zero, add_sub_cancel_left]
    exact hb
  have hmap : up = L.map π := by
    ext x
    constructor
    · rintro ⟨hxG, hxLB⟩
      obtain ⟨l, hl, b, hb, rfl⟩ := Submodule.mem_sup.mp hxLB
      refine ⟨l, hl, ?_⟩
      have h1 : π (l + b) = l + b := hπfix _ hxG
      have h2 : π b = 0 := hπzero b hb
      rw [map_add (f := _), h2, add_zero] at h1
      exact h1
    · rintro ⟨l, hl, rfl⟩
      refine ⟨hπG' l, ?_⟩
      have : π l = l - (l - π l) := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hl) (Submodule.mem_sup_right (hπB l))
  have hfg : up.FG := hmap ▸ hL.map π
  haveI : Module.Finite O up := Module.Finite.iff_fg.mpr hfg
  have htors : Module.IsTorsion O (↥up ⧸ (L ⊓ G.restrictScalars O).comap up.subtype) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨a, ha, hay⟩ := exists_nonZeroDivisor_smul_mem_of_span_eq_top_finlen (K := K) L hspan (y : V)
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨hay, ?_⟩
      exact (G.restrictScalars O).smul_mem a y.2.1
  exact Module.length_ne_top_iff.mpr (isFiniteLength_of_isTorsion htors)

end GlobalTheory
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_low_coeff_not_dvd_of_congr_mul' : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by
  first | exact @GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul | exact GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul | (intros; apply GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul <;> assumption)
end

section


theorem _root_.GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  first | exact @GlobalTheory.compact_dvr_complete_separated | exact GlobalTheory.compact_dvr_complete_separated | (intros; apply GlobalTheory.compact_dvr_complete_separated <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_free_module_compact_adic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M] (ϖ : O), Irreducible ϖ → CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧ Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  first | exact @GlobalTheory.finite_free_compact_adic_dvr | exact GlobalTheory.finite_free_compact_adic_dvr | (intros; apply GlobalTheory.finite_free_compact_adic_dvr <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero : ∀ (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Set.Finite {x : A | x ^ 2 = 1} := by
  first | exact @GlobalTheory.finite_sq_eq_one_of_finite_algebra | exact GlobalTheory.finite_sq_eq_one_of_finite_algebra | (intros; apply GlobalTheory.finite_sq_eq_one_of_finite_algebra <;> assumption)
end

section


theorem _root_.GlobalTheory.T.continuous_linearMap_of_finite : ∀ {O : Type} [CommRing O] [TopologicalSpace O] [CompactSpace O] {M M' : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Finite O M] [AddCommGroup M'] [Module O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul O M'] (f : M →ₗ[O] M'), Continuous f := by
  first | exact @GlobalTheory.linearMap_continuous_of_compactSpace_of_finite | exact GlobalTheory.linearMap_continuous_of_compactSpace_of_finite | (intros; apply GlobalTheory.linearMap_continuous_of_compactSpace_of_finite <;> assumption)
end

section

open Polynomial IsLocalRing

theorem _root_.GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one : ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]), f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 → ∃ y : S, f.eval y = 0 := by
  first | exact @GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | exact GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | (intros; apply GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  first | exact @GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | exact GlobalTheory.card_quotient_eq_of_pow_sub_self_mem | (intros; apply GlobalTheory.card_quotient_eq_of_pow_sub_self_mem <;> assumption)
end

section

open Module

theorem _root_.GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain : ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) → ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  first | exact @GlobalTheory.card_quot_span_pow | exact GlobalTheory.card_quot_span_pow | (intros; apply GlobalTheory.card_quot_span_pow <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_sum_mul_pow_of_residue_surjective_of_nilpotent : ∀ (C B : Type) [CommRing C] [CommRing B] (φ : C →+* B) (π : B) (L : C) (e m : ℕ), (∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π}) → π ^ e ∈ Ideal.span {φ L} → φ L ^ m = 0 → ∀ x : B, ∃ c : Fin e → C, x = ∑ j, φ (c j) * π ^ (j : ℕ) := by
  first | exact @GlobalTheory.span_powers_of_uniformizer_of_nilpotent | exact GlobalTheory.span_powers_of_uniformizer_of_nilpotent | (intros; apply GlobalTheory.span_powers_of_uniformizer_of_nilpotent <;> assumption)
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent : ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  first | exact @GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | exact GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | (intros; apply GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isBaseChange_lattice_of_basis_after_extension : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  first | exact @GlobalTheory.isBaseChange_subtype_of_basis_after_extension | exact GlobalTheory.isBaseChange_subtype_of_basis_after_extension | (intros; apply GlobalTheory.isBaseChange_subtype_of_basis_after_extension <;> assumption)
end
