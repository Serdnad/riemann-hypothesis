module

import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Closed
public import GroundTheory.ProfiniteCohomology.ClassFormationDefs
public import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic
import GroundTheory.ProfiniteCohomology.CoinducedModules.CohomologyCoindCokernelIsoHom
public import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
public import GroundTheory.ProfiniteCohomology.Factor
public import GroundTheory.ProfiniteCohomology.InflationRestriction
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
public import GroundTheory.ProfiniteCohomology.CoinducedModules
public import GroundTheory.ProfiniteCohomology.CupProducts

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

theorem eq_zero_of_coprime_nsmul_of_pow_nsmul {M : Type*} [AddCommGroup M] {ℓ m j : ℕ}
    (hm : m.Coprime ℓ) {x : M} (h1 : m • x = 0) (h2 : ℓ ^ j • x = 0) : x = 0 := by
  have hd : addOrderOf x ∣ Nat.gcd m (ℓ ^ j) :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h1) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  rw [Nat.Coprime.gcd_eq_one (hm.pow_right j), Nat.dvd_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.1 hd

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem eq_zero_of_cohomologyInfl_three_eq_zero (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G)
    [N.Normal] (hN : IsClosed (N : Set G)) (h1 : IsZero (cohomology (Rep.res N.subtype A) 1)) (ℓ : ℕ)
    (h2 : ∀ y : cohomology (Rep.res N.subtype A) 2, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0)
    (x : cohomology (A.quotientToInvariants N) 3) (hx : (cohomologyInfl A N 3).hom x = 0)
    (j : ℕ) (hj : ℓ ^ j • x = 0) : x = 0 := by
  have hX := coindShortComplex_shortExact A
  have hS := shortExact_map_res N hX
  have hQ := shortExact_map_quotientToInvariants_coindShortComplex A N h1
  have hδQ : IsIso (δ hQ (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hQ 1
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N 1)
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N (1 + 1))
  have hδX : IsIso (δ hX (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hX 1
    (isZero_cohomology_discreteCoind k G A 1) (isZero_cohomology_discreteCoind k G A (1 + 1))
  have hδS : IsIso (δ hS (0 + 1) (0 + 1 + 1) rfl) := isIso_δ_of_isZero hS 0
    (isZero_cohomology_res_discreteCoind (k := k) A N hN 0)
    (isZero_cohomology_res_discreteCoind (k := k) A N hN (0 + 1))
  have injQ : Function.Injective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injX : Function.Injective (δ hX (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injS : Function.Injective (δ hS (0 + 1) (0 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have surjQ : Function.Surjective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x', rfl⟩ := surjQ x
  have hsq := δ_comp_cohomologyInfl N hX hQ (1 + 1) (1 + 1 + 1) rfl
  have hx' : (cohomologyInfl (coindCokernel A) N (1 + 1)).hom x' = 0 := by
    have e : (δ hX (1 + 1) (1 + 1 + 1) rfl).hom ((cohomologyInfl (coindCokernel A) N (1 + 1)).hom x') =
        (cohomologyInfl A N 3).hom ((δ hQ (1 + 1) (1 + 1 + 1) rfl).hom x') :=
      (congrArg (fun φ => ModuleCat.Hom.hom φ x') hsq).symm
    exact injX (e.trans (hx.trans (map_zero _).symm))
  have hmem : x' ∈ LinearMap.ker (cohomologyInfl (coindCokernel A) N 2).hom := hx'
  rw [← (fiveTerm_exact (coindCokernel A) N hN).2.2.2] at hmem
  obtain ⟨w, rfl⟩ := hmem
  obtain ⟨m, hm, hmw⟩ := h2 ((δ hS (0 + 1) (0 + 1 + 1) rfl).hom w.1)
  have hw : m • w = 0 := by
    apply Subtype.ext
    apply injS
    exact (map_nsmul (δ hS (0 + 1) (0 + 1 + 1) rfl).hom m w.1).trans (hmw.trans (map_zero _).symm)
  have h1' : m • transgression (coindCokernel A) N hN w = 0 := by
    rw [← map_nsmul, hw, map_zero]
  have h2' : ℓ ^ j • transgression (coindCokernel A) N hN w = 0 := by
    apply injQ
    exact (map_nsmul _ (ℓ ^ j) _).trans (hj.trans (map_zero _).symm)
  have h0 := eq_zero_of_coprime_nsmul_of_pow_nsmul hm h1' h2'
  exact (congrArg (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom h0).trans (map_zero _)

section Extension

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A]


omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem inv_mul_contractNth_mem {n : ℕ} (V : Subgroup G) [V.Normal] (g g' : Fin (n + 1) → G)
    (h : ∀ i, (g i)⁻¹ * g' i ∈ V) (j : Fin (n + 1)) (i : Fin n) :
    (Fin.contractNth j (· * ·) g i)⁻¹ * Fin.contractNth j (· * ·) g' i ∈ V := by
  intros
  apply _root_.GroundTheory.ProfCoh.inv_mul_mem_contractNth <;> assumption

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem coe_contractNth {N : Subgroup G} {n : ℕ} (j : Fin (n + 1)) (g : Fin (n + 1) → N) (i : Fin n) :
    ((Fin.contractNth j (· * ·) g i : N) : G) = Fin.contractNth j (· * ·) (fun k => (g k : G)) i := by
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ h]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_eq _ _ _ _ h]
    rfl
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.contractNth_apply_of_gt _ _ _ _ h]

end Extension

section ExtensionLemma

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]

theorem exists_isOpen_cohomologyResLE_eq (N : Subgroup G) (hN : IsClosed (N : Set G)) (n : ℕ)
    (y : cohomology (Rep.res N.subtype A) n) :
    ∃ (H : Subgroup G) (_ : IsOpen (H : Set G)) (hNH : N ≤ H)
      (y' : cohomology (Rep.res H.subtype A) n), (cohomologyResLE A hNH n).hom y' = y := by
  apply _root_.GroundTheory.ProfCoh.exists_cohomologyResLE_eq <;> assumption

end ExtensionLemma

end GroundTheory.ProfCoh
