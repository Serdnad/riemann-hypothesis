module


import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Noetherian.Basic
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open IsLocalRing

theorem isNoetherianRing_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  classical
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).1 inferInstance I
  let A := AdicCompletion I R
  let K := I.map (algebraMap R A)
  let : WithIdeal R := ⟨⊥⟩
  let : WithIdeal A := ⟨K⟩
  have hcomplete : IsAdicComplete K A :=
    AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  have htop := (IsAdic.isAdicComplete_iff (show IsAdic K from rfl)).mp hcomplete
  have : CompleteSpace A := htop.1
  have : T2Space A := htop.2
  let vars : s → A := fun i ↦ algebraMap R A i
  have hvars : MvPowerSeries.HasEval vars := by
    constructor
    · exact fun i ↦ WithIdeal.isTopologicallyNilpotent_of_mem
        (Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span i.property))
    · simp [Filter.cofinite_eq_bot]
  have hcont : Continuous (algebraMap R A) :=
    (WithIdeal.uniformContinuous_of_map_le (f := algebraMap R A) (by
      change Ideal.map (algebraMap R A) ⊥ ≤ K
      simp)).continuous
  let ψ := MvPowerSeries.eval₂Hom hcont hvars
  let J : Ideal (MvPowerSeries s R) := Ideal.span (Set.range MvPowerSeries.X)
  have hψ_map : J.map ψ = K := by
    rw [show J = Ideal.span (Set.range MvPowerSeries.X) from rfl, Ideal.map_span, ← Set.range_comp]
    change Ideal.span (Set.range (fun i : s ↦ ψ (MvPowerSeries.X i))) = K
    have hX (i : s) : ψ (MvPowerSeries.X i) = vars i := by
      simp [ψ, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
    simp_rw [hX]
    change Ideal.span (Set.range (algebraMap R A ∘ ((↑) : s → R))) = K
    rw [Set.range_comp, Subtype.range_coe_subtype]
    change Ideal.span ((algebraMap R A) '' (s : Set R)) = K
    rw [← Ideal.map_span, hs]
  -- Evaluation is surjective because its reduction modulo the defining ideal is.
  have hhaus : IsHausdorff (J.map ψ) A := hψ_map ▸ hcomplete.toIsHausdorff
  apply isNoetherianRing_of_surjective _ _ ψ
  apply surjective_of_mk_map_comp_surjective (I := J)
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I y)
  refine ⟨MvPowerSeries.C r, Ideal.Quotient.eq.2 ?_⟩
  change ψ (MvPowerSeries.C r) - y ∈ J.map ψ
  have hC : ψ (MvPowerSeries.C r) = algebraMap R A r := by
    simp [ψ, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
  rw [hψ_map, hC]
  change algebraMap R A r - y ∈ I.map (algebraMap R A)
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ I.fg_of_isNoetherianRing,
    RingHom.mem_ker, map_sub, sub_eq_zero]
  simpa [AdicCompletion.algebraMap_apply] using hr

instance instIsNoetherianRingAdicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) :=
  isNoetherianRing_adicCompletion R I

end GroundTheory.Arith.Etale
