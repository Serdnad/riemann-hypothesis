import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientSpanSingleton

universe u_1 u_2

namespace GlobalTheory.LengthCokernelFinrank

open Module Submodule IsDiscreteValuationRing

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  have h0 : Module.length R (R ⧸ Ideal.span {(0 : R)}) = ⊤ := by
    have h := Ring.ord_eq_addVal (0 : R)
    rw [addVal_zero] at h
    exact h
  have hle := Module.length_le_of_surjective (Submodule.mkQ (Ideal.span {(0 : R)}))
    (Submodule.mkQ_surjective _)
  rw [h0] at hle
  exact top_le_iff.mp hle

theorem addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) :=
  LengthQuotientValuationDet.addVal_prod s a

variable {M : Type u_2} [AddCommGroup M] [Module R M]

theorem length_eq_top_of_finrank_ne_zero [Module.Finite R M] (h : finrank R M ≠ 0) :
    Module.length R M = ⊤ := by
  have hnt : ¬ Module.IsTorsion R M := fun ht => h (Module.finrank_eq_zero_iff_isTorsion.mpr ht)
  have hx : ∃ x : M, ∀ a : R, a • x = 0 → a = 0 := by
    by_contra hc
    push Not at hc
    apply hnt
    intro x
    obtain ⟨a, ha, ha0⟩ := hc x
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, ha⟩
  obtain ⟨x, hx⟩ := hx
  have hinj : Function.Injective (LinearMap.toSpanSingleton R M x) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact hx a (by simpa using ha)
  have hle := Module.length_le_of_injective _ hinj
  rw [length_self_eq_top] at hle
  exact top_le_iff.mp hle

theorem length_coker_eq_addVal_det [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  classical
  by_cases hk : LinearMap.ker f = ⊥
  · exact LengthQuotientValuationDet.length_quotient_eq_addVal_det (LinearMap.range f)
      (LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hk))
  · rw [LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk, addVal_zero]
    apply length_eq_top_of_finrank_ne_zero
    intro h0
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
    have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
    rw [(LinearMap.quotKerEquivRange f).finrank_eq] at h2
    have h3 : finrank R (LinearMap.ker f) = 0 := by omega
    exact hk (Submodule.finrank_eq_zero.mp h3)

end GlobalTheory.LengthCokernelFinrank
