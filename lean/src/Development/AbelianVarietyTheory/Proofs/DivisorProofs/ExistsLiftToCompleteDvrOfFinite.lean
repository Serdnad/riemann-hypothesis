import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosed
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IsLocalRingOfComplete
open IsLocalRing

namespace GlobalTheory

theorem exists_lift_to_complete_dvr_of_finite : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  intro A R _ _ _ hinj hfin V _ _ _ _ hC h
  classical
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  let K := FractionRing V
  let Ω := AlgebraicClosure K
  obtain ⟨ρ1, hρ1comp⟩ := exists_ringHom_extension_of_injective hinj
    ((algebraMap K Ω).comp ((algebraMap V K).comp h))
  have hρ1 : ∀ a : A, ρ1 (algebraMap A R a) = algebraMap K Ω (algebraMap V K (h a)) :=
    fun a => RingHom.congr_fun hρ1comp a
  obtain ⟨s, hs⟩ := hfin.fg_top
  let M : IntermediateField K Ω := IntermediateField.adjoin K (ρ1 '' (s : Set R))
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ r : R, ρ1 r ∈ M := by
    intro r
    have hr : r ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact M.add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def, map_mul, hρ1]; exact M.mul_mem (M.algebraMap_mem _) hx
  let ψ : R →+* M := ρ1.codRestrict M hmem
  have hψ : (algebraMap V M).comp h = ψ.comp (algebraMap A R) := by
    ext a
    simp only [RingHom.comp_apply]
    show (algebraMap V M (h a) : Ω) = ρ1 (algebraMap A R a)
    rw [hρ1]
    rfl
  have hint : ∀ r : R, ψ r ∈ integralClosure V M := fun r =>
    IsIntegral.map_of_comp_eq h ψ hψ (Algebra.IsIntegral.isIntegral r)
  let ρ : R →+* integralClosure V M := ψ.codRestrict (integralClosure V M) hint
  haveI hdvr := Formalism.L2.G.IntCl.isDVR V K M hC
  have hfinj := Formalism.L2.G.IntCl.alg_injective V K M
  haveI : FaithfulSMul V (integralClosure V M) := (faithfulSMul_iff_algebraMap_injective _ _).2 hfinj
  refine ⟨integralClosure V M, inferInstance, inferInstance, hdvr,
    (RingHom.charZero_iff hfinj).1 inferInstance, algebraMap V (integralClosure V M), ρ,
    Formalism.L2.G.IntCl.complete V K M hC, hfinj, Algebra.IsIntegral.isLocalHom _ _, ?_⟩
  ext a
  show ρ1 (algebraMap A R a) = (algebraMap V M (h a) : Ω)
  rw [hρ1]
  rfl

end GlobalTheory
