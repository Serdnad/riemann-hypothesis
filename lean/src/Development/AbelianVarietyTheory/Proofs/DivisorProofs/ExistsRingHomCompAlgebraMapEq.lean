import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosed

universe u_1 u_2 u_3

namespace GlobalTheory.InjectiveAlgebraHomExistence

theorem exists_algHom_of_injective {A : Type u_1} {B : Type u_2} {K : Type u_3}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra A K] [Algebra.IsIntegral A B]
    (hB : Function.Injective (algebraMap A B)) (hK : Function.Injective (algebraMap A K)) :
    Nonempty (B →ₐ[A] K) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).2 hK
  exact ⟨IsAlgClosed.lift⟩

theorem exists_ringHom_comp_algebraMap_eq {R : Type u_1} {S : Type u_2} {K : Type u_3}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (ψ : R →+* K) :
    ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  exact GlobalTheory.exists_ringHom_extension_of_injective hinj ψ

end GlobalTheory.InjectiveAlgebraHomExistence
