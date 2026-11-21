import Mathlib

namespace GlobalTheory

/-- A point with values in an algebraically closed field lifts along an integral
algebra map when it vanishes on the kernel. Choose a prime over the
kernel of the point and lift through the resulting domain. -/
theorem exists_ringHom_extension_of_ker_le {A B K : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K]
    (φ : A →+* K) (h : RingHom.ker (algebraMap A B) ≤ RingHom.ker φ) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = φ := by
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker φ) ⊥ h
  haveI : Q.IsPrime := hQ
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker φ) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective φ)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker φ) (B ⧸ Q) :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker φ)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let ψ : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker φ] K := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun a => ?_⟩
  exact (ψ.commutes (Ideal.Quotient.mk _ a)).trans (RingHom.kerLift_mk φ a)

/-- An injective integral algebra map lifts every point over an algebraically
closed field. -/
theorem exists_ringHom_extension_of_injective {A B K : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K]
    (hinj : Function.Injective (algebraMap A B)) (φ : A →+* K) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = φ := by
  apply exists_ringHom_extension_of_ker_le φ
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  exact bot_le

theorem ringHom_extend_of_isIntegral_isAlgClosed (A C K : Type) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K)
    (hk : RingHom.ker (algebraMap A C) ≤ RingHom.ker h) :
    ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  exact exists_ringHom_extension_of_ker_le h hk

end GlobalTheory
