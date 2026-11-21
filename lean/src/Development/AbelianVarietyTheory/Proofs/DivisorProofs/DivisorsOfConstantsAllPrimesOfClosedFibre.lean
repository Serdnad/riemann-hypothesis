import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialBaseLocalization
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

open GlobalTheory.LocAcyc in
theorem divConstAll_of_divConstLocal : DivConstLocal → DivConstAll := by
  intro hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH
  refine polynomialClaim_of_localization (fun T O _ _ _ => DivConst T O) ?_ ?_ T O hAIC P φ hφ hSH
  · intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hmax
    exact hL T O hAIC P φ hφ hSH hmax trivial
  · intro T T' O _ _ _ _ _ _ _ _ M _ hM hunit key
    have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hM
    intro b c s hs hbc
    have hs' : algebraMap T T' s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
    rw [IsScalarTower.algebraMap_apply T T' O] at hbc
    obtain ⟨a', w, hb⟩ := key b c _ hs' hbc
    obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective M a'
    obtain ⟨v, hv⟩ := hunit u
    refine ⟨a, v⁻¹ * w, ?_⟩
    rw [hb, Units.val_mul, ← mul_assoc]
    congr 1
    rw [Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a,
      IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.VertUnits
