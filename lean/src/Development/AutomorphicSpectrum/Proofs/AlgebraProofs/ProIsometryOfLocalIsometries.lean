import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CrtGood

open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem ProIso.nonempty_of_forall_prime : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_crt

end GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.pro_isometry_of_local_isometries : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime :=
  @_root_.GlobalTheory.CompanionTheory.Ar.ProIso.nonempty_of_forall_prime
