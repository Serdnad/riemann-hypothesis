import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExtTensor
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem indOrder_id_eq_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A :=
  PositivityTheory.HtPt.Mh.ind_id

end GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.hopf_order_induction_id : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder :=
  @_root_.GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder
