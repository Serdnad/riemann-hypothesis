module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Monoid
import Lemmata.GeneralBFactBis.Imports

@[expose] public section

namespace Bl.general_b_fact_ter_form

theorem goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) :=
  @_root_.Bl.general_b_fact_bis.goal1

end Bl.general_b_fact_ter_form
