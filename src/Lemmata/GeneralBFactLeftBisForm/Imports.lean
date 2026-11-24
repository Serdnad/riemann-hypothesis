module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Lemmata.GeneralBFactAltForm.Imports

@[expose] public section

namespace Bl.general_b_fact_left_bis_form

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O] [inst_1 : IsDomain.{0} O] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} O V] [inst_4 : Module.{0, 0} (Formalism.MainNotions.G.KK.{0} O) V]
  [IsScalarTower.{0, 0, 0} O (Formalism.MainNotions.G.KK.{0} O) V] (M : Submodule.{0, 0} O V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} (Formalism.MainNotions.G.KK.{0} O) (SetLike.coe.{0, 0} M)) y →
    Exists.{1} fun (s : O) ↦ And (Ne.{1} s 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} s y))  := by
  intro O _ _ V _ _ _ _ M y hy
  exact Bl.general_b_fact_alt_form.goal1 (F := Formalism.MainNotions.G.KK O) M hy

end Bl.general_b_fact_left_bis_form
