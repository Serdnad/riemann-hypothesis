module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Lemmata.GeneralBFactAltForm.Imports

@[expose] public section

namespace Bl.general_b_fact_left_version

open Formalism.MainNotions.G in
theorem goal1
    {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] {V : Type}
    [inst_2 : AddCommGroup V] [inst_3 : Module (KK O) V] [inst_4 : Module O V]
    [inst_5 : IsScalarTower O (KK O) V] (M : Submodule O V) :
    MQ (K := KK O) M = ⊤ → ∀ x : V, ∃ a : O, a ≠ 0 ∧ a • x ∈ M := by
  intro hM x
  exact Bl.general_b_fact_alt_form.goal1 (F := KK O) M (by
    change x ∈ MQ (K := KK O) M
    simp [hM])

end Bl.general_b_fact_left_version
