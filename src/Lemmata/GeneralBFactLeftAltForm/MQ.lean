module


import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Mathlib.RingTheory.RegularLocalRing.Defs
@[expose] public section

namespace Bl.general_b_fact_left_alt_form

open Formalism.MainNotions.G in
theorem goal1
    {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O]
    {W : Type} [inst_3 : AddCommGroup W] [inst_4 : Module (KK O) W] [inst_5 : Module O W]
    [inst_6 : IsScalarTower O (KK O) W] (M : Submodule O W) (y : W) :
    y ∈ MQ (K := KK O) M → ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  apply @_root_.GlobalTheory.LatticeBoundedAction.main <;> assumption

end Bl.general_b_fact_left_alt_form
