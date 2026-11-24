module


import Formalism.SharpRestriction.CuspSpanNormBounds.JExistsNatSmulMemL
public import Formalism.LocalRingCardinality.DataSpaces
@[expose] public section

namespace Bl.general_b_fact_left_alt

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] {S : Formalism.BasicNotions.HSpace E}
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsFullLattice.{0, 0, 0} E Λ →
    ∀ (v : S.V),
      Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} c 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} c v)) :=
  @_root_.Formalism.MainNotions.LatticeGluingRadicals.a_exists_smul_memL

end Bl.general_b_fact_left_alt
