module

public import Formalism.LocalRingCardinality.DataSpaces
import Lemmata.GeneralBFactAltForm.Imports

@[expose] public section

namespace Bl.general_b_fact_third_extra

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] {S : Formalism.BasicNotions.HSpace E}
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} Λ)) Top.top.{0} →
    ∀ (v : S.V),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} d v)) := by
  intro E _ _ _ S Λ hspan v
  exact Bl.general_b_fact_alt_form.goal1 (F := E) Λ (by simp [hspan])

end Bl.general_b_fact_third_extra
