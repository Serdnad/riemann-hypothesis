import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SectionLawsOfH0EqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankSectionsPrincipalPolarisationEqOne

namespace GlobalTheory.Reg

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

open NumberField in

theorem _root_.GlobalTheory.Reg.genFrEx_and_genFromTest : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.Formalism.L2.Pj.GenFrEx Xo c ∧ ∀ h : _root_.Formalism.L2.Pj.GenFrEx Xo c, _root_.Formalism.L2.Pj.GenFromTest Xo c h := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨_, hBaseChange, hTwist⟩ := _root_.GlobalTheory.AbLaw.section_laws_of_h0_eq_one
    _root_.GlobalTheory.AbLaw.finrank_sections_principal_polarisation_eq_one
  refine ⟨_root_.Formalism.L2.Pj.genFrEx_of hTwist, fun h Z => ?_⟩
  exact _root_.GlobalTheory.Frames.allTest_of_secBaseChange hBaseChange E H Dw l Xo c _ _

end GlobalTheory.Reg
