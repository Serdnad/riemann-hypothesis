module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteNil

theorem thick_J_isNilpotent : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R}
    {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)), ∀ x ∈ T.J, IsNilpotent x := @_root_.GlobalTheory.CompanionTheory.ChartMaps.nil_J

end GlobalTheory.CompanionTheory.SiteNil
