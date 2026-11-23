module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FiniteAbsLeOneMulMemRange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle128
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle122
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT



theorem functorial_of_unif :
    AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Functorial U := by
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hex := @GlobalTheory.EndData.exists_endU hL
  have hros := @GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU hL
  have hcalc := @GlobalTheory.EndCalc.end_calculus hL
  have hbal := @GlobalTheory.Balanced.main hL h1 h2 h3 h4
  intro R _ _ _ I hB D A G _ _ hG U
  refine ⟨hex R I hB D A G hG U, fun E E' hE => ⟨hros R I hB D A G hG U E E' hE, fun F _ _ _ => ?_⟩⟩
  exact ⟨(hcalc R I hB D A G hG U F E E E).1, hbal R I hB D A G hG U F E E' hE⟩

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.Cl

theorem galois_holds : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Galois U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ F' _ _ _ σ k hk p
  refine ⟨qkExtExists R D.toPre F F' σ.toRingHom σ.commutes k p, fun x => ?_, fun p' x x' hp hx =>
    TorsionExt.qkToAkU_iff_of_qkExt firstFiveLaws R I hI D A G hG U F F' σ k hk p p' x x' hp hx⟩
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  exact ⟨TorsionExt.fieldMap F F' ≫ x, rfl⟩

end GlobalTheory.UT.Cl
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem exists_weightPoints : Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∃ c : s.X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  intro hL V _ _ _ A G _ _ s
  have h1 := GlobalTheory.T.exists_point_representing_weight_mumfordQuotient hL V A G s
  have h2 := GlobalTheory.T.mumfordTower_repWt_unique hL V A G s
  have h3 := GlobalTheory.T.mumfordTower_repWt_mul_add V A G s
  intro t a hK
  choose c hc using h1 t a hK
  refine ⟨c, fun χ χ' => ?_, hc⟩
  exact h2 t a hK (χ + χ') _ _ (hc _) fun e => h3 t a χ χ' _ _ e (hc χ e) (hc χ' e)

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.all_uniformization_laws_hold : LL := by
  first | exact @GlobalTheory.firstFiveLaws | exact GlobalTheory.firstFiveLaws | (intros; apply GlobalTheory.firstFiveLaws <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.keyFormulaPow_and_keyDegree :
    _root_.GlobalTheory.KeyFormulaPow ∧ _root_.GlobalTheory.KeyDegreeSt := by
  obtain ⟨N, hN, hrule⟩ := _root_.GlobalTheory.KeyTop.exists_keyRule_charHalf
    _root_.GlobalTheory.abelianSchemeLaws_all.1 _root_.GlobalTheory.thetaUnifAV_closed
    _root_.GlobalTheory.inversionStatement_holds
    (_root_.GlobalTheory.phHolo_of_phKoecher _root_.GlobalTheory.phKoecher)
    _root_.GlobalTheory.torusAlgebraic_holds
  have hpow : _root_.GlobalTheory.KeyFormulaPow :=
    _root_.GlobalTheory.KeyPow.keyFormulaPow_of_keyRule _root_.GlobalTheory.thetaUnifAV_closed
      N hN hrule
  exact ⟨hpow, _root_.GlobalTheory.keyDegree_of_keyFormulaPow hpow⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

theorem _root_.GlobalTheory.T.exists_cmEllipticCurve_withPeriod : CMCurve := by
  first | exact @GlobalTheory.cmCurve_closed | exact GlobalTheory.cmCurve_closed | (intros; apply GlobalTheory.cmCurve_closed <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem uTors_closed : GlobalTheory.ZH.UTorsSt :=
  GlobalTheory.T.uniformisation_torsion_eq_of_laws GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.2.1

end GlobalTheory.ZH
end

section

namespace GlobalTheory

theorem arcClause_closed : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition :=
  GlobalTheory.T.holomorphic_degenerationArc_of_uniformisation GlobalTheory.T.abelianScheme_laws_unconditional.1 GlobalTheory.T.abelianScheme_laws_unconditional.2 GlobalTheory.T.thetaUniformisation_complexAbelianVariety

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.theta_constant_valuations_units_every_coset : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → (∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧ (v c = 0 → ∃ z, p.y = m • z)) ∧ ∀ n, 2 ≤ n → n ∣ m → ∀ (p : QkPt D.toPre F (m ^ 2)) x, p.y = 0 → QkToAkU U.toUnifPre F (m ^ 2) p x → ∃ (p' : QkPt D.toPre F (m ^ 2)) (x' : _) (t : _) (c : F), p'.y = 0 ∧ QkToAkU U.toUnifPre F (m ^ 2) p' x' ∧ (x' ^ m * (x ^ m)⁻¹) ^ n = 1 ∧ ThC A ρ m th x' t c ∧ v c = 0 := by
  first | exact @GlobalTheory.UT.ThetaConstVal.main | exact GlobalTheory.UT.ThetaConstVal.main | (intros; apply GlobalTheory.UT.ThetaConstVal.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → (∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g') ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x, p'.y = E'.h p.y → E.Act p.g p'.g → QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  first | exact @GlobalTheory.Balanced.main | exact GlobalTheory.Balanced.main | (intros; apply GlobalTheory.Balanced.main <;> assumption)
end
