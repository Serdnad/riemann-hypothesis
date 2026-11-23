module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle857
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SpecAbsolutelyIntegrallyClosedCohomology
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyExcisionAxiomHolds
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyFunctorialityAxiomsHold
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyIndEtaleBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

namespace UpperTheory.Gal.KunnethLefschetz
open GlobalTheory.EtC

theorem upTo {P : Prop} (h : A1 → A2 → A3 → A4 → A5 → A7 → A8 → A9 → A10 → A11 → B1 → B2 → B3 → B4 → B5 → B7 → C1 → C2 → C3 → C4 →
    C5 → D1 → P) : P :=
  h GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etC_a2 GlobalTheory.T.levelwiseEquivalence_isEquivalence GlobalTheory.T.mayerVietoris_equivalence_of_cover GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero
    GlobalTheory.T.etaleCohomology_bijective_of_support_bijective RedCoef.a11 GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity UpperTheory.etaleCohomology_functorialityAxioms_hold GlobalTheory.T.etC_b3 UpperTheory.etaleCohomology_excisionAxiom_holds GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology
    GlobalTheory.EtC.gaugeSplitting_holds GlobalTheory.EtC.etC_c2 UpperTheory.Cb.etale_cohomology_ind_etale_base_change HomotopyInv.homotopy_invariance_etale GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing projectiveBundleFormula_vectorBundle_any_space

theorem duality_diagonalClass_of_affineProperBaseChange (e1 : E1) : E2 :=
  UpperTheory.Et.E2.main ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.etaleCohomology_coefficient_longExactSequence, GlobalTheory.T.etaleCohomology_coefficientRing_invariance,
    GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero, GlobalTheory.T.etaleCohomology_bijective_of_support_bijective, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity, UpperTheory.etaleCohomology_functorialityAxioms_hold, GlobalTheory.T.etC_b3, UpperTheory.etaleCohomology_excisionAxiom_holds, GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic, e1⟩

end UpperTheory.Gal.KunnethLefschetz
