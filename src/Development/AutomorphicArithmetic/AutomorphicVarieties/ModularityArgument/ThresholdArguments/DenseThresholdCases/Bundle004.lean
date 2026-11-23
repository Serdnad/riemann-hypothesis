module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section




section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.U3 UpperTheory.V.Base in
def UpperTheory.GalN.V.RigidityEndomorphismWeightTwo : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω)
    (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 →
    Pr.HasFrame c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B M →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
      (r : G ℚ Ω →* GG (m := 3) (R := A)),
      Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
      ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω], Module.finrank ℚ K = 2 → η.ker = galOf ℚ K Ω →
      ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous W → (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (∀ g, (W g).val.det = ((η g : ℤˣ) : ℤ)) →
      (∃ π : GlobalTheory.CuspRep.CuspSub K 2, (GlobalTheory.CuspRep.CG.mk π).IsRegAlg ∧
        Af.AttC ι (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) π) →
      _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → FreeAt l W → AdZero2 K η W
end
end

section




section
namespace GlobalTheory.Mem.LiteralAutomorphy
open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published
structure LitLocAlt : Prop where
  bz : BernsteinZelevinskyFiniteness
  bern : BernsteinUnitaryProductIrreducible
  geo : GeometricLemma
  zel : ZelevinskyPolynomialRing
  disj : TotallyDisjointProductIrreducible
  mp : MoyPrasadJacquetIso
  temp : TemperedProductOfSquareIntegrable
  seg : EssSquareIntegrableSegments
  sq : SquareIntegrableSegment
  gen : GenericUnlinkedGL
  multi : LanglandsMultisegments
  exh : LanglandsExhaustionGL
  cos : StandardCosocleGL
  conv : LocalConverseGL
  dzi : DepthZeroInduction
  brauer : BrauerDegreeZero
  chev : ChevalleyUnits
  green : GreenRegularCharacters
structure LiteratureAutomorphyHypothesis : Prop where
  decay : CuspRapidDecay
  hc : HarishChandraFinite
  fin : AutomorphicFormsFiniteGL
  js : JacquetShalika
  cusp : CuspidalSpectrumGL
  bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN
  gk : GelfandKazhdanDual
  gal : _root_.UpperTheory.V.Z.Win.RowT
  pur : ClozelPurity
  coh : ClozelCohomological
  art : GlobalArtinReciprocity
  ray : RayClassFieldSt
  chA : HeckeLAdicCharacterAbove
  chW : AlgebraicCharacterWD
  berger : DeRhamPotSemistable
structure LiteratureCMHypothesis : Prop where
  gm : GrothendieckDeformation
  dr : AbelianDeRham
  dual : AbelianDualCrystal
  per : PeriodComparison
  gmp : GaussManinPeriods
  st : SerreTateGoodReductionSt
  cm : EllipticMainTheoremCM
  hj : HilbertClassFieldJ
  dri : SiegelKlingenDeligneRibet
  pz : PartialZetaFunctionalEquation
  fe : HeckeTateFunctionalEquation
structure LiteratureRankNHypothesis : Prop where
  loc : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt
  aut : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis
  coh : LitCoh
  cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis
end GlobalTheory.Mem.LiteralAutomorphy
end
end
