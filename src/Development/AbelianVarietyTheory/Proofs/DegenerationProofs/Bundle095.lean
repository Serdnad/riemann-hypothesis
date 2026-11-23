module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulMemAdjoinOfMemPowRange
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimQuotientLeOne
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle086
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_good_torsion_translate_of_section : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  first | exact @GlobalTheory.UnitTheta.exists_good_point_of_sec | exact GlobalTheory.UnitTheta.exists_good_point_of_sec | (intros; apply GlobalTheory.UnitTheta.exists_good_point_of_sec <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.psiUnitOn_of_fixed_over_unramified_extension : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (D : DegPre R), D.TauBimult → D.PsiEven → ∀ (P : PrimeSpectrum R), P.asIdeal.height = 1 → ∀ (n : ℕ), 2 ≤ n → (∀ (j : ℕ), ∃ (T' : Subring (AlgebraicClosure (FractionRing R))) (_ : IsDiscreteValuationRing T') (f : Localization.AtPrime P.asIdeal →+* T'), (∀ r : R, (f (algebraMap R _ r) : AlgebraicClosure (FractionRing R)) = algebraMap (FractionRing R) _ (algebraMap R _ r)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ (σ : AlgebraicClosure (FractionRing R) ≃+* AlgebraicClosure (FractionRing R)), (∀ x ∈ T', σ x = x) → ∀ p q : QkPt D (AlgebraicClosure (FractionRing R)) (n ^ j), QkExt σ.toRingHom p q → QkPt.Equiv D _ p q) → ∀ y, ∃ V : (Sp R).Opens, P ∈ V ∧ PsiUnitOn D y V := by
  first | exact @GlobalTheory.UnramTorsion.psiUnitOn_of_unramified | exact GlobalTheory.UnramTorsion.psiUnitOn_of_unramified | (intros; apply GlobalTheory.UnramTorsion.psiUnitOn_of_unramified <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_mem_nonzeroLocus_fibre_of_secBasis : SecBaseChangeAnySt → ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ s : Sp R, ∃ y ∈ nonzeroLocus th, P.A.hom ((snd (baseOver (Sp R)) P.A).left y) = s := by
  first | exact @GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre | exact GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre | (intros; apply GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem card_torsion_zeros_twist_le :
    Out.Laws → Out.Laws2 → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (c : Out.baseOver (Sp K) ⟶ P.A), 1 ≤ P.g → 4 ≤ N → 1 ≤ d → (k : K) ≠ 0 → ∀ s : LB.Sec (Out.twistLB P.A P.L (N * d) c), (∃ j, s.f j ≠ 0) → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = 1 ∧ ¬ ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s} ≤ N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) :=
  fun h _ => torsion_zero_count_twist h.mulN h.square
    (card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.torusPoint_with_characters_iff_pullDeg : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left → (∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ D.Oφ g.pG (hD.xe x) k, LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x) (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ (g.t (hD.xe x)))) → ∀ (T : Scheme.{0}) (z : T ⟶ (thickObj R' I' e G').left) (a : D'.X → Γ(T, ⊤)), (∃ τ' : T ⟶ (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left, τ' ≫ g'.i.left = z ∧ ∀ x, τ'.appTop.hom (charUnit _ D'.X x).val = a x) ↔ ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, τ ≫ g.i.left = z ≫ h ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (hD.xe x)).val = a x := by
  first | exact @GlobalTheory.TorusPull.torus_point_iff | exact GlobalTheory.TorusPull.torus_point_iff | (intros; apply GlobalTheory.TorusPull.torus_point_iff <;> assumption)
end
