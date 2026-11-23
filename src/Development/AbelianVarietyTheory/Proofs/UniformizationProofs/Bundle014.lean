module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits TensorProduct

theorem _root_.GlobalTheory.T.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres_alt : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (g : ℕ), IsRegularLocalRing (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) → ringKrullDim (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) → (∀ p : PrimeSpectrum A, ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) ≤ p.asIdeal → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) → ∀ I : Ideal A, Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] (A ⧸ I)) → Module.Flat V (A ⧸ I) := by
  first | exact @GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres | exact GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres | (intros; apply GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiPow

theorem nonempty_torusExtension {K : Type} [Field K] {G' G : Over (Spec (CommRingCat.of K))} [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (E : TorusExtension G) : Nonempty (TorusExtension G') := by
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of K)) E.X (Fin j → E.X) j (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ G' G (powObj E.B j) E.B j p (powIsPowGrp E.B j) E.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p E.i
  exact ⟨{ X := Fin j → E.X
           B := powObj E.B j
           isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j (powIsPowGrp E.B j)).2.2.2.1 E.isAbelian
           q := q'
           q_hom := hq1 E.q_hom
           q_flat := hq2 E.q_flat
           q_surjective := hq3 E.q_surjective
           q_quasiCompact := hq4 E.q_quasiCompact
           i := i'
           i_hom := hi1 E.i_hom
           isKernel := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ j pT p (powIsPowGrp E.B j) E.i E.q i' q' hi hq
             E.isKernel }⟩

theorem isSemiAbelian_of_isPowGrp : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (j : ℕ) (_ : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G G' _ _ j p hG
  obtain ⟨h1, h2, -, -, h5⟩ := GlobalTheory.PowGrp.powers S G' G j p
  have hq := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p
  refine ⟨h5 hG, h1 hG.smooth, h2 hG.separated, hq.1 hG.quasiCompact, hq.2 hG.smooth hG.geomConnected,
    fun Ω _ _ f => ?_⟩
  obtain ⟨p', -⟩ := GlobalTheory.isPowGrp_baseChange S _ f G' G j p
  obtain ⟨E⟩ := hG.fibres Ω f
  exact nonempty_torusExtension p' E

end GlobalTheory.SemiPow
end
