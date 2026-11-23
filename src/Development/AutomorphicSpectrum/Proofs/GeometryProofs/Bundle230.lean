module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle226
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle227
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TwoTorsionRankBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.StratumGenericTorsionPoints
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  first | exact @PositivityTheory.HtPt.Cd.germ_affine | exact PositivityTheory.HtPt.Cd.germ_affine
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RankBound

theorem rank_bound_of_points_of_order_two :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (k : Type) [Field k], ((2 : ℕ) : k) ≠ 0 → ∀ (x : Sp k ⟶ S) (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ (τ : TorusExtension Gk) (m : ℕ) (Q : Fin m → (Over.mk x ⟶ G)), Function.Injective Q → (∀ i, Q i ^ 2 = 1) → (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X ≤ 2 ^ (2 * g)) :=
  @PositivityTheory.Xgn.two_torsion_rank_bound

end GlobalTheory.CompanionTheory.Ar.RankBound
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_exp_chart_coordinates : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ), IsAbelianScheme A → Out.RelAmple A L → SmoothOfRelativeDimension g A.hom → ∃ u : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g, ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif | exact GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif | (intros; apply GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.level_and_hecke_of_zero_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | exact GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.LevelZero.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.GenTors

theorem exists_finite_ext_torusExtension_two_torsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :=
  PositivityTheory.Xgn.stratum_generic_torsion_points

end GlobalTheory.CompanionTheory.Ar.GenTors
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem locallyQuasiFinite_pow_semiAbelian :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N →
      LocallyQuasiFinite ((𝟙 G) ^ N).left := by
  intro S G _ hG N hN
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hm : IsMonHom ((𝟙 G) ^ N) := GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have : LocallyOfFiniteType (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType ((𝟙 G) ^ N).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (((𝟙 G) ^ N).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ((𝟙 G) ^ N).left := QuasiCompact.of_comp _ G.hom
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker S G G _ hm inferInstance inferInstance
    fun Ω _ _ t => ?_
  simp only [MonObj.comp_pow, Category.comp_id]
  exact GlobalTheory.HomExt.finite_torsion_points hG t hN

end GlobalTheory.CompanionTheory.Ar.BT
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_formal_germ_open_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine | exact GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.power_map_locally_quasi_finite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → LocallyQuasiFinite ((𝟙 G) ^ N).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian | exact GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian <;> assumption)

end
end
