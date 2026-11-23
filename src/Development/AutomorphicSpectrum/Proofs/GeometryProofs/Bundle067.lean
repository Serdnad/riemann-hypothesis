module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle057
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle059
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem hermLine_pull_blockMap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k), IsBlockMap κ v → (∀ A : HermLine ι, ∃! A' : HermLine ι', IsPullHerm κ v A A') ∧ (∀ (A : HermLine ι) (A' : HermLine ι'), IsPullHerm κ v A A' → IsSmoothHerm A → IsSmoothHerm A') ∧ (∀ (P' : Ideal (MRing ι')), ∀ z ∈ mcPts P', (fun p => z (v p)) ∈ mcPts (imageZ v P')) ∧ ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f :=
  @PositivityTheory.UnitarySelfGeneration.j_pull

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.block_join_inclusions_compat : (∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω : Type) (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω), IsBlockMap Sum.inl (joinInl ι₁ ι₂) ∧ IsBlockMap Sum.inr (joinInr ι₁ ι₂) ∧ joinVec y₁ y₂ ∘ joinInl ι₁ ι₂ = y₁ ∧ joinVec y₁ y₂ ∘ joinInr ι₁ ι₂ = y₂) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] (y : (Σ k, ι' k) → Ω), IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (K'' : Type) [Fintype K''] (ι'' : K'' → Type) [∀ k, Fintype (ι'' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (κ' : K' → K'') (v' : (Σ k, ι' k) → Σ k, ι'' k), IsBlockMap κ v → IsBlockMap κ' v' → IsBlockMap (κ' ∘ κ) (v' ∘ v) ∧ ∀ a, pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps | exact GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.frame_open_neighbourhood : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.frame_spread_near | exact GlobalTheory.CompanionTheory.Ar.frame_spread_near | (intros; apply GlobalTheory.CompanionTheory.Ar.frame_spread_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.join_coords_centre_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.join_points_charts | exact GlobalTheory.CompanionTheory.Ar.join_points_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.join_points_charts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chart_prime_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) :=
  @PositivityTheory.HtPt.Ma.prime_pt

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chRing_basicOpen_basis : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U :=
  @PositivityTheory.HtPt.Ma.basic

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chart_regAt_localisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v :=
  PositivityTheory.HtPt.Ma.regat_loc

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_le_regAt_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 :=
  @PositivityTheory.HtPt.Ma.reg_le_spec

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.dense_open_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), M.ξ ≫ f = y₀ ≫ Y.j → ∃ U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens, Dense (U : Set ((pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}))) ∧ pullback.fst (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' (f ⁻¹' abLocus Y.t.G) = U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus.exists_dense_open | exact GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus.exists_dense_open | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus.exists_dense_open <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lattice_flag_field_extension : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull | exact GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

theorem _root_.GlobalTheory.T.lie_lattice_range_of_stalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range | exact GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.piece_localization_at_element : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (R : Subring Ω) (a : Ω), IsCptGen ξ → IsPiece ξ U R → a ∈ R → a ≠ 0 → ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece <;> assumption)
end
