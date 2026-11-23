module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginRootIndexBound
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneous
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle134
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle135
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanValueBound
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_root_index_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (ρ : RootIx Dw) (q : Cpt Or.𝔐.ξ) (ch : (k : RM.K) → RM.ι k), InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) ch q → ∀ (b : Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1) → Or.𝔐.Li) (Tm : Matrix (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) (Fin (labelRk Dw (HodgeCpt.rootIdx Dw ρ).1)) RM.Ω), (∀ i : ℕ, flagStep RM.Ω b i = flagStep RM.Ω (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) i) → (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1).IsFrameAt b q → (∀ i, b i = ∑ j, Tm i j • Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1 j) → (∀ i, Tm i i ≠ 0) → ((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ) ∈ regAt Or.𝔐.ξ q ∧ (((∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) * Or.e ρ) * (Tm (HodgeCpt.rootIdx Dw ρ).2 (HodgeCpt.rootIdx Dw ρ).2) ^ (-HodgeCpt.rootSgn Dw ρ))⁻¹ ∈ regAt Or.𝔐.ξ q := by
  exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.RootUnit.root_unit
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.root_origin_component_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → ∃ ψ : kap Z ≃+* Or.𝔐.Ω₀, spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ ∧ ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv | exact GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.coord_relations_homogeneous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ k : K, ∃ (l : ℕ) (n : Fin l → ℕ) (F : Fin l → J k → MvPolynomial (J k₀) ℤ), (∀ t j, (F t j).IsHomogeneous (n t)) ∧ (∀ t j j', MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j) * y ⟨k, j'⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j') * y ⟨k, j⟩) ∧ ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ t j, MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F t j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | exact GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | (intros; apply GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.same_orbit_of_proportional_coords : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ w ∈ mcPts (mCoordIdeal y), ∀ w' ∈ mcPts (mCoordIdeal y), ∀ u : ℂ, (∀ i : J k₀, w ⟨k₀, i⟩ = u * w' ⟨k₀, i⟩) → SameOrbit w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block | exact GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block | (intros; apply GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.holomorphic_atlas_coord_compat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (e : ℕ) (M : Type) [TopologicalSpace M] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e M) (U : M → Set M) (lam : M → M → (Σ k, J k) → ℂ), Cmp.IsEmbedded A (mCoordIdeal y) U lam → ∀ (κ : Type) [Fintype κ] (ix : κ ≃ J k₀) (x : M) (p : κ), lam x x ⟨k₀, ix p⟩ ≠ 0 → ∀ j, x ∈ (A.chart j).source → DifferentiableAt ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x) ∧ (fderiv ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x)).ker = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ImmBlock.immersion_block | exact GlobalTheory.CompanionTheory.Ar.ImmBlock.immersion_block | (intros; apply GlobalTheory.CompanionTheory.Ar.ImmBlock.immersion_block <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

structure AbQuot (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) where

  tB : SAB H (Sp k)
  proper : IsProper tB.G.hom
  ktriv : Out.KTriv tB.G tB.PP.L

  Ch : Type
  [acg : AddCommGroup Ch]
  [free : Module.Free ℤ Ch]
  [fin : Module.Finite ℤ Ch]

  q : (Over.pullback x).obj t.G ⟶ tB.G
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_quasiCompact : QuasiCompact q.left

  i : splitTorus (Sp k) Ch ⟶ (Over.pullback x).obj t.G
  i_hom : IsMonHom i

  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ tB.G)

  act_q : ∀ a, (Over.pullback x).map (t.act.act a) ≫ q = q ≫ tB.act.act a

  bun : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (tB.PP.L.pull q.left)

attribute [instance] AbQuot.acg AbQuot.free AbQuot.fin

variable [StarRing (𝓞 E)]

def AbQuot.IsDiff {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} (Q : AbQuot t x) {d d' : ℕ} (g : GermAt t x d)
    (gB : GermAt Q.tB (𝟙 (Sp k)) d') (P : Matrix (Fin d') (Fin d) k) : Prop :=
  ∀ (l : Fin d) (v : Sp (DualNumber k) ⟶ ((Over.pullback x).obj t.G).left),
    v ≫ pullback.fst t.G.hom x = g.tg l → v ≫ ((Over.pullback x).obj t.G).hom = spMap (algebraMap k (DualNumber k)) →
      IsCombAtG Q.tB (𝟙 (Sp k)) gB.tg (fun i => P i l) (v ≫ Q.q.left)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem powFns_of_proper_algClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] (tB : SAB H (Sp k)), IsProper tB.G.hom → PowFns tB :=
  fun _ _ _ _ _ _ _ _ tB hp n =>
    haveI := hp
    AbelianSchemeGerms.globalFns_powObj GlobalTheory.globalFns_holds tB.G tB.semi n

end GlobalTheory.CompanionTheory.Ar.Conj.ProperPowFns
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.frame_point_abelian_map_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (y : FrPt Xo c F) (t' : SAB H (Spec (CommRingCat.of F))) (m1 : SABMap t' Xo.univ.t y.x) (g : Spec (CommRingCat.of F) ⟶ X), Small.ptY Y y = g ≫ f → ∃ b : t'.G.left ⟶ tX.G.left, IsGrpPullback t'.G tX.G g b ∧ (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (u' : Spec (CommRingCat.of (DualNumber F)) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) → u' ≫ b ≫ m.φ = Small.tanY Y y τ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.join_coords_coordTie : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω), (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | exact GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.archimedean_value_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (q m : ℕ) (u : Ω), IsSmoothHerm A → 0 < q → 0 < m → (m : Ω) * u ^ q ∈ chartLatNm y A.a q → ∃ C : ℝ, ∀ z ∈ ptsOver ℂ (mCoordIdeal y), ∀ val : ℂ, HasVal y A.a u z val → ‖val‖ ≤ Real.exp C * A.h z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound | exact GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.ArchBd.section_bound <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.specialization_coord_ratio_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (A : Subring Ω) (ev : A →+* 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → (∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x)) → ∀ (c : (k : K) → ι k), (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, ev ⟨_, hr k i⟩ = z ⟨k, i⟩ / z ⟨k, c k⟩) ∧ ∀ a : A, ∃ b : A, ev b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator | exact GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator | (intros; apply GlobalTheory.CompanionTheory.Ar.DenValue.value_and_denominator <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.value_scaling_by_monomial : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L) (a : K → ℤ) (s : Ω) (w : L), Small.HasVal y (0 : K → ℤ) s z w → w ≠ 0 → ∀ c : (k : K) → J k, (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k, z ⟨k, c k⟩ ≠ 0) → ∃ v : L, v ≠ 0 ∧ Small.HasVal y a (s * ∏ k, y ⟨k, c k⟩ ^ a k) z v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartTwist.hasVal_twist | exact GlobalTheory.CompanionTheory.Ar.ChartTwist.hasVal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartTwist.hasVal_twist <;> assumption)
end
