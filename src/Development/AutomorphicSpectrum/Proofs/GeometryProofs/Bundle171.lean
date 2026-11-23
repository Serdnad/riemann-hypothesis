module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginWeightFree
public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle164
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle165
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeGramComplexConjugate
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem good_origin_root_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b₀ : T.Comp) (lam : Top.Wt (CMType H) (Dw.p + Dw.q)) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = (T.M B b₀).coef lam 0 j) → Top.RegDominant lam → ∃ (q₀ : ℕ) (n₀ : Option (RootIx Dw) → ℤ) (ε : (T.M B b₀).Ω) (u : MRing (T.M B b₀).ι) (C s₀ : ℝ), 0 < q₀ ∧ (∀ j, (n₀ j : ℝ) = q₀ * (T.M B b₀).coef T.nu (-1) j) ∧ ε ≠ 0 ∧ ε ∈ chartLatNm (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a 1 ∧ Small.IsFormOff (mCoordIdeal (T.M B b₀).y) u ∧ 0 ≤ C ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal (T.M B b₀).y), MvPolynomial.aeval z u ≠ 0 → ∀ x : ℂ, Small.HasVal (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + (T.M B b₀).weight (Top.scale s) (lam - s • T.nu) s z ≤ C * s + Real.log (∏ r, ((o.toTowerOrigin.Or B b₀).sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H Dw l Xo c _ Y T o B b₀ lam n' hn' _
  exact root_origin_weight_free E H Dw l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y (o.toTowerOrigin.S B) (T.M B b₀)
    (o.toTowerOrigin.Sys b₀) (o.toTowerOrigin.Fx b₀) (o.toTowerOrigin.Or B b₀) lam T.nu n'
    (o.toTowerOrigin.nu_eq b₀) hn'

end GlobalTheory.CompanionTheory.Ar.Small
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_block_refinement_lines : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ i, (Λ i).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ CoordTie ℤ ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ i, ∃ (a : K' → ℤ) (e₀ : Ω), (Λ i).IsDegOn Set.univ y' a e₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_addBlocks_isDegOn | exact GlobalTheory.CompanionTheory.Ar.exists_addBlocks_isDegOn | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_addBlocks_isDegOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.tate_iso_pullback_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (k : Type) [Field k] (x' : Sp k ⟶ X') (x : Sp k ⟶ X), x = x' ≫ f → (∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t' x', I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left) ∧ ∀ I' : TateIsoAt D t' x', ∃ I : TateIsoAt D t x, I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | exact GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem isFullLevelAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X'), ξ' ≫ f = spMap i ≫ ξ → ∀ (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → ∃ ev' : D.La → (Over.mk ξ' ⟶ t'.G), IsFullLevelAt D t' ξ' N (Units.map i.toMonoidHom z) ev' ∧ ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := by
  intro E _ _ _ H D X X' t t' f m Ω Ω' _ _ i ξ ξ' hξ N z ev hfull
  have hpb : IsPullback m.φ t'.G.hom t.G.hom f := m.cart.1
  have hsq : ∀ a, (spMap i ≫ (ev a).left) ≫ t.G.hom = ξ' ≫ f := by
    intro a
    rw [Category.assoc, Over.w (ev a)]
    exact hξ.symm
  let ev' : D.La → (Over.mk ξ' ⟶ t'.G) := fun a =>
    Over.homMk (hpb.lift (spMap i ≫ (ev a).left) ξ' (hsq a)) (hpb.lift_snd _ _ _)
  have hfst : ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := fun a => hpb.lift_fst _ _ _
  have hsnd : ∀ a, (ev' a).left ≫ t'.G.hom = ξ' := fun a => hpb.lift_snd _ _ _
  refine ⟨ev', ?_, hfst⟩
  unfold IsFullLevelAt
  intro k _ _ j
  obtain ⟨I, hIζ, hIev⟩ := hfull k (j.comp i)
  have hx : spMap (j.comp i) ≫ ξ = (spMap j ≫ ξ') ≫ f := by
    rw [spMap_comp, Category.assoc, Category.assoc, hξ]
  obtain ⟨I', hζ, hev⟩ := (tateIsoAt_move E H D X X' t t' f m k (spMap j ≫ ξ') (spMap (j.comp i) ≫ ξ) hx).1 I
  refine ⟨I', ?_, ?_⟩
  · rw [hζ, hIζ]
    simp
  · intro a
    apply hpb.hom_ext
    · rw [hev N a, hIev a, Category.assoc, hfst a, spMap_comp, Category.assoc]
    · rw [Over.w (I'.ev N a), Category.assoc, hsnd a]
      rfl

end GlobalTheory.CompanionTheory.Ar.XR
end

section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_herm_root_line_degree : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_rootFlat_of_realis <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.join_coords_unit_values : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : Top.RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Top.Wt Ψ N) (s lo hi : ℝ) (f : MRing (Cmp.joinIdx M.ι R.ι)), f ∉ mCoordIdeal (Ht.joinOf M R i) → (∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j)) → (∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∀ val : Option (Ψ × Fin N) → ℂ, (∀ j, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j) w (val j)) → ∑ j, M.coef lam s j * (Real.log ((M.line t j).h (fun p => w (Cmp.joinInl M.ι R.ι p))) - Real.log ((R.line 1 j).h (fun p => w (Cmp.joinInr M.ι R.ι p))) - Real.log ‖val j‖) ∈ Set.Icc lo hi) → Ht.ArchBetween M R i u t lam s lo hi := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form | exact GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.Ext.archBetween_of_off_form <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.height_of_zero_dim_variety : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (w : (Σ k, ι k) → L), W = mCoordIdeal w ∧ w ∈ ptsOver L W ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι W 1 ![A] / (degC W : ℝ) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.height_eq_intersection_number | exact GlobalTheory.CompanionTheory.Ar.Ht.height_eq_intersection_number | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.height_eq_intersection_number <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.join_model_points_lift : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (Q : (L : Type) → [Field L] → ((Σ k, R.ι k) → L) → Prop), (∀ f : MRing R.ι, (∃ a, IsMultiHomog f a) → f ∉ R.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L R.P, aeval w f ≠ 0 ∧ Q L w) → ∀ f : MRing M.ι, (∃ a, IsMultiHomog f a) → f ∉ M.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (w : (Σ k, R.ι k) → L), ∃ z ∈ ptsOver L' (mCoordIdeal (joinOf M R i)), w ∈ ptsOver L R.P ∧ Q L w ∧ (fun p => z (joinInr M.ι R.ι p)) = (fun p => e (w p)) ∧ aeval (fun p => z (joinInl M.ι R.ι p)) f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense | exact GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.line_height_bounded_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.number_field_point_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L P, IsArithVar (mCoordIdeal w) 1 ∧ P ≤ mCoordIdeal w ∧ (∀ f : MRing ι, (∃ a, IsMultiHomog f a) → (f ∈ mCoordIdeal w ↔ aeval w f = 0)) ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι (mCoordIdeal w) 1 ![A] / (degC (mCoordIdeal w) : ℝ) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height | exact GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.root_height_difference_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N), Close M R i u c → ArchBetween M R i u t lam s lo hi → ∀ (L : Type) [Field L] [NumberField L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈ Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | exact GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  exact @PositivityTheory.Xgn.hodge_gram_complex_conjugate_alt

end GlobalTheory.CompanionTheory.Ar.Flat
end
