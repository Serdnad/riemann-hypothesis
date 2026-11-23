module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusStableSncCharts
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralModelFacts
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFree
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle190
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle188
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle189
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle186
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.exists_torus_stable_snc_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y n bd → IsArithVar (mCoordIdeal y) (n + 1) → (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) → ∃ (nc : ℕ) (χ : Fin nc → SncChart (mCoordIdeal y) n (mcPts (mCoordIdeal y) ∩ mcPts bd)), ∀ z ∈ mcPts (mCoordIdeal y), ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((χ a).γ t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncCpt.exists_sncCharts | exact GlobalTheory.CompanionTheory.Ar.SncCpt.exists_sncCharts | (intros; apply GlobalTheory.CompanionTheory.Ar.SncCpt.exists_sncCharts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem model_cpt_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q :=
  PositivityTheory.Xgn.integral_model_facts

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

theorem _root_.GlobalTheory.T.boundary_chart_lie_model_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.boundary_disc_map_embedding_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X' : Scheme.{0}) (jx : X' ⟶ Y.X) (t : SAB H X') (m : SABMap t Y.t jx) (τ : c.F →+* ℂ) (n a : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X')), a ≤ n → IsHolTo (Metric.ball 0 1) p → (∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F))) → (∀ u ∈ Flat.punct n a 1, ∀ x : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)), x ≫ pullback.fst _ _ = p u ≫ jx → Set.range x ⊆ Set.range Y.jQ) → ∃ (ρ : ℝ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (h : Sp C.R ⟶ X'), 0 < ρ ∧ ρ ≤ 1 ∧ Nonempty (SABMap C.t t h) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ h = p ((ρ : ℂ) • z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ModelChart.exists_bdryChart_of_model | exact GlobalTheory.CompanionTheory.Ar.ModelChart.exists_bdryChart_of_model | (intros; apply GlobalTheory.CompanionTheory.Ar.ModelChart.exists_bdryChart_of_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameVec

open GlobalTheory.CompanionTheory.Ar.LieSigma

theorem one_left_over {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem isVec_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ v, IsTangent v → ∃! w, a.u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ a.u.IsDiff w v) → ∀ x : D.B.carrier, ∃! c, D.IsVec a x c := by
  intro E _ _ _ H L _ _ D σ a h1 h2 x
  have hw : (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) ≫ D.t.G.hom
      = (epsAt (emb σ)).hom := by
    rw [Category.assoc, Over.w]
    simp only [epsAt, Over.mk_hom, Category.comp_id, emb]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext t <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let v : epsAt (emb σ) ⟶ D.t.G := Over.homMk _ hw
  have hvl : v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left := rfl
  have hlift : (v.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := by
    show v.left ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact hvl
  have hsq : v.left ≫ D.t.G.hom = (epsR ℂ).hom ≫ emb σ := hw
  let v' : epsR ℂ ⟶ a.A := Over.homMk (a.cart.1.lift v.left (epsR ℂ).hom hsq) (a.cart.1.lift_snd _ _ _)
  have hφ : v'.left ≫ a.φ = v.left := a.cart.1.lift_fst _ _ _
  have ht : IsTangent v' := by
    unfold IsTangent
    apply a.cart.1.hom_ext
    · have h3 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ (1 : Over.mk (𝟙 (Sp (𝓞 L))) ⟶ D.t.G).left := by
        rw [hvl, ← Category.assoc]
        have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) =
            spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ spMap (TrivSqZeroExt.fstHom (𝓞 L) (𝓞 L) (𝓞 L)).toRingHom := by
          simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 1
          ext t <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
        rw [key, Category.assoc]
        exact congrArg (fun f => spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ f) (D.MB.tan x)
      rw [Category.assoc, hφ, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left a.cart, h3, one_left_over]
      simp
    · have e : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (epsR ℂ).hom = 𝟙 _ := by
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
          ext t <;> simp
        rw [this]
        exact Spec.map_id _
      rw [Category.assoc, Over.w v', e]
      simpa using (Over.w η[a.A]).symm
  obtain ⟨c, hc, hu⟩ := h1 v' ht
  refine ⟨c, ⟨v, hlift, v', hφ, hc⟩, ?_⟩
  rintro c' ⟨v₁, hl₁, v₁', hφ₁, hc₁⟩
  have e₁ : v₁.left = v.left := by
    have : v₁.left ≫ 𝟙 _ = _ := hl₁
    rw [Category.comp_id] at this
    exact this
  have e₂ : v₁' = v' := by
    apply Over.OverMorphism.ext
    apply a.cart.1.hom_ext
    · rw [hφ₁, hφ, e₁]
    · rw [Over.w v₁', Over.w v']
  exact hu c' (e₂ ▸ hc₁)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameVec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.model_fibres_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), Dense (Set.range Y.j) → Y.SplitFibres → Y.N3 → ∀ (p : ℕ), p.Prime → ∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ModelFib.model_fibPF | exact GlobalTheory.CompanionTheory.Ar.ModelFib.model_fibPF | (intros; apply GlobalTheory.CompanionTheory.Ar.ModelFib.model_fibPF <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

theorem _root_.GlobalTheory.T.fibre_lattice_base_change_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (z : Sp ℂ ⟶ X'), (Nonempty (SABMap t' t f) → (FibreLat t' z R ↔ FibreLat t (z ≫ f) R)) ∧ ((∀ x, R'.P x = star (R.P x)) → R'.Hm = R.Hm.map (starRingEnd ℂ) → (∀ a x, R'.B a x = star (R.B a (star x))) → FibreLat t' z R → FibreLat t' (spMap (starRingEnd ℂ) ≫ z) R') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.projective_model_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ProjModel.isProjOver_comp_model | exact GlobalTheory.CompanionTheory.Ar.ProjModel.isProjOver_comp_model | (intros; apply GlobalTheory.CompanionTheory.Ar.ProjModel.isProjOver_comp_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_inner_product_map_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (X' : Scheme.{0}) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (z : Spec (CommRingCat.of ℂ) ⟶ X') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v.left = v'.left ≫ m.φ → w.left = w'.left ≫ m.φ → (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff | exact GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_tripleMap_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgePullBack

theorem hodgeInnerProduct_iff_of_abelianSchemeMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0})
    (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (z : Sp ℂ ⟶ S') (v' w' : epsAt z ⟶ t'.G)
    (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v'.left ≫ m.φ = v.left → w'.left ≫ m.φ = w.left →
      (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) :=
  fun E _ _ _ H S S' t t' f m z v' w' v w c hv hw =>
    hodgeInnerProduct_tripleMap_iff E H S t S' t' f m z v' w' v w c hv.symm hw.symm

end GlobalTheory.CompanionTheory.Ar.HodgePullBack
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

theorem _root_.GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_eq_sum_fundamental <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c₁ c₂ : ∀ k, J k), mseg y c₁ ≠ 0 → mseg y c₂ ≠ 0 → ∀ (P₁ : ChartPack G O c₁) (P₂ : ChartPack G O c₂) (x : Fin (D.p + D.q) → 𝓞 E), ∃ n : ℕ, ∃ u ∈ P₂.Dh.om, (mseg y c₁ / mseg y c₂) ^ n • (P₁.Dh.h x - P₂.Dh.h x) = (p ^ 𝔐.R p) • u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartPack_lift_overlap | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartPack_lift_overlap | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.chartPack_lift_overlap <;> assumption)
end
