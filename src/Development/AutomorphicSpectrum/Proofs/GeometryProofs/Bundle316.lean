module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightCount
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle314
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle312
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle274
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle144
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle166
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle107
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle315
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.root_model_flag_height : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S R.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → R.Ω), 1 ≤ D.p + D.q → Fl.RootLines R.xdeg e → Ht.FibreInput R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput | exact GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput | (intros; apply GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.eigen_frame_function_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | exact GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.uniform_norm_height_count : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count | exact GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count | (intros; apply GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_regularisations_tied : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S : LogLogRegularisationSetting M Dc.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ z, 0 ≤ U z) ∧ (∀ z ∈ Dc.Xo, ∀ t : K → ℂ, (∀ k, t k ≠ 0) → U (torusSmul t z) = U z) ∧ S.IsTied ∧ S'.IsTied ∧ ConjU S' := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  obtain ⟨U, hU, h0, hT, hC, -⟩ := GlobalTheory.T.intersection_system_weight_left hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨hp1, -, hp2, hc2⟩ := GlobalTheory.T.cusp_intersection_positive hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨hb, -⟩ := GlobalTheory.T.cusp_chart_log_growth_bounds hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨-, -, hL, hO⟩ := GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties K J II (CMType H) Ω W Dc Hd
  obtain ⟨M⟩ := GlobalTheory.CompanionTheory.Relay.exists_compactified_model K J II (CMType H) Ω W Dc
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_regularization_of_hodge_metric K J II (CMType H) Ω W Dc Hd M hp1
  obtain ⟨S', hS', hJ⟩ := GlobalTheory.T.exists_regularization_setting K J II (CMType H) Ω W Dc Hd M (corrW Hd U)
    (fun z hz a ha => by
      have := hL z hz a ha
      simp only [corrW, hT z a ha, this]
      ring)
    hp2 hc2 hb
    (fun z hz => by
      have := hO z hz
      simp only [corrW, hC z, this])
  exact ⟨U, M, S, S', hU, h0, fun z _ t ht => hT z t ht, hS, hS', hJ⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.cusp_intersection_finite : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ), Or.𝔐.IsCuspWeight Or.sm U → CoordsAt Or.𝔐.ξ Dc.y z w → Or.PhiWeight z w x → x ≤ S'.B.ph (M.proj w) + Real.log (S'.ref.h w) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_intersection_finite | exact GlobalTheory.CompanionTheory.Relay.cusp_intersection_finite | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_intersection_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.slope_bound_of_line_large_degree : LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel | exact GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.intersection_degree_lower : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → S'.IsTied → PosU S' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.intersection_degree_lower | exact GlobalTheory.CompanionTheory.Relay.intersection_degree_lower | (intros; apply GlobalTheory.CompanionTheory.Relay.intersection_degree_lower <;> assumption)
end
