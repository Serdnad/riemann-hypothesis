module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle295
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle304
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle156
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle179
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle229
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle257
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle164
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle199
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositive
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightEstimate
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle310
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle191
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle271
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle264
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle244
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieMetricHeight
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle077
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.toroidal_flag_smooth_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (T : GlobalTheory.CompHS.TorFlag Xo c), ∃ d : ℕ, SmoothOfRelativeDimension d (GlobalTheory.CompHS.flagStr T.X) ∧ IsProjOver (GlobalTheory.CompHS.flagStr T.X) := by
  intro E _ _ _ H D l Xo c T
  obtain ⟨p⟩ := GlobalTheory.FlagMod.LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := GlobalTheory.CompanionTheory.FlagSmooth.nonempty_atlas_of_cover T.Y p
    (GlobalTheory.CompanionTheory.FlagSmooth.exists_gChart_of_flagCover T.X)
  obtain ⟨M, g, κ, hκ, hZ⟩ := GlobalTheory.CompanionTheory.FlagSmooth.exists_cellModel T.Y p A
  obtain ⟨d, hsm, hpr⟩ := GlobalTheory.T.flag_atlas_projective_embedding E H D l Xo c T.Y p A M.YY M.π g κ hκ hZ T.smooth
  obtain ⟨h, hh, hπ⟩ := GlobalTheory.T.exists_flagModel_isIso_of_open_cells E H D l Xo c T.Y p A M g κ hκ hZ T.smooth T.flag
  have e : flagStr T.X = h ≫ M.π ≫ T.Y.s := by
    rw [← Category.assoc, hπ]
  refine ⟨d, ?_, ?_⟩
  · rw [e]; exact GlobalTheory.VarFlag.smooth_iso h _ hsm
  · rw [e]
    obtain ⟨N, i, hi, hs⟩ := hpr
    exact ⟨N, h ≫ i, inferInstance, by rw [Category.assoc, hs]⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.pair_lattice_degree_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (Wb : ChartBundle ℤ (segreCoord y) N ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → SncChart (mCoordIdeal y) n Bd), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB N ⊤ → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsChartOf (segreCoord y) Wb.lat → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → ∃ hm : HermMetric y Wb (mcPts (mCoordIdeal y) \ Bd) χ, ∀ e (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → 𝔐.Interior z → InFrameDomain y (hm.chart e) (hm.fr e) w → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((hm.b e k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (hm.gram e w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_hermMetric_hodge | exact GlobalTheory.CompanionTheory.Ar.exists_hermMetric_hodge | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_hermMetric_hodge <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeUnif

theorem isGrpPullback_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · haveI : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · have e₁ : (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      first | exact Hom.mul_comp _ _ _ | exact MonObj.mul_comp _ _ _ | exact CategoryTheory.Hom.mul_comp _ _ _
    have : (x * y).left ≫ e.hom.left = ((x ≫ e.hom) * (y ≫ e.hom)).left := by
      rw [← e₁]; rfl
    rw [this]
    exact mul_left_congr (Category.comp_id _) _ _ _ _ hx hy

theorem exists_compare {S S₁ : Scheme.{0}} {f : S₁ ⟶ S} {A A' : Over S₁} {C : Over S} [GrpObj A] [GrpObj A'] [GrpObj C]
    {a : A.left ⟶ C.left} {a' : A'.left ⟶ C.left} (hA : IsGrpPullback A C f a) (hA' : IsGrpPullback A' C f a') :
    ∃ w : A.left ⟶ A'.left, w ≫ a' = a ∧ w ≫ A'.hom = A.hom ∧ IsGrpPullback A A' (𝟙 S₁) w := by
  refine ⟨hA'.1.lift a A.hom hA.1.w, hA'.1.lift_fst _ _ _, hA'.1.lift_snd _ _ _, ?_⟩
  refine IsGrpPullback.cancel hA' ?_ ?_
  · rw [hA'.1.lift_fst, Category.id_comp]; exact hA
  · rw [hA'.1.lift_snd, Category.comp_id]

theorem slope_unif : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (z₀ : Sp (𝓞 L₀) ⟶ 𝔐.X), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L), ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G (spMap (RingOfIntegers.mapRingHom e) ≫ z₀) B.carrier), IsFibre (fun z v w c => c = h.ip z v w) _ B MB → B.slopeMax ≤ ((C * Real.log (2 + C + max (-B.normDegree ⊤) 0) + C : ℝ) : EReal) := by
  intro hN hP hR hH hS E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 h hpq
  obtain ⟨K₀, hK₀, hQ⟩ := GlobalTheory.T.lie_metric_height_bound hR E H D l Xo c Y S Ω K J y 𝔐 h hpq
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨C₁, hC₁, hT⟩ := GlobalTheory.T.semiabelian_lie_metric_height hH 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.t.semi 𝔐.Li 𝔐.M h
  obtain ⟨C₀, hC₀, hSl⟩ := hS
  obtain ⟨Cc, hCc1, hCcK, hCc₁, hCc₀⟩ : ∃ Cc : ℝ, 1 ≤ Cc ∧ K₀ ≤ Cc ∧ C₁ ≤ Cc ∧ C₀ ≤ Cc :=
    ⟨max (max K₀ C₁) (max C₀ 1), by simp, by simp, by simp, by simp⟩
  obtain ⟨C', hC', hPB⟩ := GlobalTheory.T.hermitian_bundle_quotient_degree_bound (Module.finrank Ω 𝔐.Li) Cc hCc1
  refine ⟨C', hC', fun L₀ _ _ z₀ => ?_⟩
  obtain ⟨L₁, _, _, e₁, ⟨P₁⟩⟩ := GlobalTheory.T.exists_abelian_part_extension E H 𝔐.X 𝔐.t L₀ (spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀)
  obtain ⟨σ₁⟩ : Nonempty (L₁ →+* ℂ) := inferInstance
  obtain ⟨P₁c, _, mBc, _, _⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ ℂ _ P₁ σ₁
  have hpr : IsPrincipal P₁.tB := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ ℂ σ₁ P₁.tB P₁c.tB mBc).1 (hQ _ P₁c).1
  obtain ⟨L, _, _, e₂, t', tK, ⟨m'⟩, ⟨mP⟩⟩ := GlobalTheory.T.lie_signature_number_field hN hP E H L₁ P₁.tB hpr
    (GlobalTheory.T.abelian_part_lie_signature E H D l Xo c Y S Ω K J y 𝔐 L₁ _ P₁)
  have hprK : IsPrincipal tK := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ L e₂ P₁.tB tK mP).2 hpr
  refine ⟨L, inferInstance, inferInstance, e₂.comp e₁, fun B MB hB => ?_⟩
  have hz : spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀) =
      spMap e₂ ≫ (spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀) := by
    have e : spMap (algebraMap (𝓞 L) L) ≫ spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) =
        spMap e₂ ≫ spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [← Category.assoc, e]
    simp only [Category.assoc]
  obtain ⟨B', MB', hB'⟩ := GlobalTheory.T.principal_hermitian_fibre E H L t' tK m' hprK
  have hslope := hSl E H L t' tK m' hprK B' MB' hB'
  obtain ⟨P₂, mK2, mB2, c1, c2⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ L _ P₁ e₂
  obtain ⟨w, hw, hw', hwp⟩ := exists_compare mB2.cart mP.cart
  letI := P₂.τ.addCommGroup
  letI := P₂.τ.grpB
  haveI := P₂.e_hom
  have hφ' : IsGrpPullback P₂.τ.B t'.G (spMap (algebraMap (𝓞 L) L)) (P₂.e.hom.left ≫ w ≫ m'.φ) := by
    have := (isGrpPullback_iso P₂.e).comp (hwp.comp m'.cart)
    simpa using this
  obtain ⟨MT, hMT⟩ := GlobalTheory.T.exists_cocharacter_lie_model (Sp L) P₂.τ.X L (𝟙 _)
  have hcart : IsGrpPullback P₂.tK.G 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀)) P₂.m.φ := by
    rw [hz]; exact P₂.m.cart
  obtain ⟨r, bs, hbs⟩ := hT L _ P₂.tK.G P₂.m.φ P₂.τ hcart
  obtain ⟨ε, f, hε, hf, hli, hker, hsur⟩ := GlobalTheory.T.semi_abelian_pullback_torus_extension 𝔐.X 𝔐.t.G 𝔐.t.semi L _ P₂.tK.G P₂.m.φ P₂.τ t'.G _ t'.semi hcart hφ'
    MT hMT B.carrier B'.carrier MB MB' r bs
  have hbd := hbs MT hMT B MB hB ε hε
  have hnb := GlobalTheory.T.abelian_part_maps_compatible_right E H 𝔐.X 𝔐.t L₁ L e₂ _ _ hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω 𝔐.ξ 𝔐.Li 𝔐.M K J y h K₀
    (fun zc P v v₀ c => (hQ zc P).2 v v₀ c) B B' MB MB' hB hB' f hf
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hrk := GlobalTheory.T.lie_model_rank_eq_generic 𝔐.X Ω 𝔐.ξ 𝔐.all 𝔐.t.G 𝔐.Li 𝔐.M L _ B.carrier MB
  have hC₁0 : (0 : ℝ) < C₁ := by linarith
  have hCc0 : (0 : ℝ) < Cc := by linarith
  refine hPB L B B' r ε f hrk hli hker hsur ?_ ?_ ?_
  · intro σ u
    have hs : 0 ≤ ∑ a, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    obtain ⟨h₁, h₂⟩ := hbd σ u
    refine ⟨le_trans (mul_le_mul_of_nonneg_right ?_ hs) h₁, h₂.trans (mul_le_mul_of_nonneg_right hCc₁ hs)⟩
    exact inv_anti₀ hC₁0 hCc₁
  · intro σ x
    have h0 : 0 ≤ sqAt B σ x := by
      have := (B.metric.form σ).re_inner_nonneg x
      simpa [sqAt] using this
    exact (hnb σ x).trans (mul_le_mul_of_nonneg_right hCcK h0)
  · refine hslope.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_right hCc₀ (Real.log_nonneg ?_)))
    have : (0 : ℝ) ≤ max (-B'.normDegree ⊤) 0 := le_max_right _ _
    have h' : (0 : ℝ) ≤ Module.finrank (𝓞 L) B'.carrier := Nat.cast_nonneg _
    linarith

end GlobalTheory.CompanionTheory.Ar.SlopeUnif
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.cusp_intersection_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → ChartPsh Dc (phMu Hd) ∧ ChartCont Dc (phMu Hd) ∧ ChartPsh Dc (corrW Hd U) ∧ ChartCont Dc (corrW Hd U) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive | exact GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.growthOn_le_vol_mul_flagDeg : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) ≤ ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.growth_le_vol_deg | exact GlobalTheory.CompanionTheory.Ar.Plug.growth_le_vol_deg | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.growth_le_vol_deg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  exact @GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay
end
