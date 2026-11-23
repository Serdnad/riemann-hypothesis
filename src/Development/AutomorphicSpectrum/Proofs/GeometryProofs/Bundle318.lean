module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle317
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesAnalytic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle314
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle222
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle142
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.tower_intersection_of_sandwich_split : Top.Given → Flat.FlatLineGenerator → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T) (II : IntersectionSystem), IsIntersectionSystem II → SplitComps Y → (∀ B a, ∀ p ∈ g.S B, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich (g.Or B a).𝔐 p κ) → T.I5 II ∧ T.I6 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopGood.tower_good_of_sandwich_split | exact GlobalTheory.CompanionTheory.Ar.TopGood.tower_good_of_sandwich_split | (intros; apply GlobalTheory.CompanionTheory.Ar.TopGood.tower_good_of_sandwich_split <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.final_theorem_of_inputs_left : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → Top.Given := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.given_of_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.given_of_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.given_of_inputs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.eigen_frames_analytic : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → Z.IsGeom → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → ∃ (f : Z.Ω) (κ : ℂ) (W : (Xo.XF c).Opens), κ ≠ 0 ∧ genPt Z.ξ₀ ∈ W ∧ IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (f • exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂) Z.genFib ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ y ⁻¹ᵁ W → Set.range y ⊆ U → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) f (κ * Φ y v w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_unitAn | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_unitAn | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_unitAn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopBase

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem base_setting_of_good_origin : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  intro Ch Cu hNine hWeil hAgr hProp hCmp hGiven hPts E _ _ _ _ H D Xo l c Y _ T o II hGlob hExtra hFull hp hq hqp
    hbad B hB a
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have := hne
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr hne
  have hN2 : 2 ≤ D.p + D.q := by omega
  have hsq : 4 ≤ (D.p + D.q) ^ 2 := by nlinarith
  have hB16 : 16 * Fintype.card (CMType H) ≤ B := by nlinarith
  have hB2 : 2 ≤ B := by omega
  have hB4 : 4 * Fintype.card (CMType H) + 2 ≤ B := by omega
  have hgen : genPt (o.Or B a).𝔐.ξ₀ = genPt (o.Fx a).ξf :=
    genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset ℕ, ∀ r, r ∈ S₁ ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad :=
    ⟨(Finset.range (B + 1)).filter (fun r => r.Prime ∧ r ∉ T.bad), by
      intro r
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h3⟩⟩
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp => ((o.bad_iff p).1 hp).1
  have hS₁P : ∀ p ∈ S₁, p.Prime := fun p hp => ((hS₁ p).1 hp).1
  have hdisj : Disjoint S₁ T.bad := Finset.disjoint_left.2 fun p hp hp' => ((hS₁ p).1 hp).2.2 hp'
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ T.bad := fun p hp hd =>
    (o.bad_iff p).2 ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  have horigin :=
    GlobalTheory.T.full_intersection_generic_bound hGiven hWeil E H D Xo l c Y II hFull hGlob hp hq _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ T.bad S₁
      false hbadP hS₁P hdisj hdisc
  obtain ⟨K, _, J, _, Ω, _, _, W, _, _, Dc, Hd, Or, hgen', hS, hj, hbg, -, hHT⟩ := horigin
  simp only [Bool.false_eq_true, ite_false] at hj hbg
  have hsm : Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨h, -, -⟩
    · exact h
    · exact absurd (congrFun (hbg.symm.trans h) hne.some) Sum.inl_ne_inr
  have hGood : Or.Good :=
    ⟨fun p hp => hHT p (Finset.mem_union_left _ hp),
      fun p hp => hHT p (Finset.mem_union_right _ (by rw [← hS]; exact hp))⟩
  have hSc : ∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad := by
    intro r; rw [hS]; exact hS₁ r
  have hN : Dc.N = D.p + D.q := Or.N_eq
  have hAdm : admitted Xo l c Y Or B := by
    refine ⟨hGlob, hGood, o.bad_iff, ?_, ?_, hSc, ?_⟩
    · show T.bad.card ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2
      rw [hN]; exact hbad
    · exact hB4
    · show Dc.N - Dc.j ≤ Dc.j
      rw [hN, hj]; omega
  obtain ⟨U, M, S, S', hcw, hU0, hUt, hSt, hS't, hconj⟩ :=
    GlobalTheory.T.cusp_weight_regularisations_tied hGiven E H D Xo l c Y II K J Ω W Dc Hd T.bad Or
  obtain ⟨hpos, hht, hmean⟩ := hNine E H D Xo l c Y II K J Ω W Dc Hd T.bad Or B U M S' hFull hAdm hcw hS't
  obtain ⟨X, hXH, hXU, hXrd, hXL, hX1, hX2, hX3, hX4, hX5⟩ :=
    GlobalTheory.T.corrected_weight_regularization K J II (CMType H) Ω W Dc Hd M U S S' (hostRd E) (hostLval H) Ch Cu hSt hS't hU0 hUt hpos hconj
      hht hmean
  subst hXH
  obtain ⟨hdeg, hlim, hPP⟩ := GlobalTheory.T.good_origin_intersection_tower hAgr hProp hCmp hGiven hPts E H D Xo l c Y T o II hGlob hExtra hFull hp hq
    B B a K J Ω W Dc ℤ (Fin 2 → ℤ) X Or hB2 le_rfl hqp hbg hsm hGood (hgen'.trans hgen) hSc
  obtain ⟨-, -, hSemi, -, hResK, -, -, hGaga, -, hInputs, -, hAn, -, -⟩ := hGiven
  have hStk : Top.StokesAt X B :=
    GlobalTheory.T.intersection_final_estimate hInputs hAn hResK hGaga hSemi E H D Xo l c Y II K J Ω W Dc X.H T.bad Or B U hFull hAdm hcw ℤ
      (Fin 2 → ℤ) X rfl hXU hX1 B hB4 hlim
  exact ⟨K, inferInstance, J, inferInstance, Ω, inferInstance, inferInstance, W, inferInstance, inferInstance, Dc, ℤ,
    Fin 2 → ℤ, inferInstance, inferInstance, inferInstance, X, hN, hj.trans o.j_eq.symm, hXrd, hXL, hX1, hX2, hX3, hX4,
    hX5, hdeg, hlim, hStk, hPP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopBase
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.root_origin_frame_combined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined | exact GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined | (intros; apply GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.uniform_norm_degree_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → (∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal (GlobalTheory.CompHt.topDeg U Z u) ∧ GlobalTheory.CompHt.topDeg U Z u = T.vol (κ Z) * Top.flagDeg (reW u) ∧ 0 < GlobalTheory.CompHt.topDeg U Z u) ∧ (∀ Z, 0 < GlobalTheory.CompHt.vZero U Z) ∧ (T.VolEq → ∀ Z Z', GlobalTheory.CompHt.vZero U Z = GlobalTheory.CompHt.vZero U Z') ∧ ∀ (Z : Comp Xo c) (a : WZ E), Top.RegDominant (towerWt Dw a) → volL U h a Z (Top.dimFl (CMType H) (Dw.p + Dw.q)) = T.vol (κ Z) * Top.flagDeg (towerWt Dw a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.topGrowth | exact GlobalTheory.CompanionTheory.Ar.Plug.topGrowth | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.topGrowth <;> assumption)
end
