module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsoIntegralModelsMatchingLieBases
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle040
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle023
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle029
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SurjectiveAppTopIntegralModelSquare
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle019
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle018

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem nuAlg_le_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (t t' : SAB H (Sp T.V)) (n : SABMap t t' (𝟙 (Sp T.V)))
    (hsurj : Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom) (d d' : ℕ)
    (B : FB T.V d (𝓞 E)) (B' : FB T.V d' (𝓞 E))
    (tg : Fin d → (Sp (DualNumber T.V) ⟶ t.G.left)) (tg' : Fin d' → (Sp (DualNumber T.V) ⟶ t'.G.left))
    (uv : Fin d → Fin d → T.V) (uv' : Fin d' → Fin d' → T.V)
    (x : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp T.V)) d' m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp T.V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp T.V)) d' x' m)
    (hc : IsChartG t (𝟙 (Sp T.V)) d B.G.F B.A.act tg uv x)
    (hc' : IsChartG t' (𝟙 (Sp T.V)) d' B'.G.F B'.A.act tg' uv' x')
    (hu : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x) (hu' : GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d') x')
    (hf : IsFrameG t (𝟙 (Sp T.V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t' (𝟙 (Sp T.V)) d' x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    (h : PS T.Fr 2 d) (h' : PS T.Fr 2 d') (hg : B.IsCanonGauge T.Fr h) (hg' : B'.IsCanonGauge T.Fr h')
    (uT : Lt1 Dw → Fin d → T.V) (uT' : Lt1 Dw → Fin d' → T.V)
    (v : Lt1 Dw → (Sp (DualNumber T.V) ⟶ t.G.left))
    (hv : ∀ ℓ, IsCombAtG t (𝟙 (Sp T.V)) (dirs x) (uT ℓ) (v ℓ))
    (hv' : ∀ ℓ, IsCombAtG t' (𝟙 (Sp T.V)) (dirs x') (uT' ℓ) (v ℓ ≫ n.φ))
    (u : Lt1 Dw → Fin d → T.Fr) (u' : Lt1 Dw → Fin d' → T.Fr)
    (huT : ∀ ℓ i, u ℓ i = algebraMap T.V T.Fr (uT ℓ i)) (huT' : ∀ ℓ i, u' ℓ i = algebraMap T.V T.Fr (uT' ℓ i))
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr B' a).mulVec (u' ℓ) = io (embK c ℓ.1 a) • u' ℓ)
    (ε k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (N : ℕ) :
    nuAlg Dw T B h u ε k a N ≤ nuAlg Dw T B' h' u' ε k a N := by
  obtain ⟨x'', -, hx''u, -, -⟩ := GlobalTheory.T.pushChartAlt E H T.V t t' n d x
  have hd : d = d' := GlobalTheory.T.universalJetCoordinates_dim_unique T.V t'.G d d' x'' x' (hx''u hu) hu'
  subst hd
  obtain ⟨φ, φi, hrel, hlin⟩ := GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id E H hs T.V t t' n hsurj d B B' (Fin d) (Fin d) tg tg' uv uv' x x' e e'
    hc hc' hu hu' hf hf'
  refine GlobalTheory.T.biextension_depth_le_of_related E H Dw l Xo c hs T io d B B' φ φi h h' u u' hrel hg hg' heig ?_ ε k a N
  intro ℓ
  have hu1 : u ℓ = fun i => algebraMap T.V T.Fr (uT ℓ i) := funext (huT ℓ)
  have hu2 : u' ℓ = fun j => algebraMap T.V T.Fr (uT' ℓ j) := funext (huT' ℓ)
  rw [hu1, hu2, hlin (uT ℓ) (uT' ℓ) (v ℓ) (hv ℓ) (hv' ℓ)]
  funext i
  exact RingHom.map_mulVec (algebraMap T.V T.Fr) (dLin φ) (uT' ℓ) i

theorem nuLocC_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing
    (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C C' : IntegralChartA3 Xo c T io y) (e k : ℕ)
      (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C e k a n ≤ nuLocC C' e k a n := by
  letI := H.starRing
  intro hs T io y C C' e k a n
  letI := io.toAlgebra
  obtain ⟨BT, hF, hA, hP1, hP2, hSy, hAd, hK⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨BT', hF', hA', hP1', hP2', hSy', hAd', hK'⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C'
  obtain ⟨hFK, hActK, hG, hGc⟩ := hK T.Fr
  obtain ⟨hFK', hActK', hG', hGc'⟩ := hK' T.Fr
  rw [GlobalTheory.T.localChartDepth_eq_integralBiextDepth E H Dw l Xo c T io y C BT hFK hActK e k a n,
    GlobalTheory.T.localChartDepth_eq_integralBiextDepth E H Dw l Xo c T io y C' BT' hFK' hActK' e k a n]
  obtain ⟨nm, hnm⟩ := GlobalTheory.T.exists_iso_integralModels_matching_lieBases E H Dw l Xo c T io _ C.I C'.I
  have hsurj := GlobalTheory.T.surjective_appTop_integralModel_square E H Dw l Xo c T io _ C'.I
  have hU := GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y
  have e1 : MvPowerSeries.map (algebraMap T.Fr T.Fr) C.ch.h = C.ch.h := by
    ext
    simp
  have e2 : MvPowerSeries.map (algebraMap T.Fr T.Fr) C'.ch.h = C'.ch.h := by
    ext
    simp
  rw [e1] at hGc
  rw [e2] at hGc'
  have gen := C.gen
  have gen' := C'.gen
  unfold IsGenFibreChart at gen gen'
  refine nuAlg_le_of_charts Xo c hs T io C.I.G C'.I.G nm hsurj (chD C.ch) (chD C'.ch) BT BT' C.tgT C'.tgT
    (fun j => Pi.single j 1) (fun j => Pi.single j 1) C.xT C'.xT C.eT C'.eT ?_ ?_ (hU C) (hU C') ?_ ?_
    C.ch.h C'.ch.h ((hG _).2 hGc) ((hG' _).2 hGc') C.uvecT C'.uvecT (fun ℓ => (C.I.ub ℓ.1 ℓ.2).left)
    (fun ℓ => C.dirT ℓ) ?_ C.ch.uvec C'.ch.uvec gen.1.2.2.2.2.2.2 gen'.1.2.2.2.2.2.2 ?_ e k a n
  · rw [hF, hA]
    exact C.chartT
  · rw [hF', hA']
    exact C'.chartT
  · rw [hF, hA, hP1, hP2, hSy, hAd]
    exact C.frameT
  · rw [hF', hA', hP1', hP2', hSy', hAd']
    exact C'.frameT
  · intro ℓ
    rw [hnm]
    exact C'.dirT ℓ
  · intro b ℓ
    have h2 : dAct T.Fr BT' b = dAct T.Fr C'.ch.B b := by
      funext i j
      simp only [dAct, hActK' b]
    rw [h2]
    exact GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y C' b ℓ

theorem chartIndep_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ChartIndep Xo c := by
  intro E _ _ _ H Dw l Xo c inst hs
  have hst : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hs
  subst hst
  intro T io y C C' e k a n
  exact le_antisymm (nuLocC_le Xo c hs T io y C C' e k a n) (nuLocC_le Xo c hs T io y C' C e k a n)

end GlobalTheory.ChartCmp
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteHeight

theorem id_pow_left_proj {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (N : ℕ) :
    (𝟙 G' ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left := by
  have h1 : (ObjPull.pushEquiv h G' (𝟙 G')).left = φ := Category.id_comp _
  have h2 : ObjPull.pushEquiv h G' (𝟙 G' ^ N) = ObjPull.pushEquiv h G' (𝟙 G') ≫ 𝟙 G ^ N := by
    rw [map_pow, MonObj.comp_pow, Category.comp_id]
  rw [← ObjPull.pushEquiv_left h, h2, Over.comp_left, h1]

theorem finite_torsion_pull {S S' Z : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (t : Z ⟶ S') (r : Z ⟶ S) (hr : t ≫ f = r) (N : ℕ)
    (hf : Finite {x : Over.mk r ⟶ G // x ^ N = 1}) :
    Finite {x : Over.mk t ⟶ G' // x ≫ (𝟙 G' ^ N) = 1} := by
  subst hr
  let e := ObjPull.pushEquiv h (Over.mk t)
  refine Finite.of_injective (β := {x : Over.mk (t ≫ f) ⟶ G // x ^ N = 1})
    (fun x => ⟨e x.1, ?_⟩) ?_
  · have hx : x.1 ^ N = 1 := by
      have := x.2
      rwa [MonObj.comp_pow, Category.comp_id] at this
    have : (e x.1) ^ N = 1 := by rw [← map_pow, hx, map_one]
    exact this
  · intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

theorem exists_pow_span_X_le_span_map_residue_mulF : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ N : ℕ, 1 ≤ N → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField T) 1 d)) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (mulF F.F N j)) := by
  intro T _ _ _ G _ _ D A U d F x hx N hN
  obtain ⟨x0, hu, hρ⟩ := GlobalTheory.T.isUniversalChart_of_formalGroupChart T G U.smooth d F x hx
  have hlaw := GlobalTheory.T.isFormalGroupLawOfChart_of_jetChart T G d F x hx x0 hu hρ
  have hmap := GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw T G d x0 hu F.F hlaw N
  have hp := isGrpPullback_pullback G (Spec.map (CommRingCat.ofHom (residue T)))
  obtain ⟨x', hu', -, hm, -⟩ := GlobalTheory.ChartBaseChange.chartBaseChange GlobalTheory.JetSer.jetAlg
    (GlobalTheory.JetSer.serSt_of_jetAlgSt GlobalTheory.JetSer.jetAlg) T (ResidueField T) (residue T) G _ _ hp d x0 hu
  have hm' := hm _ _ _ (id_pow_left_proj hp N) hmap
  have hsm := U.smooth
  have : LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp.1 inferInstance
  obtain ⟨M, hM⟩ := GlobalTheory.JetSer.exists_pow_le_span_sup_pow_succ (ResidueField T) _ _ (by
      rw [MonObj.comp_pow, Category.comp_id]
      have : η[(Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G] = 1 := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [this, one_pow]) (fun Ω _ _ t => by
      obtain ⟨b, rfl⟩ := Spec.map_surjective t
      refine finite_torsion_pull hp _ (Geo.Tor.spMap (b.hom.comp (residue T))) ?_ N
        (GlobalTheory.finite_torsion_special_fibre_of_unif T G D A U Ω _ (fun a ha => ?_) N hN)
      · rw [← Spec.map_comp]
        rfl
      · rw [RingHom.comp_apply, (residue_eq_zero_iff a).2 ha, map_zero]) d x' hu' _ hm'
  exact ⟨M, (GlobalTheory.pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ _ _ _ M hM).1⟩

end GlobalTheory.FiniteHeight
end
