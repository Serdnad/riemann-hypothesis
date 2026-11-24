module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeOfSumEqZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaBound.Ext

section Sections

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.AbLaw.PerfOfModel

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {Y Y' : Scheme.{0}}
  {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')} {π : Y' ⟶ Y} {M : LB Y}

theorem baseChangeHom_top_bijective [Module.Flat R R'] [CompactSpace Y] [IsSeparated f] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Function.Bijective (SecOnR.baseChangeHom M H.w ⊤ ⊤ le_top) := by
  first | exact _root_.GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective | exact @_root_.GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective | apply _root_.GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective <;> assumption

theorem eq_smul_iff (x y : SecOnR f M ⊤) (a : R) : x = a • y ↔
    ∀ i, (SecOnR.topEquiv f M x).f i = cst f _ a * (SecOnR.topEquiv f M y).f i := by
  have key : ∀ i, (SecOnR.topEquiv f M (a • y)).f i = cst f (M.U i) a * (SecOnR.topEquiv f M y).f i := by
    intro i
    have hs : a • y = (cst f ⊤ a) • y := rfl
    rw [hs, LinearEquiv.map_smul, ← rs_cst f (le_top : M.U i ≤ ⊤)]
    rfl
  have hext : ∀ (σ τ : LB.Sec M), (∀ i, σ.f i = τ.f i) → σ = τ := by
    rintro ⟨σf, _⟩ ⟨τf, _⟩ hh
    have : σf = τf := funext hh
    subst this
    rfl
  constructor
  · rintro rfl i
    exact key i
  · intro h
    apply (SecOnR.topEquiv f M).injective
    exact hext _ _ (fun i => (h i).trans (key i).symm)

theorem existsUnique_mul_pull [Module.Flat R R'] [CompactSpace Y] [IsSeparated f] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (θ : LB.Sec M)
    (hθ : ∀ σ : LB.Sec M, ∃! a : R, ∀ i, σ.f i = cst f _ a * θ.f i) (σ : LB.Sec (M.pull π)) :
    ∃! a : R', ∀ i, σ.f i = cst f' _ a * (Formalism.L2.Pj.thfPull M π θ).f i := by
  have e0 : (⊤ : Y'.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  have hext : ∀ (σ τ : LB.Sec (M.pull π)), (∀ i, σ.f i = τ.f i) → σ = τ := by
    rintro ⟨σf, _⟩ ⟨τf, _⟩ hh
    have : σf = τf := funext hh
    subst this
    rfl
  have hK : SecOnR.topEquiv f' (M.pull π) (SecOnR.pull M H.w ⊤ ⊤ e0 ((SecOnR.topEquiv f M).symm θ)) =
      Formalism.L2.Pj.thfPull M π θ := by
    apply hext
    intro J
    unfold Formalism.L2.Pj.thfPull SecOnR.topEquiv SecOnR.of SecOn.topEquiv LB.globalEquiv SecOnR.pull
    simp only [LinearEquiv.trans_apply, LinearEquiv.coe_mk]
    change (Y'.presheaf.map (homOfLE _).op).hom ((Y'.presheaf.map (homOfLE _).op).hom
      ((π.appLE _ _ _).hom ((Y.presheaf.map (homOfLE _).op).hom (θ.f (J PUnit.unit))))) = _
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
    have gen : ∀ (U U' : Y.Opens) (V V₁ V₂ : Y'.Opens) (i : Opposite.op U' ⟶ Opposite.op U)
        (e : V ≤ π ⁻¹ᵁ U) (i2 : Opposite.op V ⟶ Opposite.op V₁) (i3 : Opposite.op V₁ ⟶ Opposite.op V₂)
        (e' : V₂ ≤ π ⁻¹ᵁ U'),
        Y.presheaf.map i ≫ π.appLE U V e ≫ Y'.presheaf.map i2 ≫ Y'.presheaf.map i3 = π.appLE U' V₂ e' := by
      intros
      rw [Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    exact congrArg (fun g : Γ(Y, M.U (J PUnit.unit)) ⟶ Γ(Y', (M.pull π).U J) => g.hom (θ.f (J PUnit.unit)))
      (gen _ _ _ _ _ _ _ _ _ _)
  have hB : Function.Bijective (SecOnR.baseChangeHom M H.w ⊤ ⊤ e0) := baseChangeHom_top_bijective hM H
  have hsec : Function.Bijective (LinearMap.toSpanSingleton R (SecOnR f M ⊤) ((SecOnR.topEquiv f M).symm θ)) := by
    constructor
    · intro a b hab
      simp only [LinearMap.toSpanSingleton_apply] at hab
      obtain ⟨c, -, hc⟩ := hθ (SecOnR.topEquiv f M (a • (SecOnR.topEquiv f M).symm θ))
      have ha := (eq_smul_iff (a • (SecOnR.topEquiv f M).symm θ) ((SecOnR.topEquiv f M).symm θ) a).mp rfl
      have hb := (eq_smul_iff (a • (SecOnR.topEquiv f M).symm θ) ((SecOnR.topEquiv f M).symm θ) b).mp hab
      rw [LinearEquiv.apply_symm_apply] at ha hb
      exact (hc a ha).trans (hc b hb).symm
    · intro s
      obtain ⟨a, ha, -⟩ := hθ (SecOnR.topEquiv f M s)
      refine ⟨a, ?_⟩
      rw [LinearMap.toSpanSingleton_apply]
      refine ((eq_smul_iff s ((SecOnR.topEquiv f M).symm θ) a).mpr ?_).symm
      rw [LinearEquiv.apply_symm_apply]
      exact ha
  let φL := LinearEquiv.ofBijective _ hsec
  let Φ : R' → SecOnR f' (M.pull π) ⊤ := fun c =>
    SecOnR.baseChangeHom M H.w ⊤ ⊤ e0 (LinearEquiv.lTensor R' φL ((TensorProduct.rid R R').symm c))
  have hΦ : Function.Bijective Φ :=
    hB.comp ((LinearEquiv.lTensor R' φL).bijective.comp (TensorProduct.rid R R').symm.bijective)
  have hΦc : ∀ c, Φ c = c • SecOnR.pull M H.w ⊤ ⊤ e0 ((SecOnR.topEquiv f M).symm θ) := by
    intro c
    simp only [Φ, TensorProduct.rid_symm_apply, LinearEquiv.lTensor_tmul, φL, LinearEquiv.ofBijective_apply,
      LinearMap.toSpanSingleton_apply, one_smul, SecOnR.baseChangeHom_tmul]
  have key : ∀ c : R', (SecOnR.topEquiv f' (M.pull π)).symm σ =
      c • SecOnR.pull M H.w ⊤ ⊤ e0 ((SecOnR.topEquiv f M).symm θ) ↔
      ∀ i, σ.f i = cst f' _ c * (Formalism.L2.Pj.thfPull M π θ).f i := by
    intro c
    rw [eq_smul_iff, LinearEquiv.apply_symm_apply, hK]
  obtain ⟨c, hc⟩ := hΦ.2 ((SecOnR.topEquiv f' (M.pull π)).symm σ)
  refine ⟨c, (key c).mp (by rw [← hc, hΦc]), fun c' hc' => hΦ.1 ?_⟩
  rw [hΦc, hΦc, ← (key c').mpr hc', ← hc, hΦc]


open Geo.Tor Formalism.L2.Pj in
theorem existsUnique_mul_of_isoMaps {L' : LB Y'} (hM : M.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (M.pull π)}
    (hw : w.IsGen) (θ' : LB.Sec L') (θ : LB.Sec (M.pull π)) (h : IsoMaps w θ' θ)
    (hθ : ∀ σ : LB.Sec (M.pull π), ∃! a : R', ∀ i, σ.f i = constFn f' _ a * θ.f i) (σ' : LB.Sec L') :
    ∃! a : R', ∀ i, σ'.f i = constFn f' _ a * θ'.f i := by
  classical
  have unitCancel1 : ∀ {S : Type} [CommRing S] (u : Sˣ) (c a b x y : S), x = c * y → y = ↑u * b →
      x = ↑u * a → a = c * b := by
    intro S _ u c a b x y h1 h2 h3
    calc a = ↑u⁻¹ * (↑u * a) := (Units.inv_mul_cancel_left u a).symm
      _ = ↑u⁻¹ * (c * (↑u * b)) := by rw [← h3, h1, h2]
      _ = c * b := by rw [mul_left_comm, Units.inv_mul_cancel_left]
  have unitCancel2 : ∀ {S : Type} [CommRing S] (u : Sˣ) (c a b x y : S), a = c * b → y = ↑u * b →
      x = ↑u * a → x = c * y := by
    intro S _ u c a b x y h1 h2 h3
    rw [h3, h1, h2, mul_left_comm]
  have hMp : (M.pull π).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hM π
  obtain ⟨w', hw', hinv⟩ := GlobalTheory.GenericSectionBasis.exists_inv_iso w hw
  set σ : LB.Sec (M.pull π) := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso σ' hw' hMp hL' with hσdef
  have hrel : ∀ (y : Y') (J : (M.pull π).ι) (k : L'.ι), y ∈ (M.pull π).U J → y ∈ L'.U k →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (σ.f J) =
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y') y (J PUnit.unit) k).val *
            ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (σ'.f k) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (θ.f J) =
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y') y (J PUnit.unit) k).val *
            ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 Y') y _ (θ'.f k) := by
    intro y J k hJ hk
    constructor
    · have hs := GlobalTheory.GenericGenerated.gs_secOfIso w' σ' hw' hMp hL' J k (𝟙 Y') y
        (TopologicalSpace.Opens.mem_inf.2 ⟨hJ, hk⟩)
      rw [hinv Y' (𝟙 Y') y k J (TopologicalSpace.Opens.mem_inf.2 ⟨hk, hJ⟩), inv_inv] at hs
      exact hs
    · exact (GlobalTheory.ArcQ.FrUniq.isoMaps_iff w θ' θ).mp h Y' (𝟙 Y') y (J PUnit.unit) k
        ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull).mp hJ) hk
  obtain ⟨a, ha, huniq⟩ := hθ σ
  have haP := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ θ a).mp ha
  refine ⟨a, ?_, ?_⟩
  · refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ' θ' a).mpr ?_
    intro k y hk
    obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hM (π y)
    have hJ : y ∈ (M.pull π).U (fun _ => j) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull).mpr hj
    obtain ⟨h3, h2⟩ := hrel y (fun _ => j) k hJ hk
    exact unitCancel1 _ _ _ _ _ _ (haP (fun _ => j) y hJ) h2 h3
  · intro b hb
    have hbP := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ' θ' b).mp hb
    apply huniq
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_eq_iff f' σ θ b).mpr ?_
    intro J y hJ
    obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL' y
    obtain ⟨h3, h2⟩ := hrel y J k hJ hk
    exact unitCancel2 _ _ _ _ _ _ (hbP k y hk) h2 h3

end Sections

section Lie

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.LieRel
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec univChartLoc tanBC_alg
  pushR pushR_left pushR_map tvec_tmap fB dualMapA pushR_inj)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_eigenbasis_pullback {V V' : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing V']
    [Algebra V V'] [Module.Flat V V'] (G : Over (Sp V)) [GrpObj G] [Smooth G.hom] {O : Type} (act : O → (G ⟶ G))
    [∀ a, IsMonHom (act a)] (χ : O → V) {m : ℕ} (u : Fin m → (epsOver V V ⟶ G)) (ht : ∀ i, IsTan (u i))
    (he : ∀ i a, (u i ≫ act a).left = spMap (epsMul (χ a)) ≫ (u i).left)
    (hb : ∀ w : epsOver V V ⟶ G, IsTan w → (∀ a, (w ≫ act a).left = spMap (epsMul (χ a)) ≫ w.left) →
      ∃! c : Fin m → V, IsComb u c w) :
    ∃ u' : Fin m → (epsOver V' V' ⟶ (Over.pullback (fB V V')).obj G), (∀ i, IsTan (u' i)) ∧
      (∀ i a, (u' i ≫ (Over.pullback (fB V V')).map (act a)).left =
        spMap (epsMul (algebraMap V V' (χ a))) ≫ (u' i).left) ∧
      (∀ w : epsOver V' V' ⟶ (Over.pullback (fB V V')).obj G, IsTan w →
        (∀ a, (w ≫ (Over.pullback (fB V V')).map (act a)).left = spMap (epsMul (algebraMap V V' (χ a))) ≫ w.left) →
        ∃! c : Fin m → V', IsComb u' c w) ∧
      ∀ i, (u' i).left ≫ pullback.fst G.hom (fB V V') = spMap (dualMap (algebraMap V V')) ≫ (u i).left := by
  first | exact _root_.GlobalTheory.PlaceInt.Ext.exists_eigenbasis_pullback | exact @_root_.GlobalTheory.PlaceInt.Ext.exists_eigenbasis_pullback | apply _root_.GlobalTheory.PlaceInt.Ext.exists_eigenbasis_pullback <;> assumption

end Lie

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_restrict (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ)
    (h : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) :
    ∃ φ : T.V →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a) := by
  first | exact _root_.GlobalTheory.PlaceInt.Ext.exists_restrict | exact @_root_.GlobalTheory.PlaceInt.Ext.exists_restrict | apply _root_.GlobalTheory.PlaceInt.Ext.exists_restrict <;> assumption

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


open GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique in
theorem integral_of_frMap (T T' : CDVR) (io : c.F →+* T.Fr) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V)
    (hφ : ∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) :
    letI := io.toAlgebra
    letI := (iT.comp io).toAlgebra
    ∀ (ψ : T.Fr →ₐ[c.F] T'.Fr) (y : FrPt Xo c T.Fr) (y' : FrPt Xo c T'.Fr), ψ.toRingHom = iT → FrMap ψ y y' →
      Integral T io y → Integral T' (iT.comp io) y' := by
  intro ψ y y' hψ hm hy
  letI : Algebra c.F T.Fr := io.toAlgebra
  letI : Algebra c.F T'.Fr := (iT.comp io).toAlgebra
  have isoSec : ∀ {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {F : Y ⟶ X} (w : LB.Iso L' (L.pull F))
      (hw : w.IsGen) (hA : L'.IsLB) (hB : (L.pull F).IsLB) (s : LB.Sec (L.pull F)),
      IsoMaps w (ReciprocityTheory.ChartRestriction.G.DVR.secOfIso s hw hA hB) s := by
    intro X Y L L' F w hw hA hB s i k
    have e := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec s hw hA hB k i
    have hV : (L.pull F).U i ⊓ L'.U k ≤ L'.U k ⊓ (L.pull F).U i := le_of_eq (inf_comm _ _)
    have e2 := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.rs hV) e
    unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand at e2
    unfold ReciprocityTheory.ChartRestriction.G.Semi.res at e2
    unfold ReciprocityTheory.ChartRestriction.G.DVR.rs at e2
    have hcomp : ∀ {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(Y, U)),
        (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom a) =
          (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
      intro U V W h1 h2 a
      change (Y.presheaf.map (homOfLE h1).op ≫ Y.presheaf.map (homOfLE h2).op).hom a = _
      rw [← Functor.map_comp]
      rfl
    have hid : ∀ {U : Y.Opens} (h : U ≤ U) (a : Γ(Y, U)), (Y.presheaf.map (homOfLE h).op).hom a = a := by
      intro U h a
      change (Y.presheaf.map (𝟙 (Opposite.op U))).hom a = a
      rw [CategoryTheory.Functor.map_id]
      rfl
    simp only [map_mul, Units.coe_map_inv, MonoidHom.coe_coe, hcomp] at e2
    erw [hid] at e2
    rw [e2]
    exact (Units.mul_inv_cancel_left (w.s (i, k)) _).symm
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hlift⟩, θ, hθ, htie⟩ := hy
  have hsq : (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) := RingHom.ext hφ
  have hsqS : spMap (algebraMap T'.V T'.Fr) ≫ spMap φ = spMap iT ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.FramedBaseChange.spMap_spMap, GlobalTheory.FramedBaseChange.spMap_spMap, hsq]
  have hcast : ∀ {S' S : Scheme.{0}} {t₁ : SAB H S'} {t₂ : SAB H S} {f g : S' ⟶ S} (h : f = g) (m : SABMap t₁ t₂ f),
      ∃ m' : SABMap t₁ t₂ g, m'.φ = m.φ := by
    intro S' S t₁ t₂ f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨PP', cub', sym', adj', prim', n2, hn2⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
  let G' := (fun {t : SAB H (Sp T'.V)} (_ : SABMap t G (spMap φ)) => t) n2
  obtain ⟨PP'', cub'', sym'', adj'', prim'', m2', hm2'⟩ :=
    sabPull Out.CubePf.cubePull (spMap (algebraMap T'.V T'.Fr)) G'
  let t'' := (fun {t : SAB H (Sp T'.Fr)} (_ : SABMap t G' (spMap (algebraMap T'.V T'.Fr))) => t) m2'
  obtain ⟨k, hk⟩ := sabComp pullCubComp E H _ _ _ G G' t'' (spMap φ) (spMap (algebraMap T'.V T'.Fr)) n2 m2'
  obtain ⟨k', hk'⟩ := hcast hsqS k
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ G t' t'' (spMap (algebraMap T.V T.Fr)) (spMap iT) m2 k'
  have hx' : spMap iT ≫ y.x = y'.x := by rw [hm.1, hψ]
  obtain ⟨m1c, hm1c⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t t' t'' y.x (spMap iT) m1 n
  obtain ⟨m1', hm1'⟩ := hcast hx' m1c
  have hφinj : Function.Injective φ := by
    intro a b h
    apply IsFractionRing.injective T.V T.Fr
    apply iT.injective
    rw [← hφ, ← hφ, h]
  letI : Algebra T.V T'.V := φ.toAlgebra
  haveI : Module.IsTorsionFree T.V T'.V := ⟨fun r hr a b hab => by
    have hr0 : φ r ≠ 0 := fun h0 => hr.ne_zero (hφinj (by rw [h0, map_zero]))
    exact mul_left_cancel₀ hr0 hab⟩
  haveI : Module.Flat T.V T'.V := inferInstance
  obtain ⟨_, hsm, hsep, hqc, -, -⟩ := G.semi
  have hχ : ∀ (τ : E →+* ℂ) (a : 𝓞 E), ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ a) :=
    fun τ a => int_val (c := c) T io τ a
  choose χ hχ using hχ
  haveI : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  have hLie := fun τ => exists_eigenbasis_pullback (V' := T'.V) G.G (fun a => G.act.act a) (χ τ) (ub τ) (htan τ)
    (fun i a => heig τ i a (χ τ a) (hχ τ a))
    (fun w hw he => hbas τ w hw (fun a z hz => by
      have hz' : z = χ τ a := IsFractionRing.injective T.V T.Fr (by rw [hz, hχ])
      rw [hz']
      exact he a))
  choose ub' htan' heig' hbas' hpr' using hLie
  have hpr'' : ∀ τ i, (ub' τ i).left ≫ pullback.fst G.G.hom (spMap φ) = spMap (dualMap φ) ≫ (ub τ i).left :=
    hpr'
  have hmono : Mono (spMap (algebraMap T.V T.Fr)) := by
    haveI : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
    exact Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap T.V T.Fr)).op
  have hlift' : ∀ τ i, ∃ u'' : Sp (DualNumber T'.Fr) ⟶ t''.G.left, u'' ≫ m1'.φ = y'.u τ i ∧
      u'' ≫ m2'.φ = spMap (dualMap (algebraMap T'.V T'.Fr)) ≫ (ub' τ i).left := by
    intro τ i
    obtain ⟨u0, hu1, hu2⟩ := hlift τ i
    have hw : (spMap (dualMap (algebraMap T'.V T'.Fr)) ≫ (ub' τ i).left) ≫ G'.G.hom =
        spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap (algebraMap T'.V T'.Fr) := by
      rw [Category.assoc, Over.w (ub' τ i), GlobalTheory.Reg.ChartInhab.eps_hom, GlobalTheory.ArcQ.FrBC.dual_alg]
    have hb0 : u0 ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply (cancel_mono (spMap (algebraMap T.V T.Fr))).1
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i),
        GlobalTheory.Reg.ChartInhab.eps_hom, GlobalTheory.ArcQ.FrBC.dual_alg]
    have hkey : m2'.cart.1.lift _ _ hw ≫ n.φ = spMap (dualMap iT) ≫ u0 := by
      apply m2.cart.1.hom_ext
      · rw [Category.assoc, ← hn, hk', hk, ← Category.assoc, m2'.cart.1.lift_fst, Category.assoc, hn2,
          hpr'' τ i, Category.assoc, hu2, ← Category.assoc, ← Category.assoc, ← GlobalTheory.ArcQ.FrBC.dual_comp,
          ← GlobalTheory.ArcQ.FrBC.dual_comp, hsq]
      · rw [Category.assoc, n.cart.1.w, ← Category.assoc, m2'.cart.1.lift_snd, Category.assoc, hb0,
          GlobalTheory.ArcQ.FrBC.dual_alg]
    refine ⟨m2'.cart.1.lift _ _ hw, ?_, m2'.cart.1.lift_fst _ _ _⟩
    rw [hm1', hm1c, ← Category.assoc, hkey, Category.assoc, hu1, hm.2.1 τ i, hψ]
  unfold Integral
  refine ⟨G', t'', m1', m2', ⟨ub', htan', fun τ i a z hz => ?_, fun τ w hw he => ?_, hlift'⟩, ?_⟩
  · have hz' : z = φ (χ τ a) := IsFractionRing.injective T'.V T'.Fr (by rw [hz, hφ, hχ]; rfl)
    rw [hz']
    exact heig' τ i a
  · exact hbas' τ w hw (fun a => he a (φ (χ τ a)) (by rw [hφ, hχ]; rfl))
  · obtain ⟨wn, hwn⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso n2
    letI : GrpObj ((Over.pullback (spMap φ)).obj G.G) := G'.grp
    have hAlb := G'.PP.isLB
    have hBlb := pull_isLB G.PP.isLB n2.φ
    let θ' := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (thfPull G.PP.L n2.φ θ) hwn.1 hAlb hBlb
    have hiso : IsoMaps wn θ' (thfPull G.PP.L n2.φ θ) := isoSec wn hwn.1 hAlb hBlb _
    have hT : GlobalTheory.ArcQ.FrUniq.Comparison₂ m1 m2 θ y.s := (GlobalTheory.ArcQ.FrUniq.tie_iff m1 m2 θ y.s).1 htie
    obtain ⟨-, -, pm, hps, hpb, hpm⟩ := hm
    have hT' : GlobalTheory.ArcQ.FrUniq.Comparison₂ m1' k' θ y'.s := by
      refine GlobalTheory.ArcQ.FrUniq.tie_pull m1 m2 θ y.s n m1' k' hx'.symm rfl (hm1'.trans hm1c) hn y'.s pm hps
        (by rw [hpb, hψ]) (fun Z r z j hz => ?_) hT
      rw [← hpm (fun _ => j) (GlobalTheory.FramedBaseChange.chart_le pm hps _)]
      exact GlobalTheory.EndDivisible.gs_appLE r pm z _ _ _ hz _
    obtain ⟨w1, wk, σ, hr1, hrk, hsec, hpt⟩ := hT'
    obtain ⟨θk, hθk, hik⟩ := (GlobalTheory.ArcQBC.through_iff (w := wk) θ σ).2
      (fun z j kk hj hk => hpt _ (𝟙 _) z j kk hj hk)
    obtain ⟨w', hw', hi'⟩ := GlobalTheory.ArcQ.FrBC.exists_isoMaps_cancel n2 m2' k' hsqS.symm (hk'.trans hk) hwn hrk
      hiso (fun _ _ => rfl) hik hθk
    refine ⟨θ', ?_, (GlobalTheory.ArcQ.FrUniq.tie_iff m1' m2' θ' y'.s).2 ⟨w1, w', σ, hr1, hw', hsec,
      fun Z r z j kk hj hk => GlobalTheory.ArcQ.FrBC.gs_of_isoMaps hi' (fun _ _ => rfl) r z j kk hj hk⟩⟩
    intro σ''
    haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
    have hgen := existsUnique_mul_pull (f := G.G.hom) (f' := G'.G.hom) (π := n2.φ) G.PP.isLB n2.cart.1 θ
      (fun σ => hθ σ)
    exact existsUnique_mul_of_isoMaps (f' := G'.G.hom) G.PP.isLB hAlb hwn.1 θ' _ hiso hgen σ''

end Main

end GlobalTheory.ThetaBound.Ext

namespace GlobalTheory.ThetaBound

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem exists_isExt_and_trans : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e : ℕ), 0 < e → (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) → (∃ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y') ∧ ∀ y' : IntFr Xo c T' (iT.comp io), IsExt y iT e y' → xOf y' = spMap iT ≫ xOf y ∧ ∀ (T'' : CDVR) (iT' : T'.Fr →+* T''.Fr) (e' : ℕ) (y'' : IntFr Xo c T'' (iT'.comp (iT.comp io))), IsExt y' iT' e' y'' → IsExt y (iT'.comp iT) (e' * e) y'' := by
  first | exact _root_.GlobalTheory.PlaceInt.exists_isExt_and_trans | exact @_root_.GlobalTheory.PlaceInt.exists_isExt_and_trans | apply _root_.GlobalTheory.PlaceInt.exists_isExt_and_trans <;> assumption

end GlobalTheory.ThetaBound
