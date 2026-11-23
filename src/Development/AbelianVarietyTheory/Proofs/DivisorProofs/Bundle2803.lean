module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle473
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle186
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RigCubCarry

theorem pmaps_of_pullGen {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (H : PMaps w φ' (fun k => h ≫ φ k) ε a (LB.pullGen L φ ε t h) (𝟙 Y')) : PMaps w φ' φ ε a t h := by
  intro Z r z p q hp hq
  have e := H Z r z p q hp hq
  rw [Category.comp_id] at e
  have hm' : ∀ k, (h ≫ φ k) (r z) ∈ L.U (p k) := fun k => by
    rw [← hc k]; exact hp k
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 hm'
  have hm2 : h (r z) ∈ LB.wchart L φ p := Set.mem_iInter.2 hm'
  refine Eq.trans ?_ e
  exact ((gm_res r z _ hm _).trans (gm_pull r h z _ hm2 _)).symm


open RigidIsoCube in
theorem surjective_appTop_tripleProduct_uniformisedGroup (R : Type) [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom := by
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)

theorem cubeMap_tripleProduct_unit_eq {S : Scheme.{0}} {G' : Over S} [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G') :
    (lift (1 : 𝟙_ (Over S) ⟶ G') (lift 1 1)).left ≫ m.F3 =
      (lift (1 : Over.mk (m.e ≫ (𝟙_ (Over S)).hom) ⟶ G') (lift 1 1)).left := by
  have ht : (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom))).left = m.e := by
    have w := Over.w (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom)))
    simpa using w
  apply hom_ext_triple
  intro i
  rw [Category.assoc, cubeMap_comp_proj_three m i, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  have h1 : ∀ {T : Over S}, lift (1 : T ⟶ G') (lift 1 1) ≫ x3 G' i = 1 := by
    intro T; fin_cases i <;> simp [x3]
  rw [h1, h1, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, ht]
  have e₁ : (toUnit (𝟙_ (Over S))).left = 𝟙 _ := by simp
  rw [e₁, Category.id_comp]
  exact m.e_comm

end GlobalTheory.Mum.RigCubCarry

namespace GlobalTheory.Mum



open RigidIsoCube RigCubCarry in
theorem rigidified_galois_lin_carries_rig_and_cube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PMaps (Classical.choose hP.lg) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) ∧ ∀ hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))), PMaps (Classical.choose hP.lg) (thφ G' (x3 G')) (thφ G' (x3 G')) thε U'.cubG.t U'.cubG.t (cubeMapOf hc).F3 := by
  intro R _ _ _ hB R' _ _ _ ρ hF hGal D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact σ h bc hbc hP
  obtain ⟨hw, he, hrig, -⟩ := Classical.choose_spec hP.lg
  refine ⟨(maps_iff _ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) _
    (rigPull_le _ _ he U'.LG.L) (fun _ => rfl)).1 hrig, fun hc => ?_⟩
  have sj := surjective_appTop_tripleProduct_uniformisedGroup R' G' U'.toUnifPre
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 G' := lift 1 (lift 1 1)
  have he3 : e.left ≫ (snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have pg := (isGen_iff _).1 hw
  have hψ : ∀ k : thK.{0}, thφ G' (x3 G') k ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) =
      (cubeMapOf hc).F3 ≫ thφ G' (x3 G') k := fun k => (cubeMapOf hc).psum_comm k.down
  have eF := cubeMap_tripleProduct_unit_eq (cubeMapOf hc)
  refine pmaps_of_pullGen hψ (pmaps_of_section pg U'.LG.isLB U'.LG.isLB U'.cubG.t U'.cubG.isGen
    (LB.pullGen _ _ _ U'.cubG.t (cubeMapOf hc).F3) (DVR.pullGen_isGen _ _ _ _ U'.cubG.isGen _) hψ _ e.left he3 sj
    fun y J J' hJ hJ' => ?_)
  refine ((val_pull hJ _ _ _).trans (congrArg (fun r => val U'.cubG.t r y J) eF)).trans ?_
  have face {T : Over (Sp R')} {z : T.left} {I : (T.left ⟶ G'.left) → U'.LG.L.ι}
      (hI : Good U'.LG.L z I) (x y : T ⟶ G') :
      val U'.cubG.t (lift 1 (lift x y)).left z I = 1 := by
    have hv := val_corr hI (U'.cubG.face 0) (lift x y).left
    rw [val_one] at hv
    refine (Eq.trans ?_ (val_pull hI _ _ _).symm).trans hv
    congr 1
    rw [← Over.comp_left]
    simp [faceMap, x2, pzero, Hom.one_def]
  have f1 := face (T := Over.mk ((cubeMapOf hc).e ≫ (𝟙_ (Over (Sp R'))).hom)) hJ 1 1
  have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ G') 1 1
    (fun q => gw (Classical.choose hP.lg) q y (J (q ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)))) (J' q))
  rw [_root_.mul_one, _root_.mul_one] at p
  refine f1.trans (Eq.trans ?_ (congrArg₂ (· * ·) p (face hJ' 1 1)).symm)
  simp

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin GlobalTheory.FinitePartGeneric

noncomputable section
namespace GlobalTheory.ToricTorsionSpec

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ τ : Multiplicative D.toPre.X →* Rˣ, τ ^ k = 1 → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ k = 1 ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev₀ : R →+* V), IsLocalHom ev₀ → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf ev₀)).obj G), IsMonHom bc.hom → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (hD : IsPullDeg ev₀ D.toPre D'.toPre) (U' : Unif (maximalIdeal V) D' A' G'), IsPullUnif ev₀ hD bc U U' → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (τ' : Multiplicative D'.toPre.X →* Kˣ), (∀ χ', ((τ' χ' : Kˣ) : K) = algebraMap (FractionRing V) K (algebraMap V (FractionRing V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R)))) → ∀ (q : QkPt D'.toPre K k) (x' : TFK (R := V) K ⟶ A'.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU U'.toUnifPre K k q x' → x'.left ≫ genMap U' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = spMap ((algebraMap (FractionRing V) K).comp ((algebraMap V (FractionRing V)).comp ev₀)) ≫ s.left := by
  intro R _ _ _ hB G _ _ hG D A U k hk τ hτ
  obtain ⟨hR, hC⟩ := hB
  haveI := hC
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ := GlobalTheory.ToricTorsionSecUnif.exists_torsion_toG R hR G D A U k hk
  let u : D.toPre.X →+ Additive Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : k • u = 0 := by
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  obtain ⟨gT, hgT⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D.toPre) (T := 𝟙_ (Over (Sp R))) u
  obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k u hu hgT
  obtain ⟨h, hh, -⟩ := hU _ _ ⟨g', h₁, h₂⟩
  refine ⟨h ≫ x₀, by rw [← MonObj.comp_pow, htors, MonObj.comp_one], ?_⟩
  intro V _ _ _ _ hVc ev₀ hev G' _ _ bc hbc D' A' hD U' hUU' K _ _ _ τ' hτ' q x' hq htor hqx'
  have hV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hVc⟩
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (specOf ev₀) G hG)
  have hL := firstFiveLaws
  have hL2 := abelianSchemeLaws_all
  let ξ : Sp V ⟶ N.left := spMap ev₀ ≫ h.left
  have hh' : ξ ≫ N.hom = (𝟙_ (Over (Sp V))).hom ≫ spMap ev₀ := by
    simp only [ξ, Category.assoc, Over.w h]
    rfl
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp V))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh' g₀
  let x₁' : 𝟙_ (Over (Sp V)) ⟶ (Over.pullback (specOf ev₀)).obj G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp V))).hom (by rw [Category.assoc, Over.w]; exact hh'))
      (pullback.lift_snd _ _ _)
  let x₁ : 𝟙_ (Over (Sp V)) ⟶ G' := x₁' ≫ bc.inv
  have e₁ : x₁'.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := by
    rw [Over.comp_left, Category.assoc, ← Category.assoc bc.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Category.id_comp, e₁]
  have gG := isGrpPullback_pullback G (spMap ev₀)
  have hk₁' : x₁' ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap ev₀) ⟶ N := Over.homMk ξ hh'
    have e : pushHom gG _ x₁' = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  haveI : IsMonHom bc.inv := inferInstance
  have hk₁ : x₁ ^ k = 1 := by
    show (x₁' ≫ bc.inv) ^ k = 1
    rw [← MonObj.pow_comp, hk₁', MonObj.one_comp]
  have hp := isPointOf_thru hUU' hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  have gpg := pull_grp hD
  have hb : gp.b = 1 := Over.OverMorphism.ext (gpg.1.hom_ext (((hgp 0).1 2).trans (Eq.trans ?_ ((hgp 0).1 3).symm))
    ((Over.w _).trans (Over.w _).symm))
  swap
  · show ξ ≫ g₀.b.left = ξ ≫ (1 : N ⟶ D.toPre.P.A).left
    have e1 : h.left ≫ g₀.b.left = h.left ≫ (1 : N ⟶ D.toPre.P.A).left := by
      have t1 : gT.b.left = h.left ≫ g₀.b.left := hh.1
      have t2 : gT.b = 1 := (hgT 0).1
      have t3 : h ≫ (1 : N ⟶ D.toPre.P.A) = 1 := MonObj.comp_one h
      rw [← t1, t2, ← t3]
      rfl
    simp only [ξ, Category.assoc, e1]
  let uV : D'.toPre.X → Γ((𝟙_ (Over (Sp V))).left, ⊤)ˣ := fun y =>
    unitOn (Units.map ev₀.toMonoidHom (τ (Multiplicative.ofAdd (hD.xe y))))
  have hgpT : ∀ y, TorusVal gp y (uV y) := by
    intro y
    refine ⟨hb, corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
    have v := hgp.val_id y z hJ hJ'
    rw [GlobalTheory.TorusTorsion.val_unitGen _ _ hJ']
    generalize Geo.Tor.val (gp.s y) (𝟙 _) z J' = s at v ⊢
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at v
    rw [← v]
    have c := val_corr hJ (hh.2 (hD.xe y)) (spMap ev₀)
    have c2 := GlobalTheory.TorusTorsion.TorusVal.val_eq (hgT (hD.xe y)) (spMap ev₀) hJ
    have c3 : Geo.Tor.val (g₀.s (hD.xe y)) ξ z J = gm (spMap ev₀) z ⊤ (Additive.toMul (u (hD.xe y))) := by
      first
      | exact ((val_pull hJ _ _ _).symm.trans (c.symm.trans c2))
      | exact ((val_pull hJ _ _ _).symm.trans (c.trans c2))
      | exact (c.symm.trans c2)
      | exact (c.trans c2)
    rw [c3]
    refine Units.ext ?_
    rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
    have e := GlobalTheory.ToricTorsionSec.appTop_unitOn ev₀ (τ (Multiplicative.ofAdd (hD.xe y)))
    first
    | (simp only [uV]; rw [← e]; rfl)
    | (rw [show (uV y).val = _ from e.symm]; rfl)
    | (erw [← e]; rfl)
  let fK : V →+* K := (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V))
  let uK : D'.toPre.X →+ Additive Γ((Over.mk (spMap fK)).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ' (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  obtain ⟨gK, hgK⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D'.toPre) (T := Over.mk (spMap fK)) uK
  have hpK := GlobalTheory.ToricTorsionSec.isPullF_torusPt τ' gK hgK q.g htor
  let ρ : Over.mk (spMap fK) ⟶ 𝟙_ (Over (Sp V)) := toUnit _
  have hρ : GtPt.IsPull ρ.left gp gK := GlobalTheory.TorusTorsion.isPull_of_units ρ hgpT hgK fun χ => by
    refine (GlobalTheory.ToricTorsionSec.appTop_unitOn fK _).trans ?_
    congr 2
    refine Units.ext ?_
    have := hτ' (Multiplicative.ofAdd χ)
    simp only [toAdd_ofAdd] at this
    exact this.symm
  have hpF := GlobalTheory.ToricTorsionSec.isPullF_trans hρ hpK
  have hTF : (toUnit (TF (R := V) K)).left = 𝟙 _ ≫ ρ.left := by
    rw [Category.id_comp]
    have e₁ := Over.w (toUnit (TF (R := V) K))
    have e₂ := Over.w ρ
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := V) K)).left, ← Category.comp_id ρ.left]
    exact e₁.trans ((GlobalTheory.ToricTorsionSec.spMap_comp _ _).symm.trans e₂.symm)
  have hpF' : GtPt.IsPullF K (toUnit (TF (R := V) K)).left gp q.g := by
    rw [hTF]; exact hpF
  let yK : TFK (R := V) K ⟶ (Over.pullback (jK V)).obj G' :=
    Over.homMk (pullback.lift ((toUnit (TF (R := V) K)).left ≫ x₁.left) (jFK (R := V) K)
      (by rw [Category.assoc, Over.w x₁]; exact Over.w (toUnit (TF (R := V) K)))) (pullback.lift_snd _ _ _)
  let xF : TFK (R := V) K ⟶ A'.A := yK ≫ U'.gen.hom
  have hxF : xF.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) = (toUnit (TF (R := V) K) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hQ := qkToAkU_of_integral_torsion hL.1 V (maximalIdeal V) hV (maximalIdeal.isMaximal V).ne_top D' A' G' U' k hk
    x₁ gp hk₁ (fun e => ?_) K q xF hq hpF' hxF
  · have hEq := GlobalTheory.TorsionImage.qkToAkU_unique hL2.1 hL2.2 V (maximalIdeal V) hV D' A' G' hG' U' K k hk q x' xF hqx' hQ
    subst hEq
    have hρl : ρ.left = spMap fK := by
      have e₂ := Over.w ρ
      rw [← Category.comp_id ρ.left]
      exact e₂
    show xF.left ≫ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = _
    rw [← Category.assoc, hxF, Over.comp_left, Category.assoc, e₂, hTF, Category.id_comp, hρl, Over.comp_left]
    simp only [ξ, ← Category.assoc]
    congr 1
    rw [← GlobalTheory.ToricTorsionSec.spMap_comp]
  · let xe : Over.mk (thick V (maximalIdeal V) e) ⟶ (Over.map (thick V (maximalIdeal V) e)).obj
        (thickObj V (maximalIdeal V) e G') :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick V (maximalIdeal V) e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick V (maximalIdeal V) e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩

end GlobalTheory.ToricTorsionSpec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

def TraitRed {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    {B L : LB G.left} {N : ℕ} (s : Fin (N + 1) → B.Sec) (θ : L.Sec) (Y : Over (Sp (ResidueField R))) [GrpObj Y]
    (j : Y.left ⟶ PSpace R N) (O : Y.left.Opens) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (s i) (p' ≫ β)) hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → (p' ≫ β) x ∈ nonzeroLocus θ

def embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) : X.Opens := ⨆ i, nonzeroLocus (s i)

theorem iSup_nonzeroLocus_embH {X : Scheme.{0}} {B : LB X} {N : ℕ} (s : Fin (N + 1) → B.Sec) :
    ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (embH s).ι) = ⊤ := by
  simp only [GlobalTheory.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

def embF {R : Type} [CommRing R] {X : Scheme.{0}} {B : LB X} {N : ℕ} (q : X ⟶ Sp R) (s : Fin (N + 1) → B.Sec) :
    (embH s).toScheme ⟶ PSpace R N :=
  GlobalTheory.ProjSpace.toProj ((embH s).ι ≫ q) (fun i => GlobalTheory.secPull (s i) (embH s).ι) (iSup_nonzeroLocus_embH s)

end GlobalTheory.Mum.SecEmb
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.UU GlobalTheory.LN

def tqOfGtCoord {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : TQ (thickObj R I e G) D.X where
  B := thickObj R I e D.P.A
  isAb := hB
  q := g.q
  i := g.i
  q_hom := g.q_hom
  i_hom := g.i_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  isKernel := g.isKernel
  loc b χ := by
    have := g.q_hom
    have := g.i_hom
    let ψ := D.Oφ (D.prBe I e) χ
    have hψ : ∀ k, D.Oφ g.pG χ k = g.q.left ≫ ψ k := fun k => by
      fin_cases k
      · show (padd _ _ _).left = ((Over.map (thick R I e)).map g.q ≫ padd _ _ _).left
        congr 1
        refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]; rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
      · rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    choose j hj using fun k => exists_chart D.P.isLB (ψ k b)
    have hle : g.q.left ⁻¹ᵁ LB.wchart D.P.L ψ j ≤ LB.wchart D.P.L (D.Oφ g.pG χ) j := fun x hx =>
      Set.mem_iInter.2 fun k => by rw [hψ]; exact Set.mem_iInter.1 hx k
    refine ⟨LB.wchart D.P.L ψ j, Set.mem_iInter.2 hj, res hle ((g.t χ).s j), fun Z t x h₁ h₂ => ?_⟩
    have ap : ∀ (r : Z.left ⟶ (thickObj R I e G).left) (V) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ((thickObj R I e G).left, V)ˣ)
        (z : Z.left), gm (𝟙 Z.left) z ⊤ (Units.map (r.appLE V ⊤ h).hom.toMonoidHom u) = gm r z V u :=
      fun r V h u z => (gm_res (𝟙 Z.left) z h trivial (pullU r V u)).trans ((gm_pull _ r z V (h trivial) u).trans
        (by rw [Category.id_comp]))
    have key : Units.map (((t ≫ g.i) * x).left.appLE _ ⊤ h₁).hom.toMonoidHom (res hle ((g.t χ).s j)) =
        chV t χ * Units.map (x.left.appLE _ ⊤ h₂).hom.toMonoidHom (res hle ((g.t χ).s j)) := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have m₁ := h₁ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have m₂ := h₂ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have hq : ((t ≫ g.i) * x) ≫ g.q = x ≫ g.q := by
        rw [MonObj.mul_comp, Category.assoc, g.isKernel.w, ← Category.assoc,
          toUnit_unique (t ≫ toUnit _) (toUnit Z), ← Hom.one_def, _root_.one_mul]
      have hk : ∀ k, ((t ≫ g.i) * x).left ≫ D.Oφ g.pG χ k = x.left ≫ D.Oφ g.pG χ k := fun k => by
        rw [hψ, ← Category.assoc, ← Category.assoc, ← Over.comp_left, hq, Over.comp_left]
      rw [map_mul, ap, ap]
      refine ((gm_res _ z hle m₁ _).trans (gen_trans (g.t_gen χ) _ z (hle m₁) (hJ.mem _ _))).trans (Eq.trans ?_
        (congrArg (_ * ·) ((gm_res _ z hle m₂ _).trans (gen_trans (g.t_gen χ) _ z (hle m₂) (hJ.mem _ _)))).symm)
      have w := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (g.t_weight χ) (lift t x).left).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
      rw [← Over.comp_left, ← Over.comp_left, lift_snd] at w
      have e₁ : lift t x ≫ lift (fst _ _ ≫ g.i) (snd _ _) ≫ μ[thickObj R I e G] = (t ≫ g.i) * x := by
        rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
      have e₂ : val (charGen D.X (thickObj R I e G) D.P.L χ) (lift t x).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
        refine (gm_res _ z _ (hJ.mem _ _) _).trans ((gm_pull _ _ z ⊤ trivial _).trans ?_)
        rw [← Over.comp_left, lift_fst, gm_charUnit]
      rw [e₁, e₂] at w
      refine (congrArg₂ (· * ·) ?_ w).trans (mul_left_comm _ _ _)
      exact Finset.prod_congr rfl fun k _ => congrArg
        (fun q => gm q z (D.P.L.U (j k) ⊓ D.P.L.U (J q)) (D.P.L.g (j k) (J q)) ^ Oinvε k) (hk k)
    exact (congrArg Units.val key).trans (congrArg (· * _) (chV_val t χ))



theorem unif_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ P : GlobalTheory.UU.CP G, P.L = U.LG ∧ EvenOn P := by
  intro R _ _ _ _ D A G _ _ hS U
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hL.globalFns hS w hw
  refine ⟨U'.P, rfl, ?_⟩
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hL.globalFns U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _) (Category.id_comp _) k₃ (Over.w (U'.gt 0).pG)
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let g := U'.gt 0
  have := g.q_hom
  let Q₀ := tqOfGtCoord g hB
  obtain ⟨M₀, v, hv⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hL.globalFns D.toPre)
  have hw' : g.q.left ≫ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ :=
    (Over.w g.q).trans (Category.comp_id _).symm
  have hw'' : (g.q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) ≫ D.toPre.P.A.hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ ≫ thick R (maximalIdeal R) 0 := by
    exact (Over.w g.pG).trans (congrArg (_ ≫ ·) (Category.id_comp _).symm)
  obtain ⟨w₅, k₅⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm rfl k₄ hw''
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M₀ P₀ _ _ _ g.q.left hw' hw'' hv).2
    (toBase_mul_of_isMonHom g.q hw') w₅ k₅
  let Dsc : Q₀.Desc P₀ := ⟨M₀, w₆, k₆⟩
  obtain ⟨τ, hτ⟩ := Dsc.exists_even
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨w₀, h₀⟩, τ, hτ⟩

end GlobalTheory.Mum
end
end
