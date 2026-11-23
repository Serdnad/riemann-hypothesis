module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle154
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.PreEven
open GlobalTheory.UU GlobalTheory.ClosedPol



theorem evenOn_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P := by
  intro R _ _ _ D A G _ _ U
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.X :=
    { B := thickObj R (maximalIdeal R) 0 D.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U.P
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U.P.L.isLB _) _ (pullIso_isGen U.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := isCPMap_w hG U 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D)
  obtain ⟨w₄, k₄⟩ := cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w g.pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  exact ⟨D.X, inferInstance, inferInstance, inferInstance, Q, P₀, ⟨w₀, h₀⟩,
    GlobalTheory.UniformizationSetting.exists_even_of_desc De⟩

end GlobalTheory.Mum.PreEven
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Mum

theorem exists_comp_eq_fst {S S' U U' X X' : Scheme.{0}} {g : X ⟶ S} {g' : X' ⟶ S'} {s : S' ⟶ S} {β : X' ⟶ X}
    (pb : IsPullback β g' g s) {j : U ⟶ S} [Mono j] {j' : U' ⟶ S'} {u : U' ⟶ U} (sq : u ≫ j = j' ≫ s)
    (κ : pullback g' j' ⟶ pullback g j) (hκ : κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    ∃ c : pullback (pullback.snd g j) u ⟶ pullback g' j', c ≫ κ = pullback.fst _ _ := by
  have w : (pullback.fst (pullback.snd g j) u ≫ pullback.fst g j) ≫ g = (pullback.snd (pullback.snd g j) u ≫ j') ≫ s := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, sq, Category.assoc]
  refine ⟨pullback.lift (pb.lift _ _ w) _ (pb.lift_snd _ _ w), ?_⟩
  rw [← cancel_mono (pullback.fst g j), Category.assoc, hκ, pullback.lift_fst_assoc, pb.lift_fst]

theorem lbIso_pull_pull_of_third {Q Y X Z Z' B : Scheme.{0}} {c : Q ⟶ Y} {κ : Y ⟶ X} {q : Q ⟶ X} (hc : c ≫ κ = q)
    {p : X ⟶ Z} {p' : Y ⟶ Z'} {β : Z' ⟶ Z} (hκ : κ ≫ p = p' ≫ β) {a : X ⟶ B} {M : LB B} {N : LB Z} {L' : LB Z'}
    (hM : M.IsLB) (hN : N.IsLB) (hL' : L'.IsLB) (h₁ : LBIso (L'.pull p') (M.pull (κ ≫ a))) (h₂ : LBIso L' (N.pull β)) :
    LBIso ((M.pull a).pull q) ((N.pull p).pull q) := by
  have hA := pull_isLB hM a
  have hP := pull_isLB hN p
  have e₁ : LBIso (L'.pull (c ≫ p')) (M.pull (q ≫ a)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp c rfl (by rw [← Category.assoc, hc]) h₁
  have e₂ : LBIso (L'.pull (c ≫ p')) (N.pull (q ≫ p)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso h₂ _ (by rw [Category.assoc, ← hκ, ← hc, Category.assoc])
  exact LBIso.trans (pull_isLB hA _) (pull_isLB hM _) (pull_isLB hP _)
    (GlobalTheory.GenSpread.lbIso_pull_pull hM q rfl).symm
    (LBIso.trans (pull_isLB hM _) (pull_isLB hL' _) (pull_isLB hP _) e₁.symm
      (LBIso.trans (pull_isLB hL' _) (pull_isLB hN _) (pull_isLB hP _) e₂
        (GlobalTheory.GenSpread.lbIso_pull_pull hN q rfl)))

theorem exists_fractionRing_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ g : FractionRing R →+* FractionRing R',
      g.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := by
  have hinj : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    fun a b h => hρ (IsFractionRing.injective R' (FractionRing R') h)
  exact ⟨IsFractionRing.lift (K := FractionRing R) hinj,
    RingHom.ext fun r => IsFractionRing.lift_algebraMap (K := FractionRing R) hinj r⟩

theorem lbIso_generic_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G' → IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → ∀ (L' : LB G'.left), L'.IsLB → LBIso (L'.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) → ∀ P : GlobalTheory.UU.CP G, LBIso L' (P.L.L.pull β) → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ G' _ _ G _ _ β _ _ pb A gen κ hgen hκ L' hL' h₁ P h₂
  obtain ⟨gam, hgam⟩ := exists_fractionRing_map ρ hρ.2.1
  have sq : spMap gam ≫ jK R = jK R' ≫ spMap ρ :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap hgam).trans (spMap_comp ρ _))
  have hX : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback A.isAb (isGrpPullback_of_iso gen)
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  obtain ⟨c, hc⟩ := exists_comp_eq_fst pb.1 sq κ hκ
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap gam) _ hX (pull_isLB A.isLB _)
    (pull_isLB P.L.isLB _) (lbIso_pull_pull_of_third hc hκ A.isLB P.L.isLB hL' h₁ h₂)

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.GenPol

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ (A' : PolAV (Sp (FractionRing R))) (gen' : (Over.pullback (jK R)).obj G ≅ A'.A), IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o oA oG hlin w hw hpsi P hP
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have : IsCommMonObj A.A := A.isAb.comm
  have hwA : IsMonHom (oA.act w) := oA.hom w
  have hwA' : IsMonHom (oA.act (star w)) := oA.hom (star w)
  have hs : oA.act w * oA.act (star w) = 𝟙 A.A := by
    rw [Hom.mul_def]
    change padd A.A (oA.act w) (oA.act (star w)) = 𝟙 A.A
    rw [← oA.map_add, hw, oA.map_one]
  have ha := (GlobalTheory.RosLam.rosatiAdj_iff_lamEq laws.globalFns _ A _ _ hwA hwA').1 (oA.rosati w)
  obtain ⟨L', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.CM.exists_normalised_polarisation laws (FractionRing R) A _ _ hwA hwA' hs ha
  let A' : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L', isLB := h1, rigid := h2, sym := h3,
      ample := h4, ktriv := h5 }
  refine ⟨A', U.gen, U.gen_hom, ?_⟩
  haveI := U.gen_hom
  have hLG := U.LG.isLB
  have hAL := A.isLB
  let φ := pullback.fst G.hom (jK R)
  let GK := (Over.pullback (jK R)).obj G
  let wGK := (Over.pullback (jK R)).map (oG.act w)
  have lbc : ∀ {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ B))
      {L : LB B.left}, L.IsLB → (cubeLB B x L).IsLB := fun x L hL => DVR.linComb_isLB _ hL _ _
  have s1 : LBIso L' (cubeLB A.A ![𝟙 A.A, oA.act w] A.L) := by
    have e := GlobalTheory.LamCalc.lbIso_of_lamEq h6 (𝟙 A.A) (oA.act w)
    simp only [Category.comp_id] at e
    exact LBIso.trans h1 (lbc _ h1) (lbc _ hAL) h7 e
  have s2 := GlobalTheory.RigidBundleGlue.LBIso.pull s1 U.gen.hom.left
  have hext : LBIso (U.LG.L.pull φ) (A.L.pull U.gen.hom.left) := by
    obtain ⟨v, hv⟩ := U.ext
    exact LBIso.symm ⟨v, hv⟩
  have hgp := isGrpPullback_of_iso U.gen
  have s3 := GlobalTheory.ShapePull.iso_cubeLB_pull hgp (pushPt hgp.1.w (𝟙 GK)) hext
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 A.A) (b := oA.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      have e := congrArg (fun q => q.left) (hlin.ext w)
      simp only [Over.comp_left] at e
      simp only [pushPt, Over.homMk_left, Over.comp_left, Over.id_left, Category.id_comp]
      exact e)
  have hpb := isGrpPullback_pullback G (jK R)
  have s4 := GlobalTheory.ShapePull.iso_cubeLB_pull hpb (pushPt hpb.1.w (𝟙 GK)) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hLG φ))
    (a' := 𝟙 GK) (b' := wGK) (a := 𝟙 G) (b := oG.act w) (Category.comp_id _).symm (by
      refine Over.OverMorphism.ext ?_
      show wGK.left ≫ φ = (𝟙 GK.left ≫ φ) ≫ (oG.act w).left
      rw [Category.id_comp]
      simp only [wGK, φ, Over.pullback_map_left, pullback.lift_fst])
  have s5 := GlobalTheory.RigidBundleGlue.LBIso.pull hP φ
  have e3 : (pushPt hgp.1.w (𝟙 GK)).left = U.gen.hom.left := by simp [pushPt]
  have e4 : (pushPt hpb.1.w (𝟙 GK)).left = φ := Category.id_comp _
  rw [e3] at s3
  rw [e4] at s4
  have i1 := pull_isLB h1 U.gen.hom.left
  have i2 := pull_isLB (lbc ![𝟙 A.A, oA.act w] hAL) U.gen.hom.left
  have i3 := lbc ![𝟙 GK, wGK] (pull_isLB hLG φ)
  have i4 := pull_isLB (lbc ![𝟙 G, oG.act w] hLG) φ
  have i5 := pull_isLB P.L.isLB φ
  exact LBIso.trans i1 i2 i5 s2 (LBIso.trans i2 i3 i5 s3.symm (LBIso.trans i3 i4 i5 s4 s5.symm))

end GlobalTheory.Mum.GenPol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.Mum

theorem has_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R (maximalIdeal R) → AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → Has D → Has D' := by
  intro R R' _ _ _ _ _ _ ρ hR hR' hinj hloc D D' ⟨hD⟩ ⟨G, _, _, A, hsa, ⟨U⟩⟩
  have hP := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT := GlobalTheory.twistBaseChange
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ρ x h)
  have sq : spMap (fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hinj).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hinj)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf ρ)).obj G)) G
      (spMap (fracMap hinj) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf ρ)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap ρ))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (spMap ρ) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf ρ)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf ρ)).obj G) ≫ (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf ρ) = specOf ρ ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap ρ))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf ρ)).obj G) _ (specOf ρ) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf ρ) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf ρ)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf ρ)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf ρ)).obj G) _ (specOf ρ) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  have hgD : D'.toPre.P.g = D.toPre.P.g := H1.dim_unique _ D'.toPre.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.toPre.P.smoothDim)
    (eSec D'.toPre.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R'))
  obtain ⟨U', -, -, -⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg hP hG hS hT R R' _ _ hR hR' ρ hI D A G hsa
    U D' hD hgD ((Over.pullback (specOf ρ)).obj G) (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he
    (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨(Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance, A', IsSemiAbelian.pullback _ G hsa, ⟨U'⟩⟩

end GlobalTheory.Mum
end
end

section

noncomputable section

open IsLocalRing

namespace GlobalTheory.FiniteCompletionLocalHom

theorem isLocalHom_of_finite {R R₂ V : Type*} [CommRing R] [IsLocalRing R] [CommRing R₂] [IsLocalRing R₂]
    [CommRing V] [IsLocalRing V] (ρ : R →+* R₂) (hρ : ρ.Finite) (ψ : R₂ →+* V)
    (h : IsLocalHom (ψ.comp ρ)) : IsLocalHom ψ := by
  letI := ρ.toAlgebra
  haveI : Module.Finite R R₂ := hρ
  haveI : Algebra.IsIntegral R R₂ := Algebra.IsIntegral.of_finite R R₂

  have hc : (maximalIdeal V).comap (ψ.comp ρ) = maximalIdeal R :=
    ((IsLocalRing.local_hom_tfae (ψ.comp ρ)).out 1 5).mp h
  have hP : ((maximalIdeal V).comap ψ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    have hc' : ((maximalIdeal V).comap ψ).comap (algebraMap R R₂) = maximalIdeal R := hc
    change (((maximalIdeal V).comap ψ).comap (algebraMap R R₂)).IsMaximal
    rw [hc']
    infer_instance
  exact ((IsLocalRing.local_hom_tfae ψ).out 1 5).mpr (IsLocalRing.eq_maximalIdeal hP)

theorem exists_extension : ∀ (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), IsLocalHom φ →
    ∀ (ρ : R →+* R₂), RingHom.Finite ρ → ∀ (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω) (m : R₂ →+* Ω),
    Function.Injective m → (∀ r : R, m (ρ r) = j (algebraMap W (FractionRing W) (φ r))) →
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ GlobalTheory.Mum.FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧
      (∀ w : W, j₂ (algebraMap W₂ (FractionRing W₂) (σ w)) = j (algebraMap W (FractionRing W) w)) ∧
      ∀ r : R₂, j₂ (algebraMap W₂ (FractionRing W₂) (φ₂ r)) = m r := by
  intro R R₂ W _ _ _ _ _ _ _ _ _ hW φ hφ ρ hρ Ω _ j m hm hcomp
  obtain ⟨hdvr, hcompl, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).mp hW
  haveI := hdvr
  haveI := hcompl
  haveI := hchar
  letI : Algebra (FractionRing W) Ω := j.toAlgebra
  letI : Algebra W Ω := (j.comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

  obtain ⟨s₀, hs₀int, hs₀⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ m (fun r => hcomp r)
  have hmint : ∀ r, IsIntegral W (m r) := fun r =>
    hs₀ (integralClosure W Ω) (fun x hx => hs₀int x hx) r

  let F : IntermediateField (FractionRing W) Ω := algebraicClosure (FractionRing W) Ω
  have hmF : ∀ r, m r ∈ F := fun r =>
    ((hmint r).tower_top : IsIntegral (FractionRing W) (m r))
  letI : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic W F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing W)).mpr inferInstance
  haveI : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).mpr
    ((algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W (FractionRing W)))
  let mF : R₂ →+* F := m.codRestrict F hmF
  obtain ⟨s, hsint, hs⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ mF (fun r => Subtype.ext (hcomp r))

  obtain ⟨W', hdvr', hc₁, -, hfin, -, hloc, -, hmem⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra W F s
  haveI := hdvr'
  have hWs : ∀ a, mF a ∈ W' := hs W' fun x hx => hmem x hx (hsint x hx)
  let φ₂ : R₂ →+* W' := mF.codRestrict W' hWs
  let σ : W →+* W' := algebraMap W W'
  have hσinj : Function.Injective σ := fun a b hab =>
    FaithfulSMul.algebraMap_injective W F (congrArg Subtype.val hab)
  let ι : W' →+* Ω := (algebraMap F Ω).comp (algebraMap W' F)
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  let j₂ : FractionRing W' →+* Ω := IsFractionRing.lift hιinj
  have hC : GlobalTheory.LN.CDvr W' :=
    (GlobalTheory.LN.cDvr_iff W').mpr ⟨hdvr', hc₁, charZero_of_injective_algebraMap hσinj⟩
  have hcomm : φ₂.comp ρ = σ.comp φ := RingHom.ext fun r => Subtype.ext (Subtype.ext (hcomp r))
  haveI : IsLocalHom σ := hloc
  have hloc₂ : IsLocalHom (φ₂.comp ρ) := by
    rw [hcomm]
    exact RingHom.isLocalHom_comp σ φ
  refine ⟨W', inferInstance, inferInstance, inferInstance, σ, φ₂, j₂, hC,
    (⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hC, hσinj, RingHom.finite_algebraMap.mpr hfin⟩ : _ ∧ _ ∧ _),
    hloc, fun a b hab => hm (congrArg (fun x : W' => ((x : F) : Ω)) hab),
    isLocalHom_of_finite ρ hρ φ₂ hloc₂, hcomm, fun w => IsFractionRing.lift_algebraMap hιinj (σ w),
    fun r => IsFractionRing.lift_algebraMap hιinj (φ₂ r)⟩

end GlobalTheory.FiniteCompletionLocalHom
end
end

section

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Mum

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

abbrev baseMap (R : Type) [CommRing R] [IsDomain R] (E : Type) [Field E] [Algebra (FractionRing R) E] : R →+* E :=
  (algebraMap (FractionRing R) E).comp (algebraMap R (FractionRing R))

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

theorem finExt_integralClosure [IsLocalRing R] (hR : Base R) [FiniteDimensional (FractionRing R) E]
    [IsGalois (FractionRing R) E] :
    letI := (baseMap R E).toAlgebra
    ∃ _ : IsLocalRing (integralClosure R E), FinExt (algebraMap R (integralClosure R E)) := by
  letI := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨⟨hN, -, hI, hC⟩, -⟩ := hR
  set R₂ := integralClosure R E
  haveI : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) E R₂
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_isAdicComplete R
  haveI : IsLocalRing R₂ := GlobalTheory.TameKummer.isLocalRing_of_finite R R₂
  refine ⟨inferInstance, ⟨IsNoetherianRing.of_finite R R₂, inferInstance,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, ?_, ?_⟩
  · intro a b h
    have := congrArg (algebraMap R₂ E) h
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) E).injective this)
  · exact RingHom.finite_algebraMap.2 inferInstance

end GlobalTheory.GalClosure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

end GlobalTheory.GalClosure
end
