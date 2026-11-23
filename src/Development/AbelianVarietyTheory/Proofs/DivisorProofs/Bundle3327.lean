module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3319
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle099
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.PoincUnif

theorem exists_unif_finExt : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
    [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
    (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
    IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
    ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
    IsSemiAbelian G → IsMonHom gen.hom →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
        (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
        ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
          (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
          (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
          IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
          LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂') := by
  intro g n o _ ζ F V₁ _ _ _ hV y₁ A α α₂ hα hsq hL G _ _ gen hG hgen
  haveI : IsMonHom gen.hom := hgen
  have hdvr : IsDiscreteValuationRing V₁ := hV.1
  have hLgen : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  obtain ⟨PP, hPP⟩ := GlobalTheory.MumExt.exists_extLam V₁ G hG _ hLgen
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hβ₂, hPβ⟩ :=
    GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle V₁ hV G hG A gen hgen PP hPP
  obtain ⟨-, hinj, hfin⟩ := hρ
  have hloc : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite V₁ R' := hfin
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_algebraMap
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let fK : FractionRing V₁ →+* FractionRing R' := IsFractionRing.lift (K := FractionRing V₁) hinj'
  have hfK : ∀ a, fK (algebraMap V₁ _ a) = algebraMap R' _ (ρ a) := fun a =>
    IsFractionRing.lift_algebraMap _ _
  have hbase : jK R' ≫ spMap ρ = spMap fK ≫ jK V₁ := by
    have e : fK.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap R' (FractionRing R')).comp ρ :=
      RingHom.ext hfK
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom e.symm

  let g₁ : A₁.A.left ⟶ G₁.left := U₁.gen.inv.left ≫ pullback.fst G₁.hom (jK R')
  have hg₁ : IsGrpPullback A₁.A G₁ (jK R') g₁ := GlobalTheory.ThetaBaseChange.grp_generic U₁.toUnifPre
  have hgβ := hg₁.comp hβ
  have hfst : IsGrpPullback ((Over.pullback (jK V₁)).obj G) G (jK V₁) (pullback.fst G.hom (jK V₁)) :=
    isGrpPullback_pullback G (jK V₁)
  have hw : (g₁ ≫ β) ≫ G.hom = (A₁.A.hom ≫ spMap fK) ≫ jK V₁ := by
    have := hgβ.1.w
    simp only [Category.assoc] at this ⊢
    rw [← hbase]; exact this
  let ι' : A₁.A.left ⟶ ((Over.pullback (jK V₁)).obj G).left := hfst.1.lift (g₁ ≫ β) (A₁.A.hom ≫ spMap fK) hw
  have hι'f : ι' ≫ pullback.fst G.hom (jK V₁) = g₁ ≫ β := hfst.1.lift_fst _ _ _
  have hι's : ι' ≫ ((Over.pullback (jK V₁)).obj G).hom = A₁.A.hom ≫ spMap fK := hfst.1.lift_snd _ _ _
  have hι' : IsGrpPullback A₁.A ((Over.pullback (jK V₁)).obj G) (spMap fK) ι' :=
    IsGrpPullback.cancel hfst (hgβ.congr hbase hι'f.symm) hι's
  let ι : A₁.A.left ⟶ A.A.left := ι' ≫ gen.hom.left
  have hι : IsGrpPullback A₁.A A.A (spMap fK) ι :=
    (hι'.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  have hα' : IsGrpPullback A₁.A F.univ.A (spMap fK ≫ y₁) (ι ≫ α) := hι.comp hα

  obtain ⟨ι₂, hι₂⟩ : ∃ m, IsSquare ι m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι.1.w⟩
  obtain ⟨ι'₂, hι'₂⟩ : ∃ m, IsSquare ι' m := ⟨_, GlobalTheory.LamPull.exists_isSquare hι'.1.w⟩
  obtain ⟨g₁₂, hg₁₂⟩ : ∃ m, IsSquare g₁ m := ⟨_, GlobalTheory.LamPull.exists_isSquare hg₁.1.w⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ m, IsSquare (G' := (Over.pullback (jK V₁)).obj G) (G := G) (pullback.fst G.hom (jK V₁)) m :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hfst.1.w⟩
  have sqc : ∀ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
      {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left},
      IsSquare ψ ψ₂ → IsSquare φ φ₂ → IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := fun h' h =>
    ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
      by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩
  have hsq' := sqc hι₂ hsq
  have e₂ := GlobalTheory.LamPull.isSquare_unique (sqc hg₁₂ hβ₂) (hι'f ▸ sqc hι'₂ hκ₂)

  have hPPlb : PP.IsLB := hPP.1
  have hA₁L : LBIso A₁.L (U₁.LG.L.pull g₁) := by
    have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact LBIso.chartPull (h := U₁.gen.inv.left) (chartPullSec A₁.L _ _ hgi)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G₁.hom (jK R')) _ _ fun _ => rfl) U₁.ext
  have lamLB : ∀ {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] {M : LB X.left}, M.IsLB →
      (abelian₂ X M).IsLB := fun X _ _ M hM => DVR.linComb_isLB M hM _ _
  have s1 := GlobalTheory.LamPull.lbIso_lam_pull hg₁ U₁.LG.isLB A₁.isLB hA₁L hg₁₂
  have s2 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hPβ g₁₂
  rw [e₂] at s2
  have s3 := (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPPlb κ₂)) ι'₂).symm
  have s4 := hPP.2 κ₂ hκ₂
  have s5 := (GlobalTheory.RigidBundleGlue.LBIso.pull s4 ι'₂).symm
  have hιL : LBIso (A.L.pull ι) ((A.L.pull gen.hom.left).pull ι') :=
    (GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl hLgen) ι').symm
  have s6 := (GlobalTheory.LamPull.lbIso_lam_pull hι' hLgen (pull_isLB A.isLB ι) hιL hι'₂).symm
  have s7 := GlobalTheory.LamPull.lbIso_lam_pull hι A.isLB (pull_isLB A.isLB ι)
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB ι)) hι₂
  have s8 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull hL ι₂
  have t1 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ U₁.LG.isLB) _) (pull_isLB hPPlb _) s1 s2
  have t2 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB hPPlb _) (pull_isLB (pull_isLB hPPlb _) _) t1 s3
  have t3 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (pull_isLB hPPlb _) _) (pull_isLB (lamLB _ hLgen) _) t2 s5
  have t4 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ hLgen) _) (lamLB _ (pull_isLB A.isLB ι)) t3 s6
  have t5 := LBIso.trans (lamLB _ A₁.isLB) (lamLB _ (pull_isLB A.isLB ι)) (pull_isLB (lamLB _ A.isLB) _) t4 s7
  have t6 := LBIso.trans (lamLB _ A₁.isLB) (pull_isLB (lamLB _ A.isLB) _) (pull_isLB F.univ.isLB _) t5 s8
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap ρ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap ρ) G hG)
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, fK, hR', hinj, hloc, hfin, hfK, G₁, inferInstance,
    inferInstance, D₁, A₁, U₁, ι ≫ α, _, hG₁, hα', hsq', t6⟩

end GlobalTheory.PoincUnif
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), Extends TF.X Z Y.U la := by
  first | exact @GlobalTheory.CompHS.cusp_extends_comp | exact GlobalTheory.CompHS.cusp_extends_comp | (intros; apply GlobalTheory.CompHS.cusp_extends_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFormalAssemble

theorem siegPB_id_of_tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) := by
  intro g n B _ ζ R _ _ I hI s s' c c' t ce φ ψ β hc hφ hψ hβφ hβψ
  have H := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms
  have hp : GlobalTheory.AbLaw.IsProjBy c.A.hom :=
    GlobalTheory.WtTower.isProjBy_of_relAmple c.A (pull_isLB c.isLB _) hc.1
  obtain ⟨G, hG, hGφ, -, -, hGP⟩ := GlobalTheory.AlgUniq.exists_iso_algebraisation H R I hI (fun e => (ce e).A) β c.A c'.A
    c.ab c'.ab hp φ ψ (fun e => (hφ e).1) hβφ (fun e => (hψ e).1) hβψ
  choose b₂ hb₂ hb₂P using fun e => (hφ e).2.1
  choose b₂' hb₂' hb₂'P using fun e => (hψ e).2.1
  have hP := hGP c.P c'.P b₂ b₂' c.isLB c'.isLB hb₂ hb₂' fun e =>
    LBIso.trans (pull_isLB c.isLB _) (ce e).isLB (pull_isLB c'.isLB _) (LBIso.symm (hb₂P e)) (hb₂'P e)
  refine ⟨G.hom.left, (G.hom ⊗ₘ G.hom).left, isGrpPullback_of_iso G, ⟨?_, ?_⟩, hP, fun a => ?_⟩
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
  · have : IsProper c'.A.hom := c'.ab.proper
    have : IsProper (𝟙_ (Over (Sp R))).hom := show IsProper (𝟙 _) from inferInstance
    have key : c.lev a ≫ G.hom = c'.lev a := by
      refine GlobalTheory.Published.FormalAlgebraisation.Morphisms.hom_ext H hI fun e => ?_
      have hw : pullback.fst (𝟙_ (Over (Sp R))).hom (Out.thick R I e) =
          pullback.snd (𝟙_ (Over (Sp R))).hom (Out.thick R I e) ≫ Out.thick R I e := by
        rw [← pullback.condition]; exact (Category.comp_id _).symm
      have l1 := (hφ e).2.2 a
      have l2 := (hψ e).2.2 a
      simp only [pow_one] at l1 l2
      rw [hw, Over.comp_left, Category.assoc, Category.assoc, ← reassoc_of% l1, ← l2, ← hGφ e]
    rw [Category.id_comp, ← key, Over.comp_left]

end GlobalTheory.SiegFormalAssemble
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ N : Near (spMap ρ) G', N.Law ∧ ∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS U' a
  obtain ⟨H, hH, hall, hc, horb⟩ := GlobalTheory.T.exists_galois_invariant_nbhd_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a
  obtain ⟨X, π, hX, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_galois_quotient_invariant_open R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb
  obtain ⟨N, hN⟩ := GlobalTheory.T.glue_local_descents_near_closedFibre_galois R hR R' ρ hF hG D D' hD A' G' hS U' a H hH hall hc X π hX h1 h2 h3 h4 h5
    (GlobalTheory.T.galoisQuotient_smooth_baseChange_iso_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb X π hX h1 h2 h3 h4 h5)
  exact ⟨N, GlobalTheory.T.groupLaw_descends_galois_invariant_open R hR R' ρ hF hG D D' hD A' G' hS U' a N hN, hN⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ t₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ s₀ := by
  first | (exact @GlobalTheory.ESValT.extend_source) | (exact GlobalTheory.ESValT.extend_source) | (intros; apply GlobalTheory.ESValT.extend_source <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.AbVarDieu

variable {p : ℕ} [Fact p.Prime]

theorem pow_comp_hom {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_eq_ppow_smul (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B : AbVar k} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B)
    (n : ℕ) (h : ∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') : ∃ f' : A ⟶ B, f = p ^ n • f' := by
  obtain ⟨g, hg⟩ := (GlobalTheory.T.dieudonne_integrality_and_faithful p T k G H (t.map t' f.hom)).1 n h
  exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A B G H t t' f).1 n g hg

theorem map_nsmul_id {k : Type} [Field k] {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X) (N : ℕ) :
    t.map t ((N • 𝟙 A : A ⟶ A).hom) = (N : ℤ_[p]) • 𝟙 G := by
  have : IsMonHom (𝟙 A.X ^ N) := inferInstanceAs (IsMonHom ((N • 𝟙 A : A ⟶ A).hom))
  exact t.map_pow_id N

theorem tmap_comp (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H K : PDivGroup p k}
    (f : G ⟶ H) (g : H ⟶ K) (y : T.M K) : T.map (f ≫ g) y = T.map f (T.map g y) := by
  have := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H K trivial trivial trivial).2.1 f g
  exact LinearMap.congr_fun this y

theorem tmap_ppow_smul_id (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p] {H : PDivGroup p k}
    (a : ℕ) (y : T.M H) : T.map ((p : ℤ_[p]) ^ a • 𝟙 H) y = p ^ a • y := by
  have h := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k H H H trivial trivial trivial
  have h5 := h.2.2.2.2.1 a (𝟙 H) y
  have h1 := h.1
  change T.base.map trivial trivial _ y = _
  rw [h5, h1]
  rfl

theorem exists_ppow_quasiInverse {k : Type} [Field k] [CharP k p] {A B : AbVar k} (f : A ⟶ B)
    (hf : IsIsogeny f) (e : ℕ) (hdeg : deg f = p ^ e) :
    ∃ (a : ℕ) (f₁ : B ⟶ A), f ≫ f₁ = p ^ a • 𝟙 A ∧ f₁ ≫ f = p ^ a • 𝟙 B := by
  obtain ⟨N, f', hN, -, e1, e2⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p (Fact.out : p.Prime).ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hpm (dvd_zero p))
  have hmk : (m : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hcop : Nat.Coprime m (deg f) := by
    rw [hdeg]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm).symm
  obtain ⟨f₁, hf₁⟩ := exists_nsmul_eq_of_kills_torsion k B A f' m hmk (fun y hy => by
    apply GlobalTheory.AV.KerInv.eq_one_of_coprime f hf m hm0 hcop (y ≫ f'.hom)
    · rw [Category.assoc, ← comp_hom, e2, nsmul_hom, id_hom, comp_id_pow_eq, pow_mul', hy, one_pow]
    · rw [← pow_comp_hom, hy, MonObj.one_comp])
  have hmz : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm0.ne'
  refine ⟨a, f₁, ?_, ?_⟩
  · refine sub_eq_zero.1 (hom_torsionFree k A A (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hf₁, e1, smul_smul, mul_comm]
    exact sub_self _
  · refine sub_eq_zero.1 (hom_torsionFree k B B (m : ℤ) _ hmz ?_)
    rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.nsmul_comp, ← hf₁, e2, smul_smul, mul_comm]
    exact sub_self _

theorem exists_factor_of_range_le (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {A B C : AbVar k} {G H K : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X)
    (t'' : K.TorsionTower C.X) (f : A ⟶ B) (g : A ⟶ C) (e : ℕ) (hf : IsIsogeny f) (hdeg : deg f = p ^ e)
    (hr : LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom))) :
    ∃ u : B ⟶ C, f ≫ u = g := by
  obtain ⟨a, f₁, h1, h2⟩ := exists_ppow_quasiInverse f hf e hdeg
  have hdiv : ∀ x, ∃ x', T.map (t'.map t'' (f₁ ≫ g).hom) x = p ^ a • x' := by
    intro x
    obtain ⟨y, hy⟩ := hr (LinearMap.mem_range_self _ x)
    refine ⟨y, ?_⟩
    have c1 : t'.map t'' (f₁ ≫ g).hom = t'.map t f₁.hom ≫ t.map t'' g.hom :=
      (t'.map_congr t'' (comp_hom f₁ g)).trans (t'.map_comp t t'' _ _)
    have c2 : t'.map t f₁.hom ≫ t.map t' f.hom = (p : ℤ_[p]) ^ a • 𝟙 H := by
      rw [← t'.map_comp t t', ← Nat.cast_pow, ← map_nsmul_id t']
      exact t'.map_congr t' ((comp_hom f₁ f).symm.trans (congrArg Hom.hom h2))
    rw [c1, tmap_comp, ← hy, ← tmap_comp, c2, tmap_ppow_smul_id]
  obtain ⟨u, hu⟩ := exists_eq_ppow_smul T t' t'' (f₁ ≫ g) a hdiv
  refine ⟨u, sub_eq_zero.1 (hom_torsionFree k A C ((p ^ a : ℕ) : ℤ) _ (by exact_mod_cast (pow_pos (Fact.out : p.Prime).pos a).ne') ?_)⟩
  rw [smul_sub, natCast_zsmul, natCast_zsmul, ← Preadditive.comp_nsmul, ← hu, ← Category.assoc, h1,
    Preadditive.nsmul_comp, Category.id_comp]
  exact sub_self _

theorem abVar_dieudonne_integral_length_factor : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ n : ℕ, (∀ m, ∃ m', T.map (t.map t' f.hom) m = p ^ n • m') → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (IsIsogeny f → IsIsog (t.map t' f.hom) ∧ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map (t.map t' f.hom))) = padicValNat p (deg f)) ∧ ∀ (C : AbVar k) (K : PDivGroup p k) (t'' : K.TorsionTower C.X) (g : A ⟶ C) (e : ℕ), IsIsogeny f → deg f = p ^ e → LinearMap.range (T.map (t.map t'' g.hom)) ≤ LinearMap.range (T.map (t.map t' f.hom)) → ∃ u : B ⟶ C, f ≫ u = g := by
  intro p _ T k _ _ _ A B G H t t' f
  refine ⟨fun n h => exists_eq_ppow_smul T t t' f n h, fun hf => ?_,
    fun C K t'' g e hf hdeg hr => exists_factor_of_range_le T t t' t'' f g e hf hdeg hr⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isogeny_induces_pDivisibleGroupIsogeny_pPartDegree p k A B G H t t' f hf
  exact ⟨h1, GlobalTheory.T.dieudonneColength_eq_log_degree p T k G H _ _ h1 h2⟩

end GlobalTheory.Dieu.AbVarDieu
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualInjPull

theorem smooth_of_dimLe {S : Scheme.{0}} {A C : Over S} (h : DimLe A C) {g : ℕ}
    (hA : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension g C.hom := by
  have h1 : SmoothOfRelativeDimension g (pullback.snd A.hom (𝟙 S)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom (𝟙 S)) hA
  have h2 := h g S (𝟙 S) h1
  have sq : IsPullback (inv (pullback.fst C.hom (𝟙 S))) C.hom (pullback.snd C.hom (𝟙 S)) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [IsIso.inv_comp_eq, Category.comp_id, pullback.condition, Category.comp_id]⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h2

theorem isIso_of_mono' {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B)
    (hB' : IsAbelianScheme B') {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    (hg' : SmoothOfRelativeDimension g B'.hom) (x : B ⟶ B') [Mono x] : IsIso x := by
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    GlobalTheory.AbMonoIsoAny.isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem evc_of_iso {S : Scheme.{0}} {A T X U Y : Over S} {M : LB (A ⊗ T).left} {N : LB (X ⊗ U).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : A ⊗ T ⟶ X) (g : A ⊗ T ⟶ U) (e : LBIso M (ev N f g))
    (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN (lift a t ≫ f) (lift a t ≫ g) := by
  have c : cls M hM = cls _ (pull_isLB hN _) := (cls_eq_iff hM (pull_isLB hN _)).2 e
  rw [← evc_ev hN f g (pull_isLB hN _) a t, evc, evc, c]

theorem triv_of_triv_pull : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  intro K _ _ A A' B _ _ _ g P P' q hA hA' hB hgA' hgB hD hq hP' haP' eP T M hM haM hT
  obtain ⟨C, _, Q, hC, hdim, hQ⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare _ A' hA'
  have hgC : SmoothOfRelativeDimension g C.hom := smooth_of_dimLe hdim hgA'
  have hP := hD.isLB
  have hQl := hQ.isLB
  have hR : (ev Q (fst A C ≫ q) (snd A C)).IsLB := pull_isLB hQl _
  have haR : IsAdditive (ev Q (fst A C ≫ q) (snd A C)) := by
    refine (isAdditive_iff hR).2 fun Y a a' t ↦ ?_
    rw [evc_ev hQl, evc_ev hQl, evc_ev hQl]
    simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
    exact (isAdditive_iff hQl).1 hQ.additive Y _ _ t
  obtain ⟨s, hs, -⟩ := hQ.univ B P' hP' haP'
  obtain ⟨r, hr, -⟩ := hD.univ C _ hR haR
  have hsr : s ≫ r = 𝟙 B := by
    refine GlobalTheory.AbDual.IsDual.eq_of_evc hD ?_
    have e1 := evc_of_iso hR hP _ _ hr (fst A B) (snd A B ≫ s)
    have e1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A B) (snd A B ≫ s)
    have e2 := evc_of_iso hP' hQl _ _ hs (fst A B ≫ q) (snd A B)
    have e3 : evc hP' (fst A B ≫ q) (snd A B) = evc hP (fst A B) (snd A B) := by
      rw [← cls_ev hP' _ _ (pull_isLB hP' _), (cls_eq_iff _ hP).2 eP, evc, lift_fst_snd, Over.id_left, pull_id]
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at e1 e1' e2
    rw [Category.comp_id, ← e3, e2, ← e1', e1]
  obtain ⟨c, hc, -⟩ := hQ.univ T M hM haM
  have hcr : c ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ c)
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ c)
    have f2 := evc_of_iso hM hQl _ _ hc (fst A T ≫ q) (snd A T)
    have f3 := (triv_ev_iff hM _ _).1 hT
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1' f2
    rw [← f1, f1', ← f2, f3]))
  have h1r : (1 : T ⟶ C) ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ (1 : T ⟶ C))
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ (1 : T ⟶ C))
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1'
    rw [← f1, f1', MonObj.comp_one, evc_one_right hQl hQ.zero]))
  haveI : IsSplitMono s := IsSplitMono.mk' ⟨r, hsr⟩
  haveI : IsIso s := isIso_of_mono' hB hC hgB hgC s
  have hrinv : r = inv s := (IsIso.inv_eq_of_hom_inv_id hsr).symm
  haveI : IsIso r := by rw [hrinv]; infer_instance
  have hc1 : c = 1 := (cancel_mono r).1 (hcr.trans h1r.symm)
  refine (cls_eq_zero_iff hM).1 ?_
  rw [(cls_eq_iff hM (pull_isLB hQl _)).2 hc, cls_ev hQl, hc1, MonObj.comp_one, evc_one_right hQl hQ.zero]
end GlobalTheory.DualInjPull
end
end
