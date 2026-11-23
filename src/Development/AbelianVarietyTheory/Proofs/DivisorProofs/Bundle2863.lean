module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwistAV

open GlobalTheory.CechPic (cls pull)

section

variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G]

def genSec (a : 𝟙_ (Over (Sp R)) ⟶ G) : 𝟙_ (Over (Sp (FractionRing R))) ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by
    rw [Category.assoc, Over.w a]; simp)) (pullback.lift_snd _ _ _)

theorem genSec_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (genSec a).left ≫ pullback.fst G.hom (jK R) = jK R ≫ a.left :=
  pullback.lift_fst _ _ _

theorem const_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (toUnit ((Over.pullback (jK R)).obj G) ≫ genSec a).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ G.hom ≫ a.left := by
  rw [Over.comp_left, Category.assoc, genSec_fst, ← Category.assoc (pullback.fst G.hom (jK R)), pullback.condition]
  rfl

theorem hom_ext_gen {T : Over (Sp (FractionRing R))} {x y : T ⟶ (Over.pullback (jK R)).obj G}
    (h : x.left ≫ pullback.fst G.hom (jK R) = y.left ≫ pullback.fst G.hom (jK R)) : x = y :=
  Over.OverMorphism.ext ((isGrpPullback_pullback G (jK R)).1.hom_ext h (by
    show x.left ≫ ((Over.pullback (jK R)).obj G).hom = y.left ≫ ((Over.pullback (jK R)).obj G).hom
    rw [Over.w, Over.w]))

theorem genSec_sq (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) :
    genSec a * genSec a = η[(Over.pullback (jK R)).obj G] := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let T : Over (Sp (FractionRing R)) := 𝟙_ _
  let x₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ a
  have hx : x₀.left = (genSec a).left ≫ pullback.fst G.hom (jK R) := by
    rw [genSec_fst]; rfl
  have e := hp T (genSec a) (genSec a) x₀ x₀ hx hx
  have haa : x₀ * x₀ = toUnit _ ≫ η[G] := by
    rw [← MonObj.comp_mul, ← sq, ha, Hom.one_def, ← Category.assoc, comp_toUnit]
  set c := genSec a * genSec a with hc
  let y₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ η[G]
  have hy : y₀.left = c.left ≫ pullback.fst G.hom (jK R) := by rw [show y₀ = x₀ * x₀ from haa.symm, e]
  have e₂ := hp T c c y₀ y₀ hy hy
  have hyy : y₀ * y₀ = y₀ := by
    rw [show y₀ = 1 from Hom.one_def.symm, _root_.one_mul]
  have hcc : c * c = c := hom_ext_gen (by rw [← e₂, hyy, hy])
  exact mul_eq_left.1 hcc

theorem transl_fst [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (GlobalTheory.PolTranslate.transl (genSec a)).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let GK := (Over.pullback (jK R)).obj G
  let p : Over.mk (GK.hom ≫ jK R) ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
  have e := hp GK (𝟙 GK) (toUnit GK ≫ genSec a) p (p ≫ toUnit G ≫ a) (by simp [p])
    (by rw [const_fst]; rfl)
  have e' : p * (p ≫ toUnit G ≫ a) = p ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [MonObj.comp_mul, Category.comp_id, _root_.mul_comm]
  rw [e', Over.comp_left] at e
  exact e.symm

end

theorem exists_translate_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D A G _ _ _ U a ha P hP
  haveI := U.gen_hom
  haveI := A.isAb.comm
  haveI : IsProper A.A.hom := A.isAb.proper
  let b := genSec a
  let a' : 𝟙_ (Over (Sp (FractionRing R))) ⟶ A.A := b ≫ U.gen.hom
  have ha' : a' * a' = 1 := by
    show (b ≫ U.gen.hom) * (b ≫ U.gen.hom) = 1
    rw [← MonObj.mul_comp, genSec_sq a ha]
    exact IsMonHom.one_hom U.gen.hom
  let A₂ : PolAV (Sp (FractionRing R)) :=
    { A := A.A
      isAb := A.isAb
      g := A.g
      smoothDim := A.smoothDim
      L := GlobalTheory.RigidTranslate.rigTransl A.L a'
      isLB := LB.isLB_linComb A.isLB _ _
      rigid := GlobalTheory.RigidTranslate.rigidified_rigTransl A.isLB
      sym := GlobalTheory.RigidTranslate.sym_rigTransl ha' A.isLB A.sym
      ample := GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section a' A.isLB A.ample
      ktriv := GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ _ _ A.isLB a' A.ktriv }
  refine ⟨A₂, U.gen, U.gen_hom, ?_⟩
  let f := pullback.fst G.hom (jK R)
  let τ := ((toUnit G ≫ a) * 𝟙 G).left
  have hLG := U.LG.isLB
  have hext : pull U.gen.hom.left (cls A.L A.isLB) = pull f (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB A.isLB _) (pull_isLB hLG _)).2 U.ext
  have hP' : cls P.L.L P.L.isLB = pull τ (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff P.L.isLB (pull_isLB hLG _)).2 hP
  have hrig : pull (eSec G) (cls P.L.L P.L.isLB) = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB P.L.isLB _)).2 ⟨P.L.rig, P.L.rigGen⟩
  have ea : a.left = eSec G ≫ τ := by
    show a.left = (η[G] ≫ ((toUnit G ≫ a) * 𝟙 G)).left
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id,
      h1, _root_.mul_one]
  have hgt : U.gen.hom.left ≫ (GlobalTheory.PolTranslate.transl a').left =
      (GlobalTheory.PolTranslate.transl b).left ≫ U.gen.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PolTranslate.comp_transl, GlobalTheory.PolTranslate.transl, MonObj.mul_comp,
      Category.id_comp]
    rfl
  have hgc : U.gen.hom.left ≫ (toUnit A.A ≫ a').left = (toUnit _ ≫ b).left ≫ U.gen.hom.left := by
    rw [GlobalTheory.RigidTranslate.comp_const, ← Over.comp_left]
    rfl
  have h₁ := pull_isLB (LB.isLB_linComb A.isLB (K := Fin 2)
    ![(GlobalTheory.PolTranslate.transl a').left, (toUnit A.A ≫ a').left] ![1, -1]) U.gen.hom.left
  refine (GlobalTheory.CechPic.cls_eq_iff h₁ (pull_isLB P.L.isLB _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull _ _ h₁, GlobalTheory.CechPic.cls_linComb A.isLB, GlobalTheory.CechPic.cls_pull P.L.isLB]
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg, map_sub]
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, hgt, hgc, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_comp, hext,
      ← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, transl_fst a, const_fst a, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp f, GlobalTheory.CechPic.pull_comp, ea, GlobalTheory.CechPic.pull_comp, ← hP', hrig, map_zero, map_zero, sub_zero]
  · exact LB.isLB_linComb A.isLB _ _

end GlobalTheory.TwistAV
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.twistRatio_eq_one_at_unit : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X) (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) ae) (LB.pullGen D.P.L _ _ (gp.s χ) (thick R I e))) → ∀ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (J : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D.P.A.left) → D.P.L.ι) (J' : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val (g.t χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ h) z J * ((∏ k, gv w ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J (((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J' * val (gp.s χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = 1 := by
  intro R _ _ I D D₂ e G _ _ g g₂ β gp w χ₂ χ a h hh hf hcorr z J J' hJ hJ'
  set o := (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G) with ho
  have hom1 : o.left ≫ (thickObj R I e G).hom = 𝟙 _ := Over.w o
  have e1 : o.left ≫ h ≫ (thickObj R I e G).hom = 𝟙 _ := by rw [hh, hom1]
  have f1 : (Over.map (thick R I e)).map o ≫ fstG I e G = 1 := by
    have := GlobalTheory.FormalPoint.map_mul_fstG (R := R) (I := I) (e := e) (G := G) o o
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  let T := (Over.map (thick R I e)).obj (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))))
  have tu : (toUnit T).left = thick R I e := by
    have := Over.w (toUnit T)
    simpa [T] using this
  have e2 : o.left ≫ h ≫ (fstG I e G).left = thick R I e ≫ a.left := by
    rw [hf]
    show ((Over.map (thick R I e)).map o ≫ fstG I e G ≫ ((toUnit G ≫ a) * 𝟙 G)).left = _
    rw [← Category.assoc, f1, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, _root_.mul_one,
      Over.comp_left, tu]
  have hc := hcorr (o.left ≫ h) (by simpa [Category.assoc] using e1) (by simpa [Category.assoc] using e2)
  have va := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at va
  have vb : val (g₂.t χ₂) o.left z J' = 1 := GlobalTheory.TorusCoord.val_unit g₂ χ₂ hJ'
  let f : (_ ⟶ D₂.P.A.left) → _ := fun ψ => gv w ψ z (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ψ)
  have e0 : ∀ k, o.left ≫ D₂.Oφ g₂.pG χ₂ k = D₂.Oφ (1 : T ⟶ D₂.P.A) χ₂ k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R I e)).map o) g₂.pG χ₂ k).trans
      (congrArg (D₂.Oφ · χ₂ k) (GlobalTheory.TorusCoord.im_one g₂))
  have vc : (∏ k, f (o.left ≫ D₂.Oφ g₂.pG χ₂ k) ^ Oinvε k) = 1 := by
    refine (Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_
    rw [Fin.prod_univ_four]
    show f ((1 : T ⟶ D₂.P.A) * (toUnit T ≫ D₂.c χ₂)).left ^ (-1 : ℤ) * f (toUnit T ≫ D₂.c χ₂).left ^ (1 : ℤ) *
      f (1 : T ⟶ D₂.P.A).left ^ (1 : ℤ) * f (1 : T ⟶ D₂.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  have vc' : (∏ k, gv w (o.left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((o.left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (o.left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) = 1 := vc
  rw [vc', vb, ← Category.assoc, hom1, Category.id_comp, va, _root_.one_mul, _root_.one_mul, mul_inv_cancel]
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.Spread

theorem spread_fibre : ∀ (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (G : Over M.Z) [GrpObj G], IsSemiAbelian G → ∀ (R' : Subalgebra o Ω) (B : Over (Sp R')) [GrpObj B], IsSemiAbelian B → ∀ (A₀ : Over (Sp Ω)) [GrpObj A₀] (a' : A₀.left ⟶ B.left) (ψ : A₀.left ⟶ G.left), IsGrpPullback A₀ B (spMap R'.val.toRingHom) a' → IsGrpPullback A₀ G M.pt ψ → ∀ (K : Type) [Field K] (s : Sp K ⟶ M.Z), R' ≤ M.O (s (closedPoint K)) → ∀ (yK : R' →+* K), (∀ x : R', yK x = M.val s x) → ∀ (AK : Over (Sp K)) [GrpObj AK] (φK : AK.left ⟶ B.left), IsGrpPullback AK B (spMap yK) φK → ∃ Ψ : AK.left ⟶ G.left, IsGrpPullback AK G s Ψ ∧ (∀ (e : B ⟶ B) (F : G ⟶ G) (e₀ : A₀ ⟶ A₀), e₀.left ≫ a' = a' ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left → ∀ eK : AK ⟶ AK, eK.left ≫ φK = φK ≫ e.left → eK.left ≫ Ψ = Ψ ≫ F.left) ∧ ∀ (b : Sp R' ⟶ B.left) (gγ : Over.mk M.pt ⟶ G) (w : Sp Ω ⟶ A₀.left), b ≫ B.hom = 𝟙 _ → w ≫ A₀.hom = 𝟙 _ → w ≫ a' = spMap R'.val.toRingHom ≫ b → w ≫ ψ = gγ.left → ∀ (T : Scheme.{0}) (x : T ⟶ AK.left) (v : T ⟶ G.left), x ≫ φK = x ≫ AK.hom ≫ spMap yK ≫ b → ValAt gγ (x ≫ AK.hom ≫ s) v → x ≫ Ψ = v := by
  intro o Ω _ _ _ _ M hN G _ hG R' B _ hB A₀ _ a' ψ ha' hψ K _ s hR' yK hyK AK _ φK hφK
  set z := s (closedPoint K) with hz
  haveI : IsNoetherianRing (M.O z) := M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hN z

  let ιO : Sp (M.O z) ⟶ M.Z :=
    Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z
  have key : ∀ {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) (hy : y (closedPoint C) ⤳ z)
      (r : M.O z →+* C), r.comp (M.stalkEquiv z).toRingHom =
        (M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y).hom →
      spMap r ≫ ιO = y := by
    intro C _ _ y hy r hr
    have e : (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
        CommRingCat.ofHom r = M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y := by
      ext a
      exact congrArg (fun f : M.Z.presheaf.stalk z →+* C => f a) hr
    have e2 : spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) =
        Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hy) :=
      (Spec.map_comp _ _).symm.trans ((congrArg Spec.map e).trans (Spec.map_comp _ _))
    change spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z = y
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.Z.fromSpecStalk z) e2).trans
      ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hy)).trans ?_
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y
  have hpt : spMap (algebraMap (M.O z) Ω) ≫ ιO = M.pt :=
    key M.pt (M.pt_specializes _ z) _ (by ext a; rfl)
  let v : M.O z →+* K := RatModel.valLoc s z specializes_rfl
  have hs : spMap v ≫ ιO = s := key s specializes_rfl v (by ext a; simp [v, RatModel.valLoc])

  let ι' : R' →+* M.O z := (Subalgebra.inclusion hR').toRingHom
  have hyv : yK = v.comp ι' := by
    ext x
    rw [hyK x, RingHom.comp_apply]
    exact (RatModel.valLoc_eq_val s specializes_rfl (ι' x)).symm
  have spc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hyK' : spMap yK = spMap v ≫ spMap ι' := by rw [hyv, spc]
  have hval : spMap R'.val.toRingHom = spMap (algebraMap (M.O z) Ω) ≫ spMap ι' := by
    rw [← spc]; rfl

  let BO := (Over.pullback (spMap ι')).obj B
  let GO := (Over.pullback ιO).obj G
  have hBO : IsGrpPullback BO B (spMap ι') (pullback.fst _ _) := isGrpPullback_pullback B _
  have hGO : IsGrpPullback GO G ιO (pullback.fst _ _) := isGrpPullback_pullback G _
  have hBOs : IsSemiAbelian BO := IsSemiAbelian.pullback _ B hB
  have hGOs : IsSemiAbelian GO := IsSemiAbelian.pullback _ G hG
  let j := spMap (algebraMap (M.O z) Ω)
  let a₀ : A₀.left ⟶ BO.left := pullback.lift a' (A₀.hom ≫ j) (by
    rw [ha'.1.w, hval, Category.assoc])
  have ha₀ : a₀ ≫ pullback.fst _ _ = a' := pullback.lift_fst _ _ _
  have ha₀' : a₀ ≫ BO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀B : IsGrpPullback A₀ BO j a₀ :=
    hBO.cancel (ha'.congr hval ha₀.symm) ha₀'
  let ψ₀ : A₀.left ⟶ GO.left := pullback.lift ψ (A₀.hom ≫ j) (by
    rw [hψ.1.w, ← hpt, Category.assoc])
  have hψ₀ : ψ₀ ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hψ₀' : ψ₀ ≫ GO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀G : IsGrpPullback A₀ GO j ψ₀ :=
    hGO.cancel (hψ.congr hpt.symm hψ₀.symm) hψ₀'
  have hj : GlobalTheory.IsGenericPointHom j := GlobalTheory.IsGenericPointHom.fractionField (M.O z) Ω
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec (M.O z)) hj
    hBOs hGOs hA₀B hA₀G

  let φO : AK.left ⟶ BO.left := pullback.lift φK (AK.hom ≫ spMap v) (by
    rw [hφK.1.w, hyK', Category.assoc])
  have hφO : φO ≫ pullback.fst _ _ = φK := pullback.lift_fst _ _ _
  have hφO' : φO ≫ BO.hom = AK.hom ≫ spMap v := pullback.lift_snd _ _ _
  have hAKB : IsGrpPullback AK BO (spMap v) φO := hBO.cancel (hφK.congr hyK' hφO.symm) hφO'

  obtain ⟨-, hGsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨hBOf, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian BO hBOs
  obtain ⟨-, hGOsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian GO hGOs
  obtain ⟨hjq, hjd⟩ := hj.quasiCompact_and_dominant
  have hEw : E.hom.left ≫ GO.hom = BO.hom := Over.w E.hom
  refine ⟨φO ≫ E.hom.left ≫ pullback.fst _ _, ?_, ?_, ?_⟩
  · refine ((hAKB.comp (isGrpPullback_of_iso E)).comp hGO).congr ?_ ?_
    · rw [Category.comp_id, hs]
    · simp only [Category.assoc]
  · intro e F e₀ he₀a he₀ψ eK heK
    let eO := (Over.pullback (spMap ι')).map e
    let FO := (Over.pullback ιO).map F
    have heO : eO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e.left := pullback.lift_fst _ _ _
    have heO' : eO.left ≫ BO.hom = BO.hom := Over.w eO
    have hFO : FO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F.left := pullback.lift_fst _ _ _
    have hFO' : FO.left ≫ GO.hom = GO.hom := Over.w FO
    have h1 : e₀.left ≫ a₀ = a₀ ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, ha₀, Category.assoc, heO, ← Category.assoc, ha₀, he₀a]
      · change e₀.left ≫ a₀ ≫ BO.hom = a₀ ≫ eO.left ≫ BO.hom
        rw [heO', ha₀', ← Category.assoc, Over.w e₀]
    have h2 : e₀.left ≫ ψ₀ = ψ₀ ≫ FO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₀, Category.assoc, hFO, ← Category.assoc, hψ₀, he₀ψ]
      · change e₀.left ≫ ψ₀ ≫ GO.hom = ψ₀ ≫ FO.left ≫ GO.hom
        rw [hFO', hψ₀', ← Category.assoc, Over.w e₀]
    have h3 : eO ≫ E.hom = E.hom ≫ FO := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hA₀B.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← h1, Category.assoc, hE, ← Category.assoc, hE, h2]
    have h4 : eK.left ≫ φO = φO ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, Category.assoc, heO, ← Category.assoc, hφO, heK]
      · change eK.left ≫ φO ≫ BO.hom = φO ≫ eO.left ≫ BO.hom
        rw [heO', hφO', ← Category.assoc, Over.w eK]
    have h5 := congrArg (fun f => f.left ≫ pullback.fst G.hom ιO) h3
    simp only [Over.comp_left, Category.assoc, hFO] at h5
    rw [← Category.assoc, h4, Category.assoc, h5]
    simp only [Category.assoc]
  · intro b gγ w hb hw hwa hwψ T x vv hx hv
    by_cases hT : IsEmpty T
    · exact (isInitialOfIsEmpty (X := T)).hom_ext _ _
    obtain ⟨t₀⟩ := not_isEmpty_iff.1 hT
    obtain ⟨W, h, s', ⟨h1, h2⟩, hs', rfl⟩ := id hv
    have hzpt : (x ≫ AK.hom ≫ s) t₀ = z := by
      simp only [Scheme.Hom.comp_apply]
      exact congrArg s (Subsingleton.elim _ _)
    have hzW : z ∈ W := by rw [← hzpt, ← hs']; exact (s' t₀).2
    have hr : Set.range ιO ⊆ Set.range W.ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hp : ιO p ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.range_fromSpecStalk] at hp
      exact Specializes.mem_open hp W.isOpen hzW
    let ℓ := IsOpenImmersion.lift W.ι ιO hr
    have hℓ : ℓ ≫ W.ι = ιO := IsOpenImmersion.lift_fac _ _ _
    let bO : Sp (M.O z) ⟶ BO.left := pullback.lift (spMap ι' ≫ b) (𝟙 _) (by
      rw [Category.assoc, hb, Category.comp_id, Category.id_comp])
    have hbO : bO ≫ pullback.fst _ _ = spMap ι' ≫ b := pullback.lift_fst _ _ _
    have hbO' : bO ≫ BO.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hEG : E.hom.left ≫ pullback.fst G.hom ιO ≫ G.hom = BO.hom ≫ ιO := by
      rw [pullback.condition, ← Category.assoc, ← hEw]; rfl
    have hσ : bO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ℓ ≫ h := by
      refine ext_of_isDominant_of_isSeparated G.hom ?_ j ?_
      · rw [Category.assoc, Category.assoc, hEG, ← Category.assoc, hbO', Category.id_comp, Category.assoc, h1, hℓ]
      · have hjb : j ≫ bO = w ≫ a₀ := by
          apply pullback.hom_ext
          · rw [Category.assoc, hbO, Category.assoc, ha₀, hwa, hval, Category.assoc]
          · change j ≫ bO ≫ BO.hom = w ≫ a₀ ≫ BO.hom
            rw [hbO', ha₀', ← Category.assoc, hw, Category.comp_id, Category.id_comp]
        rw [← Category.assoc, hjb, Category.assoc, ← Category.assoc a₀, hE, hψ₀, hwψ, ← Category.assoc]
        exact (h2 _ (by rw [Category.assoc, hℓ]; exact hpt)).symm
    have hxb : x ≫ φO = (x ≫ AK.hom ≫ spMap v) ≫ bO := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, hx, Category.assoc, hbO, hyK']
        simp only [Category.assoc]
      · change x ≫ φO ≫ BO.hom = (x ≫ AK.hom ≫ spMap v) ≫ bO ≫ BO.hom
        rw [hφO', hbO', Category.comp_id]
    refine ValAt.unique ?_ hv
    refine ⟨W, h, (x ≫ AK.hom ≫ spMap v) ≫ ℓ, ⟨h1, h2⟩, ?_, ?_⟩
    · rw [Category.assoc, hℓ]
      simp only [Category.assoc, hs]
    · have hxb' : x ≫ φO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ((x ≫ AK.hom ≫ spMap v) ≫ ℓ) ≫ h := by
        rw [← Category.assoc x φO, hxb, Category.assoc, hσ]
        simp only [Category.assoc]
      simpa only [Category.assoc] using hxb'.symm

end GlobalTheory.Poinc.Spread
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

theorem smul_eighth_power_diag : ∀ (X₀ X : Type) [AddCommGroup X₀] [AddCommGroup X] (K : (Fin 8 → X₀) ≃+ (Fin 8 → X)), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) → ∃ k : X₀ ≃+ X, ∀ mu, K mu = fun u => k (mu u) := by
  intro X₀ X _ _ K hK
  have hsel : ∀ (Y : Type) [AddCommGroup Y] (w : Fin 8) (nu : Fin 8 → Y),
      (fun u : Fin 8 => ∑ v, (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) u v • nu v)
        = fun _ => nu w := by
    intro Y _ w nu
    funext u
    simp [Matrix.of_apply]
  have hc : ∀ (mu : Fin 8 → X₀) (w : Fin 8), K (fun _ => mu w) = fun _ => K mu w := by
    intro mu w
    have h := hK (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) mu
    rw [hsel, hsel] at h
    exact h
  let f : X₀ →+ X :=
    { toFun := fun x => K (fun _ => x) 0
      map_zero' := by
        show K 0 0 = 0
        simp
      map_add' := by
        intro x y
        show K ((fun _ => x) + (fun _ => y)) 0 = _
        rw [map_add (f := _)]
        rfl }
  have hform : ∀ (mu : Fin 8 → X₀) (u : Fin 8), K mu u = f (mu u) := by
    intro mu u
    show K mu u = K (fun _ => mu u) 0
    rw [hc]
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h1 : K (fun _ => x) = 0 := by
      funext u
      rw [hform]
      exact hx
    have h2 : (fun _ : Fin 8 => x) = 0 := K.injective (h1.trans (map_zero K).symm)
    exact congrFun h2 0
  have surj : Function.Surjective f := by
    intro y
    refine ⟨K.symm (fun _ => y) 0, ?_⟩
    have h := hform (K.symm fun _ => y) 0
    rw [← h]
    simp
  refine ⟨AddEquiv.ofBijective f ⟨inj, surj⟩, fun mu => funext fun u => ?_⟩
  exact hform mu u

end GlobalTheory
end
