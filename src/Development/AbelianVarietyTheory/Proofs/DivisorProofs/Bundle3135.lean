module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.Mum.EFixCube

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cube_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J →
    ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre J D A G), IsSemiAbelian G → ∀ (x y x' y' : G ⟶ G) (cx cy cx' cy' : A.A ⟶ A.A),
    Gen₀ U U x cx → Gen₀ U U y cy → Gen₀ U U x' cx' → Gen₀ U U y' cy' →
    LBIso (cubeLB A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] A.L) (cubeLB A.A ![fst A.A A.A ≫ cx', snd A.A A.A ≫ cy'] A.L) →
    LBIso (cubeLB G ![fst G G ≫ x, snd G G ≫ y] U.LG.L) (cubeLB G ![fst G G ≫ x', snd G G ≫ y'] U.LG.L) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ hS x₁ y₁ x₂ y₂ cx₁ cy₁ cx₂ cy₂ hx₁ hy₁ hx₂ hy₂ hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ (x y : G₁ ⟶ G₁) (cx cy : A₁.A ⟶ A₁.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G₁ ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U₁.LG.L U₁.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A₁.L A₁.isLB))) := by
    intro x y cx cy hx hy
    have hL := U₁.LG.isLB
    have hA := A₁.isLB
    have hgen := U₁.gen_hom
    have hc' : CechPic.pull (pullback.fst G₁.hom (jK R)) (cls U₁.LG.L hL) =
        CechPic.pull U₁.gen.hom.left (cls A₁.L hA) := by
      obtain ⟨w, hw⟩ := U₁.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G₁ (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hA₁ := A₁.isLB
  have l₁ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₁, snd G₁ G₁ ≫ y₁] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have l₂ : (cubeLB G₁ ![fst G₁ G₁ ≫ x₂, snd G₁ G₁ ≫ y₂] U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have m₁ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have m₂ : (cubeLB A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₁, snd A₁.A A₁.A ≫ cy₁] (cls _ hA₁) =
      cubeCls A₁.A ![fst A₁.A A₁.A ≫ cx₂, snd A₁.A A₁.A ≫ cy₂] (cls _ hA₁) :=
    (cls_cubeLB _ _ hA₁).symm.trans (((cls_eq_iff m₁ m₂).2 hA).trans (cls_cubeLB _ _ hA₁))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ l₁ l₂ ?_
  refine (cls_eq_iff (pull_isLB l₁ _) (pull_isLB l₂ _)).1 ?_
  rw [cls_pull l₁ _ (pull_isLB l₁ _), cls_pull l₂ _ (pull_isLB l₂ _), cls_cubeLB _ _ hL₁, cls_cubeLB _ _ hL₁,
    key x₁ y₁ cx₁ cy₁ hx₁ hy₁, key x₂ y₂ cx₂ cy₂ hx₂ hy₂, eA]

theorem cube_adj_of_oLinear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G), IsSemiAbelian G → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → ∀ a : O,
    LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ U hS O _ _ _ ιD ιA ιG hl a
  have g₁ : Gen₀ U U (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hA := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local (FractionRing R) A.A A.L (ιA.act a) (ιA.act (star a)) A.isLB (ιA.rosati a)
  have := lbIso_cube_of_generic R _ hR D A G U hS (ιG.act a) (𝟙 G) (𝟙 G) (ιG.act (star a)) (ιA.act a) (𝟙 A.A) (𝟙 A.A)
    (ιA.act (star a)) (hl.ext a) g₁ g₁ (hl.ext (star a)) (by simpa only [Category.comp_id] using hA)
  simpa only [Category.comp_id] using this

end GlobalTheory.Mum.EFixCube
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_lam_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → ∀ (a : G₁ ⟶ G₂) (cA : A₁.A ⟶ A₂.A), IsMonHom a → IsMonHom cA → Gen₀ U₁ U₂ a cA → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left) → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) := by
  intro R _ _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hS a cA ha hcA hgen hA
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G₁ G₁
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G₁ G₁
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ {D : DegData R J} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre J D A G) (x y : G₁ ⟶ G) (cx cy : A₁.A ⟶ A.A), Gen₀ U₁ U x cx → Gen₀ U₁ U y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U.LG.L U.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A.L A.isLB))) := by
    intro D A G _ _ U x y cx cy hx hy
    have hL := U.LG.isLB
    have hA := A.isLB
    have hgen := U.gen_hom
    have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hA₁ := A₁.isLB
  have hA₂ := A₂.isLB
  have lG₁ : (abelian₂ G₁ U₁.LG.L).IsLB := LB.isLB_linComb hL₁ _ _
  have lG₂ : (abelian₂ G₂ U₂.LG.L).IsLB := LB.isLB_linComb hL₂ _ _
  have lA₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb hA₁ _ _
  have lA₂ : (abelian₂ A₂.A A₂.L).IsLB := LB.isLB_linComb hA₂ _ _
  have g₁ : Gen₀ U₁ U₁ (𝟙 G₁) (𝟙 A₁.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have cG₁ : cls (abelian₂ G₁ U₁.LG.L) lG₁ = cubeCls G₁ ![fst G₁ G₁ ≫ 𝟙 G₁, snd G₁ G₁ ≫ 𝟙 G₁] (cls _ hL₁) := by
    refine (cls_cubeLB G₁ (x2 G₁) hL₁).trans ?_
    congr 1
  have cA₁ : cls (abelian₂ A₁.A A₁.L) lA₁ = cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) := by
    refine (cls_cubeLB A₁.A (x2 A₁.A) hA₁).trans ?_
    congr 1
  have cG₂ : cls ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ a) (snd G₁ G₁ ≫ a) : G2 G₁ ⟶ G2 G₂).left) (pull_isLB lG₂ _) =
      cubeCls G₂ ![fst G₁ G₁ ≫ a, snd G₁ G₁ ≫ a] (cls _ hL₂) := by
    rw [cls_pull lG₂ _ (pull_isLB lG₂ _)]
    refine (congrArg _ (cls_cubeLB G₂ (x2 G₂) hL₂)).trans ?_
    exact pull_cubeCls G₂ _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have cA₂ : cls ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA) (snd A₁.A A₁.A ≫ cA) : G2 A₁.A ⟶ G2 A₂.A).left)
      (pull_isLB lA₂ _) = cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) := by
    rw [cls_pull lA₂ _ (pull_isLB lA₂ _)]
    refine (congrArg _ (cls_cubeLB A₂.A (x2 A₂.A) hA₂)).trans ?_
    exact pull_cubeCls A₂.A _ _ _ (fun i => by fin_cases i <;> simp [x2]) _
  have eA : cubeCls A₁.A ![fst A₁.A A₁.A ≫ 𝟙 A₁.A, snd A₁.A A₁.A ≫ 𝟙 A₁.A] (cls _ hA₁) =
      cubeCls A₂.A ![fst A₁.A A₁.A ≫ cA, snd A₁.A A₁.A ≫ cA] (cls _ hA₂) :=
    cA₁.symm.trans (((cls_eq_iff lA₁ (pull_isLB lA₂ _)).2 hA).trans cA₂)
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G₁ ⊗ G₁) (η[G₁ ⊗ G₁]).left (Over.w _) _ _ lG₁ (pull_isLB lG₂ _) ?_
  refine (cls_eq_iff (pull_isLB lG₁ _) (pull_isLB (pull_isLB lG₂ _) _)).1 ?_
  rw [cls_pull lG₁ _ (pull_isLB lG₁ _), cls_pull (pull_isLB lG₂ _) _ (pull_isLB (pull_isLB lG₂ _) _), cG₁, cG₂,
    key U₁ (𝟙 G₁) (𝟙 G₁) (𝟙 A₁.A) (𝟙 A₁.A) g₁ g₁, key U₂ a a cA cA hgen hgen, eA]

end GlobalTheory.TInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.TInj

theorem torusHomOf_comp' {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem torusHomOf_id' {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem iso_lin_coord : ∀ (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂) (a : G₁ ≅ G₂), IsMonHom a.hom → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X ≃+ D₁.toPre.X), IsIso b ∧ Lin U₁ U₂ a.hom b h.toAddMonoidHom ∧ Coord U₁ U₂ a.hom b h.toAddMonoidHom := by
  intro R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ a ha
  have ha' : IsMonHom a.inv := inferInstance
  obtain ⟨b, hb, hbO⟩ := exists_abelian_hom R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨b', hb', hb'O⟩ := exists_abelian_hom R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  obtain ⟨h, hh⟩ := unifPre_hom_character_const R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨h', hh'⟩ := unifPre_hom_character_const R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  have oComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) c c',
      Over₀ Ua Ub f c → Over₀ Ub Ua g c' → Over₀ Ua Ua (f ≫ g) (c ≫ c') := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g c c' hf hg e
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg e, ← Category.assoc, hf e, Category.assoc]
  have tComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) k k',
      OnTorus Ua Ub f k → OnTorus Ub Ua g k' → OnTorus Ua Ua (f ≫ g) (fun χ => k (k' χ)) := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g k k' hf hg e
    obtain ⟨t, ht, hi⟩ := hf e
    obtain ⟨s, hs, hj⟩ := hg e
    refine ⟨t ≫ s, torusHomOf_comp' ht hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]
  have oId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), Over₀ Ua Ua (𝟙 Ga) (𝟙 _) := by
    intro Da Aa Ga _ _ Ua e
    simp
  have tId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), OnTorus Ua Ua (𝟙 Ga) (fun χ => χ) := by
    intro Da Aa Ga _ _ Ua e
    exact ⟨𝟙 _, torusHomOf_id' _, by simp⟩
  have u₁ := over₀_onTorus_unique R J hR D₁ D₁ A₁ A₁ G₁ G₁ U₁ U₁ (𝟙 G₁)
  have u₂ := over₀_onTorus_unique R J hR D₂ D₂ A₂ A₂ G₂ G₂ U₂ U₂ (𝟙 G₂)
  have bb : b ≫ b' = 𝟙 _ := u₁.1 _ _ (a.hom_inv_id ▸ oComp U₁ U₂ a.hom a.inv b b' hbO hb'O) (oId U₁)
  have bb' : b' ≫ b = 𝟙 _ := u₂.1 _ _ (a.inv_hom_id ▸ oComp U₂ U₁ a.inv a.hom b' b hb'O hbO) (oId U₂)
  have hh₁ : (fun χ => h (h' χ)) = fun χ => χ :=
    u₁.2 _ _ (a.hom_inv_id ▸ tComp U₁ U₂ a.hom a.inv h h' hh hh') (tId U₁)
  have hh₂ : (fun χ => h' (h χ)) = fun χ => χ :=
    u₂.2 _ _ (a.inv_hom_id ▸ tComp U₂ U₁ a.inv a.hom h' h hh' hh) (tId U₂)
  let hE : D₂.toPre.X ≃+ D₁.toPre.X :=
    { toFun := h, invFun := h', left_inv := fun χ => congrFun hh₂ χ, right_inv := fun χ => congrFun hh₁ χ,
      map_add' := h.map_add }
  have hL : Lin U₁ U₂ a.hom b hE.toAddMonoidHom := ⟨ha, hb, hbO, hh⟩
  exact ⟨b, hE, ⟨b', bb, bb'⟩, hL, coord_of_lin R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom b _ hL⟩

end GlobalTheory.TInj
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem ker_mod_eq_perp_range_add : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ y n hn Z Z' h hsurj t ht hiso hdiv a
  have hW : IsOpp D (LinearMap.range t) Z' := (h.symm.shear t ht hiso).symm

  have hdivZ : ∀ b ∈ Z', (∀ z : Z, (n : ℤ) ∣ D.EF (t z) b) → ∃ b'', b = n • b'' := by
    intro b hb hbd
    have hx : ∀ x : LinearMap.range t, (n : ℤ) ∣ D.EF x b := by
      rintro ⟨_, z, rfl⟩
      exact hbd z
    let φ : LinearMap.range t →+ ℤ := AddMonoidHom.mk' (fun x => D.EF x b / n) fun x x' => by
      simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]
      exact Int.add_ediv_of_dvd_left (hx x)
    obtain ⟨b'', hb'', -⟩ := hW.2.2.1 φ
    refine ⟨b'', ?_⟩
    have h0 : (n • (b'' : D.La)) - b = 0 := by
      refine hW.eq_zero (sub_mem (Z'.nsmul_mem b''.2 n) hb) fun w hw => ?_
      have e1 := hb'' ⟨w, hw⟩
      simp only [φ, AddMonoidHom.mk'_apply] at e1
      have e2 : (n : ℤ) ∣ D.EF w b := hx ⟨w, hw⟩
      rw [ef_swap, map_sub, map_nsmul, e1, nsmul_eq_mul, Int.mul_ediv_cancel' e2]
      simp
    exact (sub_eq_zero.1 h0).symm
  have hperp0 : ∀ (k : D.La), k ∈ perp D (LinearMap.range t) → ∀ z : Z, D.EF (t z) k = 0 := by
    intro k hk z
    rw [ef_swap, hk _ ⟨z, rfl⟩, neg_zero]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨b, hb, hk⟩ := hW.exists_sub_mem_perp a
    obtain ⟨b'', hb''⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z a ⟨e, he⟩
      have h2 : D.EF (t z) b = D.EF (t z) a - D.EF (t z) (a - b) := by
        rw [map_sub]; ring
      rw [h2, hperp0 _ hk z, sub_zero]
      exact h1
    refine ⟨a - b, hk, b'', ?_⟩
    rw [← hb'', sub_add_cancel]
  · rintro ⟨k, hk, e, rfl⟩
    obtain ⟨b, hb, e₁, hb1⟩ := hsurj (y k)
    obtain ⟨b'', rfl⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z (k - b) ⟨-e₁, by rw [map_sub, hb1, smul_neg]; abel⟩
      rw [map_sub, hperp0 _ hk z, zero_sub, Int.dvd_neg] at h1
      exact h1
    refine ⟨y b'' - e₁ + y e, ?_⟩
    rw [map_nsmul] at hb1
    rw [map_add (f := _), map_nsmul, smul_add, smul_sub, hb1]
    abel

end GlobalTheory.LowFilt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GFibUniq

theorem isPrimitiveRoot_map {o : Type} [CommRing o] [IsDomain o] {ζ : o} {L : ℕ} (hL : 0 < L)
    (hζ : IsPrimitiveRoot ζ L) (hu : IsUnit (L : o)) (κ : Type) [Field κ] (a : o →+* κ) : IsPrimitiveRoot (a ζ) L := by
  haveI : NeZero (L : κ) := ⟨by simpa using (hu.map a).ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have hr := (hζ.isRoot_cyclotomic hL).map (f := a)
  simpa [Polynomial.map_cyclotomic] using hr

theorem latAt_unique : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  intro o Ω _ _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hu X X' _ _ _ _ _ _ m c m' c' w h h'
  haveI : IsSeparated G.hom := hG.separated
  exact LatAt.unique hL (fun κ _ a => isPrimitiveRoot_map hL hζ hu κ a) h h'

end GlobalTheory.UPoinc.GFibUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum


theorem _root_.GlobalTheory.T.mumfordBundleIso_square_passes_second_iso : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj C]
  [IsCommMonObj C] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj C₁] [IsCommMonObj C₁] {δ : C₁.left ⟶ C.left} {M : LB B.left} {N : LB C.left} {M₁ : LB B₁.left} {N₁ : LB C₁.left}
  (gC : IsGrpPullback C₁ C f δ), M.IsLB → N.IsLB → M₁.IsLB → N₁.IsLB → ∀ (β₂ : (G2 B₁).left ⟶ (G2 B).left) (u : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ B M).pull β₂)), u.IsGen →
  ∀ (v' : LB.Iso N₁ (N.pull δ)), v'.IsGen → ∀ {m : (G2 B).left ⟶ (G2 C).left} {m₁ : (G2 B₁).left ⟶ (G2 C₁).left},
    m₁ ≫ sqOf gC = β₂ ≫ m → ∀ (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen →
    ∃ w₁ : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ C₁ N₁).pull m₁), w₁.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B₁).left) (z : Z) I J I₁ J₁, Good N z I → Good M z J → Good N₁ z I₁ →
        Good M₁ z J₁ → (∏ k, om v' z I I₁ ((p ≫ m₁) ≫ lamφ C₁ k) ^ lamε k) * lamVal w₁ p z I₁ J₁ =
          lamVal w (p ≫ β₂) z I J * lamVal u p z J J₁ := by
  first | exact @GlobalTheory.FactorPull.lam_down_gen | exact GlobalTheory.FactorPull.lam_down_gen | (intros; apply GlobalTheory.FactorPull.lam_down_gen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.extendsAt_of_codim_le_one_over_completeDVRs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (W : (Over.mk χ ⊗ G).left.Opens) (f : Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left, ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ s : Γ((Over.mk (spMap φ ≫ χ) ⊗ G).left, ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W), ∀ (O : (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⊗ G).left.Opens) (h₁ : O ≤ ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)) (h₂ : O ≤ ((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left.appLE _ O h₁).hom s = (((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left.appLE _ O h₂).hom f) → ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left → GlobalTheory.GenericExtend.ExtAt ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left W f y := by
  first | exact @GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one | exact GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one | (intros; apply GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_relativeDimension_abelian_torsionTower : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ G : PDivGroup p R, G.TorsionTower A → ∃ g, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | exact GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | (intros; apply GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham <;> assumption)
end
