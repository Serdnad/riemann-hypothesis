module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PoincAdj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend GlobalTheory.UT GlobalTheory.Mum.Two

theorem lbIso_adj_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  intro R _ _ _ hB G _ _ hS D A U E E' hA
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G G
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  let U₁ := U.toUnifPre
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G G
  let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
  have hL := U₁.LG.isLB
  have hAL := A.isLB
  have hgen := U₁.gen_hom
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U₁.LG.L hL) =
      CechPic.pull U₁.gen.hom.left (cls A.L hAL) := by
    obtain ⟨w, hw⟩ := U₁.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hAL _ (pull_isLB hAL _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
  have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
      ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
    fun q => pullback.lift_fst _ _ _
  have hu : u.left ≫ (A.A ⊗ A.A).hom =
      ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w u
  have key : ∀ (x y : G ⟶ G) (cx cy : A.A ⟶ A.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G ⊗ G).hom (jK R)) (cubeCls G ![fst G G ≫ x, snd G G ≫ y] (cls U₁.LG.L hL)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] (cls A.L hAL))) := by
    intro x y cx cy hx hy
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G ⊗ G))
      (T := G ⊗ G) (fun i => (Over.pullback (jK R)).map (![fst G G ≫ x, snd G G ≫ y] i))
      ![fst G G ≫ x, snd G G ≫ y] (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A.A A.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A.A A.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have g₁ : Gen₀ U₁ U₁ (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have k₁ := key E.aG (𝟙 G) E.aA (𝟙 A.A) E.ext g₁
  have k₂ := key (𝟙 G) E'.aG (𝟙 A.A) E'.aA g₁ E'.ext
  simp only [Category.comp_id] at k₁ k₂
  have eA : cubeCls A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] (cls _ hAL) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] (cls _ hAL) :=
    (cls_cubeLB A.A _ hAL).symm.trans (((cls_eq_iff _ _).2 hA).trans (cls_cubeLB A.A _ hAL))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G ⊗ G) (η[G ⊗ G]).left (Over.w _) _ _ (LB.isLB_linComb hL _ _)
    (LB.isLB_linComb hL _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _),
    cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _)]
  refine (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G ≫ E.aG, snd G G] hL)).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G, snd G G ≫ E'.aG] hL)).symm
  rw [k₁, k₂, eA]

end GlobalTheory.PoincAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.CExtGen

theorem exists_polAV_semiAbelian : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
        ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
          IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
          ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
            IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro g n o _ ζ F V _ _ _ hB hV y
  have hC : GlobalTheory.LN.CDvr V := ⟨hV, hB.1.2.2.2, hB.2⟩
  haveI : CharZero V := hB.2
  haveI : CharZero (FractionRing V) := inferInstance
  obtain ⟨R₁, _, _, hfin, hnt, P, α, α₂, hα, hsq, hlam⟩ := GlobalTheory.T.exists_lambdaPolarisation_siegelObject_charZeroField g n o ζ F.X F.s F.univ F.princ (FractionRing V) y
  obtain ⟨W₁, _, _, _, f₁, ψ, hW₁, hi₁, hl₁, hf₁, hc₁⟩ := GlobalTheory.T.exists_completeDVR_finite_map_of_finiteAlgebra V hC R₁ hfin hnt
  obtain ⟨P₁, φ₁, hP₁, -, hL₁⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P ψ
  obtain ⟨β₂, hβ₂, hΛ₁⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P.A P₁.A φ₁ hP₁
  have lam₁ := hΛ₁ P.L P₁.L _ F.univ.P α₂ P.isLB P₁.isLB F.univ.isLB hL₁ hlam
  obtain ⟨V₁, _, _, _, f₂, fK₂, hV₁, hi₂, hl₂, hf₂, hc₂, A, β, hβ, hLA, G, _, _, gen, hG, hgen⟩ := GlobalTheory.T.exists_semiAbelianModel_finiteExt_completeDVR W₁ hW₁ P₁
  obtain ⟨γ₂, hγ₂, hΛ₂⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P₁.A A.A β hβ
  have lam₂ := hΛ₂ P₁.L A.L _ F.univ.P (β₂ ≫ α₂) P₁.isLB A.isLB F.univ.isLB hLA lam₁
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, f₂.comp f₁, fK₂.comp (ψ.comp (algebraMap _ R₁)), hV₁,
    hi₂.comp hi₁, ?_, hf₂.comp hf₁, ?_, A, β ≫ φ₁ ≫ α, γ₂ ≫ β₂ ≫ α₂, ?_, ?_, ?_, G, inferInstance, inferInstance, gen, hG,
    hgen⟩
  · exact RingHom.isLocalHom_comp f₂ f₁
  · intro a
    simp [hc₁, hc₂]
  · refine (hβ.comp (hP₁.comp hα)).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · exact GlobalTheory.ZM.SiegPull.isSquare_comp hγ₂ (GlobalTheory.ZM.SiegPull.isSquare_comp hβ₂ hsq)
  · simpa [Category.assoc] using lam₂

end GlobalTheory.CExtGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  first | exact @GlobalTheory.UnifDvrBaseChange.exists_pelUnif | exact GlobalTheory.UnifDvrBaseChange.exists_pelUnif | (intros; apply GlobalTheory.UnifDvrBaseChange.exists_pelUnif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  first | exact @GlobalTheory.Mum.trait_at_closed_point | exact GlobalTheory.Mum.trait_at_closed_point | (intros; apply GlobalTheory.Mum.trait_at_closed_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_completeTrait_over_closedPoint_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (x₀ : M.S), M.π x₀ = closedPoint R → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ := by
  first | exact @GlobalTheory.Mum.exists_trait_over_closedPoint | exact GlobalTheory.Mum.exists_trait_over_closedPoint | (intros; apply GlobalTheory.Mum.exists_trait_over_closedPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_complete_trait_extension_of_base : ∀ (R W R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (ρ : R →+* R₁), FinExt ρ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing W) Ω] [Algebra.IsAlgebraic (FractionRing W) Ω] (e : FractionRing R₁ →+* Ω), (∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) (φ r))) → ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsLocalRing W₁) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁) (σ : Ω →+* AlgebraicClosure (FractionRing W₁)), GlobalTheory.LN.CDvr W₁ ∧ Function.Injective iw ∧ iw.Finite ∧ IsLocalHom iw ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧ φ₁.comp ρ = iw.comp φ ∧ (∀ w, σ (algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) w)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (iw w))) ∧ ∀ r, σ (e (algebraMap R₁ (FractionRing R₁) r)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (φ₁ r)) := by
  first | exact @GlobalTheory.TraitExt.exists_finite_trait_extension | exact GlobalTheory.TraitExt.exists_finite_trait_extension | (intros; apply GlobalTheory.TraitExt.exists_finite_trait_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  first | exact @GlobalTheory.MumInt.isIntegral_of_smooth | exact GlobalTheory.MumInt.isIntegral_of_smooth | (intros; apply GlobalTheory.MumInt.isIntegral_of_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  first | exact @GlobalTheory.Mum.unif_trait_baseChange | exact GlobalTheory.Mum.unif_trait_baseChange | (intros; apply GlobalTheory.Mum.unif_trait_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.appTop_bijective_and_surjective_normalDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  first | exact @GlobalTheory.Mum.Modif.appTop_bijective_surjective | exact GlobalTheory.Mum.Modif.appTop_bijective_surjective | (intros; apply GlobalTheory.Mum.Modif.appTop_bijective_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical


theorem _root_.GlobalTheory.T.exists_genericPoint_of_lies_over_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  first | exact @GlobalTheory.Mum.modif_pt_over_gen | exact GlobalTheory.Mum.modif_pt_over_gen | (intros; apply GlobalTheory.Mum.modif_pt_over_gen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_weightZero_section_nonzero_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  first | exact @GlobalTheory.Mum.exists_secB_zero_nonzero_origin | exact GlobalTheory.Mum.exists_secB_zero_nonzero_origin | (intros; apply GlobalTheory.Mum.exists_secB_zero_nonzero_origin <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.factorization_through_finite_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h → M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp → a = c ≫ M'.gp := by
  first | exact @GlobalTheory.Mum.finite_modif_eq_gp | exact GlobalTheory.Mum.finite_modif_eq_gp | (intros; apply GlobalTheory.Mum.finite_modif_eq_gp <;> assumption)
end
