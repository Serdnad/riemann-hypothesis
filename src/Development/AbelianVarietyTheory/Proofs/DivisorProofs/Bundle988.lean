module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle766
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem extHom_coefHom_restrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {C₂ C' : Type} [Category.{0} C₂] [Category.{0} C'] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (G : C' ⥤ C₂) (T : C')
    (y : R₁ ⊗[R₀] F₂.obj ((CoefMap.restrict F₂ G).G.obj T)) :
    extHom R₁ (coefHom (CoefMap.restrict F₂ G) T) y = y := by
  change Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (AlgHom.id R₀ _) y = y
  rw [Algebra.TensorProduct.map_id]; rfl

theorem isOb2_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C₂ _ F₂ C' _ G n L L₂ w w₂ c c₂ hw h1 h2
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h1
  obtain ⟨θ₂, σ₂, z₂, hθ₂, hσ₂, rfl, hz₂⟩ := h2
  have hl0 : ∀ T : C', ∃ l : L.B (n.G.obj T) →ₐ[R] L₂.B (G.obj T),
      ∀ b, L₂.p (G.obj T) (l b) = coefHom n T (L.p _ b) := by
    intro T
    haveI := L.smooth (n.G.obj T)
    exact homLift R R₀ I hI π hπ hk _ _ (L.p _) (L.semi _) (L.surj _) (L.ker _) _ _ (L₂.p (G.obj T))
      (L₂.semi _) (L₂.surj _) (L₂.ker _) (coefHom n T)
  choose l hl using hl0
  have hd : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      ((L₂.ρ (G.map a)).comp (l T)) b - ((l T').comp (L.ρ (n.G.map a))) b ∈
        I.map (algebraMap R (L₂.B (G.obj T'))) := by
    intro T T' a b
    refine (L₂.ker _ _).1 ?_
    rw [map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply]
    rw [L₂.nat, hl, hl, L.nat]
    exact (n.naturality a (L.p _ b)).symm
  choose κ hκ using fun (T T' : C') (a : T ⟶ T') ↦ ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T))
    (L₂.B (G.obj T')) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _)
    ((L₂.ρ (G.map a)).comp (l T))).1 _ (hd T T' a)).exists
  have key : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (ω : Ω[F.obj (n.G.obj T)⁄R₀]),
      θ₂ _ _ _ (G.map a) (G.map b) (q1 n T ω) + κ T T'' (a ≫ b) ω =
        L₂.ρ (G.map b) (κ T T' a ω) + κ T' T'' b (p1 F (n.G.map a) ω) +
          l T'' (θ _ _ _ (n.G.map a) (n.G.map b) ω) := by
    intro T T' T'' a b ω
    have e1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L₂.p (G.obj T)) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ₂ _ _ _ (G.map a) (G.map b))).2
      (l T) (coefHom n T) (hl T)
    have e2 := hκ T T'' (a ≫ b)
    rw [Functor.map_comp, Functor.map_comp] at e2
    have s1 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      e1).2.1 e2
    have f1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T')) (L₂.B (G.obj T'')) _ _ _ (hκ T T' a)).1 (L₂.ρ (G.map b))
    have f2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T')) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hκ T' T'' b)).2
      (L.ρ (n.G.map a)) (mp F (n.G.map a)) (L.nat (n.G.map a))
    have f3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ _ _ _ (n.G.map a) (n.G.map b))).1 (l T'')
    have s2 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
        f1).2.1 f2)).2.1 f3
    have e := congrArg (fun t : Ω[F.obj (n.G.obj T)⁄R₀] →+ L₂.B (G.obj T'') ↦ t ω)
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ (l T'' |>.comp (L.ρ (n.G.map (a ≫ b)))) _ _
        s1).2.2.1 s2)
    exact e
  choose g hgK hg using fun (T T' : C') (a : T ⟶ T') ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _
    (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (σ₂ _) (hσ₂ _)).2.2.2 (κ T T' a (w.1 _))
    ((hκ T T' a).mem _)
  have kadd : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y + y') :=
    fun y y' h h' ↦ by unfold Aug.KerQ at *; rw [map_add (f := _), h, h', add_zero]
  have kneg : ∀ {X : C₂} (y : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ (-y) :=
    fun y h ↦ by unfold Aug.KerQ at *; rw [map_neg, h, neg_zero]
  have ksub : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y - y') :=
    fun y y' h h' ↦ by rw [sub_eq_add_neg]; exact kadd _ _ h (kneg _ h')
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -g T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L₂.smooth (G.obj T'')
  have nb := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (L₂.ρ (G.map b)) (mp F₂ (G.map b)) (L₂.nat (G.map b))
    (σ₂ _) (σ₂ _) (hσ₂ _) (hσ₂ _)
  have nl := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T'')) (L.semi _) (L.surj _) (L.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (l T'') (coefHom n T'') (hl T'')
    (σ _) (σ₂ _) (hσ _) (hσ₂ _)
  change extHom R₁ (mp F₂ (G.map b)) (-g T T' a) - -g T T'' (a ≫ b) + -g T' T'' b =
    extHom R₁ (coefHom n T'') (z.1 _ _ _ (n.G.map a) (n.G.map b)) -
      extHom R₁ (coefHom (CoefMap.restrict F₂ G) T'') (z₂.1 _ _ _ (G.map a) (G.map b))
  rw [extHom_coefHom_restrict, ← sub_eq_zero]
  refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _)
    (σ₂ _) (hσ₂ _) _ ?_ ?_
  · refine ksub _ _ (kadd _ _ (ksub _ _ ?_ (kneg _ (hgK _ _ _))) (kneg _ (hgK _ _ _)))
      (ksub _ _ (nl.2 _ (hz _ _ _ _ _).1) (hz₂ _ _ _ _ _).1)
    rw [map_neg]; exact kneg _ (nb.2 _ (hgK _ _ _))
  · change σ₂ (G.obj T'') ((_ : R₁ ⊗[R₀] F₂.obj (G.obj T'')) -
      (_ - z₂.1 (G.obj T) (G.obj T') (G.obj T'') (G.map a) (G.map b))) = 0
    simp only [map_sub, map_add (f := _), map_neg]
    rw [← nb.1, ← nl.1, hg, hg, hg, (hz _ _ _ _ _).2, (hz₂ _ _ _ _ _).2, ← hw, w.2 (n.G.map a)]
    linear_combination key T T' T'' a b (w.1 _)

end GlobalTheory.Obs
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_degreeOneObstructionClass : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  first | exact @GlobalTheory.Obs.exists_isOb1 | exact GlobalTheory.Obs.exists_isOb1 | (intros; apply GlobalTheory.Obs.exists_isOb1 <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_degreeTwoObstructionClass : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  first | exact @GlobalTheory.Obs.exists_isOb2 | exact GlobalTheory.Obs.exists_isOb2 | (intros; apply GlobalTheory.Obs.exists_isOb2 <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.obstructionPullback_eq_zero_of_naturalLift_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  first | exact @GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift | exact GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift | (intros; apply GlobalTheory.Obs.obstructionPullback_eq_zero_of_naturalLift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧ ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → PrimitiveStructureSheafDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso | exact GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso | (intros; apply GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_functorial_lifts_of_obstructionTwo_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  first | exact @GlobalTheory.Obs.exists_isFun_of_isOb2_zero | exact GlobalTheory.Obs.exists_isFun_of_isOb2_zero | (intros; apply GlobalTheory.Obs.exists_isFun_of_isOb2_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semilinear_cochain_of_degreeOneObstruction_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  first | exact @GlobalTheory.Obs.exists_cochain_of_isOb1_zero | exact GlobalTheory.Obs.exists_cochain_of_isOb1_zero | (intros; apply GlobalTheory.Obs.exists_cochain_of_isOb1_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_natLift_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar C' _ F' L L' n l hl κ u hκ hus hum hκd
  have hext : ∀ T : C', ∃! ξ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T,
      (∀ b w, ξ (L.p (n.G.obj T) b • w) = l T b * ξ w) ∧
      (∀ w, ξ w ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ w : GlobForm s₀, ξ (w.1 (n.G.obj T)) = u w T := fun T ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T) ((Pi.evalAddMonoidHom _ T).comp u)
      (fun r w ↦ by simp [hus]) (fun w ↦ hum w T)
  choose ξ hξ using fun T ↦ (hext T).exists
  have hψ : ∀ T : C', ∃ ψ : L.B (n.G.obj T) →ₐ[R] L'.B T,
      IsTheta I (L.p (n.G.obj T)) (l T) ψ (-ξ T) := fun T ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (L.B (n.G.obj T)) (Sec s₀ (n.G.obj T).unop.1) (L'.B T) I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T)).2 (-ξ T)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hξ T).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hξ T).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ T b, ψ T b = l T b + ξ T (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) := fun T b ↦ by
    have h := (hψ T).der b
    rw [AddMonoidHom.neg_apply] at h
    change -ξ T _ = l T b - ψ T b at h
    linear_combination h
  refine ⟨ψ, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · rw [hψv, map_add (f := _), hl, (L'.ker T _).2 ((hξ T).2.1 _), add_zero]
  · let α : L.B (n.G.obj T) →ₐ[R] L'.B T' := (L'.ρ a).comp (l T)
    let χ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T' := κ T T' a + (L'.ρ a).toAddMonoidHom.comp (ξ T) -
      (ξ T').comp (p1 (OAff s₀) (n.G.map a)).toAddMonoidHom
    have hχ : ∀ w, χ w = κ T T' a w + L'.ρ a (ξ T w) - ξ T' (p1 (OAff s₀) (n.G.map a) w) := fun _ ↦ rfl
    have hmemV : ∀ w, ξ T' w ∈ I.map (algebraMap R (L'.B T')) := (hξ T').2.1
    have hdiff : ∀ c : L.B (n.G.obj T), ∀ x ∈ I.map (algebraMap R (L'.B T')),
        l T' (L.ρ (n.G.map a) c) * x = α c * x := by
      intro c x hx
      have h1 := (hκ T T' a).der c
      have h2 : α c - l T' (L.ρ (n.G.map a) c) ∈ I.map (algebraMap R (L'.B T')) :=
        h1 ▸ (hκ T T' a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T') (L.p _)
      (L.semi _) (L.surj _) (L.ker _) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hκ T T' a).smul, (hξ T).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← L.nat (n.G.map a) b, (hξ T').1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hκ T T' a).mem w) (algHom_mem_map I _ ((hξ T).2.1 w))) (hmemV _)
      · rw [hχ, hκd, (hξ T).2.2, ← w.2 (n.G.map a), (hξ T').2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) (n.G.map a) (L.p _ b) = L.p _ (L.ρ (n.G.map a) b) := (L.nat (n.G.map a) b).symm
    rw [hn] at h0
    have h1 := (hκ T T' a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add (f := _)]
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.affinePairLifts_glue_to_morphism_of_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l → ∃ f : Z ⟶ X, f ≫ s = t ∧ k ≫ f = f₀ ≫ i := by
  first | exact @GlobalTheory.Obs.pairs_glue | exact GlobalTheory.Obs.pairs_glue | (intros; apply GlobalTheory.Obs.pairs_glue <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem axesE1_of_axesO1 : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  intro hO R₀ R₁ _ _ _ q hq A _ g hab hsm c h₁ h₂
  obtain ⟨B, hB, pr, pr', habB, hsmB, hp, hp', -, -, -, hl, hr⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hab hsm
  letI : GrpObj B := hB
  obtain ⟨e, he⟩ := GlobalTheory.T.h1_structure_base_change_extension R₀ R₁ q hq
  set c₁ := (e _ _ _ _ _ hp').symm c with hc₁
  have hc : e _ _ _ _ _ hp' c₁ = c := by simp [hc₁]
  have hl' : IsPullO (overW (lift (𝟙 B) 1)) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift (𝟙 A) 1)) (overW (lift (𝟙 B) 1)) hl c₁ 0 ?_
    rw [hc, map_zero]; exact h₁
  have hr' : IsPullO (overW (lift 1 (𝟙 B))) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift 1 (𝟙 A))) (overW (lift 1 (𝟙 B))) hr c₁ 0 ?_
    rw [hc, map_zero]; exact h₂
  have h0 : c₁ = 0 := hO R₁ B g habB hsmB c₁ hl' hr'
  rw [← hc, h0, map_zero]

end GlobalTheory.Obs
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_of_primO2 (hO : PrimitiveStructureSheafDegTwoVanish) : PrimitiveExtendedDegTwoVanish := by
  intro R₀ R₁ _ _ _ q hq A _ g hA hsm c c₁ c₂ hμ h₁ h₂
  obtain ⟨B, _, pr, pr', hB, hBs, hp, hp', eμ, ef, es, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hA hsm
  obtain ⟨e, he⟩ := GlobalTheory.T.h2_structure_base_change_extension R₀ R₁ q hq
  set eX := e A.left B.left A.hom B.hom pr hp
  set eY := e (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
  have hc : c = eX (eX.symm c) := (eX.apply_symm_apply c).symm
  have hc₁ : c₁ = eY (eY.symm c₁) := (eY.apply_symm_apply c₁).symm
  have hc₂ : c₂ = eY (eY.symm c₂) := (eY.apply_symm_apply c₂).symm
  have hsum : c₁ + c₂ = eY (eY.symm c₁ + eY.symm c₂) := by rw [map_add (f := _), ← hc₁, ← hc₂]
  have hd : eX.symm c = 0 := by
    refine hO R₁ B g hB hBs (eX.symm c) (eY.symm c₁) (eY.symm c₂) ?_ ?_ ?_
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (μ[A]).left (μ[B]).left (overW μ[A]) (overW μ[B]) eμ _ _ ?_
      rw [← hc, ← hsum]; exact hμ
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (fst A A).left (fst B B).left (overW (fst A A)) (overW (fst B B)) ef _ _ ?_
      rw [← hc, ← hc₁]; exact h₁
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (snd A A).left (snd B B).left (overW (snd A A)) (overW (snd B B)) es _ _ ?_
      rw [← hc, ← hc₂]; exact h₂
  rw [hc, hd, map_zero]

end GlobalTheory.Obs
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.Defect

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S S' : Sys I π s₀} (Φ : S.LocIso S')

abbrev al {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)

abbrev be {U V : AffOp X₀} (a : U ⟶ V) : S.F.obj U →ₐ[R] S'.F.obj V :=
  (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)

theorem map_mem {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (f : B →ₐ[R] B')
    {x : B} (hx : x ∈ I.map (algebraMap R B)) : f x ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (f : B →+* B') hx
  rwa [Ideal.map_map, f.comp_algebraMap] at h

theorem mul_eq_zero' (hI : I ^ 2 = 0) {B : Type} [CommRing B] [Algebra R B] {x y : B}
    (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B] at h
  simpa using h

theorem diff_mem {U V : AffOp X₀} (a : U ⟶ V) (b : S.F.obj U) :
    al Φ a b - be Φ a b ∈ I.map (algebraMap R (S'.F.obj V)) := by
  rw [← S'.ker V, map_sub, sub_eq_zero]
  change S'.p V (mp S'.F a (Φ.φ U b)) = S'.p V (Φ.φ V (mp S.F a b))
  rw [S'.nat, Φ.red, Φ.red, S.nat]

theorem ex (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) :
    ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V, IsTheta I (S.p U) (al Φ a) (be Φ a) θ :=
  (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U) (S.semi U)
    (S.surj U) (S.ker U) (al Φ a)).1 (be Φ a) (diff_mem Φ a)

def th (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V :=
  (ex Φ hI hπ a).exists.choose

theorem th_spec (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) : IsTheta I (S.p U) (al Φ a) (be Φ a) (th Φ hI hπ a) :=
  (ex Φ hI hπ a).exists.choose_spec

theorem th_comp (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V W : AffOp X₀} (a : U ⟶ V)
    (b : V ⟶ W) (x : Ω[Sec s₀ U.unop.1⁄R₀]) :
    th Φ hI hπ (a ≫ b) x = mp S'.F b (th Φ hI hπ a x) + th Φ hI hπ b (p1 (OAff s₀) a x) := by
  let θ' : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj W :=
    ((mp S'.F b).toRingHom.toAddMonoidHom.comp (th Φ hI hπ a)) +
      (th Φ hI hπ b).comp (p1 (OAff s₀) a).toAddMonoidHom
  have hA := th_spec Φ hI hπ a
  have hB := th_spec Φ hI hπ b
  have h : IsTheta I (S.p U) (al Φ (a ≫ b)) (be Φ (a ≫ b)) θ' := by
    refine ⟨fun c w ↦ ?_, fun c ↦ ?_, fun w ↦ ?_⟩
    · change mp S'.F b (th Φ hI hπ a (S.p U c • w)) + th Φ hI hπ b (p1 (OAff s₀) a (S.p U c • w)) =
        al Φ (a ≫ b) c * (mp S'.F b (th Φ hI hπ a w) + th Φ hI hπ b (p1 (OAff s₀) a w))
      rw [hA.smul, oneFormsMapOfFunctorMorphism_smul]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.smul, map_mul]
      have hz : (mp S'.F b (al Φ a c) - al Φ b (mp S.F a c)) * th Φ hI hπ b (p1 (OAff s₀) a w) = 0 := by
        refine mul_eq_zero' hI ?_ (hB.mem _)
        have : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
        rw [this, ← map_sub]
        exact map_mem _ (diff_mem Φ a c)
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      rw [e2]
      linear_combination -hz
    · change mp S'.F b (th Φ hI hπ a (D R₀ _ (S.p U c))) + th Φ hI hπ b (p1 (OAff s₀) a (D R₀ _ (S.p U c))) =
        al Φ (a ≫ b) c - be Φ (a ≫ b) c
      rw [hA.der, p1_D]
      have e : mp (OAff s₀) a (S.p U c) = S.p V (mp S.F a c) := (S.nat a c).symm
      rw [e, hB.der, map_sub]
      have e2 : al Φ (a ≫ b) c = mp S'.F b (al Φ a c) := mp_comp S'.F a b _
      have e3 : be Φ (a ≫ b) c = be Φ b (mp S.F a c) := by
        change Φ.φ W (mp S.F (a ≫ b) c) = Φ.φ W (mp S.F b (mp S.F a c)); rw [mp_comp]
      have e4 : al Φ b (mp S.F a c) = mp S'.F b (be Φ a c) := rfl
      rw [e2, e3, e4]; ring
    · exact Ideal.add_mem _ (map_mem _ (hA.mem w)) (hB.mem _)
  have := (ex Φ hI hπ (a ≫ b)).unique (th_spec Φ hI hπ (a ≫ b)) h
  exact DFunLike.congr_fun this x

def cocyc (hI : I ^ 2 = 0) (hπ : Function.Surjective π) : GlobForm s₀ →+ Z1 S'.F where
  toFun w := ⟨fun U V a ↦ th Φ hI hπ a (w.1 U), fun U V W a b ↦ by
    change th Φ hI hπ (a ≫ b) (w.1 U) = mp S'.F b (th Φ hI hπ a (w.1 U)) + th Φ hI hπ b (w.1 V)
    rw [th_comp, w.2 a]⟩
  map_zero' := Subtype.ext (by funext U V a; exact map_zero _)
  map_add' w w' := Subtype.ext (by funext U V a; exact map_add _ _ _)

theorem th_smul (hI : I ^ 2 = 0) (hπ : Function.Surjective π) {U V : AffOp X₀} (a : U ⟶ V) (r : R)
    (x : Ω[Sec s₀ U.unop.1⁄R₀]) : th Φ hI hπ a (π r • x) = r • th Φ hI hπ a x := by
  rw [← algebraMap_smul (Sec s₀ U.unop.1) (π r) x, ← (S.semi U).map_algebraMap, (th_spec Φ hI hπ a).smul,
    AlgHom.commutes, ← Algebra.smul_def]

end GlobalTheory.LiftSys.Defect

theorem GlobalTheory.LiftSys.exists_defect_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), ∃ (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) (v : GlobForm s₀ →+ Z1 S'.F), Φ.IsDefect θ ∧ (∀ w U V a, (v w).1 U V a = θ U V a (w.1 U)) ∧ (∀ w, S'.IsIdealValuedLiftSystemCocycle (v w)) ∧ ∀ (r : R) w, v (π r • w) = r • v w := by
  intro R R₀ _ _ I hI π hπ _ X₀ s₀ S S' Φ
  refine ⟨fun U V a ↦ Defect.th Φ hI hπ a, Defect.cocyc Φ hI hπ, fun U V a ↦ Defect.th_spec Φ hI hπ a,
    fun w U V a ↦ rfl, fun w U V a ↦ (Defect.th_spec Φ hI hπ a).mem _, fun r w ↦ ?_⟩
  refine Subtype.ext ?_
  funext U V a
  exact Defect.th_smul Φ hI hπ a r (w.1 U)
end
end
