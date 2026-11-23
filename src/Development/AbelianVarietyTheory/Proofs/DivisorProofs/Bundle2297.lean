module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle719
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem restrict_upwardClosed_subcategory_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : ObjectProperty C), (∀ S S', (S ⟶ S') → P S → P S') →
    (∀ T, Desc.Sep F fun S (_ : T ⟶ S) ↦ P S) → (∀ T, Desc.Glue F fun S (_ : T ⟶ S) ↦ P S) →
    (∀ T, Desc.Van1 F fun S (_ : T ⟶ S) ↦ P S) → Function.Bijective (CoefMap.restrict F P.ι).pull1 := by
  intro R _ C _ F P hP sep glue van
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g₀, hg⟩ := hc
    let g : ∀ S, P S → F.obj S := fun S hS ↦ g₀ ⟨S, hS⟩
    have hg' : ∀ (S S' : C) (hS : P S) (hS' : P S') (ψ : S ⟶ S'),
        g S' hS' - mp F ψ (g S hS) = f.1 S S' ψ := fun S S' hS hS' ψ ↦
      congrFun (congrFun (congrFun hg ⟨S, hS⟩) ⟨S', hS'⟩) (ObjectProperty.homMk ψ)
    have h1 : ∀ T : C, ∃ x : F.obj T, ∀ S (u : T ⟶ S) (hS : P S),
        mp F u x = g S hS - f.1 T S u := by
      intro T
      obtain ⟨x, hx⟩ := glue T (fun S u ↦ if hS : P S then g S hS - f.1 T S u else 0)
        fun S S' u ψ hS ↦ by
          have hS' := hP _ _ ψ hS
          simp only [dif_pos hS, dif_pos hS', map_sub]
          have k1 := Z1.comp f u ψ
          have k2 := hg' S S' hS hS' ψ
          linear_combination k2 - k1
      exact ⟨x, fun S u hS ↦ by rw [hx S u hS, dif_pos hS]⟩
    choose x hx using h1
    refine H1.mk_eq_zero.2 ⟨x, ?_⟩
    funext T T' φ
    rw [amitsur_d0_apply]
    refine (sub_eq_zero.1 (sep T' _ fun S u hS ↦ ?_)).symm
    have k1 := Z1.comp f φ u
    have k2 := hx T' S u hS
    have k3 := hx T S (φ ≫ u) hS
    rw [mp_comp] at k3
    simp only [map_sub]
    linear_combination k3 - k2 - k1
  · intro c
    obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
    let z : ∀ S S', (S ⟶ S') → F.obj S' := fun S S' ψ ↦
      if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0
    have hz : ∀ S S' S'' (ψ : S ⟶ S') (χ : S' ⟶ S''), P S →
        z S S'' (ψ ≫ χ) = mp F χ (z S S' ψ) + z S' S'' χ := by
      intro S S' S'' ψ χ hp
      have hp' := hP _ _ ψ hp
      simp only [z, dif_pos hp, dif_pos hp']
      exact y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hp'⟩) (T'' := ⟨S'', hP _ _ χ hp'⟩)
        (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ)
    have hzy : ∀ (S S' : P.FullSubcategory) (ψ : S ⟶ S'), z S.obj S'.obj ψ.hom = y.1 S S' ψ := by
      intro S S' ψ
      simp only [z, dif_pos S.property]
      rfl
    have h1 : ∀ T : C, ∃ b : ∀ S, (T ⟶ S) → F.obj S, (∀ S S' u ψ, P S →
        b S' (u ≫ ψ) - mp F ψ (b S u) = z S S' ψ) ∧ (P T → ∀ S u, b S u = z T S u) := by
      intro T
      by_cases hp : P T
      · exact ⟨fun S u ↦ z T S u, fun S S' u ψ _ ↦ by
          have := hz _ _ _ u ψ hp
          linear_combination this, fun _ _ _ ↦ rfl⟩
      · obtain ⟨b, hb⟩ := van T (fun S S' _ ψ ↦ z S S' ψ) fun S S' S'' u ψ χ h ↦ hz _ _ _ ψ χ h
        exact ⟨b, hb, fun h ↦ absurd h hp⟩
    choose b hb hb' using h1
    have h2 : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ S (u : T' ⟶ S), P S →
        mp F u x = b T S (φ ≫ u) - b T' S u := by
      intro T T' φ
      refine glue T' _ fun S S' u ψ hp ↦ ?_
      have k1 := hb T _ _ (φ ≫ u) ψ hp
      have k2 := hb T' _ _ u ψ hp
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k1 - k2
    choose f hf using h2
    refine ⟨H1.mk F ⟨f, fun T T' T'' φ ψ ↦ sub_eq_zero.1 (sep T'' _ fun S u hp ↦ ?_)⟩, ?_⟩
    · have k1 := hf _ _ (φ ≫ ψ) S u hp
      have k2 := hf _ _ φ S (ψ ≫ u) hp
      have k3 := hf _ _ ψ S u hp
      simp only [map_sub, map_add (f := _), mp_comp, Category.assoc] at k1 k2 ⊢
      linear_combination k1 - k2 - k3
    · rw [CoefMap.pullCohomologyOne_class]
      congr 1
      refine Subtype.ext ?_
      funext S S' ψ
      have k1 := hf _ _ ψ.hom _ (𝟙 _) S'.property
      rw [hb' _ S.property, hb' _ S'.property, mp_id, Category.comp_id] at k1
      have k2 := hz _ _ _ (𝟙 S'.obj) (𝟙 S'.obj) S'.property
      rw [Category.id_comp, mp_id] at k2
      rw [← hzy]
      change f _ _ ψ.hom = _
      linear_combination k1 + k2

end GlobalTheory.CatCoh.Desc
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.AbelianDeRhamFreeOfHodge

def extSqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem extSqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    extSqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem free_of (hC : GlobalTheory.Published.CrystallineSmoothLift) (hA : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (s : A.left ⟶ Sp R) (hs : s = A.hom) :
    Module.Finite R (FirstDeRham s) ∧ Module.Projective R (FirstDeRham s) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham s) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham s) ≃ₗ[R] SecondDeRham s,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b := by
  subst hs
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  obtain ⟨⟨hfin, hproj, hrank⟩, ⟨eH, heH⟩, -⟩ := hA R A g hab hg
  obtain ⟨hbij, e2, he2⟩ := GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left A.hom inferInstance inferInstance inferInstance
  let E1 : FirstDeRham A.hom ≃ₗ[R] HH1 A.hom := LinearEquiv.ofBijective (cmp1 A.hom) hbij
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, ?_, ?_⟩
  · intro p
    rw [Module.rankAtStalk_eq_of_equiv E1]
    exact hrank p
  · refine ⟨(extSqEquiv E1).trans (eH.trans e2.symm), fun a b => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extSqEquiv_ιMulti, heH, LinearEquiv.symm_apply_eq]
    exact (he2 a b).symm

end GlobalTheory.Proof.AbelianDeRhamFreeOfHodge


open GlobalTheory.Proof.AbelianDeRhamFreeOfHodge in
theorem GlobalTheory.Proof.abelianDeRhamFree_of_hodge :
    GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  intro hC hA R _ A _ g hab hg
  exact free_of hC hA R A g hab hg _ (Category.comp_id _)
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) [IsMonHom u₀] [IsMonHom u], u₀.left ≫ i = i ≫ u.left →
    ∀ (P₀ Q₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → LBIso Q₀ (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left) →
    ∀ (P Q : LB (A ⊗ A).left), P.IsLB → Q.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso Q (P.pull (lift (fst A A) (snd A A ≫ u)).left) := by
  first | exact @GlobalTheory.BirigidLift.pull_one_prod_of_lift | exact GlobalTheory.BirigidLift.pull_one_prod_of_lift | (intros; apply GlobalTheory.BirigidLift.pull_one_prod_of_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) →
      HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso (P.pull l) P₀ →
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  first | exact @GlobalTheory.BirigidLift.symm_of_lift | exact GlobalTheory.BirigidLift.symm_of_lift | (intros; apply GlobalTheory.BirigidLift.symm_of_lift <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem Data.sec_smooth (D : Data) (U : D.X.affineOpens) : Algebra.Smooth D.R (Sec D.s U.1) := by
  haveI := D.smooth
  have h := HasRingHomProperty.appLE @Smooth D.s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((D.s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of D.R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of D.R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

theorem Data.mono_i (D : Data) : Mono D.i := by
  obtain ⟨s₀, hpb, -⟩ := D.red
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk D.I)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion D.i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip ‹_›
  infer_instance

theorem Data.affine_inf (D : Data) {U V : D.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := by
  haveI := D.sep
  haveI : IsSeparated (Limits.terminal.from D.X) := by
    rw [← Limits.terminal.comp_from D.s]; infer_instance
  exact hU.inf hV

theorem Data.smooth_mono_inf : ∀ D : Data, (∀ U : D.X.affineOpens, Algebra.Smooth D.R (Sec D.s U.1)) ∧ Mono D.i ∧
    ∀ U V : D.X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
  fun D ↦ ⟨D.sec_smooth, D.mono_i, fun _ _ hU hV ↦ D.affine_inf hU hV⟩

end GlobalTheory.SmoothLift
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem exists_extend_hodgeFiltration_functional_split {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hO : Function.Injective (cmpO s)) (h1 : Function.Surjective (cmp1 s))
    (hsurj : Function.Surjective (toHO1 s)) [Module.Projective R (HO1 s)]
    (ψ : F1 s →ₗ[R] R) : ∃ H : FirstDeRham s →ₗ[R] R, ∀ c : F1 s, H c = ψ c := by
  let f : FirstDeRham s →ₗ[R] HO1 s := (toHO1 s).comp (cmp1 s)
  have hf : Function.Surjective f := hsurj.comp h1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hker : ∀ c : FirstDeRham s, f c = 0 ↔ c ∈ F1 s := fun c ↦ by
    change toHO1 s (cmp1 s c) = 0 ↔ toH1O s c = 0
    rw [structureSheaf_comparison_comm]
    exact ⟨fun h ↦ hO (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  let p : FirstDeRham s →ₗ[R] F1 s := LinearMap.codRestrict (F1 s) (LinearMap.id - σ.comp f) fun c ↦ by
    rw [← hker]
    have : f (σ (f c)) = f c := LinearMap.congr_fun hσ (f c)
    simp [this]
  refine ⟨ψ.comp p, fun c ↦ ?_⟩
  have hc : f c = 0 := (hker c).2 c.2
  have : p c = c := Subtype.ext (by simp [p, hc])
  simp [this]

end GlobalTheory.CechDR

namespace GlobalTheory.AbelianExtend

open GlobalTheory.CechDR

theorem abelianScheme_hodgeFiltration_functional_extends' : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R,
      ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  intro hC hH R _ A _ g hab hdim ψ
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hsurj⟩, -⟩ := hH R A g hab hdim
  haveI := hab.smooth
  haveI := hab.proper
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have h1 := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left (A.hom ≫ 𝟙 (Sp R)) hsm hsep hqc).1.2
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 (Sp R))
  have hs' : Function.Surjective (toHO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hsurj
  haveI : Module.Projective R (HO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hproj
  exact GlobalTheory.CechDR.exists_extend_hodgeFiltration_functional_split _ hO h1 hs' ψ

end GlobalTheory.AbelianExtend
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  first | exact @GlobalTheory.BirigidHom.exists_hom_of_triv | exact GlobalTheory.BirigidHom.exists_hom_of_triv | (intros; apply GlobalTheory.BirigidHom.exists_hom_of_triv <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_image_inertia_of_potentialGoodReduction_alt : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → HasPotentialGoodReduction R K A → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  exact @GlobalTheory.finite_image_inertia_of_potentialGoodReduction
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isDiscreteValuationRing_fixedField_inertia_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsDiscreteValuationRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  first | exact @GlobalTheory.InertiaFixedDVR.isDiscreteValuationRing_fixedField_inertia | exact GlobalTheory.InertiaFixedDVR.isDiscreteValuationRing_fixedField_inertia | (intros; apply GlobalTheory.InertiaFixedDVR.isDiscreteValuationRing_fixedField_inertia <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformizer_of_valuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → V.valuation (algebraMap K Ω (algebraMap R K π)) < 1 ∧ ∀ y : IntermediateField.fixedField (inertia K V), V.valuation (y : Ω) < 1 → ∃ z : IntermediateField.fixedField (inertia K V), (z : Ω) ∈ V ∧ y = algebraMap K _ (algebraMap R K π) * z := by
  first | exact @GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia | exact GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia | (intros; apply GlobalTheory.InertiaFixedUniformizer.uniformizer_fixedField_inertia <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasPotentialGoodReduction_of_finite_image_inertia_alt : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite → HasPotentialGoodReduction R K A := by
  first | exact @GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia | exact GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia | (intros; apply GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1) ∧ ∀ x : CuspSub E a, IsNormalised x → IsDiscrete x.V := by
  first | exact @GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete | exact GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete | (intros; apply GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete <;> assumption)
end
