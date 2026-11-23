module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectExtensionAbelianLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_principalSiegelObject_extension_abelianLocus : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := by
  first | exact @GlobalTheory.SiegExtend.exists_principal_extension | exact GlobalTheory.SiegExtend.exists_principal_extension | (intros; apply GlobalTheory.SiegExtend.exists_principal_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumDescent.cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → ∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k := by
  intro R _ _ _ _ S X π hπp hπs hS U hU J e he V τ hV hτ i j k T x y w hxy hw
  set pP := pullback.fst U.hom π with hpP

  set O : U.left.Opens := V i j ⊓ V i k with hO
  let m₁ : O.toScheme ⟶ (V i j).toScheme := U.left.homOfLE inf_le_left
  let m₂ : O.toScheme ⟶ (V i k).toScheme := U.left.homOfLE inf_le_right
  have hm₁ : m₁ ≫ (V i j).ι = O.ι := Scheme.homOfLE_ι _ _
  have hm₂ : m₂ ≫ (V i k).ι = O.ι := Scheme.homOfLE_ι _ _

  let FinalForm : (pullback U.hom π).Opens := pP ⁻¹ᵁ O
  let p' : FinalForm.toScheme ⟶ O.toScheme := pP ∣_ O
  have hp' : p' ≫ O.ι = FinalForm.ι ≫ pP := morphismRestrict_ι _ _
  have hsq : IsPullback p' (FinalForm.ι ≫ pullback.snd U.hom π) (O.ι ≫ U.hom) π :=
    (isPullback_morphismRestrict pP O).paste_vert (IsPullback.of_hasPullback U.hom π)
  have hp'surj : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hπs
  have hZ : ∀ (l : J) (z : FinalForm.toScheme), (FinalForm.ι ≫ e i) z ∈ Set.range (e l) ↔ pP (FinalForm.ι z) ∈ V i l := by
    intro l z; rw [hV]; rfl
  have hZO : ∀ z : FinalForm.toScheme, pP (FinalForm.ι z) ∈ O := by
    intro z
    have : (FinalForm.ι ≫ pP) z ∈ O := by
      rw [← hp']; exact (Scheme.Opens.range_ι O).subset ⟨p' z, rfl⟩
    exact this
  have rj : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e j) := by
    rintro _ ⟨z, rfl⟩; exact (hZ j z).2 (hZO z).1
  have rk : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e k) := by
    rintro _ ⟨z, rfl⟩; exact (hZ k z).2 (hZO z).2
  let b := IsOpenImmersion.lift (e j) (FinalForm.ι ≫ e i) rj
  let c := IsOpenImmersion.lift (e k) (FinalForm.ι ≫ e i) rk
  have hb : b ≫ e j = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  have hc : c ≫ e k = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _

  have h1 : p' ≫ m₁ ≫ τ i j = b ≫ pP :=
    hτ i j _ FinalForm.ι b (p' ≫ m₁) hb.symm (by rw [Category.assoc, hm₁, hp'])
  have h2 : p' ≫ m₂ ≫ τ i k = c ≫ pP :=
    hτ i k _ FinalForm.ι c (p' ≫ m₂) hc.symm (by rw [Category.assoc, hm₂, hp'])

  have rw₀ : Set.range (m₁ ≫ τ i j) ⊆ Set.range (V j k).ι := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨z, rfl⟩ := hp'surj.surj o
    have e1 : (p' ≫ m₁ ≫ τ i j) z = (b ≫ pP) z := by rw [h1]
    have e2 : (b ≫ e j) z = (c ≫ e k) z := by rw [hb, hc]
    simp only [Scheme.Hom.comp_apply] at e1 e2
    rw [Scheme.Opens.range_ι]
    show (m₁ ≫ τ i j) (p' z) ∈ V j k
    simp only [Scheme.Hom.comp_apply]
    rw [e1, hV, e2]
    exact ⟨_, rfl⟩
  let w₀ := IsOpenImmersion.lift (V j k).ι (m₁ ≫ τ i j) rw₀
  have hw₀ : w₀ ≫ (V j k).ι = m₁ ≫ τ i j := IsOpenImmersion.lift_fac _ _ _
  have h3 : p' ≫ w₀ ≫ τ j k = c ≫ pP :=
    hτ j k _ b c (p' ≫ w₀) (hb.trans hc.symm) (by rw [Category.assoc, hw₀, h1])
  haveI := hU
  have heq : pullback.fst p' p' ≫ c ≫ pP = pullback.snd p' p' ≫ c ≫ pP := by
    rw [← h2, pullback.condition_assoc]
  obtain ⟨h₀, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S O.toScheme FinalForm.toScheme U.left π (O.ι ≫ U.hom) p'
    (FinalForm.ι ≫ pullback.snd U.hom π) hπp hπs hS inferInstance hsq (c ≫ pP) heq
  have E : w₀ ≫ τ j k = m₂ ≫ τ i k := (huniq _ h3).trans (huniq _ h2).symm

  have rt : Set.range (x ≫ (V i j).ι) ⊆ Set.range O.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Opens.range_ι (V i j)]; exact ⟨x s, rfl⟩
    · rw [hxy, ← Scheme.Opens.range_ι (V i k)]; exact ⟨y s, rfl⟩
  let t := IsOpenImmersion.lift O.ι (x ≫ (V i j).ι) rt
  have ht : t ≫ O.ι = x ≫ (V i j).ι := IsOpenImmersion.lift_fac _ _ _
  have tx : t ≫ m₁ = x := (cancel_mono (V i j).ι).1 (by rw [Category.assoc, hm₁, ht])
  have ty : t ≫ m₂ = y := (cancel_mono (V i k).ι).1 (by rw [Category.assoc, hm₂, ht, hxy])
  have tw : w = t ≫ w₀ := (cancel_mono (V j k).ι).1 (by rw [← hw, Category.assoc, hw₀, ← Category.assoc, tx])
  rw [tw, Category.assoc, E, ← Category.assoc, ty]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem chart_transition_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ (i j : J) (V : U.left.Opens), (∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j)) → ∃ τ : V.toScheme ⟶ U.left, ∀ (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ V.toScheme), a ≫ e i = b ≫ e j → v ≫ V.ι = a ≫ pullback.fst _ _ → v ≫ τ = b ≫ pullback.fst _ _ := by
  intro R _ _ _ _ S X π hπ hs hS U hU J e he hkey i j V hV
  have hpb0 : IsPullback (pullback.fst U.hom π ∣_ V) (pullback.fst U.hom π ⁻¹ᵁ V).ι V.ι
      (pullback.fst U.hom π) := isPullback_morphismRestrict _ _
  have hpb : IsPullback (pullback.fst U.hom π ∣_ V)
      ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ pullback.snd U.hom π) (V.ι ≫ U.hom) π :=
    hpb0.paste_vert (IsPullback.of_hasPullback U.hom π)
  have hflat : Flat (V.ι ≫ U.hom) := inferInstance
  have hrange : Set.range ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i).base ⊆ Set.range (e j).base := by
    rintro _ ⟨z, rfl⟩
    have hz : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ pullback.fst U.hom π ⁻¹ᵁ V := by
      have h0 : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ Set.range (pullback.fst U.hom π ⁻¹ᵁ V).ι := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at h0
    simpa using (hV _).1 hz
  let hZ := IsOpenImmersion.lift (e j) ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i) hrange
  have hZe : hZ ≫ e j = (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  let p' := pullback.fst U.hom π ∣_ V
  have heq : pullback.fst p' p' ≫ (hZ ≫ pullback.fst U.hom π) =
      pullback.snd p' p' ≫ (hZ ≫ pullback.fst U.hom π) := by
    obtain ⟨h₂, h₂e, h₂p⟩ := hkey i j (pullback p' p') (pullback.fst p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι)
      (pullback.snd p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι) (pullback.fst p' p' ≫ hZ)
      (by simp only [Category.assoc, ← morphismRestrict_ι]; rw [pullback.condition_assoc])
      (by simp only [Category.assoc, hZe])
    have : h₂ = pullback.snd p' p' ≫ hZ := by
      rw [← cancel_mono (e j), h₂e]; simp only [Category.assoc, hZe]
    subst this
    simpa only [Category.assoc] using h₂p.symm
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S V.toScheme (pullback.fst U.hom π ⁻¹ᵁ V).toScheme U.left π
    (V.ι ≫ U.hom) p' _ hπ hs hS hflat hpb _ heq
  refine ⟨τ, fun T a b v hab hv => ?_⟩
  let a' := hpb0.lift v a hv
  have ha'1 : a' ≫ p' = v := hpb0.lift_fst _ _ _
  have ha'2 : a' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι = a := hpb0.lift_snd _ _ _
  have ha'3 : a' ≫ hZ = b := by
    rw [← cancel_mono (e j), Category.assoc, hZe, ← Category.assoc, ha'2, hab]
  rw [← ha'1, Category.assoc, hτ, ← Category.assoc, ha'3]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem inv_pullback_left_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (G' : Over Y) [GrpObj G'] {T : Over X}
    (z : T ⟶ (Over.pullback f).obj G') :
    (z⁻¹).left ≫ pullback.fst G'.hom f = z.left ≫ pullback.fst G'.hom f ≫ ι[G'].left := by
  show (z ≫ (Over.pullback f).map ι[G']).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left]
  first | exact pullback.lift_fst _ _ _ | erw [pullback.lift_fst]

theorem exists_inv_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ i : G ⟶ G, ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hsm hpb φ hφ hc
  have hfl : Flat G.hom := inferInstance
  have D := fun (W : Scheme.{0}) => GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S G.left G'.left W π G.hom β G'.hom hP hS hI hfl hpb
  have epi : ∀ {W : Scheme.{0}} (a b : G.left ⟶ W), β ≫ a = β ≫ b → a = b := by
    intro W a b hab
    obtain ⟨h₀, -, hu⟩ := D W (β ≫ a) (by rw [pullback.condition_assoc])
    exact (hu a rfl).trans (hu b hab.symm).symm
  have hw : β ≫ G.hom = G'.hom ≫ π := hpb.w
  set a₁ := pullback.fst β β
  set a₂ := pullback.snd β β
  have hσ : (a₁ ≫ G'.hom) ≫ π = (a₂ ≫ G'.hom) ≫ π := by
    simp only [Category.assoc, ← hw]; rw [pullback.condition_assoc]
  let σ : pullback β β ⟶ pullback π π := pullback.lift _ _ hσ
  let x : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G' :=
    Over.homMk (pullback.lift a₁ σ (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcx : ∀ y : Over.mk σ ⟶ (Over.pullback (pullback.fst π π)).obj G',
      y.left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β =
        (y ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
    intro y; rw [Over.comp_left, Category.assoc, ← hc]
  have h2 : (x ≫ φ.hom).left ≫ pullback.fst G'.hom (pullback.snd π π) = a₂ := by
    apply hpb.hom_ext
    · rw [Category.assoc, ← hcx x]
      show pullback.lift a₁ σ _ ≫ _ ≫ β = _
      rw [pullback.lift_fst_assoc]
      exact pullback.condition
    · rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (x ≫ φ.hom).left ≫ pullback.snd G'.hom (pullback.snd π π) = σ from Over.w (x ≫ φ.hom)]
      exact pullback.lift_snd _ _ _
  have eq : a₁ ≫ ι[G'].left ≫ β = a₂ ≫ ι[G'].left ≫ β := by
    have := hcx x⁻¹
    rw [GrpObj.inv_comp, reassoc_of% inv_pullback_left_fst, reassoc_of% inv_pullback_left_fst,
      reassoc_of% h2] at this
    simp only [x, Over.homMk_left] at this
    rwa [pullback.lift_fst_assoc] at this
  obtain ⟨h₀, hh₀, -⟩ := D G.left (ι[G'].left ≫ β) eq
  have hover : h₀ ≫ G.hom = G.hom := by
    apply epi
    rw [reassoc_of% hh₀, hw, ← Category.assoc, Over.w ι[G']]
  refine ⟨Over.homMk h₀ hover, ?_⟩
  intro T x' x₀ hx
  rw [Over.comp_left]
  show x₀.left ≫ h₀ = _
  rw [hx, Category.assoc, hh₀]
  show _ = (x' ≫ ι[G']).left ≫ β
  rw [Over.comp_left, Category.assoc]

end GlobalTheory.Mum
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GrpDescent

section Pt
variable {S X : Scheme.{0}} (G' : Over S) (f : X ⟶ S)

def ptOf {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) : T ⟶ (Over.pullback f).obj G' :=
  Over.homMk (pullback.lift a T.hom ha) (pullback.lift_snd _ _ _)

theorem ptOf_fst {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f a ha).left ≫ pullback.fst G'.hom f = a := pullback.lift_fst _ _ _

theorem ptOf_mul [GrpObj G'] {T : Over X} (w : T.left ⟶ (G' ⊗ G').left) (hw : w ≫ (G' ⊗ G').hom = T.hom ≫ f)
    (h₁ : (w ≫ (fst G' G').left) ≫ G'.hom = T.hom ≫ f) (h₂ : (w ≫ (snd G' G').left) ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f _ h₁ * ptOf G' f _ h₂).left ≫ pullback.fst G'.hom f = w ≫ μ[G'].left := by
  let U : Over.mk (T.hom ≫ f) ⟶ G' ⊗ G' := Over.homMk w hw
  have e := (isGrpPullback_pullback G' f).2 T (ptOf G' f _ h₁) (ptOf G' f _ h₂) (U ≫ fst G' G') (U ≫ snd G' G')
    (ptOf_fst G' f _ h₁).symm (ptOf_fst G' f _ h₂).symm
  rw [← e, ← MonObj.comp_mul, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rfl

end Pt

theorem mul_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ m : G ⊗ G ⟶ G, ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β := by
  intro R _ _ _ _ S π hprop hsurj hint G' _ G β hsm hβ φ hφ hdat
  haveI := hsm
  haveI : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have hflat : Flat (G ⊗ G).hom := inferInstance
  let Z' : Over (Sp R) := Over.mk ((G' ⊗ G').hom ≫ π)
  let u : Z' ⟶ G := Over.homMk ((fst G' G').left ≫ β) (by
    show ((fst G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let v : Z' ⟶ G := Over.homMk ((snd G' G').left ≫ β) (by
    show ((snd G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let p : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift u v).left
  have hp1 : p ≫ (fst G G).left = (fst G' G').left ≫ β := by
    show (lift u v ≫ fst G G).left = _
    rw [lift_fst]; rfl
  have hp2 : p ≫ (snd G G).left = (snd G' G').left ≫ β := by
    show (lift u v ≫ snd G G).left = _
    rw [lift_snd]; rfl
  have hA : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have hB : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have htop : IsPullback p (snd G' G').left (snd G G).left β := by
    refine IsPullback.of_right (h₁₂ := (fst G G).left) (h₂₂ := G.hom) ?_ hp2 hB
    rw [hp1, hβ.w]
    exact hA.paste_horiz hβ
  have hpb : IsPullback p (G' ⊗ G').hom (G ⊗ G).hom π := by
    have h := htop.paste_vert hβ
    rwa [Over.w (snd G' G'), Over.w (snd G G)] at h

  have hepi : ∀ {W : Scheme.{0}} (a b : (G ⊗ G).left ⟶ W), p ≫ a = p ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ W π _ p _ hprop hsurj hint hflat hpb (p ≫ a)
      (by rw [← Category.assoc, pullback.condition, Category.assoc])
    exact (hc a rfl).trans (hc b hab.symm).symm

  have heq : pullback.fst p p ≫ μ[G'].left ≫ β = pullback.snd p p ≫ μ[G'].left ≫ β := by
    set f₁ := pullback.fst p p
    set f₂ := pullback.snd p p
    have hf : f₁ ≫ p = f₂ ≫ p := pullback.condition
    have hs : (f₁ ≫ (G' ⊗ G').hom) ≫ π = (f₂ ≫ (G' ⊗ G').hom) ≫ π := by
      rw [Category.assoc, Category.assoc, ← hpb.w, ← Category.assoc, hf, Category.assoc]
    let σ := pullback.lift _ _ hs
    let T₀ : Over (pullback π π) := Over.mk σ
    have hw₁ : f₁ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.fst π π := (pullback.lift_fst _ _ hs).symm
    have hw₂ : f₂ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.snd π π := (pullback.lift_snd _ _ hs).symm

    have htr : ∀ (a₁ a₂ : T₀.left ⟶ G'.left) (h₁ : a₁ ≫ G'.hom = T₀.hom ≫ pullback.fst π π)
        (h₂ : a₂ ≫ G'.hom = T₀.hom ≫ pullback.snd π π), a₁ ≫ β = a₂ ≫ β →
        ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom = ptOf G' (pullback.snd π π) a₂ h₂ := by
      intro a₁ a₂ h₁ h₂ hb
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · apply hβ.hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, ← hdat, ← Category.assoc, ptOf_fst, ptOf_fst, hb]
        · rw [Category.assoc, pullback.condition, ptOf_fst, h₂, ← Category.assoc]
          exact congrArg (· ≫ pullback.snd π π) (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom))
      · exact (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom)).trans (Over.w (ptOf G' (pullback.snd π π) a₂ h₂)).symm
    have hb₁ : (f₁ ≫ (fst G' G').left) ≫ β = (f₂ ≫ (fst G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp1, ← Category.assoc, hf, Category.assoc]
    have hb₂ : (f₁ ≫ (snd G' G').left) ≫ β = (f₂ ≫ (snd G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp2, ← Category.assoc, hf, Category.assoc]
    have k₁ : (f₁ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have k₂ : (f₁ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have l₁ : (f₂ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have l₂ : (f₂ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have e₁ := ptOf_mul G' (pullback.fst π π) (T := T₀) f₁ hw₁ k₁ k₂
    have e₂ := ptOf_mul G' (pullback.snd π π) (T := T₀) f₂ hw₂ l₁ l₂
    have hAB : (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ * ptOf G' (pullback.fst π π) (T := T₀) _ k₂) ≫ φ.hom =
        ptOf G' (pullback.snd π π) (T := T₀) _ l₁ * ptOf G' (pullback.snd π π) (T := T₀) _ l₂ := by
      refine ((IsMonHom.monoidHom φ.hom T₀).map_mul _ _).trans ?_
      show (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ ≫ φ.hom) * (ptOf G' (pullback.fst π π) (T := T₀) _ k₂ ≫ φ.hom) = _
      rw [htr _ _ k₁ l₁ hb₁, htr _ _ k₂ l₂ hb₂]
    rw [← Category.assoc f₁, ← e₁, ← Category.assoc f₂, ← e₂, ← hAB, Over.comp_left]
    simp only [Category.assoc]
    rw [hdat]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ _ π _ p _ hprop hsurj hint hflat hpb (μ[G'].left ≫ β) heq
  have hover : h₀ ≫ G.hom = (G ⊗ G).hom := by
    apply hepi
    rw [← Category.assoc, hh₀, Category.assoc, hβ.w, ← Category.assoc, Over.w μ[G'], hpb.w]
  refine ⟨Over.homMk h₀ hover, fun T x y x₀ y₀ hx hy => ?_⟩
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ p := by
    apply hB.hom_ext
    · rw [Category.assoc, hp1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, hx]
    · rw [Category.assoc, hp2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, hy]
  rw [Over.comp_left, hl]
  change ((lift x y).left ≫ p) ≫ h₀ = _
  rw [Category.assoc, hh₀, Hom.mul_def, Over.comp_left, Category.assoc]

end GlobalTheory.GrpDescent
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

theorem pullback_one_left_fst {S P : Scheme.{0}} (f : P ⟶ S) (G' : Over S) [GrpObj G'] :
    (η[(Over.pullback f).obj G'] : _ ⟶ _).left ≫ pullback.fst G'.hom f = f ≫ η[G'].left := by
  simp [Functor.monObjObj]

theorem descend_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R))
    (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom →
    pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β →
    ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S),
      (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hβ φ hφ hc
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_id_snd
  have hfl : Flat (𝟙 (Sp R)) := inferInstance

  have heq : pullback.fst π π ≫ (η[G'].left ≫ β) = pullback.snd π π ≫ (η[G'].left ≫ β) := by
    have h1 := pullback_one_left_fst (pullback.fst π π) G'
    have h2 := pullback_one_left_fst (pullback.snd π π) G'
    have hu : (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left =
        (η : _ ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    calc pullback.fst π π ≫ (η[G'].left ≫ β)
        = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β := by
          rw [reassoc_of% h1]
      _ = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left ≫
            pullback.fst G'.hom (pullback.snd π π) ≫ β := by rw [hc]
      _ = pullback.snd π π ≫ (η[G'].left ≫ β) := by rw [reassoc_of% hu, reassoc_of% h2]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S G.left π (𝟙 _) π (𝟙 S) hP hS hI hfl sq _ heq

  have hepi : ∀ {W : Scheme.{0}} (a b : Sp R ⟶ W), π ≫ a = π ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc'⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S W π (𝟙 _) π (𝟙 S) hP hS hI hfl sq (π ≫ a)
      (by rw [pullback.condition_assoc])
    exact (hc' a rfl).trans (hc' b hab.symm).symm
  have hsec : h₀ ≫ G.hom = 𝟙 (Sp R) := by
    apply hepi
    rw [reassoc_of% hh₀, hβ.w]
    simp
  refine ⟨Over.homMk h₀ (by simpa using hsec), fun T => ?_⟩
  simp [Hom.one_def]
  rw [hh₀]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivLocus_closed_of_relAmple : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) :=
  GlobalTheory.T.isClosed_trivialLocus_rigidified_bundle

end GlobalTheory.TrivLocus
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.polarisation_kernel_killed_over_dvr_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) → ∀ m : ℕ, (∀ (T : Over (Sp L)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ m = 1) → ∀ (T : Over (Sp W)) (x : T ⟶ G), (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ m = 1 := by
  first | exact @GlobalTheory.KerExt.kernel_killed | exact GlobalTheory.KerExt.kernel_killed | (intros; apply GlobalTheory.KerExt.kernel_killed <;> assumption)
end
