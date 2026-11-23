module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem isUnit_res_of_le_basicOpen' {X : Scheme.{0}} {U V : X.Opens} (f : Γ(X, U)) (hVU : V ≤ U)
    (h : V ≤ X.basicOpen f) : IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  have e : X.presheaf.map (homOfLE hVU).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ X.presheaf.map (homOfLE h).op := by
    rw [← Functor.map_comp]; rfl
  rw [e]
  exact hu

theorem psiUnitOn_of_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ) (y : D.X) (U : Set (Sp R)) (a b : R), (g y : FractionRing R) * algebraMap R (FractionRing R) a = algebraMap R (FractionRing R) b → (∀ p ∈ U, a ∉ (p : PrimeSpectrum R).asIdeal ∧ b ∉ (p : PrimeSpectrum R).asIdeal) → PsiUnitOn (GlobalTheory.PolDeg.rescale D g) y U → PsiUnitOn D y U := by
  intro R _ _ D g y U a b hab hU hR j V hV hVU hj h
  obtain ⟨r₀, hr₀u, hr₀⟩ := hR j V hV hVU hj h
  have hle : (V : (Sp R).Opens) ≤ ⊤ := le_top
  have hVa : V ≤ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
    intro x hx
    show x ∈ ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) : Set (Sp R))
    rw [basicOpen_eq_of_affine]
    exact (hU x (hVU hx)).1
  have hVb : V ≤ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b) := by
    intro x hx
    show x ∈ ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b) : Set (Sp R))
    rw [basicOpen_eq_of_affine]
    exact (hU x (hVU hx)).2
  obtain ⟨Au, hAu⟩ := isUnit_res_of_le_basicOpen' _ hle hVa
  obtain ⟨Bu, hBu⟩ := isUnit_res_of_le_basicOpen' _ hle hVb
  refine ⟨Au.val * r₀ * (Bu⁻¹ : Γ(Sp R, V)ˣ).val, ((Au.isUnit.mul hr₀u).mul (Bu⁻¹).isUnit), ?_⟩
  set K := FractionRing R
  set c : K →+* Γ((TK R).left, jK R ⁻¹ᵁ V) :=
    ((TK R).left.presheaf.map (homOfLE (le_top : jK R ⁻¹ᵁ V ≤ ⊤)).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    with hc
  have hnat : ∀ x : R, ((jK R).app V).hom ((Sp R).presheaf.map (homOfLE hle).op |>.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) = c (algebraMap R K x) := by
    intro x
    have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))
      ((jK R).naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [e]
    have e2 := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
    rw [hc, RingHom.comp_apply, e2]
    rfl
  have hA : ((jK R).app V).hom Au.val = c (algebraMap R K a) := by rw [hAu]; exact hnat a
  have hB : ((jK R).app V).hom Bu.val = c (algebraMap R K b) := by rw [hBu]; exact hnat b
  have hG : ∀ (W : (TK R).left.Opens) (h₁ : jK R ⁻¹ᵁ V ≤ W) (h₂ : W ≤ ⊤), ((TK R).left.presheaf.map (homOfLE h₁).op).hom (res h₂ (unitOn (g y))).val = c (g y) := by
    intro W h₁ h₂
    show ((TK R).left.presheaf.map (homOfLE h₁).op).hom (((TK R).left.presheaf.map (homOfLE h₂).op).hom (unitOn (g y)).val) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  have hBB : ((jK R).app V).hom Bu.val * ((jK R).app V).hom (Bu⁻¹ : Γ(Sp R, V)ˣ).val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hab' : c (algebraMap R K a) * c (g y) = c (algebraMap R K b) := by
    rw [← map_mul, _root_.mul_comm, hab]
  rw [map_mul, map_mul, hr₀]
  show _ * (((TK R).left.presheaf.map (homOfLE h).op).hom (_ * _)) * _ = _
  erw [map_mul]
  rw [hG, hA]
  rw [← hB] at hab'
  rw [← _root_.mul_assoc, hab', _root_.mul_right_comm, hBB, _root_.one_mul]

end GlobalTheory.PolDeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem spMap_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem gen_unique_of_eq {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {Ix : Type} [Fintype Ix]
    {φ φ' : Ix → (Y ⟶ X)} {ε : Ix → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (hφ : φ' = φ) {u : LB.Gen (LB.LinComb M φ' ε)}
    {u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  subst hφ
  exact gen_unique hM p e he hp hu hu' h Z r z J hJ

theorem gen_values_mem : ∀ (V₁ W₀ : Type) [CommRing V₁] [CommRing W₀] (ib : W₀ →+* V₁) (A : Over (Sp V₁)) [GrpObj A],
    IsAbelianScheme A → ∀ (B₀ : Over (Sp W₀)) (β : A.left ⟶ B₀.left), IsPullback β A.hom B₀.hom (spMap ib) →
    ∀ (M₀ : LB B₀.left), M₀.IsLB → ∀ (Ix : Type) [Fintype Ix] (φ : Ix → (A.left ⟶ B₀.left))
    (ψ : Ix → (B₀.left ⟶ B₀.left)), (∀ k, φ k = β ≫ ψ k) → ∀ (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb M₀ φ ε)),
    t.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    (∀ a, ev (ib a) ∈ k₀) → ∀ x₁ : Sp K ⟶ A.left, x₁ ≫ A.hom = spMap ev → DefOver k₀ (x₁ ≫ β) →
    (∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → val t x₁ z J = 1) →
    ∀ x : Sp K ⟶ A.left, x ≫ A.hom = spMap ev → DefOver k₀ (x ≫ β) →
    ∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → ∃ c ∈ k₀, (val t x z J).val = toStk z c := by
  intro V₁ W₀ _ _ ib A _ hA B₀ β hβ M₀ hM₀ Ix _ φ ψ hφ ε t ht K _ _ ev k₀ hk₀ hk x₁ hx₁ hd₁ h1 x hx hd z J hJ
  classical
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  let v : (Sp K ⟶ A.left) → ((Sp K ⟶ B₀.left) → M₀.ι) → K := fun x J =>
    valF x (LB.wchart M₀ φ (fun k => J (x ≫ φ k))) ((genSec t ht).f (fun k => J (x ≫ φ k)))
  have hv : ∀ x z J, Good M₀ z J → (val t x z J).val = toStk z (v x J) := fun x z J hJ =>
    (sval_genSec t ht x z hJ).symm.trans (toStk_valF_gs x _ z (hJ.mem φ x) _).symm
  have hfix : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) →
      ∀ k, spMap σ.toRingHom ≫ x ≫ φ k = x ≫ φ k := by
    intro x hd σ hσ k
    obtain ⟨P₀, hP₀⟩ := hd
    rw [hφ k, ← Category.assoc x, ← hP₀, Category.assoc, ← Category.assoc (spMap σ.toRingHom),
      spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  have hvσ : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∀ z J, Good M₀ z J →
      (val t (spMap σ.toRingHom ≫ x) z J).val = toStk z (σ (v x J)) := fun x hd σ hσ z J hJ =>
    (sval_genSec t ht _ z hJ).symm.trans (sval_spMap _ σ.toRingHom x z hJ (hfix x hd σ hσ))
  have hsurj : Function.Surjective (pullback.snd A.hom (spMap ev)).appTop.hom :=
    fun w => TLinPf.const_pullback GlobalTheory.SemiRigid.globalFns (spMap ev) A hA w
  have key : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ (v x J) = v x J := by
    intro σ hσ
    have hc : (pullback.fst A.hom (spMap ev) ≫ β) ≫ B₀.hom =
        (pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev) ≫ spMap ib := by
      simp only [Category.assoc]
      rw [hβ.w, pullback.condition_assoc, spMap_two, spMap_conj k₀ _ hf σ hσ]
    obtain ⟨l, hl1, hl2⟩ : ∃ l : pullback A.hom (spMap ev) ⟶ A.left, l ≫ β = pullback.fst A.hom (spMap ev) ≫ β ∧
        l ≫ A.hom = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev :=
      ⟨hβ.lift _ _ hc, hβ.lift_fst _ _ hc, hβ.lift_snd _ _ hc⟩
    obtain ⟨σt, hs1, hs2⟩ : ∃ σt : pullback A.hom (spMap ev) ⟶ pullback A.hom (spMap ev),
        σt ≫ pullback.fst A.hom (spMap ev) = l ∧
        σt ≫ pullback.snd A.hom (spMap ev) = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom :=
      ⟨pullback.lift l _ (by rw [hl2, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hσβ : σt ≫ pullback.fst A.hom (spMap ev) ≫ β = pullback.fst A.hom (spMap ev) ≫ β := by
      rw [reassoc_of% hs1, hl1]
    have hpt : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) →
        pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) ≫ σt =
          spMap σ.toRingHom ≫ pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) := by
      intro y hy hd
      obtain ⟨P₀, hP₀⟩ := hd
      apply pullback.hom_ext
      · simp only [Category.assoc, hs1, pullback.lift_fst]
        apply hβ.hom_ext
        · simp only [Category.assoc, hl1, pullback.lift_fst_assoc]
          rw [← hP₀, ← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
        · simp only [Category.assoc, hl2, pullback.lift_snd_assoc, Category.id_comp, hy]
      · simp only [Category.assoc, hs2, pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd, Category.comp_id]
    let tK := LB.pullGen M₀ φ ε t (pullback.fst A.hom (spMap ev))
    have htK : tK.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
    have hu : (LB.pullGen M₀ _ ε tK σt).IsGen := DVR.pullGen_isGen _ _ _ _ htK _
    have hval : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) → ∀ z J, Good M₀ z J →
        val (LB.pullGen M₀ _ ε tK σt) (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J =
          val t (spMap σ.toRingHom ≫ y) z J := by
      intro y hy hd z J hJ
      rw [val_pull hJ, hpt y hy hd, val_pull hJ, Category.assoc, pullback.lift_fst]
    have hvalK : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev) z J, Good M₀ z J →
        val tK (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J = val t y z J := by
      intro y hy z J hJ
      rw [val_pull hJ, pullback.lift_fst]
    have huniq := gen_unique_of_eq hM₀ (pullback.snd A.hom (spMap ev))
      (pullback.lift x₁ (𝟙 _) (by rw [hx₁, Category.id_comp])) (pullback.lift_snd _ _ _) hsurj
      (funext fun k => by rw [hφ k]; exact (reassoc_of% hσβ) (ψ k)) hu htK (fun y J hJ => by
        rw [hval x₁ hx₁ hd₁ y J hJ, hvalK x₁ hx₁ y J hJ, h1 y J hJ]
        apply Units.ext
        have e1 := hv x₁ y J hJ
        rw [h1 y J hJ, Units.val_one, ← map_one (toStk y)] at e1
        rw [hvσ x₁ hd₁ σ hσ y J hJ, ← (toStk y).injective e1, map_one, map_one, Units.val_one])
      (Sp K) (pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])) z J hJ
    rw [hval x hx hd z J hJ, hvalK x hx z J hJ] at huniq
    have e2 := congrArg Units.val huniq
    rw [hvσ x hd σ hσ z J hJ, hv x z J hJ] at e2
    exact (toStk z).injective e2
  refine ⟨v x J, ?_, hv x z J hJ⟩
  apply mem_of_finite_conj k₀ hk₀
  apply (Set.finite_singleton (v x J)).subset
  rintro b ⟨σ, hσ, rfl⟩
  exact key σ hσ

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RatioScalar

theorem scalar : ∀ {O : Type} [CommRing O] [StarRing O] {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module O Q.X] (oQ : Q.OAct O) (g : Q.X → (FractionRing V)ˣ) (o' : letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; (GlobalTheory.PolDeg.rescale Q g).OAct O), (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; o'.onB = oQ.onB) → Q.TauBimult → (GlobalTheory.PolDeg.rescale Q g).TauBimult → ∀ w0 : O, TraceFormTwistIso Q oQ w0 → (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; TraceFormTwistIso (GlobalTheory.PolDeg.rescale Q g) o' w0) → ∃ q : Q.X → Q.X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : O) a b, q (x • a) b = q a (star x • b)) ∧ ∀ y, (g y)⁻¹ = q y (w0 • y) := by
  intro O _ _ V _ _ Q _ oQ g o' ho hB hB' w0 hW hW'
  obtain ⟨hs, hd⟩ := GlobalTheory.RescaleForm.main Q oQ w0 g hB hW hB' o' ho hW'
  exact ⟨fun a b => (g (a + b) * (g a)⁻¹ * (g b)⁻¹)⁻¹, hs.inv.symm, hs.inv.add_left, hs.inv.bal,
    fun y => congrArg (·⁻¹) (hd y)⟩

end GlobalTheory.RatioScalar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinDataTriple


open GlobalTheory.LinearUnifIso in
theorem act_comm_noeth : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ _ I hI D D' A A' G G' _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory.LinDataTriple

theorem GlobalTheory.triple_iso_of_linear_data_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (t t' : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg (RingHom.id V) P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) → (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (P.oD.onB.act x)) → Nonempty (SABMap t' t (𝟙 _)) := by
  intro E _ _ _ H V _ _ _ hB t t' P P' hD hx hB'
  letI := H.starRing
  have hR : AdmBase V (maximalIdeal V) := hB.1
  have := hR.1
  obtain ⟨ψ, bc, -, hψm, hbcm, hbc', hP, -⟩ := GlobalTheory.unif_determined_by_data_normal V hR P.D P.A t.G t.semi P.U
    P'.D P'.A t'.G t'.semi P'.U hD
  have hL := GlobalTheory.firstFiveLaws.1
  have hBl : ∀ x, (P'.oD.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) =
      (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) ≫ (P.oD.onB.act x).left := by
    intro x
    have e := congrArg (fun c => c.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) (hB' x)
    simp only [Over.comp_left, Category.assoc] at e
    rw [e]
    exact congrArg (hD.e.hom.left ≫ ·) (pullback.lift_fst _ _ _)
  have hact := GlobalTheory.LinDataTriple.act_comm_noeth hL.globalFns V (maximalIdeal V) rfl P.D P'.D P.A P'.A t.G t'.G
    t'.semi P.U P'.U hD bc hbcm hP (𝓞 E) P.oD P'.oD P.oA P'.oA t.act.toRingAct t'.act.toRingAct P.lin P'.lin hx hBl
  have hact' : ∀ a, (t'.act.act a).left ≫ ψ.hom.left = ψ.hom.left ≫ (t.act.act a).left := by
    intro a
    have e := congrArg (fun c => c.left ≫ pullback.fst t.G.hom (specOf (RingHom.id V))) (hact a)
    simp only [Over.comp_left, Category.assoc] at e
    rw [← hbc', Category.assoc]
    exact e.trans (congrArg (bc.hom.left ≫ ·) (pullback.lift_fst _ _ _))
  have hLB : LBIso t'.PP.L (t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hP.lg
    rw [← P.bundle, ← P'.bundle, ← hbc']
    exact ⟨w, hw⟩
  have := P'.U.gen_hom
  have hp : IsProper (pullback.snd t'.G.hom (jK V)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (isGrpPullback_of_iso P'.U.gen).1 P'.A.isAb.proper
  have hab := GlobalTheory.RigCube.genericPoints_subset_abLocus t'.G t'.semi hp
  obtain ⟨ν, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H (Sp V) (Sp V) t t' (𝟙 _) ψ.hom.left ⟨inferInstance, hab⟩
    (isGrpPullback_of_iso ψ) hact' hLB
  exact ⟨ν⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwistCP

theorem exists_cp_transl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hG U a ha
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_generator_lineBundle_pullback_spec_localRing R G.left M.L.L M.L.isLB a.left
  obtain ⟨P, hPL, h2, h3⟩ := GlobalTheory.T.exists_translate_cubicalSymmetricLineBundle_twoTorsion (Sp R) G M a ha ρ hρ
  refine ⟨P, ?_, GlobalTheory.T.translatedUniformisationBundle_even_closedFibreTorus R hR D A G hG U a ha P hPL h2 h3⟩
  rw [hPL]
  exact GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _)

end GlobalTheory.MumTwistCP
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem thetaNZ_of_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P → GlobalTheory.LN.ThetaNZ G U.P.L.L := by
  intro R _ _ _ hB D A G _ _ U hE
  obtain ⟨V, _, _, _, φ, D', A', G', _, _, U', U₀, F, C, hV, hφ, hc, hU⟩ := GlobalTheory.T.exists_completeDVR_comparison_preUniformised R hB D A G U hE
  obtain ⟨σ, f, g, q, hq, hf, hfg, hg0, hgm⟩ := GlobalTheory.T.exists_coefficientData_of_nonzero_section R hB D A G U V φ D' A' G' U' U₀ F C hV hφ hc hU
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_section_quotient_of_expansion_dvd R hB D A G U σ f g q hq hf hfg
  have := U.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint G _ (GlobalTheory.T.exists_mem_nonzeroLocus_of_weightZero_expansion R D A G U τ g hτ hg0 hgm)

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramTorsPull

theorem torsion_fixed_unramified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D A G _ _ hG U W hW V _ _ _ φ hV hφ hcl n hn hnu j
  obtain ⟨hdvr, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (IsLocalization.map (FractionRing V) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ) :
        FractionRing R →+* FractionRing V)).toAlgebra
  have hc : ∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r)) := fun r => by
    show algebraMap (FractionRing V) _ (IsLocalization.map _ _ _ (algebraMap R _ r)) = _
    rw [IsLocalization.map_eq]
  have hk : IsUnit ((n ^ j : ℕ) : V) := by rw [Nat.cast_pow]; exact hnu.pow j
  obtain ⟨T₁, h₁, hb⟩ := GlobalTheory.T.quotientPoints_firstCoordinate_unramified_subring R D.toPre V φ hV hc (n ^ j) hk
  obtain ⟨T', h₂, hQ⟩ := GlobalTheory.T.torsionPairs_fixed_over_unramified_extension R hR D W hW V φ hV hφ hcl hc (n ^ j) hk T₁ h₁ hb
  have hT := h₁.trans h₂
  have hmem := hT.mem
  obtain ⟨hdvr', f, hf, hirr⟩ := hT
  refine ⟨T', hdvr', f, hf, hirr, fun σ hσ x hx => ?_⟩
  exact GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed R hR D A G hG U V φ hc (n ^ j) (Nat.one_le_pow _ _ (by omega)) σ (fun v => hσ _ (hmem v)) (hQ σ hσ) x hx

end GlobalTheory.UnramTorsPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.generic_chart_functions_fractions_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens) (U : M.S.Opens), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → Function.Injective (α.app W).hom ∧ ∀ b : Γ(Y, α ⁻¹ᵁ W), ∃ c s : Γ(G.left, W), IsUnit ((α.app W).hom s) ∧ b * (α.app W).hom s = (α.app W).hom c := by
  first | exact @GlobalTheory.Mum.injective_and_exists_frac_genericChart | exact GlobalTheory.Mum.injective_and_exists_frac_genericChart | (intros; apply GlobalTheory.Mum.injective_and_exists_frac_genericChart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.labels_induced_all_embeddings_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∀ (hD : IsPullDeg φ D.toPre D'.toPre) (j : ℕ), (∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧  ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x') → Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.AllEmb.induces_of_one_embedding | exact GlobalTheory.Mum.AllEmb.induces_of_one_embedding | (intros; apply GlobalTheory.Mum.AllEmb.induces_of_one_embedding <;> assumption)
end
