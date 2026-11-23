module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.RingPoint

theorem toSpec_appTop {Z : Scheme.{0}} {D : Type} [CommRing D] (θ : D →+* Γ(Z, ⊤)) (a : Γ(Spec (CommRingCat.of D), ⊤)) :
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop.hom a = θ ((Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom a) := by
  have h : (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of D)).hom ≫ CommRingCat.ofHom θ := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ : CommRingCat.of D ⟶ Γ(Z, ⊤))
  exact congrArg (fun q => q.hom a) h

theorem exists_ringPoint {S : Scheme.{0}} (Y : Over S) [IsAffine Y.left] (D : Type) [CommRing D]
    (κ : Γ(Y.left, ⊤) →+* D) : ∃ (U : Over S) (y₀ : U ⟶ Y) (e : Γ(U.left, ⊤) ≃+* D), IsAffine U.left ∧
      (∀ b, e (y₀.left.appTop.hom b) = κ b) ∧
      ∀ (Z : Over S) (y : Z ⟶ Y) (θ : D →+* Γ(Z.left, ⊤)), (∀ b, θ (κ b) = y.left.appTop.hom b) →
        ∃ σ : Z ⟶ U, σ ≫ y₀ = y ∧ ∀ a, σ.left.appTop.hom a = θ (e a) := by
  let p : Spec (CommRingCat.of D) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom κ : Γ(Y.left, ⊤) ⟶ CommRingCat.of D) ≫ Y.left.isoSpec.inv
  have hp : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (p.appTop.hom b) = κ b := fun b => by
    have h : p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom = CommRingCat.ofHom κ := by
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      simp
    exact congrArg (fun q => q.hom b) h
  refine ⟨Over.mk (p ≫ Y.hom), Over.homMk p rfl, (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv,
    inferInstanceAs (IsAffine (Spec _)), hp, fun Z y θ hθ => ?_⟩
  have h : (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ≫ p = y.left := by
    refine ext_of_isAffine ?_
    ext b
    rw [Scheme.Hom.comp_appTop]
    exact (toSpec_appTop θ _).trans ((congrArg θ (hp b)).trans (hθ b))
  refine ⟨Over.homMk (Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) ?_, Over.OverMorphism.ext h, toSpec_appTop θ⟩
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.hom) h).trans (Over.w y))

def strMap {A : Type} [CommRing A] (Z : Over (Spec (CommRingCat.of A))) : A →+* Γ(Z.left, ⊤) :=
  Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_strMap {A : Type} [CommRing A] {Z Y : Over (Spec (CommRingCat.of A))} (y : Z ⟶ Y) (a : A) :
    y.left.appTop.hom (strMap Y a) = strMap Z a := by
  rw [strMap, strMap, ← Over.w y, Scheme.Hom.comp_appTop]; rfl

theorem exists_comp_red_iff {A : Type} [CommRing A] (J : Ideal A) (Z : Over (Spec (CommRingCat.of A))) :
    (∃ s, s ≫ red J = Z.hom) ↔ ∀ a ∈ J, strMap Z a = 0 := by
  have nat : ∀ a, (red J).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ J))).inv.hom (Ideal.Quotient.mk J a) := fun a =>
    congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk J) : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J))).symm
  constructor
  · rintro ⟨s, hs⟩ a ha
    rw [strMap, ← hs, Scheme.Hom.comp_appTop]
    change s.appTop.hom ((red J).appTop.hom _) = 0
    rw [nat, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]
  · intro h
    refine ⟨Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (strMap Z) h)), ext_of_isAffine ?_⟩
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of A)).inv]
    ext a
    rw [Scheme.Hom.comp_appTop]
    refine (congrArg _ (nat a)).trans ((toSpec_appTop _ _).trans ?_)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl

end GlobalTheory.UU.RingPoint
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem torus_stable_of_surjective {S S' : Scheme.{0}} (f : S' ⟶ S) [Surjective f]
    (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] (G₀ : Over S') [GrpObj G₀]
    (F : G₀.left ⟶ G.left) (hF : IsGrpPullback G₀ G f F)
    (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G) (hi : TorusCompat f F i₀ i)
    (W : G.left.Opens)
    (hW : (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤
      ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W)) :
    (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  rw [torusCompat_iff] at hi
  let P : Over S := splitTorus S X ⊗ G
  let p : pullback P.hom f ⟶ P.left := pullback.fst P.hom f
  let Z₀ : Over S' := Over.mk (pullback.snd P.hom f)
  have hT := SplitTorus.isPullback_bcMap f X
  have w₁ : (p ≫ (fst (splitTorus S X) G).left) ≫ (splitTorus S X).hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  have w₂ : (p ≫ (snd (splitTorus S X) G).left) ≫ G.hom = pullback.snd P.hom f ≫ f := by
    rw [Category.assoc, Over.w]; exact pullback.condition
  let t₀ : Z₀ ⟶ splitTorus S' X := Over.homMk (hT.lift _ _ w₁) (hT.lift_snd _ _ w₁)
  let g₀ : Z₀ ⟶ G₀ := Over.homMk (hF.1.lift _ _ w₂) (hF.1.lift_snd _ _ w₂)
  have ht₀ : t₀.left ≫ SplitTorus.bcMap f X = p ≫ (fst (splitTorus S X) G).left := hT.lift_fst _ _ w₁
  have hg₀ : g₀.left ≫ F = p ≫ (snd (splitTorus S X) G).left := hF.1.lift_fst _ _ w₂
  let ρ : Over.mk (Z₀.hom ≫ f) ⟶ P := Over.homMk p pullback.condition
  have h1 : (ρ ≫ fst (splitTorus S X) G ≫ i).left = (t₀ ≫ i₀).left ≫ F := by
    change _ = (t₀.left ≫ i₀.left) ≫ F
    rw [Category.assoc, ← hi, ← Category.assoc t₀.left, ht₀, Category.assoc]; rfl
  have h2 : (ρ ≫ snd (splitTorus S X) G).left = g₀.left ≫ F := hg₀.symm
  have h3 := hF.2 Z₀ (t₀ ≫ i₀) g₀ _ _ h1 h2
  let l : Z₀ ⟶ splitTorus S' X ⊗ G₀ := lift t₀ g₀
  have h4 : p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left =
      l.left ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀).left ≫ F := by
    have e : l ≫ ((fst (splitTorus S' X) G₀ ≫ i₀) * snd _ G₀) = (t₀ ≫ i₀) * g₀ := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    rw [← Category.assoc, ← Over.comp_left, e, ← h3, ← MonObj.comp_mul]; rfl
  have h5 : p ≫ (snd (splitTorus S X) G).left = l.left ≫ (snd (splitTorus S' X) G₀).left ≫ F := by
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hg₀]
  have h6 : (p ≫ (snd (splitTorus S X) G).left) ⁻¹ᵁ W ≤
      (p ≫ ((fst (splitTorus S X) G ≫ i) * snd _ G).left) ⁻¹ᵁ W := by
    rw [h4, h5]
    exact fun z hz => hW hz
  intro x hx
  obtain ⟨z, rfl⟩ := p.surjective x
  exact h6 hx

theorem torus_stable_of_red : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G), TorusCompat (red J) F i₀ i → ∀ W : G.left.Opens, (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤ ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) → (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by
  intro A _ J hJ X _ G _ G₀ _ F hF i₀ i hi W hW
  haveI := surjective_red hJ
  exact torus_stable_of_surjective (red J) X G G₀ F hF i₀ i hi W hW

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem ker_app_eq_map_appLE_of_isPullback {Y Z : Scheme.{0}} {A C : CommRingCat.{0}}
    {β : A ⟶ C} (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem isPullback_red_of_ker_app_le_map (A : Type) [CommRing A] (J : Ideal A)
    (B₀ B : Scheme.{0}) (j : B₀ ⟶ B) (s₀ : B₀ ⟶ Spec (CommRingCat.of (A ⧸ J)))
    (s : B ⟶ Spec (CommRingCat.of A)) (hj : IsClosedImmersion j) (w : j ≫ s = s₀ ≫ red J)
    (hloc : ∀ b : B, ∃ V : B.Opens, b ∈ V ∧ IsAffineOpen V ∧ RingHom.ker (j.app V).hom ≤
      J.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appLE ⊤ V le_top).hom) :
    IsPullback j s₀ s (red J) := by
  have hr : IsClosedImmersion (red J) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hp : IsClosedImmersion (pullback.fst s (red J)) := inferInstance
  have hl : pullback.lift j s₀ w ≫ pullback.fst s (red J) = j := pullback.lift_fst _ _ _
  have hker : j.ker = (pullback.fst s (red J)).ker := by
    refine le_antisymm ?_ ?_
    · choose V hb hV hle using hloc
      have hcov : ⨆ b, ((⟨V b, hV b⟩ : B.affineOpens) : B.Opens) = ⊤ :=
        eq_top_iff.2 fun b _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨b, hb b⟩
      refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun b ↦ ⟨V b, hV b⟩) hcov fun b ↦ ?_
      rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
      have e := ker_app_eq_map_appLE_of_isPullback
        (β := CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective
        (IsPullback.of_hasPullback s (red J)) (hV b)
      rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at e
      exact (hle b).trans e.ge
    · have := (pullback.lift j s₀ w).le_ker_comp (pullback.fst s (red J))
      rwa [hl] at this
  have := IsClosedImmersion.isIso_of_ker_eq j (pullback.fst s (red J)) _ hl hker
  exact .of_iso_pullback ⟨w⟩ (asIso (pullback.lift j s₀ w)) hl (pullback.lift_snd _ _ _)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits TensorProduct Function

namespace GlobalTheory
namespace DualCokernelFlat

section Modules

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem dual_baseChange_surjective (hs : Surjective (algebraMap A B)) (M : Type) [AddCommGroup M]
    [Module A M] [Module.Projective A M] :
    Surjective (Module.Dual.baseChange B : Module.Dual A M → Module.Dual B (B ⊗[A] M)) := by
  intro g
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Algebra.linearMap A B)
    (g.restrictScalars A ∘ₗ TensorProduct.mk A B M 1) hs
  refine ⟨f, ?_⟩
  ext x
  have := LinearMap.congr_fun hf x
  simpa [Algebra.algebraMap_eq_smul_one] using this

theorem dual_baseChange_eq_zero_iff (M : Type) [AddCommGroup M]
    [Module A M] [Module.Free A M] [Module.Finite A M] (f : Module.Dual A M) :
    Module.Dual.baseChange B f = 0 ↔
      f ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M)) := by
  constructor
  · intro h
    let b := Module.Free.chooseBasis A M
    rw [← b.sum_dual_apply_smul_coord f]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have := LinearMap.congr_fun h (1 ⊗ₜ b i)
    simpa [RingHom.mem_ker, Algebra.algebraMap_eq_smul_one] using this
  · intro h
    refine Submodule.smul_induction_on h (fun r hr x _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, ← algebraMap_smul B r, RingHom.mem_ker.mp hr, zero_smul]
    · rw [map_add (f := _), hx, hy, add_zero]

theorem dual_baseChange_dualMap {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (a : M →ₗ[A] N) (f : Module.Dual A N) :
    Module.Dual.baseChange B (a.dualMap f) =
      (a.baseChange B).dualMap (Module.Dual.baseChange B f) := by
  ext x
  simp

theorem mem_sup_of_exact (hs : Surjective (algebraMap A B)) {M₀ M₁ M₂ : Type}
    [AddCommGroup M₀] [Module A M₀] [Module.Free A M₀] [Module.Finite A M₀]
    [AddCommGroup M₁] [Module A M₁] [Module.Free A M₁] [Module.Finite A M₁]
    [AddCommGroup M₂] [Module A M₂] [Module.Free A M₂] (a : M₀ →ₗ[A] M₁) (b : M₁ →ₗ[A] M₂)
    (h : Exact (b.baseChange B).dualMap (a.baseChange B).dualMap) (x : Module.Dual A M₁)
    (hx : a.dualMap x ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₀))) :
    x ∈ LinearMap.range b.dualMap ⊔
      (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₁)) := by
  rw [← dual_baseChange_eq_zero_iff, dual_baseChange_dualMap] at hx
  obtain ⟨y, hy⟩ := (h _).1 hx
  obtain ⟨y, rfl⟩ := dual_baseChange_surjective hs M₂ y
  have : x = b.dualMap y + (x - b.dualMap y) := by abel
  rw [this]
  refine Submodule.add_mem_sup ⟨y, rfl⟩ ?_
  rw [← dual_baseChange_eq_zero_iff, map_sub, dual_baseChange_dualMap, hy, sub_self]

end Modules

theorem mem_sup_of_exact_fibres {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsRegularLocalRing B] (π : A →+* B) (hs : Surjective π) (g : ℕ) (hg : ringKrullDim B = g)
    (C : CochainComplex (ModuleCat.{0} A) ℕ)
    (hF : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))
    (hn : ∃ n, ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : PrimeSpectrum A, RingHom.ker π ≤ p.asIdeal → ∃ (K : Type) (_ : Field K)
      (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
        ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i)
    (i : ℕ) (x : Module.Dual A (C.X (i + 1)))
    (hx : (C.d i (i + 1)).hom.dualMap x ∈
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X i)))) :
    x ∈ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ⊔
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X (i + 1)))) := by
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  let := π.toAlgebra
  have key := GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing B g hg (((ModuleCat.extendScalars π).mapHomologicalComplex _).obj C)
    (fun i => ⟨inferInstanceAs (Module.Free B (B ⊗[A] C.X i)),
      inferInstanceAs (Module.Finite B (B ⊗[A] C.X i))⟩)
    (hn.imp fun n h i hi => (ModuleCat.extendScalars π).map_isZero (h i hi)) (fun q => ?_) i
  · exact mem_sup_of_exact (B := B) hs _ _ key x hx
  obtain ⟨K, _, φ, hφ, hK⟩ := hex (q.comap π) (by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le)
  have hle : RingHom.ker π ≤ RingHom.ker φ := by
    rw [hφ, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  obtain ⟨ψ, rfl⟩ : ∃ ψ : B →+* K, ψ.comp π = φ :=
    ⟨π.liftOfSurjective hs ⟨φ, hle⟩, π.liftOfSurjective_comp hs _⟩
  refine ⟨K, inferInstance, ψ, ?_, fun j hj => ?_⟩
  · apply Ideal.comap_injective_of_surjective π hs
    rw [RingHom.comap_ker, hφ]
    rfl
  · refine (hK j (hj.imp_left fun h h' => h ?_)).of_iso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp π ψ) _).app C)
    have hm : (q.asIdeal.comap π).IsMaximal := by
      have : q.asIdeal.comap π = IsLocalRing.maximalIdeal A := h'
      rw [this]
      infer_instance
    have := (Ideal.comap_isMaximal_of_surjective π hs (K := IsLocalRing.maximalIdeal B))
    apply Ideal.comap_injective_of_surjective π hs
    rw [IsLocalRing.eq_maximalIdeal hm, IsLocalRing.eq_maximalIdeal this]

end DualCokernelFlat


open DualCokernelFlat in
theorem flat_quotient_of_equiv_coker_dualMap_of_exact_fibres :
    ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A]
      [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)]
      [Module.Flat V A] (g : ℕ),
      IsRegularLocalRing (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) →
      ringKrullDim (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) ≤ p.asIdeal →
        ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
          ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ I : Ideal A, Nonempty ((Module.Dual A (C.X 0) ⧸
        LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] (A ⧸ I)) → Module.Flat V (A ⧸ I) := by
  intro V A _ _ _ _ _ _ _ _ _ g hreg hg C hF hn hex I ⟨e⟩
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hflat : ∀ i, Module.Flat V (Module.Dual A (C.X i)) := fun i => Module.Flat.trans V A _
  have key := mem_sup_of_exact_fibres (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective g hg C hF
    hn (by rw [Ideal.mk_ker]; exact hex)
  rw [Ideal.mk_ker] at key
  have h := GlobalTheory.flat_coker_of_complex_exact_mod_maximalIdeal V A (fun i => Module.Dual A (C.X i))
    (fun i => (C.d i (i + 1)).hom.dualMap) (fun i f => ?_) (hn.imp fun n h i hi => ?_) key
  · exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm
  · ext x
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← LinearMap.comp_apply (C.d _ _).hom,
      ← ModuleCat.hom_comp, C.d_comp_d]
    simp
  · have := ModuleCat.subsingleton_of_isZero (h i hi)
    infer_instance

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits TensorProduct

theorem _root_.GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) → (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) → ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by
  first | exact @GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing | exact GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing | (intros; apply GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

lemma gtCoord_i_comp_q {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G) :
    g'.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : IsProper (thickObj R I e D.P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have := g.q_hom
  have := g'.i_hom
  exact splitTorus_hom_proper_trivial_local _ D'.X _ _ inferInstance

theorem unifPre_abelianPart_iso :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
      ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
        (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
        ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (e : ℕ),
          ∃ (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A),
            IsMonHom β.hom ∧ (U'.gt e).q ≫ β.hom = (U.gt e).q := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' e
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have := (U.gt e).q_affine
  have := (U'.gt e).q_affine
  exact flatQuotient_iso_of_same_kernel _ _ _ _ _ _ (U.gt e).q (U.gt e).i (U'.gt e).q (U'.gt e).i
    (U.gt e).q_hom (U.gt e).i_hom (U.gt e).q_flat (U.gt e).q_surj inferInstance (U.gt e).isKernel
    (U'.gt e).q_hom (U'.gt e).i_hom (U'.gt e).q_flat (U'.gt e).q_surj inferInstance
    (U'.gt e).isKernel (gtCoord_i_comp_q hI _ _) (gtCoord_i_comp_q hI _ _)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_one_of_fibre_const_of_section :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (B W : Over S) [GrpObj B], IsAbelianScheme B → ∀ (π : W ⟶ B) [Flat π.left] [Surjective π.left] [QuasiCompact π.left] (ρ : Γ(W.left, ⊤)) (σ : 𝟙_ (Over S) ⟶ W), (∀ (Z : Over S) (g₁ g₂ : Z ⟶ W), g₁ ≫ π = g₂ ≫ π → g₁.left.appTop.hom ρ = g₂.left.appTop.hom ρ) → σ.left.appTop.hom ρ = 1 → ρ = 1 := by
  intro hG S B W _ hB π _ _ _ ρ σ h hσ
  obtain ⟨a, rfl⟩ := FunDescent.exists_appTop_eq π.left ρ (by
    intro Z g₁ g₂ e
    let Z' : Over S := Over.mk (g₂ ≫ W.hom)
    let k₂ : Z' ⟶ W := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ W := Over.homMk g₁ (by
      change g₁ ≫ W.hom = g₂ ≫ W.hom
      rw [← Over.w π, reassoc_of% e])
    exact h Z' k₁ k₂ (Over.OverMorphism.ext e))
  obtain ⟨s, rfl⟩ := (hG S B hB).2 a
  rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, Category.assoc, Over.w π,
    Over.w σ] at hσ
  have hs : s = 1 := by
    have e : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [e] at hσ
    simpa using hσ
  rw [hs, map_one, map_one]

end GlobalTheory
end
