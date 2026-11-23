module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle076
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R']
    [Algebra R R'] [Module.Finite R R'] (hinj : Function.Injective (algebraMap R R')) :
    ∃ L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
      ∃ j : R' →ₐ[R] L, Function.Injective j := by
  first
  | exact @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | (apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding ..)

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem isGal_integralClosure_of_tower (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (L : Type) [Field L]
    [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L] [IsGalois (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] :
    IsGal (algebraMap R (integralClosure R L)) := by
  set K := FractionRing R
  set B := integralClosure R L
  haveI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have hRL : ∀ r : R, algebraMap B L (algebraMap R B r) = algebraMap K L (algebraMap R K r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply R K L]; rfl
  have hfix : ∀ τ : Gal (algebraMap R B), ∀ k : K,
      IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1 (algebraMap K L k) = algebraMap K L k := by
    intro τ k
    have h := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := K)
      (j := (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1).toRingHom.comp (algebraMap K L))
      (k := algebraMap K L) (by
        ext r
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [← hRL, IsFractionRing.ringEquivOfRingEquiv_algebraMap, τ.2 r])
    exact congrArg (fun f => f k) h
  let toAut : Gal (algebraMap R B) → (L ≃ₐ[K] L) := fun τ => AlgEquiv.ofRingEquiv (hfix τ)
  have htoAut : ∀ τ b, toAut τ (algebraMap B L b) = algebraMap B L (τ.1 b) := fun τ b =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
  refine ⟨Finite.of_injective toAut fun τ τ' h => Subtype.ext (RingEquiv.ext fun b => ?_), fun x hx => ?_⟩
  · apply IsFractionRing.injective B L
    rw [← htoAut, ← htoAut, h]
  · have hg : ∀ g : L ≃ₐ[K] L, g (x : L) = x := by
      intro g
      let gR : L →ₐ[R] L := (g : L →ₐ[K] L).restrictScalars R
      let gR' : L →ₐ[R] L := (g.symm : L →ₐ[K] L).restrictScalars R
      let τ : B ≃+* B :=
        { toFun := fun b => ⟨g b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR)⟩
          invFun := fun b => ⟨g.symm b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR')⟩
          left_inv := fun b => Subtype.ext (g.symm_apply_apply (b : L))
          right_inv := fun b => Subtype.ext (g.apply_symm_apply (b : L))
          map_mul' := fun a b => Subtype.ext (map_mul g (a : L) b)
          map_add' := fun a b => Subtype.ext (map_add g (a : L) b) }
      have hτ : τ ∈ Gal (algebraMap R B) := fun r => Subtype.ext (by
        show g ((algebraMap R B r : B) : L) = ((algebraMap R B r : B) : L)
        have e : ((algebraMap R B r : B) : L) = algebraMap K L (algebraMap R K r) := hRL r
        rw [e, AlgEquiv.commutes])
      exact congrArg Subtype.val (hx τ hτ)
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed (F := K) (x : L)).2 hg)
    have hint : IsIntegral R k := by
      have h1 : IsIntegral R (algebraMap K L k) := hk ▸ (x.2 : IsIntegral R (x : L))
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).1 h1
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨r, Subtype.ext ?_⟩
    have := hRL r
    rw [hr, hk] at this
    exact this

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem exists_galois_finExt_isLocalHom : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'')
    (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  intro R R' _ _ _ _ _ _ ρ hR hρ
  obtain ⟨⟨hRn, -, hRic, hRc⟩, hR0⟩ := hR
  obtain ⟨-, hinj, hfin⟩ := hρ
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  obtain ⟨L, hLf, hLg, j, hj⟩ := exists_galois_embedding R R' hinj
  set B := integralClosure R L
  obtain ⟨hBfin, hBloc, hBn, hBic, -⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hRc L
  have hmem : ∀ x : R', j x ∈ B := fun x => (Algebra.IsIntegral.isIntegral (R := R) x).map j
  let jB : R' →ₐ[R] B := j.codRestrict B hmem
  let σ : R' →+* B := jB.toRingHom
  have hcomp : σ.comp ρ = algebraMap R B := RingHom.ext fun r => jB.commutes r
  have hadm : AdmBase B (maximalIdeal B) :=
    ⟨hBn, inferInstance, hBic, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R B⟩
  have hσinj : Function.Injective σ := fun a b h => hj (congrArg (fun y : B => (y : L)) h)
  have hcfin : (σ.comp ρ).Finite := hcomp ▸ RingHom.finite_algebraMap.2 hBfin
  have hσfin : σ.Finite := RingHom.Finite.of_comp_finite hcfin
  refine ⟨B, inferInstance, inferInstance, hBloc, σ, ⟨hadm, hσinj, hσfin⟩,
    RingHom.IsIntegral.isLocalHom hσfin.to_isIntegral hσinj, ⟨hadm, hσinj.comp hinj, hcfin⟩, ?_⟩
  rw [hcomp]
  exact isGal_integralClosure_of_tower R L

end GlobalTheory.GalClosure
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_quotient_of_invariant_open {Γ : Type} [Group Γ] [Finite Γ] {Y S : Scheme.{0}} (act : Γ → (Y ⟶ Y))
    (h1 : act 1 = 𝟙 _) (hm : ∀ σ τ, act (σ * τ) = act σ ≫ act τ) (s : Y ⟶ S) (hs : ∀ σ, act σ ≫ s = s)
    (H : Y.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H)
    (hO : ∀ x ∈ H, ∃ O : Y.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) :
    ∃ (X : Over S) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ s ∧ IsAffineHom π ∧ Surjective π ∧
      (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) ∧
      (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) ∧
      ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V),
        (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)),
          (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  let r : Γ → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hr : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  have r1 : r 1 = 𝟙 _ := by
    rw [← cancel_mono H.ι, hr, h1, Category.id_comp, Category.comp_id]
  have rm : ∀ σ τ, r (σ * τ) = r σ ≫ r τ := fun σ τ => by
    rw [← cancel_mono H.ι, hr, hm, Category.assoc, hr, reassoc_of% hr]
  let ρ : Γ →* Aut H.toScheme := MonoidHom.mk'
    (fun σ => ⟨r σ⁻¹, r σ, by rw [← rm, inv_mul_cancel, r1], by rw [← rm, mul_inv_cancel, r1]⟩)
    (fun σ τ => Aut.ext (Iso.ext (show r (σ * τ)⁻¹ = r τ⁻¹ ≫ r σ⁻¹ by rw [mul_inv_rev, rm])))
  have hρ : ∀ σ, (ρ σ).asIso.hom = r σ⁻¹ := fun _ => rfl
  have hρ' : ∀ σ, r σ = (ρ σ⁻¹).asIso.hom := fun σ => by rw [hρ, inv_inv]
  have hpt : ∀ σ (x : H.toScheme), H.ι (r σ x) = act σ (H.ι x) := fun σ x => congr($(hr σ) x)
  have : OrbitsInAffineOpens ρ := ⟨fun x => by
    obtain ⟨O, hO₁, hO₂, hO₃⟩ := hO (H.ι x) x.2
    refine ⟨H.ι ⁻¹ᵁ O, hO₁.preimage_of_isOpenImmersion H.ι (by rwa [Scheme.Opens.opensRange_ι]), fun g => ?_⟩
    change H.ι (r g⁻¹ x) ∈ O
    rw [hpt]
    exact hO₃ _⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  have hinv : ∀ g, (ρ g).asIso.hom ≫ H.ι ≫ s = H.ι ≫ s := fun g => by
    rw [hρ, reassoc_of% hr, hs]
  refine ⟨Over.mk (hπ.desc (H.ι ≫ s) hinv), π, hπ.comp_desc _ hinv, hπ.isAffineHom, hπ.surjective, fun σ => ?_,
    fun x y hxy => ?_, fun V => ⟨hπ.app_injective V, fun f hf => ?_⟩⟩
  · exact (congrArg (· ≫ π) (hρ' σ)).trans (hπ.comp_eq _)
  · obtain ⟨g, rfl⟩ := (hπ.apply_eq_iff x y).mp hxy
    exact ⟨g⁻¹, (hpt _ _).symm⟩
  · exact hπ.mem_range_app V f fun g => ⟨hπ.preimage_le V g, hf g⁻¹ _⟩

theorem exists_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  intro R _ _ _ _ R' _ _ _ ρ _ hG D D' hD A' G' _ _ _ U' a H hH hO
  have := hG.1
  refine exists_quotient_of_invariant_open a.act a.act_one a.act_mul (G'.hom ≫ spMap ρ) (fun σ => ?_) H hH hO
  have e : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.2 x
  rw [← Category.assoc, (a.cart σ).1.w, Category.assoc, e]

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

theorem quot_affine_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  intro R _ _ _ R' _ _ _ _ _ _ _ G' act hact h1 hmul H hH X π hπ hAff hinv _ hsec V hV
  haveI := hAff
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  let r : Gal (algebraMap R R') → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hrπ : ∀ σ, r σ ≫ π = π := hinv
  have hr : ∀ σ, π ⁻¹ᵁ V ≤ (r σ) ⁻¹ᵁ (π ⁻¹ᵁ V) := fun σ x hx => by
    show x ∈ (r σ ≫ π) ⁻¹ᵁ V
    rw [hrπ σ]; exact hx
  have hrι : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  let a : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ⟶ Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => (r σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hr σ)
  have key0 : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec = hU.fromSpec ≫ r σ := fun σ =>
    IsAffineOpen.SpecMap_appLE_fromSpec (r σ) hU hU (hr σ)
  have key : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι = hU.fromSpec ≫ H.ι ≫ act σ := fun σ => by
    rw [← Category.assoc, key0, Category.assoc, hrι]
  have key_assoc : ∀ σ {Z : Scheme.{0}} (g : G'.left ⟶ Z),
      Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι ≫ g = hU.fromSpec ≫ H.ι ≫ act σ ≫ g := fun σ Z g => by
    simpa only [Category.assoc] using congrArg (· ≫ g) (key σ)
  have a_one : a 1 = 𝟙 _ := by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, h1, Spec.map_id]
    simp
  have a_mul : ∀ σ τ, a (σ * τ) = a τ ≫ a σ := fun σ τ => by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, hmul, Spec.map_comp]
    simp only [Category.assoc, key, key_assoc]
  have a_one' : ∀ x, (a 1).hom x = x := fun x => by rw [a_one]; rfl
  have a_mul' : ∀ σ τ x, (a (σ * τ)).hom x = (a σ).hom ((a τ).hom x) := fun σ τ x => by
    rw [a_mul]; rfl
  obtain ⟨φ', hφ'⟩ : ∃ φ' : CommRingCat.of R' ⟶ Γ(H.toScheme, π ⁻¹ᵁ V),
      Spec.map φ' = hU.fromSpec ≫ H.ι ≫ G'.hom := ⟨Spec.preimage _, Spec.map_preimage _⟩
  have semi : ∀ σ, φ' ≫ a σ = CommRingCat.ofHom (Gal.hom σ) ≫ φ' := fun σ => by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_comp, hφ', key_assoc, hact]
    simp only [Category.assoc]
  have semi' : ∀ σ y, (a σ).hom (φ'.hom y) = φ'.hom (σ.1 y) := fun σ y =>
    congrArg (fun f => f.hom y) (semi σ)
  letI alg' : Algebra R' Γ(H.toScheme, π ⁻¹ᵁ V) := φ'.hom.toAlgebra
  letI algR : Algebra R Γ(H.toScheme, π ⁻¹ᵁ V) := (φ'.hom.comp (algebraMap R R')).toAlgebra
  haveI tow : IsScalarTower R R' Γ(H.toScheme, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have fixR : ∀ σ r, (a σ).hom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r) = algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r :=
    fun σ r => by
      show (a σ).hom (φ'.hom (algebraMap R R' r)) = φ'.hom (algebraMap R R' r)
      rw [semi' σ]
      exact congrArg φ'.hom ((show ∀ r, σ.1 (algebraMap R R' r) = algebraMap R R' r from σ.2) r)
  let ah : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => { (a σ).hom with commutes' := fixR σ }
  have inv1 : ∀ σ x, (a σ).hom ((a σ⁻¹).hom x) = x := fun σ x => by
    rw [← a_mul', mul_inv_cancel, a_one']
  have inv2 : ∀ σ x, (a σ⁻¹).hom ((a σ).hom x) = x := fun σ x => by
    rw [← a_mul', inv_mul_cancel, a_one']
  let actE : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) := fun σ =>
    AlgEquiv.ofAlgHom (ah σ) (ah σ⁻¹) (AlgHom.ext fun x => inv1 σ x) (AlgHom.ext fun x => inv2 σ x)
  let actC : Gal (algebraMap R R') →* (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    { toFun := actE
      map_one' := AlgEquiv.ext fun x => a_one' x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => a_mul' σ τ x }
  have actC_apply : ∀ σ x, actC σ x = (a σ).hom x := fun _ _ => rfl
  let C : Subalgebra R Γ(H.toScheme, π ⁻¹ᵁ V) :=
    ⨅ σ, AlgHom.equalizer (actC σ : Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) (AlgHom.id R _)
  have memC : ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := fun x =>
    Algebra.mem_iInf.trans (forall_congr' fun σ => Iff.rfl)
  have happ : Spec.map (π.app V) ≫ hV.fromSpec = hU.fromSpec ≫ π := by
    rw [Scheme.Hom.app_eq_appLE]; exact IsAffineOpen.SpecMap_appLE_fromSpec π hV hU le_rfl
  have hmem : ∀ g, (π.app V).hom g ∈ C := by
    intro g; rw [memC]; intro σ
    have e : π.app V ≫ a σ = π.app V := by
      rw [← Spec.map_inj, ← cancel_mono hV.fromSpec, Spec.map_comp]
      simp only [Category.assoc]
      rw [happ, ← Category.assoc, key0, Category.assoc, hrπ]
    exact congrArg (fun f => f.hom g) e
  let ψ : Γ(X.left, V) →+* C := (π.app V).hom.codRestrict C hmem
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y h => (hsec V).1 (congrArg Subtype.val h), fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨x, hx⟩ := (hsec V).2 y (fun σ _ => (memC y).1 hy σ)
    exact ⟨x, Subtype.ext hx⟩
  let eψ := RingEquiv.ofBijective ψ hbij
  let l : Sp C ⟶ X.left := Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
  have hlr : l.opensRange = V := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, IsAffineOpen.opensRange_fromSpec]
  have sq : hU.fromSpec ≫ π = spMap (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) ≫ l := by
    rw [← happ]
    show _ = _ ≫ Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hj : hU.fromSpec ≫ H.ι ≫ G'.hom = spMap (algebraMap R' Γ(H.toScheme, π ⁻¹ᵁ V)) := by
    rw [← hφ']; rfl
  have hl : l ≫ X.hom = spMap (algebraMap R C) := by
    obtain ⟨m, hm⟩ : ∃ m : CommRingCat.of R ⟶ CommRingCat.of C, Spec.map m = l ≫ X.hom :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    rw [← hm]
    have e : m ≫ CommRingCat.ofHom (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) =
        CommRingCat.ofHom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V)) := by
      rw [← Spec.map_inj, Spec.map_comp, hm, ← Category.assoc, ← sq, Category.assoc, hπ]
      have h2 := congrArg (· ≫ spMap (algebraMap R R')) hj
      simp only [Category.assoc] at h2
      rw [h2, ← Spec.map_comp]
      rfl
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) e
  refine ⟨Γ(H.toScheme, π ⁻¹ᵁ V), inferInstance, algR, alg', tow, actC, C, hU.fromSpec, l, inferInstance,
    inferInstance, ?_, ?_, hj, hl, ?_, ?_, memC⟩
  · exact congrArg (fun U : X.left.Opens => (U : Set X.left)) hlr
  · refine (IsOpenImmersion.isPullback _ _ _ _ sq ?_).flip
    rw [hlr, IsAffineOpen.opensRange_fromSpec]
  · intro σ
    exact key σ
  · intro σ y
    exact semi' σ y

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem Near.exists_mul_pt {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {Z : Scheme.{0}} (q : Z ⟶ S) (a b : Z ⟶ N.U.left) (ha : a ≫ N.U.hom = q ≫ π)
    (hb : b ≫ N.U.hom = q ≫ π) :
    ∃ (O : Z.Opens) (h : O.toScheme ⟶ N.U.left), (∀ z : Z, π (q z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ q ≫ π ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), t ≫ O.ι ≫ q = s →
        N.Pt s (t ≫ O.ι ≫ a) x.left → N.Pt s (t ≫ O.ι ≫ b) y.left → N.Pt s (t ≫ h) (x * y).left := by
  haveI := N.isOpen
  let X₁ : Over.mk q ⟶ G := Over.homMk (pullback.lift a q ha ≫ N.u) (by
    change (pullback.lift a q ha ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let X₂ : Over.mk q ⟶ G := Over.homMk (pullback.lift b q hb ≫ N.u) (by
    change (pullback.lift b q hb ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let m : Z ⟶ G.left := (X₁ * X₂).left
  have hm : m ≫ G.hom = q := Over.w (X₁ * X₂)
  let O : Z.Opens := m ⁻¹ᵁ N.u.opensRange
  have hO : Set.range (O.ι ≫ m) ⊆ Set.range N.u := by
    rintro _ ⟨z, rfl⟩
    have hz : O.ι z ∈ O := z.2
    rw [Scheme.Hom.comp_apply]
    exact hz
  let h' : O.toScheme ⟶ pullback N.U.hom π := IsOpenImmersion.lift N.u (O.ι ≫ m) hO
  have hh : h' ≫ N.u = O.ι ≫ m := IsOpenImmersion.lift_fac _ _ _
  have hs : h' ≫ pullback.snd N.U.hom π = O.ι ≫ q := by
    rw [← N.u_over, ← Category.assoc, hh, Category.assoc, hm]
  refine ⟨O, h' ≫ pullback.fst _ _, fun z hz => ?_, ?_, ?_⟩
  · refine N.all (m z) ?_
    rw [← Scheme.Hom.comp_apply m G.hom, hm]
    exact hz
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.assoc]
  · rintro T t s x y hts ⟨x₀, hx₁, hx₂, hx₃⟩ ⟨y₀, hy₁, hy₂, hy₃⟩
    let τ : Over.mk s ⟶ Over.mk q := Over.homMk (t ≫ O.ι) (by
      change (t ≫ O.ι) ≫ q = s
      rw [Category.assoc, hts])
    have ex : x = τ ≫ X₁ := by
      ext1
      change x.left = (t ≫ O.ι) ≫ pullback.lift a q ha ≫ N.u
      rw [← hx₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hx₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hx₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    have ey : y = τ ≫ X₂ := by
      ext1
      change y.left = (t ≫ O.ι) ≫ pullback.lift b q hb ≫ N.u
      rw [← hy₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hy₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hy₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    refine ⟨t ≫ h', Category.assoc _ _ _, ?_, ?_⟩
    · rw [Category.assoc, hs, hts]
    · rw [ex, ey, ← MonObj.comp_mul, Category.assoc, hh]
      exact (Category.assoc _ _ _).symm

theorem Near.exists_mul_pt_pullback (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S)
    [GrpObj G'] (N : Near M.π G') :
    ∃ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left),
      (∀ z : ↥(pullback (N.U ⊗ N.U).hom M.π),
        (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (N.U ⊗ N.U).hom ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'),
        t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left →
        N.Pt s (t ≫ h) (x * y).left := by
  obtain ⟨O, h, h₁, h₂, h₃⟩ := N.exists_mul_pt (pullback.snd (N.U ⊗ N.U).hom M.π)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left)
    (by rw [Category.assoc, Over.w (fst N.U N.U), pullback.condition])
    (by rw [Category.assoc, Over.w (snd N.U N.U), pullback.condition])
  refine ⟨O, h, fun z hz => h₁ z ?_, ?_, h₃⟩
  · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hz
  · rw [h₂, pullback.condition]

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.spread_regular_div_localEquations_proper_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (z : M₁.Z) (G : Ω), G ∈ M₁.O z → (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x') → ∃ (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), z ∈ V.1 ∧ valF M₁.pt V.1 g = G ∧ ∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x' := by
  first | exact @GlobalTheory.Poinc.spread_regular_div | exact GlobalTheory.Poinc.spread_regular_div | (intros; apply GlobalTheory.Poinc.spread_regular_div <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cocycle_spec_prod_abelian_cohomologous_sum_mul : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  first | exact @GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | exact GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | (intros; apply GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.integralSection_expands_integrally_genericFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  first | exact @GlobalTheory.IntExpand.main | exact GlobalTheory.IntExpand.main | (intros; apply GlobalTheory.IntExpand.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.keyRule_complex_existence_jets_key_value : ∀ κ : Rule, Rule4 κ → Arch κ := by
  first | exact @GlobalTheory.MBLow.ArchProof.arch_of_rule4 | exact GlobalTheory.MBLow.ArchProof.arch_of_rule4 | (intros; apply GlobalTheory.MBLow.ArchProof.arch_of_rule4 <;> assumption)
end
