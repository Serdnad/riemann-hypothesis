module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.valuation_centre_exists : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a := by
  intro X Ω _ ξ O _ _ _ s _ hξ V hV
  let φ : O →+* V := (algebraMap O Ω).codRestrict V hV
  have hcomp : CommRingCat.ofHom (algebraMap O Ω) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap V Ω) := by
    ext x
    rfl
  have hsq : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [hξ, hcomp, Spec.map_comp]
  have hE : ValuativeCriterion.Existence s := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  obtain ⟨l, hl⟩ : ∃ l : Spec (CommRingCat.of V) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l = ξ := by
    obtain ⟨⟨l, hl, -⟩⟩ := (hE ⟨↥V, Ω, ξ, Spec.map (CommRingCat.ofHom φ), ⟨hsq⟩⟩).exists_lift
    exact ⟨l, hl⟩
  subst hl
  have hspec : (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l)
      (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ l (IsLocalRing.closedPoint (CommRingCat.of V)) :=
    (IsLocalRing.specializes_closedPoint
      ((Spec.map (CommRingCat.ofHom (algebraMap V Ω))) (IsLocalRing.closedPoint (CommRingCat.of Ω)))).map
        l.continuous
  have h : TopCat.Presheaf.stalkSpecializes X.presheaf hspec ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l) =
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (l (IsLocalRing.closedPoint (CommRingCat.of V))))]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have key : ∀ g, GlobalTheory.CompanionTheory.Ar.genMap (Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ l)
      ⟨l (IsLocalRing.closedPoint (CommRingCat.of V)), hspec⟩ g =
        ((Scheme.stalkClosedPointTo l).hom g : Ω) := by
    intro g
    exact congrArg (fun ψ => ψ.hom g) h
  refine ⟨⟨l (IsLocalRing.closedPoint (CommRingCat.of V)), hspec⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha
    rw [key g]
    exact ((Scheme.stalkClosedPointTo l).hom g).2
  · intro a ha ha0 hinv
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha
    refine ⟨g, ?_, rfl⟩
    have hloc := Scheme.isLocalHom_stalkClosedPointTo' l
    apply (isUnit_map_iff (Scheme.stalkClosedPointTo l).hom g).mp
    rw [key g] at ha0 hinv
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ ha0
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace PositivityTheory.Xgn.NormalLatticeRange

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem specMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp]

theorem one_left {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Scheme.{0}} (x : T ⟶ S) :
    (1 : Over.mk x ⟶ G).left = x ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem transport {S : Scheme.{0}} (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S)
    (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    ∃ v' : epsAt x' ⟶ G, IsTanAt G x' v' ∧ v'.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left := by
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left) ?_, ?_, rfl⟩
  · have hw := Over.w v
    simp only [Category.assoc, hw, epsAt, Over.mk_hom]
    rw [← hx, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
      (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  · unfold IsTanAt at hv ⊢
    rw [one_left] at hv ⊢
    simp only [Over.homMk_left]
    have hring : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ) =
        φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := RingHom.ext fun a => by simp [dualMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hv, ← hx, Category.assoc]

end PositivityTheory.Xgn.NormalLatticeRange

open PositivityTheory.Xgn.NormalLatticeRange in
theorem PositivityTheory.Xgn.normal_lattice_range : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j := by
  intro X Ω _ ξ h G _ E _ _ M p Ep _ _ Mp j hj
  simp only [spMap] at hj
  have hgen1 : (genMap ξ p).comp (regIso h p).symm.toRingHom = algebraMap (regAt ξ p) Ω :=
    RingHom.ext fun r => congrArg Subtype.val ((regIso h p).apply_symm_apply r)
  have hgen2 : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun a => rfl
  apply Set.Subset.antisymm
  · have hle : M.lat p ≤ LinearMap.range j := by
      apply Submodule.span_le.2
      rintro e ⟨v, hv, he⟩
      obtain ⟨v', hv', hv'l⟩ :=
        transport G (regIso h p).toRingHom (X.fromSpecStalk p.1) (regPt h p) rfl v hv
      obtain ⟨e', he'⟩ := Mp.onto v' hv'
      refine ⟨e', M.inj (Over.OverMorphism.ext ?_)⟩
      rw [hj, he', hv'l, he, ← Category.assoc, specMap_dualMap_comp, hgen2]
    exact fun e he => LinearMap.mem_range.1 (hle he)
  · rintro _ ⟨e', rfl⟩
    have hx : Spec.map (CommRingCat.ofHom (regIso h p).symm.toRingHom) ≫ regPt h p =
        X.fromSpecStalk p.1 := by
      have hid : (regIso h p).symm.toRingHom.comp (regIso h p).toRingHom = RingHom.id _ := by
        ext a
        simp
      simp only [regPt, spMap]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hid]
      simp
    obtain ⟨v', hv', hv'l⟩ := transport G (regIso h p).symm.toRingHom (regPt h p) (X.fromSpecStalk p.1) hx
      (Mp.pt e') (Mp.tan e')
    exact Submodule.subset_span ⟨v', hv', by rw [hj, hv'l, ← Category.assoc, specMap_dualMap_comp, hgen1]⟩
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_relabel_bundle

variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}

theorem exists_snd {K : Type} {ι : K → Type} (p : Σ k, ι k) (k : K) (h : p.1 = k) :
    ∃ i : ι k, p = ⟨k, i⟩ := by
  obtain ⟨a, i⟩ := p
  simp only at h
  subst h
  exact ⟨i, rfl⟩

theorem exists_down (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (s₂ : ∀ k, ι₂ k) : ∃ s₁ : ∀ k, ι₁ k, ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩ := by
  have h : ∀ k, ∃ i : ι₁ k, σ.symm ⟨e k, s₂ (e k)⟩ = ⟨k, i⟩ := fun k => by
    apply exists_snd
    apply e.injective
    rw [← hσ, Equiv.apply_symm_apply]
  choose s₁ hs using h
  exact ⟨s₁, fun k => by rw [← hs k, Equiv.apply_symm_apply]⟩

theorem exists_up (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (s₁ : ∀ k, ι₁ k) : ∃ s₂ : ∀ k, ι₂ k, ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩ := by
  have h : ∀ k, ∃ i : ι₂ k, σ ⟨e.symm k, s₁ (e.symm k)⟩ = ⟨k, i⟩ := fun k => by
    apply exists_snd
    rw [hσ, Equiv.apply_symm_apply]
  choose s₂ hs using h
  refine ⟨s₂, fun k => ?_⟩
  rw [← hs (e k)]
  exact congrArg (fun k => σ ⟨k, s₁ k⟩) (e.symm_apply_apply k).symm

theorem down_unique (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) {s₂ : ∀ k, ι₂ k}
    {s₁ t₁ : ∀ k, ι₁ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩)
    (ht : ∀ k, σ ⟨k, t₁ k⟩ = ⟨e k, s₂ (e k)⟩) : s₁ = t₁ := by
  funext k
  have h := σ.injective ((hs k).trans (ht k).symm)
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2

variable {Ω : Type} [Field Ω]

theorem cone_rename (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω)
    (f : MvPolynomial (Σ k, ι₁ k) O) :
    pointConeMap O y (rename σ f) = rename e (pointConeMap O (y ∘ σ) f) := by
  have key : (pointConeMap O y).comp (rename σ) =
      ((rename e : MvPolynomial K₁ Ω →ₐ[Ω] MvPolynomial K₂ Ω).restrictScalars O).comp
        (pointConeMap O (y ∘ σ)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, hσ]
  exact congrArg (fun φ => φ f) key

theorem pointIdeal_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    pointIdeal O y = (pointIdeal O (y ∘ σ)).map (rename σ) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨f, rfl⟩ := rename_surjective (R := O) σ σ.surjective g
    apply Ideal.mem_map_of_mem
    have h0 : pointConeMap O y (rename σ f) = 0 := hg
    rw [cone_rename O e σ hσ] at h0
    show pointConeMap O (y ∘ σ) f = 0
    apply rename_injective e e.injective
    rw [h0, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    have h0 : pointConeMap O (y ∘ σ) f = 0 := hf
    show pointConeMap O y (rename σ f) = 0
    rw [cone_rename O e σ hσ, h0, map_zero]

theorem fnField_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω) :
    fnField O y = fnField O (y ∘ σ) := by
  unfold fnField
  congr 2
  ext a
  constructor
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    have h : ∀ i : ι₂ k, ∃ i' : ι₁ (e.symm k), σ.symm ⟨k, i⟩ = ⟨e.symm k, i'⟩ := fun i => by
      apply exists_snd
      apply e.injective
      rw [← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨i', hi⟩ := h i
    obtain ⟨j', hj⟩ := h j
    refine ⟨⟨e.symm k, i', j'⟩, ?_⟩
    simp only [Function.comp]
    rw [← hi, ← hj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · rintro ⟨⟨k, i, j⟩, rfl⟩
    obtain ⟨i', hi⟩ := exists_snd (σ ⟨k, i⟩) (e k) (hσ _)
    obtain ⟨j', hj⟩ := exists_snd (σ ⟨k, j⟩) (e k) (hσ _)
    refine ⟨⟨e k, i', j'⟩, ?_⟩
    simp only [Function.comp]
    rw [hi, hj]

variable [Fintype K₁] [Fintype K₂] [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]

theorem mseg_eq (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) :
    mseg y s₂ = mseg (y ∘ σ) s₁ := by
  simp only [mseg, Function.comp, hs]
  exact (Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩)).symm

theorem mon_eq (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) (a : K₂ → ℤ) :
    ∏ k, y ⟨k, s₂ k⟩ ^ a k = ∏ k, (y ∘ σ) ⟨k, s₁ k⟩ ^ (a ∘ e) k := by
  simp only [Function.comp, hs]
  exact (Equiv.prod_comp e (fun k => y ⟨k, s₂ k⟩ ^ a k)).symm

theorem chartRing_eq (O : Type) [CommRing O] [Algebra O Ω] (e : K₁ ≃ K₂)
    (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, ι₂ k) → Ω)
    {s₁ : ∀ k, ι₁ k} {s₂ : ∀ k, ι₂ k} (hs : ∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) :
    chartRing O (mseg y) s₂ = chartRing O (mseg (y ∘ σ)) s₁ := by
  unfold chartRing
  congr 1
  ext a
  simp only [Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨t₁, ht⟩ := exists_down e σ hσ t
    exact ⟨t₁, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨t₂, ht⟩ := exists_up e σ hσ t
    exact ⟨t₂, by rw [mseg_eq e σ y hs, mseg_eq e σ y ht]⟩

end PositivityTheory.Xgn.A_relabel_bundle

open PositivityTheory.Xgn.A_relabel_bundle in
theorem PositivityTheory.Xgn.t_relabel_bundle : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) → ∀ y : (Σ k, ι₂ k) → Ω, pointIdeal O y = (pointIdeal O (y ∘ σ)).map (rename σ) ∧ fnField O y = fnField O (y ∘ σ) ∧ ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E₁ : ChartBundle O (mseg (y ∘ σ)) N V), ∃ E₂ : ChartBundle O (mseg y) N V, (∀ (s₁ : ∀ k, ι₁ k) (s₂ : ∀ k, ι₂ k), (∀ k, σ ⟨k, s₁ k⟩ = ⟨e k, s₂ (e k)⟩) → E₂.lat s₂ = E₁.lat s₁) ∧ ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K₂ → ℤ), IsFlagFrame (y ∘ σ) E₁ w (fun i => b i ∘ e) → IsFlagFrame y E₂ w b := by
  intro O _ Ω _ _ K₁ _ _ ι₁ _ K₂ _ _ ι₂ _ e σ hσ y
  refine ⟨pointIdeal_eq O e σ hσ y, fnField_eq O e σ hσ y, fun N V _ _ E₁ => ?_⟩
  choose d hd using exists_down e σ hσ
  have hm : ∀ s, mseg y s = mseg (y ∘ σ) (d s) := fun s => mseg_eq e σ y (hd s)
  have hc : ∀ s, chartRing O (mseg y) s = chartRing O (mseg (y ∘ σ)) (d s) :=
    fun s => chartRing_eq O e σ hσ y (hd s)
  refine ⟨{ lat := fun s => E₁.lat (d s)
            stable := fun s a ha v hv => E₁.stable (d s) a (by rw [← hc]; exact ha) v hv
            frame := fun s hs => by
              simp only [hc]
              exact E₁.frame (d s) (by rw [← hm]; exact hs)
            overlap := fun s t hs ht v hv => by
              simp only [hm]
              exact E₁.overlap (d s) (d t) (by rw [← hm]; exact hs) (by rw [← hm]; exact ht) v hv },
    fun s₁ s₂ h => ?_, fun w b h => ⟨fun s hs i => ?_⟩⟩
  · show E₁.lat (d s₂) = E₁.lat s₁
    rw [down_unique e σ (hd s₂) h]
  · have hs' : segreVec (y ∘ σ) (d s) ≠ 0 := by
      show mseg (y ∘ σ) (d s) ≠ 0
      rw [← hm]
      exact hs
    refine (h.graded (d s) hs' i).trans ?_
    have hc' : chartRing O (segreVec y) s = chartRing O (segreVec (y ∘ σ)) (d s) := hc s
    unfold degLat
    rw [hc', mon_eq e σ y (hd s) (b i)]
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_chart_noeth_frac

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

theorem ratio_eq [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) (k : K) (i : ι k) :
    mseg x (Function.update c k i) / mseg x c = x ⟨k, i⟩ / x ⟨k, c k⟩ := by
  have h1 : mseg x (Function.update c k i) = x ⟨k, i⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h2 : mseg x c = x ⟨k, c k⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  rw [h2] at hc
  rw [h1, h2, mul_div_mul_right _ _ (right_ne_zero_of_mul hc)]

theorem mseg_join {K' : Type} [Fintype K'] {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) c = mseg x (restrictChart c) * mseg z (fun k => c (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

def comb {K' : Type} {ι' : K' → Type} (t : ∀ k, ι k) (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => c (.inr k)

variable [∀ k, Fintype (ι k)]

theorem fnField_le [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) :
    fnField O x ≤ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
  have hk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hm : ∀ k (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
    intro k i
    rw [← ratio_eq x c hc k i]
    exact Subfield.subset_closure (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _)
  unfold fnField
  rw [Subfield.closure_le]
  rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
  · have h : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hk k)]
    show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)
    rw [h]
    exact div_mem (hm k i) (hm k j)

theorem isFractionRing_of_closure (R : Subalgebra O Ω) (h : Subfield.closure (R : Set Ω) = ⊤) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun z => ?_
  have hz : z ∈ Subfield.closure (R : Set Ω) := h ▸ Subfield.mem_top z
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have e : Subring.closure (R : Set Ω) = R.toSubring := Subring.closure_eq R.toSubring
  rw [e] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

end PositivityTheory.Xgn.A_chart_noeth_frac

open PositivityTheory.Xgn.A_chart_noeth_frac in
theorem PositivityTheory.Xgn.t_chart_noeth_frac : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x
  refine ⟨fun c => isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩), fun h c hc => ?_,
    fun K' _ _ ι' _ z => ⟨fun h => ?_, fun c hc => ?_⟩⟩
  · exact isFractionRing_of_closure _ (top_le_iff.1 (h ▸ fnField_le x c hc))
  · rw [eq_top_iff, ← h]
    unfold fnField
    refine Subfield.closure_mono (Set.union_subset_union_right _ ?_)
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨.inl k, i, j⟩, rfl⟩
  · have hc' := hc
    rw [mseg_join] at hc'
    refine ⟨left_ne_zero_of_mul hc', ?_⟩
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : mseg x t / mseg x (restrictChart c) =
        mseg (joinCoord x z) (comb t c) / mseg (joinCoord x z) c := by
      rw [mseg_join x z (comb t c), mseg_join x z c]
      exact (mul_div_mul_right _ _ (right_ne_zero_of_mul hc')).symm
    simp only
    rw [h]
    exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
end
