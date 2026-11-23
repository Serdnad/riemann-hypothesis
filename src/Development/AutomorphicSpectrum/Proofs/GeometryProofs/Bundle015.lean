module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem injective_of_maximal_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (p : X)
    [IsDomain (X.presheaf.stalk p)] (φ : X.presheaf.stalk p ⟶ CommRingCat.of Ω)
    (h : ∀ y : X, y ⤳ (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) →
      y = (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω)) :
    Function.Injective φ.hom := by
  let z : PrimeSpectrum (X.presheaf.stalk p) := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum (X.presheaf.stalk p) := PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint Ω)
  have hs : z ⤳ q := (PrimeSpectrum.le_iff_specializes z q).1 bot_le
  have hq : (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) = X.fromSpecStalk p q := rfl
  rw [hq] at h
  have h1 : X.fromSpecStalk p z = X.fromSpecStalk p q :=
    h _ (hs.map (X.fromSpecStalk p).continuous)
  have h2 : z = q := (X.fromSpecStalk p).isEmbedding.injective h1
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have h3 : a ∈ q.asIdeal := by
    change φ.hom a ∈ (IsLocalRing.closedPoint Ω).asIdeal
    rw [ha]
    exact Ideal.zero_mem _
  rw [← h2] at h3
  exact h3

theorem isCptGen_of_maximal_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : ∀ y : X, y ⤳ genPt ξ → y = genPt ξ)
    (hs : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) : IsCptGen ξ := by
  refine ⟨⟨?_, hs⟩, fun p => ?_⟩
  · have := hX (ξ (IsLocalRing.closedPoint Ω))
    refine injective_of_maximal_point _ (Scheme.stalkClosedPointTo ξ) ?_
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact h
  · obtain ⟨p, hp⟩ := p
    have := hX p
    have hp' : ξ (IsLocalRing.closedPoint Ω) ⤳ p := hp
    refine injective_of_maximal_point p
      (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ?_
    have e : Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫
        X.fromSpecStalk p = ξ := by
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    rw [e]
    exact h

theorem isCptGen_of_maximal : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X,
    (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  intro X hX x h
  have e : genPt (Ω := X.residueField x) (X.fromSpecResidueField x) = x :=
    X.fromSpecResidueField_apply x _
  refine isCptGen_of_maximal_of_surjective hX _ (by rw [e]; exact h) ?_
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
    ((X.fromSpecResidueField x).stalkMap_surjective _)

end GlobalTheory.CompanionTheory.Ar
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem spec_gamma_isoSpec_inv (S : CommRingCat.{0}) :
    Spec.map (Scheme.ΓSpecIso S).hom ≫ (Spec S).isoSpec.inv = 𝟙 _ := by
  simp [Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

theorem exists_section_of_isFinite (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsFinite f]
    (p : Spec (CommRingCat.of (FractionRing R)) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ s = p := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ψ : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of (FractionRing R) :=
    p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom
  have hφψ : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    have h1 : f.appTop ≫ p.appTop = (p ≫ f).appTop := by simp
    simp only [ψ, φ, Category.assoc]
    rw [reassoc_of% h1, hp, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have hfin : ψ.hom.Finite := by
    have h2 : f.appTop.hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    simpa [ψ] using RingHom.Finite.comp h2 h3
  have hint : ∀ a : Γ(X, ⊤), ∃ y : R, algebraMap R (FractionRing R) y = φ.hom a := by
    intro a
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    obtain ⟨P, hm, hP⟩ := hfin.to_isIntegral a
    refine ⟨P, hm, ?_⟩
    have h4 : φ.hom.comp ψ.hom = algebraMap R (FractionRing R) := by
      rw [← CommRingCat.hom_comp, hφψ]; rfl
    have := Polynomial.hom_eval₂ P ψ.hom φ.hom a
    rw [hP, map_zero, h4] at this
    exact this.symm
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  let e : R ≃+* (algebraMap R (FractionRing R)).range :=
    RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let θ₀ : Γ(X, ⊤) →+* R :=
    e.symm.toRingHom.comp (φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a))
  have hθ₀ : ∀ a, algebraMap R (FractionRing R) (θ₀ a) = φ.hom a := by
    intro a
    have h5 : e (θ₀ a) = φ.hom.codRestrict (algebraMap R (FractionRing R)).range (fun a => hint a) a := by
      simp [θ₀]
    exact congrArg Subtype.val h5
  let θ : Γ(X, ⊤) ⟶ CommRingCat.of R := CommRingCat.ofHom θ₀
  have hθφ : θ ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = φ := by
    ext a; exact hθ₀ a
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    ext r
    apply hinj
    have h6 := congrArg (fun g => g.hom r) hφψ
    have h7 := hθ₀ (ψ.hom r)
    exact h7.trans h6
  have hfθ : f.appTop ≫ θ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id, ← hψθ]
    simp [ψ]
  refine ⟨Spec.map θ ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hfθ]
    exact spec_gamma_isoSpec_inv _
  · rw [← Spec.map_comp_assoc, hθφ]
    simp only [φ, Spec.map_comp, Category.assoc]
    rw [Scheme.isoSpec_inv_naturality, reassoc_of% spec_gamma_isoSpec_inv]

theorem exists_section_of_generic_point (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens)
    (hU : IsFinite (U.ι ≫ Γ.G.hom)) (t : T) (ht : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) :
    ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧
      toUnit (genPt R) ≫ σ = Γ.pt t := by
  have hr : Set.range (Γ.pt t).left ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ht (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  let p := IsOpenImmersion.lift U.ι (Γ.pt t).left hr
  have hpι : p ≫ U.ι = (Γ.pt t).left := IsOpenImmersion.lift_fac _ _ _
  have hp : p ≫ U.ι ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [reassoc_of% hpι]; exact Over.w (Γ.pt t)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_isFinite R (U.ι ≫ Γ.G.hom) p hp
  refine ⟨Over.homMk (s ≫ U.ι) (by simpa using hs), ?_, ?_⟩
  · intro z
    have h8 : U.ι (s z) ∈ Set.range U.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h8
    simpa using h8
  · apply Over.OverMorphism.ext
    change (genPt R).hom ≫ s ≫ U.ι = (Γ.pt t).left
    rw [← hpι, ← hsp]
    simp

end GlobalTheory.CompanionTheory.Ar.BT
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

namespace ProjCoord

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

def push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) : Cpt (η ≫ f) :=
  ⟨f p.1, p.2.map f.continuous⟩

theorem genMap_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) :
    genMap (η ≫ f) (push η f p) = (genMap η p).comp (f.stalkMap p.1).hom := by
  have h1 := Scheme.stalkClosedPointTo_comp η f
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap f _ _ p.2
  have h3 : X.presheaf.stalkSpecializes (push η f p).2 ≫ Scheme.stalkClosedPointTo (η ≫ f) =
      f.stalkMap p.1 ≫ (Y.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo η) :=
    (congrArg (X.presheaf.stalkSpecializes (push η f p).2 ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo η) h2).trans
        (Category.assoc _ _ _)))
  exact congrArg (fun g => g.hom) h3

theorem regAt_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f] (p : Cpt η) :
    regAt (η ≫ f) (push η f p) = regAt η p := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  unfold regAt
  rw [genMap_push]
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := hb.2 s
    exact ⟨t, rfl⟩

theorem genMap_push_injective (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]
    (p : Cpt η) (h : Function.Injective (genMap η p)) :
    Function.Injective (genMap (η ≫ f) (push η f p)) := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  rw [genMap_push]
  exact h.comp hb.1

end OpenImm

section Chart

variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]

end Chart

section Away

open HomogeneousLocalization

variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]

end Away

section Poly

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem aeval_mul_of_isHomogeneous {B : Type} [CommRing B] [Algebra o B] (x : κ → B) (t : B)
    {g : MvPolynomial κ o} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun j => t * x j) g = t ^ n * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = n := by
    have := hg (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

end Poly

end ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanChart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem spMap_fromSpec_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) {D : Type} [CommRing D]
    (ψ : Γ(X, U) →+* D) :
    spMap ψ ≫ hU.fromSpec ≫ f = spMap (ψ.comp (f.appLE V U hUV).hom) ≫ hV.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem ringHom_eq_of_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    {ψ ψ' : Γ(X, U) →+* D} (h : spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec) : ψ = ψ' := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_ringHom_of_le {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    (x : Sp D ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* D, x = spMap φ ≫ hU.fromSpec := by
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Spec (CommRingCat.of D))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change x = Spec.map (CommRingCat.ofHom (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom) ≫ _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem le_preimage_of_fst {X : Scheme.{0}} {U : X.Opens} {C : Type} [CommRing C] (x : Sp (DualNumber C) ⟶ X)
    (h : ∀ p, (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ x) p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom := fun c => ⟨TrivSqZeroExt.inl c, by simp⟩
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ p.asIdeal := fun a ha => by
    have h0 : a.fst = 0 := ha
    have h2 : a ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  haveI := p.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  let p₀ : ↥(Sp C) := (⟨p.asIdeal.map (TrivSqZeroExt.fstHom C C C).toRingHom, hprime⟩ : PrimeSpectrum C)
  have hp : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom).base p₀ = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  have e := h p₀
  simp only [Scheme.Hom.comp_apply] at e
  show x p ∈ U
  rw [← hp]
  exact e

theorem tan_iff_der (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C) :
    (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
    (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
       ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
    (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  intro h1
  have hal : ∀ c : C, algebraMap C (DualNumber C) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hy : y = spMap (u.comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    have hw := Over.w (1 : Over.mk y ⟶ G)
    rw [h1, Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV u] at hw
    exact hw.symm
  have hbase : spMap (algebraMap C (DualNumber C)) ≫ y =
      spMap (((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    rw [hy, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨fun φ hφ hb => ?_, fun v hv => ?_⟩
  · have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      ext b
      · simpa [hal] using hφ _
      · simpa [hal] using hb b
    refine ⟨Over.homMk (spMap φ ≫ hU.fromSpec) ?_, ?_, rfl⟩
    · change (spMap φ ≫ hU.fromSpec) ≫ G.hom = spMap (algebraMap C (DualNumber C)) ≫ y
      rw [Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV φ, hbase, hcomp]
    · have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
        ext a
        exact hφ a
      change spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap φ ≫ hU.fromSpec = _
      rw [h1, ← Category.assoc, ← Spec.map_comp, ← hfst]
      rfl
  · have hv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans h1
    have hle : ⊤ ≤ v.left ⁻¹ᵁ U := by
      refine le_preimage_of_fst v.left fun p => ?_
      rw [hv']
      simp only [Scheme.Hom.comp_apply]
      exact hU.range_fromSpec.subset (Set.mem_range_self _)
    obtain ⟨φ, hφ⟩ := exists_ringHom_of_le hU v.left hle
    have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
      apply ringHom_eq_of_fromSpec hU
      rw [← hv', hφ, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      apply ringHom_eq_of_fromSpec hV
      rw [← hbase, ← spMap_fromSpec_hom G.hom hU hV hUV φ, ← Category.assoc, ← hφ]
      exact Over.w v
    refine ⟨φ, fun a => RingHom.congr_fun hfst a, fun b => ?_, hφ⟩
    have := RingHom.congr_fun hcomp b
    simpa [hal] using congrArg TrivSqZeroExt.snd this

end GlobalTheory.CompanionTheory.Ar.TanChart
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def LieChart {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Sp R ⟶ S) (f : R) : Prop :=
  ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
    (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
    (_ : Module.Projective (Localization.Away f) P)
    (m : ∀ (C : Type) [CommRing C] [Algebra R C], IsUnit (algebraMap R C f) →
      LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C)),
    ∀ (C C' : Type) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (hC : IsUnit (algebraMap R C f)) (hC' : IsUnit (algebraMap R C' f)) (c : C →ₐ[R] C') (w : P →ₗ[R] C),
      ((m C' hC').pt (c.toLinearMap ∘ₗ w)).left = spMap (dualMap c.toRingHom) ≫ ((m C hC).pt w).left

end GlobalTheory.CompanionTheory.Ar
end
end

section


theorem _root_.GlobalTheory.T.adjoin_inverse_is_localization_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω) (G : Set Ω), A = Algebra.adjoin ℚ G →
    ∀ (g : A), g ≠ 0 → S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G) → ∀ (hle : A ≤ S'),
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | exact GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | (intros; apply GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.adjoin_inverse_element_form : ∀ (T : Type) (Ω : Type) [Field Ω] [CharZero Ω] (u : T → Ω) (f : Ω) (S : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range u)) → ∀ F : MvPolynomial T ℚ, aeval u F = f → f ≠ 0 → ∀ s : S,
    ∃ (G : MvPolynomial T ℚ) (k : ℕ), (s : Ω) * f ^ k = aeval u G := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv | exact GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv | (intros; apply GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localization_kaehler_prime_ideal : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | exact GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff <;> assumption)
end
