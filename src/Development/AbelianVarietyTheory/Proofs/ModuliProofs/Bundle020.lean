module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Invariant.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.GeomFibre

theorem bijective_appTop (K : Type) [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper f] : Function.Bijective f.appTop.hom := by
  have hfin : f.appTop.hom.Finite := finite_appTop_of_universallyClosed K f
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e
  have hfin' : (f.appTop.hom.comp e.hom).Finite := hfin.comp (RingHom.Finite.of_surjective _ he.2)
  have hb : Function.Bijective (f.appTop.hom.comp e.hom) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral (k := K) _ hfin'.to_isIntegral
  exact (Function.Bijective.of_comp_iff _ he).1 hb

theorem exists_field_pullback_appTop_bijective_and_triv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → IsProper f → GeometricallyIntegral f → ∀ (K : Type) [Field K] (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π) → ∃ (K₀ : Type) (_ : Field K₀) (g₀ : R →+* K₀) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K₀)), RingHom.ker g₀ = RingHom.ker g ∧ IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) ∧ Function.Bijective f₀.appTop.hom ∧ Triv (M.pull π₀) := by
  intro R _ X f M _ _ _ K _ g X' π f' h ⟨t, ht⟩
  let a : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have h₁ := IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom a))
  have h₂ : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom a)) ≫ π)
      (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) f (Spec.map (CommRingCat.ofHom (a.comp g))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact h₁.paste_horiz h
  have : IsIntegral (pullback f' (Spec.map (CommRingCat.ofHom a))) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ h₂
  have : IsProper (pullback.snd f' (Spec.map (CommRingCat.ofHom a))) :=
    MorphismProperty.of_isPullback (P := @IsProper) h₂ inferInstance
  refine ⟨AlgebraicClosure K, inferInstance, a.comp g, _, _, _, RingHom.ker_comp_of_injective g a.injective,
    h₂, bijective_appTop _ _, ?_⟩
  exact ⟨_, LB.isGen_pullGen M _ _ t ht _⟩

end GlobalTheory.GeomFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R] (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) → Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧ (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) → ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by
  first | exact @GlobalTheory.eigenMult_of_dense | exact GlobalTheory.eigenMult_of_dense | (intros; apply GlobalTheory.eigenMult_of_dense <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace RigidFunction

theorem not_mem_basicOpen_fibre {X P F : Scheme.{0}} {K : Type} [Field K] {p : P ⟶ X}
    {t : Spec (CommRingCat.of K) ⟶ X} {φ : F ⟶ P} {q : F ⟶ Spec (CommRingCat.of K)} (w : φ ≫ p = q ≫ t)
    [IsIntegral F] [UniversallyClosed q] (V : X.Opens) (hV : ∀ x, t x ∈ V) (s : Γ(P, p ⁻¹ᵁ V)) (a b : F)
    (ha : φ a ∉ P.basicOpen s) : φ b ∉ P.basicOpen s := by
  have hle : (⊤ : F.Opens) ≤ φ ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro c _
    change p (φ c) ∈ V
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    exact hV _
  have key : ∀ c : F, φ c ∈ P.basicOpen s ↔ c ∈ F.basicOpen ((φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s) := by
    intro c
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [key] at ha ⊢
  have hF := isField_of_universallyClosed K q
  by_cases hs : (φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s = 0
  · rw [hs, Scheme.basicOpen_zero]
    exact fun h => h
  · exfalso
    apply ha
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel hs
    rw [Scheme.basicOpen_of_isUnit _ (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)]
    trivial

end RigidFunction

theorem eq_one_of_appLE_section_eq_one :
    ∀ (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left), e ≫ P.hom = 𝟙 X → Smooth P.hom → GeometricallyIntegral P.hom → (IsReduced X ∧ genericPoints X ⊆ abLocus P) → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) := by
  intro X P e he hsm hgi hXg V u h hu
  obtain ⟨hred, hgen⟩ := hXg
  have := hsm
  have := hgi
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced P.hom

  have h0 : (e.appLE _ V h).hom (u - 1) = 0 := by rw [map_sub, map_one, hu, sub_self]
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  rw [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot, not_not] at hne

  have hopen := P.hom.isOpenMap _ (P.left.basicOpen (u - 1)).isOpen
  obtain ⟨x₀, ⟨y, hy, hyx₀⟩, hxg⟩ :=
    (dense_iff_closure_eq.mpr genericPoints.closure).inter_open_nonempty _ hopen (hne.image _)
  have hxV : x₀ ∈ V := by
    rw [← hyx₀]
    exact P.left.basicOpen_le _ hy
  have hxnot : e x₀ ∉ P.left.basicOpen (u - 1) := by
    intro hm
    have hmem : x₀ ∈ X.basicOpen ((e.appLE _ V h).hom (u - 1)) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨hxV, hm⟩
    rw [h0, Scheme.basicOpen_zero] at hmem
    exact hmem

  let K := AlgebraicClosure (X.residueField x₀)
  let t : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have ht : ∀ z, t z = x₀ := by
    intro z
    have hz : t z ∈ Set.range (X.fromSpecResidueField x₀) := ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at hz
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  have : IsProper (pullback.snd P.hom t) := hgen hxg K t ⟨pt, ht pt⟩
  have : IsIntegral (pullback P.hom t) :=
    hgi.geometrically_isIntegral t (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hpt : P.hom (e x₀) = t pt := by
    rw [ht, ← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback (e x₀) pt hpt
  obtain ⟨b, hb, -⟩ := Scheme.Pullback.exists_preimage_pullback y pt (hyx₀.trans (ht pt).symm)
  have hfib := RigidFunction.not_mem_basicOpen_fibre pullback.condition V
    (fun z => by rw [ht z]; exact hxV) (u - 1) a b (by rw [ha]; exact hxnot)
  rw [hb] at hfib
  exact hfib hy

end GlobalTheory
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem exists_equiv_latticeCoords (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)),
      (∀ ν : Fin n → ℤ, T (fun k => (ν k : ℝ)) ∈ Λ) ∧
      ∀ l : Λ, ∃ ν : Fin n → ℤ, T.symm l = fun k => (ν k : ℝ) := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b0 := Module.finBasis ℤ Λ
  let b := b0.ofZLatticeBasis ℝ Λ
  refine ⟨_, b.equivFunL.symm, ?_, ?_⟩
  · intro ν
    have : b.equivFunL.symm (fun k => (ν k : ℝ)) = ∑ k, (ν k : ℝ) • b k :=
      b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    refine Submodule.smul_mem _ _ ?_
    simp [b]
  · intro l
    refine ⟨fun k => b0.repr l k, ?_⟩
    funext k
    have := Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b0 l k
    simpa [b] using this

theorem realLinear_eq_sum_single {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℂ) (u : Fin n → ℝ) :
    L u = ∑ k, (u k : ℂ) * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single u]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (u k) : Fin n → ℝ) = u k • (Pi.single k 1 : Fin n → ℝ) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul]; simp

theorem dbar_comp_equiv {n g : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)) (h : (Fin g → ℂ) → ℂ)
    (x : Fin n → ℝ) (u v : Fin g → ℂ) :
    ∑ k, ((T.symm u k : ℂ) + I * (T.symm v k : ℂ)) * fderiv ℝ (h ∘ T) x (Pi.single k 1) =
      fderiv ℝ h (T x) u + I * fderiv ℝ h (T x) v := by
  have e : ∀ y, fderiv ℝ h (T x) y = fderiv ℝ (h ∘ T) x (T.symm y) := by
    intro y
    rw [ContinuousLinearEquiv.comp_right_fderiv]; simp
  rw [e u, e v, realLinear_eq_sum_single _ (T.symm u), realLinear_eq_sum_single _ (T.symm v),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem dbar_symbol_elliptic {n g : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)) (ξ : Fin n → ℝ)
    (h : ∀ a, ∑ k, ((T.symm (Pi.single a 1) k : ℂ) +
      I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ)) * (ξ k : ℂ) = 0) : ξ = 0 := by
  have h1 : ∀ a, T.symm (Pi.single a 1) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.re (h a)
    simpa [Complex.re_sum, dotProduct] using this
  have h2 : ∀ a, T.symm (I • (Pi.single a 1 : Fin g → ℂ)) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.im (h a)
    simpa [Complex.im_sum, dotProduct] using this
  have h3 : ∀ z : Fin g → ℂ, T.symm z ⬝ᵥ ξ = 0 := fun z => by
    have hz : z = ∑ a, ((z a).re • (Pi.single a 1 : Fin g → ℂ) +
        (z a).im • (I • (Pi.single a 1 : Fin g → ℂ))) := by
      conv_lhs => rw [← Finset.univ_sum_single z]
      refine Finset.sum_congr rfl fun a _ => ?_
      funext c
      by_cases hc : c = a
      · subst hc; simp
      · simp [hc]

    rw [hz, map_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_add (f := _), map_smul, map_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2]
    simp
  have := h3 (T ξ)
  rw [T.symm_apply_apply] at this
  exact dotProduct_self_eq_zero.mp this

theorem dbar_solve_complexTorus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ w : Fin g → (Fin g → ℂ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ ∀ (l : Λ) z, w a (z + l) = w a z) → (∀ a b z, (fderiv ℝ (w b) z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ (w b) z (I • (Pi.single a 1 : Fin g → ℂ))) = (fderiv ℝ (w a) z (Pi.single b 1 : Fin g → ℂ) + I * fderiv ℝ (w a) z (I • (Pi.single b 1 : Fin g → ℂ)))) → ∃ (t : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (l : Λ) z, f (z + l) = f z) ∧ ∀ a z, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = w a z - t a := by
  intro g Λ hd hΛ w hw hc
  obtain ⟨n, T, hT1, hT2⟩ := exists_equiv_latticeCoords g Λ hΛ
  obtain ⟨t, f, hf, hper, heq⟩ := GlobalTheory.T.exists_periodic_smooth_solution_torus_system n g
    (fun a k => (T.symm (Pi.single a 1) k : ℂ) +
      I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ))
    (dbar_symbol_elliptic T) (fun a => w a ∘ T)
    (fun a => ⟨(hw a).1.comp T.contDiff, fun ν x => by
      simp only [Function.comp, map_add (f := _)]
      exact (hw a).2 ⟨_, hT1 ν⟩ _⟩)
    (fun a b x => by
      rw [dbar_comp_equiv, dbar_comp_equiv]
      exact hc a b _)
  refine ⟨t, f ∘ T.symm, hf.comp T.symm.contDiff, fun l z => ?_, fun a z => ?_⟩
  · obtain ⟨ν, hν⟩ := hT2 l
    simp only [Function.comp, map_add (f := _), hν]
    exact hper ν _
  · have h1 := dbar_comp_equiv T (f ∘ T.symm) (T.symm z) (Pi.single a 1)
      (I • (Pi.single a 1 : Fin g → ℂ))
    have h2 : (f ∘ T.symm) ∘ T = f := by funext y; simp
    rw [h2, T.apply_symm_apply] at h1
    rw [← h1, heq a]
    simp

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.invariant_tower_isPushout : ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by
  first | exact @GlobalTheory.isPushout_of_tame | exact GlobalTheory.isPushout_of_tame | (intros; apply GlobalTheory.isPushout_of_tame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

def objRestrictBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B) {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (hρ : j (baseKA l).ρ = b.ρ) (hζ : j (baseKA l).ζ = b.ζ) : Obj D l (baseKA l) (s ≫ spMap j) where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta := o.eta
  eta_add := o.eta_add
  eta_ker := o.eta_ker
  etaA := o.etaA
  etaA_add := o.etaA_add
  etaA_ker := o.etaA_ker
  geom := by
    intro k _ _ x β hx
    have h1 : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp [spMap]
    have h2 : β = (Spec.preimage (x ≫ s)).hom.comp j := by
      have h3 : spMap β = spMap ((Spec.preimage (x ≫ s)).hom.comp j) := by
        rw [← hx, ← Category.assoc]
        conv_lhs => rw [h1]
        simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    have h := o.geom k x _ h1
    rw [← hρ, ← hζ] at h
    subst h2
    exact h

theorem moduli_rep_of_base :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f) := by
  intro _ E _ _ _ H D l Xo B _ b j S s o hS hρ hζ
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := Xo.rep S (s ≫ spMap j) hS (objRestrictBase j o hρ hζ)
  refine ⟨f, ⟨hf, ⟨⟨m.toSABMap, m.eta, m.etaA⟩⟩⟩, ?_⟩
  rintro g ⟨hg, ⟨m'⟩⟩
  exact hu g ⟨hg, ⟨⟨m'.toSABMap, m'.eta, m'.etaA⟩⟩⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.tateIsometry_of_finiteLevel_isometries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  first | exact @GlobalTheory.TateTower.tateIso_of_levels | exact GlobalTheory.TateTower.tateIso_of_levels | (intros; apply GlobalTheory.TateTower.tateIso_of_levels <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (e : Q → Q → Kˣ → Prop) (n : ℕ) (ζ : Kˣ) (ev : D.La → Q), 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D.La → (∀ y c, y ^ n = 1 → e 1 y c → c = 1) → IsPrimitiveRoot ζ n → (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev a ^ n = 1) → (∀ a c, e (ev a) (ev c) (ζ ^ D.EF a c)) → (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ ∀ y, y ^ n = 1 ↔ ∃ a, ev a = y := by
  first | exact @GlobalTheory.TorsIsometry.ker_and_onto | exact GlobalTheory.TorsIsometry.ker_and_onto | (intros; apply GlobalTheory.TorsIsometry.ker_and_onto <;> assumption)
end
