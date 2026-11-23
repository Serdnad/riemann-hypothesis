module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory


theorem GlobalTheory.PtExt.fv_linear (R : Type) [CommRing R] (X : Over (Sp R)) :
    (∀ (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (f + f') = (fv f).add (fv f')) ∧
    (∀ (r : R) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
      (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D),
      fv (r • f) D D' φ x = algebraMap R D' r * fv f D D' φ x) ∧
    (∀ g : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)),
      ∃ k : Fn0 X, IsCob (whole X) (fv ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩) k) := by
  refine ⟨fun f f' ↦ rfl, ?_, fun g ↦ ⟨fun D _ _ x ↦ g (trivAt x), ?_⟩⟩
  · intro r f D _ _ D' _ _ φ x
    exact Algebra.smul_def r (ev f (trivMap φ x))
  · intro D _ _ D' _ _ φ x _
    rfl

alias GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear := GlobalTheory.PtExt.fv_linear
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem evalSectionAtPointOrZero_specMap_comp (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : evU (spMap φ ≫ x) U a = φ (evU x U a) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ _)
  unfold evU
  rw [dite_eq_left h', dite_eq_left h]
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
  have e := congrArg (fun k => k.hom (x.appLE U ⊤ h a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  exact e

theorem evalSectionAtPointOrZero_restriction (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) : evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hV.trans (fun p hp ↦ h hp)
  unfold evU
  rw [dite_eq_left hV, dite_eq_left hU]
  unfold GlobalTheory.Cris.evalAt
  have e := congrArg (fun k => k.hom a) (Scheme.Hom.map_appLE x hV (homOfLE h).op)
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  rw [e]

theorem dualNumberSndMulInverseFst_mul_units (D : Type) [CommRing D] (u u' : DualNumber D) (hu : IsUnit u) (hu' : IsUnit u') : dl (u * u') = dl u + dl u' := by
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  obtain ⟨v', hv'⟩ := hu'.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv hv'
  unfold dl
  rw [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ← hv, ← hv', ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit]
  rw [mul_inv_rev, Units.val_mul]
  have a1 : (v : D) * ↑v⁻¹ = 1 := Units.mul_inv v
  have a2 : (v' : D) * ↑v'⁻¹ = 1 := Units.mul_inv v'
  linear_combination (u'.snd * ↑v'⁻¹) * a1 + (u.snd * ↑v⁻¹) * a2

theorem dualNumberAlgHomMap_fst_snd_logDerivative (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D) : (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u)) := by
  have h1 : (epsHom φ u).fst = φ u.fst := by
    simp [epsHom, DualNumber.lift_apply_apply]
  have h2 : (epsHom φ u).snd = φ u.snd := by
    simp [epsHom, DualNumber.lift_apply_apply]
  refine ⟨h1, h2, fun hu ↦ ?_⟩
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv
  unfold dl
  rw [h1, h2, ← hv, Ring.inverse_unit, map_mul]
  have : φ (v : D) = ((Units.map (φ : D →* D') v : D'ˣ) : D') := rfl
  rw [this, Ring.inverse_unit]
  rfl
theorem evalSectionAtPointOrZero_schemeHom_app (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) : evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a := by
  unfold evU
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold GlobalTheory.Cris.evalAt
    simp only [RingHom.comp_apply]
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dite_eq_right h, dite_eq_right h']

theorem dualNumberPoint_preimage_top_of_reduction (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  let f : DualNumber D →+* D := (TrivSqZeroExt.fstHom D D D).toRingHom
  have hf : Function.Surjective f := fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩
  intro p _
  change PrimeSpectrum (DualNumber D) at p
  have hp : p ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective D f hf, PrimeSpectrum.mem_zeroLocus]
    intro z hz
    change z.fst = 0 at hz
    have hz₂ : z ^ 2 = 0 := by
      rw [pow_two]
      apply TrivSqZeroExt.ext <;> simp [hz]
    exact p.isPrime.mem_of_pow_mem 2 (hz₂ ▸ p.asIdeal.zero_mem)
  obtain ⟨q, hq⟩ := hp
  exact hq ▸ h (Set.mem_univ q)

theorem evU_dl_rules : (∀ (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ U → evU (spMap φ ≫ x) U a = φ (evU x U a)) ∧ (∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ V → evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a) ∧ (∀ (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)), evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a) ∧ (∀ (D : Type) [CommRing D] (u u' : DualNumber D), IsUnit u → IsUnit u' → dl (u * u') = dl u + dl u') ∧ (∀ (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D), (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u))) ∧ ∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens), ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U :=
  ⟨evalSectionAtPointOrZero_specMap_comp, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_schemeHom_app, dualNumberSndMulInverseFst_mul_units, dualNumberAlgHomMap_fst_snd_logDerivative, dualNumberPoint_preimage_top_of_reduction⟩

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def pullCompare {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    {D : Type} [CommRing D] [Algebra R D] (w : Pt Y D) (z : Pt X D)
    (h : z = (w ≫ u : Pt X D)) :
    trivAt z ⟶ m.obj (trivAt w) :=
  Thick.trivHom { RingHom.id D with commutes' := fun _ ↦ rfl } (by
    subst z
    change spMap (RingHom.id D) ≫ (w ≫ u).left = w.left ≫ u.left
    rw [Cris.spMap_id, Category.id_comp, Over.comp_left])

theorem exists_crystallineCocycleOnPoints_pullback_cohomologous {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    ∃ c : Fn0 Y, ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (w : Pt Y D),
      fv (m.coef.pullbackOneCocycle f) D D' φ w = fv f D D' φ (w ≫ u) + (c D' (spOver φ ≫ w) - φ (c D w)) := by
  refine ⟨fun D _ _ w ↦ ev f (pullCompare u m w (w ≫ u) rfl), fun D _ _ D' _ _ φ w ↦ ?_⟩
  have h1 : ∀ (z : Pt X D') (h : z = (spOver φ ≫ w) ≫ u),
      @Eq D' (ev f (pullCompare u m (spOver φ ≫ w) z h))
        (ev f (pullCompare u m (spOver φ ≫ w) _ rfl)) := fun z h ↦ by subst z; rfl
  have k := ev_sq f (trivMap φ (w ≫ u))
    (pullCompare u m (spOver φ ≫ w) (spOver φ ≫ w ≫ u) (Category.assoc _ _ _).symm)
    (pullCompare u m w (w ≫ u) rfl) (m.functor.map (trivMap φ w)) fun _ ↦ rfl
  have key : ∀ a b b' c d : D', b = b' → a + b = c + d → d = a + (b' - c) :=
    fun a b b' c d e h ↦ by rw [← e]; linear_combination -h
  exact key _ _ _ _ _ (h1 _ _) k

theorem exists_isAdd_of_mem_primDR (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hf : CatCoh.H1.mk _ f ∈ primDR A) :
    ∃ g : Fn2 A, IsAdd (fv f) g := by
  have h := (mem_prim_iff (dp0 R) (𝟙 _) A _).1 hf
  have M : ∀ u : A ⊗ A ⟶ A,
      IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 _) (RingHom.id R) u.left := fun u ↦
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have h' : CatCoh.H1.mk _ ((M μ[A]).coef.pullbackOneCocycle f) =
      CatCoh.H1.mk _ ((M (fst A A)).coef.pullbackOneCocycle f + (M (snd A A)).coef.pullbackOneCocycle f) := by
    rw [map_add (f := _)]; exact h
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 h'
  obtain ⟨c, hc⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M μ[A]) f
  obtain ⟨c₁, hc₁⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (fst A A)) f
  obtain ⟨c₂, hc₂⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (snd A A)) f
  let k' : Fn0 (A ⊗ A) := fun D _ _ w ↦ k (trivAt w)
  refine ⟨fun D _ _ x y ↦ k' D (lift x y) - c D (lift x y) + c₁ D (lift x y) + c₂ D (lift x y),
    fun D _ _ D' _ _ φ x y ↦ ?_⟩
  have e : k' D' (spOver φ ≫ lift x y) - φ (k' D (lift x y)) =
      fv ((M μ[A]).coef.pullbackOneCocycle f) D D' φ (lift x y) -
        (fv ((M (fst A A)).coef.pullbackOneCocycle f) D D' φ (lift x y) +
          fv ((M (snd A A)).coef.pullbackOneCocycle f) D D' φ (lift x y)) :=
    congrFun (congrFun (congrFun hk _) _) (trivMap φ (lift x y))
  rw [hc, hc₁, hc₂, lift_fst, lift_snd, ← Hom.mul_def, comp_lift] at e
  simp only [map_add (f := _), map_sub]
  linear_combination e

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_away_cover_sm :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a,
          Sm (X := X) W (D := Localization.Away (s a))
            (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) := by
  intro R _ X K W hW D _ _ x
  let f : Sp D ⟶ X.left := x.left
  let S : Set D := {s | ∃ i, ∀ q : PrimeSpectrum D, q ∈ PrimeSpectrum.basicOpen s → f q ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    by_contra h'
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h'
    let p : PrimeSpectrum D := ⟨m, hm.isPrime⟩
    have hp : f p ∈ (⨆ i, W i) := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := f ⁻¹' (W i : Set X.left)) hi ((W i).isOpen.preimage f.continuous)
    have hsS : s ∈ S := ⟨i, fun q hq ↦ hsub hq⟩
    exact hs (hle (Ideal.subset_span hsS))
  have h1 : (1 : D) ∈ Submodule.span D S := by
    change (1 : D) ∈ Ideal.span S; rw [hS]; trivial
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun a ↦ (T.equivFin.symm a : D), ?_, ?_⟩
  · have hr : Set.range (fun a ↦ (T.equivFin.symm a : D)) = (T : Set D) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact (T.equivFin.symm a).2
      · intro hy; exact ⟨T.equivFin ⟨y, hy⟩, by simp⟩
    rw [hr, Ideal.eq_top_iff_one]; exact hT
  · intro a
    obtain ⟨i, hi⟩ := hTS (T.equivFin.symm a).2
    refine ⟨i, fun q _ ↦ ?_⟩
    have hq : (spMap (algebraMap D (Localization.Away ((T.equivFin.symm a : D)))) q : PrimeSpectrum D) ∈
        PrimeSpectrum.basicOpen ((T.equivFin.symm a : D)) :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away ((T.equivFin.symm a : D))) _).le ⟨q, rfl⟩
    exact hi _ hq

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem exists_dat_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f = c.1 →
    ∀ g : Fn2 A, IsAdd (fv f) g → ∃ d : Dat t c, d.f = f ∧ d.g = g := by
  intro R _ A _ p G t c f hf g hg
  choose liftRes liftRes_spec using fun n ↦ G.res_surjective n
  let value (n : ℕ) : G.A n :=
    fv f (G.A (n + 1)) (G.A n) (G.res n).toAlgHom (t.y (n + 1))
  let h : ∀ n, G.A n := Nat.rec (motive := G.A) 0 (fun n a ↦ liftRes n (a - value n))
  refine ⟨⟨f, hf, g, hg, h, ?_⟩, rfl, rfl⟩
  intro n
  have hres : G.res n (h (n + 1)) = h n - value n := liftRes_spec n _
  change value n = h n - G.res n (h (n + 1))
  rw [hres, sub_sub_cancel]

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CobChi

theorem exists_isAdd_chi_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (n : ℕ),
    (n : R) = 0 → ∀ (u f : Fn1 A) (g : Fn2 A), IsAdd u g → Cohom (whole A) u f →
    ∃ g' : Fn2 A, IsAdd f g' ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ n : Pt A D) = 1 → GlobalTheory.PtExt.chi n g' D x = GlobalTheory.PtExt.chi n g D x := by
  intro R _ A _ n hn u f g hu ⟨k, hk⟩
  have hf : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (x : Pt A D), f D D' φ x = u D D' φ x - (k D' (spOver φ ≫ x) - φ (k D x)) := by
    intro D _ _ D' _ _ φ x
    have h := hk D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg] at h
    linear_combination -h
  refine ⟨fun D _ _ x y ↦ g D x y - (k D (x * y) - k D x - k D y), ?_, ?_⟩
  · intro D _ _ D' _ _ φ x y
    have h1 := hu D D' φ x y
    simp only [hf, comp_mul, map_sub]
    linear_combination h1
  · intro D _ _ x hx
    have hnD : (n : D) = 0 := by
      rw [← map_natCast (algebraMap R D) n, hn, map_zero]
    have hs : ∑ i ∈ Finset.range n, (k D (x ^ i * x) - k D (x ^ i) - k D x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp_rw [← pow_succ]
      rw [Finset.sum_range_sub (fun i ↦ k D (x ^ i)), hx, pow_zero, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul,
        hnD, zero_mul]
    simp only [GlobalTheory.PtExt.chi]
    rw [Finset.sum_sub_distrib, hs, sub_zero]

end GlobalTheory.CobChi
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem nonempty_ι_of_isLB (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (hP : P.IsLB) : Nonempty P.ι := by
  have hne : Nonempty (𝟙_ (Over (Sp R))).left := inferInstanceAs (Nonempty (PrimeSpectrum R))
  obtain ⟨p⟩ := hne
  let e : 𝟙_ (Over (Sp R)) ⟶ A ⊗ B := lift η[A] η[B]
  have h : e.left.base p ∈ (⨆ i, P.U i) := by rw [hP.cover]; trivial
  obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i⟩

theorem exists_isChoice : ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∃ j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι, IsChoice P j := by
  intro R _ _ A B _ _ P hP
  have hne := nonempty_ι_of_isLB R A B P hP
  classical
  refine ⟨fun D _ _ x ↦ if h : Sm (chartsA P) x then
    Classical.choose (show ∃ i, ⊤ ≤ x.left ⁻¹ᵁ chartsA P i from h)
  else Classical.choice hne, ?_⟩
  unfold IsChoice
  intro D _ _ x h
  simp only [dite_eq_left h]
  exact Classical.choose_spec (show ∃ i, ⊤ ≤ x.left ⁻¹ᵁ chartsA P i from h)

end GlobalTheory.PtExt
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {m : C1 F} {z z' : C2 F} (h : d1 F m = z - z') {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'')
    (h0 : z' T T' T'' a b = 0) :
    mp F b (m T T' a) - m T T'' (a ≫ b) + m T' T'' b = z T T' T'' a b := by
  rw [← d1_apply, h]
  simp only [Pi.sub_apply, h0, sub_zero]

theorem exists_crystallineCochain_coboundary_eq_chernCocycle {R : Type} [CommRing R] {I : Ideal R} {g : DividedPowers I} {X : Scheme.{0}}
    {s : X ⟶ Sp R} {L : LB X} {w : Z2 (O g s)} (hw : IsChern g s L (CatCoh.H2.mk _ w)) :
    ∃ V : C1 (O g s), ∀ (T T' T'' : Thick g s) (a : T ⟶ T') (b : T' ⟶ T''), IsSmall g s L.U T → T''.J = ⊥ →
      d1 _ V T T' T'' a b = w.1 T T' T'' a b := by
  obtain ⟨i, hi, u, ℓ, hu, hℓ, hz⟩ := hw
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨m, hm⟩ := hz
  classical
  have sm : ∀ {T T' : Thick g s} (_ : T ⟶ T'), IsSmall g s L.U T → IsSmall g s L.U T' := by
    rintro T T' a ⟨j, hj⟩
    exact ⟨j, a.le_preimage hj⟩
  refine ⟨fun T T' a ↦ if h : IsSmall g s L.U T then m ⟨T, h⟩ ⟨T', sm a h⟩ (ObjectProperty.homMk a) else 0, ?_⟩
  intro T T' T'' a b h hJ
  have h1 := sm a h
  have h2 := sm b h1
  rw [d1_apply]
  simp only [dite_eq_left h, dite_eq_left h1]
  refine commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing hm (T := ⟨T, h⟩) (T' := ⟨T', h1⟩) (T'' := ⟨T'', h2⟩) (ObjectProperty.homMk a)
    (ObjectProperty.homMk b) ?_
  have := (hℓ ⟨T, h⟩ ⟨T', h1⟩ ⟨T'', h2⟩ (ObjectProperty.homMk a) (ObjectProperty.homMk b)).1
  exact Ideal.mem_bot.1 (hJ.le this)

theorem exists_pt_d_eq_chern {R : Type} [CommRing R] {X : Over (Sp R)} {L : LB X.left}
    {w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))} (hw : IsChern (dp0 R) _ L (CatCoh.H2.mk _ w)) :
    ∃ V : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (z : Pt X E) (z' : Pt X E'),
      (trivAt z ⟶ trivAt z') → E',
      ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
        [Algebra R E''] (z : Pt X E) (z' : Pt X E') (z'' : Pt X E'') (a : trivAt z ⟶ trivAt z')
        (b : trivAt z' ⟶ trivAt z'') (ψ : E' →ₐ[R] E''), b.φ = ψ → Sm L.U z →
        ψ (V E E' z z' a) - V E E'' z z'' (a ≫ b) + V E' E'' z' z'' b = w.1 _ _ _ a b := by
  obtain ⟨V, hV⟩ := exists_crystallineCochain_coboundary_eq_chernCocycle hw
  refine ⟨fun E _ _ E' _ _ z z' a ↦ V _ _ a, ?_⟩
  intro E _ _ E' _ _ E'' _ _ z z' z'' a b ψ hb hz
  subst ψ
  exact hV _ _ _ a b hz rfl

theorem exists_pointwiseCochain_coboundary_eq_chernCocycle : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (L : LB X.left) (w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))), IsChern (dp0 R) _ L (CatCoh.H2.mk _ w) → ∃ n : Fn1 X, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt X E), Sm L.U z → ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) = w.1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) := by
  intro R _ X L w hw
  obtain ⟨V, hV⟩ := exists_pt_d_eq_chern hw
  refine ⟨fun E _ _ E' _ _ φ z ↦ V E E' z _ (trivMap φ z), ?_⟩
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have gen : ∀ (y : Pt X E'') (_ : y = spOver (ψ.comp φ) ≫ z) (f : trivAt z ⟶ trivAt y),
      (∀ c, f.φ c = ψ (φ c)) → V E E'' z _ (trivMap (ψ.comp φ) z) = V E E'' z y f := by
    intro y hy f hf
    subst hy
    exact congrArg (V E E'' z _) (Thick.Hom.ext' (AlgHom.ext fun c ↦ (hf c).symm))
  have hc := gen (spOver ψ ≫ spOver φ ≫ z) (by rw [← Category.assoc, spOver_comp])
    (trivMap φ z ≫ trivMap ψ (spOver φ ≫ z)) fun _ ↦ rfl
  have key := hV E E' E'' z _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) ψ rfl hz
  rw [← hc] at key
  exact key

end GlobalTheory.PtExt
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

theorem GlobalTheory.HilbFam.eValue_derivs : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I) (Ch : ℍ → ℂ), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * ∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) * hfun (2 * s) L μ Ch τ := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u Ch hf hs hN hL hφ hθ hn hLΛ hD hu
  have h1 := GlobalTheory.T.deformed_lattice_sum_derivatives_eq_eisenstein_jets hE E I φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hD hu
  have h2 := GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion hE (FR E) hf s N L hs hN hL τ (fun j ↦ κ (e.symm j)) Ch
  have hsum : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
  rw [hsum] at h2
  unfold wt at h2
  rw [hsum] at h2
  rw [h1, ← h2]
  ring
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB

theorem _root_.GlobalTheory.T.dualNumberSpec_affineOpen_functions_bijective : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  first | exact @GlobalTheory.LieVB.bijective_add_mul_epsFn | exact GlobalTheory.LieVB.bijective_add_mul_epsFn | (intros; apply GlobalTheory.LieVB.bijective_add_mul_epsFn <;> assumption)
end
