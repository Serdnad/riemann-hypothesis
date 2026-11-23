module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle071
public import Mathlib.NumberTheory.Padics.Complex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R')
    (w : σ → R') (u : σ →₀ ℕ) (a : R) :
    MvPolynomial.eval₂ ((Polynomial.C : R' →+* Polynomial R').comp β) (fun i => Polynomial.X * Polynomial.C (w i))
        (MvPolynomial.monomial u a) =
      Polynomial.C (MvPolynomial.eval₂ β w (MvPolynomial.monomial u a)) * Polynomial.X ^ u.degree := by
  simp only [MvPolynomial.eval₂_monomial, RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Polynomial.C_pow, ← map_prod, map_mul, Finsupp.degree_apply]
  ring

theorem coeff_eval₂_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  refine MvPolynomial.induction_on' F (fun u a => ?_) (fun p q hp hq => ?_)
  · simp only [MvPolynomial.coe_eval₂Hom]
    rw [eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_monomial a rfl))]
    split_ifs <;> simp
  · simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem eval₂_homogeneousComponent_eq_zero {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ)
    (h : MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_eval₂_scale β w F e]
  have key : Polynomial.toLaurent (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F) =
      MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
        (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F := by
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext r
      simp
    · funext i
      simp
  rw [h, ← map_zero Polynomial.toLaurent] at key
  rw [Polynomial.toLaurent_injective key, Polynomial.coeff_zero]

theorem spMap_comp_ringHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (β : A →+* B) (φ : B →+* C) :
    spMap φ ≫ spMap β = spMap (φ.comp β) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

private theorem secCoord_laurent_T_mul_C_of_secCoord {X Y : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {R' : Type}
    [CommRing R'] (y : Sp R' ⟶ Y) (a : Y ⟶ X) (v : σ → R') (h : SecCoord M th (y ≫ a) v) :
    SecCoord M th ((spMap (LaurentPolynomial.C : R' →+* LaurentPolynomial R') ≫ y) ≫ a)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i)) := by
  let u : (LaurentPolynomial R')ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  rw [Category.assoc]
  exact Coord.scale (Coord.baseChange h LaurentPolynomial.C) u

theorem ideals_homogeneous : (∀ (R σ : Type) [CommRing R] (Y X : Scheme.{0}) (s : Y ⟶ Sp R) (M : LB X) (th : σ → M.Sec) (a : Y ⟶ X), M.IsLB → (∀ F ∈ idealOf s M th a, ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf s M th a)) ∧ (∀ (R σ₁ σ₂ : Type) [CommRing R] (Y X₁ X₂ : Scheme.{0}) (s : Y ⟶ Sp R) (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂), M₁.IsLB → M₂.IsLB → (∀ F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂, ∀ e, MvPolynomial.homogeneousComponent e F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂)) ∧ ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → ProjRep (idealOf s M th (𝟙 Z)) s M th := by
  refine ⟨?_, ?_, ?_⟩
  · intro R σ _ Y X s M th a _ F hF e
    simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a v hyv.2⟩
    exact eval₂_homogeneousComponent_eq_zero β v F e h0
  · intro R σ₁ σ₂ _ Y X₁ X₂ s M₁ th₁ a₁ M₂ th₂ a₂ _ _ F hF e
    simp only [graphIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v₁ v₂ hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i))
      (fun i => LaurentPolynomial.C (v₂ i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a₁ v₁ hyv.2.1,
        by rw [Category.assoc]; exact Coord.baseChange hyv.2.2 LaurentPolynomial.C⟩
    have hfun : (fun i : σ₁ × σ₂ => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1 * v₂ i.2)) =
        fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1) * LaurentPolynomial.C (v₂ i.2) := by
      funext i
      rw [map_mul, ← _root_.mul_assoc]
    exact eval₂_homogeneousComponent_eq_zero β (fun i : σ₁ × σ₂ => v₁ i.1 * v₂ i.2) F e
      ((congrArg (fun g => MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp β) g F) hfun).trans h0)
  · intro R σ _ I Z s M th hI
    have hle : ∀ F ∈ I, F ∈ idealOf s M th (𝟙 Z) := by
      intro F hF
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker]
      intro R' _ β y v hyv
      rw [Category.comp_id] at hyv
      exact (hI.2.1 R' β y v hyv.1 hyv.2).2 F hF
    refine ⟨hI.1, ?_, ?_⟩
    · intro R' _ β x v hx hc
      refine ⟨(hI.2.1 R' β x v hx hc).1, fun F hF => ?_⟩
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF
      exact hF R' inferInstance β x v ⟨hx, by rwa [Category.comp_id]⟩
    · intro R' _ β v hv hz
      exact hI.2.2 R' β v hv fun F hF => hz F (hle F hF)

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.DenseFib

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) :
    ∃ φ : A →+* B, spMap φ = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eval₂_scale {R L σ : Type} [CommRing R] [CommRing L] (φ : R →+* L) (x : σ → L) (c : L)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem eq_zero_of_dense {A : Type} [CommRing A] [_root_.IsReduced A] (D : Set (Sp A)) (hD : Dense D) (a : A)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : A →+* K), Set.range (spMap κ) ⊆ D → κ a = 0) :
    a = 0 := by
  by_contra ha
  have hne : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)).Nonempty := by
    by_contra hn
    refine ha (IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff a).1 ?_))
    exact eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim
  obtain ⟨q, hqa, hqD⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen a).isOpen hne
  let q' : PrimeSpectrum A := q
  let K := AlgebraicClosure q'.asIdeal.ResidueField
  let κ : A →+* K := (algebraMap q'.asIdeal.ResidueField K).comp (algebraMap A _)
  have hker : ∀ z, κ z = 0 ↔ z ∈ q'.asIdeal := fun z => by
    simp only [κ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap q'.asIdeal.ResidueField K).injective]
    exact Ideal.algebraMap_residueField_eq_zero
  have h0 := h K κ (by
    rintro _ ⟨p, rfl⟩
    have : spMap κ p = q := by
      apply PrimeSpectrum.ext
      ext z
      have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := p.isPrime)
      change κ z ∈ p.asIdeal ↔ z ∈ q'.asIdeal
      rw [hp, ← hker]; rfl
    rwa [this])
  exact hqa ((hker a).1 h0)

theorem mem_idealOf_of_dense : ∀ (R σ : Type) [CommRing R] (Y : Scheme.{0}) (s : Y ⟶ Sp R) (N : LB Y) (ty : σ → N.Sec) (Sg : Set (Sp R)) (F : MvPolynomial σ R) (e : ℕ), IsReduced Y → Flat s → LocallyOfFinitePresentation s → N.IsLB → Dense Sg → F.IsHomogeneous e → (∀ (K : Type) [Field K] [IsAlgClosed K] (β : R →+* K) (y : Sp K ⟶ Y) (v : σ → K), y ≫ s = spMap β → Set.range (spMap β) ⊆ Sg → SecCoord N ty y v → MvPolynomial.eval₂ β v F = 0) → F ∈ idealOf s N ty (𝟙 Y) := by
  intro R σ _ Y s N ty Sg F e hred hflat hlfp hN hSg hF H
  simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, Category.comp_id]
  rintro R' _ β y v ⟨hy, hv⟩
  refine eq_zero_of_localization _ fun J hJ => ?_
  let L := Localization.AtPrime J
  let φ : R' →+* L := algebraMap R' L
  let yL : Sp L ⟶ Y := spMap φ ≫ y
  obtain ⟨A, _, x, w, hx, hp, hw⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Y N σ ty hN).2.2 (yL (IsLocalRing.closedPoint L))
  have hrange : Set.range yL ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := L) p).map yL.continuous).mem_open
      x.isOpenEmbedding.isOpen_range hp
  obtain ⟨ψ, hψ⟩ := exists_spMap (IsOpenImmersion.lift x yL hrange)
  have hψx : spMap ψ ≫ x = yL := by rw [hψ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := exists_spMap (x ≫ s)
  have hcomp : ψ.comp α = φ.comp β := by
    apply spMap_inj
    rw [← sp_comp, ← sp_comp, hα, ← Category.assoc, hψx, ← hy, Category.assoc]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 L ψ
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty R' y v hN hv).1 L φ
  rw [hψx] at h1
  obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty L yL _ hN h1).2.2 _ h2
  have hredA : IsReduced (Sp A) := isReduced_of_isOpenImmersion x
  have hredA' : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).1 hredA
  have hD : Dense ((x ≫ s) ⁻¹' Sg) := hSg.preimage (x ≫ s).isOpenMap
  have hA : MvPolynomial.eval₂ α w F = 0 := by
    refine eq_zero_of_dense _ hD _ fun K _ _ κ hκ => ?_
    rw [MvPolynomial.eval₂_comp_left]
    refine H K (κ.comp α) (spMap κ ≫ x) _ ?_ ?_
      ((GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 K κ)
    · rw [Category.assoc, ← hα, sp_comp]
    · rintro _ ⟨p, rfl⟩
      rw [← sp_comp, hα, Scheme.Hom.comp_apply]
      exact hκ ⟨p, rfl⟩
  change φ (MvPolynomial.eval₂ β v F) = 0
  rw [MvPolynomial.eval₂_comp_left, ← hcomp]
  have : (φ ∘ v) = fun i => (u : L) * (ψ ∘ w) i := funext hu
  rw [this, eval₂_scale _ _ _ hF, ← MvPolynomial.eval₂_comp_left, hA, map_zero, mul_zero]

end GlobalTheory.ZM.DenseFib
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Spread

section

variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}

theorem eq_isoPullback_hom_comp_bcMap (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (R : Subalgebra k V) (σ : T ⟶ pullback p (spMap (algebraMap k R)))
    (h₁ : σ ≫ pullback.fst _ _ = τ) (h₂ : σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom) :
    σ = hτ.isoPullback.hom ≫ bcMap p R.val := by
  apply pullback.hom_ext
  · rw [h₁, Category.assoc, bcMap_fst, IsPullback.isoPullback_hom_fst]
  · rw [h₂, Category.assoc, bcMap_snd, ← Category.assoc, IsPullback.isoPullback_hom_snd]

theorem comp_eq_id_of_models [Flat p] [IsSeparated p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) (R : Subalgebra k V)
    (f : pullback p (spMap (algebraMap k R)) ⟶ pullback q (spMap (algebraMap k R)))
    (g : pullback q (spMap (algebraMap k R)) ⟶ pullback p (spMap (algebraMap k R)))
    (hf : f ≫ pullback.snd _ _ = pullback.snd _ _) (hg : g ≫ pullback.snd _ _ = pullback.snd _ _)
    (hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ')
    (hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ) :
    f ≫ g = 𝟙 _ := by

  have hu : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f = hτ'.isoPullback.hom ≫ bcMap q R.val := by
    apply eq_isoPullback_hom_comp_bcMap hτ' R
    · simpa only [Category.assoc] using hf'
    · rw [Category.assoc, Category.assoc, hf, bcMap_snd, ← Category.assoc,
        IsPullback.isoPullback_hom_snd]

  have hfst : bcMap p R.val ≫ f ≫ g ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [← cancel_epi hτ.isoPullback.hom, reassoc_of% hu, IsPullback.isoPullback_hom_fst]
    exact hg'

  refine hom_ext_bcMap p R.val Subtype.val_injective (pullback.snd p (spMap (algebraMap k R)))
    ?_ ?_
  · rw [Category.assoc, hg, hf, Category.id_comp]
  · rw [Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hfst, bcMap_fst]
    · rw [Category.assoc, Category.assoc, hg, hf]

end

end GlobalTheory.Spread

namespace GlobalTheory

open Spread

theorem smooth_models_iso_over_fg_subalgebra :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (P Q T : Scheme.{0}) (p : P ⟶ Sp k) (q : Q ⟶ Sp k) (t : T ⟶ Sp V) (τ : T ⟶ P) (τ' : T ⟶ Q), Smooth p → IsSeparated p → QuasiCompact p → Smooth q → IsSeparated q → QuasiCompact q → IsPullback τ t p (spMap (algebraMap k V)) → IsPullback τ' t q (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))), R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ → σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  intro k V _ _ _ P Q T p q t τ τ' _ _ _ _ _ _ hτ hτ'

  have hΦ : (hτ.isoPullback.inv ≫ τ') ≫ q = pullback.fst _ _ ≫ p := by
    rw [← hτ.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]
  have hΨ : (hτ'.isoPullback.inv ≫ τ) ≫ p = pullback.fst _ _ ≫ q := by
    rw [← hτ'.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]

  obtain ⟨R₁, ψ₁, hR₁, hψ₁, hψ₁'⟩ := exists_fg_comp_eq p q _ hΦ
  obtain ⟨R, ψ₂, hR, hle, hψ₂⟩ :=
    exists_fg_forall_comp_eq q p (fun _ : Unit ↦ hτ'.isoPullback.inv ≫ τ) (fun _ ↦ hΨ) R₁ hR₁

  have ha : (bcMap p (Subalgebra.inclusion hle) ≫ ψ₁) ≫ q =
      pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, hψ₁, bcMap_fst_assoc, pullback.condition]
  have hb : ψ₂ () ≫ p = pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [(hψ₂ ()).1, pullback.condition]
  obtain ⟨f, hf₁, hf₂⟩ : ∃ f : pullback p (spMap (algebraMap k R)) ⟶
      pullback q (spMap (algebraMap k R)),
      f ≫ pullback.fst _ _ = bcMap p (Subalgebra.inclusion hle) ≫ ψ₁ ∧
        f ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ ha, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : pullback q (spMap (algebraMap k R)) ⟶
      pullback p (spMap (algebraMap k R)),
      g ≫ pullback.fst _ _ = ψ₂ () ∧ g ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ hb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ' := by
    rw [hf₁, bcMap_comp_of_eq_assoc p (Subalgebra.inclusion hle) R.val R₁.val (fun _ ↦ rfl), hψ₁',
      Iso.hom_inv_id_assoc]
  have hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ := by
    rw [hg₁, (hψ₂ ()).2, Iso.hom_inv_id_assoc]
  refine ⟨R, ⟨f, g, comp_eq_id_of_models hτ hτ' R f g hf₂ hg₂ hf' hg',
    comp_eq_id_of_models hτ' hτ R g f hg₂ hf₂ hg' hf'⟩, hR, hf₂, ?_⟩
  intro σ h₁ h₂
  rw [eq_isoPullback_hom_comp_bcMap hτ R σ h₁ h₂, Category.assoc]
  exact hf'

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GenericSpread

theorem exists_away_of_fg {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (S : Subalgebra R K) (hS : S.FG) :
    ∃ (f : R) (_ : f ≠ 0) (g : S →ₐ[R] Localization.Away f) (l : Localization.Away f →ₐ[R] K),
      ∀ x, l (g x) = x := by
  classical
  obtain ⟨t, rfl⟩ := hS
  choose p hp using fun x : K => IsLocalization.surj (nonZeroDivisors R) x
  set f : R := ∏ x ∈ t, ((p x).2 : R) with hf_def
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => nonZeroDivisors.ne_zero (p x).2.2
  have hfK : IsUnit (algebraMap R K f) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf0).isUnit
  have hpow : ∀ y : Submonoid.powers f, IsUnit (algebraMap R K y) := by
    rintro ⟨_, n, rfl⟩
    simpa using hfK.pow n
  let l : Localization.Away f →ₐ[R] K :=
    ⟨IsLocalization.lift (M := Submonoid.powers f) (S := Localization.Away f) hpow,
      fun r => IsLocalization.lift_eq hpow r⟩
  have hl : Function.Injective l := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    have h1 := congrArg l (IsLocalization.mk'_spec (Localization.Away f) a s)
    rw [map_mul, hz, zero_mul, AlgHom.commutes] at h1
    have ha : a = 0 := (IsFractionRing.injective R K) (by rw [← h1, map_zero])
    subst ha
    exact IsLocalization.mk'_zero s
  have hle : Algebra.adjoin R (↑t : Set K) ≤ l.range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, AlgHom.mem_range]
    have hdvd : ((p x).2 : R) ∣ f := Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hx)
    have hu : IsUnit (algebraMap R (Localization.Away f) ((p x).2 : R)) :=
      isUnit_of_dvd_unit (map_dvd _ hdvd) (IsLocalization.Away.algebraMap_isUnit f)
    refine ⟨algebraMap R _ (p x).1 * ↑hu.unit⁻¹, ?_⟩
    have hne : algebraMap R K ((p x).2 : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero (p x).2.2)
    apply mul_right_cancel₀ hne
    calc l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹) * algebraMap R K ((p x).2 : R)
        = l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹ * algebraMap R _ ((p x).2 : R)) := by
          rw [map_mul l _ (algebraMap R _ _), AlgHom.commutes]
      _ = l (algebraMap R _ (p x).1) := by rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
      _ = algebraMap R K (p x).1 := AlgHom.commutes l _
      _ = x * algebraMap R K ((p x).2 : R) := (hp x).symm
  refine ⟨f, hf0, (AlgEquiv.ofInjective l hl).symm.toAlgHom.comp (Subalgebra.inclusion hle), l,
    fun x => ?_⟩
  show l ((AlgEquiv.ofInjective l hl).symm (Subalgebra.inclusion hle x)) = x
  rw [← AlgEquiv.ofInjective_apply l hl, AlgEquiv.apply_symm_apply]
  rfl

end GlobalTheory.GenericSpread

namespace GlobalTheory

theorem morphisms_generic_spread_out :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B Z : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R) (I : Type) [Finite I] (u : I → (pullback pB (spMap (algebraMap R K)) ⟶ Z)), QuasiCompact pB → QuasiSeparated pB → LocallyOfFinitePresentation pZ → (∀ i, u i ≫ pZ = pullback.fst _ _ ≫ pB) → ∃ (f : R) (_ : f ≠ 0) (u' : I → (pullback pB (spMap (algebraMap R (Localization.Away f))) ⟶ Z)), ∀ i, u' i ≫ pZ = pullback.fst _ _ ≫ pB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → j ≫ u' i = u i := by
  intro R K _ _ _ _ _ _ B Z pB pZ I _ u hqc hqs hlfp hu
  have := hqc
  have := hqs
  have := hlfp
  obtain ⟨S, ψ, hSfg, -, hψ⟩ :=
    GlobalTheory.Spread.exists_fg_forall_comp_eq pB pZ u hu ⊥ Subalgebra.fg_bot
  obtain ⟨f, hf0, g, l, hgl⟩ := GlobalTheory.GenericSpread.exists_away_of_fg S hSfg
  have hmono : Mono (spMap (algebraMap R (Localization.Away f))) := inferInstance
  refine ⟨f, hf0, fun i => GlobalTheory.Spread.bcMap pB g ≫ ψ i, fun i => ⟨?_, fun j hj => ?_⟩⟩
  · rw [Category.assoc, (hψ i).1, ← Category.assoc, GlobalTheory.Spread.bcMap_fst]
  · have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap l.toRingHom := by
      apply (cancel_mono (spMap (algebraMap R (Localization.Away f)))).mp
      rw [Category.assoc, Category.assoc, GlobalTheory.Spread.spMap_algHom_comp, ← pullback.condition,
        ← pullback.condition, ← Category.assoc, hj]
    have hjb : j = GlobalTheory.Spread.bcMap pB l := GlobalTheory.Spread.eq_bcMap pB l hj hj2
    rw [hjb, ← Category.assoc, GlobalTheory.Spread.bcMap_comp_of_eq pB g l S.val hgl]
    exact (hψ i).2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.isProper_of_completeDVR_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  first | exact @GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | exact GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | (intros; apply GlobalTheory.ValuativeGeneric.isProper_of_lift_generic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.norm_psi_pull_localRingsOfIntegers : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  first | exact @GlobalTheory.ZH.PsiNormPull.norm_psi_pull | exact GlobalTheory.ZH.PsiNormPull.norm_psi_pull | (intros; apply GlobalTheory.ZH.PsiNormPull.norm_psi_pull <;> assumption)
end
