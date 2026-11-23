module

import ReciprocityTheory.SemistableReduction.SemiDegZA
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.NonzeroSmulMemSpan

theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (A : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (↑A : Set (Fin n → E))) :
    ∃ (o : NumberField.RingOfIntegers E), o ≠ (0 : NumberField.RingOfIntegers E) ∧ o • x ∈ A := by
  apply ReciprocityTheory.MultiplicativeHeights.SemiPt.clear_denom <;> assumption

end GlobalTheory.NonzeroSmulMemSpan
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen

noncomputable section

namespace GlobalTheory.Exist.ProdOpen

section BaseChange
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (X Y : Over S)

def prodMap : ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left ≫ pullback.fst (X ⊗ Y).hom φ

theorem isPullback_prodMap :
    IsPullback (prodMap φ X Y) ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
      (X ⊗ Y).hom φ := by
  have h := IsPullback.of_hasPullback (X ⊗ Y).hom φ
  have hw := Over.w (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left :=
    (Over.forget S').map_isIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  rw [← hw]
  exact isPullback_iso_comp h _

theorem lift_prodMap {Z : Over S} (a : Z ⟶ X) (b : Z ⟶ Y) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ prodMap φ X Y =
      pullback.fst Z.hom φ ≫ (lift a b).left := by
  rw [prodMap, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback.lift_fst _ _ _

theorem toUnit_section (y : 𝟙_ (Over S) ⟶ Y) :
    toUnit ((Over.pullback φ).obj X) ≫ Functor.LaxMonoidal.ε (Over.pullback φ) ≫
      (Over.pullback φ).map y = (Over.pullback φ).map (toUnit X ≫ y) := by
  rw [← Category.assoc, Functor.Monoidal.toUnit_ε, Functor.map_comp]

end BaseChange

theorem bijective_baseChange {R T : Type} [CommRing R] [CommRing T] (g₁ : R →+* T) (X : Over (Sp R))
    (h : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom)) :
    (∀ (R' : Type) [CommRing R'] (g : T →+* R') (X' : Scheme.{0}) (π : X' ⟶ ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) := by
  intro R' _ g X' π f' hp
  have hq := hp.paste_horiz (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom g₁)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hq
  exact h R' _ X' _ f' hq

theorem triv_lift_prod {R : Type} [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X)
    (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y) [Flat X.hom] [Flat Y.hom] [IsProper X.hom] [IsProper Y.hom]
    (hX : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (hY : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (M : LB (X ⊗ Y).left) (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left))
    (h₂ : Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left))
    (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T)
    (he : ∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) (he' : e ∈ IsLocalRing.maximalIdeal T)
    (H : ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left)
      (f' : X' ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {e}))),
      IsPullback π f' (X ⊗ Y).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ≫
          Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π)) :
    Triv (M.pull (prodMap (Spec.map (CommRingCat.ofHom g)) X Y)) := by
  let φ : Sp T ⟶ Sp R := Spec.map (CommRingCat.ofHom g)
  have hp := IsPullback.of_hasPullback ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))))
  refine GlobalTheory.SmallExtLift.triv_prod_of_small_extension T e he ((Over.pullback φ).obj X) ((Over.pullback φ).obj Y)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map x₀)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map y₀)
    (inferInstanceAs (Flat (pullback.snd X.hom φ))) (inferInstanceAs (Flat (pullback.snd Y.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd X.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd Y.hom φ)))
    (bijective_baseChange g X hX) (bijective_baseChange g Y hY) (M.pull (prodMap φ X Y))
    (LB.isLB_pull hM _) ?_ ?_ _ _ _ hp he' ?_
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst X.hom φ) ?_ h₁)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst Y.hom φ) ?_ h₂)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · exact triv_pull_pull _ _ (H _ _ _ (hp.paste_horiz (isPullback_prodMap φ X Y)))

theorem surjective_prod {S : Scheme.{0}} (X Y : Over S) (x₀ : 𝟙_ (Over S) ⟶ X)
    (y₀ : 𝟙_ (Over S) ⟶ Y) : Surjective (X ⊗ Y).hom := by
  have hw : (lift x₀ y₀).left ≫ (X ⊗ Y).hom = 𝟙 S := Over.w (lift x₀ y₀)
  refine ⟨fun s => ⟨(lift x₀ y₀).left s, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, hw]
  rfl

theorem triv_basicOpen_of_triv_fibre_prod : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Nonempty (Perf (X ⊗ Y).hom M) → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (X ⊗ Y).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  intro R _ X Y x₀ y₀ _ _ _ _ hX hY hXY M hM hP h₁ h₂ K _ g₀ X₀ π₀ f₀ h₀ ht₀
  haveI : IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ (X ⊗ Y).hom M hM hP inferInstance
    (surjective_prod X Y x₀ y₀) K g₀ X₀ π₀ f₀ h₀ (hXY K g₀ X₀ π₀ f₀ h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ X₀ π₀ f₀ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      refine (H T g _ _ _ (isPullback_prodMap (Spec.map (CommRingCat.ofHom g)) X Y) (hu r hr)).1 ?_
      refine triv_lift_prod X Y x₀ y₀ hX hY M hM h₁ h₂ T g e he he' fun X' π f' hp => ?_
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hp
      exact (H _ _ X' π f' hp ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle)
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range (((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ (X ⊗ Y).hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm) (hp.lift_fst _ _ _) ht

end GlobalTheory.Exist.ProdOpen
end
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section RationalPoints

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem cap_fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_add]

omit [NumberField E] in
theorem cap_fv_neg (x : Fin n → E) : fv F (-x) = - fv F x := by
  funext i
  simp [fv, TensorProduct.tmul_neg]

omit [NumberField E] in
theorem cap_fv_zero : fv F (0 : Fin n → E) = 0 := by
  funext i
  simp [fv]

omit [NumberField E] in
theorem cap_fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [cap_fv_zero]
  | succ d ih => rw [succ_nsmul, succ_nsmul, cap_fv_add, ih]

omit [NumberField E] in
theorem cap_gen_mem (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (x : Fin n → E) (hx : x ∈ L) :
    (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) ∈ hat F L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

omit [NumberField E] in
theorem cap_fv_mem (L : Set (Fin n → E)) (x : Fin n → E) (hx : x ∈ L) : fv F x ∈ hat F L :=
  cap_gen_mem F L 1 (fun v => (v.adicCompletionIntegers F).one_mem) x hx

omit [NumberField E] in
theorem cap_split (r : F) (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (algebraMap F (FiniteAdeleRing (𝓞 F) F) r + d • a) ⊗ₜ[F] x i : Fin n → RA F E)
      = fv F (algebraMap F E r • x) + d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [fv, Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, algebraMap_smul]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

omit [NumberField E] in
theorem cap_tmul_nsmul (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => a ⊗ₜ[F] (d • x) i : Fin n → RA F E)
      = d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by
  funext i
  simp only [Pi.smul_apply]
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.tmul_add, ih]

theorem cap_exists_denom (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | (apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target ..)

end RationalPoints

theorem hat_rational_points_and_approx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L hfg hsp
  have h3 : ∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
    have hadd : ∀ z w : Fin n → RA F E, (∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, w - fv F x ∈ (hat F (L : Set (Fin n → E)))) →
        (∃ x : Fin n → E, z + w - fv F x ∈ (hat F (L : Set (Fin n → E)))) := by
      rintro z w ⟨x, hx⟩ ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      have := add_mem hx hy
      rw [cap_fv_add]
      convert this using 1
      abel
    have hzero : ∃ x : Fin n → E, (0 : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) :=
      ⟨0, by rw [cap_fv_zero, sub_zero]; exact zero_mem _⟩
    have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (y : Fin n → E), ∃ x : Fin n → E,
        (fun i => a ⊗ₜ[F] y i : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro a y
      obtain ⟨d, hd, hy⟩ := cap_exists_denom L hsp y
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F d hd).1 a
      refine ⟨algebraMap F E r • y, ?_⟩
      rw [cap_split, add_sub_cancel_left, ← cap_tmul_nsmul]
      exact cap_gen_mem F _ a' ha' _ hy
    have hsingle : ∀ (i : Fin n) (t : RA F E), ∃ x : Fin n → E,
        (Pi.single i t : Fin n → RA F E) - fv F x ∈ (hat F (L : Set (Fin n → E))) := by
      intro i t
      induction t using TensorProduct.induction_on with
      | zero => simpa using hzero
      | tmul a y =>
        have := hgen a (Pi.single i y)
        convert this using 4
        funext j
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      | add s t hs ht =>
        rw [Pi.single_add]
        exact hadd _ _ hs ht
    intro z
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_induction _ (fun z => ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E))))
      hadd hzero (fun i _ => hsingle i (z i))
  refine ⟨?_, ?_, h3, ?_⟩
  · intro v
    obtain ⟨s, e, c, -, hc, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
    have hv : fv F v = ∑ a, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (e.repr v a) : RA F E) • fv F (e a) := by
      funext i
      have h := congrFun (e.sum_repr v) i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp only [fv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul]
      rw [← TensorProduct.tmul_sum, h]
    rw [hv, GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff F E n L e c hc, hc]
    exact forall_congr' fun a => (GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt F E).2.1 (c a) _
  · intro N hN z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨r, a', ha', rfl⟩ := (GlobalTheory.T.finiteAdele_strong_approximation_mod_nat F N hN).2 a ha
      refine ⟨algebraMap F E (r : F) • x, ?_, _, cap_gen_mem F _ a' ha' x hx, cap_split F _ _ _ _⟩
      exact L.smul_mem (algebraMap (𝓞 F) (𝓞 E) r) hx
    | zero => exact ⟨0, L.zero_mem, 0, zero_mem _, by simp [cap_fv_zero]⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      obtain ⟨x', hx', w', hw', rfl⟩ := hz'
      refine ⟨x + x', L.add_mem hx hx', w + w', add_mem hw hw', ?_⟩
      rw [cap_fv_add, smul_add]
      abel
    | neg z _ hz =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hz
      refine ⟨-x, L.neg_mem hx, -w, neg_mem hw, ?_⟩
      rw [cap_fv_neg, smul_neg]
      abel
  · intro z
    obtain ⟨x, hx⟩ := h3 z
    obtain ⟨d, hd, hdx⟩ := cap_exists_denom L hsp x
    refine ⟨d, hd, ?_⟩
    have := add_mem (nsmul_mem hx d) (cap_fv_mem F (L : Set (Fin n → E)) _ hdx)
    rw [cap_fv_nsmul, ← smul_add, sub_add_cancel] at this
    exact this

end GlobalTheory.AdLat
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdLat.OpenLat

variable (F : Type) [Field F] [NumberField F]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  first
  | exact @_root_.GlobalTheory.IntegralOpen.isOpen_integral
  | exact _root_.GlobalTheory.IntegralOpen.isOpen_integral
  | (apply _root_.GlobalTheory.IntegralOpen.isOpen_integral <;> assumption)

theorem exists_nsmul_adele (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → N • a ∈ U := by
  first
  | exact @_root_.GlobalTheory.LocalNormBound.main
  | exact _root_.GlobalTheory.LocalNormBound.main
  | (apply _root_.GlobalTheory.LocalNormBound.main <;> assumption)

theorem nsmul_integral_mem_nhds (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (𝓞 F) F | ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
  first
  | exact @_root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | exact _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | (apply _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> assumption)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}


omit [Algebra F E] in
theorem exists_denom (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | (apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)

theorem isOpen_nsmul_hat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); (∀ N : ℕ, 0 < N → IsOpen {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y}) ∧ ∀ W ∈ 𝓝 (0 : RA F E), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), N • y ∈ W := by
  intro F E _ _ _ _ _ n L hL
  classical
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (FiniteAdeleRing (𝓞 F) F) _
  haveI : ContinuousSMul (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.toContinuousSMul _ _
  refine ⟨fun N hN => ?_, fun W hW => ?_⟩
  · let S : AddSubgroup (Fin n → RA F E) := (hat F (L : Set (Fin n → E))).map (nsmulAddMonoidHom N)
    have hS : {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y} = S := by
      ext z
      exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩
    rw [hS]
    refine S.isOpen_of_mem_nhds (g := 0) ?_
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    let b := Module.finBasis F E
    let B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
    choose d hd hdL using fun i k => exists_denom L hL (Pi.single i (b k))
    have hn : ∀ᶠ z : Fin n → RA F E in 𝓝 0, ∀ i k, ∃ a : FiniteAdeleRing (𝓞 F) F,
        (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ B.repr (z i) k = (N * d i k) • a := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro k
      have hc : Continuous fun z : Fin n → RA F E => B.coord k (z i) :=
        (IsModuleTopology.continuous_of_linearMap (B.coord k)).comp (continuous_apply i)
      have := nsmul_integral_mem_nhds F (N * d i k) (Nat.mul_pos hN (hd i k))
      have h0 : B.coord k ((0 : Fin n → RA F E) i) = 0 := map_zero _
      exact hc.continuousAt.preimage_mem_nhds (x := 0) (h0 ▸ this)
    refine Filter.mem_of_superset hn fun z hz => ?_
    choose a ha hza using hz
    refine ⟨∑ i, ∑ k, fun j => a i k ⊗ₜ[F] (d i k • (Pi.single i (b k) : Fin n → E)) j,
      sum_mem fun i _ => sum_mem fun k _ =>
        AddSubgroup.subset_closure ⟨a i k, ha i k, _, hdL i k, rfl⟩, ?_⟩
    funext j
    rw [nsmulAddMonoidHom_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Finset.sum_apply, ← B.sum_repr (z j), Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hza, Algebra.TensorProduct.basis_apply, Pi.smul_apply, Pi.single_eq_same, TensorProduct.tmul_smul,
        smul_smul, smul_assoc]
      congr 1
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · intro i _ hij
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero, TensorProduct.tmul_zero]
    · simp
  · let w := RingOfIntegers.basis E
    let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) → RA F E :=
      fun c => ∑ k, c k • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] algebraMap (𝓞 E) E (w k))
    have hφ : Continuous φ := continuous_finsetSum _ fun k _ => by fun_prop
    have h0 : φ 0 = 0 := by simp [φ]
    have h1 : φ ⁻¹' W ∈ 𝓝 0 := hφ.continuousAt.preimage_mem_nhds (h0 ▸ hW)
    rw [nhds_pi, Filter.mem_pi] at h1
    obtain ⟨I, -, t, ht, hsub⟩ := h1
    obtain ⟨N, hN, hNt⟩ := exists_nsmul_adele F (⋂ k, t k) (Filter.iInter_mem.mpr ht)
    refine ⟨N, hN, fun y hy => ?_⟩
    have hex : ∃ c, (∀ k v, c k v ∈ v.adicCompletionIntegers F) ∧ φ c = y := by
      induction hy using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hx
        refine ⟨fun k => w.repr x k • a, fun k v => zsmul_mem (ha v) _, ?_⟩

        conv_rhs => rw [← w.sum_repr x, map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_zsmul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      | zero => exact ⟨0, fun k v => zero_mem _, h0⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hc, rfl⟩ := hx
        obtain ⟨e, he, rfl⟩ := hy
        exact ⟨c + e, fun k v => add_mem (hc k v) (he k v), by simp [φ, add_smul, Finset.sum_add_distrib]⟩
      | neg x _ hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact ⟨-c, fun k v => neg_mem (hc k v), by simp [φ]⟩
    obtain ⟨c, hc, rfl⟩ := hex
    have h2 : N • φ c = φ (N • c) := by
      simp only [φ, Finset.smul_sum, Pi.smul_apply, smul_assoc]
    rw [h2]
    exact hsub fun k _ => Set.mem_iInter.mp (hNt (c k) (hc k)) k

end GlobalTheory.AdLat.OpenLat
end
