module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle242
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
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
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem punctured_line_open_cofinite : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  intro k _ V hV χ₁ h₁
  classical

  have key : ∀ (χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k)
      (g : Localization.Away (Polynomial.X : Polynomial k)),
      g ∉ PrimeSpectrum.asIdeal (spMap χ.toRingHom (IsLocalRing.closedPoint k)) ↔ χ g ≠ 0 := by
    intro χ g
    rw [Spec.map_base]
    change g ∉ (PrimeSpectrum.comap χ.toRingHom (IsLocalRing.closedPoint k)).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hb : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hb, Ideal.mem_bot]
    rfl
  have hV' : IsOpen (V : Set (PrimeSpectrum (Localization.Away (Polynomial.X : Polynomial k)))) := hV
  obtain ⟨_, ⟨g, rfl⟩, hg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens).exists_subset_of_mem_open h₁ hV'
  have hg₁ : χ₁ g ≠ 0 := (key χ₁ g).1 hg
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial k) g
  have hXu : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 := fun χ =>
    ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map χ).ne_zero
  have hev : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, ∀ q : Polynomial k,
      χ (algebraMap (Polynomial k) _ q) = q.eval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro χ q
    have : χ.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))
        = Polynomial.aeval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
      apply Polynomial.algHom_ext
      simp
    have h2 := congrArg (fun φ => φ q) this
    simpa [Polynomial.coe_aeval_eq_eval] using h2
  have hχp : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ p) = χ g * (χ (algebraMap (Polynomial k) _ Polynomial.X)) ^ n := by
    intro χ
    rw [← hp, map_mul, map_pow]
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hχp χ₁
    rw [map_zero, map_zero] at this
    exact mul_ne_zero hg₁ (pow_ne_zero _ (hXu χ₁)) this.symm
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  rintro c ⟨hc0, hcall⟩
  by_contra hroot
  have hunit : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k),
      IsUnit (Polynomial.aeval c (y : Polynomial k)) := by
    rintro ⟨_, m, rfl⟩
    simp [hc0]
  let χc : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k)) hunit
  have hχc : χc (algebraMap (Polynomial k) _ Polynomial.X) = c := by
    simp [χc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  apply hcall χc hχc
  apply hgV
  refine (key χc g).2 ?_
  intro h0
  apply hroot
  have := hχp χc
  rw [h0, zero_mul, hev, hχc] at this
  exact this

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open PrimeSpectrum in
theorem prime_line_mem_range_comap_mapRingHom {R K : Type} [CommRing R] [Field K] (χ : R →+* K)
    (hχ : Function.Surjective χ) (P : PrimeSpectrum (Polynomial R))
    (hP : PrimeSpectrum.comap (algebraMap R (Polynomial R)) P = PrimeSpectrum.comap χ (IsLocalRing.closedPoint K)) :
    P ∈ Set.range (PrimeSpectrum.comap (Polynomial.mapRingHom χ)) := by
  have hker : RingHom.ker χ ≤ Ideal.comap Polynomial.C P.asIdeal := by
    intro a ha
    have h1 := congrArg PrimeSpectrum.asIdeal hP
    simp only [PrimeSpectrum.comap_asIdeal] at h1
    have : a ∈ Ideal.comap (algebraMap R (Polynomial R)) P.asIdeal := by
      rw [h1, Ideal.mem_comap, RingHom.mem_ker.mp ha]
      exact Ideal.zero_mem _
    exact this
  rw [range_comap_of_surjective _ _ (Polynomial.map_surjective χ hχ), PrimeSpectrum.mem_zeroLocus,
    Polynomial.ker_mapRingHom, SetLike.coe_subset_coe]
  exact Ideal.map_le_iff_le_comap.mpr hker

theorem fibre_line_over_surjection : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  intro R K _ _ χ hχ x hx
  exact prime_line_mem_range_comap_mapRingHom χ hχ x hx

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open Polynomial in
theorem poly_eq_C_of_eq_aeval_invSelf {K : Type} [CommRing K] (p q : K[X])
    (h : algebraMap K[X] (Localization.Away (X : K[X])) p =
      aeval (IsLocalization.Away.invSelf (X : K[X]) : Localization.Away (X : K[X])) q) :
    p = C (p.eval 0) := by
  set L := Localization.Away (X : K[X])
  set n := q.natDegree
  letI : Invertible (algebraMap K[X] L X) :=
    ⟨IsLocalization.Away.invSelf (X : K[X]),
      by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf _, IsLocalization.Away.mul_invSelf _⟩
  have hr : (q.reflect n).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
  have key := eval₂_reflect_mul_pow (algebraMap K L) (algebraMap K[X] L X) n (q.reflect n) hr
  rw [reflect_reflect] at key
  have hev : ∀ r : K[X], eval₂ (algebraMap K L) (algebraMap K[X] L X) r = algebraMap K[X] L r :=
    fun r => eval₂_algebraMap_X r (IsScalarTower.toAlgHom K K[X] L)
  have h2 : algebraMap K[X] L (p * X ^ n) = algebraMap K[X] L (q.reflect n) := by
    rw [map_mul, map_pow, h, aeval_def, ← hev (q.reflect n)]
    exact key
  have hinj : Function.Injective (algebraMap K[X] L) :=
    IsLocalization.injective L (Submonoid.powers_le.2 X_mem_nonzeroDivisors)
  have h3 := hinj h2
  have hdeg : (p * X ^ n).natDegree ≤ n := h3 ▸ hr
  have hp0 : p.natDegree = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    have hc : (p * X ^ n).coeff (p.natDegree + n) ≠ 0 := by
      rw [coeff_mul_X_pow]; exact mt leadingCoeff_eq_zero.mp hp
    have := le_natDegree_of_ne_zero hc
    omega
  rw [← coeff_zero_eq_eval_zero]
  exact eq_C_of_natDegree_eq_zero hp0

end GlobalTheory

namespace GlobalTheory

theorem chart_map_into_affine_const (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens)
    (hW : IsAffineOpen W) (g₀ g₁ : Sp (Polynomial K) ⟶ Y) (h₀ : ∀ x, g₀ x ∈ W) (h₁ : ∀ x, g₁ x ∈ W)
    (h : spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) :
        Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁) :
    g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  haveI := hW.isOpenImmersion_fromSpec
  have r₀ : Set.range g₀.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₀ x
  have r₁ : Set.range g₁.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₁ x
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₀ r₀)
  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₁ r₁)
  have e₀ : Spec.map φ₀ ≫ hW.fromSpec = g₀ := by rw [hφ₀]; exact IsOpenImmersion.lift_fac _ _ _
  have e₁ : Spec.map φ₁ ≫ hW.fromSpec = g₁ := by rw [hφ₁]; exact IsOpenImmersion.lift_fac _ _ _
  rw [← e₀, ← e₁] at h
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
  rw [Spec.map_inj] at h
  have key : ∀ a, φ₀ a = Polynomial.C ((φ₀ a).eval 0) := fun a =>
    poly_eq_C_of_eq_aeval_invSelf (φ₀ a) (φ₁ a) (congrArg (fun f => f.hom a) h)
  rw [← e₀]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact key a

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sections_eqLocus_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom →
    ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R,
      ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first
  | exact @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | (apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq ..)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_fst_eq_spMap_comp_unit {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ η[G].left := by
  simp [Functor.grpObjObj, Functor.monObjObj]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_snd_eq_id {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = 𝟙 _ := by
  have h := Over.w (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G])
  simpa using h


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.semilinear_symm_fixes_unit : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G ≅ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K' ⟶ pullback G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ x := by
  intro K W K' _ _ _ _ _ A _ G _ e he σ x hx₁ hx₂

  have hxη : x = (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left := by
    apply pullback.hom_ext
    · rw [hx₁, unit_pullback_left_comp_fst_eq_spMap_comp_unit]
    · rw [hx₂, unit_pullback_left_comp_snd_eq_id]
      rfl
  have hη : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left ≫ e.hom.left =
      (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') := by
    rw [_root_.GlobalTheory.spMap_comp_spMap]
    congr 1
    ext y
    exact σ.commutes y
  have hinv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have hmap : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left ≫
      pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _)
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [unit_pullback_left_comp_fst_eq_spMap_comp_unit, ← Category.assoc, hσ]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, unit_pullback_left_comp_snd_eq_id]
      simp
  rw [hxη, ← Category.assoc, hη, ← Category.assoc, hmap, Category.assoc, ← hη, Category.assoc,
    hinv, Category.comp_id]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S) (c : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left), ∃ s : LB.Sec (twistLB P.A P.L 2 c), y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | exact GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibreGen.exists_sec_mem_nonzeroLocus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_fibre_uniformisation_appellHumbert_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ₀ : c.F →+* ℂ) (U : Unf Xo c σ₀ r), 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (w : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W) (ρ : E →+* ℂ) (z : FrPt Xo c (CAt σ₀)), z.x = (U.un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt σ₀), (∀ i, IsCombAt (U.un k w).x ((U.un k w).u ρ) (C i) (z.u ρ i)) → ∃ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x) (u' : HolUnif T.pol.A T.pol.L W.g) (χ' : u'.Λ → ℂ), u'.IsAH Wu.Hm χ' ∧ ∀ i, ∃ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i ∧ u'.IsDiff (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) w' := by
  first | exact @GlobalTheory.FibreUnifComb.exists_unif_isDiff_comb | exact GlobalTheory.FibreUnifComb.exists_unif_isDiff_comb | (intros; apply GlobalTheory.FibreUnifComb.exists_unif_isDiff_comb <;> assumption)
end
