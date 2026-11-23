module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.QuadraticUnit

open Polynomial IsLocalRing

theorem norm_isUnit {R : Type} [CommRing R] [HenselianLocalRing R] (D : R) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (a * a - D * (b * b)) := by
  have hmax : ∀ x : R, x ∈ maximalIdeal R ↔ ¬ IsUnit x := fun x => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
  by_contra hnu
  have hm : a * a - D * (b * b) ∈ maximalIdeal R := (hmax _).2 hnu
  have hb : IsUnit b := by
    rcases hab with ha | hb
    · by_contra hb
      have hbm : b ∈ maximalIdeal R := (hmax b).2 hb
      have haa : a * a ∈ maximalIdeal R := by
        have he : a * a = (a * a - D * (b * b)) + D * (b * b) := by ring
        rw [he]
        exact add_mem hm (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hbm))
      exact (hmax _).1 haa (ha.mul ha)
    · exact hb
  obtain ⟨w, hw⟩ : ∃ w : R, b * w = 1 := ⟨_, hb.mul_val_inv⟩
  set c := a * w with hc
  have hcD : c * c - D ∈ maximalIdeal R := by
    have he : c * c - D = (a * a - D * (b * b)) * (w * w) := by
      have hw2 : D = D * ((b * w) * (b * w)) := by rw [hw]; ring
      rw [hc]
      nth_rewrite 1 [hw2]
      ring
    rw [he]
    exact Ideal.mul_mem_right _ _ hm
  have hcc : IsUnit (c * c) := by
    by_contra hcc
    have hDm : D ∈ maximalIdeal R := by
      have he : D = c * c - (c * c - D) := by ring
      rw [he]
      exact sub_mem ((hmax _).2 hcc) hcD
    exact (hmax _).1 hDm hD
  have hcu : IsUnit c := isUnit_of_mul_isUnit_left hcc
  obtain ⟨e, he, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C D) (monic_X_pow_sub_C D two_ne_zero) c
    (by simpa [sq] using hcD) (by simpa [derivative_X_pow, one_add_one_eq_two] using h2.mul hcu)
  apply hns
  refine ⟨e, ?_⟩
  have := he.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  linear_combination -this

theorem isUnit_add_mul {R O : Type} [CommRing R] [HenselianLocalRing R] [CommRing O]
    (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (ι a + ι b * δ) := by
  have hn := (norm_isUnit D hD h2 hns a b hab).map ι
  have he : (ι a + ι b * δ) * (ι a - ι b * δ) = ι (a * a - D * (b * b)) := by
    rw [map_sub, map_mul, map_mul, map_mul, ← hδ]
    ring
  rw [← he] at hn
  exact isUnit_of_mul_isUnit_left hn

theorem exists_eq_mul_isUnit {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D)
    (hspan : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (y : O) :
    ∃ (g : R) (u : O), IsUnit u ∧ y = ι g * u := by
  obtain ⟨p, q, rfl⟩ := hspan y
  rcases ValuationRing.dvd_total p q with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · refine ⟨p, 1 + ι r * δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns 1 r (Or.inl isUnit_one)
  · refine ⟨q, ι r + δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns r 1 (Or.inr isUnit_one)

theorem isPrincipalIdealRing_of_nonsquare_unit :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
      [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ _ ι δ D hδ hspan _ hD h2 hns
  refine ⟨fun I => ⟨?_⟩⟩
  obtain ⟨g₀, hg₀⟩ := (IsPrincipalIdealRing.principal (Ideal.comap ι I)).principal
  have hg₀I : ι g₀ ∈ I := by
    have hmem : g₀ ∈ Ideal.comap ι I := by
      rw [hg₀]
      exact Submodule.mem_span_singleton_self g₀
    exact Ideal.mem_comap.1 hmem
  refine ⟨ι g₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).2 hg₀I)⟩
  intro y hy
  obtain ⟨g, u, hu, rfl⟩ := exists_eq_mul_isUnit ι δ D hδ hspan hD h2 hns y
  have hg : g ∈ Ideal.comap ι I := by
    rw [Ideal.mem_comap]
    have he : ι g = ι g * u * ↑hu.unit⁻¹ := by rw [mul_assoc, hu.mul_val_inv, mul_one]
    rw [he]
    exact I.mul_mem_right _ hy
  rw [hg₀] at hg
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hg
  refine Ideal.mem_span_singleton.2 ⟨ι r * u, ?_⟩
  rw [← hr, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CompanionTheory.QuadraticUnit
end

section

namespace GlobalTheory.CompanionTheory.IntClosedAway

open Polynomial

theorem mem_span_of_eq_mul_integral {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (t a : A) (hred : IsReduced (A ⧸ Ideal.span {t})) (z : K)
    (hz : IsIntegral A z) (h : algebraMap A K a = algebraMap A K t * z) :
    a ∈ Ideal.span {t} := by
  obtain ⟨p, hp, hpz⟩ := hz
  have hinj := IsFractionRing.injective A K
  have h1 : (p.scaleRoots t).eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, h, Polynomial.scaleRoots_eval₂_mul, hpz, mul_zero]
  have h2 : (p.scaleRoots t).map (Ideal.Quotient.mk (Ideal.span {t})) = X ^ p.natDegree := by
    have ht0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    ext i
    rw [coeff_map, coeff_scaleRoots, coeff_X_pow, map_mul, map_pow, ht0]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, zero_pow (by omega), mul_zero]
    · subst hi
      simp [hp.coeff_natDegree]
    · rw [if_neg hi.ne', coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
  have h3 : Ideal.Quotient.mk (Ideal.span {t}) a ^ p.natDegree = 0 := by
    have h4 := congrArg (Ideal.Quotient.mk (Ideal.span {t})) h1
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h2] at h4
    simpa using h4
  exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, h3⟩)

theorem isIntegrallyClosed_of_away :
    ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) →
      IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  intro A _ _ t ht hred hcl
  have hle : Submonoid.powers t ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  let K := FractionRing A
  letI : Algebra (Localization.Away t) K :=
    (IsLocalization.lift (M := Submonoid.powers t) (g := algebraMap A K)
      (fun y => IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A))).toAlgebra
  haveI : IsScalarTower A (Localization.Away t) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  haveI : IsFractionRing (Localization.Away t) K :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers t) (Localization.Away t) K hle
  rw [isIntegrallyClosed_iff K]
  intro x hx
  have hxB : IsIntegral (Localization.Away t) x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxB
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj t y
  have hxa : algebraMap A K a = x * algebraMap A K t ^ n := by
    have h5 := congrArg (algebraMap (Localization.Away t) K) hna
    rw [map_mul, map_pow, hy, ← IsScalarTower.algebraMap_apply A (Localization.Away t) K,
      ← IsScalarTower.algebraMap_apply A (Localization.Away t) K] at h5
    exact h5.symm
  have ht' : algebraMap A K t ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ht
  clear hna
  induction n generalizing a with
  | zero => exact ⟨a, by simpa using hxa⟩
  | succ n ih =>
    have hz : IsIntegral A (x * algebraMap A K t ^ n) := hx.mul (isIntegral_algebraMap.pow n)
    have hmem : a ∈ Ideal.span {t} :=
      mem_span_of_eq_mul_integral t a hred _ hz (by rw [hxa]; ring)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ih b (mul_left_injective₀ ht' ?_)
    simp only [map_mul] at hxa
    simp only [hxa]
    ring

end GlobalTheory.CompanionTheory.IntClosedAway
end

section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LocalFinite

theorem map_maximalIdeal_le_jacobson_and_pow_le :
    ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Module.Finite O R],
      Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ (⊥ : Ideal R).jacobson ∧
        ∃ N : ℕ, (⊥ : Ideal R).jacobson ^ N ≤
          Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) := by
  intro O R _ _ _ _ _
  haveI : Algebra.IsIntegral O R := Algebra.IsIntegral.of_finite O R
  set m := IsLocalRing.maximalIdeal O with hm
  set I : Ideal R := Ideal.map (algebraMap O R) m with hI
  refine ⟨?_, ?_⟩
  · refine le_sInf ?_
    rintro M ⟨-, hM⟩
    refine Ideal.map_le_iff_le_comap.mpr ?_
    haveI : (Ideal.comap (algebraMap O R) M).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  · have hle : m ≤ Ideal.comap (algebraMap O R) I := Ideal.le_comap_map
    let f : (O ⧸ m) →+* (R ⧸ I) := Ideal.quotientMap I (algebraMap O R) hle
    letI : Field (O ⧸ m) := Ideal.Quotient.field m
    letI : Algebra (O ⧸ m) (R ⧸ I) := f.toAlgebra
    have hcomp : (f.comp (Ideal.Quotient.mk m)).Finite := by
      have h1 : (algebraMap O R).Finite := RingHom.finite_algebraMap.mpr inferInstance
      have h2 : (Ideal.Quotient.mk I).Finite :=
        RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
      have h3 : f.comp (Ideal.Quotient.mk m) = (Ideal.Quotient.mk I).comp (algebraMap O R) := by
        ext x; simp [f]
      rw [h3]
      exact h2.comp h1
    have hf : f.Finite := RingHom.Finite.of_comp_finite hcomp
    haveI : Module.Finite (O ⧸ m) (R ⧸ I) := hf
    haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite (O ⧸ m) (R ⧸ I)
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
    refine ⟨N, ?_⟩
    have hmap : Ideal.map (Ideal.Quotient.mk I) (⊥ : Ideal R).jacobson ≤
        (⊥ : Ideal (R ⧸ I)).jacobson := by
      refine le_sInf ?_
      rintro P ⟨-, hP⟩
      refine Ideal.map_le_iff_le_comap.mpr ?_
      haveI : (Ideal.comap (Ideal.Quotient.mk I) P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      exact sInf_le ⟨bot_le, this⟩
    have hz : Ideal.map (Ideal.Quotient.mk I) ((⊥ : Ideal R).jacobson ^ N) = ⊥ := by
      rw [Ideal.map_pow]
      exact le_bot_iff.mp ((Ideal.pow_right_mono hmap N).trans hN.le)
    intro x hx
    have : Ideal.Quotient.mk I x = 0 := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx
      rw [hz] at this
      simpa using this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory.CompanionTheory.LocalFinite
end

section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.JacUnit

theorem main (O O' R : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing R] [Algebra O R] (x : O' ⊗[O] R) (hx : x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson) : IsUnit (1 + x) := by
  classical
  letI : Algebra R (O' ⊗[O] R) := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom.toAlgebra
  have hint : Algebra.IsIntegral R (O' ⊗[O] R) := by
    let e : (R ⊗[O] O') ≃ₐ[O] (O' ⊗[O] R) := Algebra.TensorProduct.comm O R O'
    have hfin : (algebraMap R (R ⊗[O] O')).Finite := by
      rw [RingHom.finite_algebraMap]
      infer_instance
    have hcomp : (algebraMap R (O' ⊗[O] R)) = (e : (R ⊗[O] O') →+* (O' ⊗[O] R)).comp (algebraMap R (R ⊗[O] O')) := by
      ext r
      simp [e, RingHom.algebraMap_toAlgebra]
    have hf2 : (algebraMap R (O' ⊗[O] R)).Finite := by
      rw [hcomp]
      exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ e.surjective) hfin
    exact ⟨fun y => (hf2.to_isIntegral) y⟩
  have hle : Ideal.map (algebraMap R (O' ⊗[O] R)) (⊥ : Ideal R).jacobson ≤ (⊥ : Ideal (O' ⊗[O] R)).jacobson := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    have hc : (Ideal.comap (algebraMap R (O' ⊗[O] R)) m).IsMaximal :=
      by
        letI : Algebra.IsIntegral R (O' ⊗[O] R) := hint
        letI : Ideal.IsMaximal m := hm
        exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
    rw [← Ideal.mem_comap]
    exact (sInf_le (show _ ∈ {J : Ideal R | (⊥ : Ideal R) ≤ J ∧ J.IsMaximal} from ⟨bot_le, hc⟩) : (⊥ : Ideal R).jacobson ≤ _) hr
  have hx' : x ∈ (⊥ : Ideal (O' ⊗[O] R)).jacobson := hle hx
  have := Ideal.mem_jacobson_bot.1 hx' 1
  simpa [mul_one, add_comm] using this

end GlobalTheory.CompanionTheory.JacUnit
end

section

open TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerPushout

open KaehlerDifferential

theorem exists_retraction (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K B A R] :
    ∃ r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K],
      (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧
      (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) := by
  let e := KaehlerDifferential.tensorKaehlerEquiv K B A R
  refine ⟨e.symm.toLinearMap ∘ₗ KaehlerDifferential.map K B R R, ?_, ?_⟩
  · intro x
    have key : KaehlerDifferential.map K B R R (KaehlerDifferential.mapBaseChange K A R x) = e x := by
      induction x with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s w =>
        have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hw using Submodule.span_induction generalizing s with
        | mem w hw =>
          obtain ⟨a, rfl⟩ := hw
          simp [e, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        | zero => simp
        | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv]
        | smul a u _ hu =>
          rw [← TensorProduct.smul_tmul]
          exact hu _
    simp [key]
  · intro y
    induction y with
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    | tmul s w =>
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D K B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction generalizing s with
      | mem w hw =>
        obtain ⟨b, rfl⟩ := hw
        simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
      | zero => simp
      | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv, add_zero]
      | smul b u _ hu =>
        rw [← TensorProduct.smul_tmul]
        exact hu _

theorem range_sup_range (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [h : Algebra.IsPushout K A B R] :
    LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  set S := LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) with hS
  have hA : ∀ a : A, KaehlerDifferential.D K R (algebraMap A R a) ∈ S := fun a =>
    Submodule.mem_sup_left ⟨1 ⊗ₜ KaehlerDifferential.D K A a, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hB : ∀ b : B, KaehlerDifferential.D K R (algebraMap B R b) ∈ S := fun b =>
    Submodule.mem_sup_right ⟨1 ⊗ₜ KaehlerDifferential.D K B b, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hD : ∀ r : R, KaehlerDifferential.D K R r ∈ S := by
    intro r
    induction r using h.out.inductionOn with
    | tmul b => exact hB b
    | smul a y hy =>
      rw [Algebra.smul_def, Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ (hA a))
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  exact hD r

theorem kaehler_pushout_split : ∀ (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R], ∃ (r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K]) (π : Ω[R⁄K] →ₗ[R] R ⊗[B] Ω[B⁄K]), (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧ (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) ∧ (∀ x, π (KaehlerDifferential.mapBaseChange K A R x) = 0) ∧ (∀ y, π (KaehlerDifferential.mapBaseChange K B R y) = y) ∧ LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔ LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  intro K A B R _ _ _ _ _ _ _ _ _ _ _ h
  haveI hs : Algebra.IsPushout K B A R := h.symm
  obtain ⟨r, hr₁, hr₂⟩ := exists_retraction K A B R
  obtain ⟨π, hπ₁, hπ₂⟩ := exists_retraction K B A R
  exact ⟨r, π, hr₁, hr₂, hπ₂, hπ₁, range_sup_range K A B R⟩

end GlobalTheory.CompanionTheory.KaehlerPushout
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem prod_coordinate_bumps :
    ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A]
      [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ),
      (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) →
      Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets →
      (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧
        HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧
        ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧
      Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop
        (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ _ e ρ hρ hlim
  have hsub : ∀ k, tsupport (fun T : G => ∏ i, ρ k (e T i)) ⊆
      e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k)) := by
    intro k
    apply closure_minimal
    · intro T hT
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      intro i
      apply subset_tsupport
      rw [Function.mem_support] at hT ⊢
      exact (Finset.prod_ne_zero_iff.mp hT) i (Finset.mem_univ i)
    · exact (isClosed_set_pi fun i _ => isClosed_tsupport (ρ k)).preimage (map_continuous e)
  refine ⟨fun k => ⟨?_, ?_, fun T => Finset.prod_nonneg fun i _ => (hρ k).2.2 _⟩, ?_⟩
  · exact continuous_finsetProd _ fun i _ => (hρ k).1.comp ((continuous_apply i).comp (map_continuous e))
  · have hS : IsCompact (e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k))) :=
      (Homeomorph.isCompact_preimage (e : G ≃ₜ (ι → A))).mpr (isCompact_univ_pi fun _ => (hρ k).2.1)
    exact IsCompact.of_isClosed_subset hS (isClosed_tsupport _) (hsub k)
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro U hU
    have hV : e.symm ⁻¹' U ∈ nhds (0 : ι → A) :=
      (map_continuous e.symm).continuousAt.preimage_mem_nhds (by rwa [map_zero])
    rw [nhds_pi, Filter.mem_pi] at hV
    obtain ⟨I, -, t, ht, hIt⟩ := hV
    have hW : (⋂ i, t i) ∈ nhds (0 : A) := Filter.iInter_mem.mpr fun i => by simpa using ht i
    filter_upwards [hlim _ hW] with k hk
    intro T hT
    have h1 := hsub k hT
    simp only [Set.mem_preimage, Set.mem_univ_pi] at h1
    have h2 : e T ∈ I.pi t := fun i _ => Set.mem_iInter.mp (hk (h1 i)) i
    simpa using hIt h2

end GlobalTheory.CompanionTheory.BigCell
end
