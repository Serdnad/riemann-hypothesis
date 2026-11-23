module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open UpperTheory.Et

namespace UpperTheory.IntegralSubring

variable {A D B : Type} [CommRing A] [CommRing D] [Algebra A D] [CommRing B]

private def sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) : Subalgebra A D :=
  { φ.range with
    algebraMap_mem' := fun r => ⟨α r, by rw [← h]; rfl⟩ }

private theorem mem_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) (x : D) :
    x ∈ sub φ α h ↔ ∃ y, φ y = x := Iff.rfl

private theorem coe_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) :
    ((sub φ α h : Subalgebra A D) : Set D) = Set.range φ := rfl

private theorem int_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) (t : B)
    (hint : ∀ x : B, IsIntegral (Subring.closure (Set.range α ∪ {t})) x) :
    ∀ x ∈ sub φ α h, IsIntegral (Algebra.adjoin A {φ t}) x := by
  rintro x ⟨y, rfl⟩
  have hle : Subring.closure (Set.range α ∪ {t}) ≤
      (Algebra.adjoin A {φ t}).toSubring.comap φ := by
    rw [Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hz)
    · have : φ (α r) = algebraMap A D r := by rw [← h]; rfl
      change φ (α r) ∈ Algebra.adjoin A {φ t}
      rw [this]
      exact Subalgebra.algebraMap_mem _ r
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Algebra.subset_adjoin (Set.mem_singleton _)
  let f : Subring.closure (Set.range α ∪ {t}) →+* Algebra.adjoin A {φ t} :=
    (φ.comp (Subring.closure (Set.range α ∪ {t})).subtype).codRestrict
      (Algebra.adjoin A {φ t}) (fun r => hle r.2)
  exact IsIntegral.map_of_comp_eq f φ (by ext r; rfl) (hint y)

private theorem roots_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D)
    (hφ : Function.Injective φ)
    (hr : ∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) :
    Roots (sub φ α h) := by
  intro p hp hd
  let g : B →+* sub φ α h := φ.codRestrict (sub φ α h) (fun y => (mem_sub φ α h _).2 ⟨y, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => hφ (congrArg Subtype.val hab), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (mem_sub φ α h x).1 hx
    exact ⟨y, rfl⟩
  let e := RingEquiv.ofBijective g hg
  obtain ⟨a, ha⟩ := hr (p.map (e.symm : sub φ α h →+* B)) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hpm : (p.map (e.symm : sub φ α h →+* B)).map (e : B →+* sub φ α h) = p := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext x
    simp
  rw [← hpm, Polynomial.eval_map]
  have := Polynomial.eval₂_hom (e : B →+* sub φ α h) a (p := p.map (e.symm : sub φ α h →+* B))
  rw [ha, map_zero] at this
  exact this

end UpperTheory.IntegralSubring

open UpperTheory.IntegralSubring in
theorem UpperTheory.isIntegral_of_localization_cover_unit_product :
    ∀ {A D B C : Type} [CommRing A] [CommRing D] [Algebra A D] [CommRing B] [CommRing C]
        (φ : B →+* D) (ψ : C →+* D) (α : A →+* B) (β : A →+* C),
        φ.comp α = algebraMap A D → ψ.comp β = algebraMap A D → Function.Injective φ → Function.Injective ψ →
        ∀ (t : B) (s : C), φ t * ψ s = 1 → (∀ x : D, ∃ (k : ℕ) (y : B), φ t ^ k * x = φ y) →
        (∀ x : D, ∃ (k : ℕ) (y : C), ψ s ^ k * x = ψ y) →
        (∀ x : B, IsIntegral (Subring.closure (Set.range α ∪ {t})) x) →
        (∀ x : C, IsIntegral (Subring.closure (Set.range β ∪ {s})) x) →
        (∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) →
        (∀ p : Polynomial C, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) →
        ∃ T : TC A D, T.Int ∧ Roots T.B ∧ Roots T.C ∧ (T.B : Set D) = Set.range φ ∧ (T.C : Set D) = Set.range ψ := by
  intro A D B C _ _ _ _ _ φ ψ α β hα hβ hφ hψ t s hts hlB hlC hiB hiC hrB hrC
  refine ⟨⟨sub φ α hα, sub ψ β hβ, φ t, ψ s, hts, (mem_sub φ α hα _).2 ⟨t, rfl⟩,
    (mem_sub ψ β hβ _).2 ⟨s, rfl⟩, ?_, ?_⟩, ⟨int_sub φ α hα t hiB, int_sub ψ β hβ s hiC⟩,
    roots_sub φ α hα hφ hrB, roots_sub ψ β hβ hψ hrC, coe_sub φ α hα, coe_sub ψ β hβ⟩
  · intro x
    obtain ⟨k, y, hy⟩ := hlB x
    exact ⟨k, (mem_sub φ α hα _).2 ⟨y, hy.symm⟩⟩
  · intro x
    obtain ⟨k, y, hy⟩ := hlC x
    exact ⟨k, (mem_sub ψ β hβ _).2 ⟨y, hy.symm⟩⟩
end

section

noncomputable section
open IsLocalRing UpperTheory.Et

theorem UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity :
    ∀ (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Int → ∀ (q : ℕ), 0 < q → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ (φ : LaurentPolynomial A →ₐ[A] D) (P : Polynomial (LaurentPolynomial A)) (n : ℕ), φ (LaurentPolynomial.T 1) = T.t ∧ φ (LaurentPolynomial.T (-1)) = T.s ∧ P.Monic ∧ P.eval₂ φ.toRingHom w = 0 ∧
        ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) := by
  intro A D _ _ _ _ T hI q hq w hw
  classical
  let τ : Dˣ := ⟨T.t, T.s, T.ts, by rw [mul_comm]; exact T.ts⟩
  let φ0 : LaurentPolynomial A →+* D := LaurentPolynomial.eval₂ (algebraMap A D) τ
  have hcomm : ∀ a : A, φ0 (algebraMap A (LaurentPolynomial A) a) = algebraMap A D a := by
    intro a
    simp [φ0, LaurentPolynomial.algebraMap_apply]
  let φ : LaurentPolynomial A →ₐ[A] D := { φ0 with commutes' := hcomm }
  have ht : φ (LaurentPolynomial.T 1) = T.t := by
    change φ0 _ = _
    simp [φ0, τ]
  have hs : φ (LaurentPolynomial.T (-1)) = T.s := by
    change φ0 _ = _
    simp [φ0, τ, zpow_neg]
  letI : Algebra (LaurentPolynomial A) D := φ.toRingHom.toAlgebra
  have hmap : ∀ r, algebraMap (LaurentPolynomial A) D r = φ r := fun _ => rfl
  have hadj : Algebra.adjoin A {T.t} ≤ φ.range := by
    refine Algebra.adjoin_le ?_
    rintro _ rfl
    exact ⟨_, ht⟩
  have hB : ∀ b ∈ T.B, IsIntegral (LaurentPolynomial A) b := by
    intro b hb
    obtain ⟨p, hpm, hp0⟩ := hI.1 b hb
    have hl : p.map (algebraMap (Algebra.adjoin A {T.t}) D) ∈
        Polynomial.lifts (algebraMap (LaurentPolynomial A) D) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨r, hr⟩ := hadj (p.coeff n).2
      exact ⟨r, hr⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hpm.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map]
    exact hp0
  have hint : Algebra.IsIntegral (LaurentPolynomial A) D := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, hk⟩ := T.locB x
    have hsI : IsIntegral (LaurentPolynomial A) T.s := by
      rw [← hs]
      exact isIntegral_algebraMap
    have : x = T.s ^ k * (T.t ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, mul_comm T.s, T.ts, one_pow, one_mul]
    rw [this]
    exact (hsI.pow k).mul (hB _ hk)
  have hu : w ^ q - 1 ∈ Ideal.map (algebraMap (LaurentPolynomial A) D)
      ((maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) := by
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro a ha d _
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have : algebraMap A D a = algebraMap (LaurentPolynomial A) D (algebraMap A (LaurentPolynomial A) a) := by
        rw [hmap]
        exact (hcomm a).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    · intro x y hx hy
      exact Ideal.add_mem _ hx hy
  obtain ⟨Q, hQm, hQ0, hQc⟩ := Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hu
  set I := (maximalIdeal A).map (algebraMap A (LaurentPolynomial A)) with hIdef
  have hmon : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : LaurentPolynomial A) hq.ne'
  have hdeg : (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)).natDegree ≠ 0 := by
    have := Polynomial.natDegree_X_pow_sub_C (n := q) (1 : LaurentPolynomial A)
    rw [map_one] at this
    rw [this]
    exact hq.ne'
  refine ⟨φ, Q.comp (Polynomial.X ^ q - 1), Q.natDegree, ht, hs, hQm.comp hmon hdeg, ?_, ?_⟩
  · rw [Polynomial.eval₂_comp]
    have : Polynomial.eval₂ φ.toRingHom w (Polynomial.X ^ q - 1 : Polynomial (LaurentPolynomial A)) = w ^ q - 1 := by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow]
    rw [this]
    exact hQ0
  · intro i
    have hcoef : ∀ j, (Q - Polynomial.X ^ Q.natDegree).coeff j ∈ I := by
      intro j
      by_cases hj : j = Q.natDegree
      · subst hj
        have : Q.coeff Q.natDegree = 1 := hQm
        simp [this]
      · simpa [Polynomial.coeff_X_pow, hj] using hQc j hj
    have heq : Q.comp (Polynomial.X ^ q - 1) - (Polynomial.X ^ q - 1) ^ Q.natDegree =
        (Q - Polynomial.X ^ Q.natDegree).comp (Polynomial.X ^ q - 1) := by
      simp [Polynomial.sub_comp]
    rw [heq, ← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_comp]
    have : (Q - Polynomial.X ^ Q.natDegree).map (Ideal.Quotient.mk I) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact hcoef j
    rw [this]
    simp

end
end

section

noncomputable section
open IsLocalRing UpperTheory.Et

open Polynomial in
private lemma split_of_units {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) (ζ : A) (hq : q ≠ 0) (h1 : ζ ^ q = 1)
    (hu : ∀ i ∈ Finset.range q, ∀ j ∈ Finset.range q, i ≠ j → IsUnit (ζ ^ i - ζ ^ j)) :
    (X ^ q - 1 : A[X]) = ∏ a ∈ Finset.range q, (X - C (ζ ^ a)) := by
  have hmon : ∀ a ∈ Finset.range q, (X - C (ζ ^ a) : A[X]).Monic := fun a _ => monic_X_sub_C _
  have hdvd : (∏ a ∈ Finset.range q, (X - C (ζ ^ a))) ∣ (X ^ q - 1 : A[X]) := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub (hu i hi j hj hij)
    · intro a _
      rw [dvd_iff_isRoot]
      show eval (ζ ^ a) (X ^ q - 1 : A[X]) = 0
      rw [eval_sub, eval_pow, eval_X, eval_one, ← pow_mul, mul_comm, pow_mul, h1, one_pow, sub_self]
  have hm1 : (X ^ q - 1 : A[X]).Monic := by
    have h := monic_X_pow_sub_C (1 : A) hq
    rwa [map_one] at h
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ hmon) hm1 hdvd ?_
  rw [natDegree_prod_of_monic _ _ hmon]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [← map_one C, natDegree_X_pow_sub_C _]

theorem UpperTheory.exists_goodRoot_of_henselian_sepClosed_residue :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)] (q : ℕ), IsUnit (q : A) → ∃ ζ : A, GoodRoot q ζ := by
  intro A _ _ _ q hqu
  have hqk : ((q : ResidueField A)) ≠ 0 := by
    rw [← map_natCast (residue A)]
    exact (residue_ne_zero_iff_isUnit _).2 hqu
  haveI : NeZero (q : ResidueField A) := ⟨hqk⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hqk (by simp)
  haveI : NeZero q := ⟨hq0⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField A) q
  obtain ⟨a0, rfl⟩ := residue_surjective z
  have ha0 : IsUnit a0 := (residue_ne_zero_iff_isUnit _).1 (hz.ne_zero hq0)
  have hmon : (Polynomial.X ^ q - 1 : Polynomial A).Monic := by
    have h := Polynomial.monic_X_pow_sub_C (1 : A) hq0
    rwa [map_one] at h
  obtain ⟨ζ, hroot, hζ⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ q - 1 : Polynomial A) hmon a0
    (by
      rw [← residue_eq_zero_iff]
      simp [hz.pow_eq_one])
    (by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_natCast,
        Polynomial.eval_pow, Polynomial.eval_X]
      exact hqu.mul (ha0.pow _))
  have hζq : ζ ^ q = 1 := by
    have h := hroot.eq_zero
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h
    exact sub_eq_zero.1 h
  have hres : residue A ζ = residue A a0 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hζ
  have hunits : ∀ i < q, ∀ j < q, i ≠ j → IsUnit (ζ ^ i - ζ ^ j) := by
    intro i hi j hj hij
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_pow, map_pow, hres]
    intro h
    exact hij (hz.pow_inj hi hj (sub_eq_zero.1 h))
  refine ⟨ζ, hζq, ?_, ?_⟩
  · intro a b hab
    exact hunits a.val (ZMod.val_lt a) b.val (ZMod.val_lt b) (fun h => hab (ZMod.val_injective q h))
  · intro S' _ φ x
    have key := split_of_units q ζ hq0 hζq
      (fun i hi j hj hij => hunits i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij)
    have h := congrArg (Polynomial.eval₂ φ x) key
    simpa [Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Polynomial.eval₂_C] using h

end
end

section

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem coord_mem_of_mem {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hx : x ∈ I.map (algebraMap A D)) (i : ι) :
    β.repr x i ∈ I := by
  have hx' : x ∈ I • (⊤ : Submodule A D) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on (p := fun y => β.repr y i ∈ I) hx' ?_ ?_
  · intro a ha n _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · intro y z hy hz
    rw [map_add (f := _), Finsupp.add_apply]
    exact I.add_mem hy hz

private theorem mem_smul_span_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) (W : Set ι) {x : D}
    (hW : x ∈ Submodule.span A (β '' W)) (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I • Submodule.span A (β '' W) := by
  have hs : ↑(β.repr x).support ⊆ W := (β.mem_span_image).1 hW
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun i hi => ?_)
  exact Submodule.smul_mem_smul (hc i) (Submodule.subset_span ⟨i, hs hi, rfl⟩)

private theorem mem_map_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I.map (algebraMap A D) := by
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))

theorem UpperTheory.exists_twoChart_quotient_of_finite_coord :
    ∀ (A D : Type) [CommRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → T.Coord → ∀ I : Ideal A, ∃ T' : TC A (D ⧸ I.map (algebraMap A D)), T'.Fin ∧ T'.t = Ideal.Quotient.mk _ T.t ∧ T'.s = Ideal.Quotient.mk _ T.s ∧
      (∀ j, ∀ y ∈ T'.S j, ∃ x ∈ T.S j, Ideal.Quotient.mk _ x = y) ∧ (∀ j, ∀ x ∈ T.S j, Ideal.Quotient.mk _ x ∈ T'.S j) ∧
      (∀ x ∈ T.B, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.B) ∧ ∀ x ∈ T.C, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.C := by
  classical
  intro A D _ _ _ T hF hC I
  obtain ⟨ι, β, U, V, hU, hV⟩ := hC
  set J := I.map (algebraMap A D) with hJ
  let q := Ideal.Quotient.mkₐ A J
  have hq : ∀ z, q z = Ideal.Quotient.mk J z := fun z => rfl
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have h1 : Ideal.Quotient.mk J T.t * Ideal.Quotient.mk J T.s = 1 := by
    rw [← map_mul, T.ts, map_one]
  let T' : TC A (D ⧸ J) :=
    { B := T.B.map q
      C := T.C.map q
      t := Ideal.Quotient.mk J T.t
      s := Ideal.Quotient.mk J T.s
      ts := h1
      tB := Subalgebra.mem_map.2 ⟨T.t, T.tB, rfl⟩
      sC := Subalgebra.mem_map.2 ⟨T.s, T.sC, rfl⟩
      locB := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locB x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩
      locC := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locC x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩ }
  refine ⟨T', ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨X, hX1, hX2⟩ := hF
    refine ⟨X.image q, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact Subalgebra.mem_map.2 ⟨x, hX1 x hx, rfl⟩
    · intro b hb
      obtain ⟨b0, hb0, rfl⟩ := Subalgebra.mem_map.1 hb
      have hm := Submodule.mem_map_of_mem (f := q.toLinearMap) (hX2 b0 hb0)
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨y, ⟨x, hx, i, rfl⟩, rfl⟩
      refine ⟨q x, Finset.mem_image.2 ⟨x, hx, rfl⟩, i, ?_⟩
      show q (T.t ^ i * x) = Ideal.Quotient.mk J T.t ^ i * q x
      rw [map_mul, map_pow]
      rfl
  · intro j y hy
    obtain ⟨hyB, hyC⟩ := Submodule.mem_inf.1 hy
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 hyB
    obtain ⟨c, hc, hce⟩ := Subalgebra.mem_map.1 (Submodule.mem_comap.1 hyC)
    have hw : T.t ^ j * c ∈ Submodule.span A (β '' V j) := by
      rw [← (hV j).1, Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_pow,
        mul_comm T.s, T.ts, one_pow, one_mul]
      exact hc
    have hbw : b - T.t ^ j * c ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, ← hq c, hce]
      change Ideal.Quotient.mk J b - Ideal.Quotient.mk J T.t ^ j *
        (Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J b) = 0
      rw [← mul_assoc, ← mul_pow, h1, one_pow, one_mul, sub_self]
    have hcoord := coord_mem_of_mem β I hbw
    have hbU : ↑(β.repr b).support ⊆ U := β.mem_span_image.1 (by rw [← hU]; exact hb)
    have hwV : ↑(β.repr (T.t ^ j * c)).support ⊆ V j := β.mem_span_image.1 hw
    set f := Finsupp.filter (· ∈ V j) (β.repr b) with hf
    have hrx : β.repr (β.repr.symm f) = f := β.repr.apply_symm_apply f
    refine ⟨β.repr.symm f, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · show β.repr.symm f ∈ Subalgebra.toSubmodule T.B
      rw [hU, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hbU hi.1
    · show β.repr.symm f ∈ Submodule.comap (LinearMap.mulLeft A (T.s ^ j)) (Subalgebra.toSubmodule T.C)
      rw [(hV j).1, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hi.2
    · refine Ideal.Quotient.eq.2 (mem_map_of_coord β I (fun i => ?_))
      rw [map_sub, Finsupp.sub_apply, hrx, hf, Finsupp.filter_apply]
      by_cases hi : i ∈ V j
      · rw [if_pos hi, sub_self]
        exact I.zero_mem
      · rw [if_neg hi, zero_sub]
        have hw0 : β.repr (T.t ^ j * c) i = 0 := Finsupp.notMem_support_iff.1 (fun h => hi (hwV h))
        have hci := hcoord i
        rw [map_sub, Finsupp.sub_apply, hw0, sub_zero] at hci
        exact I.neg_mem hci
  · intro j x hx
    obtain ⟨hxB, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨Subalgebra.mem_map.2 ⟨x, hxB, rfl⟩, ?_⟩
    show Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J x ∈ T.C.map q
    exact Subalgebra.mem_map.2 ⟨T.s ^ j * x, hxC, by rw [hq, map_mul, map_pow]⟩
  · intro x hx hxJ
    have hxs : x ∈ Submodule.span A (β '' U) := by rw [← hU]; exact hx
    rw [hU]
    exact mem_smul_span_of_coord β I U hxs (coord_mem_of_mem β I hxJ)
  · intro x hx hxJ
    have hC0 : Subalgebra.toSubmodule T.C = Submodule.span A (β '' V 0) := by
      rw [← (hV 0).1, pow_zero, LinearMap.mulLeft_one, Submodule.comap_id]
    have hxs : x ∈ Submodule.span A (β '' V 0) := by rw [← hC0]; exact hx
    rw [hC0]
    exact mem_smul_span_of_coord β I (V 0) hxs (coord_mem_of_mem β I hxJ)

end
end
