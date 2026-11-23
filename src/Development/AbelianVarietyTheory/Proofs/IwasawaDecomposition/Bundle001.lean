module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Quotient
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SplitTrace

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton, show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp,
    Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

theorem split_of_card (p : ℕ) (hp : p.Prime) {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K))
    (he : Function.Injective e) (hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal)
    (hcard : Fintype.card ι = Module.finrank ℚ K) :
    (∀ i, Ideal.absNorm (e i).asIdeal = p) ∧ Ideal.span {(p : 𝓞 K)} = ⨅ i, (e i).asIdeal := by
  classical
  set n := Module.finrank ℚ K
  have hcop : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      IsCoprime (e i).asIdeal (e j).asIdeal := fun i _ j _ hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  have hJ : ∏ i, (e i).asIdeal = ⨅ i, (e i).asIdeal := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]; simp
  have hle : Ideal.span {(p : 𝓞 K)} ≤ ∏ i, (e i).asIdeal := by
    rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_iInf.2 hmem
  have hdvd_i : ∀ i, Ideal.absNorm (e i).asIdeal ∣ p ^ n := fun i => by
    rw [← absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 (hmem i))
  choose k hkn hk using fun i => (Nat.dvd_prime_pow hp).1 (hdvd_i i)
  have hk1 : ∀ i, 1 ≤ k i := fun i => by
    rcases Nat.eq_zero_or_pos (k i) with h | h
    · exfalso
      have h1 := hk i
      rw [h, pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact (e i).isPrime.ne_top h1
    · exact h
  have hprod : Ideal.absNorm (∏ i, (e i).asIdeal) = p ^ ∑ i, k i := by
    rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => hk i
  have hsum_le : ∑ i, k i ≤ n := by
    have h := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hprod, absNorm_span_natCast] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hsum_eq : ∑ i, k i = ∑ _i : ι, 1 := by
    refine le_antisymm ?_ (Finset.sum_le_sum fun i _ => hk1 i)
    simpa [hcard] using hsum_le
  have hkeq : ∀ i, k i = 1 := fun i =>
    ((Finset.sum_eq_sum_iff_of_le (fun j _ => hk1 j)).1 hsum_eq.symm i (Finset.mem_univ i)).symm
  refine ⟨fun i => by rw [hk i, hkeq i, pow_one], ?_⟩
  rw [← hJ]
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hle
  have hnL : Ideal.absNorm L = 1 := by
    have h := congrArg Ideal.absNorm hL
    rw [map_mul, hprod, absNorm_span_natCast, show ∑ i, k i = n by simpa [hcard] using hsum_eq] at h
    have hpn : 0 < p ^ n := pow_pos hp.pos n
    exact Nat.eq_of_mul_eq_mul_left hpn (by rw [mul_one]; exact h.symm)
  rw [hL, Ideal.absNorm_eq_one_iff.1 hnL, Ideal.mul_top]

theorem trace_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (z : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) z = ∑ i, Algebra.trace R (A i) (z i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b i), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
  rw [show z * Pi.single i (b i k) = Pi.single i (z i * b i k) by
    funext j; by_cases h : j = i
    · subst h; simp
    · simp [h]]
  simp

theorem intTrace_modEq_sum : ∀ {K : Type} [Field K] [NumberField K] (p : ℕ), p.Prime → ∀ {ι : Type} [Fintype ι] (e : ι → HeightOneSpectrum (𝓞 K)), Function.Injective e → (∀ W : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ W.asIdeal ↔ ∃ i, e i = W) → Fintype.card ι = Module.finrank ℚ K → ∀ (x : 𝓞 K) (b : ι → ℤ), (∀ i, x - (b i : 𝓞 K) ∈ (e i).asIdeal) → ((Algebra.intTrace ℤ (𝓞 K) x : ℤ) : ZMod p) = ∑ i, (b i : ZMod p) := by
  intro K _ _ p hp ι _ e he hW hcard x b hxb
  classical
  have hmem : ∀ i, (p : 𝓞 K) ∈ (e i).asIdeal := fun i => (hW (e i)).2 ⟨i, rfl⟩
  obtain ⟨hnorm, hspan⟩ := split_of_card p hp e he hmem hcard
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = ⨅ i, (e i).asIdeal := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hspan
  have hPv : ∀ i, P ≤ (e i).asIdeal.comap (algebraMap ℤ (𝓞 K)) := fun i => by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact iInf_le _ i
  letI : ∀ i, Algebra (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.algebraQuotientOfLEComap (hPv i)
  haveI : ∀ i, IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => .of_algebraMap_eq' rfl
  haveI : ∀ i, Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) := fun i => Module.Finite.of_restrictScalars_finite ℤ _ _
  letI : ∀ i, Field (𝓞 K ⧸ (e i).asIdeal) := fun i => Ideal.Quotient.field _
  have hcop : Pairwise (Function.onFun IsCoprime fun i => (e i).asIdeal) := fun i j hij =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun h => hij (he h))
  let φ : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] (∀ i, 𝓞 K ⧸ (e i).asIdeal) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientInfRingEquivPiQuotient _ hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hφ : φ (Ideal.Quotient.mk _ x) = fun i => Ideal.Quotient.mk (e i).asIdeal x := rfl
  have hx1 : ∀ i, Ideal.Quotient.mk (e i).asIdeal x =
      algebraMap (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) (Ideal.Quotient.mk P (b i)) := fun i => by
    rw [Ideal.Quotient.eq.mpr (hxb i)]
    show _ = Ideal.Quotient.mk (e i).asIdeal (algebraMap ℤ (𝓞 K) (b i))
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfr : ∀ i, Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ (e i).asIdeal) = 1 := fun i => by
    have hcardv : Nat.card (𝓞 K ⧸ (e i).asIdeal) = p := by
      rw [← hnorm i, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ (e i).asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P (∑ i, b i) := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv φ, hφ, trace_pi]
    simp_rw [hx1, Algebra.trace_algebraMap, hfr, one_smul]

    rw [map_sum]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  rw [← Int.cast_sum, ZMod.intCast_eq_intCast_iff_dvd_sub]
  obtain ⟨m, hm⟩ := key
  exact ⟨-m, by linear_combination -hm⟩

end GlobalTheory.SplitTrace
end
end

section

namespace GlobalTheory.GramLinearMap

theorem gram_comb {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') {c d : ℂ}
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) (x y : U →₀ ℂ) :
    B (Finsupp.linearCombination ℂ f x) (Finsupp.linearCombination ℂ f y) * c =
      d * B' (Finsupp.linearCombination ℂ f' x) (Finsupp.linearCombination ℂ f' y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add (f := _), LinearMap.add_apply, add_mul, mul_add, h₁, h₂]
  | single u a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), add_mul, mul_add, h₁, h₂]
    | single v b =>
      simp only [Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      linear_combination (b * (starRingEnd ℂ) a) * h u v

theorem exists_linearMap_of_gram {P : Type} [AddCommGroup P] [Module ℂ P]
    {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') (hB : ∀ y : P, B y y = 0 → y = 0) {c d : ℂ} (hc : c ≠ 0)
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u : U, ψ (f' u) = f u := by
  set T := Finsupp.linearCombination ℂ f with hT
  set T' := Finsupp.linearCombination ℂ f' with hT'
  have hker : ∀ x, T' x = 0 → T x = 0 := by
    intro x hx
    apply hB
    have := gram_comb f f' h x x
    rw [← hT, ← hT', hx] at this
    simpa [hc] using this
  obtain ⟨g, hg⟩ := T'.rangeRestrict.exists_rightInverse_of_surjective T'.range_rangeRestrict
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (T ∘ₗ g)
  refine ⟨ψ, fun u => ?_⟩
  have h1 : T' (Finsupp.single u 1) = f' u := by simp [hT']
  have h2 : T (Finsupp.single u 1) = f u := by simp [hT]
  let z : LinearMap.range T' := ⟨f' u, _, h1⟩
  have h3 : ψ (f' u) = T (g z) := LinearMap.congr_fun hψ z
  have h4 : T' (g z) = f' u := congrArg Subtype.val (LinearMap.congr_fun hg z)
  have h5 : T (g z - Finsupp.single u 1) = 0 := hker _ (by rw [map_sub, h4, h1, sub_self])
  rw [map_sub, sub_eq_zero] at h5
  rw [h3, h5, h2]

end GlobalTheory.GramLinearMap
end

section

open Matrix

namespace GlobalTheory

theorem exists_isotropic_dual_of_skew {V : Type*} [AddCommGroup V] [Module ℚ V] {g : ℕ}
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (ε ψ : Fin g → V) (hB : ∀ x y, B x y = -B y x)
    (hε : ∀ i j, B (ε i) (ε j) = 0)
    (hψ : ∀ i j, B (ψ j) (ε i) = if i = j then 1 else 0) :
    ∃ φ : Fin g → V, (∀ i j, B (φ i) (φ j) = 0) ∧
      (∀ i j, B (φ j) (ε i) = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  classical
  have h1 : ∀ k l, B (ψ l) (ε k) = if k = l then 1 else 0 := fun k l => hψ k l
  have h2 : ∀ k l, B (ε k) (ψ l) = -(if k = l then 1 else 0) := fun k l => by
    rw [hB, h1]
  refine ⟨fun j => ψ j + ∑ k, (B (ψ j) (ψ k) / 2) • ε k, ?_, ?_, ?_⟩
  · intro i j

    simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, h2, mul_zero,
    Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_neg, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [hB (ψ i) (ψ j)]
  · intro i j

    simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, mul_zero,
    Finset.sum_const_zero, add_zero]
  · intro j
    simp only [add_sub_cancel_left]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_isotropic_dual_of_skew_matrix (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (ε ψ : Fin g → Fin r → ℚ) (hM : Mqᵀ = -Mq) (hε : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0)
    (hψ : ∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) :
    ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_isotropic_dual_of_skew (Matrix.toLinearMap₂' ℚ Mq) ε ψ
    (fun x y => by
      simp only [Matrix.toLinearMap₂'_apply']
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, Matrix.neg_mulVec,
        neg_dotProduct, dotProduct_comm])
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hε i j)
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hψ i j)
  exact ⟨φ, fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₁ i j,
    fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₂ i j, h₃⟩

end GlobalTheory
end

section

namespace GlobalTheory.TracePowEq

open Matrix

theorem trace_pow_eq {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
    (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (hPQ : P * Q = (1 : Matrix (Fin m) (Fin m) ℂ))
    (hQP : Q * P = (1 : Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ (a b : Fin m), E' a b = ∑ c : Fin n, ∑ d : Fin n, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c : Fin m, ((Matrix.of : (Fin m → Fin m → A) → Matrix (Fin m) (Fin m) A) E' ^ k) c c
      = ∑ c : Fin n, ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ k) c c := by

  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin n) A, S = Qᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin m) A, T = Pᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  have hTS : T * S = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hQP, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hST : S * T = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

  have hE : (Matrix.of E' : Matrix (Fin m) (Fin m) A) = S * Matrix.of E * T := by
    ext a b
    have key : ∀ c d, (Q c a * P b d) • E c d = S a c * E c d * T d b := by
      intro c d
      rw [hS, hT, Matrix.map_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.transpose_apply,
        Algebra.smul_def, map_mul, mul_assoc, Algebra.commutes (P b d) (E c d), ← mul_assoc]
    rw [Matrix.of_apply, h a b]
    simp only [key, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm

  have hpow : ∀ j : ℕ, (S * Matrix.of E * T) ^ j = S * Matrix.of E ^ j * T := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hST]
    | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      calc S * Matrix.of E ^ j * T * (S * Matrix.of E * T)
          = S * Matrix.of E ^ j * (T * S) * Matrix.of E * T := by simp only [Matrix.mul_assoc]
        _ = S * (Matrix.of E ^ j * Matrix.of E) * T := by rw [hTS, Matrix.mul_one, Matrix.mul_assoc S]

  have hcyc : ∀ X : Matrix (Fin n) (Fin m) A, ∑ c, (S * X) c c = ∑ d, (X * S) d d := by
    intro X
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Matrix.map_apply, Algebra.commutes]
  rw [hE, hpow, Matrix.mul_assoc, hcyc, Matrix.mul_assoc, hTS, Matrix.mul_one]

end GlobalTheory.TracePowEq
end

section

namespace GlobalTheory

theorem _root_.GlobalTheory.ksForm_baseChange :
    ∀ {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']
      (ι : LL →+* LL'), (∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) →
      ∀ {n : ℕ} (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n → LL')),
      (∀ x, x ∈ WK ↔ (fun k => ι (x k)) ∈ WK') →
      (∀ x' ∈ WK', ∃ x ∈ WK, x' = fun k => ι (x k)) →
      (∃ (m : ℕ) (b : Fin m → (Fin n → LL)), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧
        Submodule.span LL (Set.range b) = ⊤) →
      ∃ (m : ℕ) (b : Fin m → (Fin n → LL')), (∀ i, b i ∈ WK') ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK' ∧ LinearIndependent LL' b ∧
        Submodule.span LL' (Set.range b) = ⊤ := by
  intro LL LL' Ks _ _ _ _ _ ι hι n WK WK' hmem hsurj ⟨m, b, hbW, hKs, hspanK, hLL, hspanLL⟩
  let Φ : (Fin n → LL) →ₗ[Ks] (Fin n → LL') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by ext k; simp
      map_smul' := fun c x => by ext k; simp [Algebra.smul_def, hι] }
  have hker : LinearMap.ker Φ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => funext fun k => ?_
    have hk : ι (x k) = 0 := congrFun hx k
    simpa using hk
  have hmn : m = n := by
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hLL (by rw [hspanLL]))
    simp at h
    omega
  subst hmn
  have hLL' : LinearIndependent LL' (Φ ∘ b) := by
    have hu : IsUnit (Matrix.of b) := Matrix.linearIndependent_rows_iff_isUnit.1 hLL
    exact Matrix.linearIndependent_rows_iff_isUnit.2 (hu.map ι.mapMatrix)
  refine ⟨m, Φ ∘ b, fun i => (hmem _).1 (hbW i), hKs.map' Φ hker, ?_, hLL', ?_⟩
  · rw [Set.range_comp, Submodule.span_image, hspanK]
    ext x'
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hx'
      obtain ⟨x, hx, rfl⟩ := hsurj x' hx'
      exact ⟨x, hx, rfl⟩
  · exact hLL'.span_eq_top_of_card_eq_finrank' (by simp)

end GlobalTheory
end

section

namespace GlobalTheory.IsolatedTheoremThree

theorem main : (let d1 : (R : Type) → {A : Type} → [inst : CommRing R] → [inst_1 : CommRing A] → [inst_2 : Algebra R A] → (ℕ → A) → ℕ → Submodule R A := @(fun (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) ↦ Submodule.span R (γ '' {m : ℕ | m < N})); ∀ {R A : Type} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A], (∀ (n : ℕ), IsUnit (↑(Nat.factorial n) : A)) → ∀ (ξ : R) (γ : ℕ → A), (∀ (n : ℕ), (↑(Nat.factorial n) : A) * γ n = (Algebra.algebraMap R A : R → A) ξ ^ n) → ∀ (N : ℕ), ∀ w ∈ Submodule.span R (Set.range γ), ∃ w₁ ∈ d1 R γ N, (Algebra.algebraMap R A : R → A) ξ ^ N ∣ w - w₁) := by
  intro d1 R A _ _ _ hfac ξ γ hγ N w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, rfl⟩ := hw
    by_cases hn : n < N
    · exact ⟨γ n, Submodule.subset_span ⟨n, hn, rfl⟩, by simp⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [sub_zero]
      obtain ⟨u, hu⟩ := hfac n
      have hg : γ n = ↑u⁻¹ * algebraMap R A ξ ^ n := by
        rw [← hγ n, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
      have hp : algebraMap R A ξ ^ n = algebraMap R A ξ ^ N * algebraMap R A ξ ^ (n - N) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hg, hp]
      exact Dvd.intro (↑u⁻¹ * algebraMap R A ξ ^ (n - N)) (by ring)
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hda⟩ := hx
    obtain ⟨b, hb, hdb⟩ := hy
    refine ⟨a + b, Submodule.add_mem _ ha hb, ?_⟩
    rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
    exact dvd_add hda hdb
  | smul r x _ hx =>
    obtain ⟨a, ha, hda⟩ := hx
    refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
    rw [← smul_sub, Algebra.smul_def]
    exact Dvd.dvd.mul_left hda _

end GlobalTheory.IsolatedTheoremThree
end

section

open IsLocalRing

namespace GlobalTheory

theorem mem_ideal_smul_top_iff_mem {V : Type} [CommRing V] (I : Ideal V) (x : V) :
    x ∈ I • (⊤ : Submodule V V) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem localHom_map_mem_maximalIdeal_pow {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) {x : A}
    (hx : x ∈ maximalIdeal A ^ n) : α x ∈ maximalIdeal V ^ n := by
  have h1 : (maximalIdeal A).map α ≤ maximalIdeal V := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact map_nonunit α y hy
  have := Ideal.mem_map_of_mem α hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h1 n this

theorem eval_map_mem_maximalIdeal_pow_of_coeff_mem {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) (D : Polynomial A)
    (hD : ∀ i, D.coeff i ∈ maximalIdeal A ^ n) (η : V) :
    (D.map α).eval η ∈ maximalIdeal V ^ n := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (localHom_map_mem_maximalIdeal_pow α n (hD i))

end GlobalTheory
end
