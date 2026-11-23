module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.IntegralClosure
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj.DatLin

open NumberField ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E]

theorem sum_embeddings_eq (z : E) :
    (((Algebra.trace ℚ E z : ℚ) : ℂ)) = ∑ σ : E →+* ℂ, σ z := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

theorem trace_eq_sum_psi (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ ∈ Ψ, 2 * (τ z).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, sum_embeddings_eq, ← Finset.sum_add_sum_compl Ψ]

  have hc : ∑ σ ∈ Ψᶜ, σ z = ∑ τ ∈ Ψ, conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_coe, Finset.mem_compl] at hσ ⊢
      rw [hΨ, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
      exact hσ
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_compl]
      exact (hΨ τ).mp hτ
    · intro σ _; exact star_star σ
    · intro τ _; exact star_star τ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hc, ← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Complex.add_conj]

theorem sesq_repr [StarRing E] {V : Type} [AddCommGroup V] [Module E V] {ι : Type} [Fintype ι]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis ι E V) (x y : V) :
    h x y = ∑ i, ∑ j, star (b.repr x i) * h (b i) (b j) * b.repr y j := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
  starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Formalism.L2.Pj.DatLin
end
end

section

noncomputable section

namespace Formalism.L2.Pj.CompSplitPfC

open TensorProduct

variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]

theorem cspC_alg (s : S) : algebraMap S (S ⊗[P] FractionRing P) s = s ⊗ₜ (1 : FractionRing P) := rfl

theorem cspC_inj : Function.Injective (algebraMap S (S ⊗[P] FractionRing P)) := by
  have hf : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
    IsFractionRing.injective P (FractionRing P)
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (Algebra.linearMap P (FractionRing P)) hf
  have key : ∀ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      (LinearMap.lTensor S (Algebra.linearMap P (FractionRing P))) ((TensorProduct.rid P S).symm s) := by
    intro s
    rw [cspC_alg, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  intro a b h
  rw [key, key] at h
  exact (TensorProduct.rid P S).symm.injective (h2 h)

theorem cspC_artinian : IsArtinianRing (S ⊗[P] FractionRing P) := by
  haveI : Algebra.Etale (FractionRing P) (FractionRing P ⊗[P] S) := inferInstance
  haveI : Module.Finite (FractionRing P) (FractionRing P ⊗[P] S) :=
    Algebra.FormallyUnramified.finite_of_free (FractionRing P) _
  haveI : IsArtinianRing (FractionRing P ⊗[P] S) := IsArtinianRing.of_finite (FractionRing P) _
  exact Function.Surjective.isArtinianRing (f := (Algebra.TensorProduct.comm P (FractionRing P) S))
    (Algebra.TensorProduct.comm P (FractionRing P) S).surjective

theorem cspC_range (y : S ⊗[P] integralClosure P (FractionRing P)) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      Algebra.TensorProduct.map (AlgHom.id P S) (integralClosure P (FractionRing P)).val y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s z =>
    obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := FractionRing P)).mp z.2
    refine ⟨p • s, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, cspC_alg, ← hp,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨s', hs'⟩ := hb
    exact ⟨s + s', by rw [map_add (f := _), map_add (f := _), hs, hs']⟩

theorem cspC_idem_of {r : S ⊗[P] FractionRing P} (hr : IsIdempotentElem r) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s = r := by
  have hint : IsIntegral S r := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, hr.eq]
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := S)
    (B := FractionRing P)).2 ⟨r, hint⟩
  obtain ⟨s, hs⟩ := cspC_range y
  refine ⟨s, hs.trans ?_⟩
  exact congrArg Subtype.val hy

variable (P) in
include P in
theorem cspC_minimal_unique {q P1 P2 : Ideal S} [hq : q.IsPrime] (h1 : P1 ∈ minimalPrimes S)
    (h2 : P2 ∈ minimalPrimes S) (hq1 : P1 ≤ q) (hq2 : P2 ≤ q) : P1 = P2 := by
  by_contra hne
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors P)
  have hP1 : P1.IsPrime := Ideal.minimalPrimes_isPrime h1
  have hP2 : P2.IsPrime := Ideal.minimalPrimes_isPrime h2
  have hM : ∀ I ∈ minimalPrimes S, Disjoint (M : Set S) I := by
    intro I hI
    refine Set.disjoint_left.2 fun m hm hmI => ?_
    have hnzd : m ∈ nonZeroDivisors S := by
      refine mem_nonZeroDivisors_iff_right.2 fun x hx => cspC_inj (P := P) ?_
      have hu := IsLocalization.map_units (S ⊗[P] FractionRing P) (⟨m, hm⟩ : M)
      have h0 : algebraMap S (S ⊗[P] FractionRing P) x * algebraMap S (S ⊗[P] FractionRing P) m = 0 := by
        rw [← map_mul, hx, map_zero]
      rw [map_zero]
      exact (hu.mul_left_eq_zero).1 h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hI) hmI hnzd
  let Q1 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P1
  let Q2 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P2
  have hQ1 : Q1.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P1 hP1 (hM P1 h1)
  have hQ2 : Q2.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P2 hP2 (hM P2 h2)
  have hc1 : Q1.comap (algebraMap S (S ⊗[P] FractionRing P)) = P1 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP1 (hM P1 h1)
  have hc2 : Q2.comap (algebraMap S (S ⊗[P] FractionRing P)) = P2 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP2 (hM P2 h2)
  have hQne : Q1 ≠ Q2 := fun e => hne (by rw [← hc1, ← hc2, e])
  have := cspC_artinian (P := P) (S := S)
  obtain ⟨r, hr2, hrid, hrall⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne Q2
  have hr1 : r ∈ Q1 := hrall Q1 hQ1 hQne
  obtain ⟨s, hs⟩ := cspC_idem_of (P := P) hrid
  have hs1 : s ∈ P1 := by rw [← hc1, Ideal.mem_comap, hs]; exact hr1
  have hs2 : s ∉ P2 := by rw [← hc2, Ideal.mem_comap, hs]; exact hr2
  have hsid : s * s = s := cspC_inj (P := P) (by rw [map_mul, hs, hrid.eq])
  have h0 : (1 - s) * s ∈ P2 := by
    rw [sub_mul, one_mul, hsid, sub_self]
    exact P2.zero_mem
  have h1s : 1 - s ∈ P2 := (hP2.mem_or_mem h0).resolve_right hs2
  have : (1 : S) ∈ q := by
    have := q.add_mem (hq2 h1s) (hq1 hs1)
    rwa [sub_add_cancel] at this
  exact hq.ne_top ((Ideal.eq_top_iff_one _).2 this)

end Formalism.L2.Pj.CompSplitPfC
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Matrix IsDedekindDomain

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]


variable (V) in
abbrev valI : Valuation F (WithZero (Multiplicative ℤ)) := (IsDiscreteValuationRing.maximalIdeal V).valuation F

theorem exists_of_valI_le_one {x : F} (h : valI (V := V) x ≤ 1) : ∃ a : V, algebraMap V F a = x := by
  have hall : ∀ w : IsDedekindDomain.HeightOneSpectrum V, w = IsDiscreteValuationRing.maximalIdeal V := by
    intro w
    first
    | exact IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
    | (ext1; exact IsLocalRing.eq_maximalIdeal w.isMaximal)
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F x
    (fun w => by rw [hall w]; exact h)
  exact ⟨a, ha⟩

theorem exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun r => valI (V := V) (A r 0)) Finset.univ_nonempty
  have hcol : ∃ r, A r 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
  have hp0 : A p 0 ≠ 0 := by
    obtain ⟨r, hr⟩ := hcol
    intro h0
    have := hp r (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hr ((valI (V := V)).zero_iff.1 (le_antisymm this zero_le))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) V := σ.permMatrix V
  have hc : ∀ i, ∃ a : V, algebraMap V F a = A (σ i) 0 / A p 0 := by
    intro i
    apply exists_of_valI_le_one
    rw [map_div₀]
    have hpos : valI (V := V) (A p 0) ≠ 0 := by simpa using hp0
    rw [div_le_one₀ (zero_lt_iff.2 hpos)]
    exact hp _ (Finset.mem_univ _)
  choose c hc using hc
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -c i else 0
  refine ⟨E * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · have hE : E.det = 1 := by
        rw [Matrix.det_of_isLowerTriangular E]
        · simp [E]
        · intro i j hij
          have hij' : i < j := hij
          have hj : j ≠ 0 := fun h => by subst h; exact Fin.not_lt_zero _ hij'
          simp only [E, Matrix.of_apply, if_neg (ne_of_lt hij'), if_neg hj]
      rw [hE]; exact isUnit_one
    · simp only [P, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro i
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
    have hPA : ∀ r, (P.map (algebraMap V F) * A) r 0 = A (σ r) 0 := by
      intro r
      simp [P, Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [hPA, Matrix.map_apply, E, Matrix.of_apply]
    rw [if_neg (Fin.succ_ne_zero i)]
    simp only [if_true, Fin.succ_ne_zero, map_neg, map_one, map_zero, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one, one_mul]
      rw [hc]
      have : σ 0 = p := by simp [σ]
      rw [this]
      field_simp
      ring
    · intro j _ hji
      rw [if_neg (fun h => hji (Fin.succ_injective _ h).symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h

theorem iwasawa : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U := by
  intro n
  induction n with
  | zero =>
    intro A _
    exact ⟨1, A, by simp, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    obtain ⟨Q, hQ, hQA⟩ := exists_clear_col (V := V) (n := n) A hA
    set B := Q.map (algebraMap V F) * A with hB
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [hQA, B]
    have hQF : (Q.map (algebraMap V F)).det = algebraMap V F Q.det := by
      rw [RingHom.map_det]; rfl
    have hBne : B.det ≠ 0 := by
      rw [hB, Matrix.det_mul, hQF]
      exact mul_ne_zero (hQ.map (algebraMap V F)).ne_zero hA
    have hB00 : B 0 0 ≠ 0 := by intro h; apply hBne; rw [hdetB, h, zero_mul]
    obtain ⟨k', U', hk', hU', hd', hA'⟩ := ih (B.submatrix Fin.succ Fin.succ) (by
      intro h; apply hBne; rw [hdetB, h, mul_zero])
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => k' i' j') j) i
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      Fin.cases (B 0 j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hKU : K.map (algebraMap V F) * U = B := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ, hQA]
        · have h1 := congrFun (congrFun hA' i') j'
          simp only [Matrix.submatrix_apply] at h1
          rw [h1]
          simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
    have hKdet : K.det = k'.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [K]
      rfl
    refine ⟨Q⁻¹ * K, U, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hKdet]
      exact (Matrix.isUnit_nonsing_inv_det Q hQ).mul hk'
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [U]
        | succ j' =>
          have : j' < i' := Fin.succ_lt_succ_iff.1 hij
          simpa [U] using hU' this
    · intro i
      induction i using Fin.cases with
      | zero => simpa [U] using hB00
      | succ i' => simpa [U] using hd' i'
    · rw [Matrix.map_mul, Matrix.mul_assoc, hKU, hB, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul Q hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem upper_inv {m : ℕ} (U : Matrix (Fin m) (Fin m) F) (hU : U.BlockTriangular id) (hd : ∀ i, U i i ≠ 0) :
    U⁻¹.BlockTriangular id ∧ (∀ i, U⁻¹ i i ≠ 0) ∧ U * U⁻¹ = 1 := by
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hinv : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  refine ⟨hinv, fun i => ?_, Matrix.mul_nonsing_inv U hu⟩
  have h1 : (U⁻¹ * U) i i = 1 := by rw [Matrix.nonsing_inv_mul U hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hinv hlt, zero_mul]
    · rw [hU hgt, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem iwasawa' {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (N : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ N.BlockTriangular id ∧
      (∀ i, N i i ≠ 0) ∧ A * N = k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, hA⟩ := iwasawa (V := V) A hA
  obtain ⟨hinv, hdinv, hUU⟩ := upper_inv U hU hd
  refine ⟨k, U⁻¹, hk, hinv, hdinv, ?_⟩
  rw [hA, Matrix.mul_assoc, hUU, Matrix.mul_one]

end Formalism.L2.Pj
end
end
