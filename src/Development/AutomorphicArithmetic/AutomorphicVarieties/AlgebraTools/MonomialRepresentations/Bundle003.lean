module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Polynomial Matrix

private theorem charpoly_fromBlocks_antidiagonal_fin_two {F : Type} [Field F] (P Q : Matrix (Fin 2) (Fin 2) F) :
    (fromBlocks 0 P Q 0).charpoly = X ^ 4 - C ((Q * P) 0 0 + (Q * P) 1 1) * X ^ 2
      + C ((Q * P) 0 0 * (Q * P) 1 1 - (Q * P) 0 1 * (Q * P) 1 0) := by
  unfold Matrix.charpoly
  rw [charmatrix_fromBlocks]
  have hcz : charmatrix (0 : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ : Fin 2 => (X : F[X])) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [charmatrix_apply]
    · simp [charmatrix_apply, diagonal_apply_ne _ h]
  rw [hcz]
  generalize hS : (diagonal (fun _ : Fin 2 => (X : F[X])) : Matrix (Fin 2) (Fin 2) F[X]) = S
  generalize hP' : P.map C = P'
  generalize hQ' : Q.map C = Q'
  have hcomm : S * P' = P' * S := by
    subst hS
    ext i j
    simp [mul_comm]
  have hprod : fromBlocks S (-P') (-Q') S * fromBlocks S P' 0 S
      = fromBlocks (S * S) 0 (-(Q' * S)) (S * S - Q' * P') := by
    rw [fromBlocks_multiply, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · rw [hcomm, neg_mul, add_neg_cancel]
    · simp
    · rw [neg_mul, add_comm, sub_eq_add_neg]
  have hdet := congrArg det hprod
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdet
  have hSd : det S = X ^ 2 := by
    subst hS
    simp [det_diagonal, Fin.prod_univ_two, sq]
  rw [det_mul, hSd] at hdet
  have hX : (X ^ 2 * X ^ 2 : F[X]) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ X_ne_zero)
  have hG : det (fromBlocks S (-P') (-Q') S) = det (S * S - Q' * P') := by
    apply mul_right_cancel₀ hX
    rw [hdet]
    ring
  rw [hG, det_fin_two]
  subst hS hP' hQ'
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem separable_biquadratic_of_ne_zero_of_discrim_ne_zero {F : Type} [Field F] (a d : F) (h2 : (2 : F) ≠ 0) (hd : d ≠ 0)
    (he : a ^ 2 - 4 * d ≠ 0) : (X ^ 4 - C a * X ^ 2 + C d : F[X]).Separable := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hk : 4 * d * (8 * d - 2 * a ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero h4 hd) ?_
    rw [show 8 * d - 2 * a ^ 2 = -2 * (a ^ 2 - 4 * d) by ring]
    exact mul_ne_zero (neg_ne_zero.2 h2) he
  have hder : derivative (X ^ 4 - C a * X ^ 2 + C d : F[X]) = 4 * X ^ 3 - 2 * C a * X := by
    rw [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X_pow, derivative_C]
    norm_num
    simp only [map_ofNat]
    ring
  have hCe : (C (8 * d - 2 * a ^ 2) : F[X]) = 8 * C d - 2 * C a ^ 2 := by
    simp only [map_mul, map_sub, map_pow, map_ofNat]
  have key : (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)) * (X ^ 4 - C a * X ^ 2 + C d)
      + (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X) * (4 * X ^ 3 - 2 * C a * X)
      = C (4 * d * (8 * d - 2 * a ^ 2)) := by
    rw [map_mul, map_mul, hCe]
    simp only [map_ofNat]
    ring
  unfold Polynomial.Separable IsCoprime
  refine ⟨C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)),
    C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X), ?_⟩
  rw [hder]
  calc _ = C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * C (4 * d * (8 * d - 2 * a ^ 2)) := by rw [← key]; ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hk, C_1]

private theorem discSwap_lemma_3 {K : Type} [Field K] (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ)
    (hw₁ : StrictAnti w₁) (hw₂ : StrictAnti w₂) (hb : b 0 0 ≠ 0) (hc : c 0 0 ≠ 0)
    (hbd : b.det ≠ 0) (hcd : c.det ≠ 0) :
    let N := (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) *
      (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i));
    N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 ∧
      (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0) ≠ 0 := by
  intro N
  have h01 : (0 : Fin 2) < 1 := by decide
  obtain ⟨n, hn, hn0⟩ : ∃ n : ℕ, w₁ 0 = w₁ 1 + n ∧ 0 < n :=
    ⟨(w₁ 0 - w₁ 1).toNat, by have := hw₁ h01; omega, by have := hw₁ h01; omega⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m : ℕ, w₂ 0 = w₂ 1 + m ∧ 0 < m :=
    ⟨(w₂ 0 - w₂ 1).toNat, by have := hw₂ h01; omega, by have := hw₂ h01; omega⟩
  set f := algebraMap K (RatFunc K) with hf
  set Y : RatFunc K := RatFunc.X with hY
  have hY0 : Y ≠ 0 := RatFunc.X_ne_zero
  have hA : Y ^ w₁ 0 = Y ^ w₁ 1 * Y ^ n := by rw [hn, zpow_add₀ hY0, zpow_natCast]
  have hB : Y ^ w₂ 0 = Y ^ w₂ 1 * Y ^ m := by rw [hm, zpow_add₀ hY0, zpow_natCast]
  have hu : Y ^ w₁ 1 ≠ 0 := zpow_ne_zero _ hY0
  have hv : Y ^ w₂ 1 ≠ 0 := zpow_ne_zero _ hY0
  have e00 : N 0 0 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e01 : N 0 1 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e10 : N 1 0 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e11 : N 1 1 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0
      = f (c.det * b.det) * (Y ^ w₁ 1) ^ 2 * (Y ^ w₂ 1) ^ 2 * Y ^ (n + m) := by
    rw [e00, e01, e10, e11, hA, hB, det_fin_two, det_fin_two]
    simp only [map_mul, map_sub]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdet]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hu)) (pow_ne_zero _ hv)) (pow_ne_zero _ hY0)
    exact (map_ne_zero f).2 (mul_ne_zero hcd hbd)
  · set q : K[X] := C (c 0 0 * b 0 0) * X ^ (n + m)
      + (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1)) with hq
    set Pol : K[X] := q ^ 2 - C (4 * (c.det * b.det)) * X ^ (n + m) with hPol
    have hkey : (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0)
        = (Y ^ w₁ 1 * Y ^ w₂ 1) ^ 2 * algebraMap K[X] (RatFunc K) Pol := by
      rw [hdet, e00, e11, hA, hB, hPol, hq]
      simp only [map_mul, map_sub, map_add (f := _), map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        map_ofNat, hf, RatFunc.algebraMap_eq_C, hY]
      ring
    have hrest : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
        < n + m := by
      have h1 : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
          ≤ max n m := by
        refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_right _ _)
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_left _ _)
        · rw [natDegree_C]; exact Nat.zero_le _
      omega
    have hqd : q.natDegree = n + m := by
      rw [hq, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ (mul_ne_zero hc hb)]
      exact hrest
    have hPol0 : Pol ≠ 0 := by
      intro h0
      have hsq : q ^ 2 = C (4 * (c.det * b.det)) * X ^ (n + m) := sub_eq_zero.1 (hPol ▸ h0)
      have := congrArg natDegree hsq
      rw [natDegree_pow, hqd] at this
      have hle := natDegree_C_mul_X_pow_le (4 * (c.det * b.det)) (n + m)
      omega
    rw [hkey]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu hv)) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hPol0

theorem UpperTheory.V.AlgebraTools.discSwap :
    ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ), StrictAnti w₁ → StrictAnti w₂ →
      b 0 0 ≠ 0 → c 0 0 ≠ 0 → b.det ≠ 0 → c.det ≠ 0 →
      ((fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
        diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))).charpoly.Separable := by
  intro K _ h2 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  have hblk : (fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
      diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
      = fromBlocks 0 (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
          (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.mul_diagonal]
  have h2' : (2 : RatFunc K) ≠ 0 := by
    rw [show (2 : RatFunc K) = algebraMap K (RatFunc K) 2 from (map_ofNat _ 2).symm]
    exact (_root_.map_ne_zero _).2 h2
  obtain ⟨hd, he⟩ := discSwap_lemma_3 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  rw [hblk, charpoly_fromBlocks_antidiagonal_fin_two]
  exact separable_biquadratic_of_ne_zero_of_discrim_ne_zero _ _ h2' hd he
end

section

open Polynomial Matrix

private lemma torusTransfer_sep_iff {L : Type*} [Field L] (p : L[X]) (hp : p.Monic) (n : ℕ)
    (hn : p.natDegree = n) :
    p.Separable ↔ p.resultant (derivative p) n n ≠ 0 := by
  classical
  set q := p.map (algebraMap L p.SplittingField) with hq
  have hqm : q.Monic := hp.map _
  have hqd : q.natDegree = n := by
    rw [hq, hp.natDegree_map, hn]
  have hspl : q.Splits := SplittingField.splits p
  have hq0 : q ≠ 0 := hqm.ne_zero
  have hdeg : (derivative q).natDegree ≤ n :=
    (natDegree_derivative_le q).trans (by rw [hqd]; exact Nat.sub_le n 1)
  have hres : algebraMap L p.SplittingField (p.resultant (derivative p) n n) =
      (q.roots.map fun x => (derivative q).eval x).prod := by
    rw [← resultant_map_map, ← derivative_map, ← hq]
    have h := resultant_eq_prod_eval q (derivative q) n hdeg hspl
    rw [hqd, hqm.leadingCoeff, one_pow, one_mul] at h
    exact h
  rw [← separable_map (algebraMap L p.SplittingField), ← hq, ← nodup_roots_iff_of_splits hq0 hspl,
    ne_eq, ← map_eq_zero (algebraMap L p.SplittingField), hres, Multiset.prod_eq_zero_iff]
  constructor
  · intro hnd hz
    obtain ⟨α, hα, hα0⟩ := Multiset.mem_map.1 hz
    have hc := (Multiset.nodup_iff_count_le_one.1 hnd) α
    rw [count_roots] at hc
    have hlt : 1 < rootMultiplicity α q :=
      (one_lt_rootMultiplicity_iff_isRoot hq0).2 ⟨(mem_roots hq0).1 hα, hα0⟩
    omega
  · intro hne
    rw [Multiset.nodup_iff_count_le_one]
    intro α
    rw [count_roots]
    by_contra hlt
    push_neg at hlt
    obtain ⟨hr, hr'⟩ := (one_lt_rootMultiplicity_iff_isRoot hq0).1 hlt
    exact hne (Multiset.mem_map.2 ⟨α, (mem_roots hq0).2 hr, hr'⟩)

private lemma torusTransfer_fiber {K : Type*} [Field K] {σ : Type*} [DecidableEq K]
    (S : Finset σ) (c : σ → K) (v : σ → K) (h : ∀ m : ℕ, ∑ s ∈ S, c s * v s ^ m = 0) (j : K) :
    ∑ s ∈ S with v s = j, c s = 0 := by
  classical
  have hP : ∀ P : K[X], ∑ s ∈ S, c s * P.eval (v s) = 0 := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [eval_add, mul_add, Finset.sum_add_distrib, hp, hq, add_zero]
    | monomial n a =>
      simp only [eval_monomial]
      calc ∑ s ∈ S, c s * (a * v s ^ n) = a * ∑ s ∈ S, c s * v s ^ n := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 0 := by rw [h n, mul_zero]
  set P : K[X] := ∏ j' ∈ (S.image v).erase j, (X - C j') with hPdef
  have hev : ∀ s ∈ S, P.eval (v s) = if v s = j then P.eval j else 0 := by
    intro s hs
    split_ifs with hsj
    · rw [hsj]
    · rw [hPdef, eval_prod]
      apply Finset.prod_eq_zero (i := v s)
      · exact Finset.mem_erase.2 ⟨hsj, Finset.mem_image_of_mem v hs⟩
      · simp
  have hPj : P.eval j ≠ 0 := by
    rw [hPdef, eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun j' hj' => by
      rw [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.2 (Finset.ne_of_mem_erase hj').symm
  have h0 := hP P
  have h1 : ∑ s ∈ S, c s * P.eval (v s) = ∑ s ∈ S, if v s = j then c s * P.eval j else 0 :=
    Finset.sum_congr rfl fun s hs => by rw [hev s hs, mul_ite, mul_zero]
  rw [h1, ← Finset.sum_filter, ← Finset.sum_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_right hPj

private lemma torusTransfer_key {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (a : ι → Kˣ) (w : ι → ℤ)
    (hw : ∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0)
    (F : MvPolynomial ι K)
    (h : ∀ m : ℕ, MvPolynomial.eval (fun i => (a i : K) ^ m) F = 0) :
    MvPolynomial.eval₂Hom (algebraMap K (RatFunc K))
      (fun i => (RatFunc.X : RatFunc K) ^ w i) F = 0 := by
  classical
  set T : RatFunc K := RatFunc.X with hTdef
  have hT : T ≠ 0 := RatFunc.X_ne_zero
  have hpow : ∀ μ : ι →₀ ℕ, ∏ i, (T ^ w i) ^ μ i = T ^ (∑ i, (μ i : ℤ) * w i) := by
    intro μ
    have key : ∀ s : Finset ι, ∏ i ∈ s, (T ^ w i) ^ μ i = T ^ (∑ i ∈ s, (μ i : ℤ) * w i) := by
      intro s
      refine Finset.induction_on s (by simp) ?_
      intro i s hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ hT, ih, ← zpow_natCast,
        ← _root_.zpow_mul, mul_comm (w i)]
    exact key _
  have hfib : ∀ j : K, ∑ μ ∈ F.support with (∏ i, (a i : K) ^ μ i) = j, F.coeff μ = 0 := by
    intro j
    apply torusTransfer_fiber F.support (fun μ => F.coeff μ) (fun μ => ∏ i, (a i : K) ^ μ i)
    intro m
    have hm := h m
    rw [MvPolynomial.eval_eq'] at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by ring
  have hterm : ∀ μ : ι →₀ ℕ, algebraMap K (RatFunc K) (F.coeff μ) * ∏ i, (T ^ w i) ^ μ i =
      algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i) := fun μ => by rw [hpow]
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Finset.sum_congr rfl fun μ _ => hterm μ,
    ← Finset.sum_fiberwise_of_maps_to (t := F.support.image fun μ => ∏ i, (a i : K) ^ μ i)
      (g := fun μ => ∏ i, (a i : K) ^ μ i) (fun μ hμ => Finset.mem_image_of_mem _ hμ)
      (fun μ => algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i))]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hne : (F.support.filter fun μ => ∏ i, (a i : K) ^ μ i = j).Nonempty
  · obtain ⟨μ0, hμ0⟩ := hne
    have hsame : ∀ μ ∈ F.support.filter (fun μ => ∏ i, (a i : K) ^ μ i = j),
        algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ i : ℤ) * w i) =
          algebraMap K (RatFunc K) (F.coeff μ) * T ^ (∑ i, (μ0 i : ℤ) * w i) := by
      intro μ hμ
      rw [Finset.mem_filter] at hμ hμ0
      have hv : (∏ i, (a i : K) ^ μ i) = ∏ i, (a i : K) ^ μ0 i := hμ.2.trans hμ0.2.symm
      have hvU : ∏ i, a i ^ μ i = ∏ i, a i ^ μ0 i := by
        apply Units.ext
        push_cast
        exact hv
      have h1 : ∏ i, a i ^ ((μ i : ℤ) - μ0 i) = 1 := by
        simp only [_root_.zpow_sub, zpow_natCast]
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hvU, mul_inv_cancel]
      have h2 := hw _ h1
      simp only [sub_mul, Finset.sum_sub_distrib] at h2
      rw [sub_eq_zero.1 h2]

    rw [Finset.sum_congr rfl hsame, ← Finset.sum_mul, ← map_sum, hfib j, map_zero, zero_mul]
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]

private lemma torusTransfer_spec {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Matrix ι ι K) {L : Type*} [Field L] (f : K →+* L) (t : ι → L) :
    (x.map f * diagonal t).charpoly.Separable ↔
      MvPolynomial.eval₂Hom f t
        ((x.map (MvPolynomial.C : K →+* MvPolynomial ι K) * diagonal MvPolynomial.X).charpoly.resultant
          (derivative (x.map (MvPolynomial.C : K →+* MvPolynomial ι K)
            * diagonal MvPolynomial.X).charpoly) (Fintype.card ι) (Fintype.card ι)) ≠ 0 := by
  have hM : (x.map (MvPolynomial.C : K →+* MvPolynomial ι K) * diagonal MvPolynomial.X).map
      (MvPolynomial.eval₂Hom f t) = x.map f * diagonal t := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [← resultant_map_map, ← derivative_map, ← charpoly_map, hM]
  exact torusTransfer_sep_iff _ (charpoly_monic _) _ (charpoly_natDegree_eq_dim _)

theorem UpperTheory.V.AlgebraTools.torusTransfer :
    ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι K) (a : ι → Kˣ) (w : ι → ℤ),
      (∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0) →
      (x.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w i)).charpoly.Separable →
      ∃ m : ℕ, (x * diagonal (fun i => (a i : K) ^ m)).charpoly.Separable := by
  classical
  intro K _ ι _ _ x a w hw hsep
  have hne := (torusTransfer_spec x (algebraMap K (RatFunc K))
    (fun i => (RatFunc.X : RatFunc K) ^ w i)).1 hsep
  by_contra hall
  push_neg at hall
  apply hne
  apply torusTransfer_key a w hw
  intro m
  have hx : x.map (RingHom.id K) = x := by
    ext i j
    rfl
  have hs := torusTransfer_spec x (RingHom.id K) (fun i => (a i : K) ^ m)
  rw [hx] at hs
  exact not_not.1 (mt hs.2 (hall m))
end
