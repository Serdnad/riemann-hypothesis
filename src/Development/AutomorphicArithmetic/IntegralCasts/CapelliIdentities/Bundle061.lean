module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

section

theorem UpperTheory.infinite_norm_one_elements :
    ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
        {t : E | t * σ t = 1}.Infinite := by
  intro F E _ _ _ _ σ hE hσ
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hw : ¬ NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isComplex_iff.mp (hE.isComplex w)
  generalize w.embedding = τ at hw
  have hinv : ∀ x : E, σ (σ x) = x := fun x =>
    τ.injective (by rw [hσ, hσ, star_star])
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra h
    push Not at h
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [h] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  have h1 : ∀ n : ℕ, (n : E) + a ≠ 0 := by
    intro n hn
    apply ha
    have : a = -(n : E) := by linear_combination hn
    rw [this, map_neg, map_natCast]
  have h2 : ∀ n : ℕ, (n : E) + σ a ≠ 0 := by
    intro n hn
    apply h1 n
    have := congrArg σ hn
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + a) / ((n : E) + σ a)) ?_ ?_
  · intro m n hmn
    have h3 := (div_eq_div_iff (h2 m) (h2 n)).mp hmn
    have h4 : ((m : E) - n) * (σ a - a) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact Nat.cast_injective (R := E) (sub_eq_zero.mp h)
    · exact absurd (sub_eq_zero.mp h) ha
  · intro n
    show _ * σ _ = 1
    rw [map_div₀, map_add (f := _), map_add (f := _), map_natCast, hinv, div_mul_div_cancel₀ (h2 n), div_self (h1 n)]
end

section

open NumberField

private lemma norm_le_prod {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (I : Ideal (RingOfIntegers F)) (y : RingOfIntegers F) (hy : y ∈ I) (h0 : y ≠ 0) :
    (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace F, w (y : F) := by
  have hdvd : Ideal.absNorm I ∣ Ideal.absNorm (Ideal.span {y}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 hy)
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hpos : 0 < (Algebra.norm ℤ y).natAbs := by
    rw [Int.natAbs_pos]
    exact (Algebra.norm_ne_zero_iff).2 h0
  have hle := Nat.le_of_dvd hpos hdvd
  have hprod : ∏ w : InfinitePlace F, w (y : F) = ((|Algebra.norm ℚ (y : F)| : ℚ) : ℝ) := by
    rw [← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(NumberField.IsTotallyReal.isReal w).mult_eq_one, pow_one]
  rw [hprod, ← Algebra.coe_norm_int]
  have : ((Algebra.norm ℤ y).natAbs : ℝ) = |((Algebra.norm ℤ y : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h2 : (Ideal.absNorm I : ℝ) ≤ ((Algebra.norm ℤ y).natAbs : ℝ) := by exact_mod_cast hle
  rw [this] at h2
  push_cast
  exact h2

private lemma sep {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (N : ℕ) (hN : 0 < N) (I : Ideal (RingOfIntegers F)) (x x' : F)
    (hx : ∃ y ∈ I, (y : F) = (N : F) * x) (hx' : ∃ y ∈ I, (y : F) = (N : F) * x') (hne : x ≠ x') :
    (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace F, w ((N : F) * (x - x')) := by
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨y', hy', hyx'⟩ := hx'
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ((y - y' : RingOfIntegers F) : F) = (N : F) * (x - x') := by
    have e : ((y - y' : RingOfIntegers F) : F) = (y : F) - (y' : F) := map_sub _ _ _
    rw [e, hyx, hyx']
    ring
  have h0 : y - y' ≠ 0 := by
    intro h
    rw [h] at hcoe
    have : (N : F) * (x - x') = 0 := by simpa using hcoe.symm
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hN' h1
    · exact hne (sub_eq_zero.1 h1)
  have := norm_le_prod I (y - y') (I.sub_mem hy hy') h0
  rwa [hcoe] at this

private lemma key {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (N : ℕ) (hN : 0 < N) (I : Ideal (RingOfIntegers F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B)
    (S : Set F)
    (hS : S = {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = (N : F) * x) ∧
      ∀ w : InfinitePlace F, (w : F → ℝ) x ≤ B}) :
    S.Finite ∧ (S.ncard : ℝ) * (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases S.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · subst hE
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero, zero_mul]
    positivity
  have hmem : ∀ x, x ∈ S → x ≠ 0 ∧ (∃ y ∈ I, (y : F) = (N : F) * x) ∧
      ∀ w : InfinitePlace F, (w : F → ℝ) x ≤ B := fun x hx => by
    rw [hS] at hx; exact hx
  set n := Module.finrank ℚ F with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hcard : Fintype.card (InfinitePlace F) = n := by
    rw [hn_def, ← InfinitePlace.sum_mult_eq, Finset.card_univ.symm, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun w _ => ((NumberField.IsTotallyReal.isReal w).mult_eq_one).symm
  set C : ℝ := B * N with hC
  have hC0 : 0 ≤ C := by positivity
  set A : ℝ := (Ideal.absNorm I : ℝ) with hA
  have hA0 : 0 < A := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    rw [hA]; exact_mod_cast Nat.pos_of_ne_zero this
  set s : ℝ := A ^ ((n : ℝ)⁻¹) with hs_def
  have hs : s ^ n = A := Real.rpow_inv_natCast_pow hA0.le hn.ne'
  have hs0 : 0 < s := Real.rpow_pos_of_pos hA0 _
  have hN'F : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hwN : ∀ (w : InfinitePlace F) (z : F), w ((N : F) * z) = N * w z := by
    intro w z
    rw [map_mul]
    congr 1
    have := w.norm_embedding_eq (N : F)
    rw [← this]
    simp
  have hAC : A ≤ C ^ n := by
    have h1 := sep N hN I x0 0 (hmem x0 hx0).2.1 ⟨0, I.zero_mem, by simp⟩ (hmem x0 hx0).1
    refine h1.trans ?_
    rw [← hcard, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun w _ => w.1.nonneg _) fun w _ => ?_
    rw [sub_zero, hwN, hC, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hmem x0 hx0).2.2 w) hNr.le
  have hsC : s ≤ C := by
    have : s ^ n ≤ C ^ n := by rw [hs]; exact hAC
    exact (pow_le_pow_iff_left₀ hs0.le hC0 hn.ne').1 this
  let ρ : InfinitePlace F → (F →+* ℝ) := fun w =>
    InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w)
  have hρ : ∀ w z, |ρ w z| = w z := fun w z => by
    simpa [Real.norm_eq_abs] using
      InfinitePlace.norm_embedding_of_isReal (NumberField.IsTotallyReal.isReal w) z
  set K : ℤ := ⌊2 * C / s⌋ with hK
  let f : F → InfinitePlace F → ℤ := fun x w => ⌊((N : ℝ) * ρ w x + C) / s⌋
  let T : Finset (InfinitePlace F → ℤ) := Fintype.piFinset fun _ => Finset.Icc 0 K
  have hmaps : ∀ x ∈ S, f x ∈ (T : Set (InfinitePlace F → ℤ)) := by
    intro x hx
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro w
    have hb : |ρ w x| ≤ B := by rw [hρ]; exact (hmem x hx).2.2 w
    obtain ⟨hb1, hb2⟩ := abs_le.1 hb
    have h1 : -C ≤ (N : ℝ) * ρ w x := by
      have := mul_le_mul_of_nonneg_left hb1 hNr.le
      rw [hC]; linarith
    have h2 : (N : ℝ) * ρ w x ≤ C := by
      have := mul_le_mul_of_nonneg_left hb2 hNr.le
      rw [hC]; linarith
    constructor
    · exact Int.floor_nonneg.2 (div_nonneg (by linarith) hs0.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hs0.le)
  have hinj : Set.InjOn f S := by
    intro x hx x' hx' hff
    by_contra hne
    have h1 := sep N hN I x x' (hmem x hx).2.1 (hmem x' hx').2.1 hne
    have hz : (N : F) * (x - x') ≠ 0 := mul_ne_zero hN'F (sub_ne_zero.2 hne)
    have h2 : ∏ w : InfinitePlace F, w ((N : F) * (x - x')) < ∏ _w : InfinitePlace F, s := by
      refine Finset.prod_lt_prod_of_nonempty₀ (fun w _ => w.pos_iff.2 hz) (fun w _ => ?_)
        Finset.univ_nonempty
      have hw := congrFun hff w
      have h3 := Int.abs_sub_lt_one_of_floor_eq_floor hw
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at h3
      have h4 : w ((N : F) * (x - x')) = |(N : ℝ) * ρ w x + C - ((N : ℝ) * ρ w x' + C)| := by
        rw [hwN, ← hρ w (x - x'), map_sub, ← abs_of_pos hNr, ← abs_mul, abs_of_pos hNr]
        congr 1
        ring
      rw [h4]
      exact h3
    rw [Finset.prod_const, Finset.card_univ, hcard, hs] at h2
    linarith
  have hTfin : (T : Set (InfinitePlace F → ℤ)).Finite := T.finite_toSet
  refine ⟨Set.Finite.of_injOn (f := f) hmaps hinj hTfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn f hmaps hinj hTfin
  have hK0 : 0 ≤ K := Int.floor_nonneg.2 (by positivity)
  have hTc : (T : Set (InfinitePlace F → ℤ)).ncard = (K.toNat + 1) ^ n := by
    rw [Set.ncard_coe_finset]
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, hcard]
    congr 1
    omega
  rw [hTc] at hle
  have hle' : (S.ncard : ℝ) ≤ ((K : ℝ) + 1) ^ n := by
    have : (S.ncard : ℝ) ≤ (((K.toNat + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast hle
    refine this.trans (le_of_eq ?_)
    push_cast
    congr 2
    exact_mod_cast Int.toNat_of_nonneg hK0
  have hKs : ((K : ℝ) + 1) * s ≤ 4 * C := by
    have h1 : (K : ℝ) ≤ 2 * C / s := Int.floor_le _
    have h2 : (K : ℝ) * s ≤ 2 * C := (le_div_iff₀ hs0).1 h1
    nlinarith
  have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ K := by exact_mod_cast hK0
    linarith
  calc (S.ncard : ℝ) * A ≤ ((K : ℝ) + 1) ^ n * s ^ n := by
        rw [hs]; exact mul_le_mul_of_nonneg_right hle' hA0.le
    _ = (((K : ℝ) + 1) * s) ^ n := (mul_pow _ _ _).symm
    _ ≤ (4 * C) ^ n := pow_le_pow_left₀ (by positivity) hKs n
    _ = (4 * B * N) ^ n := by rw [hC]; ring_nf

theorem UpperTheory.Reformulated.B.GaloisBoundSecond.main :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] [NumberField.IsTotallyReal F] (N : ℕ),
      (0 : ℕ) < N →
        ∀ (I : Ideal (NumberField.RingOfIntegers F)),
          I ≠ ⊥ →
            ∀ (B : ℝ),
              (0 : ℝ) ≤ B →
                {x : F |
                      x ≠ (0 : F) ∧
                        (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                          ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.Finite ∧
                  (↑{x : F |
                              x ≠ (0 : F) ∧
                                (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                                  ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.ncard :
                        ℝ) *
                      (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers F) → ℕ) I) : ℝ) ≤
                    ((4 : ℝ) * B * (↑N : ℝ)) ^ Module.finrank ℚ F := by
  intro F _ _ _ N hN I hI B hB
  exact key N hN I hI B hB _ rfl
end

section

open Polynomial

private theorem pow_congr {l : ℕ} [Fact (Nat.Prime l)] {x : PadicAlgCl l} (hx : ‖x‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let F := IntermediateField.adjoin ℚ_[l] {x}
  have hF : FiniteDimensional ℚ_[l] F := IntermediateField.adjoin.finiteDimensional hint
  let V : Submodule ℚ_[l] (PadicAlgCl l) := F.toSubalgebra.toSubmodule
  have hV : FiniteDimensional ℚ_[l] V := hF
  have hP : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
  have hxF : x ∈ F := IntermediateField.mem_adjoin_simple_self ℚ_[l] x
  let u : ℕ → V := fun n => ⟨x ^ n, pow_mem hxF n⟩
  have hu : ∀ n, u n ∈ Metric.closedBall (0 : V) 1 := by
    intro n
    rw [mem_closedBall_zero_iff]
    change ‖x ^ n‖ ≤ 1
    rw [norm_pow, hx, one_pow]
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_closedBall (0 : V) 1).tendsto_subseq hu
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 ha.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (Nat.le_succ N)
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, Nat.sub_pos_of_lt hlt, ?_⟩
  have h2 : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1 := by
    rw [dist_eq_norm] at h1
    exact h1
  have h3 : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (φ (N + 1) - φ N) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
  rwa [h3, norm_mul, norm_pow, hx, one_pow, one_mul] at h2

private theorem descend {l : ℕ} [hl : Fact (Nat.Prime l)] {y : PadicAlgCl l} (hy : ‖y‖ = 1)
    (h : ‖y ^ l - 1‖ < 1) : ‖y - 1‖ < 1 := by
  have hp : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  set z := y - 1 with hz
  have hz1 : ‖z‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max y (-1)
    rw [norm_neg, norm_one, hy, max_self, ← sub_eq_add_neg] at this
    exact this
  have hyz : y = z + 1 := by rw [hz]; ring
  have e := add_pow_prime_eq' hl.out z 1
  set S := ∑ k ∈ Finset.Ioo 0 l, z ^ k * 1 ^ (l - k) * ((l.choose k / l : ℕ) : PadicAlgCl l)
    with hS
  have hS1 : ‖S‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : z ^ l = (y ^ l - 1) + -((l : PadicAlgCl l) * S) := by
    rw [hyz, e]; ring
  have h4 : ‖z ^ l‖ < 1 := by
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h ?_)
    rw [norm_neg, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hp hS1
  rw [norm_pow] at h4
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h4

private theorem coprime_pow_congr {l : ℕ} [hl : Fact (Nat.Prime l)] {x : PadicAlgCl l}
    (hx : ‖x‖ = 1) : ∃ m : ℕ, ¬l ∣ m ∧ ‖x ^ m - 1‖ < 1 := by
  obtain ⟨n, hn, h⟩ := pow_congr hx
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  refine ⟨m, hm, ?_⟩
  clear hn
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply descend (by rw [norm_pow, hx, one_pow])
    rwa [← pow_mul, mul_right_comm, ← pow_succ]

theorem UpperTheory.Reformulated.B.ExistsRootCongruence.exists_root_congr :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x : PadicAlgCl l},
    ‖x‖ = (1 : ℝ) → ∃ (m : ℕ) (ζ : PadicAlgCl l), ¬l ∣ m ∧ ζ ^ m = (1 : PadicAlgCl l) ∧ ‖x - ζ‖ < (1 : ℝ) := by
  intro l _ x hx
  obtain ⟨m, hm, h⟩ := coprime_pow_congr hx
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  haveI : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm0 hμ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  by_contra hcon
  push Not at hcon
  rw [e, norm_prod] at h
  refine absurd h (not_lt.2 ?_)
  refine Finset.prod_induction _ (fun r : ℝ => 1 ≤ r)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_
  intro ζ hζ
  exact hcon m ζ hm ((mem_nthRootsFinset hm0 1).1 hζ)
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh58.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qh58.norm_det_le :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (ι : UpperTheory.Reformulated.B.Qh58.Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
      (R : ℝ),
      (1 : ℝ) ≤ R →
        (∀ (i j : Fin n), ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh58.Qbar l) (M i j)‖ ≤ R) →
          ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh58.Qbar l) M.det‖ ≤ R ^ n := by
  intro l _ ι n M R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR

  rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_
  intro σ _
  rw [map_mul, map_prod, norm_mul, norm_prod, map_intCast]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : PadicAlgCl l)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  rw [h1, one_mul]
  calc ∏ i, ‖ι.symm (M (σ i) i)‖ ≤ ∏ _i : Fin n, R :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)
    _ = R ^ n := by simp
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh59.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qh59.norm_det_le :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (ι : UpperTheory.Reformulated.B.Qh59.Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
      (R : ℝ),
      (1 : ℝ) ≤ R →
        (∀ (i j : Fin n), ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) (M i j)‖ ≤ R) →
          ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) M.det‖ ≤ R ^ n := by
  intro l inst ι n M R hR h
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR

  rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_
  intro σ _
  rw [map_mul, map_prod, norm_mul, norm_prod, map_intCast]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : UpperTheory.Reformulated.B.Qh59.Qbar l)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  have h2 : ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ R ^ n := by
    calc ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ ∏ _i : Fin n, R :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)
      _ = R ^ n := by simp
  calc _ ≤ 1 * R ^ n :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
    _ = R ^ n := one_mul _
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk14.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qk14.norm_eq_one :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x : UpperTheory.Reformulated.B.Qk14.Qbar l},
      ‖x - (1 : UpperTheory.Reformulated.B.Qk14.Qbar l)‖ < (1 : ℝ) → ‖x‖ = (1 : ℝ) := by
  intro l _ x h
  have hne : ‖x - 1‖ ≠ ‖(1 : UpperTheory.Reformulated.B.Qk14.Qbar l)‖ := by
    rw [norm_one]
    exact h.ne
  have key := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [sub_add_cancel, norm_one] at key
  rw [key]
  exact max_eq_right h.le
end

section

noncomputable def UpperTheory.Reformulated.B.Qi27.muPrime :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Set ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ {ζ : ℂ_[l] | ∃ (n : ℕ), (0 : ℕ) < n ∧ ¬l ∣ n ∧ ζ ^ n = (1 : ℂ_[l])}

noncomputable def UpperTheory.Reformulated.B.Qi27.ringA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Subring ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Subring.closure (UpperTheory.Reformulated.B.Qi27.muPrime l)

theorem UpperTheory.Reformulated.B.Qi27.norm_ringA_le :
    ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {x : ℂ_[l]}, x ∈ UpperTheory.Reformulated.B.Qi27.ringA l → ‖x‖ ≤ (1 : ℝ) := by
  intro l hl x hx
  unfold UpperTheory.Reformulated.B.Qi27.ringA at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨n, hn, -, h⟩ := hy
    have h1 : ‖y‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').1 h1).le
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  | neg a _ ha => simpa using ha
  | mul a b _ _ ha hb =>
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
end
