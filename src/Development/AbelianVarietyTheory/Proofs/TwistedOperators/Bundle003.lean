module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

section

open Finset Polynomial

namespace GlobalTheory

lemma shiftDiffPoly_coeff_comp (f : ℂ[X]) (n : ℕ) :
    (f.comp (X + 1)).coeff n = ∑ i ∈ range (f.natDegree + 1), f.coeff i * (i.choose n : ℂ) := by
  rw [comp, eval₂_eq_sum_range]
  simp [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_add_one_pow]

lemma shiftDiffPoly_coeff_top (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) :
    (f.comp (X + 1) - f).coeff n = 0 := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have : b < n := by simp at hb; omega
    simp [Nat.choose_eq_zero_of_lt this]
  · intro hn'
    have : f.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by simp at hn'; omega)
    simp [this]

lemma shiftDiffPoly_coeff_sub (f : ℂ[X]) (e : ℕ) (he : f.natDegree = e + 1) :
    (f.comp (X + 1) - f).coeff e = ((e : ℂ) + 1) * f.coeff (e + 1) := by
  rw [coeff_sub, shiftDiffPoly_coeff_comp, he, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero]
  · simp [Nat.choose_succ_self_right]; ring
  · intro i hi
    simp at hi
    simp [Nat.choose_eq_zero_of_lt hi]

theorem newton_recursion_poly_unique : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by
  intro m N p f r hmN hp0 hf hr hid
  have hlead : ∀ k : ℕ, ((X - C (m:ℂ)) ^ k).coeff k = 1 := fun k => by
    have h := ((monic_X_sub_C (m:ℂ)).pow k).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at h
  set Pi : ℂ[X] := ∑ k ∈ range (N + 1), C ((-1) ^ k * p k) * (X - C (m:ℂ)) ^ (N - k) with hPi
  set g : ℂ[X] := f.comp (X + 1) - f with hg
  have hpoly : (X - C (m:ℂ)) ^ (N + 1) * g - f * Pi = r := by
    apply Polynomial.funext
    intro u
    simp only [hg, hPi, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_add,
      eval_one, Polynomial.eval_finsetSum]
    rw [← hid u]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hPiN : Pi.coeff N = (m : ℂ) + 1 := by
    rw [hPi, Polynomial.finsetSum_coeff, Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp only [pow_zero, one_mul, Nat.sub_zero, coeff_C_mul, hlead, hp0, mul_one, zero_add]
    · intro k hk
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [natDegree_pow, natDegree_X_sub_C]
      simp at hk
      omega
  have hPideg : Pi.natDegree ≤ N := by
    rw [hPi]
    apply natDegree_sum_le_of_forall_le
    intro k _
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow, natDegree_X_sub_C]
    omega
  set d := f.natDegree with hd
  have hcoef : ((X - C (m:ℂ)) ^ (N + 1) * g - f * Pi).coeff (d + N) = r.coeff (d + N) := by rw [hpoly]
  rw [coeff_sub] at hcoef
  have hr0 : r.coeff (d + N) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h2 : (f * Pi).coeff (d + N) = f.coeff d * Pi.coeff N :=
    coeff_mul_add_eq_of_natDegree_le le_rfl hPideg
  have h1 : ((X - C (m:ℂ)) ^ (N + 1) * g).coeff (d + N) = d * f.coeff d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have hg0 : g = 0 := by
        ext n
        rw [coeff_zero]
        exact shiftDiffPoly_coeff_top f n (by omega)
      rw [hg0, mul_zero, coeff_zero, h0]
      simp
    · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hgdeg : g.natDegree ≤ e := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn
        exact shiftDiffPoly_coeff_top f n (by omega)
      have hidx : d + N = (N + 1) + e := by omega
      rw [hidx, coeff_mul_add_eq_of_natDegree_le (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]) hgdeg,
        hlead, one_mul, shiftDiffPoly_coeff_sub f e he, he]
      push_cast
      ring
  rw [h1, h2, hPiN, hr0] at hcoef
  have hne : (d : ℂ) - ((m : ℂ) + 1) ≠ 0 := by
    intro h
    have h' : (d : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; linear_combination h
    have := Nat.cast_injective h'
    omega
  have hc : f.coeff d = 0 := by
    have : f.coeff d * ((d : ℂ) - ((m : ℂ) + 1)) = 0 := by linear_combination hcoef
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hne
  exact leadingCoeff_eq_zero.mp hc

end GlobalTheory
end

section

namespace GlobalTheory.FactorThroughProjection

theorem exists_factor_through_projection {J : Type} [Fintype J] [DecidableEq J] (A : J → Type)
    [inst : (i : J) → CommRing (A i)] {k : Type} [inst_1 : CommRing k] [IsDomain k]
    (χ : ((i : J) → A i) →+* k) :
    ∃ (i : J) (ψ : A i →+* k), ∀ (x : (i : J) → A i), χ x = ψ (x i) := by
  have hsum : ∑ i : J, χ (Pi.single i (1 : A i)) = 1 := by

    rw [← map_sum]
    have h : ∑ i : J, (Pi.single i (1 : A i) : (j : J) → A j) = 1 :=
      Finset.univ_sum_single (1 : (j : J) → A j)
    rw [h, map_one]
  have hne : ∑ i : J, χ (Pi.single i (1 : A i)) ≠ 0 := by
    rw [hsum]; exact one_ne_zero
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hmul : ∀ a b : A i, (Pi.single i (a * b) : (j : J) → A j)
      = Pi.single i a * Pi.single i b := by
    intro a b
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have hone : χ (Pi.single i (1 : A i)) = 1 := by
    apply mul_left_cancel₀ hi
    rw [← map_mul, ← hmul, mul_one, mul_one]
  let ψ : A i →+* k :=
    { toFun := fun a => χ (Pi.single i a)
      map_one' := hone
      map_mul' := fun a b => by rw [hmul, map_mul]
      map_zero' := by simp
      map_add' := fun a b => by rw [Pi.single_add, map_add (f := _)] }
  refine ⟨i, ψ, fun x => ?_⟩
  change χ x = χ (Pi.single i (x i))
  have hx : (Pi.single i (x i) : (j : J) → A j) = x * Pi.single i (1 : A i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [hx, map_mul, hone, mul_one]

end GlobalTheory.FactorThroughProjection
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_word_le_number_pow : ∀ (T H κ : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype κ] (Φ : T →ₗ[ℂ] H) (a c : κ → Module.End ℂ T) (M : Module.End ℂ T) (r r' : ℝ), 1 ≤ r → r' ≤ r → (∀ j x y, inner ℂ (Φ (c j x)) (Φ y) = inner ℂ (Φ x) (Φ (a j y))) → (∀ j, a j * c j - c j * a j = (r' : ℂ) • 1) → M = ∑ j, c j * a j + (r : ℂ) • 1 → (∀ j, M * a j = a j * (M - (r : ℂ) • 1)) → (∀ j, M * c j = c j * (M + (r : ℂ) • 1)) → ∀ (l : List (Module.End ℂ T)) (d : ℕ), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) → l.length ≤ d → ∃ C : ℝ, ∀ x, ‖Φ (l.prod x)‖ ≤ C * ‖Φ ((M ^ d) x)‖ := by
  intro T H κ _ _ _ _ _ Φ a c M r r' hr hr' hadj hcomm hM hMa hMc l d hl hld

  have hreal : ∀ (s : ℝ) (x : T), RCLike.re (inner ℂ (Φ x) (Φ ((s : ℂ) • x))) = s * ‖Φ x‖ ^ 2 := by
    intro s x
    rw [map_smul, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
    left; rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hca : ∀ j x, RCLike.re (inner ℂ (Φ x) (Φ (c j (a j x)))) = ‖Φ (a j x)‖ ^ 2 := by
    intro j x
    rw [← inner_conj_symm, hadj, RCLike.conj_re, inner_self_eq_norm_sq]
  have hMx : ∀ x, M x = ∑ j, c j (a j x) + (r : ℂ) • x := by
    intro x; subst hM; simp [Module.End.mul_apply]
  have hQeq : ∀ x, RCLike.re (inner ℂ (Φ x) (Φ (M x))) = ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 := by
    intro x

    rw [hMx, map_add (f := _), inner_add_right, map_add (f := _), ← hreal, map_sum, inner_sum, map_sum]
    simp only [hca]
  have hQ : ∀ x, ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 ≤ ‖Φ x‖ * ‖Φ (M x)‖ := by
    intro x; rw [← hQeq]; exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hsum : ∀ x, 0 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2 := fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hrx : ∀ x, r * ‖Φ x‖ ≤ ‖Φ (M x)‖ := by
    intro x
    rcases (norm_nonneg (Φ x)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · refine le_of_mul_le_mul_left ?_ hpos
      nlinarith [hQ x, hsum x]
  have hx : ∀ x, ‖Φ x‖ ≤ ‖Φ (M x)‖ := by
    intro x; nlinarith [hrx x, norm_nonneg (Φ x)]
  have hsq : ∀ x u, 0 ≤ u → u ^ 2 ≤ ∑ j, ‖Φ (a j x)‖ ^ 2 + r * ‖Φ x‖ ^ 2 → u ≤ ‖Φ (M x)‖ := by
    intro x u hu h
    have h1 := hQ x
    have h2 := mul_le_mul_of_nonneg_right (hx x) (norm_nonneg (Φ (M x)))
    have h3 : u ^ 2 ≤ ‖Φ (M x)‖ ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hu (norm_nonneg _) two_ne_zero).1 h3
  have ha : ∀ j x, ‖Φ (a j x)‖ ≤ ‖Φ (M x)‖ := by
    intro j x
    refine hsq x _ (norm_nonneg _) ?_
    have := Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have : 0 ≤ r * ‖Φ x‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hac : ∀ j, a j * c j = c j * a j + (r' : ℂ) • 1 := fun j => sub_eq_iff_eq_add'.1 (hcomm j)
  have hc : ∀ j x, ‖Φ (c j x)‖ ≤ ‖Φ (M x)‖ := by
    intro j x
    refine hsq x _ (norm_nonneg _) ?_
    have e : ‖Φ (c j x)‖ ^ 2 = ‖Φ (a j x)‖ ^ 2 + r' * ‖Φ x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hadj, ← Module.End.mul_apply, hac, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, map_add, inner_add_right, map_add, hca, hreal]
    have := Finset.single_le_sum (f := fun i => ‖Φ (a i x)‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have : r' * ‖Φ x‖ ^ 2 ≤ r * ‖Φ x‖ ^ 2 := mul_le_mul_of_nonneg_right hr' (sq_nonneg _)
    linarith
  have hC : ∀ s : ℝ, Commute M (M + (s : ℂ) • 1) := fun s =>
    (Commute.refl M).add_right ((Commute.one_right M).smul_right _)
  have hshift : ∀ (s : ℝ), |s| ≤ r → ∀ y, ‖Φ ((M + (s : ℂ) • 1) y)‖ ≤ 2 * ‖Φ (M y)‖ := by
    intro s hs y
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
    calc ‖Φ (M y) + (s : ℂ) • Φ y‖ ≤ ‖Φ (M y)‖ + ‖(s : ℂ) • Φ y‖ := norm_add_le _ _
      _ = ‖Φ (M y)‖ + |s| * ‖Φ y‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖Φ (M y)‖ + r * ‖Φ y‖ := by gcongr
      _ ≤ 2 * ‖Φ (M y)‖ := by linarith [hrx y]
  have hpow : ∀ (s : ℝ), |s| ≤ r → ∀ k y, ‖Φ (((M + (s : ℂ) • 1) ^ k) y)‖ ≤ 2 ^ k * ‖Φ ((M ^ k) y)‖ := by
    intro s hs k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      have e := LinearMap.congr_fun ((hC s).pow_left k).eq y
      rw [Module.End.mul_apply, Module.End.mul_apply] at e
      rw [pow_succ (M + (s : ℂ) • 1) k, Module.End.mul_apply, pow_succ' M k, Module.End.mul_apply]
      calc ‖Φ (((M + (s : ℂ) • 1) ^ k) ((M + (s : ℂ) • 1) y))‖
          ≤ 2 ^ k * ‖Φ ((M ^ k) ((M + (s : ℂ) • 1) y))‖ := ih _
        _ = 2 ^ k * ‖Φ ((M + (s : ℂ) • 1) ((M ^ k) y))‖ := by rw [e]
        _ ≤ 2 ^ k * (2 * ‖Φ (M ((M ^ k) y))‖) := by gcongr; exact hshift s hs _
        _ = 2 ^ (k + 1) * ‖Φ (M ((M ^ k) y))‖ := by ring
  have hcommx : ∀ (s : ℝ) (k : ℕ) x, M (((M + (s : ℂ) • 1) ^ k) x) = ((M + (s : ℂ) • 1) ^ k) (M x) := by
    intro s k x
    have e := LinearMap.congr_fun ((hC s).pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e
  have hMka : ∀ j (k : ℕ) x, (M ^ k) (a j x) = a j (((M + ((-r : ℝ) : ℂ) • 1) ^ k) x) := by
    intro j k x
    have hs : SemiconjBy (a j) (M + ((-r : ℝ) : ℂ) • 1) M := by
      unfold SemiconjBy; rw [hMa j]; push_cast; rw [neg_smul, ← sub_eq_add_neg]
    have e := LinearMap.congr_fun (hs.pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e.symm
  have hMkc : ∀ j (k : ℕ) x, (M ^ k) (c j x) = c j (((M + (r : ℂ) • 1) ^ k) x) := by
    intro j k x
    have hs : SemiconjBy (c j) (M + (r : ℂ) • 1) M := by
      unfold SemiconjBy; rw [hMc j]
    have e := LinearMap.congr_fun (hs.pow_right k).eq x
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    exact e.symm
  have hra : |(-r)| ≤ r := by rw [abs_neg, abs_of_nonneg (by linarith)]
  have hrc : |r| ≤ r := by rw [abs_of_nonneg (by linarith)]
  have hPa : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (a j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro j k; refine ⟨2 ^ k, fun x => ?_⟩
    rw [hMka]
    calc _ ≤ ‖Φ (M (((M + ((-r : ℝ) : ℂ) • 1) ^ k) x))‖ := ha j _
      _ = ‖Φ (((M + ((-r : ℝ) : ℂ) • 1) ^ k) (M x))‖ := by rw [hcommx]
      _ ≤ 2 ^ k * ‖Φ ((M ^ k) (M x))‖ := hpow _ hra k _
      _ = 2 ^ k * ‖Φ ((M ^ (k + 1)) x)‖ := by rw [pow_succ M k, Module.End.mul_apply]
  have hPc : ∀ j (k : ℕ), ∃ C : ℝ, ∀ x, ‖Φ ((M ^ k) (c j x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro j k; refine ⟨2 ^ k, fun x => ?_⟩
    rw [hMkc]
    calc _ ≤ ‖Φ (M (((M + (r : ℂ) • 1) ^ k) x))‖ := hc j _
      _ = ‖Φ (((M + (r : ℂ) • 1) ^ k) (M x))‖ := by rw [hcommx]
      _ ≤ 2 ^ k * ‖Φ ((M ^ k) (M x))‖ := hpow _ hrc k _
      _ = 2 ^ k * ‖Φ ((M ^ (k + 1)) x)‖ := by rw [pow_succ M k, Module.End.mul_apply]
  have hP : ∀ X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c), ∀ k : ℕ, ∃ C : ℝ,
      ∀ x, ‖Φ ((M ^ k) (X x))‖ ≤ C * ‖Φ ((M ^ (k + 1)) x)‖ := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X h =>
      rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact hPa j
      · exact hPc j
    | zero => intro k; exact ⟨0, fun x => by simp⟩
    | add X Y _ _ hX hY =>
      intro k
      obtain ⟨C1, h1⟩ := hX k
      obtain ⟨C2, h2⟩ := hY k
      refine ⟨C1 + C2, fun x => ?_⟩
      rw [LinearMap.add_apply, map_add (f := _), map_add (f := _)]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ C1 * _ + C2 * _ := add_le_add (h1 x) (h2 x)
        _ = _ := by ring
    | smul s X _ hX =>
      intro k
      obtain ⟨C1, h1⟩ := hX k
      refine ⟨‖s‖ * C1, fun x => ?_⟩
      rw [LinearMap.smul_apply, map_smul, map_smul, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 x) (norm_nonneg _)
  have hlist : ∀ l : List (Module.End ℂ T), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) →
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Φ ((M ^ k) (l.prod x))‖ ≤ C * ‖Φ ((M ^ (k + l.length)) x)‖ := by
    intro l
    induction l with
    | nil => intro _ k; exact ⟨1, zero_le_one, fun x => by simp⟩
    | cons X l ih =>
      intro hXl k
      obtain ⟨C1, h1⟩ := hP X (hXl X (by simp)) k
      obtain ⟨C2, hC2, h2⟩ := ih (fun Y hY => hXl Y (List.mem_cons_of_mem _ hY)) (k + 1)
      refine ⟨max C1 0 * C2, mul_nonneg (le_max_right _ _) hC2, fun x => ?_⟩
      rw [List.prod_cons, Module.End.mul_apply, List.length_cons]
      calc _ ≤ C1 * ‖Φ ((M ^ (k + 1)) (l.prod x))‖ := h1 _
        _ ≤ max C1 0 * ‖Φ ((M ^ (k + 1)) (l.prod x))‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C1 0 * (C2 * ‖Φ ((M ^ (k + 1 + l.length)) x)‖) :=
            mul_le_mul_of_nonneg_left (h2 x) (le_max_right _ _)
        _ = max C1 0 * C2 * ‖Φ ((M ^ (k + (l.length + 1))) x)‖ := by
            rw [mul_assoc, show k + (l.length + 1) = k + 1 + l.length by omega]
  have hmono : ∀ x n i, ‖Φ ((M ^ n) x)‖ ≤ ‖Φ ((M ^ (n + i)) x)‖ := by
    intro x n i
    induction i with
    | zero => simp
    | succ i ih => rw [← add_assoc, pow_succ', Module.End.mul_apply]; exact ih.trans (hx _)
  obtain ⟨C, hC0, h⟩ := hlist l hl 0
  refine ⟨C, fun x => ?_⟩
  have h' := h x
  rw [pow_zero, Module.End.one_apply, zero_add] at h'
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hld
  exact h'.trans (mul_le_mul_of_nonneg_left (hmono x _ i) hC0)

end GlobalTheory
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_clm_of_gram_eq_smul {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E)
    (K : ℝ) (hK : ∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs)) :
    ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  classical
  let Φ : (α →₀ ℂ) →ₗ[ℂ] Hs := Finsupp.linearCombination ℂ u
  let Ψ : (α →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ f
  have hinner : ∀ z w : α →₀ ℂ, ⟪Ψ z, Ψ w⟫_ℂ = (K : ℂ) * ⟪Φ z, Φ w⟫_ℂ := by
    intro z w
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), inner_add_left, h₁, h₂]; ring
    | single a c =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w₁ w₂ h₁ h₂ => simp only [map_add (f := _), inner_add_right, h₁, h₂]; ring
      | single b d =>
        simp only [Φ, Ψ, Finsupp.linearCombination_single, inner_smul_left, inner_smul_right, hK]
        ring
  have hnorm : ∀ z, ‖Ψ z‖ ^ 2 = K * ‖Φ z‖ ^ 2 := by
    intro z
    have h := hinner z z
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    simpa using h
  have hbound : ∀ z, ‖Ψ z‖ ≤ Real.sqrt (max K 0) * ‖Φ z‖ := by
    intro z
    have hs : Real.sqrt (max K 0) ^ 2 = max K 0 := Real.sq_sqrt (le_max_right _ _)
    have h0 : 0 ≤ Real.sqrt (max K 0) := Real.sqrt_nonneg _
    have h1 : ‖Ψ z‖ ^ 2 ≤ (Real.sqrt (max K 0) * ‖Φ z‖) ^ 2 := by
      rw [mul_pow, hs, hnorm]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 h1
  have hdense : DenseRange Φ := by
    have hr : Set.range Φ = (Submodule.span ℂ (Set.range u) : Set Hs) := by
      rw [← LinearMap.coe_range]
      exact congrArg _ (Finsupp.range_linearCombination ℂ)
    rw [DenseRange, hr]
    exact hd
  refine ⟨Ψ.extendOfNorm Φ, fun a => ?_⟩
  have h := LinearMap.extendOfNorm_eq hdense ⟨_, hbound⟩ (Finsupp.single a 1)
  simpa [Φ, Ψ, Finsupp.linearCombination_single] using h
end GlobalTheory
end
