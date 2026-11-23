module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem exp_neg_two_mul_le_one_sub {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    Real.exp (-(2 * s)) ≤ 1 - s := by
  have hpos : 0 < 1 + 2 * s := by linarith
  have h2 : 1 + 2 * s ≤ Real.exp (2 * s) := by linarith [Real.add_one_le_exp (2 * s)]
  rw [Real.exp_neg]
  have h3 : (Real.exp (2 * s))⁻¹ ≤ (1 + 2 * s)⁻¹ := inv_anti₀ hpos h2
  have h4 : (1 + 2 * s)⁻¹ ≤ 1 - s := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

theorem prod_one_sub_bounded_below :
    ∀ (ι : Type) (s : ι → ℝ), (∀ v, 0 ≤ s v) → (∀ v, s v < 1) → Summable s →
      ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏ v ∈ S, (1 - s v) := by
  intro ι s h0 h1 hs
  classical
  have hev : ∀ᶠ v in cofinite, s v < 1 / 2 :=
    hs.tendsto_cofinite_zero.eventually (eventually_lt_nhds (by norm_num))
  have hfin : {v | ¬ s v < 1 / 2}.Finite := Filter.eventually_cofinite.mp hev
  set F : Finset ι := hfin.toFinset with hFdef
  have hout : ∀ v, v ∉ F → s v ≤ 1 / 2 := by
    intro v hv
    by_contra hcon
    exact hv (by
      rw [hFdef, Set.Finite.mem_toFinset]
      intro hlt
      exact hcon hlt.le)
  have hfac : ∀ v, 0 < 1 - s v := fun v => by linarith [h1 v]
  have hle1 : ∀ v, 1 - s v ≤ 1 := fun v => by linarith [h0 v]
  have hc : 0 < ∏ v ∈ F, (1 - s v) := Finset.prod_pos fun v _ => hfac v
  refine ⟨(∏ v ∈ F, (1 - s v)) * Real.exp (-(2 * ∑' v, s v)), mul_pos hc (Real.exp_pos _),
    fun S => ?_⟩
  have hsplit : ∏ v ∈ S, (1 - s v) =
      (∏ v ∈ S.filter (· ∈ F), (1 - s v)) * ∏ v ∈ S.filter (· ∉ F), (1 - s v) :=
    (Finset.prod_filter_mul_prod_filter_not S (· ∈ F) _).symm
  have hsub : S.filter (· ∈ F) ⊆ F := fun v hv => (Finset.mem_filter.mp hv).2
  have hA : ∏ v ∈ F, (1 - s v) ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v) := by
    rw [← Finset.prod_sdiff hsub]
    have hp : 0 ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v) :=
      Finset.prod_nonneg fun v _ => (hfac v).le
    have hq : ∏ v ∈ F \ S.filter (· ∈ F), (1 - s v) ≤ 1 :=
      Finset.prod_le_one₀ (fun v _ => (hfac v).le) (fun v _ => hle1 v)
    exact mul_le_of_le_one_left hp hq
  have hB : Real.exp (-(2 * ∑' v, s v)) ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v) := by
    have hsum : ∑ v ∈ S.filter (· ∉ F), s v ≤ ∑' v, s v :=
      hs.sum_le_tsum _ (fun v _ => h0 v)
    calc Real.exp (-(2 * ∑' v, s v))
        ≤ Real.exp (∑ v ∈ S.filter (· ∉ F), -(2 * s v)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ v ∈ S.filter (· ∉ F), Real.exp (-(2 * s v)) := Real.exp_sum _ _
      _ ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v) :=
          Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le)
            (fun v hv => exp_neg_two_mul_le_one_sub (h0 v)
              (hout v (Finset.mem_filter.mp hv).2))
  rw [hsplit]
  exact mul_le_mul hA hB (Real.exp_pos _).le
    (Finset.prod_nonneg fun v _ => (hfac v).le)

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem conj_sub_mul_neg_mul_of_norm_one {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (starRingEnd ℂ) (x - y) * (-(x * y)) = x - y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have cx : (starRingEnd ℂ) x = x⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hx]; simp
  have cy : (starRingEnd ℂ) y = y⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hy]; simp
  rw [map_sub, cx, cy]
  field_simp
  ring

theorem resultant_phase_unit_circle :
    ∀ (a b : ℕ) (α : Fin a → ℂ) (β : Fin b → ℂ), (∀ i, ‖α i‖ = 1) → (∀ j, ‖β j‖ = 1) →
      (∀ i j, α i ≠ β j) → ∀ k : ℤ,
        let R : ℂ := ∏ i, ∏ j, (α i - β j)
        (R / (‖R‖ : ℂ)) ^ (2 * k - 1) * (‖R‖ : ℂ) =
          (starRingEnd ℂ) R * ((-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ k := by
  intro a b α β hα hβ hne k R
  set D : ℂ := (-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a with hD
  have hR : R ≠ 0 := by
    simp only [R]
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro j _
    exact sub_ne_zero.mpr (hne i j)
  have hDprod : D = ∏ i, ∏ j, (-(α i * β j)) := by
    simp only [hD, Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.prod_pow, pow_mul]
    ring
  have hconj : (starRingEnd ℂ) R * D = R := by
    rw [hDprod]
    simp only [R, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact conj_sub_mul_neg_mul_of_norm_one (hα i) (hβ j)
  have hcR : (starRingEnd ℂ) R ≠ 0 := by simpa using hR
  have hr : ((‖R‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hR
  have hsq : ((‖R‖ : ℝ) : ℂ) ^ 2 = R * (starRingEnd ℂ) R := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  set u : ℂ := R / ((‖R‖ : ℝ) : ℂ) with hu
  have hu0 : u ≠ 0 := div_ne_zero hR hr
  have hu2 : u ^ 2 = D := by
    rw [hu, div_pow, hsq, pow_two, mul_div_mul_left _ _ hR, eq_comm]
    exact eq_div_of_mul_eq hcR (by rw [mul_comm]; exact hconj)
  have : u ^ (2 * k - 1) = D ^ k * u⁻¹ := by
    rw [zpow_sub₀ hu0, zpow_mul, zpow_one, zpow_two, ← pow_two, hu2, div_eq_mul_inv]
  rw [this, hu]
  field_simp
  linear_combination (D ^ k) * hsq

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem ultra_matrix_mul_entry_le {E : Type} [NormedField E] [IsUltrametricDist E] {n : Type} [Fintype n]
    [DecidableEq n] (A B : Matrix n n E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) ?_
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

theorem matrix_one_add_pow_sub_entry_le :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) →
      ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  intro E _ _ n _ _ Y t ht0 ht1 hY m
  induction m with
  | zero => intro i j; simp; positivity
  | succ m ih =>
    have key : (1 + Y) ^ (m + 1) - 1 - ((m + 1 : ℕ) : E) • Y
        = ((1 + Y) ^ m - 1 - (m : E) • Y) + ((1 + Y) ^ m - 1 - (m : E) • Y) * Y
          + (m : E) • (Y * Y) := by
      rw [pow_succ]
      push_cast
      simp only [mul_add, add_mul, mul_one, one_mul, sub_mul, smul_mul_assoc, add_smul, one_smul]
      abel
    intro i j
    rw [key]
    have h1 := ih i j
    have h2 : ‖(((1 + Y) ^ m - 1 - (m : E) • Y) * Y) i j‖ ≤ t ^ 2 := by
      have := ultra_matrix_mul_entry_le _ Y (t ^ 2) t (by positivity) ht0 ih hY i j
      calc _ ≤ t ^ 2 * t := this
        _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
        _ = t ^ 2 := mul_one _
    have h3 : ‖((m : E) • (Y * Y)) i j‖ ≤ t ^ 2 := by
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
      have := ultra_matrix_mul_entry_le Y Y t t ht0 ht0 hY hY i j
      calc ‖(m : E)‖ * ‖(Y * Y) i j‖ ≤ 1 * (t * t) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one E m) this (norm_nonneg _) zero_le_one
        _ = t ^ 2 := by ring
    rw [Matrix.add_apply, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)

end GlobalTheory
end

section

namespace GlobalTheory.PMonE


open Finset in
theorem _root_.GlobalTheory.PMonE.exists_window_radii : ∀ (F : Type) [NontriviallyNormedField F]
    [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin (k + 1) → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ π : Fin (k + 1) → F, (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) ∧
      (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) =
        ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) ∧
      (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p := by
  intro F _ _ _ p _ _ _ k ϖ hϖ lam hlam hanti hclose
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hl : ∀ j, 0 < ‖lam j‖ := fun j => norm_pos_iff.mpr (hlam j)
  have hρ : ∀ j : Fin k, ∃ y : F, y ^ p ^ (j : ℕ) = lam j.castSucc / lam j.succ :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ (pow_pos (by omega) _)
  choose ρ hρ using hρ
  have hρn : ∀ j : Fin k, ‖ρ j‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ / ‖lam j.succ‖ := fun j => by
    rw [← norm_pow, hρ, norm_div]
  have hρ1 : ∀ j : Fin k, 1 ≤ ‖ρ j‖ := fun j => by
    rw [← one_le_pow_iff_of_nonneg (norm_nonneg _) (pow_pos (by omega : 0 < p) (j : ℕ)).ne', hρn,
      one_le_div (hl _)]
    exact hanti (Fin.castSucc_le_succ j)
  set ρ' : ℕ → F := fun n => if h : n < k then ρ ⟨n, h⟩ else 1 with hρ'
  have hρ'1 : ∀ n, 1 ≤ ‖ρ' n‖ := fun n => by
    simp only [hρ']; split_ifs with h
    · exact hρ1 _
    · simp
  have hρ'ne : ∀ n, ρ' n ≠ 0 := fun n h0 => by
    have := hρ'1 n; rw [h0, norm_zero] at this; linarith
  set P : ℕ → F := fun j => ∏ n ∈ range j, ρ' n with hP
  have hPne : ∀ j, P j ≠ 0 := fun j => prod_ne_zero_iff.mpr fun n _ => hρ'ne n
  have hPsucc : ∀ j, P (j + 1) = P j * ρ' j := fun j => prod_range_succ _ _
  have hPmono : Monotone fun j => ‖P j‖ := by
    refine monotone_nat_of_le_succ fun j => ?_
    simp only [hPsucc, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (hρ'1 j)
  have hP0 : P 0 = 1 := by simp [hP]
  have hc1 : 1 ≤ ‖P k‖ := by
    have := hPmono (Nat.zero_le k); simpa [hP0] using this
  set c := ‖P k‖ with hc
  have hcpos : 0 < c := by linarith
  set N := p ^ (k + 1) - 1 with hN
  have hpk : 2 ≤ p ^ (k + 1) := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hNpos : 0 < N := by omega
  have hN1 : p ^ (k + 1) = N + 1 := by omega
  set w : F := (lam 0 * ϖ) ^ p / ((lam (Fin.last k)) ^ p * P k ^ p ^ (k + 1)) with hw
  have hwn : ‖w‖ = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c ^ (N + 1)) := by
    rw [hw]
    simp only [norm_div, norm_mul, norm_pow, hϖ, ← hN1]
    ring
  have hwne : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (hlam 0) (by
      intro h0; rw [h0, norm_zero] at hϖ; exact (inv_pos.mpr hpR).ne' hϖ.symm)))
      (mul_ne_zero (pow_ne_zero _ (hlam _)) (pow_ne_zero _ (hPne k)))
  obtain ⟨π0, hπ0⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
  have hπ0ne : π0 ≠ 0 := by
    intro h0; rw [h0, zero_pow hNpos.ne'] at hπ0; exact hwne hπ0.symm
  set s := ‖π0‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr hπ0ne
  have hsN : s ^ N = ‖w‖ := by rw [hs, ← norm_pow, hπ0]
  have hl0 : ‖lam 0‖ / p < ‖lam (Fin.last k)‖ := by
    rw [div_lt_iff₀ hpR, mul_comm]; exact hclose 0 (Fin.last k)
  have hsc : s * c < 1 := by
    have key : (s * c) ^ N < 1 := by
      have hwc : ‖w‖ * c ^ N = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c) := by
        rw [hwn, pow_succ]
        field_simp
      rw [mul_pow, hsN, hwc, div_lt_one (by have := hl (Fin.last k); positivity)]
      calc (‖lam 0‖ / p) ^ p < ‖lam (Fin.last k)‖ ^ p :=
            pow_lt_pow_left₀ hl0 (by positivity) (by omega)
        _ ≤ ‖lam (Fin.last k)‖ ^ p * c :=
            le_mul_of_one_le_right (by have := hl (Fin.last k); positivity) hc1
    exact (pow_lt_one_iff_of_nonneg (by positivity) hNpos.ne').mp key
  refine ⟨fun j => π0 * P j, fun j => ⟨mul_ne_zero hπ0ne (hPne _), ?_⟩, fun j => ?_, ?_⟩
  · rw [norm_mul, ← hs]
    calc s * ‖P j‖ ≤ s * c := mul_le_mul_of_nonneg_left (hPmono (Nat.lt_succ_iff.mp j.isLt)) hspos.le
      _ < 1 := hsc
  · simp only [Fin.val_succ, Fin.coe_castSucc, hPsucc, norm_mul, mul_pow]
    have : ρ' j = ρ j := by simp [hρ', j.isLt]
    rw [this, hρn]
    have := hl j.succ
    field_simp
  · simp only [Fin.val_zero, Fin.val_last, hP0, mul_one, norm_mul, ← hs, ← hc, mul_pow, ← pow_mul]
    rw [← pow_succ, hN1, pow_succ s N, hsN, hwn]
    have := hl (Fin.last k)
    field_simp

end GlobalTheory.PMonE
end

section

namespace GlobalTheory.UnitValueExistence

open Matrix

theorem norm_add_lt_one {E : Type} [NormedField E] [IsUltrametricDist E] {a b : E}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem norm_one_add_eq_one {E : Type} [NormedField E] [IsUltrametricDist E] {a : E}
    (ha : ‖a‖ < 1) : ‖1 + a‖ = 1 := by
  have h : ‖(1 : E)‖ ≠ ‖a‖ := by rw [norm_one]; exact ha.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left ha.le]

theorem norm_det_lt_one {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (h : ∀ i j, ‖G i j‖ < 1) : ‖G.det‖ < 1 := by
  rw [Matrix.det_apply']
  refine Finset.sum_induction _ (fun x : E => ‖x‖ < 1) (fun a b ha hb => norm_add_lt_one ha hb)
    (by simp) ?_
  intro σ _
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [norm_mul, hs, one_mul, norm_prod]
  obtain ⟨i⟩ := ‹Nonempty n›
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h2 : ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => (h _ _).le)
  calc ‖G (σ i) i‖ * ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ ‖G (σ i) i‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact h _ _

theorem exists_unit_value {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he : ‖e0‖ ≤ (1 : ℝ)) (htr : e0 + star e0 = 1)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (hG : Matrix.IsHermitian G) (hint : ∀ i j, ‖G i j‖ ≤ (1 : ℝ)) (hdet : ‖G.det‖ = (1 : ℝ)) :
    ∃ (i : n) (w : n → E), (∀ a, ‖w a‖ ≤ (1 : ℝ)) ∧ w i = 1 ∧
      ‖star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ) := by
  by_cases hd : ∃ i, ‖G i i‖ = 1
  · obtain ⟨i, hi⟩ := hd
    refine ⟨i, Pi.single i 1, ?_, by simp, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    · have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
        rw [Pi.star_single, star_one]
      rw [hs, single_dotProduct, Matrix.mulVec_single_one]
      simpa using hi
  · have hdiag : ∀ i, ‖G i i‖ < 1 := fun i =>
      lt_of_le_of_ne (hint i i) (fun h => hd ⟨i, h⟩)
    have hex : ∃ i j, ‖G i j‖ = 1 := by
      by_contra hne
      have := norm_det_lt_one G (fun i j => lt_of_le_of_ne (hint i j) (fun h => hne ⟨i, j, h⟩))
      exact this.ne hdet
    obtain ⟨i, j, hij⟩ := hex
    have hne : i ≠ j := by
      rintro rfl
      exact (hdiag i).ne hij
    have hg0 : G i j ≠ 0 := by
      intro h; rw [h, norm_zero] at hij; exact zero_ne_one hij
    set t : E := e0 / G i j with ht
    have htn : ‖t‖ ≤ 1 := by rw [ht, norm_div, hij, div_one]; exact he
    have htG : G i j * t = e0 := by rw [ht]; field_simp
    have hji : G j i = star (G i j) := (hG.apply j i).symm
    have htG' : star t * G j i = star e0 := by rw [hji, ← star_mul, htG]
    refine ⟨i, Pi.single i 1 + Pi.single j t, ?_, ?_, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp [Pi.single_eq_of_ne hne]
      · by_cases hb : a = j
        · subst hb; simpa [Pi.single_eq_of_ne ha] using htn
        · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
    · simp [Pi.single_eq_of_ne hne]
    · have hs : star (Pi.single i (1 : E) + Pi.single j t : n → E)
          = Pi.single i 1 + Pi.single j (star t) := by
        rw [star_add, Pi.star_single, Pi.star_single, star_one]
      have key : star (Pi.single i (1 : E) + Pi.single j t : n → E) ⬝ᵥ
          Matrix.mulVec G (Pi.single i 1 + Pi.single j t)
          = 1 + (G i i + star t * (G j j * t)) := by
        rw [hs, add_dotProduct, single_dotProduct, single_dotProduct, Matrix.mulVec_add]
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct_single]
        linear_combination htG + htG' + htr
      rw [key]
      apply norm_one_add_eq_one
      apply norm_add_lt_one (hdiag i)
      rw [norm_mul, norm_mul, hstar]
      have h1 := hdiag j
      have h2 := norm_nonneg t
      have h3 := norm_nonneg (G j j)
      have h4 : ‖G j j‖ * ‖t‖ ≤ ‖G j j‖ := mul_le_of_le_one_right h3 htn
      have h5 : ‖t‖ * (‖G j j‖ * ‖t‖) ≤ ‖G j j‖ * ‖t‖ :=
        mul_le_of_le_one_left (mul_nonneg h3 h2) htn
      linarith

theorem main : (let d1 : {E : Type} → [NormedField E] → {n m : Type} → Matrix n m E → Prop := @(fun {E : Type} [NormedField E] {n m : Type} (h : Matrix n m E) ↦ ∀ (i : n) (j : m), ‖h i j‖ ≤ (1 : ℝ)); ∀ {E : Type} [inst : NormedField E] [IsUltrametricDist E] [inst_2 : StarRing E], (∀ (y : E), ‖Star.star y‖ = ‖y‖) → ∀ (e0 : E), ‖e0‖ ≤ (1 : ℝ) → e0 + Star.star e0 = (1 : E) → ∀ {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] [Nonempty n] (G : Matrix n n E), Matrix.IsHermitian G → d1 G → ‖Matrix.det G‖ = (1 : ℝ) → ∃ (i : n) (w : n → E), (∀ (a : n), ‖w a‖ ≤ (1 : ℝ)) ∧ w i = (1 : E) ∧ ‖Star.star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ)) := by
  intro d1 E _ _ _ hstar e0 he htr n _ _ _ G hG hint hdet
  exact exists_unit_value hstar e0 he htr G hG hint hdet

end GlobalTheory.UnitValueExistence
end

section

open Polynomial

namespace GlobalTheory

theorem norm_hasSum_eq_of_dominant : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type)
    (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  intro K _ _ ι f s i₀ hsum h
  classical
  have hs : Summable f := hsum.summable
  have hf : Filter.Tendsto f Filter.cofinite (nhds 0) := hs.tendsto_cofinite_zero
  rw [← hsum.tsum_eq, hs.tsum_eq_add_tsum_ite i₀]
  by_cases h0 : f i₀ = 0
  · have : ∀ i, (if i = i₀ then 0 else f i) = 0 := by
      intro i
      split_ifs with hi
      · rfl
      · have := h i hi
        rw [h0, norm_zero] at this
        exact absurd this (norm_nonneg _).not_gt
    simp [this]
  have hc : 0 < ‖f i₀‖ := norm_pos_iff.2 h0
  set g : ι → K := fun i => if i = i₀ then 0 else f i with hg
  have hglt : ∀ i, ‖g i‖ < ‖f i₀‖ := by
    intro i
    simp only [hg]
    split_ifs with hi
    · simpa using hc
    · exact h i hi
  have hfin : {i | ¬ ‖f i‖ < ‖f i₀‖ / 2}.Finite := by
    have := (NormedAddGroup.tendsto_nhds_zero.1 hf) (‖f i₀‖ / 2) (by positivity)
    exact Filter.eventually_cofinite.1 this
  obtain ⟨j, -, hj⟩ := Set.exists_max_image _ (fun i => ‖g i‖) hfin
    ⟨i₀, by simp only [Set.mem_setOf_eq]; linarith⟩
  have hb : ‖∑' i, g i‖ ≤ max (‖f i₀‖ / 2) ‖g j‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
    by_cases hi : ‖f i‖ < ‖f i₀‖ / 2
    · refine le_max_of_le_left ?_
      simp only [hg]
      split_ifs
      · simp only [norm_zero]; positivity
      · exact hi.le
    · exact le_max_of_le_right (hj i hi)
  have hlt : ‖∑' i, g i‖ < ‖f i₀‖ := hb.trans_lt (max_lt (by linarith) (hglt j))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

end GlobalTheory
end
