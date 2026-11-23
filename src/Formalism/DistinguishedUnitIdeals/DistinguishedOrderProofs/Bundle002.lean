module

public import Formalism.DistinguishedUnitIdeals.Bundle001
public import Formalism.DistinguishedUnitIdeals.Statement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.ExponentWindows

section Rounding

variable {K D : Type} [Field K] [AddCommGroup D] [Module K D]

lemma filt_eq_of_no_jump (Fil : ℤ → Submodule K D) (a c : ℤ) (hac : a ≤ c)
    (h : ∀ u, a ≤ u → u < c → Fil u = Fil (u+1)) : Fil a = Fil c := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, c = a + k := ⟨(c - a).toNat, by omega⟩
  clear hac
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 := ih (fun u h1 h2 => h u h1 (by omega))
    have e2 := h (a + k) (by omega) (by omega)
    rw [e1, e2]
    congr 1
    push_cast
    ring

lemma filt_eq_top_of_no_jump_below (Fil : ℤ → Submodule K D) (hA : Antitone Fil) (lo : ℤ) (hlo : Fil lo = ⊤) (a : ℤ)
    (h : ∀ u, u < a → Fil u = Fil (u+1)) : ∀ u, u ≤ a → Fil u = ⊤ := by
  intro u hu
  rcases le_or_gt u lo with hul | hul
  · exact top_unique (by rw [← hlo]; exact hA hul)
  · rw [← filt_eq_of_no_jump Fil lo u hul.le (fun v _ h2 => h v (by omega)), hlo]

lemma filt_eq_bot_of_no_jump_above (Fil : ℤ → Submodule K D) (hA : Antitone Fil) (hi : ℤ) (hhi : Fil hi = ⊥) (a : ℤ)
    (h : ∀ u, a ≤ u → Fil u = Fil (u+1)) : ∀ u, a ≤ u → Fil u = ⊥ := by
  intro u hu
  rcases le_or_gt hi u with hul | hul
  · exact le_bot_iff.mp (by rw [← hhi]; exact hA hul)
  · rw [filt_eq_of_no_jump Fil u hi hul.le (fun v h1 _ => h v (by omega)), hhi]

lemma filt_eq_of_no_jump_between (Fil : ℤ → Submodule K D) (a c : ℤ)
    (h : ∀ u, a ≤ u → u < c → Fil u = Fil (u+1)) : ∀ u, a ≤ u → u ≤ c → Fil u = Fil c := by
  intro u hu huc
  exact filt_eq_of_no_jump Fil u c huc (fun v h1 h2 => h v (by omega) h2)

theorem filtration_rounding : Rounding := by
  unfold Rounding
  intro K D _ _ _ Fil G S η g b hF hG hS hη hGg hSg hηg hgb
  simp only [IsFilt, NbThin, NbUp, NbDown] at hF ⊢
  obtain ⟨hA, ⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hF
  refine ⟨fun hj i => ?_, fun hj i => ?_, fun hj i => ?_⟩
  · have top : ∀ u, u ≤ -G → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-G)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, G + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (G + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1
      · exact bot_le
      · rw [top (-i) (by omega)]
    · split_ifs with h1
      · rw [bot (-i) (by omega)]
      · exact le_top
  · have top : ∀ u, u ≤ -η → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-η)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, b + S + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (b + S + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have mid : ∀ u, η + 1 ≤ u → u ≤ b → Fil u = Fil b :=
      filt_eq_of_no_jump_between Fil (η + 1) b
        (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1 h2
      · exact bot_le
      · exact hA (show -i ≤ b by omega)
      · rw [top (-i) (by omega)]
    · split_ifs with h1 h2
      · rw [bot (-i) (by omega)]
      · rcases le_or_gt b (-i) with h3 | h3
        · exact hA h3
        · rw [mid (-i) (by omega) (by omega)]
      · exact le_top
  · have top : ∀ u, u ≤ -b - S → Fil u = ⊤ :=
      filt_eq_top_of_no_jump_below Fil hA lo hlo (-b - S)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have bot : ∀ u, η + 1 ≤ u → Fil u = ⊥ :=
      filt_eq_bot_of_no_jump_above Fil hA hi hhi (η + 1)
        (fun u hu => by_contra fun hne => by have := hj u hne; omega)
    have mid : ∀ u, -b + 1 ≤ u → u ≤ -η → Fil u = Fil (-η) :=
      filt_eq_of_no_jump_between Fil (-b + 1) (-η)
        (fun u hu hu' => by_contra fun hne => by have := hj u hne; omega)
    constructor
    · split_ifs with h1 h2
      · exact bot_le
      · exact hA (show -i ≤ -η by omega)
      · rw [top (-i) (by omega)]
    · split_ifs with h1 h2
      · rw [bot (-i) (by omega)]
      · rcases le_or_gt (-η) (-i) with h3 | h3
        · exact hA h3
        · rw [mid (-i) (by omega) (by omega)]
      · exact le_top

end Rounding

end Formalism.ExponentWindows
end

section

noncomputable section

namespace Formalism.ExponentWindows

theorem pow_apply_sub_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (n : ℕ) : (γ ^ n) w - w ∈ U := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := hU _ ih
    have e0 : (γ ^ (n + 1)) w = γ ((γ ^ n) w) := by rw [pow_succ']; rfl
    have e : (γ ^ (n + 1)) w - w = γ ((γ ^ n) w - w) + (γ w - w) := by
      rw [e0, map_sub]; abel
    rw [e]
    exact U.add_mem h1 hw

theorem aeval_apply_sub_eval_one_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (P : Polynomial R) :
    Polynomial.aeval γ P w - P.eval 1 • w ∈ U := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : Polynomial.aeval γ (p + q) w - (p + q).eval 1 • w =
        (Polynomial.aeval γ p w - p.eval 1 • w) + (Polynomial.aeval γ q w - q.eval 1 • w) := by
      rw [map_add (f := _), LinearMap.add_apply, Polynomial.eval_add, add_smul]; abel
    rw [e]
    exact U.add_mem hp hq
  | monomial n a =>
    have e : Polynomial.aeval γ (Polynomial.monomial n a) w - (Polynomial.monomial n a).eval 1 • w =
        a • ((γ ^ n) w - w) := by
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, one_pow, mul_one, smul_sub]
      congr 1
      all_goals first
        | rfl
        | simp [Module.algebraMap_end_apply]
    rw [e]
    exact U.smul_mem a (pow_apply_sub_mem γ U hU w hw n)

theorem aeval_sub_eval_one_smul_mem : KillerShift := by
  intro R M _ _ _ γ U hU P w hw
  exact aeval_apply_sub_eval_one_mem γ U hU w hw P

end Formalism.ExponentWindows
end
end

section

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

theorem lam_eq_pow_mul {O : Type} [CommRing O] (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s : ℕ)
    (hs : s < ell) :
    abelian₂ p H ell = p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t := by
  unfold abelian₂
  rw [← Finset.mul_prod_erase (Finset.range ell) (fun t => p t ^ H t) (Finset.mem_range.mpr hs)]

theorem levelCond_of_sub_pow_smul {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (P : PowerSeries O)
    (H b : ℕ) (k : Kind) (hk : k ≠ Kind.down) (V : Submodule O (Fin r → O))
    (y w : Fin r → PowerSeries O) (m : ℕ)
    (h : LevelCond ϖ P H b k V (C (ϖ ^ m) • y - P ^ H • w)) :
    LevelCond ϖ P H b k V y := by
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    refine ⟨N + m, z + C (ϖ ^ N) • w, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, ← hz, smul_sub, smul_comm (P ^ H) (C (ϖ ^ N)) w]
    abel
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    refine ⟨N + m, c, z + C (ϖ ^ N) • w, hc, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, smul_comm (P ^ H) (C (ϖ ^ N)) w, ← add_assoc, ← hz,
      smul_sub]
    abel
  | down => exact absurd rfl hk

theorem levels_mod_const_iff_of_no_down : MNone := by
  intro O _ _ _ ϖ _ ℓ ell r p H b kind V _ _ _ _ hnd y
  constructor
  · intro hII s hs
    obtain ⟨d, k, hd⟩ := hII s hs
    rw [lam_eq_pow_mul p H ell s hs, mul_smul] at hd
    exact levelCond_of_sub_pow_smul ϖ (p s) (H s) (b s) (kind s) (hnd s hs) (V s) y _ k hd
  · intro hNN s hs
    refine ⟨0, 0, ?_⟩
    have h0 : (cst (0 : Fin r → O) : Fin r → PowerSeries O) = 0 := by
      funext i; simp [cst]
    simpa [h0] using hNN s hs

end Formalism.ExponentWindows
end
end
