module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rank_rows_of_crude_bounds (y m k f L l A B : ℝ) (hy : 8 ≤ y) (hA : 64 * A ≤ y) (hB : B ≤ y)
    (hm0 : 0 ≤ m) (hm : m ≤ 2 * y) (hk : y ^ 9 ≤ k) (hf : y ^ 4 ≤ f) (hL0 : 0 ≤ L) (hL : L ≤ y)
    (hl0 : 0 ≤ l) (hl : l ≤ y ^ 2) :
    m ^ 2 * L ≤ k ∧ m * y * l ≤ k ∧ A * m ^ 6 * L ≤ k * Real.log k ∧ B * L ≤ f * Real.log k := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hpow : ∀ a b : ℕ, a ≤ b → y ^ a ≤ y ^ b := fun a b h => pow_le_pow_right₀ hy1 h
  have hk8 : 8 ≤ k := by
    have := hpow 1 9 (by norm_num)
    rw [pow_one] at this
    linarith
  have hlog : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hkk : k ≤ k * Real.log k := le_mul_of_one_le_right (by linarith) hlog
  have hff : f ≤ f * Real.log k := le_mul_of_one_le_right (le_trans (by positivity) hf) hlog
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m ^ 2 * L ≤ (2 * y) ^ 2 * y := by gcongr
      _ = 4 * y ^ 3 := by ring
      _ ≤ y * y ^ 3 := by gcongr; linarith
      _ = y ^ 4 := by ring
      _ ≤ k := (hpow 4 9 (by norm_num)).trans hk
  · calc m * y * l ≤ (2 * y) * y * y ^ 2 := by gcongr
      _ = 2 * y ^ 4 := by ring
      _ ≤ y * y ^ 4 := by gcongr; linarith
      _ = y ^ 5 := by ring
      _ ≤ k := (hpow 5 9 (by norm_num)).trans hk
  · calc A * m ^ 6 * L = A * (m ^ 6 * L) := by ring
      _ ≤ (y / 64) * (m ^ 6 * L) := by gcongr; linarith
      _ ≤ (y / 64) * ((2 * y) ^ 6 * y) := by gcongr
      _ = y ^ 8 := by ring
      _ ≤ k := (hpow 8 9 (by norm_num)).trans hk
      _ ≤ _ := hkk
  · calc B * L ≤ y * L := by gcongr
      _ ≤ y * y := by gcongr
      _ = y ^ 2 := by ring
      _ ≤ f := (hpow 2 4 (by norm_num)).trans hf
      _ ≤ _ := hff

theorem szRow_rank_lower_bounds :
    SzRow (fun C D L => ((D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k) ∧ ((D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) * Real.log L.sc.x ≤ D.R.k) ∧ (C.P.Ck6 * (D.R.m : ℝ) ^ 6 * L.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k) ∧ (C.P.CfL * L.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(max 8 (max (64 * C.P.Ck6) C.P.CfL)) ^ 2, ?_⟩⟩⟩
  intro D L _ hx hV
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hV.ranks
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hp := L.sc.eps_pos
  have hq := L.sc.eps_lt
  have hy : max 8 (max (64 * C.P.Ck6) C.P.CfL) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le hx
  have hnat : ∀ j : ℕ, (L.sc.x ^ ((1 : ℝ) / 2)) ^ j = L.sc.x ^ ((j : ℝ) / 2) := by
    intro j
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  have hmono : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  refine rank_rows_of_crude_bounds (L.sc.x ^ ((1 : ℝ) / 2)) _ _ _ _ _ _ _
    ((le_max_left _ _).trans hy) (((le_max_left _ _).trans (le_max_right _ _)).trans hy)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hy) (Nat.cast_nonneg _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine hm.trans ?_
    rw [← Real.sqrt_eq_rpow]
    have hd : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
    have : L.sc.x * L.sc.delta1 ≤ L.sc.x := mul_le_of_le_one_right hx0.le hd
    gcongr
  · rw [hnat]
    exact (hmono _ _ (by push_cast; linarith)).trans hk
  · rw [hnat]
    refine ((hmono _ _ (by push_cast; linarith)).trans hn).trans ?_
    have h0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
    unfold Ranks.f
    push_cast
    linarith
  · exact Real.rpow_nonneg hx0.le _
  · exact hmono _ _ (by linarith)
  · exact Real.log_nonneg hx1.le
  · rw [hnat]
    have := Real.log_le_sub_one_of_pos hx0
    norm_num
    linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_rankSizes : SzRow (fun _ _ L => SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeT L ∧ SizeTT L ∧ SizeDe2 L ∧ SizeLw L) := by
  intro eps h0 h1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨Real.exp (100 / eps * (2 * C.P.Cpde) + 4455), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog' : 100 / eps * (2 * C.P.Cpde) + 4455 ≤ Real.log L.sc.x := (Real.le_log_iff_exp_le hx0).2 hx
  have hq : 0 < 100 / eps := by positivity
  have hC1 : 1 ≤ C.P.Cpde := hV.host.one_le
  have hlog : 100 / eps + 4455 ≤ Real.log L.sc.x := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * C.P.Cpde by linarith) hq.le
    linarith
  have hth : szTh L = eps / 100 := by rw [szTh, he]
  have hth0 : 0 ≤ szTh L := by rw [hth]; positivity
  have h2C : 2 * C.P.Cpde ≤ L.sc.x ^ szTh L := by
    rw [Real.rpow_def_of_pos hx0, hth]
    have a : 2 * C.P.Cpde ≤ Real.log L.sc.x * (eps / 100) := by
      have b : 100 / eps * (2 * C.P.Cpde) * (eps / 100) = 2 * C.P.Cpde := by field_simp
      have c : 100 / eps * (2 * C.P.Cpde) * (eps / 100) ≤ Real.log L.sc.x * (eps / 100) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have := Real.add_one_le_exp (Real.log L.sc.x * (eps / 100))
    linarith
  have h2 : 2 ≤ L.sc.x ^ szTh L := by linarith
  have hneg : L.sc.x ^ (-szTh L) ≤ 1 / 2 := by
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hlo : ∀ a : ℝ, L.sc.x ^ (a - szTh L) ≤ L.sc.x ^ a := fun a =>
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hhi : ∀ a : ℝ, 2 * L.sc.x ^ a ≤ L.sc.x ^ (a + szTh L) := fun a => by
    rw [Real.rpow_add hx0, mul_comm]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hn : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have n2 : (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := by
    refine (hV.ranks.n_le_of_o hV.host.o_le).trans ?_
    rw [Real.rpow_add hx0 (2 + 8 * L.sc.eps), mul_comm]
    exact mul_le_mul_of_nonneg_left h2C (by positivity)
  obtain ⟨⟨n1, -⟩, ⟨m1, m2⟩, ⟨k1, k2⟩, -⟩ := hV.ranks
  obtain ⟨-, ⟨t1, t2⟩, d2, -, -, hLw, -⟩ := hV.host
  have hs := Real.sqrt_nonneg (L.sc.x * L.sc.delta1)
  have hd1 : 0 ≤ L.sc.delta1 := by unfold Scale.delta1; positivity
  refine ⟨⟨(hlo _).trans n1, n2⟩, ⟨?_, ?_⟩, ⟨(hlo _).trans k1, k2.trans (hhi _)⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hneg hs
    linarith
  · exact m2.trans (mul_le_mul_of_nonneg_right h2 hs)
  · have h := D.R.rank_add_five_le
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  · exact L.t_win.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
  · have := mul_le_mul_of_nonneg_right hneg (mul_nonneg hn.le hd1)
    calc L.sc.x ^ (-szTh L) * D.R.n * L.sc.delta1 = L.sc.x ^ (-szTh L) * (D.R.n * L.sc.delta1) := by ring
      _ ≤ 1 / 2 * (D.R.n * L.sc.delta1) := this
      _ = L.sc.delta1 * D.R.n / 2 := by ring
      _ ≤ _ := t1
  · exact t2.trans (le_of_eq (by unfold szNst; ring))
  · unfold SizeDe2
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn]
    exact d2
  · unfold SizeLw
    rw [hLw, Lwv, he]
    have a1 : (⌈(405 : ℝ) * Real.log L.sc.x⌉₊ : ℝ) < 405 * Real.log L.sc.x + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have a2 : (⌈30 / eps⌉₊ : ℝ) < 30 / eps + 1 := Nat.ceil_lt_add_one (by positivity)
    have a3 : 100 / eps = 10 / 3 * (30 / eps) := by ring
    have a4 : 4455 * Real.log L.sc.x ≤ Real.log L.sc.x ^ 2 := by nlinarith
    push_cast
    linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem logf_sq_le_rS : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), x0 ≤ s.x → RankVal s R →
    Real.log R.f ^ 2 ≤ (R.rS : ℝ) := by
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (1 / 4) 0 36 (1 / 2) 2 le_rfl (by norm_num) (by norm_num)
  refine ⟨max x1 (Real.exp 1), fun s R hx hR => ?_⟩
  have hn := hR.n_le'
  obtain ⟨-, ⟨hm, -⟩, -, -⟩ := hR
  have hx1 := h1 s.x (le_trans (le_max_left _ _) hx)
  have hxe : Real.exp 1 ≤ s.x := le_trans (le_max_right _ _) hx
  have h1x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_lt
  have he0 := s.eps_pos
  have hl : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  rw [Real.rpow_zero] at hx1
  have hm' : s.x ^ (1 / 4 : ℝ) ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm
    apply Real.le_sqrt_of_sq_le
    unfold Scale.delta1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have : s.x * s.x ^ (-(s.eps / 8)) = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [this]
    apply Real.rpow_le_rpow_of_exponent_le h1x.le
    push_cast
    linarith
  have hf1 : 1 ≤ R.f := by
    have : 0 < R.ord := R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (3 : ℝ) := by
    have : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1x.le (by norm_num)
    unfold Ranks.f
    push_cast
    linarith
  have hlf : Real.log R.f ≤ 6 * Real.log s.x := by
    have h2 := Real.log_le_log (by linarith) hf
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h2
    have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlf0 : 0 ≤ Real.log R.f := Real.log_nonneg hf1'
  have hsq : Real.log R.f ^ 2 ≤ (6 * Real.log s.x) ^ 2 := pow_le_pow_left₀ hlf0 hlf 2
  have hr : R.m ≤ 2 * R.rS + 3 := by unfold Ranks.rS; omega
  have hr' : (R.m : ℝ) ≤ 2 * R.rS + 3 := by exact_mod_cast hr
  nlinarith

theorem szRow_logf : SzRow (fun C D L => (Real.log D.R.f ≤ Real.sqrt D.R.rS) ∧
    (Real.log D.R.f ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L) ∧
    (Real.log (Real.log L.sc.b) ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r) ∧
    ((4 * (D.R.f : ℝ) + 10) * D.R.r ≤ nW L C.P.CnW)) := by
  intro eps _ _ C hC
  obtain ⟨x1, h1⟩ := logf_sq_le_rS
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 C.P.cLL⁻¹, fun D L _ hx hV => ?_⟩⟩⟩
  have hsq := h1 L.sc D.R (le_trans (le_max_left _ _) hx) hV.ranks
  have hxc : C.P.cLL⁻¹ ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hc1 : 1 ≤ C.P.cLL⁻¹ := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  have hc0 : 0 < C.P.cLL := inv_pos.mp (by linarith)
  have hW : C.P.CnW = 10 := hC.1.2.2.2.2.2.2.2.1
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
  have h1x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_lt
  have he0 := L.sc.eps_pos
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hf2 : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf2' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf2
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow h1x.le he0.le
  have hm2' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  refine ⟨Real.le_sqrt_of_sq_le hsq, ?_, ?_, ?_⟩
  · have hr : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have hr' : (D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast hr
    have h2 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h3 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L := le_mul_of_one_le_right (by positivity) hL
    linarith
  · have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    have hxk : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := by
      conv_lhs => rw [← Real.rpow_one L.sc.x]
      exact Real.rpow_le_rpow_of_exponent_le h1x.le (by linarith)
    have hxr : L.sc.x ≤ D.R.r := by linarith
    have hl0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg h1x.le
    have hlr : Real.log L.sc.x ≤ Real.log D.R.r := Real.log_le_log hx0 hxr
    have hb : Real.log (Real.log L.sc.b) = L.sc.eps * Real.log L.sc.x := by
      unfold Scale.b Scale.L
      rw [Real.log_exp, Real.log_rpow hx0]
    have hcr : 1 ≤ C.P.cLL * D.R.r := by
      have := mul_le_mul_of_nonneg_left (le_trans hxc hxr) hc0.le
      rwa [mul_inv_cancel₀ hc0.ne'] at this
    have hcrf : 1 ≤ C.P.cLL * D.R.r * D.R.f := by nlinarith
    have h3 : Real.log D.R.r ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r :=
      le_mul_of_one_le_left (by linarith) hcrf
    rw [hb]
    nlinarith
  · unfold nW
    rw [hW]
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by linarith
    have h2 : 0 ≤ (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m := by positivity
    have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
    nlinarith [mul_nonneg hr0 h2, mul_nonneg hr0 (sub_nonneg.mpr hf2')]

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

open NumberField in
private theorem exists_mul_pow_le_exp_half_rpow (eps K : ℝ) (N : ℕ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → K * x ^ N ≤ Real.exp (x ^ eps / 2) := by
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 eps ((N : ℝ) + 1) 0 (1 / 2) 0 le_rfl heps (by norm_num)
  refine ⟨max (max x1 K) 1, fun x hx => ?_⟩
  have hxK : K ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1' : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hlog := hx1 x hx1'
  simp only [zero_mul, add_zero] at hlog
  calc K * x ^ N ≤ x * x ^ N := mul_le_mul_of_nonneg_right hxK (by positivity)
    _ = Real.exp (((N : ℝ) + 1) * Real.log x) := by
        rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul, Real.exp_log hxpos]
        ring
    _ ≤ Real.exp (x ^ eps / 2) := by
        apply Real.exp_le_exp.mpr
        linarith

open NumberField in
private theorem zBase_and_log_b_bounds {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (hR : _root_.GlobalTheory.EX.RankVal L.sc D.R) :
    1 ≤ L.sc.x ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ 5 ∧ (D.R.m : ℝ) ≤ 2 * L.sc.x ^ 5 ∧
      (D.R.f : ℝ) ≤ 2 * L.sc.x ^ 5 ∧ (D.R.r : ℝ) ≤ 4 * L.sc.x ^ 5 ∧
      ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) ≤ 2 * L.sc.x ^ 377 ∧
      Real.log L.sc.b ≤ L.sc.x ∧ 0 ≤ Real.log L.sc.b ∧
      0 ≤ _root_.Formalism.BasicNotions.zBase L ∧ _root_.Formalism.BasicNotions.zBase L ≤ 8 * L.sc.x ^ 11 ∧
      ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ 32 * L.sc.x ^ 15 := by
  obtain ⟨-, -, ⟨-, hk⟩, -⟩ := hR
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have heps := L.sc.eps_pos
  have heps' := L.sc.eps_lt
  have hx5 : x ^ (9 / 2 + 10 * L.sc.eps) ≤ x ^ 5 := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    push_cast; linarith
  have hkx : (D.R.k : ℝ) ≤ 2 * x ^ 5 := by linarith
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hrk : D.R.r ≤ 2 * D.R.k := by
    show D.R.k + D.R.m - 1 ≤ 2 * D.R.k
    omega
  have hmx : (D.R.m : ℝ) ≤ 2 * x ^ 5 := le_trans (by exact_mod_cast hmk) hkx
  have hfx : (D.R.f : ℝ) ≤ 2 * x ^ 5 := le_trans (by exact_mod_cast hfk) hkx
  have hrx : (D.R.r : ℝ) ≤ 4 * x ^ 5 := by
    have : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast hrk
    linarith
  have hL0 : 0 ≤ L.sc.L := Real.rpow_nonneg hx0 _
  have hLx : L.sc.L ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show L.sc.eps ≤ 1 by linarith)
    simpa [_root_.Formalism.BasicNotions.Scale.L] using h
  have hlogb : Real.log L.sc.b = L.sc.L := by simp [_root_.Formalism.BasicNotions.Scale.b]
  have hxp : 1 ≤ x ^ 377 := one_le_pow₀ hx1
  have hT : ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) ≤ 2 * x ^ 377 := by
    simp only [_root_.GlobalTheory.EX.TOv]
    have hpow : x ^ (377 : ℝ) = x ^ (377 : ℕ) := by exact_mod_cast Real.rpow_natCast x 377
    rw [hpow]
    have := Nat.ceil_lt_add_one (show 0 ≤ x ^ 377 by positivity)
    linarith
  have hz : _root_.Formalism.BasicNotions.zBase L = (D.R.f : ℝ) * D.R.r * L.sc.L := by simp [_root_.Formalism.BasicNotions.zBase]
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hch : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
    rw [Nat.choose_two_right]
    calc D.R.r * (D.R.r - 1) / 2 ≤ D.R.r * (D.R.r - 1) := Nat.div_le_self _ _
      _ ≤ D.R.r * D.R.r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = D.R.r ^ 2 := by ring
  have hchR : ((D.R.r.choose 2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hch
  refine ⟨hx1, hkx, hmx, hfx, hrx, hT, by rw [hlogb]; exact hLx, by rw [hlogb]; exact hL0,
    by rw [hz]; positivity, ?_, ?_⟩
  · rw [hz]
    calc (D.R.f : ℝ) * D.R.r * L.sc.L ≤ (2 * x ^ 5) * (4 * x ^ 5) * x := by gcongr
      _ = 8 * x ^ 11 := by ring
  · push_cast
    calc (D.R.f : ℝ) * ((D.R.r.choose 2 : ℕ) : ℝ) ≤ (2 * x ^ 5) * (4 * x ^ 5) ^ 2 := by
          gcongr
          exact le_trans hchR (by gcongr)
      _ = 32 * x ^ 15 := by ring

open NumberField in
private theorem scale_b_rpow_half (s : _root_.Formalism.BasicNotions.Scale) :
    s.b ^ (1 / 2 : ℝ) = Real.exp (s.x ^ s.eps / 2) := by
  simp only [_root_.Formalism.BasicNotions.Scale.b, _root_.Formalism.BasicNotions.Scale.L]
  rw [← Real.exp_mul]
  ring_nf

open NumberField in
private theorem exp_half_le_scale_b (s : _root_.Formalism.BasicNotions.Scale) :
    Real.exp (s.x ^ s.eps / 2) ≤ s.b := by
  simp only [_root_.Formalism.BasicNotions.Scale.b, _root_.Formalism.BasicNotions.Scale.L]
  apply Real.exp_le_exp.mpr
  have : 0 ≤ s.x ^ s.eps := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  linarith


open NumberField in
theorem _root_.GlobalTheory.EX.szRow_poly_le_b : _root_.GlobalTheory.EX.SzRow (fun C D L => (((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ (C.T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ C.T.eP) ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 ≤ L.sc.b)) := by
  intro eps heps _ C hC
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, h1⟩ := exists_mul_pow_le_exp_half_rpow eps 2048 (377 + 30 + 1 + ⌈C.T.Cb⌉₊) heps
  obtain ⟨x2, h2⟩ := exists_mul_pow_le_exp_half_rpow eps 2048 (377 + 30 + 1) heps
  obtain ⟨x3, h3⟩ := exists_mul_pow_le_exp_half_rpow eps
    (|C.T.CbN| * 16 * C.T.CP ^ 2 * 8 ^ 24 * 32 ^ 3) (15 + 264 + 45) heps
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max x1 x2) x3, fun D L hε hx hL => ?_⟩⟩⟩
  obtain ⟨hx1, hk, hm, hf, hr, hT, hlog, hlog0, hz0, hz, hQ⟩ :=
    zBase_and_log_b_bounds L hL.ranks
  have hxCb : L.sc.x ^ C.T.Cb ≤ L.sc.x ^ ⌈C.T.Cb⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil _)
  have hxCb0 : 0 ≤ L.sc.x ^ C.T.Cb := Real.rpow_nonneg (by linarith) _
  have hb2 : L.sc.b ^ (1 / 2 : ℝ) = Real.exp (L.sc.x ^ eps / 2) := by rw [scale_b_rpow_half, hε]
  have hbb : Real.exp (L.sc.x ^ eps / 2) ≤ L.sc.b := hε ▸ exp_half_le_scale_b L.sc
  have hzP : _root_.Formalism.BasicNotions.zBase L ^ C.T.eP = _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ) := by
    rw [heP]; exact_mod_cast Real.rpow_natCast _ 12
  have hx0 : (0 : ℝ) ≤ L.sc.x := by linarith
  have hxa : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x3 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  refine ⟨?_, ?_, ?_⟩
  · calc ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ C.T.Cb
          ≤ (2 * L.sc.x ^ 377) * (32 * L.sc.x ^ 15) ^ 2 * L.sc.x * L.sc.x ^ ⌈C.T.Cb⌉₊ := by gcongr
      _ = 2048 * L.sc.x ^ (377 + 30 + 1 + ⌈C.T.Cb⌉₊) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h1 _ hxa
      _ ≤ L.sc.b := hbb
  · rw [hb2]
    calc ((_root_.GlobalTheory.EX.TOv L.sc : ℕ) : ℝ) * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * Real.log L.sc.b
          ≤ (2 * L.sc.x ^ 377) * (32 * L.sc.x ^ 15) ^ 2 * L.sc.x := by gcongr
      _ = 2048 * L.sc.x ^ (377 + 30 + 1) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h2 _ hxb
  · rw [hzP]
    have hrest : 0 ≤ (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
        ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 := by positivity
    calc C.T.CbN * (D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3
          = C.T.CbN * ((D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
            ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3) := by ring
      _ ≤ |C.T.CbN| * ((D.R.r : ℝ) * D.R.m * D.R.k * (C.T.CP * _root_.Formalism.BasicNotions.zBase L ^ (12 : ℕ)) ^ 2 *
            ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right (le_abs_self _) hrest
      _ ≤ |C.T.CbN| * ((4 * L.sc.x ^ 5) * (2 * L.sc.x ^ 5) * (2 * L.sc.x ^ 5) *
            (C.T.CP * (8 * L.sc.x ^ 11) ^ (12 : ℕ)) ^ 2 * (32 * L.sc.x ^ 15) ^ 3) := by gcongr
      _ = (|C.T.CbN| * 16 * C.T.CP ^ 2 * 8 ^ 24 * 32 ^ 3) * L.sc.x ^ (15 + 264 + 45) := by ring
      _ ≤ Real.exp (L.sc.x ^ eps / 2) := h3 _ hxc
      _ ≤ L.sc.b := hbb

end GlobalTheory.EX
end
