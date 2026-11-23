module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rbS_numeric {x E P X b k r m de Del lg : ℝ} (hx : 8 ≤ x) (hE0 : 0 < E) (hE : E ≤ x) (hP : 0 ≤ P)
    (hk0 : 0 ≤ k) (hk : k ≤ 2 * x ^ 5) (hr : r ≤ 2 * k) (hm : 2 ≤ m) (hde : E⁻¹ ≤ de)
    (hD0 : 0 ≤ Del) (hD : Del ≤ 2 * P) (hl0 : 0 ≤ lg) (hl : lg ≤ x) (hb : 0 < b)
    (hX : x ^ 16 ≤ X) (hPb : x ^ 22 * P ≤ b) :
    r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de)) ≤ de * m * b := by
  have hx0 : 0 < x := by linarith
  have hxde : x⁻¹ ≤ de := (inv_anti₀ hE0 hE).trans hde
  have hde0 : 0 < de := lt_of_lt_of_le (inv_pos.mpr hx0) hxde
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have h1 : k * E / (m * de) ≤ 2 * x ^ 7 := by
    calc k * E / (m * de) ≤ (2 * x ^ 5) * x / (1 * x⁻¹) := by
          gcongr
          linarith
      _ = 2 * x ^ 7 := by field_simp
  have h2 : x * b / X ≤ b / (8 * x ^ 14) := by
    calc x * b / X ≤ x * b / x ^ 16 := by gcongr
      _ = b / (x * x ^ 14) := by field_simp
      _ ≤ b / (8 * x ^ 14) := by gcongr
  have h3 : k * (4 * Del) ≤ b / (8 * x ^ 14) := by
    rw [le_div_iff₀ (by positivity)]
    have h128 : (128 : ℝ) ≤ x ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 3)
    calc k * (4 * Del) * (8 * x ^ 14) ≤ (2 * x ^ 5) * (4 * (2 * P)) * (8 * x ^ 14) := by gcongr
      _ = 128 * (x ^ 19 * P) := by ring
      _ ≤ x ^ 3 * (x ^ 19 * P) := by gcongr
      _ = x ^ 22 * P := by ring
      _ ≤ b := hPb
  have hr' : r ≤ 4 * x ^ 5 := by linarith
  calc r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de))
      ≤ (4 * x ^ 5) * (b / (8 * x ^ 14) + b / (8 * x ^ 14)) * x * (2 * x ^ 7) := by
        gcongr
    _ = x⁻¹ * 2 * b := by field_simp; ring
    _ ≤ de * m * b := by gcongr

theorem szRow_rbS : SzRow (fun C D L => ((D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * lA L ≤
    L.de2 * D.R.m * L.sc.b)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 16 0 1 0 le_rfl (by linarith) one_pos
  obtain ⟨x2, h2⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 eps (22 + cD) 0 1 0 le_rfl he0 one_pos
  refine ⟨max 8 (max x1 x2), fun D L heps hx V => ?_⟩
  have hx8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx1 := h1 _ (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx)
  have hx2 := h2 _ (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx)
  simp only [zero_mul, add_zero, one_mul] at hx1 hx2
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hP : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hone hcD
  have hn : (0 : ℝ) < D.R.n := by
    have hn : 0 < D.R.n := by
      unfold Ranks.n
      have := D.R.two_le_m
      have := D.R.m_le_f
      omega
    exact_mod_cast hn
  beta_reduce
  unfold lA Scale.b' Scale.a
  rw [L.Sc_eq, V.Del_eq]
  refine rbS_numeric (P := L.sc.x ^ cD) hx8 (Real.rpow_pos_of_pos hx0 _) ?_ (by linarith) (Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_ (by positivity) ?_ (Real.log_nonneg hone) ((Real.log_le_sub_one_of_pos hx0).trans (by linarith))
    (Real.exp_pos _) ?_ ?_
  · calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ = L.sc.x := Real.rpow_one _
  · refine V.ranks.2.2.1.2.trans ?_
    have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hone (by push_cast; linarith)
    rw [Real.rpow_natCast] at this
    linarith
  · have h := D.R.m_add_three_le_k
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
    exact_mod_cast this
  · exact_mod_cast D.R.two_le_m
  · rw [L.typeDensity_eq_card_div, le_div_iff₀ hn, ← Real.rpow_neg hx0.le]
    exact V.host.2.2.1
  · have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    simp only [Delv, Rat.cast_natCast]
    linarith
  · unfold Scale.X'
    rw [heps, ← Real.exp_log (pow_pos hx0 16), Real.log_pow]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  · unfold Scale.b Scale.L
    rw [heps, ← Real.rpow_natCast, ← Real.rpow_add hx0, Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem f_mul_r_mul_L_le_pow_fourteen (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (hR : RankVal s R) :
    (R.f : ℝ) * (R.r : ℝ) * s.L ≤ s.x ^ 14 := by
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 ≤ s.x := by linarith
  have he0 := s.eps_pos
  have he1 := s.eps_lt
  obtain ⟨⟨-, hn⟩, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := hR
  have hpow : ∀ (a : ℝ) (n : ℕ), a ≤ n → s.x ^ a ≤ s.x ^ n := fun a n h => by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 h
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ 3 := by
    have h3 := hpow (2 + 8 * s.eps) 3 (by push_cast; linarith)
    have h2 : (R.f : ℝ) = 2 * (R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hk5 : (R.k : ℝ) ≤ 2 * s.x ^ 5 := by
    have h5 := hpow (9 / 2 + 10 * s.eps) 5 (by push_cast; linarith)
    linarith
  have hm1 : (R.m : ℝ) ≤ 2 * s.x := by
    have hd : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hsq : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      calc Real.sqrt (s.x * s.delta1) ≤ Real.sqrt (s.x ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [mul_le_mul_of_nonneg_left hd hx0]
        _ = s.x := Real.sqrt_sq hx0
    linarith
  have hx5 : s.x ≤ s.x ^ 5 := by
    have h4 : 1 ≤ s.x ^ 4 := one_le_pow₀ hx1
    nlinarith
  have hr : (R.r : ℝ) ≤ 4 * s.x ^ 5 := by
    have h1 : R.r ≤ R.k + R.m := Nat.sub_le _ _
    have h2 : (R.r : ℝ) ≤ R.k + R.m := by exact_mod_cast h1
    linarith
  have hL : s.L ≤ s.x := by
    calc s.x ^ s.eps ≤ s.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = s.x := Real.rpow_one _
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg hx0 _
  have h16 : (16 : ℝ) ≤ s.x ^ 5 := by
    have h1 : (2 : ℝ) ^ 5 ≤ s.x ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
    norm_num at h1
    linarith
  have hx3 := pow_nonneg hx0 3
  have hx5' := pow_nonneg hx0 5
  calc (R.f : ℝ) * R.r * s.L ≤ (4 * s.x ^ 3) * (4 * s.x ^ 5) * s.x :=
        mul_le_mul (mul_le_mul hf hr (by positivity) (by linarith)) hL hL0
          (mul_nonneg (by linarith) (by linarith))
    _ = 16 * s.x ^ 9 := by ring
    _ ≤ s.x ^ 5 * s.x ^ 9 := mul_le_mul_of_nonneg_right h16 (pow_nonneg hx0 9)
    _ = s.x ^ 14 := by ring

theorem szRow_TO_PP_le_b : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ))) := by
  intro eps heps heps' C hC
  obtain ⟨-, -, -, -, -, -, -, -, heP, -, -, -, -, hCP, -, hLast⟩ := hC
  have hCb : 1 ≤ C.T.Cb := hLast C.T.Cb (by simp [FC.cLast])
  obtain ⟨x1, hx1⟩ := GlobalTheory.scale_poly_comparison eps (1259 + C.T.Cb) (1 / 2) heps (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max x1 2) (4 * C.T.CP ^ 3), fun D L hLe hx hV => ?_⟩⟩⟩
  have hxK : 4 * C.T.CP ^ 3 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have hCP0 : 0 ≤ C.T.CP := by linarith

  have hXb := (hx1 L.sc hLe hxx1).2.2.1
  have hX' : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0 _)
  have hxc : L.sc.x ^ (1259 + C.T.Cb) ≤ L.sc.b ^ (1 / 2 : ℝ) :=
    le_trans (le_mul_of_one_le_right (Real.rpow_nonneg hx0 _) hX') hXb
  have hbh : L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b := by
    calc L.sc.b ^ (1 / 2 : ℝ) ≤ L.sc.b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
      _ = L.sc.b := Real.rpow_one _

  have hz : zBase L ≤ L.sc.x ^ 14 := f_mul_r_mul_L_le_pow_fourteen L.sc D.R hx2 hV.ranks
  obtain ⟨⟨hn1, -⟩, -, -, -⟩ := hV.ranks
  have hn : 1 ≤ (D.R.n : ℝ) := le_trans (Real.one_le_rpow hx1' (by linarith [L.sc.eps_pos])) hn1
  have hf1 : 1 ≤ (D.R.f : ℝ) := by
    have h2 : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by simp [Ranks.f]
    rw [h2]
    linarith
  have hr1 : 1 ≤ (D.R.r : ℝ) := by
    have h2 := D.R.two_le_m
    have h3 : 1 ≤ D.R.r := by
      unfold Ranks.r
      omega
    exact_mod_cast h3
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1' (le_of_lt L.sc.eps_pos)
  have hz1 : 1 ≤ zBase L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hL1
  have hz0 : 0 ≤ zBase L := by linarith
  have hz12 : zBase L ^ (12 : ℝ) = zBase L ^ (12 : ℕ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hP1 : 1 ≤ C.T.CP * zBase L ^ (12 : ℝ) := by
    rw [hz12]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hz1)
  have hP2 : C.T.CP * zBase L ^ (12 : ℝ) ≤ C.T.CP * L.sc.x ^ 168 := by
    rw [hz12]
    apply mul_le_mul_of_nonneg_left _ hCP0
    calc zBase L ^ 12 ≤ (L.sc.x ^ 14) ^ 12 := pow_le_pow_left₀ hz0 hz 12
      _ = L.sc.x ^ 168 := by ring
  have hT1 : (1 : ℝ) ≤ ((TOv L.sc : ℕ) : ℝ) := by
    have h1 : 0 < TOv L.sc := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxpos _)
    exact_mod_cast h1
  have hT2 : ((TOv L.sc : ℕ) : ℝ) ≤ 2 * L.sc.x ^ 377 := by
    have h1 : ((TOv L.sc : ℕ) : ℝ) < L.sc.x ^ (377 : ℝ) + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0 _)
    have h2 : L.sc.x ^ (377 : ℝ) = L.sc.x ^ (377 : ℕ) := by
      rw [show (377 : ℝ) = ((377 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : 1 ≤ L.sc.x ^ (377 : ℕ) := one_le_pow₀ hx1'
    rw [h2] at h1
    linarith
  have hCb1 : 1 ≤ L.sc.x ^ C.T.Cb := Real.one_le_rpow hx1' (by linarith)
  have hW : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤
      L.sc.x ^ (1259 + C.T.Cb) := by
    have h1 : (C.T.CP * zBase L ^ (12 : ℝ)) ^ 3 ≤ (C.T.CP * L.sc.x ^ 168) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hP2 3
    have h2 : ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ (2 * L.sc.x ^ 377) ^ 2 := pow_le_pow_left₀ (by linarith) hT2 2
    have h3 := mul_le_mul h1 h2 (by positivity) (pow_nonneg (mul_nonneg hCP0 (pow_nonneg hx0 _)) _)
    have h4 : (C.T.CP * L.sc.x ^ 168) ^ 3 * (2 * L.sc.x ^ 377) ^ 2 = 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 := by ring
    have h5 : 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x ^ 1259 := by
      calc 4 * C.T.CP ^ 3 * L.sc.x ^ 1258 ≤ L.sc.x * L.sc.x ^ 1258 :=
            mul_le_mul_of_nonneg_right hxK (pow_nonneg hx0 _)
        _ = L.sc.x ^ 1259 := by ring
    have h6 : L.sc.x ^ (1259 : ℕ) * L.sc.x ^ C.T.Cb = L.sc.x ^ (1259 + C.T.Cb) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hxpos]
      norm_num
    rw [← h6]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0 _)
    rw [← h4] at h5
    exact le_trans h3 h5
  beta_reduce
  rw [heP]
  generalize ((TOv L.sc : ℕ) : ℝ) = T at hT1 hW ⊢
  generalize C.T.CP * zBase L ^ (12 : ℝ) = P at hP1 hW ⊢
  have hTP : T * P ≤ P ^ 3 * T ^ 2 := by
    have hP3 : P ≤ P ^ 3 := by nlinarith [one_le_pow₀ (n := 2) hP1]
    have hT' : T ≤ T ^ 2 := by nlinarith
    calc T * P ≤ T ^ 2 * P ^ 3 := mul_le_mul hT' hP3 (by linarith) (by positivity)
      _ = P ^ 3 * T ^ 2 := by ring
  have hW' : P ^ 3 * T ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ) := by
    have h1 : P ^ 3 * T ^ 2 ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by linarith) 3) (sq_nonneg T)) hCb1
    linarith
  have hTPx : T * P * L.sc.x ^ C.T.Cb ≤ P ^ 3 * T ^ 2 * L.sc.x ^ C.T.Cb :=
    mul_le_mul_of_nonneg_right hTP (Real.rpow_nonneg hx0 _)
  refine ⟨?_, ?_, ?_, hW'⟩
  · linarith
  · linarith
  · linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_thinSize_ge : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.Cw ≤ L.sc.w'' D.R.n ∧ L.sc.b ^ C.P.cw ≤ L.sc.w'' D.R.n)) := by
  intro eps he he' C hC
  obtain ⟨x1, h1⟩ := GlobalTheory.scale_poly_comparison eps (5 * |(C.P.Cw : ℝ)|) (1 / 10) he (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 16, fun D L hs hx hV => ?_⟩⟩⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx16 : (16 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hone : (1 : ℝ) ≤ L.sc.x := by linarith
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  obtain ⟨⟨hn1, -⟩, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  rw [hs] at hn1 hk1 hk2
  have h2 : (2 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by norm_num) hx16 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have e : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [e] at h
  have hup : ∀ a b : ℝ, 1 / 4 + a ≤ b → 2 * L.sc.x ^ a ≤ L.sc.x ^ b := fun a b hab => by
    calc 2 * L.sc.x ^ a ≤ L.sc.x ^ ((1 : ℝ) / 4) * L.sc.x ^ a :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
      _ = L.sc.x ^ (1 / 4 + a) := (Real.rpow_add hx0 _ _).symm
      _ ≤ L.sc.x ^ b := Real.rpow_le_rpow_of_exponent_le hone hab
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := hV.ranks.n_le'.trans (hup _ _ (by norm_num))
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := hk2.trans (hup _ _ (by linarith))
  have hn0 : (1 : ℝ) ≤ D.R.n := (Real.one_le_rpow hone (by linarith)).trans hn1
  have hk0 : (1 : ℝ) ≤ D.R.k := (Real.one_le_rpow hone (by linarith)).trans hk1
  obtain ⟨-, -, -, -, -, hw, -⟩ := h1 L.sc hs hx1
  obtain ⟨hw, -, -⟩ := hw D.R.n (by exact_mod_cast hn0) hn3
  have hb1 : (1 : ℝ) ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hA : (1 : ℝ) ≤ L.sc.b ^ ((1 : ℝ) - 1 / 10) := Real.one_le_rpow hb1 (by norm_num)
  have hB : (1 : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := Real.one_le_rpow hone (by positivity)
  have hcw : C.P.cw = 9 / 10 := hC.2.2.2.2.1
  have hkC : (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := by
    calc (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ (D.R.k : ℝ) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow_of_exponent_le hk0 (le_abs_self _)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg _)
      _ = L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := (Real.rpow_mul hx0.le _ _).symm
  refine ⟨?_, ?_⟩
  · refine hkC.trans (le_trans ?_ hw)
    exact le_mul_of_one_le_left (by linarith) hA
  · rw [hcw, show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num]
    exact le_trans (le_mul_of_one_le_right (by linarith) hB) hw

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_cloud_le : SzRow (fun C D L => (4 * L.Sc ≤ L.LaG * L.sc.b' / D.R.k) ∧
    (4 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b') ∧
    (Real.log (D.s.Del : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4) / 2)) := by
  intro eps he he' C hC
  refine ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps (cD + 11) 1 1 0 (by positivity) (by linarith) one_pos
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) cD 1 (1 / 2) 0 le_rfl (by positivity) (by norm_num)
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hCD : 1 ≤ C.P.CDelG := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  refine ⟨max (max x1 x2) (max x3 (128 * C.P.CDelG)), fun D L hε hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hΛ : 1 ≤ L.LaG := by
    rw [hV.La_eq]
    refine le_trans ?_ ((h1 L.sc hε hx1).2.2 C.GK hLa).1
    exact Real.one_le_rpow hx1'.le L.sc.eps_pos.le
  have hp1 : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hx1'.le hcD
  have hDel : (D.s.Del : ℝ) = (⌈L.sc.x ^ cD⌉₊ : ℝ) := by
    rw [hV.Del_eq]; simp [Delv]
  have hD2 : (D.s.Del : ℝ) ≤ 2 * L.sc.x ^ cD := by
    rw [hDel]
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    linarith
  have hD1 : 1 ≤ (D.s.Del : ℝ) := by
    rw [hDel]; exact hp1.trans (Nat.le_ceil _)
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (by positivity) hV.ranks.2.2.1.1
  have hk : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℕ) := by
    refine hV.ranks.2.2.1.2.trans ?_
    have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hε]; push_cast; linarith)
    rw [Real.rpow_natCast] at this
    linarith
  have hb : L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) ≤ L.sc.b' := by
    have h := h2 L.sc.x hx2
    have e1 : L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) = Real.exp ((cD + 11) * Real.log L.sc.x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0, Real.rpow_def_of_pos hx0, mul_comm]; norm_num
    have e2 : L.sc.b' = L.sc.x * Real.exp (L.sc.x ^ eps - L.sc.x ^ (eps / 3)) := by
      simp only [Scale.b', Scale.a, Scale.b, Scale.X', Scale.L, hε, Real.exp_sub]; ring
    rw [e1, e2]
    have h5 : Real.exp ((cD + 11) * Real.log L.sc.x) ≤ Real.exp (L.sc.x ^ eps - L.sc.x ^ (eps / 3)) :=
      Real.exp_le_exp.2 (by simp only [pow_zero, mul_one, one_mul] at h; linarith)
    have h6 := Real.exp_pos (L.sc.x ^ eps - L.sc.x ^ (eps / 3))
    nlinarith
  have key : 16 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b' := by
    have hk2 : (D.R.k : ℝ) ^ 2 ≤ (2 * L.sc.x ^ (5 : ℕ)) ^ 2 := by gcongr
    have hb0 : 0 ≤ L.sc.b' := le_trans (by positivity) hb
    calc 16 * C.P.CDelG * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ)
        ≤ 16 * C.P.CDelG * (2 * L.sc.x ^ (5 : ℕ)) ^ 2 * (2 * L.sc.x ^ cD) := by gcongr
      _ = (128 * C.P.CDelG) * (L.sc.x ^ cD * L.sc.x ^ (10 : ℕ)) := by ring
      _ ≤ L.sc.x * (L.sc.x ^ cD * L.sc.x ^ (10 : ℕ)) := by gcongr
      _ = L.sc.x ^ cD * L.sc.x ^ (11 : ℕ) := by ring
      _ ≤ L.sc.b' := hb
      _ ≤ L.LaG * L.sc.b' := le_mul_of_one_le_left hb0 hΛ
  have hP : 0 ≤ (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hk0, L.Sc_eq]
    nlinarith
  · nlinarith
  · have h := h3 L.sc.x hx3
    simp only [pow_zero, mul_one, Real.rpow_zero] at h
    have h7 : Real.log (D.s.Del : ℝ) ≤ Real.log (2 * L.sc.x ^ cD) := Real.log_le_log (by linarith) hD2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h7
    have h8 := Real.log_two_lt_d9
    rw [hε]
    linarith

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory

theorem boxSum_eq_of_funBdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  intro E _ _ K _ _ P hq ι _ _ f N hf A B hA hB
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  unfold boxSum
  refine weighted_sum_piFinset ι E K
    (fun g => (∀ a, g a ≠ 0 → IntAt P ((qOf P : E) ^ N * a)) ∧
      ∀ a u, IntAt P u → g (a + (qOf P : E) ^ N * u) = g a) _ _ _ _ ?_ f ?_
  · rintro g ⟨h1, h2⟩
    rw [sum_valsQ_of_invariant E P K g N h2 A B hB,
      sum_valsQ_eq_of_support_intAt E P hq K g N h1 A N hA]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  · intro t i
    refine ⟨fun a ha => ?_, fun a u hu => ?_⟩
    · simpa using hf.1 _ ha i
    · have e : Function.update t i (a + (qOf P : E) ^ N * u)
          = Function.update t i a + ((qOf P : E) ^ N) • (Pi.single i u : ι → E) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      simp only [e]
      refine hf.2 _ _ fun j => ?_
      by_cases hj : j = i
      · subst hj; simpa using hu
      · simpa [hj] using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.level_eq_parahoric_category

theorem conj_res {k : Type} [CommRing k] {n c : ℕ} {ρ r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    {γ g : (Fin n → k) ≃ₗ[k] (Fin n → k)} (hγ : ∀ x, ρ (Loc.inX k n c x) = Loc.inX k n c (γ x))
    (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (x : Fin n → k) :
    (ρ⁻¹ * r * ρ) (Loc.inX k n c x) = Loc.inX k n c ((γ⁻¹ * g * γ) x) := by
  show ρ.symm (r (ρ _)) = Loc.inX k n c (γ.symm (g (γ x)))
  rw [hγ, hg, LinearEquiv.symm_apply_eq, hγ, LinearEquiv.apply_symm_apply]

theorem n1Arg_conj_eq {F : Type} [Field F] {n c : ℕ} {ρ r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hρ : ρ ∈ Loc.R1 F n c) (hr : r ∈ Loc.R1 F n c) : Loc.n1Arg (ρ⁻¹ * r * ρ) = Loc.n1Arg r := by
  have h1 := unipotentCharacterArgument_mul_stabilizer hρ.1 (mul_mem (mul_mem (inv_mem hρ) hr) hρ).1
  have h2 := unipotentCharacterArgument_mul_stabilizer hr.1 hρ.1
  have e : ρ * (ρ⁻¹ * r * ρ) = r * ρ := by group
  rw [e, h2] at h1
  linear_combination -h1

end GlobalTheory.Proof.level_eq_parahoric_category
end
