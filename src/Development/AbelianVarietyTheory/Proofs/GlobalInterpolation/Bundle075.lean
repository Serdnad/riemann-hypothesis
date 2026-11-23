module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rankVal_crude (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (h : RankVal s R) :
    (0 < (R.n : ℝ) ∧ (R.n : ℝ) ≤ s.x ^ 4) ∧ (R.m : ℝ) ≤ s.x ^ 2 ∧ (R.k : ℝ) ≤ s.x ^ 6 := by
  have hn1 := h.n_lo
  have hn2 := h.n_le'
  obtain ⟨-, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := h
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  refine ⟨⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hn1, ?_⟩, ?_, ?_⟩
  · have h1 : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; norm_num)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 3 := by positivity
    have h3 : s.x ^ 4 = s.x * s.x ^ 3 := by ring
    nlinarith
  · have h1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have h2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      apply Real.sqrt_le_iff.2
      refine ⟨hx0.le, ?_⟩
      nlinarith
    nlinarith
  · have h1 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 5 := by positivity
    have h3 : s.x ^ 6 = s.x * s.x ^ 5 := by ring
    nlinarith

theorem gap_crude (x C k m t : ℝ) (hx : 2 ≤ x) (hC : C ≤ x) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (ht0 : 0 ≤ t)
    (hm : m ≤ x ^ 2) (hk : k ≤ x ^ 6) (ht : t ≤ x ^ 401) :
    C * k * m ^ 4 + (k + m * (t + 1)) * m ^ 10 < x ^ 430 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have a1 : C * k * m ^ 4 ≤ x * x ^ 6 * (x ^ 2) ^ 4 := by
    have : C * k * m ^ 4 ≤ x * k * m ^ 4 := by gcongr
    refine this.trans ?_
    gcongr
  have a2 : (1 : ℝ) ≤ x ^ 401 := one_le_pow₀ hx1
  have a3 : (k + m * (t + 1)) * m ^ 10 ≤ (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 := by gcongr
  have a4 : x * x ^ 6 * (x ^ 2) ^ 4 = x ^ 15 := by ring
  have a5 : (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 = x ^ 26 + 2 * x ^ 423 := by ring
  have a6 : x ^ 15 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a7 : x ^ 26 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a8 : (2 : ℝ) ^ 7 ≤ x ^ 7 := by gcongr
  have a9 : x ^ 430 = x ^ 7 * x ^ 423 := by ring
  have a10 : 0 < x ^ 423 := by positivity
  have a11 : 2 ^ 7 * x ^ 423 ≤ x ^ 7 * x ^ 423 := by gcongr
  rw [a9]
  rw [a4] at a1
  rw [a5] at a3
  generalize x ^ 423 = y at *
  linarith

theorem base_sizes_ge (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (n : ℕ), s.eps = eps → x0 ≤ s.x →
    0 < (n : ℝ) → (n : ℝ) ≤ s.x ^ 4 → s.x ^ 430 ≤ s.b ∧ s.x ^ 430 ≤ s.b' ∧ s.x ^ 430 ≤ s.w'' n := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps 434 1 1 0 (by positivity)
    (by linarith) one_pos
  refine ⟨x0, fun s n hs hx hn0 hn => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h1 := h0 s.x hx
  rw [← hs] at h1
  simp only [pow_zero, one_mul, mul_one] at h1
  have hX0 : 0 < s.X' := Real.exp_pos _
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have h2 : s.x ^ 434 * s.X' ≤ s.b := by
    have e : s.x ^ 434 = Real.exp (434 * Real.log s.x) := by
      rw [show (434 : ℝ) = ((434 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : s.x ^ 430 ≤ s.x ^ 434 := pow_le_pow_right₀ hx1 (by norm_num)
  have h4 : s.x ^ 434 ≤ s.b / s.X' := (le_div_iff₀ hX0).2 h2
  have h5 : 0 < s.x ^ 434 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact h3.trans ((le_mul_of_one_le_right h5.le hX1).trans h2)
  · have e : s.b' = s.x * (s.b / s.X') := by rw [Scale.b', Scale.a]; ring
    rw [e]
    exact h3.trans (h4.trans (le_mul_of_one_le_left (h5.le.trans h4) hx1))
  · have e : s.w'' n = (s.b / s.X') / n := by
      rw [Scale.w'', Scale.b', Scale.a]; field_simp
    rw [e, le_div_iff₀ hn0]
    refine le_trans ?_ h4
    calc s.x ^ 430 * n ≤ s.x ^ 430 * s.x ^ 4 := by gcongr
      _ = s.x ^ 434 := by ring

theorem szRow_sig_gaps : SzRow (fun C D L => (∀ τ, (∀ (i : ℕ) (h : i + 1 < D.R.k - 1), gapS D C.P.Cgap < (((D.hc τ).v ⟨i, by omega⟩ - (D.hc τ).v ⟨i + 1, h⟩ : ℚ) : ℝ)) ∧ (∀ (hk : 2 ≤ D.R.k) (hm : 0 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ + (D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) ∧ (∀ (j : ℕ) (h : j + 1 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)))) := by
  intro eps he _ C hC
  obtain ⟨x0, hx0⟩ := base_sizes_ge eps he
  refine ⟨430, fun cD hcD => ⟨430, fun ch hch => ⟨max x0 (max 2 C.P.Cgap), fun D L hs hx hV => ?_⟩⟩⟩
  have hxa : x0 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C.P.Cgap ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, hk⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hb', hw⟩ := hx0 L.sc D.R.n hs hxa hn0 hn
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by
    have h1 := L.t_win.2
    rw [hV.Ct_eq, hC.1.2.2.2.2.2.2.2.2.2, show (401 : ℝ) = ((401 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    exact h1
  have hg : gapS D C.P.Cgap < L.sc.x ^ 430 := by
    have := gap_crude L.sc.x C.P.Cgap D.R.k D.R.m D.R.t hx2 hxC (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hm hk ht
    unfold gapS Ranks.N
    push_cast
    exact this
  have hp : 0 < L.sc.x ^ 430 := by positivity
  have hpow : ∀ c : ℝ, 430 ≤ c → L.sc.x ^ 430 ≤ (⌈L.sc.x ^ c⌉₊ : ℝ) := by
    intro c hc
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; exact hc)
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hb1 : ∀ τ, L.sc.x ^ 430 ≤ (b1 τ : ℝ) := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      rw [htop τ ⟨t, htT⟩ hteq.symm]
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg (by linarith) (by linarith))
      push_cast
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h3 := Int.le_ceil L.sc.b
        have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
        linarith
      · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
        exact hw.trans (Int.le_ceil _)
  generalize L.sc.x ^ 430 = y at *
  intro τ
  refine ⟨fun i h => ?_, fun hk2 hm0 => ?_, fun j h => ?_⟩
  · rw [hv, hv]
    have e : D.R.k - 2 - i = (D.R.k - 2 - (i + 1)) + 1 := by omega
    simp only [e]
    have := hpow cD hcD
    unfold Delv
    push_cast
    linarith
  · rw [hv, (hbj τ _).1]
    have := hb1 τ
    simp only [Nat.sub_self]
    push_cast
    linarith
  · rw [(hbj τ _).1, (hbj τ _).1]
    have := hpow ch hch
    unfold h0v
    push_cast
    linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_la_rho_bot : SzRow (fun _ _ L => SizeLa L ∧ SizeRho L ∧ SizeBot L) := by
  intro eps he he' C hC
  have hLa1 : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (eps + eps / 100)
    (2 * C.GK.La * CN ^ 2) 2 (by linarith)
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    ((2 + 8 * eps + eps / 100) + -(eps / 8) + eps + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 32 0 (by linarith)
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
    (eps / 100 + (eps + eps / 100)) (-2 + (9 / 2 + 10 * eps)) 2 1 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max (max (max x1 x2) (max x3 x4)) 1, ?_⟩⟩⟩
  intro D L hε hx hV
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hone⟩ := hx
  have hpos : 0 < L.sc.x := by linarith
  obtain ⟨hlo, hhi⟩ := (h1 L.sc hε hx1).2.2 C.GK hLa1
  rw [← hV.La_eq] at hlo hhi
  have hup : L.LaG ≤ L.sc.x ^ (eps + eps / 100) := by
    have := h2 _ hx2
    rw [hε] at hhi
    calc L.LaG ≤ _ := hhi
      _ = 2 * C.GK.La * CN ^ 2 * L.sc.x ^ eps * Real.log L.sc.x ^ 2 := by ring
      _ ≤ _ := this
  refine ⟨⟨hlo, ?_⟩, ?_, ?_⟩
  · simpa only [szTh, hε] using hup
  · have hn := hV.ranks.n_le
    obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
    have h3' := h3 _ hx3
    have h4' := h4 _ hx4
    simp only [Real.rpow_add hpos, pow_zero, pow_one, mul_one] at h3' h4'
    rw [← Real.rpow_add hpos 2, ← Real.rpow_add hpos (2 + 8 * eps) (eps / 100), ← Real.rpow_add hpos (9 / 2),
      ← Real.rpow_add hpos eps (eps / 100)] at h3'
    rw [← Real.rpow_add hpos (9 / 2), ← Real.rpow_add hpos eps (eps / 100)] at h4'
    have hL0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hpos _).le hlo
    unfold SizeRho szNst szTh Scale.delta1
    rw [hε] at hn hk ⊢
    have hkpos : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hpos _) hk
    have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hone
    rw [← add_div, div_le_iff₀ hkpos]
    have hA : 4 * (2 * (D.R.n : ℝ) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps * L.LaG ≤
        4 * (2 * (2 * L.sc.x ^ (2 + 8 * eps + eps / 100)) * L.sc.x ^ (-(eps / 8))) * L.sc.x ^ eps *
          L.sc.x ^ (eps + eps / 100) := by gcongr
    have hB : L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.LaG ≤
        L.sc.x ^ (eps / 100) * Real.log L.sc.x * L.sc.x ^ (eps + eps / 100) := by gcongr
    have hK : L.sc.x ^ (-2 : ℝ) * L.sc.x ^ (9 / 2 + 10 * eps) ≤ L.sc.x ^ (-2 : ℝ) * D.R.k := by gcongr
    linarith
  · intro t
    have := hV.bT_le t
    unfold szNst
    exact this

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_real_inequality_le_inv_sq {x e n δ k La A c : ℝ} (hx : 1 < x) (hδ : δ ≤ 1)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hn0 : 0 ≤ n) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ A * Real.log x ^ 2 * x ^ e) (hc : 0 ≤ c)
    (h1 : 32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 2 * c * A * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * δ) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have he0 : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnδ : n * δ ≤ 2 * x ^ (2 + 8 * e) := (mul_le_of_le_one_right hn0 hδ).trans hn
  have t1 : 4 * (2 * n * δ) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * δ) * x ^ e * La = 8 * (n * δ) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (A * Real.log x ^ 2 * x ^ e) := by
          gcongr
      _ = (32 * A * x ^ (2 + 10 * e) * Real.log x ^ 2) / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ c * Real.log x * (A * Real.log x ^ 2 * x ^ e) := by gcongr
      _ = (2 * c * A * x ^ e * Real.log x ^ 3) / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k :=
    mul_le_mul_of_nonneg_left hk (Real.rpow_pos_of_pos hx0 _).le
  linarith

theorem szRow_tops_band_bottoms :
    SzRow (fun C D L => ((D.host.TT.card : ℝ) ≤ Nstar L) ∧ (rhoP L C.P.Crho ≤ L.sc.x ^ (-2 : ℝ)) ∧
      (∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k)) := by
  intro eps h0 h1 C hC
  have hLa : 1 ≤ C.GK.La := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hrho : 1 ≤ C.P.Crho := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps) (32 * (2 * C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x3, hx3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps) (2 * C.P.Crho * (2 * C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 (max x2 x3), fun D L he hx V => ⟨?_, ?_, ?_⟩⟩⟩⟩
  · have := V.host.2.1.2
    unfold LevelStarExponents.Nstar
    linarith
  · have hx1' : x1 ≤ L.sc.x := (le_max_left _ _).trans hx
    have hx2' : x2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
    have hx3' : x3 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
    obtain ⟨-, -, hK⟩ := hx1 L.sc he hx1'
    obtain ⟨hlo, hup⟩ := hK C.GK hLa
    have hxp : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
    have a2 := hx2 _ hx2'
    have a3 := hx3 _ hx3'
    rw [← he] at a2 a3
    unfold rhoP LevelStarExponents.Nstar
    rw [V.La_eq]
    have hδ : L.sc.delta1 ≤ L.sc.x ^ (-(L.sc.eps / 100)) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by have := L.sc.eps_pos; linarith)
    have hδ0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hxp.le _
    have hn : (D.R.n : ℝ) * L.sc.delta1 ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
      calc (D.R.n : ℝ) * L.sc.delta1
          ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 100)) :=
            mul_le_mul V.ranks.n_le hδ hδ0 (by positivity)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hxp]; congr 2; ring
    have key := bandWidth_real_inequality_le_inv_sq (A := 2 * C.GK.La * CN ^ 2) (c := C.P.Crho) L.sc.one_lt_alt (le_refl (1 : ℝ))
      hn (mul_nonneg (Nat.cast_nonneg _) hδ0) V.ranks.2.2.1.1 ((Real.rpow_pos_of_pos hxp _).le.trans hlo)
      (hup.trans (le_of_eq (by ring))) (by linarith) a2 a3
    rw [mul_one, ← mul_assoc 2] at key
    exact key
  · exact V.bT_le

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.unfolding_bounded_integral

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n' c' n c : ℕ}

def extZ (c' c : ℕ) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F) :=
  Loc.inX F n c ∘ₗ z ∘ₗ LinearMap.funLeft F F (Fin.castAdd c')

theorem extZ_apply (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (v : Fin (n' + c') → F) :
    extZ c' c z v = Loc.inX F n c (z fun a => v (Fin.castAdd c' a)) := rfl

theorem unfoldingAffineLinearMap_add_eq_add_frM (xj z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) (t : Loc.FC n' c' n c → F) :
    Loc.xx1 (xj + a • z) t = Loc.xx1 xj t + a • extZ c' c z := by
  refine LinearMap.pi_ext' fun s => LinearMap.ext_ring ?_
  funext l
  change Loc.xx1 (xj + a • z) t (Pi.single s 1) l =
    Loc.xx1 xj t (Pi.single s 1) l + a * extZ c' c z (Pi.single s 1) l
  rw [linearMap_unfolding_apply_single, linearMap_unfolding_apply_single, extZ_apply, inX_apply]
  by_cases hs : s.1 < n'
  · have hf : ¬ Loc.IsFree n' n c l.1 s.1 := fun h => by have := h.1; omega
    have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) =
        Pi.single (⟨s.1, hs⟩ : Fin n') 1 := by
      funext b
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    rw [dite_eq_right hf, dite_eq_right hf, dite_eq_left hs, dite_eq_left hs, e]
    split_ifs with hl
    · simp
    · simp
  · have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) = 0 := by
      funext b
      have := b.2
      rw [Pi.single_apply, if_neg]
      · rfl
      · intro h
        apply hs
        rw [← h]
        simp
    rw [e, map_zero, dite_eq_right hs, dite_eq_right hs]
    simp

theorem chArg_add (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) :
    Loc.chArg (x + a • extZ c' c z) = Loc.chArg x := by
  unfold Loc.chArg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul, extZ_apply,
    atN_of_mem_Ufl (inX_mem_Ufl i _), mul_zero, add_zero]

end SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {v : Fin n → E} (hv : IntV P v) : IntV P (Loc.inX E n c v) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hv _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfold_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (N A B : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), HomBdd P N Psi → (∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj ≠ 0 → IntHom P (((qOf P : E) ^ N) • xj)) ∧ ∀ xj z : (Fin n' → E) →ₗ[E] (Fin n → E), IntHom P z → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi (xj + ((qOf P : E) ^ N) • z) = GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj := by
  intro E _ _ K _ P n' c' n c psi N A B Psi hPsi
  refine ⟨fun xj hx => ?_, fun xj z hz => ?_⟩
  · unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1 at hx
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    have h := hPsi.1 _ (left_ne_zero_of_mul ht)
    intro v hv a
    have h2 := h _ (intV_inX (c := c') hv) (Fin.castAdd c a)
    rw [LinearMap.smul_apply, unfoldingAffinePointMap_apply_inclusion, Pi.smul_apply, inX_castAdd] at h2
    exact h2
  · have hy : IntHom P (extZ c' c z) := fun v hv => by
      rw [extZ_apply]
      exact intV_inX (hz _ fun a => hv _)
    unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [unfoldingAffineLinearMap_add_eq_add_frM, chArg_add, hPsi.2 _ _ hy]

end GlobalTheory.Proof.unfolding_bounded_integral
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime

theorem exists_intAt_pow_mul {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    ∃ m : ℕ, IntAt P ((qOf P : E) ^ m * a) := by
  have e : (qOf P : E) = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
  have h1 : P.valuation E (qOf P : E) < 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key : ∃ m : ℕ, P.valuation E ((qOf P : E) ^ m * a) ≤ 1 := by
    rcases eq_or_ne (P.valuation E a) 0 with ha | ha
    · exact ⟨0, by simp [ha]⟩
    have hq : P.valuation E (qOf P : E) ≠ 0 := by
      simpa using GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
    refine ⟨(WithZero.log (P.valuation E a)).toNat, ?_⟩
    rw [map_mul, map_pow]
    rw [← WithZero.exp_log hq, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_log hq, ← WithZero.exp_log ha, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
    set u := WithZero.log (P.valuation E (qOf P : E))
    set w := WithZero.log (P.valuation E a)
    have h2 : w ≤ (w.toNat : ℤ) := Int.self_le_toNat w
    have h3 : (0 : ℤ) ≤ (w.toNat : ℤ) := Int.natCast_nonneg _
    rw [nsmul_eq_mul]
    nlinarith
  obtain ⟨m, h⟩ := key
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer _ h
  exact ⟨m, n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem exists_intAt_family {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ m : ℕ, ∀ m', m ≤ m' → ∀ i, IntAt P ((qOf P : E) ^ m' * f i) := by
  choose g hg using fun i => exists_intAt_pow_mul P (f i)
  exact ⟨Finset.univ.sup g, fun m' hm i =>
    GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono ((Finset.le_sup (Finset.mem_univ i)).trans hm) (hg i)⟩

theorem bounded_denominators : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  intro E _ _ P a b
  refine ⟨fun v => ?_, fun y => ?_⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P v
    exact ⟨m, fun m' h l => hm m' h l⟩
  · obtain ⟨m, hm⟩ := exists_intAt_family P (fun p : Fin a × Fin b => y (Pi.single p.1 1) p.2)
    exact ⟨m, fun m' h => (intHom_iff _).2 fun s l => hm m' h (s, l)⟩

end GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime
end
