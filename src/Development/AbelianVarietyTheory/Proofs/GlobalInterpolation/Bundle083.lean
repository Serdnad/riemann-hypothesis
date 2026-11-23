module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle076
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle077
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem window_scale_bounds (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (cD ch : ℝ) :
    ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L →
      2 ≤ L.sc.x ∧ Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 ≤ L.sc.w'' D.R.n ∧
      L.sc.w'' D.R.n ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ L.sc.b := by
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (max ch 0 + 10) (1 / 2) he (by norm_num)
  obtain ⟨CN, x3, h3⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 1 2 (2 * (max 1 C.GK.La * CN ^ 2)) 2 (by norm_num)
  refine ⟨max (max x1 x2) (max (max x3 x4) 2), fun D L hs hx hV => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx2 : x2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx3 : x3 ≤ L.sc.x :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx4 : x4 ≤ L.sc.x :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx5 : 2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  obtain ⟨hf, hm, -⟩ := h1 L.sc D.R hs hx1 hV.ranks
  obtain ⟨-, -, -, hb', -, hw, -⟩ := h2 L.sc hs hx2
  obtain ⟨-, -, hLa⟩ := h3 L.sc hs hx3
  have hLa' := (hLa { C.GK with La := max 1 C.GK.La } (le_max_left _ _)).2
  have h4' := h4 L.sc.x hx4
  clear h1 h2 h3 h4 hLa hx1 hx2 hx3 hx4 hx
  have hetaE := hV.eta_eq
  have hLaE := hV.La_eq
  have hbT := hV.bT_le
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
  obtain ⟨hw1, hw2, -⟩ := hw D.R.n hn1 (by linarith)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hsq : L.sc.b ^ (1 - 1 / 2 : ℝ) = Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hsq1 : 1 ≤ Real.sqrt L.sc.b := Real.one_le_sqrt.2 hb1
  rw [hsq] at hw1
  have hy1 : 1 ≤ L.sc.x ^ (max ch 0) := Real.one_le_rpow hone (le_max_right _ _)
  have hych : L.sc.x ^ ch ≤ L.sc.x ^ (max ch 0) := Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hsplit : L.sc.x ^ (max ch 0 + 10) = L.sc.x ^ (max ch 0) * L.sc.x ^ 10 := by
    rw [Real.rpow_add hx0]; norm_num
  rw [hsplit] at hw1 hb'
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := Real.exp_pos (L.sc.x ^ (L.sc.eps / 3))
    positivity
  have hf3 : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by
    have : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by norm_num
    rw [← this]; exact hf
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
    have := Real.rpow_le_rpow_of_exponent_le hone (show L.sc.eps ≤ 1 by rw [hs]; linarith)
    rwa [Real.rpow_one] at this
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hd1 : L.sc.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hone (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hLa2 : L.LaG ≤ L.sc.x ^ 2 := by
    have ha : 0 ≤ Real.log L.sc.a := by
      apply Real.log_nonneg
      unfold Scale.a
      exact one_le_mul_of_one_le_of_one_le hone hb1
    have e1 : L.LaG ≤ G.La { C.GK with La := max 1 C.GK.La } L.sc := by
      rw [hLaE]
      unfold G.La
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) ha
    have e2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by norm_num
    rw [Real.rpow_one, e2] at h4'
    have e3 : 0 ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 := by
      have : 0 ≤ max 1 C.GK.La := le_trans zero_le_one (le_max_left _ _)
      positivity
    have e4 : max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x) :=
      mul_le_mul_of_nonneg_left (by linarith) e3
    have e5 : G.La { C.GK with La := max 1 C.GK.La } L.sc ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) := hLa'
    linarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hh0 : (h0v L.sc ch : ℝ) ≤ 4 * L.sc.x ^ (max ch 0) := by
    unfold h0v
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ch)
    push_cast
    linarith
  have hh00 : (0 : ℝ) ≤ h0v L.sc ch := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.x * (4 * L.sc.x ^ (max ch 0)) := by
    rw [hetaE]; exact mul_le_mul hm hh0 hh00 hx0.le
  have hterm : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
      L.sc.x ^ 6 * L.sc.b' := by
    have e1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ 3 * 1 * L.sc.x := by
      have e0 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ 3 := hfn ▸ hf3
      exact mul_le_mul (mul_le_mul e0 hd1 hd0 (by positivity)) hxe hxe0 (by positivity)
    have e2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG ≤ L.sc.x ^ 6 := by
      calc _ ≤ 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x ^ 2 :=
            mul_le_mul_of_nonneg_left hLa2 (by positivity)
        _ ≤ L.sc.x ^ 3 * 1 * L.sc.x * L.sc.x ^ 2 := mul_le_mul_of_nonneg_right e1 (by positivity)
        _ = _ := by ring
    rw [div_le_iff₀ (by linarith)]
    calc _ ≤ L.sc.x ^ 6 * L.sc.b' := mul_le_mul_of_nonneg_right e2 hb'0.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hk1
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hone
  clear hych hsplit hh0 hLa' h4' hw
  generalize L.sc.x ^ (max ch 0) = y at hw1 hb' hy1 heta
  have hp4 : (16 : ℝ) ≤ L.sc.x ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hx5 4
    linarith
  have hp6 : L.sc.x ≤ L.sc.x ^ 6 := le_self_pow₀ hone (by norm_num)
  have hp10 : 16 * L.sc.x ^ 6 ≤ L.sc.x ^ 10 := by
    calc _ ≤ L.sc.x ^ 4 * L.sc.x ^ 6 := mul_le_mul_of_nonneg_right hp4 (by positivity)
      _ = _ := by ring
  have hyx : L.sc.x ^ 10 ≤ y * L.sc.x ^ 10 := le_mul_of_one_le_left (by positivity) hy1
  have hyx1 : 1 ≤ y * L.sc.x ^ 10 := by linarith
  have hA : y * (16 * L.sc.x) ≤ y * L.sc.x ^ 10 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : 1 ≤ y * L.sc.x := one_le_mul_of_one_le_of_one_le hy1 hone
  have hC : y * L.sc.x ^ 10 ≤ Real.sqrt L.sc.b * (y * L.sc.x ^ 10) := le_mul_of_one_le_left (by linarith) hsq1
  have hD : L.sc.b' * (L.sc.x ^ 6 + 2) ≤ L.sc.b' * (y * L.sc.x ^ 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hb'0.le
  refine ⟨hx5, le_trans (le_mul_of_one_le_right (by linarith) hyx1) hw1, by linarith, hw2,
    le_trans (le_mul_of_one_le_right hb'0.le hyx1) hb', fun t => ?_⟩
  have := hbT t
  linarith

theorem place_top_or_thick_or_thin (D : D7) (τ : D.what₂.Tau) :
    (∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t) ∨
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces ∨ D.host.IsThin (D.eTau τ : D.R.GG) := by
  by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)

theorem szRow_sizeW_sizeBm_sizeXpp : SzRow (fun _ _ L => SizeW L ∧ SizeBm L ∧ SizeXpp L) := by
  intro eps he he' C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x0, h⟩ := window_scale_bounds eps he he' C cD ch
  refine ⟨x0, fun D L hs hx hV => ?_⟩
  obtain ⟨hx2, hW, heta, hwb, hbb, htop⟩ := h D L hs hx hV
  have heta0 := L.etaSz_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hdiv : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx0.le
  refine ⟨hW, ?_, ?_⟩
  · intro τ hm
    obtain ⟨-, -, ⟨b1, hb, h1, h2, h3⟩, -⟩ := hV.hc
    have hlow : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · rw [h1 τ t ht]
        have e1 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 hdiv
        have e2 := L.bT_ge t
        push_cast
        linarith
      · have e1 := Int.le_ceil L.sc.b
        have e2 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (h2 τ ht).1
        linarith
      · rw [h3 τ ht]; exact Int.le_ceil _
    rw [(hb τ _).1, (hb τ _).1]
    have e1 : ((D.R.m - 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast Nat.sub_le _ _
    have e2 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]; exact mul_le_mul_of_nonneg_right e1 (Nat.cast_nonneg _)
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Nat.cast_zero, zero_mul, add_zero]
    linarith
  · intro j τ j' τ' hj1 hj2 hj1' hj2'
    have hup : wj D j τ ≤ 2 * L.sc.b := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j hj1 hj2 τ t ht).2
        have := htop t
        linarith
      · have := (L.win_thick j hj1 hj2 τ ht).2
        linarith
      · have := (L.win_thin j hj1 hj2 τ ht).2
        linarith
    have hlo : L.sc.w'' D.R.n ≤ wj D j' τ' := by
      rcases place_top_or_thick_or_thin D τ' with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j' hj1' hj2' τ' t ht).1
        have := L.bT_ge t
        linarith
      · have := (L.win_thick j' hj1' hj2' τ' ht).1
        linarith
      · exact (L.win_thin j' hj1' hj2' τ' ht).1
    have hw0 : 0 < L.sc.w'' D.R.n := by linarith
    have hb0 : 0 < L.sc.b := by linarith
    have hX0 : 0 ≤ L.sc.X'' D.R.n := by
      unfold Scale.X'' Scale.a; positivity
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      unfold Scale.X'' Scale.a; exact div_mul_cancel₀ _ hw0.ne'
    calc wj D j τ ≤ 2 * L.sc.b := hup
      _ ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx2 hb0.le
      _ = _ := hXw.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hX0

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem hostBounds_two_mul_rpow_log_sq_le (eps : ℝ) (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 2 * x ^ (eps / 5) * Real.log x ^ 2 ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 4 * eps / 5) (by positivity)).bound
    (c := 1 / 2) (by norm_num)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg h2.le _)] at h1
  have e : x ^ eps = x ^ (eps / 5) * x ^ (4 * eps / 5) := by
    rw [← Real.rpow_add h2]; congr 1; ring
  have hp : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos h2 _
  rw [e]
  nlinarith

theorem hostBounds_log_of_sqrt_exp_lt {a y : ℝ} (h : Real.sqrt (Real.exp a) < y) :
    a / 2 ≤ Real.log y := by
  have h0 : 0 < Real.sqrt (Real.exp a) := Real.sqrt_pos.mpr (Real.exp_pos a)
  have h1 := Real.log_le_log h0 h.le
  rwa [Real.log_sqrt (Real.exp_pos a).le, Real.log_exp] at h1

private theorem hostBounds_rd (R : Ranks) (H : Host R) :
    1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  have hq0 : (1 : ℝ) ≤ H.q := by exact_mod_cast H.hyp.1.one_le
  have hd0 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.hyp.2.1.one_le
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have hqd : (1 : ℝ) ≤ (H.q : ℝ) * H.d := one_le_mul_of_one_le_of_one_le hq0 hd0
  have hs1 : 1 ≤ Real.sqrt ((H.q : ℝ) * H.d) := Real.one_le_sqrt.mpr hqd
  have hs2 : Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.q : ℝ) * H.d := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ (H.q : ℝ) * H.d by positivity)
    nlinarith
  obtain ⟨hrd1, hrd2, -⟩ := factRd R H
  have he0 : (0 : ℝ) ≤ R.e := Nat.cast_nonneg _
  have hB : (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hlo : (1 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨(one_le_mul_of_one_le_of_one_le hlo (Real.one_le_sqrt.mpr hd0)).trans hrd1, hrd2.trans ?_⟩
  have : (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.QS : ℝ) * ((H.q : ℝ) * H.d) :=
    mul_le_mul (by linarith) hs2 (Real.sqrt_nonneg _) hS0.le
  rwa [mul_assoc]

theorem hostBounds_ez {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) : s.eps / C8 ≤ s.ez :=
  div_le_div_of_nonneg_left s.eps_pos.le (lt_of_lt_of_le one_pos s.one_le_J) h.2.2.2.2.2.2.2.2.1

theorem hostBounds_one_le_log_div {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H)
    (hx : Real.exp C8 ≤ s.x) : 1 ≤ Real.log s.x / s.J := by
  rw [one_le_div (lt_of_lt_of_le one_pos s.one_le_J)]
  exact h.2.2.2.2.2.2.2.2.1.trans ((Real.le_log_iff_exp_le (by linarith [s.one_lt_alt])).mpr hx)

private theorem hostBounds_win {s : Scale} {Y : ℝ} (h : PairWin s Y) :
    s.x ^ (s.ez / 5) ≤ Y ^ (s.eps / 5) ∧ Y ^ (s.eps / 5) ≤ s.x ^ (s.eps / 5) ∧
      (Real.log s.x / s.J) ^ 2 ≤ Real.log Y ^ 2 ∧ Real.log Y ^ 2 ≤ Real.log s.x ^ 2 := by
  obtain ⟨h1, h2⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hJ : 0 < s.J := lt_of_lt_of_le one_pos s.one_le_J
  have he := s.eps_pos
  have hp : 0 < s.x ^ (1 / s.J) := Real.rpow_pos_of_pos hx0 _
  have hY : 0 < Y := hp.trans_le h1
  have hl : Real.log s.x / s.J ≤ Real.log Y := by
    have := Real.log_le_log hp h1
    rw [Real.log_rpow hx0] at this
    calc Real.log s.x / s.J = 1 / s.J * Real.log s.x := by ring
      _ ≤ _ := this
  have hl0 : 0 ≤ Real.log s.x / s.J := div_nonneg (Real.log_pos hx1).le hJ.le
  refine ⟨?_, Real.rpow_le_rpow hY.le h2 (by positivity), pow_le_pow_left₀ hl0 hl 2,
    pow_le_pow_left₀ (hl0.trans hl) (Real.log_le_log hY h2) 2⟩
  have e : s.x ^ (s.ez / 5) = (s.x ^ (1 / s.J)) ^ (s.eps / 5) := by
    rw [← Real.rpow_mul hx0.le]; congr 1; unfold Scale.ez; ring
  rw [e]
  exact Real.rpow_le_rpow hp.le h1 (by positivity)

theorem hostBounds : ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C8 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H → s.x ^ (s.ez / 5) / 2 ≤ Real.log H.q ∧ Real.log H.q ≤ s.x ^ (s.eps / 5) ∧ s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 / 2 ≤ Real.log H.d ∧ Real.log H.d ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ 1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ∧ Real.log H.rdE ≤ s.L ∧ Real.log H.pde ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log H.pde' ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  intro eps C8 he _ hC
  obtain ⟨x0, hx0⟩ := hostBounds_two_mul_rpow_log_sq_le eps he
  refine ⟨x0, fun s R H hse hx _ hH => ?_⟩
  subst hse
  obtain ⟨⟨Y, hW, hq, -, hq1, hq2, hd, -, hd1, hd2, -, -, hNY⟩, -, -, ⟨hp, hp'⟩, -⟩ := hH
  obtain ⟨w1, w2, w3, w4⟩ := hostBounds_win hW
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have p1 : 0 < s.x ^ (s.ez / 5) := Real.rpow_pos_of_pos hxp _
  have v1 : s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 :=
    mul_le_mul w1 w3 (sq_nonneg _) (p1.le.trans w1)
  have v2 : Y ^ (s.eps / 5) * Real.log Y ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 :=
    mul_le_mul w2 w4 (sq_nonneg _) (Real.rpow_pos_of_pos hxp _).le
  have hq0 : (0 : ℝ) < H.q := by exact_mod_cast hq.pos
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have lq : Real.log H.q ≤ Y ^ (s.eps / 5) := (Real.log_le_iff_le_exp hq0).mpr hq2
  have ld : Real.log H.d ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 := (Real.log_le_iff_le_exp hd0).mpr hd2
  have lq' : Y ^ (s.eps / 5) / 2 ≤ Real.log H.q := hostBounds_log_of_sqrt_exp_lt hq1
  have ld' : Y ^ (s.eps / 5) * Real.log Y ^ 2 / 2 ≤ Real.log H.d := hostBounds_log_of_sqrt_exp_lt hd1
  have hN : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by linarith
  obtain ⟨hrd1, hrd3⟩ := hostBounds_rd R H
  have hNpos : (0 : ℝ) < (H.QS : ℝ) * H.q * H.d := by positivity
  have hpl : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 →
      Real.log p ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    intro p hpp hle
    have h1 := Real.log_le_log (by exact_mod_cast hpp.pos) hle
    rw [Real.log_rpow hNpos] at h1
    have h2 := mul_le_mul_of_nonneg_left hN (show 0 ≤ C8 by linarith)
    linarith
  exact ⟨by linarith, lq.trans w2, by linarith, ld.trans v2, hN, hrd1, (factRd R H).2.1,
    ((Real.log_le_log (by linarith) hrd3).trans hN).trans (hx0 _ hx),
    hpl _ H.pde_prime hp, hpl _ H.pde'_prime hp'⟩

end GlobalTheory.EX
end

section

noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

theorem mem_valO_of_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L)
    (W : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : ∀ r : 𝓞 K, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom j r ∈ W.asIdeal) (x : K) :
    j x ∈ valO W ↔ x ∈ valO Q := by
  letI : Algebra K L := j.toAlgebra
  haveI : W.asIdeal.LiesOver Q.asIdeal := ⟨Ideal.ext fun r => h r⟩
  rw [mem_valO, mem_valO, show j x = algebraMap K L x from rfl,
    ← HeightOneSpectrum.valuation_liesOver L Q W x]
  exact pow_le_one_iff (Ideal.ramificationIdx_pos_of_isDedekindDomain' W.asIdeal Q.ne_bot).ne'

theorem mem_Ow_iff_valO (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) : x ∈ Ow D w ↔ x ∈ valO (D.plEq w) :=
  D.val_nonneg_iff w x

theorem resChar_mem_plEq (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar', ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

theorem resChar_eq_of_mem_plEq (D : D7) (w : D.what₂.places.Pl) {T : ℕ} (hT : T.Prime)
    (h : (T : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = T := by
  by_contra hne
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (T : 𝓞 D.what₂.LL) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.what₂.places.resChar_prime w) hT).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem_plEq D w)) (Ideal.mul_mem_left _ _ h)

end GlobalTheory.LvT.Inh
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

theorem relIndex_eq_prod_locP (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (M₁ M₂ : Submodule (𝓞 E) W) (h₁ : Full M₁) (h₂ : Full M₂) (hD : Dom S M₁ M₂) :
    M₂.toAddSubgroup.relIndex M₁.toAddSubgroup =
      ∏ P ∈ S, (localization₂ P.asIdeal M₂).toAddSubgroup.relIndex (localization₂ P.asIdeal M₁).toAddSubgroup := by
  classical
  let Q : S → Type := fun P => (localization₂ P.1.asIdeal M₁).toAddSubgroup ⧸
    (localization₂ P.1.asIdeal M₂).toAddSubgroup.addSubgroupOf (localization₂ P.1.asIdeal M₁).toAddSubgroup
  let g : ∀ P : S, M₁.toAddSubgroup →+ Q P := fun P =>
    (QuotientAddGroup.mk' _).comp (AddSubgroup.inclusion (H := M₁.toAddSubgroup) (K := (localization₂ P.1.asIdeal M₁).toAddSubgroup)
      fun x hx => mem_localization_of_mem P.1 hx)
  have hg : ∀ (P : S) (x : M₁.toAddSubgroup) (y : (localization₂ P.1.asIdeal M₁).toAddSubgroup),
      g P x = (QuotientAddGroup.mk y : Q P) ↔ (x : W) - y ∈ localization₂ P.1.asIdeal M₂ := by
    intro P x y
    exact QuotientAddGroup.eq_iff_sub_mem
  let f : M₁.toAddSubgroup →+ ∀ P : S, Q P := AddMonoidHom.pi g
  have hker : f.ker = M₂.toAddSubgroup.addSubgroupOf M₁.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, funext_iff]
    constructor
    · intro h
      refine mem_of_locP fun P => ?_
      by_cases hP : P ∈ S
      · simpa using (hg ⟨P, hP⟩ x 0).1 (h ⟨P, hP⟩)
      · exact hD.2 P hP (mem_localization_of_mem P x.2)
    · intro h P
      exact (hg P x 0).2 (by simpa using mem_localization_of_mem P.1 h)
  have hsurj : Function.Surjective f := by
    intro y
    choose x hx using fun P : S => QuotientAddGroup.mk_surjective (y P)
    choose t ht ht' using fun P : S => (h₁.inf h₂).approx {P.1} (x P : W)
    have htM : ∀ P : S, t P ∈ M₁ := fun P => mem_of_locP fun R => by
      by_cases hR : R = P.1
      · subst hR
        have := (localization₂ P.1.asIdeal M₁).add_mem
          (localization_mono P.1 inf_le_left (ht P P.1 (Finset.mem_singleton_self _))) (x P).2
        simpa using this
      · exact localization_mono R inf_le_left (ht' P R (by simpa using hR))
    refine ⟨∑ P : S, ⟨t P, htM P⟩, funext fun P => ?_⟩
    rw [← hx P]
    refine (hg P _ _).2 ?_
    change M₁.toAddSubgroup.subtype (∑ P : S, ⟨t P, htM P⟩) - (x P : W) ∈ _
    rw [map_sum M₁.toAddSubgroup.subtype, ← Finset.add_sum_erase _ _ (Finset.mem_univ P), add_sub_right_comm]
    refine Submodule.add_mem _ (localization_mono P.1 inf_le_right (ht P P.1 (Finset.mem_singleton_self _)))
      (Submodule.sum_mem _ fun R hR => localization_mono P.1 inf_le_right (ht' R P.1 ?_))
    rw [Finset.mem_singleton]
    exact fun e => (Finset.ne_of_mem_erase hR) (Subtype.ext e.symm)
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top,
    Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl

end GlobalTheory.ThetaMove
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  first | exact @GlobalTheory.boxSum_eq_of_funBdd | exact GlobalTheory.boxSum_eq_of_funBdd | (intros; apply GlobalTheory.boxSum_eq_of_funBdd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), N ≤ D → CharTo P D psi → HomBdd P N Psi → ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), FunBdd P N (integrand psi Psi xj) ∧ ∀ t : Loc.FC n' c' n c → E, Psi (Loc.xx1 xj t) ≠ 0 → IntAt P ((qOf P : E) ^ N * Loc.chArg (Loc.xx1 xj t)) := by
  first | exact @GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | exact GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | (intros; apply GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  first | exact @GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | exact GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | (intros; apply GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd <;> assumption)
end
