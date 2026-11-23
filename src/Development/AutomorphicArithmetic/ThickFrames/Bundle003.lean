module

public import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SubspaceCounting.Bundle001

@[expose] public section

section

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

private theorem UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_card (c n : ℕ) (T : Finset ℕ) (h0 : 0 ∉ T)
    (h : ∀ a ∈ T, c * a < n) : c * T.card ≤ n := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  have hsub : T ⊆ Finset.Icc 1 (T.max' hne) := by
    intro a ha
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (fun e => h0 (e ▸ ha)), T.le_max' a ha⟩
  have hc : T.card ≤ T.max' hne := by simpa using Finset.card_le_card hsub
  exact (Nat.mul_le_mul_left c hc).trans (h _ (T.max'_mem hne)).le

private theorem UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_large (A B t : ℝ) (ht : 0 < t) :
    ∃ y0 : ℝ, ∀ y, y0 ≤ y → 2 ≤ y ∧ A + Real.log y ≤ t * y ∧ B ≤ t * y := by
  refine ⟨max 2 (max ((A - Real.log (t / 2)) / (t / 2)) (B / t)), fun y hy => ?_⟩
  have h2 : 2 ≤ y := (le_max_left _ _).trans hy
  have h3 : (A - Real.log (t / 2)) / (t / 2) ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have h4 : B / t ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  rw [div_le_iff₀ (by positivity)] at h3 h4
  have h5 := Real.log_le_sub_one_of_pos (show 0 < t / 2 * y by positivity)
  rw [Real.log_mul (by positivity) (by positivity)] at h5
  exact ⟨h2, by linarith, by linarith⟩

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2 :
    ∃ CT : ℝ, 0 < CT ∧ ∀ eps Co CL : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (φ : Formalism.HC.Frame) (Lw : ℕ), 2 ≤ Lw →
      (Lw : ℝ) ≤ CL * Real.log x → (φ.o : ℝ) ≤ Co → x ^ hE eps / 2 ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ Co * x ^ hE eps →
      ∃ T2 : Finset ℕ, (∀ s ∈ T2, 4 * Lw * s < φ.n0) ∧ Formalism.FrobeniusOrbits.NoRel T2 Lw ∧
        (φ.n0 : ℝ) * Real.exp (-(CT * Real.sqrt (Real.log (φ.n0 : ℝ) * Real.log Lw))) / Lw ≤ T2.card ∧
        x ^ (-eps) * φ.ord ≤ (T2.card : ℝ) ∧ 4 * Lw * T2.card ≤ φ.n0 := by
  have amgm : ∀ p q : ℝ, p * q ≤ ((p + q) / 2) ^ 2 := fun p q => by
    nlinarith [sq_nonneg (p - q)]
  obtain ⟨C, hC, hT⟩ := Formalism.FrobeniusOrbits.hostThickExists
  refine ⟨2 * C, by positivity, ?_⟩
  intro eps Co CL he he'
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + 3 * C ^ 2 / (2 * eps) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = eps / (2 * K) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [htd]; positivity
  obtain ⟨y0, hy0⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_large
    ((Real.log (4 * Co) + eps / 6 * Real.log Co + K * Real.log CL) / K)
    (t * (Real.log (2 * Co) + Real.log 2 / C ^ 2) / 2) t htpos
  refine ⟨Real.exp y0, fun x hx φ Lw hLw hLwx hoC hord1 hord2 => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  obtain ⟨h2y, hA, hB⟩ := hy0 (Real.log x) (by
    calc y0 = Real.log (Real.exp y0) := (Real.log_exp y0).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hx)
  have hypos : 0 < Real.log x := by linarith
  have hx2 : 2 ≤ x := by
    have h1 : Real.exp 2 ≤ x := by
      calc Real.exp 2 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h2y
        _ = x := Real.exp_log hxpos
    have h2 : (2:ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    linarith
  have hx1 : 1 ≤ x := by linarith
  have hn0pos : (0:ℝ) < φ.n0 := by exact_mod_cast φ.n0_pos
  have hn01 : (1:ℝ) ≤ φ.n0 := by exact_mod_cast φ.n0_pos
  have hopos : (0:ℝ) < φ.o := by exact_mod_cast φ.o_pos
  have hordeq : (φ.ord : ℝ) = (φ.o : ℝ) * φ.n0 := by exact_mod_cast φ.exponent_eq_index_mul_cyclic_order
  have hn0ord : (φ.n0 : ℝ) ≤ φ.ord := by exact_mod_cast φ.cyclic_order_le_exponent
  have hCo : 0 < Co := lt_of_lt_of_le hopos hoC
  have hordCo : (φ.ord : ℝ) ≤ Co * φ.n0 := by
    rw [hordeq]; exact mul_le_mul_of_nonneg_right hoC hn0pos.le
  have hxE : 0 < x ^ hE eps := Real.rpow_pos_of_pos hxpos _
  have hEval : hE eps = 2 + 8 * eps := rfl
  have hLw2 : (2:ℝ) ≤ Lw := by exact_mod_cast hLw
  have hLwpos : (0:ℝ) < Lw := by linarith
  have hCL : 0 < CL := by
    by_contra hneg
    push_neg at hneg
    have := mul_le_mul_of_nonneg_right hneg hypos.le
    linarith
  have hb : Real.log Lw ≤ Real.log CL + Real.log (Real.log x) := by
    rw [← Real.log_mul hCL.ne' hypos.ne']
    exact Real.log_le_log hLwpos hLwx
  have hb0 : Real.log 2 ≤ Real.log Lw := Real.log_le_log (by norm_num) hLw2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ Real.log φ.n0 := Real.log_nonneg hn01
  have hepsx : eps * Real.log x ≤ 1 / 52 * Real.log x := mul_le_mul_of_nonneg_right he'.le hypos.le
  have hepsx0 : 0 ≤ eps * Real.log x := mul_nonneg he.le hypos.le
  have ha : Real.log φ.n0 ≤ Real.log Co + 3 * Real.log x := by
    have h1 : Real.log φ.n0 ≤ Real.log (Co * x ^ hE eps) :=
      Real.log_le_log hn0pos (le_trans hn0ord hord2)
    rw [Real.log_mul hCo.ne' hxE.ne', Real.log_rpow hxpos, hEval] at h1
    linarith
  have hlow : (Real.log (2 * Co) + Real.log 2 / C ^ 2) / 2 ≤ Real.log x := by
    have : t * ((Real.log (2 * Co) + Real.log 2 / C ^ 2) / 2) ≤ t * Real.log x := by
      linarith
    exact le_of_mul_le_mul_left this htpos
  have ha_low : Real.log 2 / C ^ 2 ≤ Real.log φ.n0 := by
    have h1 : x ^ hE eps / (2 * Co) ≤ φ.n0 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div hxE.ne' (by positivity), Real.log_rpow hxpos, hEval] at h2
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.sqrt (Real.log φ.n0 * Real.log Lw) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = eps / (3 * C) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hu_up : u ≤ (δ * Real.log φ.n0 + Real.log Lw / δ) / 2 := by
    have key : Real.log φ.n0 * Real.log Lw
        = (δ * Real.log φ.n0) * (Real.log Lw / δ) := by
      field_simp
    have hsq : Real.log φ.n0 * Real.log Lw ≤ ((δ * Real.log φ.n0 + Real.log Lw / δ) / 2) ^ 2 := by
      rw [key]; exact amgm _ _
    have h3 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity)] at h3
    rw [hu]; exact h3
  have hu_low : Real.log 2 / C ≤ u := by
    have hsq : (Real.log 2 / C) ^ 2 ≤ Real.log φ.n0 * Real.log Lw := by
      have e : (Real.log 2 / C) ^ 2 = (Real.log 2 / C ^ 2) * Real.log 2 := by
        field_simp
      rw [e]
      exact mul_le_mul ha_low hb0 hlog2.le ha0
    have h3 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity)] at h3
    rw [hu]; exact h3
  have hCu_eq : C * ((δ * Real.log φ.n0 + Real.log Lw / δ) / 2)
      = eps / 6 * Real.log φ.n0 + (K - 1) * Real.log Lw := by
    rw [hδ, hK]; field_simp; ring
  have hCu : C * u ≤ eps / 6 * Real.log φ.n0 + (K - 1) * Real.log Lw := by
    rw [← hCu_eq]; exact mul_le_mul_of_nonneg_left hu_up hC.le
  have hKt : K * t = eps / 2 := by rw [htd]; field_simp
  have hKt' : K * (t * Real.log x) = eps / 2 * Real.log x := by rw [← mul_assoc, hKt]
  have hKA : K * ((Real.log (4 * Co) + eps / 6 * Real.log Co + K * Real.log CL) / K)
      = Real.log (4 * Co) + eps / 6 * Real.log Co + K * Real.log CL := by
    field_simp
  have hA' := mul_le_mul_of_nonneg_left hA hKpos.le
  have hKb := mul_le_mul_of_nonneg_left hb hKpos.le
  have hea := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ eps / 6)
  have hgoal : Real.log (4 * Co) + Real.log Lw + C * u ≤ eps * Real.log x := by
    rw [mul_add] at hA' hKb hea
    linarith
  obtain ⟨E, hE'⟩ : ∃ E : ℝ, E = Real.exp (C * u) := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE']; exact Real.exp_pos _
  have hexp : 4 * Co * Lw * E ≤ x ^ eps := by
    rw [Real.rpow_def_of_pos hxpos]
    have e : 4 * Co * Lw * E = Real.exp (Real.log (4 * Co) + Real.log Lw + C * u) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_log hLwpos, hE']
    rw [e]
    apply Real.exp_le_exp.mpr
    linarith [mul_comm eps (Real.log x)]
  have hE2 : 2 ≤ E := by
    have h1 : Real.log 2 ≤ C * u := by
      have h3 := mul_le_mul_of_nonneg_left hu_low hC.le
      rw [mul_div_cancel₀ _ hC.ne'] at h3
      exact h3
    rw [hE']
    calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (C * u) := Real.exp_le_exp.mpr h1
  have hP : 0 < x ^ eps := Real.rpow_pos_of_pos hxpos _
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = φ.n0 * E⁻¹ / Lw := ⟨_, rfl⟩
  have hX : x ^ (-eps) * φ.ord ≤ Q / 4 := by
    rw [Real.rpow_neg hxpos.le, hQ]
    rw [show (x ^ eps)⁻¹ * (φ.ord : ℝ) = φ.ord / x ^ eps by ring,
      show (φ.n0 : ℝ) * E⁻¹ / Lw / 4 = φ.n0 / (4 * Lw * E) by field_simp]
    rw [div_le_div_iff₀ hP (by positivity)]
    calc (φ.ord : ℝ) * (4 * Lw * E) ≤ (Co * φ.n0) * (4 * Lw * E) := by gcongr
      _ = φ.n0 * (4 * Co * Lw * E) := by ring
      _ ≤ φ.n0 * x ^ eps := by gcongr
  have hX1 : 1 ≤ x ^ (-eps) * φ.ord := by
    have h1 : x ^ (1:ℝ) ≤ x ^ (-eps + hE eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hEval]; linarith)
    rw [Real.rpow_add hxpos, Real.rpow_one] at h1
    have h2 := mul_le_mul_of_nonneg_left hord1 (Real.rpow_pos_of_pos hxpos (-eps)).le
    linarith
  obtain ⟨T, hTs, hTnr, hTc⟩ := hT φ.n0 Lw hLw
  rw [← hu] at hTc
  have hTc' : Q ≤ T.card := by
    rw [hQ, hE', ← Real.exp_neg, ← neg_mul]
    exact hTc
  have hcardN : T.card ≤ (T.erase 0).card + 1 := by
    have := Finset.pred_card_le_card_erase (s := T) (a := 0)
    omega
  have hcard : (T.card : ℝ) ≤ (T.erase 0).card + 1 := by exact_mod_cast hcardN
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  refine ⟨T.erase 0, fun s hs => hTs s (Finset.mem_of_mem_erase hs), ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FrobeniusOrbits.NoRel at hTnr ⊢
    intro s1 h1 s2 h2 s3 h3
    exact hTnr s1 (Finset.mem_of_mem_erase h1) s2 (Finset.mem_of_mem_erase h2) s3
      (Finset.mem_of_mem_erase h3)
  · have e : (φ.n0 : ℝ) * Real.exp (-(2 * C * Real.sqrt (Real.log φ.n0 * Real.log Lw))) / Lw
        = Q * E⁻¹ := by
      rw [hQ, hE', ← hu, ← Real.exp_neg, show -(2 * C * u) = -(C * u) + -(C * u) by ring,
        Real.exp_add]
      ring
    rw [e]
    have hEinv : E⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hE2
    have h3 := mul_le_mul_of_nonneg_left hEinv hQ0
    linarith
  · linarith
  · exact UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2_card (4 * Lw) φ.n0 (T.erase 0) (Finset.notMem_erase 0 T)
      (fun s hs => hTs s (Finset.mem_of_mem_erase hs))
end

section

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.markedLow_bounds :
    ∀ (δ : ℝ) (r : ℕ), 0 < δ → δ ≤ 1 / 100 →
      (1 / 10 : ℝ) ^ (6 * r + 1) ≤ markedLow δ r (Formalism.MainNotions.G.goodU δ) ∧ markedLow δ r (Formalism.MainNotions.G.goodU δ) ≤ 1 := by
  intro δ r hδ hδ1
  unfold markedLow Formalism.MainNotions.G.goodU
  set u := ⌈1 / δ⌉₊ with hu
  have hu1 : 1 / δ ≤ (u : ℝ) := Nat.le_ceil _
  have hu2 : (u : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have huδ1 : 1 ≤ (u : ℝ) * δ := by
    have h := mul_le_mul_of_nonneg_right hu1 hδ.le
    rwa [one_div, inv_mul_cancel₀ hδ.ne'] at h
  have huδ2 : (u : ℝ) * δ ≤ 1 + δ := by
    have h := mul_le_mul_of_nonneg_right hu2.le hδ.le
    rwa [add_mul, one_div, inv_mul_cancel₀ hδ.ne', one_mul] at h
  have h1δ : 0 < 1 - δ := by linarith
  have hlog : -(δ / (1 - δ)) ≤ Real.log (1 - δ) := by
    have h := Real.one_sub_inv_le_log_of_pos h1δ
    have e : 1 - (1 - δ)⁻¹ = -(δ / (1 - δ)) := by
      field_simp
      ring
    rw [e] at h
    exact h
  have hexp : (1 - δ) ^ u = Real.exp (u * Real.log (1 - δ)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos h1δ u)]
  have hq : (u : ℝ) * δ / (1 - δ) ≤ 103 / 100 := by
    rw [div_le_iff₀ h1δ]
    nlinarith
  have hA : 3 / 10 ≤ (1 - δ) ^ u := by
    rw [hexp]
    have step : -(103 / 100 : ℝ) ≤ u * Real.log (1 - δ) := by
      have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
      have e2 : (u : ℝ) * (-(δ / (1 - δ))) = -((u : ℝ) * δ / (1 - δ)) := by ring
      linarith
    have hE : Real.exp (103 / 100) ≤ 10 / 3 := by
      have e3 : Real.exp (103 / 100) = Real.exp 1 * Real.exp (3 / 100) := by
        rw [← Real.exp_add]
        norm_num
      have h3 := Real.abs_exp_sub_one_sub_id_le (x := (3 / 100 : ℝ)) (by norm_num)
      have h4 : Real.exp (3 / 100) ≤ 1 + 3 / 100 + (3 / 100) ^ 2 := by
        have := (abs_le.mp h3).2
        linarith
      have h5 := Real.exp_one_lt_d9
      have h6 : 0 ≤ Real.exp (3 / 100) := (Real.exp_pos _).le
      have h7 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
      rw [e3]
      nlinarith
    have hmono : Real.exp (-(103 / 100)) ≤ Real.exp (u * Real.log (1 - δ)) := Real.exp_le_exp.mpr step
    rw [Real.exp_neg] at hmono
    have hpos := Real.exp_pos (103 / 100 : ℝ)
    have hinv : 3 / 10 ≤ (Real.exp (103 / 100))⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hpos]
      norm_num
      linarith
    linarith
  have hqge : (u : ℝ) - 1 ≤ 2 * ((u / 2 : ℕ) : ℝ) := by
    have h : u ≤ 2 * (u / 2) + 1 := by omega
    have h' : (u : ℝ) ≤ 2 * ((u / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hqle : 2 * ((u / 2 : ℕ) : ℝ) ≤ u := by
    have h : 2 * (u / 2) ≤ u := Nat.mul_div_le u 2
    exact_mod_cast h
  have hP : (1 - δ) ^ u ≤ (1 - δ) ^ (u - 1) :=
    pow_le_pow_of_le_one h1δ.le (by linarith) (Nat.sub_le u 1)
  have hP1 : (1 - δ) ^ (u - 1) ≤ 1 := pow_le_one₀ h1δ.le (by linarith)
  have hP0 : 0 ≤ (1 - δ) ^ (u - 1) := pow_nonneg h1δ.le _
  have hq0 : (0 : ℝ) ≤ ((u / 2 : ℕ) : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
  have hqδ : 99 / 200 ≤ ((u / 2 : ℕ) : ℝ) * δ := by nlinarith
  have hqδ2 : ((u / 2 : ℕ) : ℝ) * δ ≤ 1 := by nlinarith
  have eB : ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) =
      3 / 4 * ((((u / 2 : ℕ) : ℝ) * δ) * (1 - δ) ^ (u - 1)) := by ring
  have hB : 1 / 10 ≤ ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) := by
    rw [eB]
    have h := mul_le_mul hqδ (le_trans hA hP) (by norm_num) hq0
    linarith
  have hB1 : ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) ≤ 1 := by
    rw [eB]
    have h := mul_le_mul hqδ2 hP1 hP0 (by norm_num)
    linarith
  have hB0 : 0 ≤ ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) := by linarith
  have hA0 : 0 ≤ (1 - δ) ^ u := pow_nonneg h1δ.le _
  constructor
  · calc (1 / 10 : ℝ) ^ (6 * r + 1) = (1 / 10 : ℝ) ^ (3 * r + 1) * (1 / 10 : ℝ) ^ (3 * r) := by
          rw [← pow_add]
          congr 1
          ring
      _ ≤ ((1 - δ) ^ u) ^ (3 * r + 1) * (((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1)) ^ (3 * r) :=
          mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith) _) (pow_le_pow_left₀ (by norm_num) hB _)
            (by positivity) (pow_nonneg hA0 _)
  · exact mul_le_one₀ (pow_le_one₀ hA0 (pow_le_one₀ h1δ.le (by linarith))) (pow_nonneg hB0 _)
      (pow_le_one₀ hB0 hB1)
end
