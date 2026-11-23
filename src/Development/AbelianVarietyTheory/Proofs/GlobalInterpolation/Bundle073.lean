module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle068
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rank_const_absorb {x : ℝ} (hx : 1 < x) (hK : (1000 : ℝ) ≤ x ^ ((1 : ℝ) / 1000)) {a b C : ℝ}
    (hC : C ≤ 1000) (hab : a + 1 / 1000 ≤ b) : C * x ^ a ≤ x ^ b := by
  have hx0 : 0 < x := by linarith
  calc C * x ^ a ≤ x ^ ((1 : ℝ) / 1000) * x ^ a :=
        mul_le_mul_of_nonneg_right (hC.trans hK) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (a + 1 / 1000) := by rw [Real.rpow_add hx0, mul_comm]
    _ ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab

theorem rank_mul_le {x : ℝ} (hx : 0 < x) {u v a b : ℝ} (hv : 0 ≤ v) (hu : u ≤ x ^ a) (hv' : v ≤ x ^ b) :
    u * v ≤ x ^ (a + b) := by
  rw [Real.rpow_add hx]
  exact mul_le_mul hu hv' hv (Real.rpow_nonneg hx.le _)

theorem rank_basic_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.f : ℝ) ≤ s.x ^ (3 : ℝ) ∧ (R.m : ℝ) ≤ s.x ∧ (R.r : ℝ) ≤ s.x ^ (5 : ℝ) ∧ R.k ≤ R.r ∧ R.r ≤ 2 * R.k ∧ s.L ≤ s.x ∧ 1 ≤ s.L ∧ s.x ^ ((13 : ℝ) / 2) ≤ (R.f : ℝ) * R.r * s.L ∧ (R.f : ℝ) * R.r * s.L ≤ s.x ^ ((687 : ℝ) / 100) ∧ ((R.f * R.r.choose 2 : ℕ) : ℝ) ≤ s.x ^ (12 : ℝ) ∧ (R.k : ℝ) * R.f / R.m ≤ s.x ^ (7 : ℝ) ∧ ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) ∧ s.x ^ (377 : ℝ) ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.N R.m : ℝ) ≤ s.x ^ (402 : ℝ) ∧ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  intro eps he0 he1
  refine ⟨(1000 : ℝ) ^ (1000 : ℝ), fun s R hs hx0 hR => ?_⟩
  have hn2 := RankVal.n_le hR
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, ht⟩ := hR
  have hx := s.one_lt_alt
  have hxp : 0 < s.x := lt_trans one_pos hx
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hK : (1000 : ℝ) ≤ s.x ^ ((1 : ℝ) / 1000) := by
    calc (1000 : ℝ) = ((1000 : ℝ) ^ (1000 : ℝ)) ^ ((1 : ℝ) / 1000) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hx0 (by norm_num)
  clear hx0
  have ab : ∀ {a b C : ℝ}, C ≤ 1000 → a + 1 / 1000 ≤ b → C * s.x ^ a ≤ s.x ^ b :=
    fun hC hab => rank_const_absorb hx hK hC hab
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun h => Real.rpow_le_rpow_of_exponent_le hx.le h
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx.le h
  have hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
    have : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hxp, Real.rpow_one]; rfl
    rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]
    congr 1; ring
  rw [hsq] at hm1 hm2
  have h2m := R.two_le_m
  have hmk := R.m_add_three_le_k
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hrk : R.r ≤ 2 * R.k := by unfold Ranks.r; omega
  have hkr' : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
  have hrk' : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast hrk
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have hf : (R.f : ℝ) ≤ s.x ^ ((2156 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (b := 2156 / 1000) (by norm_num) (by linarith)
    linarith
  have hr : (R.r : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 9 / 2 + 10 * s.eps) (b := 4694 / 1000) (by norm_num) (by linarith)
    linarith
  have hk : (R.k : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := hkr'.trans hr
  have hL : s.L ≤ s.x ^ ((20 : ℝ) / 1000) := mono (by linarith)
  have hL1 : 1 ≤ s.L := one e0.le
  have hmu : (R.m : ℝ) ≤ s.x ^ ((501 : ℝ) / 1000) := by
    have := ab (C := 2) (a := 1 / 2 - s.eps / 16) (b := 501 / 1000) (by norm_num) (by linarith)
    linarith
  have hmp : (0 : ℝ) < R.m := by exact_mod_cast (by omega : 0 < R.m)
  have hmi : (R.m : ℝ)⁻¹ ≤ s.x ^ (-(498 : ℝ) / 1000) := by
    have h1 : s.x ^ ((498 : ℝ) / 1000) ≤ R.m := (mono (by linarith)).trans hm1
    rw [neg_div, Real.rpow_neg hxp.le]
    exact inv_anti₀ (by positivity) h1
  have f0 : (0 : ℝ) ≤ R.f := by positivity
  have r0 : (0 : ℝ) ≤ R.r := by positivity
  have k0 : (0 : ℝ) ≤ R.k := by positivity
  have L0 : (0 : ℝ) ≤ s.L := by linarith
  have mi0 : (0 : ℝ) ≤ (R.m : ℝ)⁻¹ := by positivity
  have k1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : 1 ≤ R.f := by
    have : R.m ≤ R.f := R.m_le_f
    omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hfr := rank_mul_le hxp r0 hf hr

  have hB0 : 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    have : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    positivity
  have hApos : 0 < 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 := by
    have : (0 : ℝ) < R.r := by linarith
    have : (0 : ℝ) < (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by linarith
    positivity
  have hW1 : 1 ≤ nWv R s := by
    have := Nat.ceil_pos.mpr hApos
    unfold nWv; omega
  have hW : ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) := by
    have h1 := (Nat.ceil_lt_add_one hApos.le).le
    have hk' : (R.k : ℝ) - 1 ≤ s.x ^ ((4694 : ℝ) / 1000) := by linarith
    have k0' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have h2 := rank_mul_le hxp mi0 (rank_mul_le hxp L0 (rank_mul_le hxp L0 (rank_mul_le hxp k0'
      (rank_mul_le hxp k0' (rank_mul_le hxp k0' (rank_mul_le hxp f0 hfr hf) hk') hk') hk') hL) hL) hmi
    have h3 := h2.trans (mono (b := 227 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 227 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((227 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 28) (a := 227 / 10) (b := 229 / 10) (by norm_num) (by norm_num)
    have h7 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8
        = (10 * ((R.f : ℝ) * R.r) + 10 * ((R.f : ℝ) * R.r * R.f * ((R.k : ℝ) - 1) * ((R.k : ℝ) - 1)
          * ((R.k : ℝ) - 1) * s.L * s.L * (R.m : ℝ)⁻¹)) / 8 := by
      rw [div_eq_mul_inv ((R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2)]; ring
    unfold nWv
    push_cast
    linarith
  have hT1 : s.x ^ (377 : ℝ) ≤ (TOv s : ℝ) := Nat.le_ceil _
  have hT2 : (TOv s : ℝ) ≤ s.x ^ (378 : ℝ) := by
    have h1 : (TOv s : ℝ) ≤ s.x ^ (377 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h5 : 1 ≤ s.x ^ (377 : ℝ) := one (by norm_num)
    have h6 := ab (C := 2) (a := 377) (b := 378) (by norm_num) (by norm_num)
    linarith
  have ht1 : TOv s ≤ R.t := by
    have h1 : TOv s ≤ TOv s * nWv R s := Nat.le_mul_of_pos_right _ hW1
    have h2 : R.r ≤ 8 * R.f * R.r := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have ht2 : (R.t : ℝ) ≤ s.x ^ (401 : ℝ) := by
    have h1 : R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s := by omega
    have h2 : (R.t : ℝ) ≤ 8 * (R.f * R.r) + 4 + TOv s * nWv R s := by
      have : ((R.t : ℕ) : ℝ) ≤ ((8 * R.f * R.r + 4 + TOv s * nWv R s : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have h3 := (rank_mul_le hxp (by positivity) hT2 hW).trans (mono (b := 4009 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 4009 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((4009 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 13) (a := 4009 / 10) (b := 401) (by norm_num) (by norm_num)
    linarith
  refine ⟨hf.trans (mono (by norm_num)), ?_, hr.trans (mono (by norm_num)), hkr, hrk, ?_, hL1, ?_, ?_, ?_, ?_,
    hW, hT1.trans (by exact_mod_cast ht1), ht2, ?_, hm1, hm2⟩
  · simpa using hmu.trans (mono (b := 1) (by norm_num))
  · simpa using hL.trans (mono (b := 1) (by norm_num))
  · have h1 : s.x ^ (2 : ℝ) ≤ R.f := by
      have := mono (a := 2) (b := 2 + 8 * s.eps) (by linarith)
      have : (0 : ℝ) ≤ R.n := by positivity
      linarith
    have h2 : s.x ^ ((9 : ℝ) / 2) ≤ R.r := by
      have := mono (a := 9 / 2) (b := 9 / 2 + 10 * s.eps) (by linarith)
      linarith
    calc s.x ^ ((13 : ℝ) / 2) = s.x ^ (2 : ℝ) * s.x ^ ((9 : ℝ) / 2) * 1 := by
          rw [← Real.rpow_add hxp]; norm_num
      _ ≤ _ := by gcongr
  · exact (rank_mul_le hxp L0 hfr hL).trans (mono (by norm_num))
  · have h1 : ((R.r.choose 2 : ℕ) : ℝ) ≤ R.r * R.r := by
      have := Nat.choose_le_pow R.r 2
      rw [sq] at this
      exact_mod_cast this
    have h2 := (rank_mul_le hxp r0 hfr hr).trans (mono (b := 12) (by norm_num))
    push_cast
    calc (R.f : ℝ) * (R.r.choose 2 : ℕ) ≤ R.f * (R.r * R.r) := by gcongr
      _ ≤ _ := by rw [← mul_assoc]; exact h2
  · rw [div_eq_mul_inv]
    exact (rank_mul_le hxp mi0 (rank_mul_le hxp f0 hk hf) hmi).trans (mono (by norm_num))
  · have h3 := (rank_mul_le hxp (by positivity) hmu ht2).trans (mono (b := 4016 / 10) (by norm_num))
    have h4 := hk.trans (mono (b := 4016 / 10) (by norm_num))
    have h5 := hmu.trans (mono (b := 4016 / 10) (by norm_num))
    have h6 := ab (C := 3) (a := 4016 / 10) (b := 402) (by norm_num) (by norm_num)
    unfold Ranks.N
    push_cast
    linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nWv_lower (R : Ranks) (s : Scale) :
    10 * R.r * (R.f + R.f * (R.k - 1) ^ 3) ≤ nWv R s := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hm : (0 : ℝ) < R.m := by
    have := R.two_le_m
    exact_mod_cast (by omega : 0 < R.m)
  have hmf : (R.m : ℝ) ≤ R.f := by
    have : R.m ≤ R.f := R.m_le_f
    exact_mod_cast this
  have hL : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le
  have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ R.k := by exact_mod_cast hk
    linarith
  have hL2 : 1 ≤ s.L ^ 2 := one_le_pow₀ hL
  have h1 : (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 ≤
      (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    rw [le_div_iff₀ hm]
    have hA : (0 : ℝ) ≤ (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 := by positivity
    have hf : (0 : ℝ) ≤ R.f := by positivity
    calc (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 * R.m ≤ (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 * R.f :=
          mul_le_mul_of_nonneg_left hmf hA
      _ = (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h2 := Nat.le_ceil (10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8)
  have h3 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3) ≤
      10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : ((10 * R.r * (R.f + R.f * (R.k - 1) ^ 3) : ℕ) : ℝ) ≤ (nWv R s : ℕ) := by
    unfold nWv
    push_cast [Nat.cast_sub hk]
    linarith
  exact_mod_cast h4

theorem nWv_three_lower (R : Ranks) (s : Scale) :
    R.f * R.r * (R.r + 1) ≤ nWv R s ∧ (R.k - 1) * R.f + 2 * R.r ≤ nWv R s ∧
      8 * R.f * R.r + 4 ≤ nWv R s := by
  have h := nWv_lower R s
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hf : 2 ≤ R.f := le_trans h2 R.m_le_f
  have hr : R.r = R.k + R.m - 1 := rfl
  generalize nWv R s = W at h
  generalize R.f = f at *
  generalize R.r = r at *
  obtain ⟨j, hj⟩ : ∃ j, R.k - 1 = j := ⟨_, rfl⟩
  rw [hj] at h ⊢
  have hj1 : 1 ≤ j := by omega
  have hjr : j ≤ r := by omega
  have hrj : r + 1 ≤ 2 * j := by omega
  have hj3 : j ≤ j ^ 3 := Nat.le_self_pow (by norm_num) j
  have hfr : 2 * 2 ≤ f * r := Nat.mul_le_mul hf (by omega)
  have e : 10 * r * (f + f * j ^ 3) = 10 * (f * r) + f * r * (10 * j ^ 3) := by ring
  rw [e] at h
  have a1 : f * r * (r + 1) ≤ f * r * (10 * j ^ 3) := Nat.mul_le_mul_left _ (by omega)
  have a2 : j * f ≤ f * r := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hjr
  have a3 : 2 * r ≤ f * r := Nat.mul_le_mul_right _ hf
  have a4 : 8 * f * r = 8 * (f * r) := by ring
  refine ⟨by omega, by omega, by omega⟩

theorem szRow_nW : SzRow (fun C D L => (nW L C.P.CnW ≤ ((nWv D.R L.sc : ℕ) : ℝ) ∧ ((nWv D.R L.sc : ℕ) : ℝ) < nW L C.P.CnW + 8) ∧ (8 ∣ (nWv D.R L.sc : ℕ)) ∧ (D.R.r + D.R.t = (8 * D.R.f * D.R.r + 4 : ℕ) + (TOv L.sc : ℕ) * (nWv D.R L.sc : ℕ)) ∧ ((TOv L.sc : ℕ) = ⌈L.sc.x ^ C.T.cTO⌉₊) ∧ (Odd (D.R.r + 6 : ℕ)) ∧ (D.R.r + 5 < (D.R.r + 6 : ℕ)) ∧ ((D.R.r + 6 : ℕ) ≤ D.R.r + 7) ∧ (D.R.f * D.R.r * (D.R.r + 1) ≤ (nWv D.R L.sc : ℕ) ∧ (D.R.k - 1) * D.R.f + 2 * D.R.r ≤ (nWv D.R L.sc : ℕ) ∧ (8 * D.R.f * D.R.r + 4 : ℕ) ≤ (nWv D.R L.sc : ℕ))) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩
  have hW : C.P.CnW = 10 := by
    have hF := hC.1
    unfold FC.Fixed at hF
    tauto
  have hT : C.T.cTO = 377 := hC.2.2.2.2.2.2.2.2.2.1
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast this
    linarith
  refine ⟨⟨?_, ?_⟩, Dvd.intro _ rfl, hV.ranks.2.2.2, ?_, ?_, by omega, by omega, nWv_three_lower _ _⟩
  · rw [hW]; unfold nW nWv
    have := Nat.le_ceil (10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8)
    push_cast
    linarith
  · rw [hW]; unfold nW nWv
    have := Nat.ceil_lt_add_one (a := 10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8) (by positivity)
    push_cast
    linarith
  · rw [hT]; rfl
  · obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    exact ⟨a + b + 2, by omega⟩

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nWv_le_zBase_pow_four {D : D7} (L : SizeData₂ D) :
    1 ≤ zBase L ∧ (D.R.f : ℝ) * D.R.m ≤ zBase L ∧ ((nWv D.R L.sc : ℕ) : ℝ) ≤ 28 * zBase L ^ 4 := by
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by omega
    exact_mod_cast this
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  unfold nWv zBase
  push_cast
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.r : ℝ) = r at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.k : ℝ) = k at *
  generalize L.sc.L = l at *
  have hfr : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have hfrZ : f * r ≤ f * r * l := le_mul_of_one_le_right (by positivity) hL
  have hZ : 1 ≤ f * r * l := hfr.trans hfrZ
  refine ⟨hZ, le_trans (by gcongr) hfrZ, ?_⟩
  have hk0 : 0 ≤ k - 1 := by linarith
  have hk3 : (k - 1) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hk0 (by linarith) 3
  have hc := (Nat.ceil_lt_add_one (a := 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m) / 8) (by positivity)).le
  have a1 : f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m ≤ f ^ 2 * r ^ 3 * l ^ 2 := by
    refine (div_le_self (by positivity) hm).trans ?_
    gcongr
  have a2 : 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * l ^ 2 / m) ≤ 10 * r * (f + f ^ 2 * r ^ 3 * l ^ 2) := by gcongr
  have m0 : 1 ≤ (f * r * l) ^ 4 := one_le_pow₀ hZ
  have m1 : f * r * l ≤ (f * r * l) ^ 4 := le_self_pow₀ hZ (by norm_num)
  have m2 : f ^ 2 * r ^ 4 * l ^ 2 ≤ (f * r * l) ^ 4 := by
    have b1 : f ^ 2 ≤ f ^ 4 := pow_le_pow_right₀ hf (by norm_num)
    have b2 : l ^ 2 ≤ l ^ 4 := pow_le_pow_right₀ hL (by norm_num)
    calc f ^ 2 * r ^ 4 * l ^ 2 ≤ f ^ 4 * r ^ 4 * l ^ 4 := by gcongr
      _ = (f * r * l) ^ 4 := by ring
  have e : 10 * r * (f + f ^ 2 * r ^ 3 * l ^ 2) = 10 * (f * r) + 10 * (f ^ 2 * r ^ 4 * l ^ 2) := by ring
  rw [e] at a2
  linarith

theorem szRow_nW_le_PP : SzRow (fun C D L => ((2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP)) ∧ (((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP))) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ _ => ?_⟩⟩⟩
  obtain ⟨hZ, hfm, hn⟩ := nWv_le_zBase_pow_four L
  obtain ⟨-, -, -, -, -, -, -, -, heP, -, -, -, -, hCP, -⟩ := hC
  have e : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP, ← Real.rpow_natCast]; norm_num
  have hP : 1000 * zBase L ^ (12 : ℕ) ≤ C.T.CP * zBase L ^ C.T.eP := by
    rw [e]
    exact mul_le_mul_of_nonneg_right hCP (by positivity)
  have h8 : zBase L ^ 8 ≤ zBase L ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
  have h4 : zBase L ^ 4 ≤ zBase L ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
  have h12 : 0 ≤ zBase L ^ 12 := by positivity
  refine ⟨le_trans ?_ hP, le_trans ?_ hP⟩
  · have ha : 2 * (D.R.f : ℝ) * D.R.m ≤ 2 * zBase L := by linarith
    calc (2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ)
        ≤ (2 * zBase L) ^ 4 * (28 * zBase L ^ 4) := by gcongr
      _ = 448 * zBase L ^ 8 := by ring
      _ ≤ 1000 * zBase L ^ 12 := by linarith
  · linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem m_pow_five_mul_f_mul_L_le (s : Scale) (R : Ranks) (h : RankVal s R) :
    (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
  have hn := h.n_le
  obtain ⟨-, ⟨-, hm⟩, -, -⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have hm2 : (R.m : ℝ) ≤ 2 * s.x ^ (1 / 2 - s.eps / 16) := by
    refine hm.trans (le_of_eq ?_)
    have hd : s.delta1 = s.x ^ (-(s.eps / 8)) := rfl
    rw [hd, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith [s.eps_lt]), ← Real.rpow_mul hx0.le]
    congr 2; ring
  have hm5 : (R.m : ℝ) ^ 5 ≤ 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
    calc (R.m : ℝ) ^ 5 ≤ (2 * s.x ^ (1 / 2 - s.eps / 16)) ^ 5 := by gcongr
      _ = 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
        rw [mul_pow, ← Real.rpow_natCast (s.x ^ (1 / 2 - s.eps / 16)), ← Real.rpow_mul hx0.le]
        congr 1
        · norm_num
        · congr 1; push_cast; ring
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (2 + 8 * s.eps + s.eps / 100) := by
    simp only [Ranks.f]; push_cast; linarith
  have hL : s.L = s.x ^ s.eps := rfl
  have hL0 : 0 ≤ s.x ^ s.eps := by positivity
  calc (R.m : ℝ) ^ 5 * R.f * s.L
      ≤ (32 * s.x ^ (5 / 2 - 5 * s.eps / 16)) * (4 * s.x ^ (2 + 8 * s.eps + s.eps / 100)) * s.x ^ s.eps := by
        rw [hL]; gcongr
    _ = 128 * (s.x ^ (5 / 2 - 5 * s.eps / 16) * s.x ^ (2 + 8 * s.eps + s.eps / 100) * s.x ^ s.eps) := by ring
    _ ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) (by norm_num)

theorem exists_injective_words : ∀ eps CG CF : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ CG → 0 ≤ CF → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → ∃ c : Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ → (Fin (R.k - 2) → Bool), Function.Injective c ∧ 0 < ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ := by
  intro eps CG CF he _ hG hF
  set K : ℝ := 2 * (2 + 256 * CG + CF) + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K ^ (1 / eps), fun s R hs hx hR => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hb := m_pow_five_mul_f_mul_L_le s R hR
  have hk := hR.2.2.1.1
  rw [hs] at hb hk
  have hKx : K ≤ s.x ^ eps := by
    calc K = (K ^ (1 / eps)) ^ eps := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel he.ne', Real.rpow_one]
      _ ≤ s.x ^ eps := by gcongr
  set X : ℝ := s.x ^ (9 / 2 + 9 * eps) with hX
  have hxX : s.x ≤ X := by
    calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hkX : K * X ≤ R.k := by
    refine le_trans ?_ hk
    have : s.x ^ (9 / 2 + 10 * eps) = s.x ^ eps * X := by
      rw [hX, ← Real.rpow_add hx0]; congr 1; ring
    rw [this]; gcongr
  have hk2 : 2 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hlog : Real.log s.x ≤ X := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hA : CG * (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * CG * X := by
    calc CG * (R.m : ℝ) ^ 5 * R.f * s.L = CG * ((R.m : ℝ) ^ 5 * R.f * s.L) := by ring
      _ ≤ CG * (128 * X) := by gcongr
      _ = _ := by ring
  have hFX : Real.log s.x * CF ≤ X * CF := by gcongr
  have hkc : ((R.k - 2 : ℕ) : ℝ) = (R.k : ℝ) - 2 := by rw [Nat.cast_sub hk2]; norm_num
  have hmain : 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF ≤ ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
    calc 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF
        ≤ Real.exp 2 * Real.exp (128 * CG * X) ^ 2 * Real.exp (X * CF) := by
          rw [Real.rpow_def_of_pos hx0]; gcongr
      _ = Real.exp (2 + 256 * CG * X + X * CF) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (((R.k - 2 : ℕ) : ℝ) * Real.log 2) := by
          apply Real.exp_le_exp.2
          have h1 : 2 + 256 * CG * X + X * CF ≤ ((R.k - 2 : ℕ) : ℝ) * (1 / 2) := by
            rw [hkc]; rw [hK] at hkX; nlinarith
          refine h1.trans ?_
          gcongr
      _ = ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]; push_cast; rfl
  have hle := Nat.ceil_le.2 hmain
  have hcard : Fintype.card (Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊) ≤
      Fintype.card (Fin (R.k - 2) → Bool) := by
    simpa using hle
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨c, c.injective, Nat.ceil_pos.2 (by positivity)⟩

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.localChar_eq_heckeChar_localComponent_of_values : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (P : HeightOneSpectrum (𝓞 E)) (ψ : Formalism.L2.Host.HChar E) (cq : K) (t : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → (∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ cq = ((ψ.locK P q : ℂˣ) : ℂ)) → (∀ (x : Eˣ) (y : 𝓞 E) (c : (𝓞 E ⧸ P.asIdeal)ˣ), (x : E) = (y : E) → (c : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal y → σ ((t c : Kˣ) : K) = ((ψ.locK P x : ℂˣ) : ℂ)) → ∀ a : Eˣ, σ (LocE.locChar (Formalism.L2.Col.qOf P) cq t (a : E)) = ((ψ.locK P a : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.LocCharComp.locChar_eq_locK | exact GlobalTheory.LocCharComp.locChar_eq_locK | (intros; apply GlobalTheory.LocCharComp.locChar_eq_locK <;> assumption)
end
