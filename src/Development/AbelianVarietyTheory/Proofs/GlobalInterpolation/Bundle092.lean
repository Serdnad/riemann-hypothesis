module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle050
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle084
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem gap_cube_bound (x t k m r : ℝ) (hx : 4 ≤ x) (ht0 : 0 ≤ t) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r)
    (ht : t ≤ x ^ 401) (hk : k ≤ x ^ 5) (hm : m ≤ x) (hr : r ≤ x ^ 5) :
    t + 2 * (k + m * (t + (r + 6) + 1)) ^ 3 + 1 ≤ x ^ 1210 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have h5 : x ^ 5 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
  have h7 : (7 : ℝ) ≤ x ^ 401 := by
    have : x ^ 2 ≤ x ^ 401 := pow_le_pow_right₀ hx1 (by norm_num)
    nlinarith
  have h402 : x ^ 401 ≤ x ^ 402 := pow_le_pow_right₀ hx1 (by norm_num)
  have hA : k + m * (t + (r + 6) + 1) ≤ x ^ 403 := by
    have h1 : m * (t + (r + 6) + 1) ≤ x * (3 * x ^ 401) :=
      mul_le_mul hm (by linarith) (by positivity) hx0
    have h2 : x * (3 * x ^ 401) = 3 * x ^ 402 := by ring
    have h3 : 4 * x ^ 402 ≤ x * x ^ 402 := mul_le_mul_of_nonneg_right hx (by positivity)
    have h4 : x * x ^ 402 = x ^ 403 := by ring
    linarith
  have hA3 : (k + m * (t + (r + 6) + 1)) ^ 3 ≤ (x ^ 403) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hA 3
  have e1 : (x ^ 403) ^ 3 = x ^ 1209 := by rw [← pow_mul]
  have h9 : x ^ 401 ≤ x ^ 1209 := pow_le_pow_right₀ hx1 (by norm_num)
  have h1 : (1 : ℝ) ≤ x ^ 1209 := one_le_pow₀ hx1
  have h3 : 4 * x ^ 1209 ≤ x * x ^ 1209 := mul_le_mul_of_nonneg_right hx (by positivity)
  have h4 : x * x ^ 1209 = x ^ 1210 := (pow_succ' x 1209).symm
  rw [e1] at hA3
  linarith

theorem szRow_gap_fun_fN : SzRow (fun C D L => ((D.R.t : ℝ) + 2 * ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 + 1 ≤ h0 L) ∧ ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ h0 L)) := by
  intro eps he0 he1 C hC
  have hCN : 1 ≤ C.P.Ch0N := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD _ => ⟨max 1210 (3 + 402 * C.P.Ch0N), fun ch hch => ⟨max x0 4, ?_⟩⟩⟩
  intro D L hε hx hV
  have hx4 : 4 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hxp : 0 < L.sc.x := by linarith
  obtain ⟨hf, hm, hr, hkr, -, -, -, -, -, -, -, -, -, ht, hN, hm1, -⟩ :=
    hx0 L.sc D.R hε (le_trans (le_max_left _ _) hx) hV.ranks
  have hmp : (0 : ℝ) < D.R.m := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hm1
  have hh : L.sc.x ^ ch ≤ h0 L := by
    have e : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0
      rw [hV.eta_eq]
      field_simp
    rw [e]
    unfold h0v
    push_cast
    have h1 := Nat.le_ceil (L.sc.x ^ ch)
    have h2 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by exact_mod_cast ht
    have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by exact_mod_cast hr
    have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
    have h1 := gap_cube_bound L.sc.x D.R.t D.R.k D.R.m D.R.r hx4 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) ht' hk' hm hr'
    have h2 : L.sc.x ^ ((1210 : ℕ) : ℝ) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (by push_cast; exact le_max_left _ _) hch)
    rw [Real.rpow_natCast] at h2
    linarith
  · have h1 : (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ (L.sc.x ^ (402 : ℝ)) ^ C.P.Ch0N :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)
    rw [← Real.rpow_mul hxp.le] at h1
    have h2 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ L.sc.x ^ (3 : ℝ) * L.sc.x ^ (402 * C.P.Ch0N) :=
      mul_le_mul hf h1 (by positivity) (by positivity)
    rw [← Real.rpow_add hxp] at h2
    have h3 : L.sc.x ^ (3 + 402 * C.P.Ch0N) ≤ L.sc.x ^ ch :=
      Real.rpow_le_rpow_of_exponent_le hx1 (le_trans (le_max_right _ _) hch)
    linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem cloudUnit_poly_bounds (x c F K cD k m N f L : ℝ) (hx : 1 ≤ x) (hc : 1 ≤ c) (hcx : c ≤ x) (hF : 1 ≤ F)
    (hK : 1 ≤ K) (hcD : 5 * c + F * c + 406 * K + 412 ≤ cD)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ (5 : ℝ)) (hm0 : 0 ≤ m) (hm : m ≤ x) (hN0 : 0 ≤ N) (hN : N ≤ x ^ (402 : ℝ))
    (hf0 : 0 ≤ f) (hf : f ≤ x ^ (3 : ℝ)) (hL0 : 0 ≤ L) (hL : L ≤ x) :
    (k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ cD ∧ c * m * N ≤ x ^ cD ∧
      k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ cD ∧ N * m ^ 10 ≤ x ^ cD) ∧ (N * f * L) ^ K ≤ x ^ cD := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hFc : 0 ≤ F * c := by positivity
  have mono : ∀ a : ℝ, a ≤ 5 * c + F * c + 406 * K + 412 → x ^ a ≤ x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx (ha.trans hcD)
  have hkc : k ^ c ≤ x ^ (5 * c) := by
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow hk0 hk hc0
  have hnat : ∀ n : ℕ, x ^ n = x ^ (n : ℝ) := fun n => (Real.rpow_natCast x n).symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have h1 : (c * m) ^ 3 ≤ x ^ (6 : ℝ) := by
      calc (c * m) ^ 3 ≤ (x * x) ^ 3 := by gcongr
        _ = x ^ (6 : ℕ) := by ring
        _ = x ^ (6 : ℝ) := by rw [hnat]; norm_num
    have hp : 0 < x ^ (-F) := Real.rpow_pos_of_pos hx0 _
    have h2 : x ^ (-(F * c)) ≤ (6 * x ^ (-F)) ^ c := by
      rw [← neg_mul, Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow hp.le (by linarith) hc0
    have hq : 0 < x ^ (-(F * c)) := Real.rpow_pos_of_pos hx0 _
    calc k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ (5 * c) * x ^ (6 : ℝ) / x ^ (-(F * c)) := by gcongr
      _ = x ^ (5 * c + 6 + F * c) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0]; congr 1; ring
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc c * m * N ≤ x * x * x ^ (402 : ℝ) := by gcongr
      _ = x ^ (2 : ℕ) * x ^ (402 : ℝ) := by ring
      _ = x ^ (404 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ (5 * c) * (x * x ^ 4 * x) ^ 4 := by gcongr
      _ = x ^ (5 * c) * x ^ (24 : ℕ) := by ring
      _ = x ^ (5 * c + 24) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc N * m ^ 10 ≤ x ^ (402 : ℝ) * x ^ 10 := by gcongr
      _ = x ^ (412 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · have h1 : N * f * L ≤ x ^ (406 : ℝ) := by
      calc N * f * L ≤ x ^ (402 : ℝ) * x ^ (3 : ℝ) * x := by gcongr
        _ = x ^ (406 : ℝ) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; norm_num
    calc (N * f * L) ^ K ≤ (x ^ (406 : ℝ)) ^ K := Real.rpow_le_rpow (by positivity) h1 (by linarith)
      _ = x ^ (406 * K) := by rw [← Real.rpow_mul hx0.le]
      _ ≤ x ^ cD := mono _ (by linarith)

theorem szRow_cloudUnit_lower : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * D.R.m) ^ 3 / D.div.etaF ^ C.P.CDel ≤ (D.s.Del : ℝ) ∧ C.P.CDel * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧ (D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * (D.R.m : ℝ) ^ 4 * L.sc.L) ^ 4 ≤ (D.s.Del : ℝ) ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ)) ∧ (((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ (D.s.Del : ℝ))) := by
  intro eps h0 h1 C hC
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, hlast⟩ := hC
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hc : 1 ≤ C.P.CDel := hlast _ (by simp [FC.cLast])
  have hK : 1 ≤ C.P.CCount := hlast _ (by simp [FC.cLast])
  refine ⟨5 * C.P.CDel + C.P.CF * C.P.CDel + 406 * C.P.CCount + 412, fun cD hcD => ⟨0, fun ch _ =>
    ⟨max x0 C.P.CDel, fun D L he hx V => ?_⟩⟩⟩
  have hxc : C.P.CDel ≤ L.sc.x := (le_max_right _ _).trans hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ :=
    hx0 L.sc D.R he ((le_max_left _ _).trans hx) V.ranks
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hDel : L.sc.x ^ cD ≤ (D.s.Del : ℝ) := by
    rw [V.Del_eq, Rat.cast_natCast]
    exact Nat.le_ceil _
  obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := cloudUnit_poly_bounds L.sc.x C.P.CDel C.P.CF C.P.CCount cD D.R.k D.R.m
    (D.R.N D.R.m) D.R.f L.sc.L (hc.trans hxc) hc hxc hF hK hcD (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) hm
    (Nat.cast_nonneg _) hN (Nat.cast_nonneg _) hf (by linarith) hL
  rw [← V.etaF_eq] at a1
  exact ⟨⟨a1.trans hDel, a2.trans hDel, a3.trans hDel, a4.trans hDel⟩, a5.trans hDel⟩

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lowsFar_poly {y n t N l k d : ℝ} (hy : 28 ≤ y) (hn0 : 0 ≤ n) (ht0 : 0 ≤ t) (hN0 : 0 ≤ N) (hl0 : 0 ≤ l)
    (hk0 : 0 ≤ k) (hd0 : 0 ≤ d) (hn : n ≤ y) (ht : t ≤ y) (hN : N ≤ y) (hl : l ≤ y) (hk : k ≤ y) (hd : d ≤ 2 * y) :
    2 * (n * t ^ 2 * (N + t) * l ^ 2 + k * n ^ 2 * (k * (4 * d) + t + l)) + t / 2 + 3 ≤ y ^ 7 := by
  have hy0 : 0 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have h1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ y * y ^ 2 * (y + y) * y ^ 2 := by gcongr
  have h2 : k * n ^ 2 * (k * (4 * d) + t + l) ≤ y * y ^ 2 * (y * (4 * (2 * y)) + y + y) := by gcongr
  have e1 : y * y ^ 2 * (y + y) * y ^ 2 = 2 * y ^ 6 := by ring
  have e2 : y * y ^ 2 * (y * (4 * (2 * y)) + y + y) = 8 * y ^ 5 + 2 * y ^ 4 := by ring
  have p5 : y ^ 5 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p4 : y ^ 4 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p1 : y ^ 1 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p7 : 28 * y ^ 6 ≤ y ^ 7 := by
    calc 28 * y ^ 6 ≤ y * y ^ 6 := by gcongr
      _ = y ^ 7 := by ring
  rw [pow_one] at p1
  linarith

theorem half_le_abs_node_sub_mid (b : ℝ) (i j : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    H ≤ |(b + i * (2 * H)) - (b + j * (2 * H) + 2 * H / 2)| := by
  rcases Nat.lt_or_ge j i with h | h
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by nlinarith))
  · have : (i : ℝ) ≤ j := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by nlinarith))

theorem szRow_lowsFar : SzRow (fun C D L => (∀ τ (i j : Fin D.R.m),
    2 * L.sc.b / lStar L + (D.R.t : ℝ) / 2 + 3 ≤ |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)|)) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨402, fun cD hcD => ⟨cD * 7, fun ch hch => ⟨max x1 28, fun D L he hx V τ i j => ?_⟩⟩⟩
  have hx28 : 28 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  obtain ⟨hf, -, hr, hkr, -, hLx, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ :=
    hx1 L.sc D.R he (le_trans (le_max_left _ _) hx) V.ranks
  have up : ∀ a : ℝ, a ≤ 402 → L.sc.x ^ a ≤ L.sc.x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' (le_trans ha hcD)
  have hxy : L.sc.x ≤ L.sc.x ^ cD := by simpa using up 1 (by norm_num)
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.n : ℝ) ≤ D.R.f := by
      unfold Ranks.f; exact_mod_cast (by omega)
    exact this.trans (hf.trans (up _ (by norm_num)))
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (hr.trans (up _ (by norm_num)))
  have hd : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have key := lowsFar_poly (y := L.sc.x ^ cD) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn
    (ht.trans (up _ (by norm_num))) (hN.trans (up _ (by norm_num))) (hLx.trans hxy) hk hd
  have h7 : (L.sc.x ^ cD) ^ 7 ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hx1' (by simpa using hch)
  obtain ⟨-, -, ⟨b1, hb, -⟩, -⟩ := V.hc
  have hdist := half_le_abs_node_sub_mid (b1 τ : ℝ) i.1 j.1 (⌈L.sc.x ^ ch⌉₊ : ℝ) (Nat.cast_nonneg _)
  have heq : (((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ) =
      ((b1 τ : ℝ) + i.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ))) -
        ((b1 τ : ℝ) + j.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) + 2 * (⌈L.sc.x ^ ch⌉₊ : ℝ) / 2) := by
    rw [(hb τ j).2, (hb τ i).1, (hb τ j).1]
    unfold h0v
    push_cast
    ring
  rw [heq]
  refine le_trans ?_ (key.trans (h7.trans hdist))
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hm : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega)
  have hS : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, V.Del_eq]; push_cast; ring
  unfold lStar
  rw [hS]
  set Λ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * ((D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) + D.R.t + L.sc.L) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ L.sc.L := by linarith
    positivity
  have : 2 * L.sc.b / ((D.R.m : ℝ) * L.sc.b / Λ) ≤ 2 * Λ := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hΛ0 hb0.le]
  linarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_pp_dim_to_le_rpow :
    SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.x ^ L.Ct) ∧
      (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct) ∧ (((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct)) := by
  intro eps h0 h1 C hC
  obtain ⟨xr, hxr⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max xr (max C.T.CP 2), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 : xr ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx2 : C.T.CP ≤ L.sc.x := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hx3 : (2 : ℝ) ≤ L.sc.x := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  have hone : (1 : ℝ) ≤ L.sc.x := by linarith
  have hpos : (0 : ℝ) < L.sc.x := by linarith
  obtain ⟨-, -, -, -, -, -, -, hZ0, hZ, hD, -⟩ := hxr L.sc D.R he hx1 hV.ranks
  have hCt : L.Ct = 401 := hV.Ct_eq.trans hC.1.2.2.2.2.2.2.2.2.2
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  beta_reduce
  rw [hCt, heP]
  refine ⟨?_, hD.trans (Real.rpow_le_rpow_of_exponent_le hone (by norm_num)), ?_⟩
  · have hz0 : 0 ≤ zBase L := le_trans (Real.rpow_nonneg hpos.le _) hZ0
    have hz : zBase L ^ (12 : ℝ) ≤ L.sc.x ^ ((687 : ℝ) / 100 * 12) := by
      rw [Real.rpow_mul hpos.le]
      exact Real.rpow_le_rpow hz0 hZ (by norm_num)
    calc C.T.CP * zBase L ^ (12 : ℝ) ≤ L.sc.x * L.sc.x ^ ((687 : ℝ) / 100 * 12) :=
          mul_le_mul hx2 hz (Real.rpow_nonneg hz0 _) hpos.le
      _ = L.sc.x ^ (1 + (687 : ℝ) / 100 * 12) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ L.sc.x ^ (401 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
  · have h377 : (1 : ℝ) ≤ L.sc.x ^ (377 : ℝ) := Real.one_le_rpow hone (by norm_num)
    have hc : ((TOv L.sc : ℕ) : ℝ) < L.sc.x ^ (377 : ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
    calc ((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x * L.sc.x ^ (377 : ℝ) := by nlinarith
      _ = L.sc.x ^ (1 + 377 : ℝ) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ L.sc.x ^ (401 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by norm_num)

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_eta_bounds : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨401, fun ch hch => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (ch + (1224 : ℕ)) (1 / 2) he0 (by norm_num)
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) (ch + (3 : ℕ)) 0 1 0 le_rfl
    (by positivity) one_pos
  refine ⟨max (max x1 x2) (max x3 2), fun D L hE hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, s3, -, -, s6, -⟩ := h1 L.sc hE hx1
  obtain ⟨rf, rm, rr, rk, -, -, -, -, -, -, -, -, -, rt, -⟩ := h2 L.sc D.R hE hx2 V.ranks
  have h3' := h3 L.sc.x hx3
  have heta := V.eta_eq
  have hpos := L.etaSz_pos
  unfold h0v at heta
  push_cast at heta
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn1' : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn1
  obtain ⟨s7, -⟩ := s6 D.R.n hn1 (by linarith)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have rk' : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast rk) rr
  rw [hE]
  generalize L.sc.x = x at *
  generalize L.sc.b = b at *
  generalize L.sc.X' = X at *
  generalize L.sc.w'' D.R.n = w at *
  generalize L.etaSz = η at *
  generalize (D.R.t : ℝ) = t at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.k : ℝ) = k at *
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hty : t ≤ x ^ ch := rt.trans (Real.rpow_le_rpow_of_exponent_le hx1' hch)
  have e3 : x ^ (ch + (3 : ℕ)) = x ^ ch * x ^ 3 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have eB : x ^ (ch + (1224 : ℕ)) = x ^ ch * x ^ 1224 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have rf' : f ≤ x ^ 3 := by rw [← Real.rpow_natCast]; exact_mod_cast rf
  have rk'' : k ≤ x ^ 5 := by rw [← Real.rpow_natCast]; exact_mod_cast rk'
  have rt' : t ≤ x ^ 401 := by rw [← Real.rpow_natCast]; exact_mod_cast rt
  have hy1 : 1 ≤ x ^ ch := ht1.trans hty
  have hc1 : x ^ ch ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hup : η ≤ x ^ ch * x ^ 3 := by
    rw [heta]
    have a1 : 2 * (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch * x ^ 2 := by
      have : 4 ≤ x ^ 2 := by nlinarith
      nlinarith
    calc m * (2 * (⌈x ^ ch⌉₊ : ℝ)) ≤ x * (x ^ ch * x ^ 2) := by gcongr
      _ = _ := by ring
  have hlo : t ≤ η := by rw [heta]; nlinarith
  have hlog : Real.log η ≤ x ^ (eps / 4) := by
    have a1 : Real.log η ≤ (ch + (3 : ℕ)) * Real.log x := by
      rw [← Real.log_rpow hx0, e3]; exact Real.log_le_log hpos hup
    simp only [zero_mul, add_zero, one_mul] at h3'
    exact a1.trans h3'
  rw [eB] at s3 s7
  generalize x ^ ch = y at *
  have hB0 : 0 ≤ y * x ^ 1224 := by positivity
  have hBb : y * x ^ 1224 ≤ b := by
    have a1 : b ^ (1 / 2 : ℝ) ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
    rw [Real.rpow_one] at a1
    exact (le_mul_of_one_le_right hB0 hX1).trans (s3.trans a1)
  have hBw : y * x ^ 1224 ≤ w :=
    (le_mul_of_one_le_left hB0 (Real.one_le_rpow hb1 (by norm_num))).trans s7
  have hf0 : 0 < f := by linarith
  refine ⟨?_, hlog, hlo, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    calc η * (t ^ 3 * f * k ^ 3) ≤ (y * x ^ 3) * ((x ^ 401) ^ 3 * x ^ 3 * (x ^ 5) ^ 3) := by gcongr
      _ = y * x ^ 1224 := by ring
      _ ≤ b := hBb
  · rw [le_div_iff₀ hx0]
    calc t * η * x ≤ x ^ 401 * (y * x ^ 3) * x := by gcongr
      _ = y * x ^ 405 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw
  · have a1 : t + 1 ≤ x * x ^ 401 :=
      calc t + 1 ≤ t + t := by gcongr
        _ = 2 * t := by ring
        _ ≤ x * x ^ 401 := by gcongr
    calc m * (t + 1) * η ≤ x * (x * x ^ 401) * (y * x ^ 3) := by gcongr
      _ = y * x ^ 406 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

namespace GlobalTheory.KerT

theorem sub_add_le_spread {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    lam.w a - lam.w b + (N : ℤ) ≤ lam.spread := by
  have hN : 0 < N := a.pos
  have h1 : lam.w a ≤ lam.w ⟨0, hN⟩ := lam.anti (Fin.le_def.2 (Nat.zero_le _))
  have h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w b := lam.anti (Fin.le_def.2 (by have := b.2; simp only; omega))
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  linarith

theorem alcoveAt_of_ok : ∀ (Z : Dat), Z.Ok → ∀ (u : Z.Pr.Word) (j : ℕ), j ≤ Z.R.m → AlcoveAt Z.W u j := by
  intro Z hZ u j hj τ a b
  have h1 := hZ.sizes.two_spread_lt u j hj τ
  have h2 := sub_add_le_spread (Z.W.lamTrue u j τ) a b
  linarith

end GlobalTheory.KerT
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem _root_.GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT) (φ : Fn X i) (Φ : M.Pt → M.Val), M.IsExt φ Φ → M.IsExt (Uop X i v φ) (fun p => ∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, Φ p₁) := by
  first | exact @GlobalTheory.LvT.uop_isExt | exact GlobalTheory.LvT.uop_isExt | (intros; apply GlobalTheory.LvT.uop_isExt <;> assumption)
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem _root_.GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → X.fm.seenP w = true → ∀ (V : Finset X.A.vT) (v : X.A.vT), v ∈ V → ∀ p, ∀ y ∈ Co.valB w V p, ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • y ∈ Co.valB w (V.erase v) p := by
  first | exact @GlobalTheory.LvT.pow_smul_mem_valB_erase | exact GlobalTheory.LvT.pow_smul_mem_valB_erase | (intros; apply GlobalTheory.LvT.pow_smul_mem_valB_erase <;> assumption)
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem _root_.GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → ∀ (V : Finset X.A.vT) (p : M.Pt), (0 : M.Val) ∈ Co.valB w V p ∧ (∀ y ∈ Co.valB w V p, ∀ y' ∈ Co.valB w V p, y + y' ∈ Co.valB w V p) ∧ (∀ r ∈ Ow D w, ∀ y ∈ Co.valB w V p, D.what₂.embLL r • y ∈ Co.valB w V p) ∧ ∀ (g : M.G), ∀ y ∈ Co.valB w V p, M.act g y ∈ Co.valB w V (g • p) := by
  first | exact @GlobalTheory.LvT.ValEq.valB_laws | exact GlobalTheory.LvT.ValEq.valB_laws | (intros; apply GlobalTheory.LvT.ValEq.valB_laws <;> assumption)
end
