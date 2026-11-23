module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle010
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesPairingStabilizerBlockDiagonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle020
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FiveFactors

theorem volU_eq (k : ℕ) : GlobalTheory.FlagMeas.volU k = sphV k * (2 : ℝ) ^ (((k : ℝ) ^ 2 - k) / 2) := by
  unfold GlobalTheory.FlagMeas.volU
  congr 1
  rw [← Real.rpow_natCast, ← Nat.choose_two_right, Nat.cast_choose_two]
  congr 1
  ring

theorem sum_Ioc_half (m n : ℕ) (h : m ≤ n) :
    ∑ M ∈ Finset.Ioc m n, ((M : ℝ) - 1 / 2) = ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) / 2 := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    rw [Finset.sum_Ioc_succ_top h, ih]
    push_cast
    ring

theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem prod_rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (m n : ℕ) (h : m ≤ n) :
    ∏ M ∈ Finset.Ioc m n, rankFac E M =
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (((n : ℝ) ^ 2 - (m : ℝ) ^ 2) / 2)) *
        ∏ M ∈ Finset.Ioc m n, Formalism.HermitianLatticesTheory.lValEta E M := by
  have hv := vInv_pos E
  unfold rankFac
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by positivity), ← Finset.mul_sum,
    sum_Ioc_half m n h]

theorem dimN_eq (n a : ℕ) (j : Fin a → ℕ) (h : 2 * ∑ i, j i ≤ n) :
    (dimN n j : ℝ) = 2 * ((∑ i, j i : ℕ) : ℝ) ^ 2 - ∑ i, (j i : ℝ) ^ 2
      + 2 * ((∑ i, j i : ℕ) : ℝ) * (n - 2 * ((∑ i, j i : ℕ) : ℝ)) := by
  have h1 := (GlobalTheory.dim_unipotent_radical_identities a (fun i => (j i : ℤ)) n).1
  have h2 : (dimN n j : ℤ) = 2 * ((∑ i, j i : ℕ) : ℤ) ^ 2 - ∑ i, (j i : ℤ) ^ 2
      + 2 * ((∑ i, j i : ℕ) : ℤ) * (n - 2 * ((∑ i, j i : ℕ) : ℤ)) := by
    unfold dimN
    push_cast [Nat.cast_sub h, Finset.sum_filter]
    exact h1
  exact_mod_cast h2

theorem cIw_eq (p q a : ℕ) (j : Fin a → ℕ) (hp : ∑ i, j i ≤ p) (hq : ∑ i, j i ≤ q) :
    cIw p q j = (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2) + (((p : ℝ) + q) * ((∑ i, j i : ℕ) : ℝ)
        - ((∑ i, j i : ℕ) : ℝ) ^ 2 - ((∑ i, j i : ℕ) : ℝ) / 2 - ∑ i, (j i : ℝ) ^ 2)) *
      (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hP : (∏ i, GlobalTheory.FlagMeas.volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) =
      (∏ i, sphV (j i)) * (2 : ℝ) ^ (∑ i, (j i : ℝ) ^ 2 - ((∑ i, j i : ℕ) : ℝ) / 2) := by
    simp only [volU_eq, mul_assoc, ← Real.rpow_add h2]
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos h2]
    congr 2
    push_cast
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold cIw
  rw [hP]
  simp only [volU_eq]
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  generalize ((∑ i, j i : ℕ) : ℝ) = J
  generalize ∑ i, (j i : ℝ) ^ 2 = S
  generalize (dimN (p + q) j : ℝ) = D
  have key : (2 : ℝ) ^ (-(D / 2) + (((p : ℝ) + q) * J - J ^ 2 - J / 2 - S)) =
      (2 : ℝ) ^ (-(D / 2)) * (2 : ℝ) ^ (((p : ℝ) ^ 2 - p) / 2) * (2 : ℝ) ^ (((q : ℝ) ^ 2 - q) / 2) /
      ((2 : ℝ) ^ (S - J / 2) * (2 : ℝ) ^ ((((p : ℝ) - J) ^ 2 - (p - J)) / 2) *
        (2 : ℝ) ^ ((((q : ℝ) - J) ^ 2 - (q - J)) / 2)) := by
    simp only [← Real.rpow_add h2, ← Real.rpow_sub h2]
    congr 1
    ring
  rw [key, div_mul_div_comm]
  congr 1 <;> ring

theorem prod_five_factors : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (p q a : ℕ) (j : Fin a → ℕ), ∑ i, j i ≤ q → 2 * q + 2 ≤ p + q → cIw p q j ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2) * (∏ i, 2 ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) / ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac E M = kapBd E p q j := by
  intro E _ _ _ _ p q a j hq hpq
  have hp : ∑ i, j i ≤ p := by omega
  have hn : 2 * ∑ i, j i ≤ p + q := by omega
  have hv := vInv_pos E
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hD := dimN_eq (p + q) a j hn
  have hmid : (∏ i, (2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E *
      Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) =
      (2 : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2) * (dedekindZeta_residue E ^ a *
      Formalism.HermitianLatticesTheory.vInv E ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2) *
        ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l) := by
    have hc : (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2 =
        ((∑ i, Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
    rw [hc, Real.rpow_natCast, Real.rpow_natCast]
    simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hmid, prod_rankFac E _ _ (Nat.sub_le _ _), cIw_eq p q a j hp hq, mul_pow,
    ← Real.rpow_mul_natCast h2.le, Nat.cast_sub hn]
  unfold kapBd
  rw [hD]
  push_cast [-Nat.cast_sum]
  generalize ((∑ i, j i : ℕ) : ℝ) = J
  generalize ∑ i, (j i : ℝ) ^ 2 = S
  generalize (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) ^
    Formalism.HermitianLatticesTheory.fDeg E = R
  generalize (Formalism.HermitianLatticesTheory.fDeg E : ℝ) = f
  generalize Formalism.HermitianLatticesTheory.vInv E = v at hv ⊢
  generalize ((p : ℝ) + q) = n
  rw [Real.mul_rpow h2.le hv.le, Real.mul_rpow h2.le hv.le, ← div_div]
  congr 1
  have k2 : (2 : ℝ) ^ (-(f * (n * J - J ^ 2 + J / 2))) =
      (2 : ℝ) ^ ((-((2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) + (n * J - J ^ 2 - J / 2 - S)) * f) *
      (2 : ℝ) ^ (f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) * (2 : ℝ) ^ (f * S) /
      (2 : ℝ) ^ (f * ((n ^ 2 - (n - 2 * J) ^ 2) / 2)) := by
    simp only [← Real.rpow_add h2, ← Real.rpow_sub h2]
    congr 1
    ring
  have kv : v ^ (-(f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2)) =
      v ^ (f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) * v ^ (f * S) /
      v ^ (f * ((n ^ 2 - (n - 2 * J) ^ 2) / 2)) := by
    simp only [← Real.rpow_add hv, ← Real.rpow_sub hv]
    congr 1
    ring
  rw [k2, kv]
  field_simp

end GlobalTheory.FiveFactors
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.VolArith

theorem volU_two : volU 2 = 8 * Real.pi ^ 3 := by
  unfold volU sphV
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  norm_num
  ring

theorem one_le_fDeg (E : Type) [Field E] [NumberField E] : 1 ≤ Formalism.HermitianLatticesTheory.fDeg E :=
  Fintype.card_pos

theorem one_le_rd (E : Type) [Field E] [NumberField E] : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have h : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero E)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg E)) (by positivity)
  linarith

theorem sum_half (n : ℕ) (hn : 2 ≤ n) :
    ∑ M ∈ Finset.Ioc 2 n, ((M : ℝ) - 1 / 2) = ((n : ℝ) ^ 2 - 4) / 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, ih]
    push_cast
    ring

theorem lVal_le (E : Type) [Field E] [NumberField E] [StarRing E] (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (M : ℕ) (hM : 3 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      Formalism.HermitianLatticesTheory.lValEta E M ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  obtain ⟨-, h0, h1⟩ := Formalism.HermitianLattices.GenusMassVolumes.log_l_value_field_bound E hE M hM
  refine ⟨h0, ?_⟩
  have hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))
    simpa using this
  have hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M :=
    hs.tsum_pos (fun m => by positivity) 0 (by positivity)
  rw [← Real.log_le_log_iff h0 (pow_pos hz _), Real.log_pow]
  exact (le_abs_self _).trans h1

theorem prod_rankFac_le (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ ∏ M ∈ Finset.Ioc 2 n, rankFac E M ∧
    ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) *
        1.4 ^ Formalism.HermitianLatticesTheory.fDeg E := by
  have hr := one_le_rd E
  have hr0 : 0 < 2 * Formalism.HermitianLatticesTheory.vInv E := by linarith
  have hL : ∀ M ∈ Finset.Ioc 2 n, 0 ≤ Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).1.le
  unfold rankFac
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr0, ← Finset.mul_sum, sum_half n hn]
  refine ⟨mul_nonneg (Real.rpow_nonneg hr0.le _) (Finset.prod_nonneg hL), ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0.le _)
  refine (Finset.prod_le_prod₀ hL (fun M hM => (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).2)).trans ?_
  rw [Finset.prod_pow]
  refine pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l) ?_ _
  have e : Finset.Ioc 2 n = Finset.Icc 3 n := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [e]
  exact (GlobalTheory.zetaProd_sphereVolume_bounds.2.1 n).le

theorem volume_bound_arith : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (X : ℝ), 8 ≤ n → 2 ≤ X → 2 * Formalism.HermitianLatticesTheory.vInv E ≤ X → 2 * Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ X ^ 2 → volU 2 ^ Formalism.HermitianLatticesTheory.fDeg E * (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) * (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E)) * ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤ X ^ (n ^ 2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE n X hn hX hrX hfX
  obtain ⟨hP0, hP⟩ := prod_rankFac_le E hE n (by omega)
  have hr := one_le_rd E
  have hf := one_le_fDeg E
  set r := 2 * Formalism.HermitianLatticesTheory.vInv E with hrdef
  set f := Formalism.HermitianLatticesTheory.fDeg E with hfdef
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlog1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hA : 1 + f * Real.log r ≤ X ^ 2 := by nlinarith
  have hA0 : 0 ≤ 1 + f * Real.log r := by positivity
  have hpi : Real.pi ^ 3 ≤ 3.15 ^ 3 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 3
  have hc : 8 * Real.pi ^ 3 * 4 * 1.4 ≤ X ^ 11 := by
    have : (2 : ℝ) ^ 11 ≤ X ^ 11 := pow_le_pow_left₀ (by norm_num) hX 11
    nlinarith
  have hpi0 := Real.pi_pos
  have he0 : 0 ≤ (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2) := mul_nonneg (by linarith) (by nlinarith)
  have h1 : (8 * Real.pi ^ 3 * 4 * 1.4) ^ f ≤ (X ^ 11) ^ f := pow_le_pow_left₀ (by positivity) hc f
  have h2 : r ^ (5 * f) ≤ X ^ (5 * f) := pow_le_pow_left₀ (by linarith) hrX _
  have h3 : (1 + f * Real.log r) ^ (5 * f) ≤ (X ^ 2) ^ (5 * f) := pow_le_pow_left₀ hA0 hA _
  have h4 : r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) ≤ X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) :=
    Real.rpow_le_rpow (by linarith) hrX he0
  have hr0 : 0 < r := by linarith
  rw [volU_two]
  calc (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        ∏ M ∈ Finset.Ioc 2 n, rankFac E M
      ≤ (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        (r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) * 1.4 ^ f) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ = (8 * Real.pi ^ 3 * 4 * 1.4) ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f) *
        r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [mul_pow (8 * Real.pi ^ 3 * 4), mul_pow (8 * Real.pi ^ 3)]
        ring
    _ ≤ (X ^ 11) ^ f * X ^ (5 * f) * (X ^ 2) ^ (5 * f) *
        X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        gcongr
    _ = X ^ (((26 * f : ℕ) : ℝ) + (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [Real.rpow_add hX0, Real.rpow_natCast, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 2
        ring
    _ ≤ X ^ ((n ^ 2 * f : ℕ) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        push_cast
        have : (64 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        nlinarith
    _ = X ^ (n ^ 2 * f) := Real.rpow_natCast _ _

end GlobalTheory.VolArith
end

section

open Matrix

namespace GlobalTheory.Amp.BlockFrame

theorem blockAnti_scaled_pairing : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := by
  intro K _ j r hj w
  obtain ⟨τ, γ, t, ht⟩ := GlobalTheory.HL.BlockStab.exists_monomial (E := K) w.blocks
  rw [w.size] at ht

  have hγN : ∀ a, a < j → γ a < (Finset.range j).sup γ + 1 := fun a ha =>
    Nat.lt_succ_of_le (Finset.le_sup (f := γ) (Finset.mem_range.mpr ha))
  refine ⟨fun a => if (a : ℕ) < j then γ a else (Finset.range j).sup γ + 1, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    dsimp only
    split_ifs with h1 h2 h2
    · exact ((ht a h1).2.2.2 b h2).2.1 hab'
    · exact (hγN a h1).le
    · omega
    · exact le_rfl
  · intro a b hb
    have hb' : ¬ ((b : ℕ) < j) := by omega
    dsimp only
    rw [if_neg hb']
    by_cases ha : (a : ℕ) < j
    · rw [if_pos ha]
      exact ⟨fun h => absurd h (hγN a ha).ne, fun h => absurd h (by omega)⟩
    · rw [if_neg ha]
      exact ⟨fun _ => by omega, fun _ => rfl⟩
  · intro σ sgn ρ hρ
    simp only [Fin.val_castLE, Fin.is_lt, if_true]

    have hent : ∀ a b : Fin j, w.mat b a = if (a : ℕ) = τ b then (t (γ b) : K) else 0 :=
      fun a b => ((ht b b.isLt).2.2.2 a a.isLt).2.2.2
    have key : ∀ a b : Fin j,
        (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * σ (w.mat b a * ((sgn a : ℤ) : K)) ≠ 0 →
          (a : ℕ) = τ b := by
      intro a b h
      by_contra hne
      apply h
      rw [hent a b, if_neg hne, zero_mul, map_zero, mul_zero]
    have hs : ∀ a : Fin j, ‖σ ((sgn a : ℤ) : K)‖ = 1 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]
    have hsK : ∀ a : Fin j, ((sgn a : ℤ) : K) ≠ 0 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]

    have hZ : (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) =
        Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) *
          (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ *
          Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
        Matrix.transpose_apply, Complex.ofReal_mul, map_mul]
      ring
    have hd : ∀ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 := fun a =>
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hρ.ne'))
    unfold GlobalTheory.Amp.BlockAnti
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact ((ht a a.isLt).2.2.2 b b.isLt).2.1 hab
    · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
        show ((Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ).det =
          σ (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).det from
          (RingHom.map_det σ _).symm,
        Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
      have hP : ∏ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun a _ => hd a
      refine mul_ne_zero (mul_ne_zero hP ?_) hP
      exact (map_ne_zero σ).mpr (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => hsK a)
        (GlobalTheory.SgLoc.PtAlg.isUnit_det w).ne_zero)
    · intro a b h
      have e := key a b h
      show γ a = γ b
      rw [e]
      exact (ht b b.isLt).2.2.1
    · intro a b a' b' h1 h2 hγ
      have hγ' : γ a = γ a' := hγ
      have e1 := key a b h1
      have e2 := key a' b' h2
      have hb : (b : ℕ) = τ a := by rw [e1, (ht b b.isLt).2.1]
      have hb' : (b' : ℕ) = τ a' := by rw [e2, (ht b' b'.isLt).2.1]
      have hsum : (a : ℕ) + τ a = a' + τ a' := ((ht a a.isLt).2.2.2 a' a'.isLt).2.2.1 hγ'
      refine ⟨?_, ?_, ?_⟩
      · have hγb : γ b = γ a := by rw [hb]; exact (ht a a.isLt).2.2.1
        have hγb' : γ b' = γ a := by rw [hb', hγ']; exact (ht a' a'.isLt).2.2.1
        have hw1 : w.mat b a = (t (γ a) : K) := by rw [hent a b, if_pos e1, hγb]
        have hw2 : w.mat b' a' = (t (γ a) : K) := by rw [hent a' b', if_pos e2, hγb']
        have ha := a.isLt
        have hb2 := b.isLt
        have ha' := a'.isLt
        have hb2' := b'.isLt
        have hexp : (r - b.val) + (r - a.val) = (r - b'.val) + (r - a'.val) := by omega
        have hc : ((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) =
            (ρ ^ (r - b'.val))⁻¹ * (ρ ^ (r - a'.val))⁻¹ := by
          rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add, hexp]
        simp only [Matrix.of_apply]
        rw [hw1, hw2, hc, norm_mul, norm_mul, map_mul, map_mul, norm_mul, norm_mul, hs a, hs a']
      · intro haa
        subst haa
        exact Fin.ext (hb.trans hb'.symm)
      · intro hlt
        have hlt' : (a : ℕ) < a' := hlt
        exact Fin.lt_def.mpr (by omega)

end GlobalTheory.Amp.BlockFrame
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.AdelicLattice

theorem adelicLattice_selfDual : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  intro I y
  have hsig : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := by
    ext a
    rfl
  have hdual : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ ∀ z ∈ I.L,
      Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J z x ∈
        (algebraMap (𝓞 I.E) I.E).range := by
    rw [hsig]
    exact I.L_dual

  have hgen : Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) =
      (fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E)) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hLf : ∀ u, u ∈ I.Lf ↔ u ∈ Submodule.span (IntAf I.F I.E)
      ((fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) := by
    intro u
    show u ∈ Submodule.span _ _ ↔ _
    rw [hgen]
  constructor
  · intro hy y' hy'
    have hy'' := (hLf y').1 hy'
    unfold hAf
    induction hy using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      exact Formalism.UG.P.csDual_span I.cm.sig I.J I.L (x : Fin I.n → I.E) ((hdual _).1 x.2) y' hy''
    | zero =>
      rw [Formalism.UG.P.csScale_hform_zero_right]
      exact zero_mem _
    | add u v _ _ hu hv =>
      rw [Formalism.UG.P.csScale_hform_add_right]
      exact add_mem hu hv
    | smul c v _ hv =>
      rw [Subring.smul_def, Formalism.UG.P.csScale_hform_smul_right]
      exact mul_mem c.2 hv
  · intro h
    have hmem := GlobalTheory.PointLattice.mem_latS_of_integral (F := I.F) I.cm.sig I.J I.L hdual I.L_span y
      (fun w hw => h w ((hLf w).2 hw))
    exact (hLf y).2 hmem

end GlobalTheory.AdelicLattice
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

theorem _root_.GlobalTheory.T.exists_prime_idempotent_integralAdeles : ∀ (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E)), ∃ ε : IntAf I.F I.E, ε * ε = ε ∧ 1 - ε ∈ extId I w.asIdeal ∧ (∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ε ∈ extId I u.asIdeal) ∧ (∀ z : IntAf I.F I.E, z ∉ extId I w.asIdeal → ∃ t : IntAf I.F I.E, z * t * ε = ε) ∧ (¬ IsConj I w w → (ε : (I.E ⊗[I.F] Af I.F)) * Formalism.UG.sigR I.cm.sig (Af I.F) ε = 0) := by
  first | exact @GlobalTheory.RowLev.exists_prime_idempotent | exact GlobalTheory.RowLev.exists_prime_idempotent | (intros; apply GlobalTheory.RowLev.exists_prime_idempotent <;> assumption)
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.autPointLatticeIntersection_selfDual_properties : ∀ (I : AutInst) (x : I.GA), (∀ y, y ∈ lamX I x ↔ I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf) ∧ (lamX I x).FG ∧ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤ ∧ (∀ y, y ∈ lamX I x ↔ ∀ z ∈ lamX I x, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ ∀ k : I.GA, k.2 ∈ I.Kset → lamX I (x * k) = lamX I x := by
  first | exact @GlobalTheory.PointLattice.lamX_selfDual | exact GlobalTheory.PointLattice.lamX_selfDual | (intros; apply GlobalTheory.PointLattice.lamX_selfDual <;> assumption)
end
