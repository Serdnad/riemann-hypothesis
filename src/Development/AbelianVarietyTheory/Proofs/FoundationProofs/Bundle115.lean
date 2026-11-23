module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.HahnSeries.Summable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle108
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hahnSeries_inv_converges : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → Den h⁻¹ ∧ ∃ C' : ℝ, HS ε C' φ⁻¹ h⁻¹ := by
  intro Ω _ ε C φ h hD hne hS
  obtain ⟨N, n₀, a, hN, ha0, hcoef, hzero⟩ := GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD hne
  obtain ⟨Φ, hΦ1, hΦ0⟩ := GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q Ω N hN
  set p : PowerSeries Ω := PowerSeries.mk a with hpdef
  have hp0 : PowerSeries.constantCoeff p ≠ 0 := by simpa [p] using ha0
  set q : PowerSeries Ω := p⁻¹ with hqdef
  have hdiv : ∀ (r : ℚ) (m : ℤ) (k : ℕ), r - (m : ℚ) / N = (k : ℚ) / N ↔ r = ((m + k : ℤ) : ℚ) / N := by
    intro r m k
    rw [sub_eq_iff_eq_add]
    push_cast
    constructor <;> intro hr <;> rw [hr] <;> ring
  have hh : h = HahnSeries.single ((n₀ : ℚ) / N) (1 : Ω) * Φ p := by
    ext r
    rw [HahnSeries.coeff_single_mul, one_mul]
    by_cases hr : ∃ k : ℕ, r = ((n₀ + k : ℤ) : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hcoef k, (hdiv _ n₀ k).2 rfl, hΦ1]
      simp [p]
    · push_neg at hr
      rw [hzero r hr, hΦ0]
      intro k hk
      exact hr k ((hdiv r n₀ k).1 hk)
  set g : HahnSeries ℚ Ω := HahnSeries.single (((-n₀ : ℤ) : ℚ) / N) (1 : Ω) * Φ q with hgdef
  have hg : h⁻¹ = g := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hh, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, hqdef,
      PowerSeries.mul_inv_cancel _ hp0, map_one, mul_one, mul_one]
    have : (n₀ : ℚ) / N + ((-n₀ : ℤ) : ℚ) / N = 0 := by push_cast; ring
    rw [this, HahnSeries.single_zero_one]
  have hgc : ∀ k : ℕ, g.coeff (((-n₀ + k : ℤ) : ℚ) / N) = PowerSeries.coeff k q := by
    intro k
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul, (hdiv _ (-n₀) k).2 rfl, hΦ1]
  have hgz : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((-n₀ + k : ℤ) : ℚ) / N) → g.coeff r = 0 := by
    intro r hr
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul]
    apply hΦ0
    intro k hk
    exact hr k ((hdiv r (-n₀) k).1 hk)
  refine ⟨?_, ?_⟩
  · rw [hg]
    refine ⟨N, hN, fun r hr => ?_⟩
    by_contra H
    push_neg at H
    exact hr (hgz r fun k hk => H _ hk)

  set A : ℕ → ℂ := fun k => ε (a k) with hAdef
  have hA0 : A 0 ≠ 0 := (map_ne_zero ε).2 ha0
  have hnorm : ∀ z : ℂ, ‖Complex.exp (2 * Real.pi * Complex.I * z / N)‖ = Real.exp (-(2 * Real.pi * z.im / N)) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    have hNc : ((N : ℂ)) = ((N : ℝ) : ℂ) := by push_cast; rfl
    rw [hNc, Complex.div_ofReal_re]
    simp
    ring
  have hred : ∀ z : ℂ, C < z.im → HasSum (fun k : ℕ => A k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := by
    intro z hz
    exact (GlobalTheory.fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN hcoef hzero).1 (hS z hz)
  set t0 : ℝ := max C 0 + 1 with ht0
  set z0 : ℂ := (t0 : ℂ) * Complex.I with hz0
  have hz0im : C < z0.im := by
    simp [z0, t0]
    have := le_max_left C 0
    linarith
  set x0 : ℂ := Complex.exp (2 * Real.pi * Complex.I * z0 / N) with hx0
  have hx0pos : 0 < ‖x0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hsum0 := hred z0 hz0im
  have hconv : ∀ x : ℂ, ‖x‖ < ‖x0‖ → Summable fun n => A n * x ^ n := fun x hx =>
    summable_powerSeries_of_norm_lt hsum0.tendsto_sum_nat.cauchySeq hx
  obtain ⟨ρ', hρ', hmain⟩ := GlobalTheory.T.hasSum_powerSeries_inv_of_convergent A ‖x0‖ hx0pos hA0 hconv
  have hmk : PowerSeries.mk A = PowerSeries.map ε p := by
    ext k
    simp [p, A]
  have hmapinv : PowerSeries.map ε q = (PowerSeries.mk A)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one]
    · rw [hmk, ← map_mul, hqdef, PowerSeries.inv_mul_cancel _ hp0, map_one]
    · simpa using hA0
  refine ⟨max C ((N : ℝ) * |Real.log ρ'| / (2 * Real.pi)), fun z hz => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  have hzL : (N : ℝ) * |Real.log ρ'| / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hx : ‖x‖ < ρ' := by
    rw [hxdef, hnorm, ← Real.exp_log hρ']
    apply Real.exp_lt_exp.2
    have hpi : 0 < 2 * Real.pi := by positivity
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hpi] at hzL
    have h1 : |Real.log ρ'| < 2 * Real.pi * z.im / N := by
      rw [lt_div_iff₀ hNr]; linarith
    have h2 := neg_abs_le (Real.log ρ')
    have h3 : -(2 * Real.pi * z.im / N) = -(2 * Real.pi * z.im / N) := rfl
    linarith
  obtain ⟨hS0, hinv⟩ := hmain x hx
  have htsum : (∑' n, A n * x ^ n) = φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)) :=
    (hred z hzC).tsum_eq
  rw [hg]
  apply (GlobalTheory.fn_hasSum_reindex_nat Ω ε g N (-n₀) (fun k => PowerSeries.coeff k q) z (φ⁻¹ z) hN hgc hgz).2
  convert (preTransparency := .reducible) hinv using 1
  · funext k
    rw [← hmapinv, PowerSeries.coeff_map]
  · rw [htsum, mul_inv, ← Complex.exp_neg, Pi.inv_apply]
    congr 2
    push_cast
    ring

end GlobalTheory
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ

theorem intCast_eq_of_dvd_sub {k : ℕ} {x y : ℤ} (h : (k : ℤ) ∣ x - y) : (x : ZMod k) = (y : ZMod k) :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y k).2 (by rw [← neg_sub]; exact dvd_neg.2 h)

theorem exists_scalar_mod_level : ∀ (N l a M : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → 0 < M → ¬ l ∣ M →
    ∃ c ∈ Gam N l, (∀ g : SL(2, ℤ), c * g * c⁻¹ * g⁻¹ ∈ CongruenceSubgroup.Gamma (M * N * l ^ a)) ∧
      ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (l ^ a)) = if i = j then -1 else 0 := by
  intro N l a M _ hl _ hlN _ hlM
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = ((M * N : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = ((l ^ (a + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  have hcop : IsCoprime Q L := by
    rw [hQ, hL, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2
      (fun h => (hl.dvd_mul.1 h).elim hlM hlN)))
  obtain ⟨α, β, hab⟩ := hcop
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = β * L - α * Q := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = Q * L := ⟨_, rfl⟩
  have e1 : t * t + m * (4 * α * β) = 1 := by
    rw [ht, hm]; linear_combination (α * Q + β * L + 1) * hab
  have hc : IsCoprime t (m ^ 2) := IsCoprime.pow_right ⟨t, 4 * α * β, by linear_combination e1⟩
  obtain ⟨u, v, e2⟩ := hc
  have hut : u - t = m * (4 * α * β * u - t * v * m) := by linear_combination (-u) * e1 + t * e2
  have ht1 : t - 1 = Q * (-2 * α) := by rw [ht]; linear_combination hab
  have ht2 : t - -1 = L * (2 * β) := by rw [ht]; linear_combination (-1 : ℤ) * hab
  obtain ⟨c, hcm⟩ : ∃ c : SL(2, ℤ), (c : Matrix (Fin 2) (Fin 2) ℤ) = !![t, -(m * v); m, u] :=
    ⟨⟨!![t, -(m * v); m, u], by rw [Matrix.det_fin_two_of]; linear_combination e2⟩, rfl⟩
  have h00 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = t := by rw [hcm]; rfl
  have h01 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(m * v) := by rw [hcm]; rfl
  have h10 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = m := by rw [hcm]; rfl
  have h11 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = u := by rw [hcm]; rfl
  have hNQ : (N : ℤ) ∣ Q := hQ ▸ Int.natCast_dvd_natCast.2 (dvd_mul_left N M)
  have hlaL : ((l ^ a : ℕ) : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (pow_dvd_pow l (Nat.le_succ a))
  have hlL : (l : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (dvd_pow_self l (Nat.succ_ne_zero a))
  have hKm : ((M * N * l ^ a : ℕ) : ℤ) ∣ m := by
    rw [hm, hQ, hL, ← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_left _ (pow_dvd_pow l (Nat.le_succ a)))
  have hNm : (N : ℤ) ∣ m := hm ▸ hNQ.mul_right L
  have hlm : (l : ℤ) ∣ m := hm ▸ hlL.mul_left Q
  have hlam : ((l ^ a : ℕ) : ℤ) ∣ m := hm ▸ hlaL.mul_left Q

  have tN : ((t : ℤ) : ZMod N) = 1 := by
    simpa using intCast_eq_of_dvd_sub (k := N) (y := 1) (hNQ.trans ⟨_, ht1⟩)
  have uN : ((u : ℤ) : ZMod N) = 1 := by
    have hd : (N : ℤ) ∣ u - 1 := by
      rw [show u - 1 = (u - t) + (t - 1) by ring]
      exact dvd_add (hNm.trans ⟨_, hut⟩) (hNQ.trans ⟨_, ht1⟩)
    simpa using intCast_eq_of_dvd_sub (k := N) hd
  have mN : ((m : ℤ) : ZMod N) = 0 := by simpa using intCast_eq_of_dvd_sub (k := N) (y := 0) (by simpa using hNm)
  have ml : ((m : ℤ) : ZMod l) = 0 := by simpa using intCast_eq_of_dvd_sub (k := l) (y := 0) (by simpa using hlm)

  have tla : ((t : ℤ) : ZMod (l ^ a)) = -1 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := -1) (hlaL.trans ⟨_, ht2⟩)
  have ula : ((u : ℤ) : ZMod (l ^ a)) = -1 := by
    have hd : ((l ^ a : ℕ) : ℤ) ∣ u - -1 := by
      rw [show u - -1 = (u - t) + (t - -1) by ring]
      exact dvd_add (hlam.trans ⟨_, hut⟩) (hlaL.trans ⟨_, ht2⟩)
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) hd
  have mla : ((m : ℤ) : ZMod (l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := 0) (by simpa using hlam)

  have mK : ((m : ℤ) : ZMod (M * N * l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := M * N * l ^ a) (y := 0) (by simpa using hKm)
  have uK : ((u : ℤ) : ZMod (M * N * l ^ a)) = t := intCast_eq_of_dvd_sub (hKm.trans ⟨_, hut⟩)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [Gam, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
    simp only [h00, h11, h10, tN, uN, mN, ml, and_self]
  · intro g
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv]
    set φ := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * N * l ^ a)))
    have hsc : (↑(φ c) : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) =
        ((t : ℤ) : ZMod (M * N * l ^ a)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [φ, Matrix.SpecialLinearGroup.map_apply_coe, h00, h01, h10, h11, mK, uK]
    have hcomm : φ c * φ g = φ g * φ c := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hsc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, tla, ula, mla]

end GlobalTheory.KZ
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.ClsMod

variable {l : ℕ} [Fact l.Prime] {G : Type} [AddCommGroup G]

abbrev Q (l : ℕ) [Fact l.Prime] (n : ℕ) (G : Type) [AddCommGroup G] : Type :=
  (ℤ_[l] ⊗[ℤ] G) ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G)))

theorem idl_pow_eq_ker (n : ℕ) : (idl l) ^ n = RingHom.ker (PadicInt.toZModPow (p := l) n) := by
  rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow]

theorem smul_mem_of_toZModPow {n : ℕ} {a : ℤ_[l]} (ha : PadicInt.toZModPow n a = 0) (m : ℤ_[l] ⊗[ℤ] G) :
    a • m ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G)) :=
  Submodule.smul_mem_smul (by rw [idl_pow_eq_ker]; exact ha) trivial

instance neZero_pow (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem mk_tmul (n : ℕ) (c : ℤ_[l]) (g : G) :
    (Submodule.Quotient.mk (c ⊗ₜ[ℤ] g) : Q l n G) =
      Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] (((PadicInt.toZModPow n c).val : ℕ) • g)) := by
  rw [Submodule.Quotient.eq]
  have h : c ⊗ₜ[ℤ] g - (1 : ℤ_[l]) ⊗ₜ[ℤ] (((PadicInt.toZModPow n c).val : ℕ) • g)
      = (c - ((PadicInt.toZModPow n c).val : ℤ_[l])) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul,
      nsmul_eq_mul, mul_one]
  rw [h]
  apply smul_mem_of_toZModPow
  rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]

theorem exists_mk (n : ℕ) (y : Q l n G) : ∃ g : G, Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) = y := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c g => exact ⟨_, (mk_tmul n c g).symm⟩
  | add x y hx hy =>
    obtain ⟨gx, hx⟩ := hx
    obtain ⟨gy, hy⟩ := hy
    exact ⟨gx + gy, by rw [TensorProduct.tmul_add, Submodule.Quotient.mk_add, hx, hy, Submodule.Quotient.mk_add]⟩

abbrev H (l n : ℕ) (G : Type) [AddCommGroup G] : AddSubgroup G := (nsmulAddMonoidHom (α := G) (l ^ n)).range

def psi (n : ℕ) : ℤ_[l] →+ (G →+ G ⧸ H l n G) :=
  (ZMod.lift (l ^ n) ⟨zmultiplesHom (G →+ G ⧸ H l n G) (QuotientAddGroup.mk' (H l n G)), by
    ext g
    simp only [zmultiplesHom_apply, AddMonoidHom.zsmul_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.zero_apply]
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨g, by rw [nsmulAddMonoidHom_apply, ← natCast_zsmul, Nat.cast_pow]⟩⟩).comp (PadicInt.toZModPow n).toAddMonoidHom

theorem psi_one (n : ℕ) (g : G) : psi (l := l) n 1 g = QuotientAddGroup.mk g := by
  have e : (1 : ZMod (l ^ n)) = ((1 : ℤ) : ZMod (l ^ n)) := by simp
  simp only [psi, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_one]
  rw [e, ZMod.lift_coe]
  simp

def phi (n : ℕ) : ℤ_[l] ⊗[ℤ] G →+ G ⧸ H l n G :=
  TensorProduct.liftAddHom (psi n) (fun r c g => by rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul])

theorem phi_tmul (n : ℕ) (c : ℤ_[l]) (g : G) : phi n (c ⊗ₜ[ℤ] g) = psi n c g :=
  TensorProduct.liftAddHom_tmul _ _ _ _

theorem phi_eq_zero (n : ℕ) (x : ℤ_[l] ⊗[ℤ] G) (hx : x ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] G))) :
    phi n x = 0 := by
  refine Submodule.smul_induction_on hx (fun a ha m hm => ?_) (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])
  clear hm
  rw [idl_pow_eq_ker, RingHom.mem_ker] at ha
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul c g =>
    rw [TensorProduct.smul_tmul', phi_tmul, smul_eq_mul]
    simp [psi, ha]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]

theorem mk_eq_iff (n : ℕ) (g g' : G) :
    (Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g) : Q l n G) = Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ[ℤ] g') ↔
      ∃ h : G, g = g' + (l ^ n) • h := by
  constructor
  · intro e
    rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub] at e
    have h0 := phi_eq_zero n _ e
    rw [phi_tmul, psi_one, QuotientAddGroup.eq_zero_iff] at h0
    obtain ⟨h, hh⟩ := h0
    refine ⟨h, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hh
    rw [hh]; abel
  · rintro ⟨h, rfl⟩
    rw [Submodule.Quotient.eq, ← TensorProduct.tmul_sub, add_sub_cancel_left, TensorProduct.tmul_smul,
      ← Nat.cast_smul_eq_nsmul ℤ_[l]]
    apply smul_mem_of_toZModPow
    rw [map_natCast, ZMod.natCast_self]

end GlobalTheory.KZ.ClsMod


open GlobalTheory.KZ.ClsMod in
theorem GlobalTheory.KZ.H3.cls_props : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, (∀ y, ∃ f, X.cls l n f = y) ∧ (∀ f f' : X.Kˣ, X.cls l n f = X.cls l n f' ↔ ∃ g : X.Kˣ, f = f' * g ^ (l ^ n)) ∧ (∀ f f' : X.Kˣ, X.cls l n (f * f') = X.cls l n f + X.cls l n f') ∧ X.cls l n 1 = 0 ∧ (∀ (c : ℤ_[l]) (f : X.Kˣ), c • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n c).val)) ∧ (∀ (φ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = X.cls l n (Units.map φ.toMonoidHom f)) ∧ (∀ (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x = X.cls l (n + 1) f → AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) := by
  intro Ω _ _ ε X l _ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨g, hg⟩ := exists_mk n y
    exact ⟨Additive.toMul g, hg⟩
  · intro f f'
    unfold Tower.cls
    rw [mk_eq_iff]
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨Additive.toMul h, ?_⟩
      apply Additive.ofMul.injective
      rw [hh, ofMul_mul, ofMul_pow]; rfl
    · rintro ⟨g, rfl⟩
      exact ⟨Additive.ofMul g, by rw [ofMul_mul, ofMul_pow]⟩
  · intro f f'
    unfold Tower.cls
    rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]
  · unfold Tower.cls
    rw [ofMul_one, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]
  · intro c f
    unfold Tower.cls
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, mk_tmul, ofMul_pow]
  · intro φ x f hx
    rw [AdicCompletion.eval_apply] at hx ⊢
    have e := AdicCompletion.map_val_apply (idl l)
      (LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) x
    refine (e.trans ?_)
    rw [hx, Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
    rfl
  · intro x f hx
    rw [AdicCompletion.eval_apply] at hx ⊢
    rw [← AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x, hx]
    rfl
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem Datum.theta_ne_zero_of_mem {G : Type} [Group G] [TopologicalSpace G] {H : Set G} {θ : G → ℂ}
    (hD : Datum H θ) {j : G} (hj : j ∈ H) : θ j ≠ 0 := by
  intro h0
  have h := hD.val_mul j hj j⁻¹ (hD.inv j hj)
  rw [mul_inv_cancel, hD.val_one, h0, zero_mul] at h
  exact one_ne_zero h

theorem eig_compl_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  intro G V _ _ _ _ _ π hπ H θ hD
  refine ⟨fun u hu he => ?_, fun w => ?_⟩
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ H θ hD u hu
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    have hsum : ∑ j ∈ R, (θ j)⁻¹ • π j u = (R.card : ℂ) • u := by
      rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
      intro j hj
      rw [he j (hRH j hj), smul_smul, inv_mul_cancel₀ (hD.theta_ne_zero_of_mem (hRH j hj)), one_smul]
    rw [hsum] at hs
    exact (smul_eq_zero.mp hs).resolve_left hc
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ H θ hD w
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    refine ⟨(R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w, ?_, ?_⟩
    · intro h hh
      rw [(π h).map_smul, hs h hh]
      exact smul_comm _ _ _
    · have e : w - (R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w
          = (R.card : ℂ)⁻¹ • ∑ j ∈ R, (w - (θ j)⁻¹ • π j w) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ hc, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
      have hθ := hD.theta_ne_zero_of_mem (hRH j hj)
      have e2 : w - (θ j)⁻¹ • π j w = -(θ j)⁻¹ • (π j w - θ j • w) := by
        rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hθ, one_smul, neg_sub]
      rw [e2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hRH j hj, w, rfl⟩)

end GlobalTheory.PsType
end

section

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_mem_span_of_trData : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C,
      (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  intro A S M _ _ _ _ _ B C tr n a b e ht D hD x hx
  set N : Submodule S M := Submodule.span S (D '' (B : Set S))
  have hD' : IsDerOn C (fun s => N.mkQ (D s)) :=
    { add := fun u hu v hv => by simp only [hD.add u hu v hv, map_add (f := _)]
      mul := fun u hu v hv => by simp only [hD.mul u hu v hv, map_add (f := _), map_smul]
      alg := fun r => by simp only [hD.alg r, map_zero] }
  have hB : ∀ β ∈ B, N.mkQ (D β) = 0 := fun β hβ => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨β, hβ, rfl⟩
  have h := GlobalTheory.T.derivationOn_vanishing_on_subalgebra_killed_sq A S (M ⧸ N) B C tr n a b e ht (fun s => N.mkQ (D s)) hD' hB x hx
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact h

end GlobalTheory.AlmostEt
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_conj_level_elem_exponent_shimura : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M → l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧ (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  first | exact @GlobalTheory.exists_conj_level_exponent | exact GlobalTheory.exists_conj_level_exponent | (intros; apply GlobalTheory.exists_conj_level_exponent <;> assumption)
end
