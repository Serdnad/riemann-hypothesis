module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.IsoP

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem pow_eq_one {p : ℕ} {S : Matrix κ κ ℤ} (h : ∑ i ∈ Finset.range p, S ^ i = 0) : S ^ p = 1 := by
  have := geom_sum_mul S p
  rw [h, zero_mul] at this
  exact (sub_eq_zero.mp this.symm)

theorem map_pow_eq (S : Matrix κ κ ℤ) (n : ℕ) : (S.map (Int.cast : ℤ → F)) ^ n = (S ^ n).map (Int.cast : ℤ → F) := by
  show ((Int.castRingHom F).mapMatrix S) ^ n = (Int.castRingHom F).mapMatrix (S ^ n)
  rw [map_pow]

theorem iter_eq (A : Matrix κ κ F) (n : ℕ) (x : κ → F) : (fun x => A *ᵥ x)^[n] x = (A ^ n) *ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Matrix.mulVec_mulVec]

theorem mem_LL (x : κ → F) : x ∈ LL F κ ↔ ∀ i, x i ∈ integralClosure ℤ F := by
  simp [LL, AddSubgroup.mem_pi]

theorem mulVec_LL (M : Matrix κ κ ℤ) {x : κ → F} (hx : x ∈ LL F κ) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ LL F κ := by
  rw [mem_LL] at hx ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hx j)

theorem mulVec_aL (M : Matrix κ κ ℤ) (a : F) {x : κ → F} (hx : x ∈ aL κ a) : (M.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a := by
  simp only [aL, AddSubgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨_, mulVec_LL M hy, ?_⟩
  simp [Matrix.mulVec_smul]

theorem pow_mulVec_fix (A : Matrix κ κ F) {x : κ → F} (hx : A *ᵥ x = x) (n : ℕ) : (A ^ n) *ᵥ x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hx, ih]

theorem prime_not_dvd_of_neg_one_pow_mul_modEq_one {p : ℕ} (hp : p.Prime) {t : ℕ} {k : ℕ} (h : (-1) ^ k * (t : ℤ) ≡ 1 [ZMOD p]) : ¬ (p : ℤ) ∣ t := by
  intro hd
  have h2 := Int.modEq_iff_dvd.mp h
  have h3 : (p : ℤ) ∣ 1 := by
    have h4 := dvd_add h2 (dvd_mul_of_dvd_right hd ((-1) ^ k))
    simpa using h4
  have h5 : p ∣ 1 := by exact_mod_cast h3
  exact hp.not_dvd_one h5

private theorem sum_pow_map_intCast_eq_zero {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {p : ℕ} {S : Matrix κ κ ℤ} (cyc : ∑ i ∈ Finset.range p, S ^ i = 0) :
    ∑ i ∈ Finset.range p, (S.map (Int.cast : ℤ → F)) ^ i = 0 := by
  simp only [map_pow_eq]
  have e := congrArg (Int.castRingHom F).mapMatrix cyc

  rw [map_sum, map_zero] at e
  exact e

theorem isometry_order_p : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  intro F _ _ p hp κ _ _ G S t hL
  obtain ⟨_, _, iso, cyc, _, cong⟩ := hL
  have hφ : ∀ M : Matrix κ κ ℤ, M.map (Int.cast : ℤ → F) = (Int.castRingHom F).mapMatrix M := fun _ => rfl
  have hsum0 := sum_pow_map_intCast_eq_zero (F := F) cyc
  set S' : Matrix κ κ F := S.map (Int.cast : ℤ → F) with hS'
  have hpow : S' ^ p = 1 := by
    rw [hS', map_pow_eq, pow_eq_one cyc]
    simp
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hinv : ∀ y : κ → F, S' *ᵥ ((S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ', hp1, hpow, Matrix.one_mulVec]
  have hinv' : ∀ y : κ → F, (S ^ (p - 1)).map (Int.cast : ℤ → F) *ᵥ (S' *ᵥ y) = y := by
    intro y
    rw [← map_pow_eq, Matrix.mulVec_mulVec, ← pow_succ, hp1, hpow, Matrix.one_mulVec]
  have hsum : ∑ i ∈ Finset.range p, S' ^ i = 0 := hsum0
  have hBF : ∀ x y : κ → F, BF G (S' *ᵥ x) (S' *ᵥ y) = BF G x y := by
    intro x y
    have key : S'ᵀ * G.map (Int.cast : ℤ → F) * S' = G.map (Int.cast : ℤ → F) := by
      rw [hS', ← Matrix.transpose_map]
      simp only [hφ]
      rw [← map_mul, ← map_mul, iso]
    unfold BF
    rw [← Matrix.vecMul_transpose S' x, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, key]
  have memD : ∀ y : κ → F, y ∈ dualL F G ↔ ∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n :=
    fun _ => Iff.rfl
  refine ⟨fun x y => ⟨hBF x y, ?_⟩, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_, prime_not_dvd_of_neg_one_pow_mul_modEq_one hp cong⟩
  · unfold QF
    rw [hBF]
  · rw [iter_eq, hpow, Matrix.one_mulVec]
  · intro hx
    have e : ∑ i ∈ Finset.range p, S' ^ i *ᵥ x = 0 := by
      rw [← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec]
    simp only [pow_mulVec_fix S' hx, Finset.sum_const, Finset.card_range] at e
    rw [← Nat.cast_smul_eq_nsmul F] at e
    have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    exact (smul_eq_zero.mp e).resolve_left hp0
  · rw [memD, memD]
    constructor
    · intro h l hl
      have h' := h _ (mulVec_LL S hl)
      rwa [hBF] at h'
    · intro h l hl
      have h' := h _ (mulVec_LL (S ^ (p - 1)) hl)
      rwa [← hBF, hinv] at h'
  · intro a
    constructor
    · intro h
      have h' := mulVec_aL (S ^ (p - 1)) a h
      rwa [hinv'] at h'
    · intro h
      exact mulVec_aL S a h
  · intro N x hN hcop hx hz
    have hstep : ∀ i : ℕ, S' ^ i *ᵥ x - x ∈ aL κ (N : F) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : S' ^ (i + 1) *ᵥ x - x = S' *ᵥ (S' ^ i *ᵥ x - x) + (S' *ᵥ x - x) := by
          rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
          abel
        rw [e]
        exact add_mem (mulVec_aL S _ ih) hz
    have hpx : (p : F) • x ∈ aL κ (N : F) := by
      have h0 : ∑ i ∈ Finset.range p, (S' ^ i *ᵥ x - x) = -((p : F) • x) := by
        rw [Finset.sum_sub_distrib, ← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec, Finset.sum_const,
          Finset.card_range, zero_sub, Nat.cast_smul_eq_nsmul]
      have hs := AddSubgroup.sum_mem (aL κ (N : F)) (t := Finset.range p) (fun i _ => hstep i)
      rw [h0] at hs
      exact neg_mem_iff.mp hs
    have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hNx : (N : F) ^ 2 • x ∈ aL κ (N : F) := by
      simp only [aL, AddSubgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨y, hy, ?_⟩
      simp only [DistribSMul.toAddMonoidHom_apply, smul_smul]
      rw [pow_two, mul_assoc, mul_inv_cancel₀ hN0, mul_one]
    obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) ((N : ℤ) ^ 2) := by
      have hc : Nat.Coprime p (N ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
      exact_mod_cast Nat.isCoprime_iff_coprime.mpr hc
    have hx' : x = u • ((p : F) • x) + v • ((N : F) ^ 2 • x) := by
      rw [← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul, ← add_smul]
      have e : (u : F) * p + (v : F) * (N : F) ^ 2 = 1 := by exact_mod_cast huv
      rw [e, one_smul]
    rw [hx']
    exact add_mem (zsmul_mem hpx u) (zsmul_mem hNx v)

end GlobalTheory.HilbertThetaSeries.IsoP

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → (∀ x y : κ → F, BF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) ((S.map (Int.cast : ℤ → F)) *ᵥ y) = BF G x y ∧ QF G ((S.map (Int.cast : ℤ → F)) *ᵥ x) = QF G x) ∧ (∀ x : κ → F, (fun x => (S.map (Int.cast : ℤ → F)) *ᵥ x)^[p] x = x ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x = x → x = 0) ∧ ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ dualL F G ↔ x ∈ dualL F G) ∧ ∀ a : F, ((S.map (Int.cast : ℤ → F)) *ᵥ x ∈ aL κ a ↔ x ∈ aL κ a)) ∧ (∀ (N : ℕ) (x : κ → F), 0 < N → N.Coprime p → x ∈ aL κ (N : F)⁻¹ → (S.map (Int.cast : ℤ → F)) *ᵥ x - x ∈ aL κ (N : F) → x ∈ aL κ (N : F)) ∧ ¬ (p : ℤ) ∣ t := by
  first | exact @GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | exact GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p | (intros; apply GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QUniq

def chr {V : Type} [Fintype V] (μ x : V → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ))

theorem chr_add {V : Type} [Fintype V] (μ x y : V → ℝ) : chr μ (x + y) = chr μ x * chr μ y := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]

theorem chr_add' {V : Type} [Fintype V] (μ ν x : V → ℝ) : chr (μ + ν) x = chr μ x * chr ν x := by
  simp only [chr, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.exp_add]

theorem chr_zero {V : Type} [Fintype V] (μ : V → ℝ) : chr μ 0 = 1 := by simp [chr]

theorem chr_zero' {V : Type} [Fintype V] (x : V → ℝ) : chr 0 x = 1 := by simp [chr]

theorem norm_chr {V : Type} [Fintype V] (μ x : V → ℝ) : ‖chr μ x‖ = 1 := by
  have : (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ)) = ((2 * Real.pi * ∑ v, μ v * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [chr, this, Complex.norm_exp_ofReal_mul_I]

theorem exists_chr {V : Type} [Fintype V] (μ : V → ℝ) (h : μ ≠ 0) : ∃ g, chr μ g = -1 := by
  classical
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  have hv' : (μ v : ℂ) ≠ 0 := by exact_mod_cast hv
  refine ⟨Pi.single v (1 / (2 * μ v)), ?_⟩
  have : ∑ w, (μ w : ℂ) * ((Pi.single v (1 / (2 * μ v)) : V → ℝ) w : ℂ) = 1 / 2 := by
    rw [Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]; push_cast; field_simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  rw [chr, this, ← Complex.exp_pi_mul_I]
  congr 1; ring

theorem hasSum_congr' {ι : Type} {f g : ι → ℂ} {d : ℂ} (h : HasSum f d) (e : ∀ i, g i = f i) : HasSum g d := by
  rwa [show g = f from funext e]

private theorem hasSum_average_chr_of_hasSum {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (C : ι → ℂ) (d : ℂ)
    (h : ∀ x, HasSum (fun i => C i * chr (μ i) x) d) (g : V → ℝ) (x : V → ℝ) :
    HasSum (fun i => C i * ((1 + chr (μ i) g) / 2) * chr (μ i) x) d := by
  have h2 := ((h x).add (h (x + g))).div_const 2
  have hd : (d + d) / 2 = d := by ring
  rw [hd] at h2
  refine hasSum_congr' h2 (fun i => ?_)
  rw [chr_add]
  ring

private theorem norm_one_add_chr_div_two_le_one {V : Type} [Fintype V] (μ x : V → ℝ) : ‖(1 + chr μ x) / 2‖ ≤ 1 := by
  rw [norm_div]
  have h1 := norm_add_le (1 : ℂ) (chr μ x)
  rw [norm_one, norm_chr] at h1
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith

theorem kill_freq {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) (S : Finset ι) :
    ∃ C : ι → ℂ, (∀ i, ‖C i‖ ≤ ‖B i‖) ∧ (∀ i ∈ S, C i = 0) ∧ ∀ x, HasSum (fun i => C i * chr (μ i) x) d := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨B, fun i => le_rfl, by simp, h⟩
  · intro j S _ ih
    obtain ⟨C, hCn, hCS, hC⟩ := ih
    by_cases hj : C j = 0
    · refine ⟨C, hCn, fun i hi => ?_, hC⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hj
      · exact hCS i hi
    · have hB : B j ≠ 0 := by
        intro hB0
        apply hj
        have h3 := hCn j
        rw [hB0, norm_zero] at h3
        exact norm_le_zero_iff.mp h3
      obtain ⟨g, hg⟩ := exists_chr (μ j) (hμ j hB)
      refine ⟨fun i => C i * ((1 + chr (μ i) g) / 2), fun i => ?_, fun i hi => ?_,
        fun x => hasSum_average_chr_of_hasSum μ C d hC g x⟩
      · rw [norm_mul]
        calc ‖C i‖ * ‖(1 + chr (μ i) g) / 2‖ ≤ ‖C i‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_one_add_chr_div_two_le_one _ _) (norm_nonneg _)
          _ ≤ ‖B i‖ := by
              rw [mul_one]
              exact hCn i
      · rcases Finset.mem_insert.mp hi with rfl | hi
        · simp [hg]
        · simp [hCS i hi]

theorem const_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) d) : d = 0 := by
  classical
  have hB : Summable B := by
    have h0 := (h 0).summable
    simpa [chr_zero] using h0
  have hnB : Summable (fun i => ‖B i‖) := summable_norm_iff.mpr hB
  have key : ∀ ε > 0, ‖d‖ ≤ ε := by
    intro ε hε
    obtain ⟨S, hS⟩ := (summable_iff_vanishing_norm.mp hnB) ε hε
    obtain ⟨C, hCn, hCS, hC⟩ := kill_freq μ B d hμ h S
    have hC0 := Filter.Tendsto.norm (hC 0)
    refine le_of_tendsto' hC0 (fun t => ?_)
    simp only [chr_zero, mul_one]
    have e1 : ∑ i ∈ t \ S, C i = ∑ i ∈ t, C i :=
      Finset.sum_subset Finset.sdiff_subset (fun i hi hni => hCS i (by
        rw [Finset.mem_sdiff] at hni
        tauto))
    rw [← e1]
    calc ‖∑ i ∈ t \ S, C i‖ ≤ ∑ i ∈ t \ S, ‖C i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ t \ S, ‖B i‖ := Finset.sum_le_sum (fun i _ => hCn i)
      _ ≤ ‖∑ i ∈ t \ S, ‖B i‖‖ := Real.le_norm_self _
      _ ≤ ε := (hS _ Finset.sdiff_disjoint).le
  by_contra hd
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have h3 := key (‖d‖ / 2) (by linarith)
  linarith

theorem coef_eq_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (hμ : Function.Injective μ)
    (h : ∀ x, HasSum (fun i => B i * chr (μ i) x) 0) (j : ι) : B j = 0 := by
  classical
  apply neg_eq_zero.mp
  apply const_eq_zero (fun i => μ i + -μ j) (Function.update B j 0) (-B j)
  · intro i hi h0
    have hij : i ≠ j := by
      rintro rfl
      simp at hi
    exact hij (hμ (add_neg_eq_zero.mp h0))
  · intro x
    have h1 := ((h x).mul_left (chr (-μ j) x)).update j 0
    have hc : chr (-μ j) x * chr (μ j) x = 1 := by
      rw [← chr_add', neg_add_cancel, chr_zero']
    have hval : (0 - chr (-μ j) x * (B j * chr (μ j) x) + chr (-μ j) x * 0) = -B j := by
      linear_combination (-B j) * hc
    rw [hval] at h1
    refine hasSum_congr' h1 (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Function.update_of_ne hij, Function.update_of_ne hij, chr_add']
      ring

end GlobalTheory.HilbertThetaSeries.QUniq

private theorem ez_at_imaginary_unit_shift_eq {F : Type} [Field F] [NumberField F] (ζ : F) (x : InfinitePlace F → ℝ) :
    ez ζ (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)) =
      GlobalTheory.HilbertThetaSeries.QUniq.chr (fun v => reAt v ζ) x *
        Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I) := by
  simp only [ez, GlobalTheory.HilbertThetaSeries.QUniq.chr, UpperHalfPlane.coe_mk]
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]


open GlobalTheory.HilbertThetaSeries.QUniq in
theorem GlobalTheory.HilbertThetaSeries.hasQ_unique : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a b : F → ℂ),
    HasQ f a → HasQ f b → a = b := by
  intro F _ _ _ f a b ha hb
  funext ξ
  have hinj : Function.Injective (fun ζ : F => fun v : InfinitePlace F => reAt v ζ) := by
    intro ζ η hζη
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hv := IsTotallyReal.isReal v
    have h1 := congrFun hζη v
    simp only [reAt] at h1
    apply (InfinitePlace.embedding_of_isReal hv).injective
    rw [← InfinitePlace.embedding_of_isReal_apply hv ζ, ← InfinitePlace.embedding_of_isReal_apply hv η,
      Complex.ofReal_re, Complex.ofReal_re] at h1
    exact h1
  have hsum : ∀ x : InfinitePlace F → ℝ, HasSum (fun ζ => ((a ζ - b ζ) *
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ζ : ℂ) * Complex.I)) *
        chr (fun v => reAt v ζ) x) 0 := by
    intro x
    have h2 := (ha.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp))).sub
      (hb.2 (fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I) (by simp)))
    rw [sub_self] at h2
    refine hasSum_congr' h2 (fun ζ => ?_)
    simp only [ez_at_imaginary_unit_shift_eq]
    ring
  have key := coef_eq_zero (fun ζ : F => fun v => reAt v ζ) _ hinj hsum ξ
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (Complex.exp_ne_zero _))
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem hasQ_lin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  intro F _ _ _ f g a b c hf hg
  obtain ⟨⟨D, hD, hfa⟩, hfs⟩ := hf
  obtain ⟨⟨E, hE, hgb⟩, hgs⟩ := hg
  have hez : ∀ z : Hn F, ez (0 : F) z = 1 := by
    intro z
    simp [ez, reAt]
  have scale : ∀ (ξ : F) (m k : ℕ), IsIntegral ℤ ((m : F) * ξ) →
      IsIntegral ℤ (((m * k : ℕ) : F) * ξ) ∧ IsIntegral ℤ (((k * m : ℕ) : F) * ξ) := by
    intro ξ m k h
    have e1 : ((m * k : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have e2 : ((k * m : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have hk : IsIntegral ℤ ((k : ℤ) : F) := isIntegral_algebraMap
    exact ⟨e1 ▸ hk.mul h, e2 ▸ hk.mul h⟩
  have both : ∀ ξ : F, a ξ ≠ 0 ∨ b ξ ≠ 0 →
      (ξ = 0 ∨ TP ξ) ∧ IsIntegral ℤ (((D * E : ℕ) : F) * ξ) := by
    intro ξ h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := hfa ξ h
      exact ⟨h1, (scale ξ D E h2).1⟩
    · obtain ⟨h1, h2⟩ := hgb ξ h
      exact ⟨h1, (scale ξ E D h2).2⟩
  have hDE : 0 < D * E := Nat.mul_pos hD hE
  refine ⟨⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨D, hD, ?_⟩, ?_⟩, ⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨1, one_pos, ?_⟩, ?_⟩⟩
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.add_apply, add_mul] using (hfs z).add (hgs z)
  · intro ξ h
    apply hfa
    intro h0
    apply h
    simp [h0]
  · intro z
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using (hfs z).mul_left c
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.sub_apply, sub_mul] using (hfs z).sub (hgs z)
  · intro ξ h
    have h0 : ξ = 0 := by
      by_contra hne
      apply h
      simp [hne]
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : F))
  · intro z
    have := hasSum_single (f := fun ξ : F => (open Classical in if ξ = 0 then c else 0) * ez ξ z) (0 : F) (by
      intro ξ hξ
      simp [hξ])
    convert this using 1
    simp [hez z]
end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.qExpansion_linear_combination : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_lin | exact GlobalTheory.HilbertThetaSeries.hasQ_lin | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_lin <;> assumption)
end
