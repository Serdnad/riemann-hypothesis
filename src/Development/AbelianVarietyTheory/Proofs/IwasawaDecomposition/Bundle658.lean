module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.PeriodFrame

open GlobalTheory.ShFam.Hor

def combMat {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k i => ∑ m, (ε i m : ℂ) * l m k

def perTau {n g r₀ r : ℕ} (a : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ)
    (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ) (s : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (D : ℂ) • ((combMat (ζ (logExp a s)) α)⁻¹ * combMat (lam s) φ)

theorem combMat_comb {g r r' : ℕ} (w : Fin r' → Fin g → ℂ) (l : Fin r → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ)
    (α : Matrix (Fin g) (Fin r') ℚ) (hw : ∀ i, w i = ∑ j, c i j • l j) :
    combMat w α = combMat l (α * c.map (Int.cast : ℤ → ℚ)) := by
  ext k i
  simp only [combMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hw, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by
    simp only [Pi.mul_apply, Pi.intCast_apply]; ring

theorem combMat_add_mul {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (φ + bᵀ * ε) = combMat l φ + combMat l ε * b.map (Rat.cast : ℚ → ℂ) := by
  ext k j
  simp only [combMat, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem combMat_shift {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) (D : ℕ) (Bk : Matrix (Fin g) (Fin g) ℤ) (hP : IsUnit (combMat l ε).det)
    (hB : ∀ i j, (Bk i j : ℚ) = D * b i j) :
    (D : ℂ) • ((combMat l ε)⁻¹ * combMat l (φ + bᵀ * ε)) =
      (D : ℂ) • ((combMat l ε)⁻¹ * combMat l φ) + Bk.map (Int.cast : ℤ → ℂ) := by
  rw [combMat_add_mul, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, smul_add]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have h := congrArg (Rat.cast : ℚ → ℂ) (hB i j)
  push_cast at h
  rw [h]

theorem shift_mem {n a : ℕ} (ha : a ≤ n) (k : Fin a) {s : Fin n → ℂ} (hs : s ∈ logDom n a) :
    s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I) ∈ logDom n a ∧
      logExp a (s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) = logExp a s := by
  simp only [logDom, Set.mem_setOf_eq] at hs ⊢
  constructor
  · intro j
    have h := hs j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [hk, if_true] at h ⊢
      simpa [Pi.add_apply] using h
    · simpa [Pi.add_apply, Pi.single_eq_of_ne hj] using h
  · funext j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, _root_.mul_one]
    · simp [logExp, Pi.single_eq_of_ne hj]

end GlobalTheory.PeriodFrame
end
end

section

open GlobalTheory.ShFam.Hor

set_option autoImplicit false

namespace GlobalTheory.LogDescent

open Complex Topology

theorem continuous_logExp (n a : ℕ) : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) := by
  refine continuous_pi fun k => ?_
  simp only [logExp]
  split_ifs
  · exact Complex.continuous_exp.comp (continuous_apply k)
  · exact continuous_apply k

theorem mem_logDom_of_mem_ball {n a : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (s : Fin n → ℂ)
    (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) : s ∈ logDom n a := by
  intro k
  have hz := mem_ball_zero_iff.1 hs
  have hk' := (norm_le_pi_norm (logExp a s) k).trans_lt hz
  split_ifs with hk
  · simp only [logExp, hk, if_true, Complex.norm_exp] at hk'
    exact Real.exp_lt_one_iff.mp (lt_of_lt_of_le hk' hρ1)
  · simp only [logExp, hk, if_false] at hk'
    exact lt_of_lt_of_le hk' hρ1

theorem logExp_shift {n a : ℕ} (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    logExp a (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = logExp a s := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · simp [logExp, Pi.single_eq_of_ne hj]

variable {n a : ℕ} {ρ : ℝ} {h : (Fin n → ℂ) → ℂ}

theorem inv_int (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (k : Fin n) (hk : (k : ℕ) < a) (m : ℤ) :
    h (s + Pi.single k ((m : ℂ) * (2 * Real.pi * Complex.I))) = h s := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have ht : logExp a (s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : s + Pi.single k ((((m : ℤ) + 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) =
        s + Pi.single k (((m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) + Pi.single k (2 * Real.pi * Complex.I) := by
      rw [add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [e, this, ih]
  | pred m ih =>
    set t := s + Pi.single k ((((-(m : ℤ) - 1 : ℤ)) : ℂ) * (2 * Real.pi * Complex.I)) with htdef
    have ht : logExp a t ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
      rw [htdef, logExp_shift s k hk]; exact hs
    have := hinv _ (mem_logDom_of_mem_ball hρ1 _ ht) ht k hk
    have e : t + Pi.single k (2 * Real.pi * Complex.I) =
        s + Pi.single k ((((-(m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [htdef, add_assoc, ← Pi.single_add]; congr 2; push_cast; ring
    rw [← this, e, ih]

theorem key (hρ1 : ρ ≤ 1)
    (hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s)
    (s s' : Fin n → ℂ) (hs : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ) (he : logExp a s = logExp a s') :
    h s = h s' := by
  suffices H : ∀ S : Finset (Fin n), ∀ s s' : Fin n → ℂ, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      logExp a s = logExp a s' → (∀ k ∉ S, s k = s' k) → h s = h s' from
    H Finset.univ s s' hs he (fun k hk => absurd (Finset.mem_univ k) hk)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro s s' _ _ hk
    congr 1; funext k; exact hk k (Finset.notMem_empty k)
  | insert j S hjS ih =>
    intro s s' hs he hk
    have hej := congrFun he j
    set s'' := Function.update s' j (s j) with hs''
    have he'' : logExp a s = logExp a s'' := by
      funext k
      by_cases hkj : k = j
      · subst hkj; simp [hs'', logExp]
      · have := congrFun he k
        simpa [hs'', logExp, Function.update_of_ne hkj] using this
    have h1 : h s = h s'' := ih s s'' hs he'' (fun k hk' => by
      by_cases hkj : k = j
      · subst hkj; simp [hs'']
      · rw [hs'', Function.update_of_ne hkj]
        exact hk k (by simp [hkj, hk']))
    rw [h1]
    have hs2 : logExp a s'' ∈ Metric.ball (0 : Fin n → ℂ) ρ := he'' ▸ hs
    by_cases hja : (j : ℕ) < a
    · simp only [logExp, hja, if_true] at hej
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hej.symm
      have e : s' = s'' + Pi.single j ((m : ℂ) * (2 * Real.pi * Complex.I)) := by
        funext k
        by_cases hkj : k = j
        · subst hkj; simp [hs'', hm]
        · simp [hs'', Function.update_of_ne hkj, Pi.single_eq_of_ne hkj]
      rw [e, inv_int hρ1 hinv s'' hs2 j hja m]
    · simp only [logExp, hja, if_false] at hej
      congr 1
      rw [hs'', hej, Function.update_eq_self]

theorem dom_mem_nhds {ρ : ℝ} (hρ1 : ρ ≤ 1) (s₀ : Fin n → ℂ)
    (hs₀ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ) :
    {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 s₀ := by
  have ho : IsOpen (logExp a ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    Metric.isOpen_ball.preimage (continuous_logExp n a)
  refine Filter.mem_of_superset (ho.mem_nhds hs₀) ?_
  intro s hs
  rw [Set.mem_preimage] at hs
  exact ⟨mem_logDom_of_mem_ball hρ1 s hs, hs⟩

noncomputable def logSec (a : ℕ) {n : ℕ} (z : Fin n → ℂ) : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k

noncomputable def logSecAt (a : ℕ) {n : ℕ} (z₀ z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if (k : ℕ) < a then Complex.log (z₀ k) + Complex.log (z k / z₀ k) else z k

theorem logExp_logSec (z : Fin n → ℂ) (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSec a z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp [logExp, logSec, hk, Complex.exp_log (hz k hk)]
  · simp [logExp, logSec, hk]

theorem logExp_logSecAt (z₀ z : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0)
    (hz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : logExp a (logSecAt a z₀ z) = z := by
  funext k
  by_cases hk : (k : ℕ) < a
  · simp only [logExp, logSecAt, hk, if_true]
    rw [Complex.exp_add, Complex.exp_log (hz₀ k hk), Complex.exp_log (div_ne_zero (hz k hk) (hz₀ k hk))]
    field_simp [hz₀ k hk]
  · simp [logExp, logSecAt, hk]

theorem differentiableAt_logSecAt (z₀ : Fin n → ℂ) (hz₀ : ∀ k : Fin n, (k : ℕ) < a → z₀ k ≠ 0) :
    DifferentiableAt ℂ (logSecAt a z₀) z₀ := by
  rw [differentiableAt_pi]
  intro k
  have hpk : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k) z₀ := differentiableAt_apply k z₀
  by_cases hk : (k : ℕ) < a
  · simp only [logSecAt, hk, if_true]
    refine (differentiableAt_const _).add ?_
    have hq : DifferentiableAt ℂ (fun z : Fin n → ℂ => z k / z₀ k) z₀ := by
      simpa [div_eq_mul_inv] using hpk.mul_const (z₀ k)⁻¹
    refine hq.clog ?_
    simp [div_self (hz₀ k hk), Complex.one_mem_slitPlane]
  · simpa [logSecAt, hk] using hpk

theorem descent : ∀ (n a : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ → ρ ≤ 1 →
    DifferentiableOn ℂ h {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} →
    (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ k : Fin n, (k : ℕ) < a →
      h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s) →
    ∃ H : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → h s = H (logExp a s) := by
  intro n a ρ h _ hρ1 hd hinv
  refine ⟨fun z => h (logSec a z), ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨hb₀, hn₀⟩ := hz₀

    have hU : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
      have h1 : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.isOpen_ball.mem_nhds hb₀
      refine h1.and ?_
      rw [Filter.eventually_all]
      intro k
      by_cases hk : (k : ℕ) < a
      · exact ((continuous_apply k).continuousAt.eventually_ne (hn₀ k hk)).mono fun z hz _ => hz
      · exact Filter.Eventually.of_forall fun z hk' => absurd hk' hk
    have hEq : (fun z => h (logSec a z)) =ᶠ[𝓝 z₀] fun z => h (logSecAt a z₀ z) := by
      refine hU.mono fun z ⟨hb, hn⟩ => ?_
      refine key hρ1 hinv _ _ ?_ ?_
      · rw [logExp_logSec z hn]; exact hb
      · rw [logExp_logSec z hn, logExp_logSecAt z₀ z hn₀ hn]
    have hD : {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ} ∈ 𝓝 (logSecAt a z₀ z₀) := by
      refine dom_mem_nhds hρ1 _ ?_
      rw [logExp_logSecAt z₀ z₀ hn₀ hn₀]; exact hb₀
    have hh : DifferentiableAt ℂ h (logSecAt a z₀ z₀) := hd.differentiableAt hD
    have hcomp : DifferentiableAt ℂ (h ∘ logSecAt a z₀) z₀ :=
      DifferentiableAt.comp (𝕜 := ℂ) z₀ hh (differentiableAt_logSecAt z₀ hn₀)
    exact (hcomp.congr_of_eventuallyEq hEq).differentiableWithinAt
  · intro s _ hs
    have hn : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]; exact Complex.exp_ne_zero _
    refine key hρ1 hinv _ _ hs ?_
    rw [logExp_logSec _ hn]

end GlobalTheory.LogDescent
end

section

open GlobalTheory.ShFam.Hor
open scoped Matrix

namespace GlobalTheory

theorem monodromy_dotProduct_nonneg : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  intro n a g ha ρ₁ τ B hρ0 hρ1 hdiff hpos hmon k v
  by_cases hv : v = 0
  · subst hv; simp
  set j : Fin n := Fin.castLE ha k with hj
  have hjlt : (j : ℕ) < a := by simp [hj]
  let s₀ : Fin n → ℂ := fun i => if (i : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0
  let u : ℂ → Fin n → ℂ := fun t => Function.update s₀ j t
  let D := {s : Fin n → ℂ | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}
  have hlog2 : Real.log (ρ₁ / 2) < 0 := Real.log_neg (by positivity) (by linarith)
  have hlogle : Real.log ρ₁ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hexp2 : Real.exp (Real.log (ρ₁ / 2)) = ρ₁ / 2 := Real.exp_log (by positivity)
  have hmem : ∀ t : ℂ, t.re < Real.log ρ₁ → u t ∈ D := by
    intro t ht
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        simp only [u, Function.update_self, hjlt, if_true]
        linarith
      · simp only [u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · simpa using hlog2
        · simp
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ0]
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [logExp, u, Function.update_self, hjlt, if_true, Complex.norm_exp]
        calc Real.exp t.re < Real.exp (Real.log ρ₁) := Real.exp_lt_exp.2 ht
          _ = ρ₁ := Real.exp_log hρ0
      · simp only [logExp, u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · rw [Complex.norm_exp, Complex.ofReal_re, hexp2]; linarith
        · simpa using hρ0
  let v' : Fin g → ℂ := fun i => (v i : ℂ)
  let f : ℂ → ℂ := fun t => v' ⬝ᵥ (τ (u t) *ᵥ v')
  have hshift : ∀ t : ℂ, u (t + 2 * Real.pi * Complex.I) = u t + Pi.single j (2 * Real.pi * Complex.I) := by
    intro t
    ext i
    by_cases hi : i = j
    · subst hi; simp [u]
    · simp [u, hi, Function.update_of_ne hi, Pi.single_apply]
  have hcast : v' ⬝ᵥ ((B k).map (Int.cast : ℤ → ℂ) *ᵥ v') = ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    simp [v', dotProduct, Matrix.mulVec, Matrix.map_apply]
  have hper : ∀ t : ℂ, t.re < Real.log ρ₁ → f (t + 2 * Real.pi * Complex.I) = f t + ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    intro t ht
    have h1 := hmon (u t) (hmem t ht).1 (hmem t ht).2 k
    simp only [f]
    rw [hshift t, h1, Matrix.add_mulVec, dotProduct_add, hcast]
  let v'' : Fin g → ℝ := fun i => (v i : ℝ)
  have hv'' : v'' ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa [v''] using this
  have him : ∀ t : ℂ, t.re < Real.log ρ₁ → 0 < (f t).im := by
    intro t ht
    have hp := ((hpos (u t) (hmem t ht).1 (hmem t ht).2).2).dotProduct_mulVec_pos hv''
    have heq : (f t).im = star v'' ⬝ᵥ (((τ (u t)).map Complex.im) *ᵥ v'') := by
      simp [f, v', v'', dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum]
    rw [heq]; exact hp
  have hu : Differentiable ℂ u := fun t => (hasFDerivAt_update s₀ t).differentiableAt
  have hent : ∀ i l, DifferentiableOn ℂ (fun t => τ (u t) i l) {t : ℂ | t.re < Real.log ρ₁} :=
    fun i l => (hdiff i l).comp hu.differentiableOn (fun t ht => hmem t ht)
  have hdf : DifferentiableOn ℂ f {t : ℂ | t.re < Real.log ρ₁} := by
    simp only [f, dotProduct, Matrix.mulVec]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro l _
    exact (hent i l).mul_const _
  exact_mod_cast GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos (Real.log ρ₁) f (v ⬝ᵥ (B k *ᵥ v)) hdf hper him

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.TwoMarkings

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ}

theorem linearIndependent_dirs {i : Fin Fu.n} {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ}
    {y : Sp ℂ ⟶ Xo.XF c} (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hy : y ≫ pullback.fst _ _ = Fu.u i P) (hj : y ≫ Z.jQ = a.1.1)
    {v₀ : Letter Dw → (Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left)}
    (h1 : ∀ z, v₀ z ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (h2 : ∀ z, v₀ z ≫ Z.m.φ = a.2.v z.1 z.2)
    (h3 : ∀ z, IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ z ≫ Z.m0.toSABMap.φ)) :
    LinearIndependent ℂ W := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hj]
  have hty : ∀ z j, W z j ≠ 0 → (e j).1 = z.1 := fun z =>
    (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ z.1 (h3 z)).1 fun b =>
      (eig_iff Z.m0.toSABMap (h1 z) b _).2 ((eig_iff Z.m (h1 z) b _).1 (h2 z ▸ a.2.eig z.1 z.2 b))
  obtain ⟨t1, t2, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 0
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [(t1 _ _ hv).1, ← hy, Category.assoc])
  rw [Fintype.linearIndependent_iff]
  rintro cf hc ⟨τ, k⟩
  have hb := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hy k1).1 (t1 _ _ hv)))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1
      ((GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ τ hv).2 (fun j hj => absurd rfl hj) b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hb
  have hcomb : ∀ d : Fin (Dw.mult τ) → ℂ, ∑ k, d k • W ⟨τ, k⟩ = 0 →
      IsCombAtG Z.t (a.1.1 ≫ genι Z) (fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ) d (v' ≫ Z.m.φ) := fun d hd =>
    (comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) d k1).2 ((comb_iff Z.m0.toSABMap hy (fun k => h1 ⟨τ, k⟩) d k1).1
      ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _ _ (fun k => h3 ⟨τ, k⟩) d _).2 (hd ▸ hv)))
  have hτ : ∑ k, cf ⟨τ, k⟩ • W ⟨τ, k⟩ = 0 := by
    funext j
    have hz : ∀ ρ, (e j).1 ≠ ρ → (∑ k, cf ⟨ρ, k⟩ • W ⟨ρ, k⟩) j = 0 := fun ρ hρ => by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Pi.smul_apply, by_contra fun h => hρ (hty ⟨ρ, k⟩ j h), smul_zero]
    by_cases h : (e j).1 = τ
    · have := congrFun hc j
      rw [Fintype.sum_sigma, Finset.sum_apply, Finset.sum_eq_single τ (fun ρ _ hρ => hz ρ (h ▸ hρ.symm)) (by simp)] at this
      exact this
    · exact hz τ h
  exact congrFun (hb.unique (hcomb _ hτ) (hcomb 0 (by simp))) k

theorem per_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a
  haveI := Z.jQ_open
  refine ⟨?_, ?_⟩
  · rintro i j Q Q' ⟨P, W, y, hP, hy, hj, -⟩ ⟨P', W', y', hP', hy', hj', -⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    exact Fu.disj i j P P' hP hP' (hy.symm.trans hy')
  · rintro i Q Q' ⟨P, W, y, hP, hy, hj, hv, hQ⟩ ⟨P', W', y', hP', hy', hj', hv', hQ'⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    choose v₀ h1 h2 h3 using hv
    choose v₁ k1 k2 k3 using hv'
    obtain rfl : v₀ = v₁ := funext fun z =>
      Z.m.cart.1.hom_ext ((h2 z).trans (k2 z).symm) ((h1 z).trans (k1 z).symm)
    obtain ⟨gam, h, g1, g2, g3, g4⟩ := (Fu.fibre i P P' hP hP').1 (hy.symm.trans hy')
    have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
      LinearMap.toMatrix'_mulVec _ z
    obtain ⟨-, -, h5⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ Fu i P P' gam
      (LinearMap.toMatrix' h.toLinearMap) hP hP' g1 g2 g3 (fun a => by rw [hm, g4])
    simp only [hm] at h5
    obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P' hP'
    have hW : ∀ z, h (W z) = W' z := fun z => (t3 _ (t1 _ _ (k3 z))).unique
      ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ Fu i P hP i P' h.toLinearMap hP' h5 _ _).1 (h3 z)) (k3 z)
    refine ⟨gam, g1, g2, fun v => funext fun z => ?_⟩
    refine Fintype.linearIndependent_iffₛ.1 (linearIndependent_dirs hP' hy' hj' k1 k2 k3) _ _ ?_ z

    rw [← hQ', g4, hQ, map_sum]
    simp only [map_smul, hW]

end GlobalTheory.ShFam.Hor.TwoMarkings
end
