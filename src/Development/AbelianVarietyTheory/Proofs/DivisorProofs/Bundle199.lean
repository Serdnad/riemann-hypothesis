module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle047
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle045
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

@[expose] public section

section

open Complex MeasureTheory

namespace GlobalTheory.CharFamily

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem seminorm_mul_le (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (h g : SchwartzMap E ℂ)
    (hg : ∀ x, g x = c x * h x) (k n m : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcb : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i c x‖ ≤ M * (1 + ‖x‖) ^ m) :
    SchwartzMap.seminorm ℂ k n g ≤ 2 ^ n * M *
      (2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h) := by
  set S := 2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h
    with hS
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine SchwartzMap.seminorm_le_bound ℂ k n g (by positivity) fun x => ?_
  have hg' : (⇑g) = fun x => c x * h x := funext hg
  rw [hg']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) hc (h.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        ≤ (n.choose i : ℝ) * (M * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hcb i hi' x
    have h2 : (1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + m, n)) le_rfl (Nat.sub_le n i) h x
    have h5 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
    have hc0 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i c x‖ *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + ‖x‖) ^ k * (M * (1 + ‖x‖) ^ m) *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by gcongr
      _ = (n.choose i : ℝ) * (M * ((1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖)) := by
            ring
      _ ≤ (n.choose i : ℝ) * (M * S) := by gcongr
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => c y * h y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * S) := Finset.sum_le_sum hterm
    _ = 2 ^ n * M * S := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

theorem contDiff_char (L : E →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => Complex.exp (I * (L x : ℂ))) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (I * (y : ℂ))) := by fun_prop
  exact hc.comp L.contDiff

theorem norm_iteratedFDeriv_char_le (L : E →L[ℝ] ℝ) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ))) x‖ ≤ ‖L‖ ^ i := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) := by
    fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) (L x)‖
          * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, Complex.norm_I]
        simp

theorem norm_iteratedFDeriv_char_sub_one_le (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ)) - 1) x‖
      ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) := by fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) ∘ ⇑L := by
    funext x; simp; ring
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  cases i with
  | zero =>
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    have h0 : (1 : ℂ) * Complex.exp (I * ((L x : ℝ) : ℂ)) + 0 * ((L x : ℝ) : ℂ) + (-1)
        = Complex.exp (((L x : ℝ) : ℂ) * I) - 1 := by ring_nf
    simp only [h0]
    calc _ ≤ 2 * |L x| := GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_le (L x)
      _ ≤ 2 * (‖L‖ * ‖x‖) := by gcongr; rw [← Real.norm_eq_abs]; exact L.le_opNorm x
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith
  | succ j =>
    rw [iteratedDeriv_succ', GlobalTheory.CharFormDeriv.deriv_affine_cexp]
    have hd : (fun y : ℝ => (1 : ℂ) * I * Complex.exp (I * y) + 0)
        = fun y : ℝ => I * Complex.exp (I * y) := by funext y; ring
    rw [hd, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
    have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
    rw [norm_mul, norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_pow, Complex.norm_I]
    simp only [one_pow, mul_one, one_mul]
    calc ‖L‖ ^ (j + 1) ≤ ‖L‖ ^ 1 := pow_le_pow_of_le_one hL0 hL (by omega)
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith

theorem one_add_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  have han : 0 ≤ a ^ n := pow_nonneg ha n
  rcases le_total a 1 with h | h
  · have : (1 + a) ^ n ≤ 2 ^ n := by gcongr; linarith
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have : (1 + a) ^ n ≤ (2 * a) ^ n := by gcongr; linarith
    rw [mul_pow] at this
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]

theorem charMul_family : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  intro E P _ _ _ _ A f
  have htg : ∀ L : E →L[ℝ] ℝ,
      Function.HasTemperateGrowth (fun x : E => Complex.exp (I * (L x : ℂ))) := fun L => by
    simpa using GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L 1
  let Φ : P → SchwartzMap E ℂ := fun ξ =>
    SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.exp (I * (A ξ x : ℂ))) f
  have hΦ : ∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x := fun ξ x => by
    simp only [Φ, SchwartzMap.smulLeftCLM_apply_apply (htg (A ξ)), smul_eq_mul]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun ζ => ?_
    unfold ContinuousAt
    rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds Φ (Φ ζ)]
    rintro ⟨k, n⟩ ε hε
    set K := 2 * 2 ^ n * (2 ^ (k + 1) *
      ((Finset.Iic (k + 1, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) (Φ ζ)) with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _))
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    set m := min 1 (ε / (K + 1)) with hm
    have hm0 : 0 < m := lt_min one_pos (div_pos hε (by linarith))
    have hδ : 0 < m / (‖A‖ + 1) := div_pos hm0 (by linarith)
    filter_upwards [Metric.ball_mem_nhds ζ hδ] with η hη
    rw [Metric.mem_ball, dist_eq_norm] at hη
    show SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) < ε
    set L := A (η - ζ) with hLdef
    have hLle : ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := A.le_opNorm _
    have hLm : ‖L‖ < m := by
      calc ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := hLle
        _ ≤ (‖A‖ + 1) * ‖η - ζ‖ := by gcongr; linarith
        _ < (‖A‖ + 1) * (m / (‖A‖ + 1)) := by gcongr
        _ = m := by field_simp
    have hL1 : ‖L‖ ≤ 1 := (lt_of_lt_of_le hLm (min_le_left _ _)).le
    have hLε : ‖L‖ < ε / (K + 1) := lt_of_lt_of_le hLm (min_le_right _ _)
    have hpt : ∀ x, (Φ η - Φ ζ) x = (Complex.exp (I * (L x : ℂ)) - 1) * Φ ζ x := fun x => by
      have hs : A η x = L x + A ζ x := by simp [hLdef, map_sub]
      rw [SchwartzMap.sub_apply, hΦ, hΦ, hs]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      ((contDiff_char L).sub contDiff_const) (Φ ζ) (Φ η - Φ ζ) hpt k n 1 (2 * ‖L‖)
      (by positivity) (fun i _ x => norm_iteratedFDeriv_char_sub_one_le L hL1 i x)
    calc SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) ≤ ‖L‖ * K := by rw [hK]; linarith [hb]
      _ ≤ ‖L‖ * (K + 1) := by gcongr; linarith
      _ < ε / (K + 1) * (K + 1) := by gcongr
      _ = ε := by field_simp
  · intro k n
    set S := 2 ^ (k + 0) * ((Finset.Iic (k + 0, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) f
      with hS
    have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
    refine ⟨2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S, fun ξ => ?_⟩
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
    set L := A ξ with hLdef
    have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ))) (contDiff_char L) f (Φ ξ)
      (hΦ ξ) k n 0 ((1 + ‖L‖) ^ n) (by positivity) (fun i hi x => by
        rw [pow_zero, mul_one]
        calc _ ≤ ‖L‖ ^ i := norm_iteratedFDeriv_char_le L i x
          _ ≤ (1 + ‖L‖) ^ i := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi)
    have h1 : (1 + ‖L‖) ^ n ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
      calc (1 + ‖L‖) ^ n ≤ ((1 + ‖A‖) * (1 + ‖ξ‖)) ^ n := by
            gcongr
            have := A.le_opNorm ξ
            nlinarith
        _ = (1 + ‖A‖) ^ n * (1 + ‖ξ‖) ^ n := mul_pow _ _ _
        _ ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
            gcongr; exact one_add_pow_le _ hξ0 n
    calc SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ 2 ^ n * (1 + ‖L‖) ^ n * S := hb
      _ ≤ 2 ^ n * ((1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n))) * S := by gcongr
      _ = 2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S * (1 + ‖ξ‖ ^ n) := by ring

end GlobalTheory.CharFamily
end

section

open scoped SchwartzMap

namespace GlobalTheory.LinearPhase

open Complex GlobalTheory.CharFormDeriv

theorem seminorm_phase_sub_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  intro V _ _ L c f k n
  set L' : V →L[ℝ] ℝ := (-(2 * Real.pi)) • L with hL'
  have hL'x : ∀ x, ((L' x : ℝ) : ℂ) = -(2 * Real.pi) * (L x : ℂ) := fun x => by
    simp [hL']
  set K := 3 * 2 ^ n * (1 + ‖L'‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)
      with hK
  have hgt : Function.HasTemperateGrowth (fun x : V => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  set g : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f with hgdef
  have hg : ∀ x, g x = (L x : ℂ) * f x := fun x => by
    rw [hgdef, SchwartzMap.smulLeftCLM_apply_apply hgt, smul_eq_mul]
  refine ⟨K + 2 * |2 * Real.pi * c| *
    (SchwartzMap.seminorm ℂ k n f + 2 * Real.pi * SchwartzMap.seminorm ℂ k n g), fun t ht1 => ?_⟩
  set a : ℂ := Complex.exp (((-(2 * Real.pi * c * t ^ 2) : ℝ) : ℂ) * I) with ha
  have hfun : (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) := by
    funext x
    rw [ha, ← Complex.exp_add, hL'x]
    congr 1
    push_cast
    ring
  have het : Function.HasTemperateGrowth fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) :=
    (Function.HasTemperateGrowth.const a).mul (hasTemperateGrowth_char L' t)
  rw [hfun]
  set A : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => Complex.exp ((I * t) * (L' x : ℂ))) f with hAdef
  have hA : ∀ x, A x = Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hAdef, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L' t), smul_eq_mul]
  set E : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ))) f with hEdef
  have hE : ∀ x, E x = a * Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hEdef, SchwartzMap.smulLeftCLM_apply_apply het, smul_eq_mul]
  rcases eq_or_ne t 0 with ht0 | ht0
  · have h0 : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g = 0 := by
      ext x
      simp only [SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hE, ha, ht0]
      simp
    rw [h0, map_zero, ht0]
    simp
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  set u : 𝓢(V, ℂ) := (t : ℂ)⁻¹ • (A - f) + (2 * Real.pi * I : ℂ) • g with hudef
  have hu : ∀ x, u x = rem t (L' x) * f x := fun x => by
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hg,
      rem, smul_eq_mul, hL'x]
    ring
  have hub : SchwartzMap.seminorm ℂ k n u ≤ |t| * K := seminorm_rem_mul_le L' f u ht0 ht1 hu k n
  have hid : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g
      = (a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g) := by
    ext x
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hE,
      smul_eq_mul]
    field_simp
    ring
  have hna : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hna1 : ‖a - 1‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 := by
    refine (norm_cexp_mul_I_sub_one_le _).trans (le_of_eq ?_)
    rw [abs_neg, abs_mul (2 * Real.pi * c), abs_of_nonneg (sq_nonneg t)]
    ring
  have hpf := apply_nonneg (SchwartzMap.seminorm ℂ k n) f
  have hpg := apply_nonneg (SchwartzMap.seminorm ℂ k n) g
  have hpi := Real.pi_pos
  have hn1 : ‖a * t‖ = |t| := by rw [norm_mul, hna, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖-((a - 1) * t * (2 * Real.pi * I))‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) := by
    have h2 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hpi]
    rw [norm_neg, norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs]
    calc ‖a - 1‖ * |t| * (2 * Real.pi) ≤ (2 * |2 * Real.pi * c| * t ^ 2) * 1 * (2 * Real.pi) := by
          gcongr
      _ = _ := by ring
  rw [hid]
  calc SchwartzMap.seminorm ℂ k n ((a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g))
      ≤ SchwartzMap.seminorm ℂ k n ((a * t) • u) + (SchwartzMap.seminorm ℂ k n ((a - 1) • f) +
          SchwartzMap.seminorm ℂ k n ((-((a - 1) * t * (2 * Real.pi * I))) • g)) :=
        (map_add_le_add _ _ _).trans (by gcongr; exact map_add_le_add _ _ _)
    _ = |t| * SchwartzMap.seminorm ℂ k n u + (‖a - 1‖ * SchwartzMap.seminorm ℂ k n f +
          ‖-((a - 1) * t * (2 * Real.pi * I))‖ * SchwartzMap.seminorm ℂ k n g) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul, hn1]
    _ ≤ |t| * (|t| * K) + (2 * |2 * Real.pi * c| * t ^ 2 * SchwartzMap.seminorm ℂ k n f +
          2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) * SchwartzMap.seminorm ℂ k n g) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← sq, sq_abs]; ring

end GlobalTheory.LinearPhase
end

section

open Complex

namespace GlobalTheory.CharModGrowth

theorem norm_iteratedFDeriv_char_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ ≤ (|t| * ‖L‖) ^ n := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) := by
    fun_prop
  have e : (fun x : V => Complex.exp ((I * t) * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := n) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ n (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) (L x)‖
          * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (|t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : (I * t) * ((L x : ℝ) : ℂ) = ((t * L x : ℝ) : ℂ) * I := by push_cast; ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, norm_mul,
          Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        simp [mul_pow]

theorem seminorm_char_mul_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) (f u : SchwartzMap V ℂ)
    (hu : ∀ x, u x = Complex.exp ((I * t) * (L x : ℂ)) * f x) {R : ℝ} (hR1 : 1 ≤ R)
    (hR : |t| * ‖L‖ ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n u ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) f)
        * R ^ n := by
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) f :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  have hR0 : 0 ≤ R := by linarith
  refine SchwartzMap.seminorm_le_bound ℂ k n u (by positivity) fun x => ?_
  have hu' : (⇑u) = fun x => Complex.exp ((I * t) * (L x : ℂ)) * f x := funext hu
  rw [hu']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L t).1 (f.smooth ⊤) x (n := n)
    (by exact_mod_cast le_top)
  calc _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖ :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ ≤ _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖
            ≤ R ^ n :=
          (norm_iteratedFDeriv_char_le L t i x).trans
            ((pow_le_pow_left₀ (by positivity) hR i).trans (pow_le_pow_right₀ hR1 hi'))
        have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ SchwartzMap.seminorm ℂ k (n - i) f :=
          SchwartzMap.le_seminorm ℂ k (n - i) f x
        calc _ = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) *
              ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ := by ring
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)) h1
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))

theorem seminorm_char_mul_polynomial_growth :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  intro V _ _ _ P h v hv k n
  let Q : V →L[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.flip P)
  have hQ : ∀ μ x, Q μ x = P x μ := fun μ x => rfl
  set A : ℝ := |2 * Real.pi| * ‖Q‖ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) h)
    * (1 + A) ^ n, fun μ => ?_⟩
  have hμ : 0 ≤ ‖μ‖ := norm_nonneg μ
  rw [mul_assoc, ← mul_pow]
  refine seminorm_char_mul_le (Q μ) (2 * Real.pi) h (v μ) (fun x => ?_) ?_ ?_ k n
  · rw [hv, hQ]; congr 2; push_cast; ring
  · nlinarith [mul_nonneg hA0 hμ]
  · calc |2 * Real.pi| * ‖Q μ‖ ≤ |2 * Real.pi| * (‖Q‖ * ‖μ‖) :=
          mul_le_mul_of_nonneg_left (Q.le_opNorm μ) (abs_nonneg _)
      _ = A * ‖μ‖ := by rw [hA]; ring
      _ ≤ _ := by nlinarith

end GlobalTheory.CharModGrowth
end

section


theorem _root_.GlobalTheory.T.schwartz_bijection_right_inverse : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ), Function.Bijective T → ∃ S : SchwartzMap W ℂ →L[ℂ] SchwartzMap V ℂ, ∀ f, T (S f) = f := by
  first | exact @GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse | exact GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse | (intros; apply GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse <;> assumption)
end

section


theorem _root_.GlobalTheory.T.schwartz_continuousAt_of_continuousAt_apply_of_bounded : ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  first | exact @GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | exact GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | (intros; apply GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded <;> assumption)
end

section

open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | exact GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | (intros; apply GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le <;> assumption)
end

section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  first | exact @GlobalTheory.schwartz_closure_stable_linearForm_fourier | exact GlobalTheory.schwartz_closure_stable_linearForm_fourier | (intros; apply GlobalTheory.schwartz_closure_stable_linearForm_fourier <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.linear_independent_complex_map : ∀ {E : Type} [Field E] {r n : ℕ} (τ : E →+* ℂ) (e : Fin n → Matrix (Fin r) (Fin r) E), LinearIndependent E e → LinearIndependent ℝ (fun i => (e i).map τ) := by
  first | exact @GlobalTheory.linearIndependent_real_map_of_fieldEmb | exact GlobalTheory.linearIndependent_real_map_of_fieldEmb | (intros; apply GlobalTheory.linearIndependent_real_map_of_fieldEmb <;> assumption)
end
