module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow

@[expose] public section

section

noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.LinearTraceLemmas

variable {A Y : Type} [MeasurableSpace Y] (ν : Measure Y) (V : Submodule ℂ (A → ℂ))

def evl (a : A) : Module.Dual ℂ V := (LinearMap.proj a : (A → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype

theorem evl_apply (a : A) (f : V) : evl V a f = f.1 a := rfl

theorem span_evl [FiniteDimensional ℂ V] : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ V).surjective f
  have hv : v = 0 := by
    apply Subtype.ext
    funext a
    have h1 : (Module.evalEquiv ℂ V v) (evl V a) = 0 :=
      LinearMap.mem_ker.mp (hfk (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (Module.evalEquiv ℂ V v) (evl V a) = v.1 a := by
      rfl
    have h3 : v.1 a = 0 := h2.symm.trans h1
    simpa using h3
  exact hf0 (by rw [hv, map_zero])

omit [MeasurableSpace Y] in
theorem bound_mul {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y) (C D : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) (y : Y) : ‖g y * h y‖ ≤ C * D := by
  have hn' := hn y
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have hlt : C < 0 := not_le.mp hneg
    have : C * n y < 0 := mul_neg_of_neg_of_pos hlt hn'
    linarith [norm_nonneg (g y), hC y]
  rw [norm_mul]
  calc ‖g y‖ * ‖h y‖ ≤ (C * n y) * ‖h y‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
    _ = C * (‖h y‖ * n y) := by ring
    _ ≤ C * D := mul_le_mul_of_nonneg_left (hD y) hC0

theorem integrable_mul [IsFiniteMeasure ν] {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y)
    (hg : Measurable g) (hh : Measurable h) (C D : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * n y)
    (hD : ∀ y, ‖h y‖ * n y ≤ D) : Integrable (fun y => g y * h y) ν := by
  exact (integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable
    (ae_of_all _ fun y => bound_mul hn C D hC hD y)

def Good (K : Y → V) (ev : Y → A) (n : Y → ℝ) (φ : Module.Dual ℂ V) : Prop :=
  Measurable (fun y => φ (K y)) ∧ (∃ C, ∀ y, ‖φ (K y)‖ ≤ C * n y) ∧
    ∀ f : V, ∫ y, φ (K y) * f.1 (ev y) ∂ν = φ f

theorem good_all [IsFiniteMeasure ν] [FiniteDimensional ℂ V] (K : Y → V) (ev : Y → A) (n : Y → ℝ)
    (hn : ∀ y, 0 < n y) (hK : ∀ a, Measurable fun y => (K y).1 a)
    (hev : ∀ f : V, Measurable fun y => f.1 (ev y)) (hKb : ∀ a, ∃ C, ∀ y, ‖(K y).1 a‖ ≤ C * n y)
    (hevb : ∀ f : V, ∃ C, ∀ y, ‖f.1 (ev y)‖ * n y ≤ C)
    (hrep : ∀ (f : V) a, ∫ y, (K y).1 a * f.1 (ev y) ∂ν = f.1 a) (φ : Module.Dual ℂ V) :
    Good ν V K ev n φ := by
  have hint : ∀ ψ : Module.Dual ℂ V, Good ν V K ev n ψ → ∀ f : V,
      Integrable (fun y => ψ (K y) * f.1 (ev y)) ν := by
    intro ψ hψ f
    obtain ⟨C, hC⟩ := hψ.2.1
    obtain ⟨D, hD⟩ := hevb f
    exact integrable_mul ν hn hψ.1 (hev f) C D hC hD
  have hadd : ∀ φ₁ φ₂, Good ν V K ev n φ₁ → Good ν V K ev n φ₂ → Good ν V K ev n (φ₁ + φ₂) := by
    intro φ₁ φ₂ h₁ h₂
    obtain ⟨C₁, hC₁⟩ := h₁.2.1
    obtain ⟨C₂, hC₂⟩ := h₂.2.1
    refine ⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))
    · simp only [LinearMap.add_apply, add_mul]
      rw [integral_add (hint φ₁ h₁ f) (hint φ₂ h₂ f), h₁.2.2 f, h₂.2.2 f]
  have hzero : Good ν V K ev n 0 := by
    refine ⟨?_, ⟨0, fun y => ?_⟩, fun f => ?_⟩
    · simp
    · simp
    · simp
  have hsmul : ∀ (c : ℂ) φ, Good ν V K ev n φ → Good ν V K ev n (c • φ) := by
    intro c φ h
    obtain ⟨C, hC⟩ := h.2.1
    refine ⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2.2 f]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Submodule ℂ (Module.Dual ℂ V), ∀ ψ, ψ ∈ Sg ↔ Good ν V K ev n ψ :=
    ⟨{ carrier := {ψ | Good ν V K ev n ψ}
       add_mem' := fun {a b} ha hb => hadd a b ha hb
       zero_mem' := hzero
       smul_mem' := fun c ψ h => hsmul c ψ h }, fun _ => Iff.rfl⟩
  have hev' : ∀ a, Good ν V K ev n (evl V a) := by
    intro a
    refine ⟨?_, ?_, fun f => ?_⟩
    · simpa only [evl_apply] using hK a
    · simpa only [evl_apply] using hKb a
    · simpa only [evl_apply] using hrep f a
  have htop : Sg = ⊤ := by
    rw [eq_top_iff, ← span_evl V, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (hSg _).mpr (hev' a)
  exact (hSg φ).mp (by rw [htop]; exact Submodule.mem_top)

theorem main : UpperTheory.Esk.LinTr := by
  intro A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep
  have hgood : ∀ φ : Module.Dual ℂ V, Good ν V K ev n φ :=
    good_all ν V K ev n hn hK hev hKb hevb hrep
  let b := Module.finBasis ℂ V
  have hexp : ∀ y, (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y) := by
    intro y
    have e : T (K y) = ∑ i, b.repr (K y) i • T (b i) := by
      conv_lhs => rw [← b.sum_repr (K y)]

      rw [map_sum]
      simp only [map_smul]
    rw [e]
    simp [Module.Basis.coord_apply]
  have hmeas : Measurable fun y => (T (K y)).1 (ev y) := by
    simp_rw [hexp]
    exact Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i)))
  have hbd : ∃ C, ∀ y, ‖(T (K y)).1 (ev y)‖ ≤ C := by
    choose Cs hCs using fun i => (hgood (b.coord i)).2.1
    choose Ds hDs using fun i => hevb (T (b i))
    refine ⟨∑ i, Cs i * Ds i, fun y => ?_⟩
    rw [hexp]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => bound_mul hn (Cs i) (Ds i) (hCs i) (hDs i) y)
  have hintg : ∀ i, Integrable (fun y => b.coord i (K y) * (T (b i)).1 (ev y)) ν := by
    intro i
    obtain ⟨C, hC⟩ := (hgood (b.coord i)).2.1
    obtain ⟨D, hD⟩ := hevb (T (b i))
    exact integrable_mul ν hn (hgood (b.coord i)).1 (hev (T (b i))) C D hC hD
  refine ⟨hmeas, hbd, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hintg i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hgood (b.coord i)).2.2 (T (b i))]
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end UpperTheory.Esk.LinearTraceLemmas

theorem UpperTheory.Esk.pf_LinTr : UpperTheory.Esk.LinTr := by
  exact UpperTheory.Esk.LinearTraceLemmas.main
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem a_sq_rpow {n : ℝ} (hn : 0 ≤ n) (k : ℕ) : (n ^ 2) ^ ((k : ℝ) / 2) = n ^ k := by
  rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn, ← Real.rpow_natCast n k]
  congr 1
  push_cast <;> ring

theorem a_rpow_half_sq {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : a ^ ((k : ℝ) / 2) * a ^ ((k : ℝ) / 2) = a ^ k := by
  rw [← Real.mul_rpow ha ha, ← sq, a_sq_rpow ha]

theorem p5 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2) = |z.1.im| ^ ((k : ℝ) / 2) := by
  have hden : den g z.1 ≠ 0 := den_ne g z.2
  have hD : 0 < ‖den g z.1‖ := norm_pos_iff.mpr hden
  have hdet : 0 < |g.val.det| := abs_pos.mpr g.det_ne_zero
  have him : (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
    rw [coe_smul, im_div]
  have hns : Complex.normSq (den g z.1) = ‖den g z.1‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have habs : |(g • z).1.im| = |g.val.det| * |z.1.im| / ‖den g z.1‖ ^ 2 := by
    rw [him, hns, abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖den g z.1‖ ^ 2)]
  have hj : ‖j1 k g z‖ = ‖den g z.1‖ ^ k * |g.val.det| ^ (-(k : ℝ) / 2) := by
    rw [j1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hinv : |g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2) = 1 := by
    rw [neg_div, Real.rpow_neg (abs_nonneg _), inv_mul_cancel₀ (Real.rpow_pos_of_pos hdet _).ne']
  have hDk : ‖den g z.1‖ ^ k ≠ 0 := pow_ne_zero _ hD.ne'
  rw [hj, habs, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
    a_sq_rpow (norm_nonneg _)]
  rw [show ∀ A B C E : ℝ, A * B * (C * E / A) = (B * C) * E * (A / A) from fun _ _ _ _ => by ring,
    hinv, div_self hDk, one_mul, mul_one]

theorem a_sub_conj_ne (z w : P) (h : 0 < z.1.im * w.1.im) : z.1 - conj w.1 ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
  have hzw : z.1.im = -w.1.im := by linarith
  rw [hzw] at h
  nlinarith [sq_nonneg w.1.im]

theorem p6 (k : ℕ) (z w : P) (hk : 1 ≤ k) : ‖q1 k z w‖ * |z.1.im| ^ ((k : ℝ) / 2) = ((k : ℝ) - 1) / (4 * Real.pi) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) / 2 ≠ 0 := by
    intro h0
    linarith
  by_cases h : 0 < z.1.im * w.1.im
  · have hq : q1 k z w = ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (z.1 - conj w.1)) ^ k := by
      rw [q1, if_pos h]
    have hkap : kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
      rw [kap, if_pos h]
    have hd : z.1 - conj w.1 ≠ 0 := a_sub_conj_ne z w h
    have hdn : 0 < ‖z.1 - conj w.1‖ := norm_pos_iff.mpr hd
    have hww : ‖w.1 - conj w.1‖ = 2 * |w.1.im| := by
      rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    have hc : ‖((k : ℂ) - 1) / (4 * Real.pi)‖ = ((k : ℝ) - 1) / (4 * Real.pi) := by
      have hpi := Real.pi_pos
      have e : ((k : ℂ) - 1) / (4 * Real.pi) = ((((k : ℝ) - 1) / (4 * Real.pi) : ℝ) : ℂ) := by
        push_cast <;> ring
      rw [e, Complex.norm_real, Real.norm_of_nonneg (by apply div_nonneg <;> linarith)]
    have hzw : z.1.im * w.1.im = |z.1.im| * |w.1.im| := by
      rw [← abs_mul, abs_of_pos h]
    have h4 : (4 : ℝ) ^ ((k : ℝ) / 2) = 2 ^ k := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, a_sq_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hq, norm_mul, hc, norm_pow, norm_div, hww, hkap, hzw,
      Real.div_rpow (by positivity) (by positivity), a_sq_rpow hdn.le,
      Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _), h4,
      div_pow, mul_pow, ← a_rpow_half_sq (abs_nonneg w.1.im) k]
    ring
  · have hq : q1 k z w = 0 := by
      rw [q1, if_neg h]
    have hkap : kap z w = 0 := by
      rw [kap, if_neg h]
    rw [hq, hkap, norm_zero, zero_mul, Real.zero_rpow hk0, mul_zero, zero_mul]

end UpperTheory.Esk.AutomorphyFactorLemmas
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem kap_rot (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m 0 0 = a) (h01 : m 0 1 = b)
    (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) (z : P) (hz : 0 < z.1.im) :
    kap z (m • z) ≤ (a ^ 2 + b ^ 2) / b ^ 2 * kap iP z := by
  set x := z.1.re with hx
  set y := z.1.im with hy
  have hden : den m z.1 ≠ 0 := den_ne m z.2
  have hnd : 0 < Complex.normSq (den m z.1) := Complex.normSq_pos.2 hden
  have hdet : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, h00, h01, h10, h11]; ring
  have hb2 : 0 < b ^ 2 := by positivity
  have hs : 0 < a ^ 2 + b ^ 2 := by positivity
  have hwim : (m • z).1.im = (a ^ 2 + b ^ 2) * y / Complex.normSq (den m z.1) := by
    rw [coe_smul, im_div, hdet]
  have hwpos : 0 < (m • z).1.im := by rw [hwim]; positivity
  have hconj : z.1 - conj (m • z).1 = (z.1 * conj (den m z.1) - conj (num m z.1)) / conj (den m z.1) := by
    have : conj (den m z.1) ≠ 0 := (map_ne_zero _).2 hden
    rw [coe_smul, map_div₀]
    field_simp
  have hE : Complex.normSq (z.1 * conj (den m z.1) - conj (num m z.1)) =
      b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
    rw [Complex.normSq_apply]
    simp [num, den, h00, h01, h10, h11, ← hx, ← hy]
    ring
  have hN : ‖z.1 - conj (m • z).1‖ ^ 2 = (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) / Complex.normSq (den m z.1) := by
    rw [hconj, Complex.sq_norm, Complex.normSq_div, Complex.normSq_conj, hE]
  have hI : ‖iP.1 - conj z.1‖ ^ 2 = x ^ 2 + (1 + y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [iP, ← hx, ← hy]
    ring
  have hk1 : kap z (m • z) = 4 * (a ^ 2 + b ^ 2) * y ^ 2 / (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) := by
    rw [kap, if_pos (mul_pos hz hwpos), hN, hwim]
    simp only [← hy]
    field_simp
  have hk2 : kap iP z = 4 * y / (x ^ 2 + (1 + y) ^ 2) := by
    rw [kap, if_pos (by simpa [iP] using hz), hI]
    simp [iP, ← hy]
  rw [hk1, hk2]
  have hQ : 0 < b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by positivity
  have hR : 0 < x ^ 2 + (1 + y) ^ 2 := by positivity
  rw [div_mul_div_comm, div_le_div_iff₀ hQ (mul_pos hb2 hR)]
  have h1 : 2 * y ≤ x ^ 2 + y ^ 2 + 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  have key : b ^ 2 * (y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2) ≤ b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
    have : y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2 ≤ (x ^ 2 + y ^ 2 + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hb2.le, sq_nonneg a, sq_nonneg y]
  have e : x ^ 2 + (1 + y) ^ 2 = (x ^ 2 + y ^ 2 + 1) + 2 * y := by ring
  rw [e]
  have hs' : 0 ≤ 4 * (a ^ 2 + b ^ 2) * y := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hs']

theorem exists_fix (g : GL (Fin 2) ℝ) (hg : g.val.trace ^ 2 < 4 * g.val.det) : ∃ z : P, g • z = z := by
  have htr : g.val.trace = g 0 0 + g 1 1 := Matrix.trace_fin_two _
  rw [htr, det_eq] at hg
  set p := g 0 0 with hp
  set q := g 0 1 with hq
  set r := g 1 0 with hr
  set t := g 1 1 with ht
  set D := 4 * (p * t - q * r) - (p + t) ^ 2 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hg
    nlinarith [sq_nonneg (p - t)]
  set sD := Real.sqrt D with hsD
  have hsD0 : 0 < sD := Real.sqrt_pos.2 hD0
  have hsD2 : (sD : ℂ) ^ 2 = (D : ℂ) := by
    rw [← Complex.ofReal_pow, hsD, Real.sq_sqrt hD0.le]
  set z0 : ℂ := (((p - t : ℝ) : ℂ) + Complex.I * sD) / (2 * (r : ℂ)) with hz0
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0
  have him : z0.im ≠ 0 := by
    have : z0 = (((p - t) / (2 * r) : ℝ) : ℂ) + ((sD / (2 * r) : ℝ) : ℂ) * Complex.I := by
      rw [hz0]; push_cast; field_simp
    rw [this]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add]
    rw [add_zero]
    exact div_ne_zero hsD0.ne' (mul_ne_zero two_ne_zero hr0)
  have hz : (2 * (r : ℂ)) * z0 = ((p - t : ℝ) : ℂ) + Complex.I * sD := by
    rw [hz0]; field_simp
  have hquad : (r : ℂ) * z0 ^ 2 + ((t : ℂ) - p) * z0 - q = 0 := by
    have h4 : (4 * (r : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hrc
    apply mul_left_cancel₀ h4
    rw [mul_zero]
    have hDc : (D : ℂ) = 4 * ((p : ℂ) * t - q * r) - (p + t) ^ 2 := by rw [hD]; push_cast; ring
    rw [hDc] at hsD2
    push_cast at hz
    linear_combination (2 * (r : ℂ) * z0 + ((p : ℂ) - t + Complex.I * sD) + 2 * ((t : ℂ) - p)) * hz
      + (sD : ℂ) ^ 2 * Complex.I_sq - hsD2
  refine ⟨(⟨z0, him⟩ : P), Subtype.ext ?_⟩
  change num g z0 / den g z0 = z0
  have hd := den_ne g (z := z0) him
  rw [div_eq_iff hd]
  simp only [num, den]
  rw [← hp, ← hq, ← hr, ← ht]
  linear_combination (-1 : ℂ) * hquad

end UpperTheory.Esk.RadialIntegralLemmas
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem b_cv : Continuous (fun z : P => z.1) := by
  exact continuous_subtype_val

theorem b_ne (z w : ℂ) (h : 0 < z.im * w.im) : z - conj w ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h1
  have h2 : w.im = -z.im := by linarith
  rw [h2] at h
  nlinarith [mul_self_nonneg z.im]

theorem b_neg (z w : P) (h : ¬ 0 < z.1.im * w.1.im) : z.1.im * w.1.im < 0 := by
  have hne : z.1.im * w.1.im ≠ 0 := mul_ne_zero z.2 w.2
  exact lt_of_le_of_ne (not_lt.mp h) hne

theorem p7 (k : ℕ) (g : GL (Fin 2) ℝ) : Continuous (j1 k g) := by
  unfold j1 den
  exact (((continuous_const.mul b_cv).add continuous_const).pow k).mul continuous_const

theorem p8 (k : ℕ) : Continuous fun p : P × P => q1 k p.1 p.2 := by
  have hz : Continuous fun p : P × P => p.1.1 := b_cv.comp continuous_fst
  have hw : Continuous fun p : P × P => p.2.1 := b_cv.comp continuous_snd
  have hf : Continuous fun p : P × P => p.1.1.im * p.2.1.im :=
    (Complex.continuous_im.comp hz).mul (Complex.continuous_im.comp hw)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : 0 < p.1.1.im * p.2.1.im
  · have hU : ∀ᶠ q in nhds p, 0 < q.1.1.im * q.2.1.im := (hf.tendsto p).eventually (lt_mem_nhds hp)
    have hg : ContinuousAt (fun q : P × P =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((q.2.1 - conj q.2.1) / (q.1.1 - conj q.2.1)) ^ k) p := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.pow
      apply ContinuousAt.div
      · exact (hw.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact (hz.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact b_ne _ _ hp
    apply hg.congr
    filter_upwards [hU] with q hq
    simp only [q1, if_pos hq]
  · have hV : ∀ᶠ q in nhds p, q.1.1.im * q.2.1.im < 0 :=
      (hf.tendsto p).eventually (gt_mem_nhds (b_neg p.1 p.2 hp))
    have hg : ContinuousAt (fun _ : P × P => (0 : ℂ)) p := continuousAt_const
    apply hg.congr
    filter_upwards [hV] with q hq
    simp only [q1, if_neg (not_lt.mpr hq.le)]

theorem p9 (k : ℕ) (w : P) : Hol1 fun z => q1 k z w := by
  intro t ht
  have ht' : t.im ≠ 0 := ht
  apply DifferentiableAt.differentiableWithinAt
  have hcont : Continuous fun s : ℂ => s.im * w.1.im := Complex.continuous_im.mul continuous_const
  by_cases hp : 0 < t.im * w.1.im
  · have hU : ∀ᶠ s in nhds t, 0 < s.im * w.1.im := (hcont.tendsto t).eventually (lt_mem_nhds hp)
    have hd : DifferentiableAt ℂ (fun s : ℂ =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (s - conj w.1)) ^ k) t := by
      apply DifferentiableAt.mul (differentiableAt_const _)
      apply DifferentiableAt.pow
      apply DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub (differentiableAt_const _))
      exact b_ne _ _ hp
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU] with s hs
    have hs' : s.im ≠ 0 := fun h0 => by rw [h0, zero_mul] at hs; exact lt_irrefl _ hs
    simp only [ext1, dif_pos hs', q1, if_pos hs]
  · have hneg : t.im * w.1.im < 0 := lt_of_le_of_ne (not_lt.mp hp) (mul_ne_zero ht' w.2)
    have hV : ∀ᶠ s in nhds t, s.im * w.1.im < 0 := (hcont.tendsto t).eventually (gt_mem_nhds hneg)
    apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hV] with s hs
    by_cases hs' : s.im ≠ 0
    · simp only [ext1, dif_pos hs', q1, if_neg (not_lt.mpr hs.le)]
    · simp only [ext1, dif_neg hs']

end UpperTheory.Esk.AutomorphyFactorLemmas
end
end
