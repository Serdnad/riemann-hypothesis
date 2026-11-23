module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenGainPolynomial

theorem re_inner_self {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : V) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by
  have := inner_self_eq_norm_sq (𝕜 := ℂ) w
  simpa using this

theorem phi_lb (s : ℕ) (c ν x : ℝ) (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - c * y ^ 4 ≤ ((1 + y) ^ s)⁻¹) :
    ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * c / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))
      ≤ ((1 + x) ^ s)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have hy1 : -1 < (x - ν) / (1 + ν) := by
    rw [lt_div_iff₀ h1]; linarith
  have hA' := hA _ hy1
  have hx1 : 1 + x = (1 + ν) * (1 + (x - ν) / (1 + ν)) := by field_simp; ring
  have ha : 0 ≤ ((1 + ν) ^ s)⁻¹ := by positivity
  calc _ = ((1 + ν) ^ s)⁻¹ * (1 - s * ((x - ν) / (1 + ν)) + (s : ℝ) ^ 2 / 4 * ((x - ν) / (1 + ν)) ^ 2
          - c * ((x - ν) / (1 + ν)) ^ 4) := by
          field_simp; ring
    _ ≤ ((1 + ν) ^ s)⁻¹ * ((1 + (x - ν) / (1 + ν)) ^ s)⁻¹ := mul_le_mul_of_nonneg_left hA' ha
    _ = ((1 + x) ^ s)⁻¹ := by rw [hx1, mul_pow, mul_inv]

theorem fc_poly {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (ν k0 k1 k2 k4 : ℝ) (w : V) :
    (inner ℂ w (fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) w)).re =
      k0 * ‖w‖ ^ 2 + k1 * (inner ℂ w (fc b μ (fun x => x - ν) w)).re
        + k2 * ‖fc b μ (fun x => x - ν) w‖ ^ 2
        + k4 * ‖fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) w)‖ ^ 2 := by
  have e1 : ∀ (k : ℝ) (f : ℝ → ℝ), fc b μ (fun x => k * f x) = (k : ℂ) • fc b μ f := by
    intro k f
    calc fc b μ (fun x => k * f x) = fc b μ (fun _ => k) * fc b μ f := hmul (fun _ => k) f
      _ = (k : ℂ) • fc b μ f := by rw [hconst, smul_mul_assoc, one_mul]
  have hT2 : fc b μ (fun x => (x - ν) * (x - ν)) = fc b μ (fun x => x - ν) * fc b μ (fun x => x - ν) :=
    hmul (fun x => x - ν) (fun x => x - ν)
  have hT4 : fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) =
      fc b μ (fun x => (x - ν) * (x - ν)) * fc b μ (fun x => (x - ν) * (x - ν)) :=
    hmul (fun x => (x - ν) * (x - ν)) (fun x => (x - ν) * (x - ν))
  have hF : fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) =
      (k0 : ℂ) • 1 + (k1 : ℂ) • fc b μ (fun x => x - ν) + (k2 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν))
        + (k4 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) := by
    rw [hadd (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν)))
        (fun x => k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))),
      hadd (fun x => k0 + k1 * (x - ν)) (fun x => k2 * ((x - ν) * (x - ν))),
      hadd (fun _ => k0) (fun x => k1 * (x - ν)), hconst,
      e1 k1 (fun x => x - ν), e1 k2 (fun x => (x - ν) * (x - ν)),
      e1 k4 (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν)))]
  rw [hF, hT4, hT2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply,
    inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  have r2 : ∀ u : V, inner ℂ u (fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) u)) =
      inner ℂ (fc b μ (fun x => x - ν) u) (fc b μ (fun x => x - ν) u) := fun u => (hsym _ _ _).symm
  have r4 := (hsym (fun x => x - ν) w _).symm.trans (r2 (fc b μ (fun x => x - ν) w))
  rw [r4, r2]
  simp only [re_inner_self]

theorem main {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (hid : fc b μ (fun x => x) = casimirK ε E)
    (κ c : ℝ) (s : ℕ) (c0 C cs ν : ℝ) (hc0 : 0 < c0) (hC : 0 ≤ C) (hcs0 : 0 ≤ cs)
    (hsC : c + 1 ≤ (s : ℝ) ^ 2 * c0 / 4 - s * C)
    (hν0 : 0 ≤ ν) (hνc : cs * C ≤ ν) (v : V) (hv : Eig ε E ν v)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - cs * y ^ 4 ≤ ((1 + y) ^ s)⁻¹)
    (hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2)
    (h8 : c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2 ≤ ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2)
    (h9a : ‖∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)‖ ≤ C * (1 + ν) * ‖v‖ ^ 2)
    (h9b : ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ C * (1 + ν) ^ 3 * ‖v‖ ^ 2) :
    ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have ha : 0 < ((1 + ν) ^ s)⁻¹ := by positivity
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hT : ∀ u, fc b μ (fun x => x - ν) u = casimirK ε E u - (ν : ℂ) • u := by
    intro u
    have hf : (fun x : ℝ => x - ν) = fun x => x + -ν := by funext x; ring
    rw [hf, hadd (fun x => x) (fun _ => -ν), hid, hconst]
    simp [sub_eq_add_neg]
  have hTE : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (E p.1 p.2 v) = Z ε E p.1 p.2 v := by
    intro p
    rw [hT, Z, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hTZ : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (Z ε E p.1 p.2 v) =
      (casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v := by
    intro p
    rw [hT, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hp : ∀ p ∈ nc ε,
      ((1 + ν) ^ s)⁻¹ * ‖E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)).re
        + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ‖Z ε E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4))
          * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ (inner ℂ (E p.1 p.2 v) (fc b μ (fun x => ((1 + x) ^ s)⁻¹) (E p.1 p.2 v))).re := by
    intro p _
    have := hmono (fun x => ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν))))
      (fun x => ((1 + x) ^ s)⁻¹) (fun x hx => phi_lb s cs ν x hν0 hx hA) (E p.1 p.2 v)
    rw [fc_poly hsym hadd hmul hconst, hTE, hTZ] at this
    exact this
  unfold beta
  rw [Complex.re_sum]
  refine le_trans ?_ (Finset.sum_le_sum hp)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum, hE]
  have hN : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hR := le_trans (Complex.re_le_norm _) h9a
  have hk1 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * s / (1 + ν) := by positivity
    linarith
  have hk2 : 0 ≤ ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) := by positivity
  have hk4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4 := by positivity
    linarith
  have i2 := mul_le_mul_of_nonpos_left hR hk1
  have i3 := mul_le_mul_of_nonneg_left h8 hk2
  have i4 := mul_le_mul_of_nonpos_left h9b hk4
  have e2 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) * (C * (1 + ν) * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (s * C) * ‖v‖ ^ 2) := by
    field_simp
  have e3 : ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) * (c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2)
      = ((1 + ν) ^ s)⁻¹ * ((s : ℝ) ^ 2 * c0 / 4) * ‖v‖ ^ 2 := by
    field_simp
  have e4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) * (C * (1 + ν) ^ 3 * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (cs * C / (1 + ν)) * ‖v‖ ^ 2) := by
    field_simp
  rw [e2] at i2
  rw [e3] at i3
  rw [e4] at i4
  have b4 : cs * C / (1 + ν) ≤ 1 := (div_le_one h1).2 (by linarith)
  have hb4 := mul_le_mul_of_nonneg_left b4 (mul_nonneg ha.le hN)
  have hs := mul_le_mul_of_nonneg_left hsC (mul_nonneg ha.le hN)
  nlinarith

end EigenGainPolynomial

theorem eigen_gain_of_moments : A0 → A8 → A9 → A10 → FunctionalCalculusLaws → A12 := by
  intro h0 h8 h9 h10 h11 n ε V _ _ E hM ι b μ hB κ hκ c hc
  obtain ⟨-, -, -, hnorm⟩ := h0 n ε V E hM
  obtain ⟨c0, x1, hc0, h8'⟩ := h8 n ε V E hM
  obtain ⟨C, hC, h9'⟩ := h9 n ε V E hM
  obtain ⟨-, hsym, hmono, hadd, hmul, hconst, hid⟩ := h11 n ε V E hM ι b μ hB
  obtain ⟨cs, hcs, h10'⟩ := h10 (⌈4 * (C + c + 1) / c0⌉₊ + 1) (by omega)
  refine ⟨⌈4 * (C + c + 1) / c0⌉₊ + 1, max 0 (max x1 (cs * C)), by omega, le_max_left _ _, ?_⟩
  intro ν v hν hv
  have hν0 : 0 ≤ ν := le_trans (le_max_left _ _) hν
  have hνx : x1 ≤ ν := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hν
  have hνc : cs * C ≤ ν := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hν
  have hsC : c + 1 ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) ^ 2 * c0 / 4
      - ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * C := by
    have hce := Nat.le_ceil (4 * (C + c + 1) / c0)
    have hsc : 4 * (C + c + 1) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * c0 := by
      have := (div_le_iff₀ hc0).1 hce
      push_cast
      nlinarith
    have hs1 : (1 : ℝ) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 * (C + c + 1) / c0⌉₊]
    nlinarith
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2 := by
    rw [(hnorm κ hκ v).2.1, hv', inner_smul_right, Complex.re_ofReal_mul, EigenGainPolynomial.re_inner_self]
    ring
  obtain ⟨h9a, h9b⟩ := h9' ν v hν0 hv
  exact EigenGainPolynomial.main hsym hmono hadd hmul hconst hid κ c _ c0 C cs ν hc0 hC hcs hsC hν0 hνc v hv h10'
    hE (h8' ν v hνx hv) h9a h9b

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace PMaxPr

theorem hilbert_schmidt_nonneg_alt {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

def evalAt {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : V →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : Matrix (Fin n) (Fin n) ℂ => ℂ) g).comp F

@[simp] theorem evalAt_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (v : V) : evalAt g F v = F v g := rfl

theorem sq_bound (x C w : ℝ) (N : ℕ) (h : x ≤ C * w ^ N) (hx : 0 ≤ x) : x ^ 2 ≤ C ^ 2 * w ^ (2 * N) := by
  calc x ^ 2 ≤ (C * w ^ N) ^ 2 := pow_le_pow_left₀ hx h 2
    _ = C ^ 2 * w ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm N 2]

end PMaxPr

open PMaxPr in
theorem maxPr_of : CasimirIsRealScalar → EigenbasisExists → A13 → UnitaryGroupFacts → MaximumPrincipleVar → SumSquaresSecondDerivative → B5 → MaxPr := by
  intro hA3c hA11a hA13 _ hB4a hB4b hB5 n ε V _ _ E hM N
  classical
  obtain ⟨κ, hκ⟩ := hA3c n ε V E hM
  obtain ⟨ι, b, μ, hb⟩ := hA11a n ε V E hM
  obtain ⟨c, hc0, hc⟩ := hB4a n ε (2 * N)
  obtain ⟨s, x₀, C₁, hs, hC₁, h13⟩ := hA13 n ε V E hM ι b μ hb κ hκ (c / 2) (div_nonneg hc0 (by norm_num))
  have hTfin : {i | μ i < x₀}.Finite := (hb.fin x₀).subset fun i (hi : μ i < x₀) => show μ i ≤ x₀ from le_of_lt hi
  have hT : ∀ i, i ∈ hTfin.toFinset ↔ μ i < x₀ := fun i => by simp
  have hW1 : 0 ≤ (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    pow_nonneg (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) _
  have hKK : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) hW1
  refine ⟨s, Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)),
    hTfin.toFinset.image b, Real.sqrt_nonneg _, ?_⟩
  intro F hcont hder hgrow B hB hI v
  have hA0 : 0 ≤ 2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) (Nat.cast_nonneg _)) (sq_nonneg B)
  choose Cf hCf using hgrow
  have key : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) →
      ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) 1‖ ^ 2 ≤
        (Real.sqrt (2 * C₁ * hTfin.toFinset.card * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (2 * N)) * B) ^ 2 := by
    intro R S hS
    have hcu : ContinuousOn (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) (UJset ε) :=
      continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hcont (b i)).norm.pow 2)
    have hgu : ∃ C : ℝ, ∀ g ∈ UJset ε,
        (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) ≤ C * (1 + hs2 g) ^ (2 * N) := by
      refine ⟨∑ i ∈ S, phiR s R (μ i) * Cf (b i) ^ 2, fun g hg => ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sq_bound _ _ _ _ (hCf (b i) g hg) (norm_nonneg _)) (le_max_right _ _)
    have hdu : ∀ g ∈ UJset ε, ∃ d : Fin n × Fin n → ℝ,
        (∀ p ∈ nc ε, ∃ u' : ℝ → ℝ, (∀ t, HasDerivAt (fun t : ℝ =>
          ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2))‖ ^ 2) (u' t) t) ∧
          HasDerivAt u' (d p) 0) ∧
        c * (∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) -
          2 * C₁ * (hTfin.toFinset.card : ℝ) * B ^ 2 * (1 + hs2 g) ^ (2 * N) ≤ ∑ p ∈ nc ε, d p := by
      intro g hg
      obtain ⟨d, hd, hsum⟩ := hB4b n ε V E hM ι b μ hb κ hκ F hder S (fun i => phiR s R (μ i)) g hg
      refine ⟨d, hd, ?_⟩
      rw [hsum]
      have h13g := h13 R (evalAt g F) S hTfin.toFinset hS hT
      simp only [evalAt_apply] at h13g
      have hTb : ∑ i ∈ hTfin.toFinset, ‖F (b i) g‖ ^ 2 ≤
          hTfin.toFinset.card • (B ^ 2 * (1 + hs2 g) ^ (2 * N)) :=
        Finset.sum_le_card_nsmul _ _ _ fun i hi =>
          sq_bound _ _ _ _ (hI (b i) (Finset.mem_image_of_mem b hi) g hg) (norm_nonneg _)
      rw [nsmul_eq_mul] at hTb
      have h2 := mul_le_mul_of_nonneg_left hTb hC₁
      nlinarith [h2, h13g]
    have h1 := hc (fun g => ∑ i ∈ S, phiR s R (μ i) * ‖F (b i) g‖ ^ 2) _ hA0 hcu hgu hdu
    calc _ ≤ _ := h1
      _ = _ := by rw [mul_pow, Real.sq_sqrt hKK]; ring
  have h5 := hB5 n ε V E hM ι b μ hb (evalAt 1 F) s _
    (mul_nonneg (Real.sqrt_nonneg _) hB) (fun R S hS => by simpa only [evalAt_apply] using key R S hS) hs v
  simpa only [evalAt_apply] using h5

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirRealScalar

variable {n : ℕ}

theorem casimir_eq_trace {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) :
    casimir E = (Mm E ^ 2).trace := by
  unfold casimir Mm
  rw [sq, Matrix.trace]
  simp [Matrix.diag, Matrix.mul_apply]

theorem term_im {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E) (a b : Fin n) (v : V) :
    (inner ℂ v (E a b (E b a v))).im = 0 := by
  rw [← inner_conj_symm, hu a b, Complex.conj_im, neg_eq_zero]
  have h1 : (adjSign ε a b).im = 0 := by
    unfold adjSign
    split_ifs <;> simp
  have h2 : (inner ℂ (E b a v) (E b a v)).im = 0 := inner_self_im (𝕜 := ℂ) _
  rw [Complex.mul_im, h1, h2]
  ring

theorem cas_im {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E) (v : V) :
    (inner ℂ v (casimir E v)).im = 0 := by
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, inner_sum, Complex.im_sum]
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => term_im ε E hu a b v

end CasimirRealScalar

theorem casimir_real_of_central : A2 → A3 → CasimirIsRealScalar := by
  intro h2 h3
  unfold CasimirIsRealScalar ForMod
  intro n ε V _ _ E h
  have hc : ∀ a b, E a b * casimir E = casimir E * E a b := by
    intro a b
    rw [CasimirRealScalar.casimir_eq_trace]
    exact h2 n ε V E h 2 a b
  obtain ⟨c, hc'⟩ := h3 n ε V E h (casimir E) hc
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have him := CasimirRealScalar.cas_im ε E h.uni v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hcim : c.im = 0 := by
    rw [hc', inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.mul_im] at him
    have hre : ((‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have him2 : ((‖v‖ : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    erw [hre, him2, mul_zero, zero_add] at him
    rcases mul_eq_zero.mp him with h0 | h0
    · exact h0
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h0) hn
  refine ⟨c.re, fun w => ?_⟩
  rw [hc' w]
  congr 1
  apply Complex.ext <;> simp [hcim]

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirPowerCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_pow (E : Fin n → Fin n → Module.End ℂ V) (hE : IsGlRep E) (c d : Fin n) :
    ∀ (k : ℕ) (a b : Fin n), E c d * (Mm E ^ k) a b - (Mm E ^ k) a b * E c d =
      (if d = a then (Mm E ^ k) c b else 0) - (if b = c then (Mm E ^ k) a d else 0) := by
  have hM : ∀ i j, Mm E i j = E i j := fun _ _ => rfl
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [pow_zero, Matrix.one_apply]
    have h0 : (if d = a then (if c = b then (1 : Module.End ℂ V) else 0) else 0) =
        (if b = c then (if a = d then 1 else 0) else 0) := by
      by_cases h2 : d = a
      · subst h2
        by_cases h3 : b = c
        · subst h3; simp
        · simp [h3, Ne.symm h3]
      · simp [h2, Ne.symm h2]
    rw [h0, sub_self]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    have key : ∀ j, E c d * ((Mm E ^ k) a j * E j b) - ((Mm E ^ k) a j * E j b) * E c d
        = (E c d * (Mm E ^ k) a j - (Mm E ^ k) a j * E c d) * E j b
          + (Mm E ^ k) a j * (E c d * E j b - E j b * E c d) := by
      intro j; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, hM]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [key, ih, hE c d]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : d = a <;> by_cases h2 : b = c <;> simp [h1, h2] <;> abel

end CasimirPowerCommute

theorem gelfand_central_holds : A2 := by
  intro n ε V _ _ E h k c d
  have hc := CasimirPowerCommute.comm_pow E h.gl c d k
  rw [← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Matrix.diag_apply, hc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end PositivityTheory.CW

end
end
