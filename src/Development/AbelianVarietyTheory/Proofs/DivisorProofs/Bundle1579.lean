module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.EigenvalueNormSignature

theorem form_mulVec {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star (M *ᵥ x) ⬝ᵥ A *ᵥ (M *ᵥ y) = star x ⬝ᵥ (Mᴴ * A * M) *ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_ne_zero_of_sig {n : ℕ} {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (hs : sigPosH hh + sigNegH hh = n) : h.det ≠ 0 := by
  intro hd
  rw [hh.det_eq_prod_eigenvalues] at hd
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hd
  have hi0 : hh.eigenvalues i = 0 := by simpa using hi
  unfold sigPosH sigNegH at hs
  have hdis : Disjoint (fun j : Fin n => 0 < hh.eigenvalues j) (fun j => hh.eigenvalues j < 0) := by
    rw [Pi.disjoint_iff]; intro j
    simp only [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩; linarith
  rw [← Fintype.card_subtype_or_disjoint _ _ hdis] at hs
  have hlt : Fintype.card {j : Fin n // 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0} < Fintype.card (Fin n) :=
    Fintype.card_subtype_lt (p := fun j => 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0) (x := i)
      (by rw [hi0]; simp)
  rw [Fintype.card_fin] at hlt
  omega

end GlobalTheory.EigenvalueNormSignature

namespace GlobalTheory


open GlobalTheory.EigenvalueNormSignature in
theorem eig_norm_sq_of_similitude : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  intro n h Q Γ hh Z c hle hs hQ hc hΓ hcase w x hx hw
  have hdet := det_ne_zero_of_sig hh hs
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hZinj : ∀ v : Fin n → ℂ, v ≠ 0 → Zm *ᵥ v ≠ 0 := by
    intro v hv h0
    apply hv
    have : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ (Zm *ᵥ v) = v := by
      rw [mulVec_mulVec, hZm, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hB : ∀ u v : Fin n → ℂ, star u ⬝ᵥ Q *ᵥ v = star (Zm *ᵥ u) ⬝ᵥ h *ᵥ (Zm *ᵥ v) := by
    intro u v; rw [form_mulVec, hQ]

  have hsim : ∀ (a b : ℂ) (u v : Fin n → ℂ), Γ *ᵥ u = a • u → Γ *ᵥ v = b • v →
      (star a * b - c) * (star u ⬝ᵥ Q *ᵥ v) = 0 := by
    intro a b u v hu hv
    have e := form_mulVec Γ Q u v
    rw [hΓ, hu, hv] at e
    simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_mulVec] at e
    rw [RCLike.star_def] at e ⊢
    linear_combination e
  have hnorm : ∀ a : ℂ, star a * a = (c : ℂ) → ‖a‖ ^ 2 = c := by
    intro a ha
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = c := by
      rw [← ha, RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this
  by_cases hq : star x ⬝ᵥ Q *ᵥ x = 0
  · rcases hcase with h0 | ⟨μ, x₀, hμ, hpos⟩
    · have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x) (hZinj x hx)
      rw [← hB, hq] at this; simp at this
    · have h1 : sigPosH hh = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · have hx₀ : x₀ ≠ 0 := by rintro rfl; simp at hpos
          have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x₀) (hZinj x₀ hx₀)
          rw [← hB] at this; linarith
        · exact h1
      have hμμ := hsim μ μ x₀ x₀ hμ hμ
      have hq0 : star x₀ ⬝ᵥ Q *ᵥ x₀ ≠ 0 := fun e => by rw [e] at hpos; simp at hpos
      have hμc : star μ * μ = (c : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hμμ).resolve_right hq0)
      by_cases hb : star x₀ ⬝ᵥ Q *ᵥ x = 0
      · have := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet h1 (Zm *ᵥ x₀) (Zm *ᵥ x)
          (by rw [← hB]; exact hpos) (by rw [← hB]; exact hb) (hZinj x hx)
        rw [← hB, hq] at this; simp at this
      · have hμw := sub_eq_zero.mp ((mul_eq_zero.mp (hsim μ w x₀ x hμ hw)).resolve_right hb)
        have hμ0 : star μ ≠ 0 := by
          intro e; rw [e, zero_mul] at hμc; exact hc (by exact_mod_cast hμc.symm)
        have hwμ : w = μ := mul_left_cancel₀ hμ0 (hμw.trans hμc.symm)
        rw [hwμ]; exact hnorm μ hμc
  · exact hnorm w (sub_eq_zero.mp ((mul_eq_zero.mp (hsim w w x x hw hw)).resolve_right hq))

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.PositiveDefiniteFormIdentities

theorem form_pull {n : ℕ} (h Z : Matrix (Fin n) (Fin n) ℂ) (v v' : Fin n → ℂ) :
    star (Z *ᵥ v) ⬝ᵥ h *ᵥ (Z *ᵥ v') = star v ⬝ᵥ (Zᴴ * h * Z) *ᵥ v' := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem form_swap {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ Q *ᵥ x = star (star x ⬝ᵥ Q *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hQ.eq, ← dotProduct_mulVec]

theorem form_expand {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (w z : Fin n → ℂ) (a : ℂ)
    (hwz : star z ⬝ᵥ Q *ᵥ w = 0) :
    star (w + a • z) ⬝ᵥ Q *ᵥ (w + a • z) =
      star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * (star z ⬝ᵥ Q *ᵥ z) := by
  have hzw : star w ⬝ᵥ Q *ᵥ z = 0 := by rw [form_swap hQ, hwz, star_zero]
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hwz, hzw, smul_eq_mul, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  ring

theorem form_self_ofReal {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x : Fin n → ℂ) :
    ((star x ⬝ᵥ Q *ᵥ x).re : ℂ) = star x ⬝ᵥ Q *ᵥ x := by
  have h := form_swap hQ x x
  exact Complex.conj_eq_iff_re.mp h.symm

end GlobalTheory.PositiveDefiniteFormIdentities

namespace GlobalTheory


open GlobalTheory.PositiveDefiniteFormIdentities in
theorem similitude_preserves_posDef : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  intro n h Q M hh Z s hdet hsig hQZ hs hsim z c hz hMz
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hQ : Q.IsHermitian := by
    rw [hQZ]
    simp [IsHermitian, conjTranspose_mul, hh.eq, Matrix.mul_assoc]
  set q0 : ℝ := (star z ⬝ᵥ Q *ᵥ z).re with hq0
  have hq : star z ⬝ᵥ Q *ᵥ z = (q0 : ℂ) := (form_self_ofReal hQ z).symm
  have hq0ne : (q0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  set u : Fin n → ℂ := Q *ᵥ z with hu
  set H : Matrix (Fin n) (Fin n) ℂ := ((2 / q0 : ℝ) : ℂ) • vecMulVec u (star u) - Q with hH
  have hsu : ∀ x : Fin n → ℂ, star u ⬝ᵥ x = star z ⬝ᵥ Q *ᵥ x := by
    intro x
    rw [hu, star_mulVec, ← dotProduct_mulVec, hQ.eq]
  have hus : ∀ x : Fin n → ℂ, star x ⬝ᵥ u = star (star z ⬝ᵥ Q *ᵥ x) := by
    intro x
    rw [hu, ← form_swap hQ]

  have hval : ∀ x : Fin n → ℂ, star x ⬝ᵥ H *ᵥ x =
      ((2 / q0 * Complex.normSq (star z ⬝ᵥ Q *ᵥ x) - (star x ⬝ᵥ Q *ᵥ x).re : ℝ) : ℂ) := by
    intro x
    rw [hH, sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, hsu, hus, smul_eq_mul, smul_eq_mul]
    have e := form_self_ofReal hQ x
    push_cast
    rw [e, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hHh : H.IsHermitian := by
    rw [hH]
    refine IsHermitian.sub ?_ hQ
    ext i j
    simp [vecMulVec_apply, mul_comm]
  have hpos : H.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hHh fun x hx => ?_
    rw [hval x]
    refine Complex.zero_lt_real.mpr ?_
    set p := star z ⬝ᵥ Q *ᵥ x with hp
    set a : ℂ := p / (q0 : ℂ) with ha
    have hpa : p = a * q0 := by rw [ha]; field_simp
    set w := x - a • z with hw
    have hxw : x = w + a • z := by rw [hw]; abel
    have hwz : star z ⬝ᵥ Q *ᵥ w = 0 := by
      rw [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hq, ← hp, hpa, sub_self]
    have hexp : star x ⬝ᵥ Q *ᵥ x = star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * q0 := by
      conv_lhs => rw [hxw]
      rw [form_expand hQ w z a hwz, hq]
    have hre : (star x ⬝ᵥ Q *ᵥ x).re = (star w ⬝ᵥ Q *ᵥ w).re + Complex.normSq a * q0 := by
      rw [hexp, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hnp : Complex.normSq p = Complex.normSq a * q0 ^ 2 := by
      rw [hpa, Complex.normSq_mul, Complex.normSq_ofReal]; ring
    have h2 : 2 / q0 * (Complex.normSq a * q0 ^ 2) = 2 * Complex.normSq a * q0 := by
      field_simp
    rw [hre, hnp, h2]
    by_cases hw0 : w = 0
    · have ha0 : a ≠ 0 := by
        intro ha0
        apply hx
        rw [hxw, hw0, ha0, zero_smul, add_zero]
      have e : (star w ⬝ᵥ Q *ᵥ w).re = 0 := by simp [hw0]
      rw [e]
      nlinarith [Complex.normSq_pos.mpr ha0]
    · have hZw : Zm *ᵥ w ≠ 0 := by
        intro h0
        apply hw0
        have hinv : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm = 1 := Units.inv_mul Z
        calc w = (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm) *ᵥ w := by rw [hinv, one_mulVec]
          _ = 0 := by rw [← mulVec_mulVec, h0, mulVec_zero]
      have hneg := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet hsig (Zm *ᵥ z) (Zm *ᵥ w)
        (by rw [form_pull, ← hQZ]; exact hz) (by rw [form_pull, ← hQZ]; exact hwz) hZw
      rw [form_pull, ← hQZ] at hneg
      nlinarith [Complex.normSq_nonneg a]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hc : star c * c = (s : ℂ) := by
    have e1 := congrArg (fun A => star z ⬝ᵥ A *ᵥ z) hsim
    rw [← form_pull Q M z z, hMz] at e1
    simp only [star_smul, mulVec_smul, smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1
    rw [← hu, hq] at e1
    have e3 : (star c * c - s) * (q0 : ℂ) = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hq0ne)
  have hMu : Mᴴ *ᵥ u = star c • u := by
    have e2 := congrArg (fun A => A *ᵥ z) hsim
    rw [← mulVec_mulVec, ← mulVec_mulVec, hMz, mulVec_smul, mulVec_smul, smul_mulVec, ← hu] at e2
    apply smul_right_injective _ hs0
    change (s : ℂ) • (Mᴴ *ᵥ u) = (s : ℂ) • (star c • u)
    calc (s : ℂ) • (Mᴴ *ᵥ u) = star c • (c • Mᴴ *ᵥ u) := by rw [smul_smul, hc]
      _ = star c • ((s : ℂ) • u) := by rw [e2]
      _ = (s : ℂ) • (star c • u) := smul_comm _ _ _
  have hstar : star u ᵥ* M = c • star u := by
    have e : star (Mᴴ *ᵥ u) = star u ᵥ* M := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [← e, hMu, star_smul, star_star]
  have hM1 : Mᴴ * vecMulVec u (star u) * M = (s : ℂ) • vecMulVec u (star u) := by
    rw [mul_vecMulVec, vecMulVec_mul, hMu, hstar, ← hc]
    ext i j
    simp [vecMulVec_apply]
    ring
  refine ⟨H, hpos, ?_⟩
  rw [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hM1, hsim, smul_sub,
    smul_comm ((2 / q0 : ℝ) : ℂ) (s : ℂ)]

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem diag_sign_of_pos_eigenvector : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  intro n A h g hA W Z lam d hdet hsig hh hZ hlam hg i₀ x hx hxpos
  have key : ∀ (N B : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ),
      star (N *ᵥ u) ⬝ᵥ B *ᵥ (N *ᵥ u') = star u ⬝ᵥ (Nᴴ * B * N) *ᵥ u' := by
    intro N B u u'
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  set M : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ) * (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  have hMd : Mᴴ * A * M = diagonal (fun i => (d i : ℂ)) := by
    rw [← hZ, hh, hM, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨y, rfl⟩ : ∃ y, x = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y :=
    ⟨(↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
  have hy : ∀ i, i ≠ i₀ → y i = 0 := by
    have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (diagonal lam *ᵥ y)
        = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (lam i₀ • y) := by
      rw [mulVec_mulVec, ← hg, ← mulVec_mulVec, hx, mulVec_smul]
    have h2 : diagonal lam *ᵥ y = lam i₀ • y := by
      have := congrArg (fun v => (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) h1
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, one_mulVec] using this
    intro i hi
    have h3 := congrFun h2 i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h3
    have h4 : (lam i - lam i₀) * y i = 0 := by rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (hlam (sub_eq_zero.mp h5)) hi
    · exact h5
  have hform : star ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) ⬝ᵥ h *ᵥ ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y)
      = ((d i₀ * Complex.normSq (y i₀) : ℝ) : ℂ) := by
    rw [key, hZ]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hy i hi]) (by simp)]
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  rw [hform, Complex.ofReal_re] at hxpos
  have hd0 : 0 < d i₀ := by
    by_contra hc
    push_neg at hc
    nlinarith [Complex.normSq_nonneg (y i₀)]
  refine ⟨hd0, fun i hi => ?_⟩
  have hNM : ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) * M = 1 := by
    rw [hM, Matrix.mul_assoc, ← Matrix.mul_assoc (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ), Units.inv_mul,
      Matrix.one_mul, Units.inv_mul]
  have hval : ∀ j k : Fin n, star (M *ᵥ Pi.single j 1) ⬝ᵥ A *ᵥ (M *ᵥ Pi.single k 1)
      = if j = k then (d j : ℂ) else 0 := by
    intro j k
    rw [key, hMd]
    by_cases hjk : j = k
    · subst hjk; simp [dotProduct, mulVec_diagonal, Pi.single_apply]
    · simp [dotProduct, mulVec_diagonal, Pi.single_apply, hjk]
      intro hkj; exact absurd hkj.symm hjk
  have hne : M *ᵥ Pi.single i (1 : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (fun v => ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) h0
    simp only [mulVec_mulVec, hNM, one_mulVec, mulVec_zero] at this
    have := congrFun this i
    simp at this
  have hneg := re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig (M *ᵥ Pi.single i₀ 1)
    (M *ᵥ Pi.single i 1) (by rw [hval]; simpa using hd0) (by rw [hval, if_neg (Ne.symm hi)]) hne
  rw [hval, if_pos rfl, Complex.ofReal_re] at hneg
  exact hneg

end GlobalTheory
end

section

open Matrix GlobalTheory.LKTrip

namespace GlobalTheory.HermitianMajorantIdentities

theorem mul_vecMulVec_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    A * vecMulVec u v * B = vecMulVec (A *ᵥ u) (v ᵥ* B) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem form_vecMulVec {n : ℕ} (u x : Fin n → ℂ) :
    star x ⬝ᵥ vecMulVec u (star u) *ᵥ x = (star x ⬝ᵥ u) * (star u ⬝ᵥ x) := by
  rw [vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]

theorem herm_swap {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ H *ᵥ x = star (star x ⬝ᵥ H *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hH.eq, ← dotProduct_mulVec]

end GlobalTheory.HermitianMajorantIdentities

namespace GlobalTheory


open GlobalTheory.HermitianMajorantIdentities in
theorem exists_posDef_majorant_of_sigPosH_eq_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  intro n H hH hdet hsig z hz
  set a : ℝ := (star z ⬝ᵥ H *ᵥ z).re with ha
  have hzz : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := by
    have h := herm_swap hH z z
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  set u : Fin n → ℂ := H *ᵥ z with hu
  have hux : ∀ x, star u ⬝ᵥ x = star z ⬝ᵥ H *ᵥ x := by
    intro x; rw [hu, star_mulVec, hH.eq, ← dotProduct_mulVec]
  refine ⟨((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, hH.eq, conjTranspose_vecMulVec, star_star]
    simp [Complex.star_def]
  · intro x hx
    set q := star z ⬝ᵥ H *ᵥ x with hq
    set t : ℂ := q / (a : ℂ) with ht
    set x' := x - t • z with hx'
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hzx' : star z ⬝ᵥ H *ᵥ x' = 0 := by
      rw [hx', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hzz, ← hq, ht, smul_eq_mul]
      field_simp; ring
    have hx'z : star x' ⬝ᵥ H *ᵥ z = 0 := by
      rw [herm_swap hH z x', hzx', star_zero]
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have hxe : x = t • z + x' := by rw [hx']; abel
    have hxx : star x ⬝ᵥ H *ᵥ x = star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x' := by
      conv_lhs => rw [hxe]
      simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hzx', hx'z, hzz']
      ring
    have hxz : star x ⬝ᵥ H *ᵥ z = star q := herm_swap hH z x
    have hP : star x ⬝ᵥ (((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H) *ᵥ x
        = ((2 / a : ℝ) : ℂ) * (star q * q) - (star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x') := by
      rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, form_vecMulVec, hux, hxx,
        smul_eq_mul]
      rw [show star x ⬝ᵥ u = star q from hxz]
    have hqt : q = t * (a : ℂ) := by rw [ht]; field_simp
    have hnt : star t * t = ((Complex.normSq t : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hP, hqt, star_mul', Complex.star_def, Complex.conj_ofReal]
    have e1 : ((starRingEnd ℂ) t * (a : ℂ) * (t * (a : ℂ))) = ((Complex.normSq t * a * a : ℝ) : ℂ) := by
      rw [← Complex.star_def, show star t * (a:ℂ) * (t * (a:ℂ)) = (star t * t) * ((a * a : ℝ) : ℂ) by push_cast; ring, hnt]
      push_cast; ring
    rw [e1, ← Complex.star_def, hnt]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_mul]
    have hapos : 0 < a := hz
    by_cases h0 : x' = 0
    · have htne : t ≠ 0 := by
        intro ht0
        apply hx
        rw [hxe, h0, ht0, zero_smul, add_zero]
      have hnpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr htne
      rw [h0]
      simp only [star_zero, zero_dotProduct, Complex.zero_re, add_zero]
      field_simp
      nlinarith [mul_pos hnpos hapos]
    · have hneg := re_form_neg_of_orth_of_sigPosH_eq_one H hH hdet hsig z x' hz hzx' h0
      have hn0 : 0 ≤ Complex.normSq t := Complex.normSq_nonneg t
      have : 2 / a * (Complex.normSq t * a * a) - Complex.normSq t * a = Complex.normSq t * a := by
        field_simp; ring
      nlinarith [mul_nonneg hn0 hapos.le]
  · intro Y s c hs hY hYz
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hA : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = (s : ℂ) * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hY,
        smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hB : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = star c * (star z ⬝ᵥ H *ᵥ (Y *ᵥ x)) := by
      intro x
      rw [hYz, star_smul, smul_dotProduct, smul_eq_mul]
    have hsc : (s : ℂ) = star c * c := by
      have h1 := (hA z).symm.trans (hB z)
      rw [hYz, mulVec_smul, dotProduct_smul, smul_eq_mul, hzz'] at h1
      have h2 : ((s : ℂ) - star c * c) * (a : ℂ) = 0 := by rw [sub_mul, h1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha0)
    have hc0 : star c ≠ 0 := by
      intro h0
      have : (s : ℂ) = 0 := by rw [hsc, h0, zero_mul]
      exact hs.ne' (by exact_mod_cast this)
    have hrow : ∀ x, star z ⬝ᵥ H *ᵥ (Y *ᵥ x) = c * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      have h1 := (hA x).symm.trans (hB x)
      rw [hsc, mul_assoc] at h1
      exact (mul_left_cancel₀ hc0 h1).symm
    have hrowv : star u ᵥ* Y = c • star u := by
      funext j
      have h1 : (star u ᵥ* Y) ⬝ᵥ Pi.single j 1 = (c • star u) ⬝ᵥ Pi.single j 1 := by
        rw [← dotProduct_mulVec, hux, hrow, smul_dotProduct, hux, smul_eq_mul]
      simpa [dotProduct_single] using h1
    have hcolv : Yᴴ *ᵥ u = star c • u := by
      have h1 := congrArg star hrowv
      rw [star_vecMul, star_star, star_smul, star_star] at h1
      exact h1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul', hcolv,
      hrowv, hY]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hsc]
    ring

end GlobalTheory
end
