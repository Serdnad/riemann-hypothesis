module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle003
public import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem fac_eq_zero_of_smul (t : ℕ × ℕ × ℕ) (τ : ℍ) (γ : SL(2, ℤ))
    (h : γ • pt t.1 t.2.1 t.2.2 τ = τ) : fac t τ = 0 := by
  unfold fac
  have h1 : AA τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * AA (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← AA_smul, h]
  have h2 : DD τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * DD (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← DD_smul, h]
  rw [h1, h2]
  ring

private lemma exists_SL2_mul_eq_Tmat_of_det_eq {m : ℕ} (hm : 0 < m) (A B C D : ℤ) (hdet : A * D - B * C = m) :
    ∃ g : SL(2, ℤ), ∃ s ∈ Tm m, 0 < s.2.2 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) * !![A, B; C, D] = Tmat s := by
  have hAC : A ≠ 0 ∨ C ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (m : ℤ) = 0 := by rw [← hdet, hc.1, hc.2]; ring
    omega
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = Int.gcd A C := ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    first
    | exact Int.gcd_pos_iff.mpr hAC
    | (rcases hAC with h | h
       · exact Int.gcd_pos_of_ne_zero_left C h
       · exact Int.gcd_pos_of_ne_zero_right A h)
  obtain ⟨a0, ha0⟩ : (G : ℤ) ∣ A := by
    rw [hG]
    first | exact Int.gcd_dvd_left | exact Int.gcd_dvd_left A C | exact Int.gcd_dvd_left _ _
  obtain ⟨c0, hc0⟩ : (G : ℤ) ∣ C := by
    rw [hG]
    first | exact Int.gcd_dvd_right | exact Int.gcd_dvd_right A C | exact Int.gcd_dvd_right _ _
  obtain ⟨x, y, hbez⟩ : ∃ x y : ℤ, (G : ℤ) = A * x + C * y :=
    ⟨_, _, by rw [hG]; exact Int.gcd_eq_gcd_ab A C⟩
  have hG0 : (G : ℤ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have h1 : a0 * x + c0 * y = 1 := by
    apply mul_left_cancel₀ hG0
    linear_combination -hbez - x * ha0 - y * hc0
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = a0 * D - c0 * B := ⟨_, rfl⟩
  have hGd : (G : ℤ) * d = m := by
    rw [hd]
    linear_combination hdet - D * ha0 + B * hc0
  have hdpos : 0 < d := by
    have h2 : 0 < (G : ℤ) * d := by rw [hGd]; exact_mod_cast hm
    have h3 : (0 : ℤ) < G := by exact_mod_cast hGpos
    by_contra h4
    push_neg at h4
    nlinarith
  obtain ⟨q, b, hdiv, hb0, hbd⟩ : ∃ q b : ℤ, d * q + b = x * B + y * D ∧ 0 ≤ b ∧ b < d :=
    ⟨(x * B + y * D) / d, (x * B + y * D) % d,
      (by first
          | (have h5 := Int.emod_add_ediv (x * B + y * D) d; linarith)
          | (have h5 := Int.ediv_add_emod' (x * B + y * D) d; linarith)
          | (have h5 := Int.mul_ediv_add_emod (x * B + y * D) d; linarith)), Int.emod_nonneg _ hdpos.ne',
      Int.emod_lt_of_pos _ hdpos⟩
  have hdet1 : (x + q * c0) * a0 - (y - q * a0) * -c0 = 1 := by linear_combination h1
  have e1 : (x + q * c0) * A + (y - q * a0) * C = (G : ℤ) := by
    linear_combination -hbez + q * c0 * ha0 - q * a0 * hc0
  have e2 : (x + q * c0) * B + (y - q * a0) * D = b := by
    linear_combination -hdiv + q * hd
  have e3 : -c0 * A + a0 * C = 0 := by
    linear_combination -c0 * ha0 + a0 * hc0
  have e4 : -c0 * B + a0 * D = d := by
    linear_combination -hd
  lift d to ℕ using hdpos.le
  lift b to ℕ using hb0
  have hGdn : G * d = m := by exact_mod_cast hGd
  have hmd : m / G = d := by rw [← hGdn, Nat.mul_div_cancel_left _ hGpos]
  refine ⟨⟨!![x + q * c0, y - q * a0; -c0, a0], by rw [Matrix.det_fin_two_of]; exact hdet1⟩, (G, b, d), ?_, by show 0 < d; exact_mod_cast hdpos, ?_⟩
  · simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
    refine ⟨⟨G, b⟩, ⟨⟨⟨d, hGdn.symm⟩, hm.ne'⟩, ?_⟩, ?_⟩
    · rw [hmd]; exact_mod_cast hbd
    · simp [hmd]
  · show !![x + q * c0, y - q * a0; -c0, a0] * !![A, B; C, D] = Tmat (G, b, d)
    rw [Matrix.mul_fin_two, e1, e2, e3, e4]
    all_goals first | rfl | (unfold Tmat; rfl) | simp [Tmat]

theorem Gm_vanish {m : ℕ} (hm : 0 < m) (τ : ℍ) (A B C D : ℤ) (hdet : A * D - B * C = m)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : Gm m τ = 0 := by
  obtain ⟨g, s, hs, he, hgs⟩ := exists_SL2_mul_eq_Tmat_of_det_eq hm A B C D hdet
  obtain ⟨p, q, r, w, hg⟩ : ∃ p q r w : ℤ, (g : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdg : p * w - q * r = 1 := by
    have h0 := Matrix.SpecialLinearGroup.det_coe g
    rw [hg, Matrix.det_fin_two_of] at h0
    exact h0
  have hp : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by rw [hg]; rfl
  have hq : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q := by rw [hg]; rfl
  have hr : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by rw [hg]; rfl
  have hw : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = w := by rw [hg]; rfl
  rw [hg] at hgs
  unfold Tmat at hgs
  rw [Matrix.mul_fin_two] at hgs
  have e00 : p * A + q * C = ((s.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 0
  have e01 : p * B + q * D = ((s.2.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 1
  have e10 : r * A + w * C = 0 := congrFun (congrFun hgs 1) 0
  have e11 : r * B + w * D = ((s.2.2 : ℕ) : ℤ) := congrFun (congrFun hgs 1) 1
  have ea : (s.1 : ℂ) = p * A + q * C := by exact_mod_cast e00.symm
  have eb : (s.2.1 : ℂ) = p * B + q * D := by exact_mod_cast e01.symm
  have ez : (r : ℂ) * A + w * C = 0 := by exact_mod_cast e10
  have ee : (s.2.2 : ℂ) = r * B + w * D := by exact_mod_cast e11.symm
  have hE : (s.2.2 : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hden : (r : ℂ) * τ + w ≠ 0 := by
    intro h0
    have him : (r : ℝ) * τ.im = 0 := by
      have h3 := congrArg Complex.im h0
      simpa using h3
    have hτ := τ.im_pos
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp him with h4 | h4
      · exact_mod_cast h4
      · linarith
    rw [hr0] at h0
    have hw0 : w = 0 := by
      have h3 := congrArg Complex.re h0
      simp at h3
      exact_mod_cast h3
    rw [hr0, hw0] at hdg
    simp at hdg
  have c1 : ∀ z : ℤ, (((algebraMap ℤ ℝ) z : ℝ) : ℂ) = (z : ℂ) := by
    intro z
    rw [eq_intCast]
    push_cast
    rfl
  have hform : ((g • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hp, hq, hr, hw]
    try rw [c1 p, c1 q, c1 r, c1 w]
  have hX : ((s.1 : ℂ) * τ + (s.2.1 : ℂ)) / (s.2.2 : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    rw [div_eq_div_iff hE hden]
    linear_combination ((τ : ℂ) * (r * τ + w)) * ea + ((r : ℂ) * τ + w) * eb
      + ((p : ℂ) * (r * τ + w) - (p * τ + q) * r) * hfix + ((p : ℂ) * τ + q) * τ * ez
      - ((p : ℂ) * τ + q) * ee
  have hpt : pt s.1 s.2.1 s.2.2 τ = g • τ := by
    unfold pt
    rw [hX, ← hform]
    first
    | exact UpperHalfPlane.ofComplex_apply (g • τ)
    | simp
  unfold Gm
  apply Finset.prod_eq_zero hs
  apply fac_eq_zero_of_smul s τ g⁻¹
  rw [hpt, inv_smul_smul]

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem denom_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  first
  | rfl
  | simp [UpperHalfPlane.denom]
  | (simp [UpperHalfPlane.denom]; norm_cast)

theorem smul_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  first
  | (rw [UpperHalfPlane.coe_smul, UpperHalfPlane.num, denom_SL_coe]; simp)
  | (rw [UpperHalfPlane.specialLinearGroup_apply]; simp)
  | simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]

theorem pt_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    pt t.1 t.2.1 t.2.2 (γ • τ) = γ' • pt t'.1 t'.2.1 t'.2.2 τ ∧
      denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * denom γ τ := by
  have hm : ∀ i j, (Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') i j := fun i j => by rw [h]
  have z00 : (t.1 : ℤ) * γ 0 0 + (t.2.1 : ℤ) * γ 1 0 = γ' 0 0 * (t'.1 : ℤ) := by
    have hh := hm 0 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z01 : (t.1 : ℤ) * γ 0 1 + (t.2.1 : ℤ) * γ 1 1 = γ' 0 0 * (t'.2.1 : ℤ) + γ' 0 1 * (t'.2.2 : ℤ) := by
    have hh := hm 0 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z10 : (t.2.2 : ℤ) * γ 1 0 = γ' 1 0 * (t'.1 : ℤ) := by
    have hh := hm 1 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z11 : (t.2.2 : ℤ) * γ 1 1 = γ' 1 0 * (t'.2.1 : ℤ) + γ' 1 1 * (t'.2.2 : ℤ) := by
    have hh := hm 1 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have c00 : (t.1 : ℂ) * ((γ 0 0 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z00
  have c01 : (t.1 : ℂ) * ((γ 0 1 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 0 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z01
  have c10 : (t.2.2 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z10
  have c11 : (t.2.2 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 1 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z11
  have he : (t.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht.2.ne'
  have he' : (t'.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hD' : ((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hZ : ((γ • τ : ℍ) : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) = ((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ) := by
    rw [smul_SL_coe γ τ]; exact div_mul_cancel₀ _ hD
  have hW : ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) * (t'.2.2 : ℂ) = (t'.1 : ℂ) * (τ : ℂ) + (t'.2.1 : ℂ) := by
    rw [pt_coe ht'.1 ht'.2]; exact div_mul_cancel₀ _ he'
  have c2 : (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    linear_combination ((γ' 1 0 : ℤ) : ℂ) * hW - (τ : ℂ) * c10 - c11
  refine ⟨UpperHalfPlane.ext ?_, ?_⟩
  · rw [pt_coe ht.1 ht.2, smul_SL_coe γ' (pt t'.1 t'.2.1 t'.2.2 τ), div_eq_div_iff he hD']
    have key : ((t'.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) *
        (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) - (((γ' 0 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 0 1 : ℤ) : ℂ)) * (t.2.2 : ℂ)) = 0 := by
      linear_combination (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * c2 +
        ((t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * ((t.1 : ℂ) * hZ - ((γ' 0 0 : ℤ) : ℂ) * hW + (τ : ℂ) * c00 + c01)
    rcases mul_eq_zero.mp key with h0 | h0
    · exact absurd h0 (mul_ne_zero he' hD)
    · exact sub_eq_zero.mp h0
  · rw [denom_SL_coe, denom_SL_coe]
    exact c2

theorem fac_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    fac t (γ • τ) = denom γ τ ^ 24 * ((t.2.2 : ℂ) / t'.2.2) ^ 12 * fac t' τ := by
  obtain ⟨h1, h2⟩ := pt_smul ht ht' γ γ' h τ
  have he' : ((t'.2.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hd : denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) = (t.2.2 : ℂ) / t'.2.2 * denom γ τ := by
    rw [div_mul_eq_mul_div, eq_div_iff he']
    exact h2
  simp only [fac]
  rw [h1, AA_smul, DD_smul, AA_smul, DD_smul, hd]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_hermite_normal_form_coords {m : ℕ} (hm : 0 < m) (p q r s : ℤ) (h : p * s - q * r = m) :
    ∃ (x y z w : ℤ) (a b e : ℕ), x * w - y * z = 1 ∧ a * e = m ∧ b < e ∧
      p = x * a ∧ q = x * b + y * e ∧ r = z * a ∧ s = z * b + w * e := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set g : ℕ := Int.gcd p r with hg
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [hg, Int.gcd_eq_zero_iff] at h0
      rw [h0.1, h0.2] at h
      simp at h
      omega
    · exact h0
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  obtain ⟨x, hx⟩ : (g : ℤ) ∣ p := Int.gcd_dvd_left p r
  obtain ⟨z, hz⟩ : (g : ℤ) ∣ r := Int.gcd_dvd_right p r
  set u := Int.gcdA p r
  set v := Int.gcdB p r
  have hbez : (g : ℤ) = p * u + r * v := Int.gcd_eq_gcd_ab p r
  have h1 : x * u + z * v = 1 := by
    have : (g : ℤ) * (x * u + z * v) = g * 1 := by
      rw [mul_one]; conv_rhs => rw [hbez, hx, hz]
      ring
    exact mul_left_cancel₀ hgZ.ne' this
  set E : ℤ := x * s - z * q with hE
  have hgE : (g : ℤ) * E = m := by rw [← h, hx, hz, hE]; ring
  have hE0 : 0 < E := by
    by_contra hc
    have : (g : ℤ) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgZ.le (not_lt.mp hc)
    omega
  set b0 : ℤ := u * q + v * s with hb0
  have hmod0 : 0 ≤ b0 % E := Int.emod_nonneg _ hE0.ne'
  have hmod1 : b0 % E < E := Int.emod_lt_of_pos _ hE0
  have hdiv : b0 % E + E * (b0 / E) = b0 := Int.emod_add_mul_ediv b0 E
  set k := b0 / E
  set B := b0 % E
  have hEn : ((E.toNat : ℕ) : ℤ) = E := Int.toNat_of_nonneg hE0.le
  have hBn : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hmod0
  refine ⟨x, x * k - v, z, z * k + u, g, B.toNat, E.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · have : ((g * E.toNat : ℕ) : ℤ) = m := by push_cast; rw [hEn]; exact hgE
    exact_mod_cast this
  · omega
  · rw [hx]; ring
  · rw [hEn, hBn]
    have : x * B + (x * k - v) * E = x * b0 - v * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-q) * h1
  · rw [hz]; ring
  · rw [hEn, hBn]
    have : z * B + (z * k + u) * E = z * b0 + u * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-s) * h1

theorem hnf_exists {m : ℕ} (hm : 0 < m) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = m) :
    ∃ (γ : SL(2, ℤ)) (t : ℕ × ℕ × ℕ), t ∈ Tm m ∧ M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t := by
  rw [Matrix.det_fin_two] at hM
  obtain ⟨x, y, z, w, a, b, e, hdet, hae, hbe, h00, h01, h10, h11⟩ :=
    exists_hermite_normal_form_coords hm (M 0 0) (M 0 1) (M 1 0) (M 1 1) hM
  refine ⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, (a, b, e),
    (mem_Tm hm _).2 ⟨hae, hbe⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]

theorem hnf_unique {m : ℕ} (hm : 0 < m) {t t' : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (ht' : t' ∈ Tm m)
    (γ : SL(2, ℤ)) (h : Tmat t = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') : t = t' := by
  obtain ⟨a, b, e⟩ := t
  obtain ⟨a', b', e'⟩ := t'
  obtain ⟨hae, hbe⟩ := (mem_Tm hm _).1 ht
  obtain ⟨hae', hbe'⟩ := (mem_Tm hm _).1 ht'
  obtain ⟨ha, he⟩ := Tm_pos hm ht
  obtain ⟨ha', he'⟩ := Tm_pos hm ht'
  simp only at hae hbe hae' hbe' ha he ha' he'
  have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have h00 : (a : ℤ) = γ.1 0 0 * a' := by
    have := congrFun (congrFun h 0) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (b : ℤ) = γ.1 0 0 * b' + γ.1 0 1 * e' := by
    have := congrFun (congrFun h 0) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : (0 : ℤ) = γ.1 1 0 * a' := by
    have := congrFun (congrFun h 1) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (e : ℤ) = γ.1 1 0 * b' + γ.1 1 1 * e' := by
    have := congrFun (congrFun h 1) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  generalize γ.1 0 0 = x at *
  generalize γ.1 0 1 = y at *
  generalize γ.1 1 0 = z at *
  generalize γ.1 1 1 = w at *
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have haZ' : (0 : ℤ) < a' := by exact_mod_cast ha'
  have heZ' : (0 : ℤ) < e' := by exact_mod_cast he'
  have hz : z = 0 := by
    rcases mul_eq_zero.1 h10.symm with h0 | h0
    · exact h0
    · omega
  subst hz
  have hxw : x * w = 1 := by linear_combination hdet
  have hx0 : 0 < x := by
    by_contra hc
    have : x * a' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) haZ'.le
    omega
  have hx : x = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hxw with h0 | h0
    · exact h0
    · omega
  subst hx
  have hw : w = 1 := by linear_combination hxw
  subst hw
  have e1 : a = a' := by omega
  have e2 : e = e' := by omega
  subst e1 e2
  have hy : y = 0 := by
    have hbZ : (b : ℤ) < e := by exact_mod_cast hbe
    have hbZ' : (b' : ℤ) < e := by exact_mod_cast hbe'
    by_contra hc
    rcases lt_or_gt_of_ne hc with h0 | h0
    · have : y * e ≤ -1 * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
    · have : 1 * (e : ℤ) ≤ y * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
  subst hy
  have e3 : b = b' := by omega
  subst e3
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

def ChebOmSt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) (H : Subgroup (Ω ≃ₐ[E] Ω)) (hn : H.Normal)
    (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hI : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), LiesAbove A v → v ∉ S →
      ∀ g : Ω ≃ₐ[E] Ω, InertiaEl A g → g ∈ H) (σ : Ω ≃ₐ[E] Ω),
    ∃ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v ∧ v ∉ S ∧
      (Nat.card (𝓞 E ⧸ v.asIdeal)).Prime ∧ IsArithFrobenius A v φ ∧ σ⁻¹ * φ ∈ H

end ReciprocityTheory.ChartRestriction.L1
end
end
