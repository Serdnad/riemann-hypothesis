module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
public import Formalism.MahlerMeasure.Bundle002
public import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
public import Formalism.PolynomialDimension.Bundle002
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open Polynomial Finset Formalism.GM

section
variable (K : Type) [Field K] [CharZero K]

theorem binK_natDegree (k : ℕ) : (binK K k).natDegree = k := by
  unfold binK
  have h : ((k.factorial : K))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast k.factorial_ne_zero)
  rw [natDegree_C_mul h, descPochhammer_natDegree]

theorem binK_coeff_top (k : ℕ) : (binK K k).coeff k = ((k.factorial : K))⁻¹ := by
  unfold binK
  rw [coeff_C_mul]
  have h := (monic_descPochhammer K k).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [h, mul_one]

theorem binMat_natDegree_le {n : ℕ} (J : ℕ) (c : Fin n → Fin n → ℕ → K) (a b : Fin n) :
    (binMatK K J c a b).natDegree ≤ J := by
  unfold binMatK
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [binK_natDegree]
  simp only [mem_range] at hk; omega

theorem binMat_coeff_top {n : ℕ} (J : ℕ) (c : Fin n → Fin n → ℕ → K) (a b : Fin n) :
    (binMatK K J c a b).coeff J = c a b J * ((J.factorial : K))⁻¹ := by
  unfold binMatK
  rw [finsetSum_coeff, Finset.sum_eq_single J]
  · rw [coeff_C_mul, binK_coeff_top]
  · intro k hk hne
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [binK_natDegree]
    simp only [mem_range] at hk; omega
  · intro h; simp at h

end

theorem lead_bound (p : ℕ) [hp : Fact p.Prime] (n J : ℕ) (c : Fin n → Fin n → ℕ → ℚ_[p]) (d : Fin n → ℚ_[p])
    (hc : ∀ a b, c a b J = if a = b then d a else 0) (R Λ : ℝ) (hd : ∀ a, d a ≠ 0 ∧ -Real.logb p ‖d a‖ ≤ R)
    (hV : (J : ℝ) / ((p : ℝ) - 1) - padicValNat p J.factorial ≤ Λ) :
    (binMatK ℚ_[p] J c).det ≠ 0 ∧
      -Real.logb p ‖(binMatK ℚ_[p] J c).det.leadingCoeff‖ +
        ((binMatK ℚ_[p] J c).det.natDegree : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * (R + Λ) := by
  have hJ0 : ((J.factorial : ℚ_[p])) ≠ 0 := by exact_mod_cast J.factorial_ne_zero
  obtain ⟨h1, h2⟩ := Formalism.CountingSumsFrames.Top.detLeadDiag ℚ_[p] n J (binMatK ℚ_[p] J c) (fun a => d a * ((J.factorial : ℚ_[p]))⁻¹)
    (binMat_natDegree_le ℚ_[p] J c) (fun a b => by
      rw [binMat_coeff_top, hc]; split_ifs <;> simp)
  have hne : ∏ a, d a * ((J.factorial : ℚ_[p]))⁻¹ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => mul_ne_zero (hd a).1 (inv_ne_zero hJ0)
  have hdet : (binMatK ℚ_[p] J c).det ≠ 0 := by
    intro h0; rw [h0, coeff_zero] at h2; exact hne h2.symm
  have hdeg : (binMatK ℚ_[p] J c).det.natDegree = n * J :=
    le_antisymm h1 (le_natDegree_of_ne_zero (by rw [h2]; exact hne))
  have hlead : (binMatK ℚ_[p] J c).det.leadingCoeff = ∏ a, d a * ((J.factorial : ℚ_[p]))⁻¹ := by
    rw [leadingCoeff, hdeg, h2]
  refine ⟨hdet, ?_⟩
  rw [hlead, hdeg, norm_prod, Real.logb_prod _ _ (fun a _ => norm_ne_zero_iff.2 (mul_ne_zero (hd a).1 (inv_ne_zero hJ0)))]
  have hterm : ∀ a, Real.logb p ‖d a * ((J.factorial : ℚ_[p]))⁻¹‖ =
      Real.logb p ‖d a‖ + padicValNat p J.factorial := by
    intro a
    rw [norm_mul, norm_inv, Real.logb_mul (norm_ne_zero_iff.2 (hd a).1) (inv_ne_zero (norm_ne_zero_iff.2 hJ0)),
      Real.logb_inv, Formalism.GM.MeanGammaLemmas.neglog_nat p _ J.factorial_ne_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : -∑ a, Real.logb p ‖d a‖ ≤ n * R := by
    rw [← Finset.sum_neg_distrib]
    calc ∑ a, -Real.logb p ‖d a‖ ≤ ∑ _a : Fin n, R := Finset.sum_le_sum fun a _ => (hd a).2
      _ = n * R := by simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_le_mul_of_nonneg_left hV hn
  push_cast
  have e1 : (n : ℝ) * J / ((p : ℝ) - 1) = n * ((J : ℝ) / ((p : ℝ) - 1)) := by ring
  rw [e1]
  nlinarith

end Formalism.MainNotions.G.GramWindowAlt

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality

section Ops

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type} {r : ℕ}

theorem one_le_p : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

theorem bnd_Xl (w e : Fin r → σ) (J l : ℕ) (hl : l ≤ J) (B : ℝ) (hB : 0 ≤ B) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd B u) :
    Bnd (B * (p : ℝ) ^ ((r + 1) * Nat.log p J))
      ((((l.factorial : ℚ_[p]) ^ 2 * (J.choose l : ℚ_[p]))⁻¹) • ((tieE w e ^ l) ((tieF w e ^ l) u))) := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  set Mc : ℝ := (p : ℝ) ^ (Nat.log p J) with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ J, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 (Nat.log_mono_right hj))
  let D : Fin r → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (D a) (D b) := by
    intro a b
    simp only [D, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum D hcomm (fun a k => contr_D _ _ k) hM1 J hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : Formalism.GM.tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, D c := rfl
  have h1 := hF l hl B hB u hu
  rw [← hFeq] at h1
  have h2 := contr_pow zero_le_one (contr_E (p := p) w e) l _ (by positivity) _ h1
  have eq : (((l.factorial : ℚ_[p]) ^ 2 * (J.choose l : ℚ_[p]))⁻¹) • ((tieE w e ^ l) ((tieF w e ^ l) u)) =
      (((J.choose l : ℕ) : ℚ_[p])⁻¹) • ((tieE w e ^ l) (((((l.factorial : ℚ_[p]) ^ 2))⁻¹ • (tieF w e ^ l)) u)) := by
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv, mul_comm]
  rw [eq]
  refine bnd_mono (bnd_smul _ h2) ?_
  have hA := hM J le_rfl l hl
  calc ‖(((J.choose l : ℕ) : ℚ_[p]))⁻¹‖ * (B * Mc ^ r * 1 ^ l) ≤ Mc * (B * Mc ^ r * 1 ^ l) := by gcongr
    _ = B * (p : ℝ) ^ ((r + 1) * Nat.log p J) := by
        rw [hMc, one_pow, mul_one, ← pow_mul, mul_comm ((p : ℝ) ^ Nat.log p J), mul_assoc, ← pow_add]
        congr 2; ring

theorem bnd_pow_iff (k : ℕ) (u : MvPolynomial σ ℚ_[p]) :
    Bnd ((p : ℝ) ^ k) u ↔ M.IsIntegral' p (((p : ℚ_[p]) ^ k) • u) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one one_le_p
  have hk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp0 k
  refine forall_congr' fun m => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hk, mul_one]

theorem bnd_phi (w e : Fin r → σ) (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (hr : 1 ≤ r) (o n z Λ : ℕ) (hΛ : Nat.log p (o + n + r + z) + 1 ≤ Λ) (k : ℕ) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd ((p : ℝ) ^ k) u) : Bnd ((p : ℝ) ^ (k + (r + 1) * Λ)) (tiePhi w e o n z u) := by
  have h1 := (bnd_pow_iff k u).1 hu
  have h2 := Formalism.GM.projectorIntegral p σ r w e hw he hwe hr o n z _ h1
  rw [map_smul, smul_smul, ← pow_add] at h2
  refine bnd_mono ((bnd_pow_iff _ _).2 h2) (pow_le_pow_right₀ one_le_p ?_)
  have := Nat.mul_le_mul_left (r + 1) hΛ
  omega

theorem bnd_foldr {ι : Type} (φ : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) (c : ℕ) (l : List ι)
    (h : ∀ i ∈ l, ∀ k u, Bnd ((p : ℝ) ^ k) u → Bnd ((p : ℝ) ^ (k + c)) (φ i u)) (k : ℕ) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd ((p : ℝ) ^ k) u) :
    Bnd ((p : ℝ) ^ (k + l.length * c)) ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) u) := by
  induction l with
  | nil => simpa using hu
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, List.length_cons]
    have h1 := ih (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))
    have h2 := h i List.mem_cons_self _ _ h1
    rw [show k + (l.length + 1) * c = k + l.length * c + c by ring]
    exact h2

theorem norm_fock_le (U v : MvPolynomial σ ℚ_[p]) (dF : ℕ) (hdF : dF ≠ 0) (k E : ℕ) (hU : Bnd ((p : ℝ) ^ k) U)
    (hv : Bnd 1 v)
    (hval : ∀ m ∈ v.support, padicValNat p dF ≤ padicValNat p (m.prod fun _ i => i.factorial) + E) :
    ‖M.fockK U v / (dF : ℚ_[p])‖ ≤ (p : ℝ) ^ (k + E) := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  unfold M.fockK
  rw [Finset.sum_div]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m _ => ?_
  by_cases hm : m ∈ v.support
  · have hne : (m.prod fun _ i => i.factorial) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _
    have hcast : (m.prod fun _ j => (j.factorial : ℚ_[p])) = (((m.prod fun _ i => i.factorial) : ℕ) : ℚ_[p]) := by
      simp [Finsupp.prod]
    rw [hcast, norm_div, norm_mul, norm_mul, Formalism.GM.MeanGammaLemmas.norm_nat p _ hne, Formalism.GM.MeanGammaLemmas.norm_nat p _ hdF,
      mul_div_assoc, ← zpow_sub₀ hp0.ne']
    have h3 : (p : ℝ) ^ (-(padicValNat p (m.prod fun _ i => i.factorial) : ℤ) - -(padicValNat p dF : ℤ)) ≤
        (p : ℝ) ^ E := by
      rw [← zpow_natCast]
      apply zpow_le_zpow_right₀ hp1
      have := hval m hm
      omega
    calc ‖AddMonoidAlgebra.coeff U m‖ * ‖AddMonoidAlgebra.coeff v m‖ *
          (p : ℝ) ^ (-(padicValNat p (m.prod fun _ i => i.factorial) : ℤ) - -(padicValNat p dF : ℤ))
        ≤ (p : ℝ) ^ k * 1 * (p : ℝ) ^ E := by
          gcongr
          · exact hU m
          · exact hv m
      _ = (p : ℝ) ^ (k + E) := by rw [mul_one, pow_add]
  · rw [notMem_support_iff.1 hm, mul_zero, zero_mul, zero_div, norm_zero]
    positivity

end Ops

end Formalism.MainNotions.G.GramWindowAlt

end
end
