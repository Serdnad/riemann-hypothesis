module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle015
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle007
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle013
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle011
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin

@[expose] public section

section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def kronFun (p : ℕ) (τ : ℍ) : ℂ := Gm p τ + (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2

theorem kronSq_isMF (p : ℕ) :
    IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (fun τ => (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2) := by
  have h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p) := isMF_AA.mul (isMF_DD.pow p)
  have h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ) :=
    ((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)
  have h3 := (h1.sub h2).pow 2
  exact h3.congr_weight (by push_cast; ring)

theorem Gm_isMF' {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (Gm p) := (gmForm hp.pos).congr_weight (by rw [card_Tm_prime hp]; push_cast; ring)

theorem kronFun_isMF {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (kronFun p) := (Gm_isMF' hp).add (kronSq_isMF p)

theorem aC_conv : Conv aC := convergesOnDisk_eisensteinFourCubeSeries
theorem dC_conv : Conv dC := convergesOnDisk_discriminantSeries
theorem aC_ev (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  exact evalSeries_eisensteinFourCubeSeries τ
theorem dC_ev (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  exact evalSeries_discriminantSeries τ

theorem kronFun_qExp {p : ℕ} (hp : p.Prime) :
    qExpansion 1 (kronFun p) = qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2 := by
  have hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1 := fun τ => by
    rw [qm_one_eq]
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hG := Gm_isMF' hp
  have c1 : Conv (aC * dC ^ p) := aC_conv.mul (dC_conv.pow p)
  have c2 : Conv (aC ^ p * dC) := (aC_conv.pow p).mul dC_conv
  have c3 : Conv (aC * dC ^ p - aC ^ p * dC) := c1.sub c2
  apply (kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))
  intro τ
  rw [ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ),
    ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ),
    ev_pow aC_conv p (hq τ), aC_ev, dC_ev]
  rfl

theorem kronFun_div {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ qExpansion 1 (kronFun p) = PowerSeries.C (1 - zetaC p) * w := by
  obtain ⟨w, hw, hk⟩ := kronSer hp
  have hp0 : 0 < p := hp.pos
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (p * n) w, fun n => by simpa using hw (p * n), ?_⟩
  rw [kronFun_qExp hp]
  ext n
  have key : PowerSeries.coeff (p * n) (xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)) =
      PowerSeries.coeff n (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    simp [xp, PowerSeries.coeff_mk, Nat.mul_div_cancel_left n hp0]
  have hsum : xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) =
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    rw [← gmQ_xp hp0]
    ext m
    simp only [xp, PowerSeries.coeff_mk, map_add (f := _)]
    split_ifs <;> simp
  rw [← key, hsum, hk]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

theorem kronFun_poly {p : ℕ} (hp : p.Prime) :
    ∃ Q : Polynomial ℂ, (∀ i, Q.coeff i ∈ Rm p) ∧
      ∀ τ, kronFun p τ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * Q.eval (jT τ)) := by
  obtain ⟨w, hw, hqe⟩ := kronFun_div hp
  have hc0 : (1 - zetaC p) ≠ 0 := one_sub_zeta_ne_zero hp
  have hK := kronFun_isMF hp
  let f : ℍ → ℂ := fun τ => (1 - zetaC p)⁻¹ * kronFun p τ
  have hf : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) f := hK.const_mul (1 - zetaC p)⁻¹
  have hwq : qExpansion 1 f = w := by
    apply hf.qExp_eq
    · have e : w = PowerSeries.C (1 - zetaC p)⁻¹ * qExpansion 1 (kronFun p) := by
        rw [hqe, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [e]
      exact hK.conv.C_mul _
    · intro τ
      have hs := (hK.hasSum τ).mul_left (1 - zetaC p)⁻¹
      have hw' : ∀ n, PowerSeries.coeff n w * qm 1 τ ^ n =
          (1 - zetaC p)⁻¹ * (PowerSeries.coeff n (qExpansion 1 (kronFun p)) * qm 1 τ ^ n) := by
        intro n
        rw [hqe, PowerSeries.coeff_C_mul]
        field_simp
      unfold ev
      simp_rw [hw']
      exact hs.tsum_eq
  obtain ⟨P, hPc, -, hPe⟩ := qPrin (Rm p) (2 * (p + 1)) f hf (by rw [hwq]; exact hw)
  refine ⟨P, hPc, fun τ => ?_⟩
  calc kronFun p τ = (1 - zetaC p) * f τ := by
        rw [show f τ = (1 - zetaC p)⁻¹ * kronFun p τ from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    _ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * P.eval (jT τ)) := by rw [hPe τ]

theorem kronPt {p : ℕ} (hp : p.Prime) {τ : ℍ} (h : Gm p τ = 0) :
    ∃ r : ℂ, IsIntegral ℤ r ∧ (jT τ ^ p - jT τ) ^ 2 = (1 - zetaC p) * r := by
  obtain ⟨Q, hQ, hK⟩ := kronFun_poly hp
  have hD := DD_ne_zero τ
  have hsq : ¬ IsSquare p := Irreducible.not_isSquare hp
  have hj := jT_isIntegral hp.pos hsq h
  have hint : IsIntegral ℤ (Q.eval (jT τ)) := by
    rw [Polynomial.eval_eq_sum_range]
    exact IsIntegral.sum _ fun i _ => (Rm_isIntegral hp.pos (hQ i)).mul (hj.pow i)
  refine ⟨Q.eval (jT τ), hint, ?_⟩
  have e1 := hK τ
  unfold kronFun at e1
  rw [h, zero_add] at e1
  have hA : AA τ = jT τ * DD τ := by rw [jT, div_mul_cancel₀ _ hD]
  rw [hA] at e1
  have e2 : (jT τ ^ p - jT τ) ^ 2 * DD τ ^ (2 * (p + 1)) =
      (1 - zetaC p) * Q.eval (jT τ) * DD τ ^ (2 * (p + 1)) := by
    linear_combination e1
  exact mul_right_cancel₀ (pow_ne_zero _ hD) e2

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem norm_le_one_of_root {l : ℕ} [Fact l.Prime] {x : ℂ_[l]} (P : Polynomial ℤ) (hm : P.Monic)
    (h : P.eval₂ (Int.castRingHom ℂ_[l]) x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  have hsum := hm.as_sum
  rw [hsum] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := hlt.le
  have hn0 : P.natDegree ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom ℂ_[l]) (P.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (P.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hc : ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ ≤ 1 := by
      rw [eq_intCast (Int.castRingHom ℂ_[l])]
      exact IsUltrametricDist.norm_intCast_le_one _ _
    calc ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (P.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 (by omega)) (by positivity) zero_le_one
      _ = ‖x‖ ^ (P.natDegree - 1) := one_mul _
  have heq := eq_neg_of_add_eq_zero_left h
  have h1 : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ (P.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]
    exact hbound
  have h2 : ‖x‖ ^ (P.natDegree - 1) < ‖x‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith

theorem jInt : JInt := by
  intro d L hsf hd hL l _ ι
  obtain ⟨P, hm, hP⟩ := cm1 d L hsf hd hL
  refine norm_le_one_of_root P hm ?_
  have h := congrArg (ι : ℂ →+* ℂ_[l]) hP
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [← h]
  congr 1
  exact Subsingleton.elim _ _

end ReciprocityTheory.ChartRestriction.L1
end
end

section

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}

theorem IsHalfReps.notMem (h : IsHalfReps L α T) {P : ℂ} (hP : P ∈ T) : P ∉ L.lattice := by
  intro hPL
  apply (h.1 P hP).2
  rw [two_mul]
  exact add_mem hPL hPL

theorem IsHalfReps.kerReps (h : IsHalfReps L α T) :
    IsKerReps L α (T ∪ T.image (fun P => -P)) ∧ Disjoint T (T.image (fun P => -P)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact ⟨(h.1 P hP).1, h.notMem hP⟩
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      refine ⟨?_, ?_⟩
      · rw [mul_neg]; exact neg_mem (h.1 Q hQ).1
      · intro hn; exact h.notMem hQ (by simpa using neg_mem hn)
  · intro P hP Q hQ hPQ
    rcases Finset.mem_union.mp hP with hP | hP <;> rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact h.2.1 P hP Q hQ (Or.inl hPQ)
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have e : P = Q' := h.2.1 P hP Q' hQ' (Or.inr (by simpa using hPQ))
      subst e
      exact absurd (by rw [two_mul]; simpa using hPQ) (h.1 P hP).2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      have h1 : P' + Q ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - Q) = P' + Q := by ring
        rwa [e] at this
      have e : P' = Q := h.2.1 P' hP' Q hQ (Or.inr h1)
      subst e
      exact absurd (by rw [two_mul]; exact h1) (h.1 P' hP').2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have h1 : P' - Q' ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - -Q') = P' - Q' := by ring
        rwa [e] at this
      rw [h.2.1 P' hP' Q' hQ' (Or.inl h1)]
  · intro z hz hzL
    obtain ⟨P, hP, hzP | hzP⟩ := h.2.2 z hz hzL
    · exact ⟨P, Finset.mem_union_left _ hP, hzP⟩
    · exact ⟨-P, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hP), by simpa using hzP⟩
  · rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP'
    have h0 : P + Q ∈ L.lattice := by rw [← hQP]; simp
    have e : P = Q := h.2.1 P hP Q hQ (Or.inr h0)
    subst e
    exact (h.1 P hP).2 (by rw [two_mul]; exact h0)

theorem IsHalfReps.card (h : IsHalfReps L α T) (hα : α ≠ 0) (hs : MulStable L α) :
    2 * (T.card : ℝ) + 1 = Complex.normSq α := by
  have h1 := kerRepsCard L α _ hα hs h.kerReps.1
  rw [Finset.card_union_of_disjoint h.kerReps.2, Finset.card_image_of_injective _ neg_injective] at h1
  rw [← h1]; push_cast; ring

theorem IsHalfReps.injOn (h : IsHalfReps L α T) : Set.InjOn L.weierstrassP (T : Set ℂ) := by
  intro P hP Q hQ hPQ
  exact h.2.1 P hP Q hQ ((pInjective L P Q (h.notMem hP) (h.notMem hQ)).mp hPQ)

theorem IsHalfReps.fW_ne (h : IsHalfReps L α T) {x : ℂ} (hx : x ∈ xsOf L T) : fW L.g₂ L.g₃ x ≠ 0 := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
  have hPL := h.notMem hP
  unfold fW
  rw [← L.derivWeierstrassP_sq P hPL]
  exact pow_ne_zero 2 (fun h0 => (h.1 P hP).2 ((pDerivZero L P hPL).mp h0))

theorem IsHalfReps.mem_xsOf (h : IsHalfReps L α T) (hs : MulStable L α) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassP z ∈ xsOf L T ↔ α * z ∈ L.lattice := by
  constructor
  · intro hx
    obtain ⟨P, hP, hPz⟩ := Finset.mem_image.mp hx
    rcases (pInjective L z P hz (h.notMem hP)).mp hPz.symm with h1 | h1
    · have e : α * z = α * (z - P) + α * P := by ring
      rw [e]; exact add_mem (hs _ h1) (h.1 P hP).1
    · have e : α * z = α * (z + P) - α * P := by ring
      rw [e]; exact sub_mem (hs _ h1) (h.1 P hP).1
  · intro hk
    obtain ⟨P, hP, h1⟩ := h.2.2 z hk hz
    exact Finset.mem_image.mpr ⟨P, hP, ((pInjective L z P hz (h.notMem hP)).mpr h1).symm⟩

theorem ker_norm (hs : MulStable L α) {N : ℕ} (hN : Complex.normSq α = N) {z : ℂ}
    (hz : α * z ∈ L.lattice) : (N : ℂ) * z ∈ L.lattice := by
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hs
  have h1 : (N : ℂ) = α * (starRingEnd ℂ) α := by
    rw [Complex.mul_conj, hN]; simp
  have e : (N : ℂ) * z = t • (α * z) - α * (α * z) := by
    rw [h1, zsmul_eq_mul, ← ht]; ring
  rw [e]
  exact sub_mem (zsmul_mem hz t) (hs _ hz)

theorem halfReps_exist (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (hs : MulStable L α) (N : ℕ)
    (hN : Complex.normSq α = N) (hodd : Odd N) : ∃ T : Finset ℂ, IsHalfReps L α T := by
  obtain ⟨S, hS⟩ := kerRepsExist L α hα hs
  let g : ℂ → ℂ := fun x => Classical.epsilon (fun Q => Q ∈ S ∧ L.weierstrassP Q = x)
  have hg : ∀ P ∈ S, g (L.weierstrassP P) ∈ S ∧ L.weierstrassP (g (L.weierstrassP P)) = L.weierstrassP P :=
    fun P hP => Classical.epsilon_spec (p := fun Q => Q ∈ S ∧ L.weierstrassP Q = L.weierstrassP P) ⟨P, hP, rfl⟩
  refine ⟨(S.image L.weierstrassP).image g, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    have hk := hS.1 _ (hg P0 hP0).1
    refine ⟨hk.1, fun h2 => hk.2 ?_⟩
    obtain ⟨k, hk'⟩ := hodd
    have h3 := ker_norm hs hN hk.1
    have e : g (L.weierstrassP P0) = (N : ℂ) * g (L.weierstrassP P0) - (k : ℤ) • (2 * g (L.weierstrassP P0)) := by
      rw [hk', zsmul_eq_mul]; push_cast; ring
    rw [e]
    exact sub_mem h3 (zsmul_mem h2 _)
  · intro P hP Q hQ hPQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨Q0, hQ0, rfl⟩ := Finset.mem_image.mp hy
    have h1 := (pInjective L _ _ (hS.1 _ (hg P0 hP0).1).2 (hS.1 _ (hg Q0 hQ0).1).2).mpr hPQ
    rw [(hg P0 hP0).2, (hg Q0 hQ0).2] at h1
    rw [h1]
  · intro z hz hzL
    obtain ⟨P0, hP0, h0⟩ := hS.2.2 z hz hzL
    refine ⟨g (L.weierstrassP P0),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hP0), ?_⟩
    apply (pInjective L _ _ hzL (hS.1 _ (hg P0 hP0).1).2).mp
    rw [(hg P0 hP0).2]
    exact (pInjective L _ _ hzL (hS.1 _ hP0).2).mpr (Or.inl h0)

end ReciprocityTheory.ChartRestriction.L1
end
end
