module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpForm

open PowerSeries

theorem exists_subst_inverse {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : constantCoeff l = 0) (h1 : coeff 1 l = 1) :
    ∃ ex : PowerSeries R, constantCoeff ex = 0 ∧
      subst ex l = (X : PowerSeries R) ∧ subst l ex = (X : PowerSeries R) := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, h'⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h (), h' ()⟩

theorem subst_eq_of_equation {K : Type} [Field K] [CharZero K] {a b : K}
    {P m q M : PowerSeries K} (hP : IsWpSer a b P) (hm : constantCoeff m = 1)
    (hq : constantCoeff q = 1)
    (hd : X * PowerSeries.derivative q - 2 * q = PowerSeries.derivative (X * m) * M)
    (hM : M ^ 2 = 4 * q ^ 3 - C a * X ^ 4 * q - C b * X ^ 6) :
    (subst (X * m : PowerSeries K) P : PowerSeries K) = m ^ 2 * q := by
  set l : PowerSeries K := X * m with hl
  have h0 : constantCoeff l = 0 := by simp [hl]
  have h1 : coeff 1 l = 1 := by
    rw [hl, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]; simpa using hm
  obtain ⟨ex, he0, he1, he2⟩ := exists_subst_inverse l h0 h1
  have sl : HasSubst l := HasSubst.of_constantCoeff_zero' h0
  have se : HasSubst ex := HasSubst.of_constantCoeff_zero' he0
  have hle : ∀ f : PowerSeries K, (subst l (subst ex f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply se sl, he2]
    exact congrFun MvPowerSeries.subst_self f
  have hel : ∀ f : PowerSeries K, (subst ex (subst l f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply sl se, he1]
    exact congrFun MvPowerSeries.subst_self f
  set Q : PowerSeries K := subst ex (m ^ 2 * q) with hQ
  have hQl : (subst l Q : PowerSeries K) = m ^ 2 * q := hle _
  have hw : PowerSeries.derivative l = m + X * PowerSeries.derivative m := by
    rw [hl, Derivation.leibniz]; simp [add_comm]
  have hw0 : PowerSeries.derivative l ≠ 0 := by
    intro h
    have := congrArg constantCoeff (hw.symm.trans h)
    simp [hm] at this
  have hch := derivative_subst (f := Q) sl
  rw [hQl, Derivation.leibniz, Derivation.leibniz_pow] at hch
  simp only [smul_eq_mul, nsmul_eq_mul] at hch
  have key : l * (subst l (PowerSeries.derivative Q) : PowerSeries K) - 2 * (m ^ 2 * q) = m ^ 3 * M := by
    apply mul_right_cancel₀ hw0
    have hch' : m ^ 2 * PowerSeries.derivative q + q * (2 * (m * PowerSeries.derivative m)) =
        (subst l (PowerSeries.derivative Q) : PowerSeries K) * PowerSeries.derivative l := by simpa using hch
    linear_combination -l * hch' + m ^ 3 * hd - 2 * m ^ 2 * q * hw +
      (m ^ 2 * PowerSeries.derivative q + q * (2 * (m * PowerSeries.derivative m))) * hl
  have hQW : IsWpSer a b Q := by
    constructor
    · have h2 : ∀ f : PowerSeries K, constantCoeff (subst ex f : PowerSeries K) = constantCoeff f := by
        intro f
        have hf := eq_X_mul_shift_add_const f
        conv_lhs => rw [hf]
        rw [← coe_substAlgHom se, map_add (f := _), map_mul, substAlgHom_X, map_add (f := _), map_mul, he0,
          C_eq_algebraMap, AlgHom.commutes]
        simp
      rw [hQ, h2]; simp [hm, hq]
    · rw [← hel (_ ^ 2), ← hel (_ - C b * X ^ 6)]
      congr 1
      change subst l ((X * PowerSeries.derivative Q - 2 * Q) ^ 2) = _
      rw [← coe_substAlgHom sl]
      simp only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, C_eq_algebraMap,
        AlgHom.commutes]
      rw [coe_substAlgHom sl, hQl]
      simp only [C_eq_algebraMap] at hM
      change (l * _ - _) ^ 2 = _ - algebraMap K (PowerSeries K) a * l ^ 4 * _ -
        algebraMap K (PowerSeries K) b * l ^ 6
      rw [key, hl]
      linear_combination m ^ 6 * hM
  rw [(GlobalTheory.WpSeries.existsUnique_isWpSer K a b).unique hP hQW, hQl]

theorem dX_eq_derivative {K : Type*} [CommRing K] (f : PowerSeries K) : dX f = PowerSeries.derivative f := by
  ext n
  simp [dX, coeff_derivative, mul_comm]

theorem derivative_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.derivative (flog W wq) = omegaW W wq := by
  ext n
  have : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [flog, coeff_derivative, this]

theorem wp_flog : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  intro p _ W wq P hwq hP
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  obtain ⟨m, hm⟩ := X_dvd_iff.2 (GlobalTheory.GenusOneDatum.constantCoeff_flog W wq)
  have hm1 : constantCoeff m = 1 := by
    have := GlobalTheory.GenusOneDatum.coeff_one_flog hwq
    rw [hm, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul] at this
    simpa using this
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * PowerSeries.derivative wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * PowerSeries.derivative wq) * (wq * N)⁻¹ := by
      rw [← dX_eq_derivative]; rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * PowerSeries.derivative e + e * PowerSeries.derivative wq = 0 := by
    have := congrArg (PowerSeries.derivative (R := ℂ_[p])) he
    rw [Derivation.leibniz] at this
    simpa using this
  set r := W.b₂ / 12 with hr
  have hq : lineSer e (-r) = e + C r * X ^ 2 := by simp [lineSer]
  have hdq : PowerSeries.derivative (e + C r * X ^ 2) = PowerSeries.derivative e + C r * (2 * X) := by
    rw [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow]; simp
  have hW : wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
    C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := hwq
  have hW' : e ^ 2 = e ^ 3 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + C W.a₃ * X ^ 3 * e +
      C W.a₄ * X ^ 4 * e + C W.a₆ * X ^ 6 := by
    linear_combination e ^ 3 * hW + (-e ^ 2 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 +
      (C W.a₃ * X ^ 3 + C W.a₄ * X ^ 4) * e * (wq * e + 1) +
      C W.a₆ * X ^ 6 * ((wq * e) ^ 2 + wq * e + 1)) * he
  have hNe : N * e = C W.a₁ * X * e + C W.a₃ * X ^ 3 - 2 * e := by
    rw [hN]; linear_combination C W.a₃ * X ^ 3 * he
  have c2 : (12 : PowerSeries ℂ_[p]) * C r = C W.a₁ ^ 2 + 4 * C W.a₂ := by
    have : 12 * r = W.a₁ ^ 2 + 4 * W.a₂ := by rw [hr, WeierstrassCurve.b₂]; ring
    simpa only [map_mul, map_add (f := _), map_pow, map_ofNat] using congrArg (C (R := ℂ_[p])) this
  have c4 : (C (W.c₄ / 12) : PowerSeries ℂ_[p]) =
      12 * C r ^ 2 - 2 * (2 * C W.a₄ + C W.a₁ * C W.a₃) := by
    have : W.c₄ / 12 = 12 * r ^ 2 - 2 * (2 * W.a₄ + W.a₁ * W.a₃) := by
      rw [hr, WeierstrassCurve.c₄, WeierstrassCurve.b₄]; ring
    rw [this]; simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat]
  have c6 : (C (W.c₆ / 216) : PowerSeries ℂ_[p]) =
      2 * C r * (2 * C W.a₄ + C W.a₁ * C W.a₃) - 8 * C r ^ 3 - (C W.a₃ ^ 2 + 4 * C W.a₆) := by
    have : W.c₆ / 216 = 2 * r * (2 * W.a₄ + W.a₁ * W.a₃) - 8 * r ^ 3 - (W.a₃ ^ 2 + 4 * W.a₆) := by
      rw [hr, WeierstrassCurve.c₆, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
    rw [this]; simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat]
  have main := subst_eq_of_equation (m := m) (q := e + C r * X ^ 2) (M := N * e) hP hm1
    (by simp [he1])
    (by
      rw [← hm, derivative_flog, hdq]
      linear_combination -e ^ 2 * hω + X * e * hde +
        (omegaW W wq * N * e + 2 * e - X * PowerSeries.derivative e) * he)
    (by
      rw [hNe, c4, c6]
      linear_combination 4 * hW' - X ^ 2 * e ^ 2 * c2)
  rw [hq, hm, main]
  ring

end GlobalTheory.WpForm
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

open Polynomial

variable {Λ : AddSubgroup ℂ}

theorem IsLat.wpF_add_of_mem (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem IsLat.entire_eq_of_periodic (h : IsLat Λ) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ ω ∈ Λ, ∀ z, F (z + ω) = F z) (z : ℂ) : F z = F 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  exact hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hF.continuous
      fun z w hw => hper w ((hL w).2 hw) z).isBounded z 0

theorem IsLat.sqTh_law (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sqTh Λ v (z + ω) * sgStar Λ z ^ 2 = sqTh Λ v z * sgStar Λ (z + ω) ^ 2 := by
  by_cases hz : z ∈ Λ
  · rw [(h.sg_eq_zero z).2 hz, (h.sg_eq_zero _).2 (add_mem hz hω)]
    simp
  · have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using sub_mem h' hω)
    rw [h.sqTh_eq hv hz, h.sqTh_eq hv hz', h.wpF_add_of_mem hω]
    ring

theorem IsLat.exists_poly_wp (h : IsLat Λ) (k : ℕ) : ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ z, F (-z) = F z) →
    (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) →
    ∃ P : ℂ[X], P.natDegree ≤ k ∧ P.coeff k = F 0 ∧
      ∀ z ∉ Λ, F z = sgStar Λ z ^ (2 * k) * P.eval (wpF Λ z) := by
  induction k with
  | zero =>
    intro F hF _ hlaw
    refine ⟨C (F 0), by simp, by simp, fun z _ => ?_⟩
    simpa using h.entire_eq_of_periodic hF (fun ω hω z => by simpa using hlaw ω hω z) z
  | succ k ih =>
    intro F hF he hlaw
    obtain ⟨v, hv⟩ := h.dense_compl.nonempty
    have hv : v ∉ Λ := hv
    have hd := h.differentiable_sqTh v
    obtain ⟨G, hG, hGe, hFG, hGl⟩ := GlobalTheory.EvenTheta.exists_eq_sg_sq_mul Λ h k
      (fun z => F z - F 0 * sqTh Λ v z ^ (k + 1)) (by fun_prop)
      (fun z => by simp only [he, sqTh_neg]) (by simp [h.sqTh_zero hv])
      (fun ω hω z => by
        have h1 := congrArg (· ^ (k + 1)) (h.sqTh_law hv hω z)
        simp only [mul_pow, ← pow_mul] at h1
        linear_combination hlaw ω hω z - F 0 * h1)
    obtain ⟨P, hP, -, hPG⟩ := ih G hG hGe hGl
    have hm : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).Monic := (monic_X_sub_C _).pow _
    have hdeg : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).natDegree = k + 1 := by
      rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    refine ⟨C (F 0) * (X - C (wpF Λ v)) ^ (k + 1) + P, ?_, ?_, fun z hz => ?_⟩
    · refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hdeg.le) (by omega)
    · have h1 := hm.coeff_natDegree
      rw [hdeg] at h1
      rw [coeff_add, coeff_C_mul, h1, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k + 1)]
      simp
    · have h1 := hFG z
      simp only [hPG z hz, h.sqTh_eq hv hz, mul_pow, ← pow_mul] at h1
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
      linear_combination h1

theorem exists_eval_eq_prod_fin {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) (h1 : P.coeff k = 1) :
    ∃ r : Fin k → ℂ, ∀ x, P.eval x = ∏ i, (x - r i) := by
  have hdeg : P.natDegree = k := natDegree_eq_of_le_of_coeff_ne_zero hP (by rw [h1]; exact one_ne_zero)
  have hm : P.Monic := by rw [Monic, leadingCoeff, hdeg, h1]
  have hs : P.Splits := IsAlgClosed.splits P
  have he := hs.eq_prod_roots_of_monic hm
  have hc := hs.natDegree_eq_card_roots
  obtain ⟨l, hl⟩ := Quotient.exists_rep P.roots
  have hl : (l : Multiset ℂ) = P.roots := hl
  rw [← hl] at he hc
  rw [hdeg, Multiset.coe_card] at hc
  subst hc
  refine ⟨fun i => l[i.1]'i.2, fun x => ?_⟩
  rw [he, eval_multiset_prod, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  exact (Fin.prod_univ_fun_getElem l fun a => x - a).symm

theorem exists_eq_prod_sqTh : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  intro Λ h k F hF he h0 hlaw
  obtain ⟨P, hP, hc, hPF⟩ := h.exists_poly_wp k F hF he hlaw
  obtain ⟨r, hr⟩ := exists_eval_eq_prod_fin hP (hc.trans h0)
  choose Q hQ hQr using fun i => GlobalTheory.EvenTheta.exists_wpF_eq Λ h (r i)
  refine ⟨Q, hQ, fun z => ?_⟩
  refine congrFun (Continuous.ext_on h.dense_compl hF.continuous
    (g := fun z => ∏ i, sqTh Λ (Q i) z)
    (continuous_finsetProd _ fun i _ => (h.differentiable_sqTh (Q i)).continuous) fun z hz => ?_) z
  have hz : z ∉ Λ := hz
  beta_reduce
  simp only [h.sqTh_eq (hQ _) hz, hQr, hPF z hz, hr, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

namespace GlobalTheory.TranslLin

open PowerSeries

theorem taylorCoeffAtZero_const_mul (F : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coef1 (fun z => c * F z) n = c * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

theorem taylorCoeffAtZero_linearCombination {ι : Type} (s : Finset ι) (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (hφ : ∀ k, Differentiable ℂ (φ k)) (n : ℕ) :
    coef1 (fun z => ∑ k ∈ s, c k * φ k z) n = ∑ k ∈ s, c k * coef1 (φ k) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hd : Differentiable ℂ (fun z => ∑ k ∈ s, c k * φ k z) := by
      fun_prop
    rw [GlobalTheory.SerTransport.taylorCoeff_add_entire ((hφ a).const_mul (c a)) hd, taylorCoeffAtZero_const_mul, ih]

theorem exists_retraction : ∃ π : ℂ →ₗ[Qbar] Qbar, ∀ q : Qbar, π (q : ℂ) = q := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 (fun x y h => Subtype.val_injective h))
  exact ⟨π, fun q => LinearMap.congr_fun hπ q⟩

theorem lamC_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {y : ℂ} (h : y ∈ Qbar) :
    lamC lam y = lam ⟨y, h⟩ := dif_pos h

theorem transl_lin : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  intro p _ g ι _ φ c E hE hφ hEq
  obtain ⟨π, hπ⟩ := exists_retraction
  refine ⟨fun k => ((π (c k) : Qbar) : ℂ), fun k => (π (c k)).2, ?_⟩
  have hE' : E = fun z => ∑ k, c k * φ k z := funext hEq
  have key : ∀ n, (⟨coef1 E n, hE.2 n⟩ : Qbar) =
      ∑ k, π (c k) * (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) := by
    intro n
    have h1 : coef1 E n = ∑ k, c k * coef1 (φ k) n := by
      rw [hE']; exact taylorCoeffAtZero_linearCombination Finset.univ φ c (fun k => (hφ k).1) n
    have h2 : π ((⟨coef1 E n, hE.2 n⟩ : Qbar) : ℂ) = π (∑ k, c k * coef1 (φ k) n) :=
      congrArg π h1

    rw [hπ, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : c k * coef1 (φ k) n = (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) • c k := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hser : GL3Theta.ser1 g.lam E =
      ∑ k, C (lamC g.lam ((π (c k) : Qbar) : ℂ)) * GL3Theta.ser1 g.lam (φ k) := by
    ext n

    rw [GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam (hE.2 n), key n, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, coeff_C_mul, GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam ((hφ k).2 n),
      GlobalTheory.SerTransport.lamC_coe]
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  simp only [GlobalTheory.SerTransport.atU_eq, hser]

  simp only [← coe_substAlgHom hs, map_sum, map_mul]
  simp only [coe_substAlgHom, subst_C]
  rfl

end GlobalTheory.TranslLin
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Double

variable {Λ : AddSubgroup ℂ}

theorem exists_evenTheta_translate_mul_sq_comb (h : IsLat Λ) {t s : ℂ} (ht : t ∉ Λ) (h2 : 2 * t ∈ Λ) (hs : s ∉ Λ) :
    ∃ α γ : ℂ, ∀ w, GL3Theta.th0 Λ t (w + s) * GL3Theta.th0 Λ t (w - s) =
      α * GL3Theta.th0 Λ t w ^ 2 + γ * sgStar Λ w ^ 2 := by
  have hs0 := (h.sg_eq_zero s).not.2 hs
  have ht0 := (h.sg_eq_zero t).not.2 ht
  set E : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) t / (area Λ : ℂ) -
    (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) with hE
  set K : ℂ := Complex.exp ((Real.pi : ℂ) * t * (starRingEnd ℂ) t / (area Λ : ℂ)) with hK
  set c : ℂ := U1 Λ t (sgStar Λ) 0 with hc
  have hθ : ∀ u, GL3Theta.th0 Λ t u = sgStar Λ (u + t) * E u * c⁻¹ := fun u => rfl
  refine ⟨-sgStar Λ s ^ 2 * (wpF Λ t - wpF Λ s),
    -sgStar Λ s ^ 2 * c⁻¹ ^ 2 * K / sgStar Λ t ^ 2, fun w => ?_⟩
  have e1 : E (w + s) * E (w - s) = E w ^ 2 := by
    simp only [hE]
    rw [sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : sgStar Λ (w + 2 * t) * E w ^ 2 = -K * sgStar Λ w := by
    have hl := h.sg_law h2 w
    rw [if_neg (by simpa using ht)] at hl
    rw [show -K * sgStar Λ w = (-1 * sgStar Λ w) * K by ring, ← hl]
    simp only [U1, hE, hK]
    rw [mul_assoc (sgStar Λ _), sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    simp only [map_mul, map_ofNat]
    ring
  have e3 := h.sqTh_sub hs ht (w + t)
  rw [sqTh, sqTh, show t + (w + t) = w + 2 * t by ring, show t - (w + t) = -w by ring,
    show s + (w + t) = w + s + t by ring, show s - (w + t) = -(w - s + t) by ring,
    h.sg_neg, h.sg_neg, div_eq_iff (pow_ne_zero 2 hs0)] at e3
  rw [hθ, hθ, hθ]
  linear_combination (sgStar Λ (w + s + t) * sgStar Λ (w - s + t) * c⁻¹ ^ 2) * e1 -
    (E w ^ 2 * c⁻¹ ^ 2) * e3 +
    (sgStar Λ s ^ 2 * c⁻¹ ^ 2 * sgStar Λ w / sgStar Λ t ^ 2) * e2

theorem evenTheta_double_translate_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ s, s ∉ Λ → ∀ z, U1 Λ s (sgStar Λ) 0 ^ 2 * (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) z * GL3Theta.th0 Λ t₀ z) = U1 Λ s (sgStar Λ) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) z ^ 2 + (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) 0 - U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 4) * U1 Λ s (sgStar Λ) z ^ 2 := by
  intro Λ h t ht h2 s hs z
  obtain ⟨α, γ, hp⟩ := exists_evenTheta_translate_mul_sq_comb h ht h2 hs
  obtain ⟨-, h1, hev, -⟩ := evenThetaTwoTorsion_basic_properties Λ h t ht h2
  have hα : α = GL3Theta.th0 Λ t s ^ 2 := by
    have := hp 0
    rw [zero_add, zero_sub, hev, h1, (h.sg_eq_zero 0).2 Λ.zero_mem] at this
    linear_combination -this
  set F : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) s / (area Λ : ℂ) -
    (Real.pi : ℂ) * s * (starRingEnd ℂ) s / (2 * (area Λ : ℂ))) with hF
  have hU : ∀ (G : ℂ → ℂ) u, U1 Λ s G u = G (u + s) * F u := fun _ _ => rfl
  have hU2 : ∀ (G : ℂ → ℂ) u, U1 Λ (2 * s) G u = G (u + s + s) * (F u ^ 2 * F 0 ^ 2) := by
    intro G u
    simp only [U1, hF]
    rw [sq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    · ring
    · simp only [map_mul, map_ofNat]
      ring
  have p1 := hp (z + s)
  have p0 := hp (0 + s)
  rw [add_sub_cancel_right, hα] at p1 p0
  rw [h1] at p0
  simp only [hU, hU2]
  simp only [zero_add] at p0 ⊢
  linear_combination (sgStar Λ s ^ 2 * F 0 ^ 4 * F z ^ 2) * p1 -
    (F 0 ^ 4 * F z ^ 2 * sgStar Λ (z + s) ^ 2) * p0

end GlobalTheory.EvenTheta.Double
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_half_period_sub_not_mem_of_isLat : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, 2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  first | exact @GlobalTheory.HalfPeriod.exists_other_half_period | exact GlobalTheory.HalfPeriod.exists_other_half_period | (intros; apply GlobalTheory.HalfPeriod.exists_other_half_period <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.powerSeriesCoeffNormLeOne_functional_equation_padic : ∀ (p : ℕ) [Fact p.Prime] (f h A B : PowerSeries ℂ_[p]) (N : ℕ), PowerSeries.constantCoeff f = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖(N : ℂ_[p])‖ < 1 → IntSer A → PowerSeries.constantCoeff A = 1 → IntSer B → PowerSeries.constantCoeff B = 1 → (PowerSeries.subst h f : PowerSeries ℂ_[p]) * A = f ^ N * B → IntSer f := by
  first | exact @GlobalTheory.EvenTheta.FunEq.intSer_of_funEq_padic | exact GlobalTheory.EvenTheta.FunEq.intSer_of_funEq_padic | (intros; apply GlobalTheory.EvenTheta.FunEq.intSer_of_funEq_padic <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.existsUnique_isWeierstrassPSeries : ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  first | exact @GlobalTheory.WpSeries.existsUnique_isWpSer | exact GlobalTheory.WpSeries.existsUnique_isWpSer | (intros; apply GlobalTheory.WpSeries.existsUnique_isWpSer <;> assumption)
end
