module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

theorem wick_of (hI : IntegP) : Wick := by
  intro m n ε c t hc b hb M a i
  have hdet := amat_det_ne ε hc t hb a
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set E : (Fin m → Fin n → ℂ) → ℂ := fun x => Complex.exp (evX (phiP ε c t b) x) with hEdef
  have hsec : ∀ P, secN ε c t P b = ∫ x, evX P x * E x := by
    intro P; unfold secN; congr 1; funext x; rw [mul_assoc, exp_phiP]
  have hint : ∀ P, Integrable (fun x => evX P x * E x) := by
    intro P
    refine (hI m n c hc P).mono ?_ ?_
    · exact ((evX_continuous P).mul (evX_continuous (phiP ε c t b)).cexp).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hx : E x = gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := (exp_phiP ε c t b x).symm
      rw [hx, ← mul_assoc, norm_mul _ (Complex.exp _), norm_exp_tr ε t b hb x, mul_one]
  have hE : ∀ x, HasFDerivAt E (E x • dEv (phiP ε c t b) x) x := fun x => (hasFDerivAt_evX (phiP ε c t b) x).cexp
  have hfd : ∀ x v, fderiv ℝ E x v = E x * evX (∑ k, C (crd k v) * pderiv k (phiP ε c t b)) x := by
    intro x v; rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, dEv_apply]
  have hPd : ∀ (P : PX m n) x v, fderiv ℝ (evX P) x v = evX (∑ k, C (crd k v) * pderiv k P) x := by
    intro P x v; rw [(hasFDerivAt_evX P x).fderiv, dEv_apply]
  have hintD : ∀ (P : PX m n) v, Integrable (fun x => evX P x * fderiv ℝ E x v) := by
    intro P v
    refine (hint (P * ∑ k, C (crd k v) * pderiv k (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hfd]; simp only [evX, map_mul]; ring
  have hintM : ∀ (P : PX m n) v, Integrable (fun x => fderiv ℝ (evX P) x v * E x) := by
    intro P v; simp_rw [hPd]; exact hint _
  have ibp : ∀ (P : PX m n) (v : Fin m → Fin n → ℂ),
      ∫ x, evX P x * fderiv ℝ E x v = -∫ x, fderiv ℝ (evX P) x v * E x := by
    intro P v
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hintM P v) (hintD P v) (hint P)
      (fun x _ => (hasFDerivAt_evX P x).differentiableAt) (fun x _ => (hE x).differentiableAt)
  have ibpW : ∀ j : Fin n, ∫ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
      -∫ x, evX (pderiv (a, j, false) M) x * E x := by
    intro j
    have hWE : ∀ x, fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
        Complex.I * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
        2 * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) := by
      intro x
      rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      have := dEv_wirt (phiP ε c t b) x a j
      linear_combination (E x) * this
    have hpt : ∀ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
        (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0))) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero)]
      linear_combination (-(evX M x)) * hWE x
    have hptM : ∀ x, evX (pderiv (a, j, false) M) x * E x =
        (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) * E x -
          Complex.I * (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) * E x)) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero), (hasFDerivAt_evX M x).fderiv]
      have := dEv_wirt M x a j
      linear_combination (-(E x)) * this
    simp_rw [hpt, hptM]
    rw [integral_div, integral_div, integral_sub (hintD M _) ((hintD M _).const_mul _),
      integral_sub (hintM M _) ((hintM M _).const_mul _), integral_const_mul, integral_const_mul, ibp, ibp]
    ring
  have hAA : Amat ε c t b a * (Amat ε c t b a)⁻¹ = 1 := Matrix.mul_nonsing_inv (Amat ε c t b a) (isUnit_iff_ne_zero.mpr hdet)
  have key : ∀ x, evX (X (a, i, true) * M) x * E x =
      -∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x)) := by
    intro x
    simp only [evX_pderiv_phiP]
    have h1 : ∀ k, ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i = if k = i then 1 else 0 := by
      intro k; rw [← Matrix.mul_apply, hAA, Matrix.one_apply]
    have h2 : ∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * -∑ k, Amat ε c t b a k j * star (x a k))) =
        -(evX M x * E x * ∑ k, star (x a k) * ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i) := by
      simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_neg]
    simp only [evX, map_mul, eval_X, if_true]
    ring
  rw [hsec]
  simp_rw [key]
  rw [integral_neg, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, ibpW, hsec]
    simp only [Finset.sum_neg_distrib, mul_neg, neg_neg]
  · intro j _
    refine Integrable.const_mul ?_ _
    refine (hint (M * pderiv (a, j, false) (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [evX, map_mul]; ring

end PositivityTheory.Rg.Sw.WR.G
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem ratBound (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ∃ C : ℝ, ∀ y : E n, ‖(Delta^[N] (cls s 0 p q R)) y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
  obtain ⟨hUo, hFc, c₀, C₀, hc₀, hb⟩ := hB n s hs p q R
  set K : ℝ := ((N * n : ℕ) : ℝ) with hK
  set C₁ : ℝ := max C₀ 0 with hC₁
  refine ⟨(Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁, fun y => ?_⟩
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  set w : Fin n → ℝ := fun i => 1 + |lam i| with hw
  have hwpos : ∀ i, 0 < w i := fun i => by simp only [hw]; positivity
  set W : ℝ := ∏ i, w i with hW
  have hWpos : 0 < W := Finset.prod_pos fun i _ => hwpos i
  set d : Mc n := Matrix.diagonal (fun i => (lam i : ℂ)) with hd
  set ρ : Fin n → Fin n → ℝ := fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|)) with hρ
  have hρpos : ∀ i j, 0 < ρ i j := fun i j => mul_pos hc₀ (Real.sqrt_pos.2 (mul_pos (hwpos i) (hwpos j)))
  have hlink := (hL n (Fr s p q R) (Ugood s) hUo hFc (herm_mem_Ugood s hs)).1 N y
  rw [cls_zero, hlink, hy]
  set F' : Mc n → ℂ := fun c => Fr s p q R (k * c * kᴴ) with hF'
  set U' : Set (Mc n) := {c | k * c * kᴴ ∈ Ugood s} with hU'
  have hU'o : IsOpen U' := hUo.preimage (contDiff_conj k).continuous
  have hF'c : ContDiffOn ℂ (⊤ : ℕ∞) F' U' := hFc.comp (contDiff_conj k).contDiffOn (fun c hc => hc)
  have hdisc : pdisc d ρ ⊆ U' := fun b hb' => (hb k hk lam b hb').1
  have hdmem : d ∈ U' := hdisc (fun i j => by simp [hρpos i j |>.le])
  have hherm' : ∀ y', herm y' ∈ U' := fun y' => conj_mem_Ugood s k hk _ (herm_mem_Ugood s hs y')
  rw [← hI n (Fr s p q R) (Ugood s) hUo hFc k hk N d hdmem, (hL n F' U' hU'o hF'c hherm').2 N d hdmem]
  have hM : ∀ b ∈ pdisc d ρ, ‖F' b‖ ≤ C₁ * W ^ (-((p + q : ℕ) : ℝ)) := fun b hb' =>
    ((hb k hk lam b hb').2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hWpos.le _))
  have hword : ∀ τ : Fin N → Equiv.Perm (Fin n),
      ‖word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖ ≤
        ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
    intro τ
    have h := hC n F' U' hU'o hF'c d ρ hρpos hdisc _ hM ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
    rw [prod_blocks N (fun j k => (((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)).length : ℝ) /
      ρ (τ j k) k)]
    rw [length_blocks]
    show ∏ j, ∏ k, K / ρ ((τ j) k) k = ((K / c₀) ^ n / W) ^ N
    have hblock : ∀ j, ∏ k, K / ρ ((τ j) k) k = (K / c₀) ^ n / W := by
      intro j
      have hs := prod_sqrt_perm (τ j) w hwpos
      simp only [hw] at hs
      simp only [hρ]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs, div_pow]
      simp only [hW, hw]
      field_simp
    rw [Finset.prod_congr rfl fun j _ => hblock j, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsgn : ∀ τ : Fin N → Equiv.Perm (Fin n), ‖(((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))‖ = 1 := by
    intro τ
    have h : ∀ j, |((Equiv.Perm.sign (τ j) : ℤ))| = 1 := fun j => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (τ j)) with h | h <;> simp [h]
    have h2 : |∏ j, ((Equiv.Perm.sign (τ j) : ℤ))| = 1 := by
      rw [Finset.abs_prod, Finset.prod_eq_one fun j _ => h j]
    rw [Complex.norm_intCast]
    exact_mod_cast h2
  have hdP : dP y ≤ W ^ (2 : ℝ) := by
    rw [dP_of_spectral y k hk lam hy, Real.rpow_two, hW, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    simp only [hw]
    have : lam i ^ 2 = |lam i| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg (lam i)]
  have hWe : ∀ e : ℝ, 0 ≤ e → W ^ (-e) ≤ (dP y) ^ (-e / 2) := by
    intro e he
    have h1 : W ^ (-e) = (W ^ (2 : ℝ)) ^ (-e / 2) := by
      rw [← Real.rpow_mul hWpos.le]; ring_nf
    rw [h1]
    exact Real.rpow_le_rpow_of_nonpos (dP_pos y) hdP (by linarith)
  calc ‖∑ τ : Fin N → Equiv.Perm (Fin n), (((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ)) *
          word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖
      ≤ ∑ τ : Fin N → Equiv.Perm (Fin n), ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        rw [norm_mul, hsgn τ, one_mul]; exact hword τ
    _ = (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (W ^ (-((p + q + N : ℕ) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : W ^ (-((p + q + N : ℕ) : ℝ)) = W ^ (-((p + q : ℕ) : ℝ)) * (W ^ N)⁻¹ := by
          rw [show (-((p + q + N : ℕ) : ℝ)) = (-((p + q : ℕ) : ℝ)) + (-(N : ℝ)) by push_cast; ring,
            Real.rpow_add hWpos, Real.rpow_neg hWpos.le, Real.rpow_natCast, Real.rpow_neg hWpos.le, Real.rpow_natCast]
        rw [this, div_pow]; ring
    _ ≤ (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_left (hWe _ (by positivity)) ?_
        refine mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (pow_nonneg (div_nonneg (by positivity) hc₀.le) _) _))
          (le_max_right _ _)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ}

theorem norm_cexp_It (t r : ℝ) : ‖Complex.exp (Complex.I * t * r)‖ = 1 := by
  have : Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_cexp_neg_It (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  have : -(Complex.I * (t : ℂ) * (r : ℂ)) = ((-(t * r) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem ip_sub_right (y u w : E n) : ip y (u - w) = ip y u - ip y w := by
  simp only [ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ip_comm (y y' : E n) : ip y y' = ip y' y := by
  simp only [ip, mul_comm]

theorem continuous_ip : Continuous (fun p : E n × E n => ip p.1 p.2) := by
  unfold ip
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => by fun_prop

theorem continuous_gK : Continuous (gK (n := n)) := by
  unfold gK
  exact continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ => by fun_prop

def gam (ε : ℝ) (y : E n) : ℂ := Complex.exp (-((ε * ip y y : ℝ) : ℂ))

theorem continuous_gam (ε : ℝ) : Continuous (gam (n := n) ε) := by
  unfold gam
  have h : Continuous (fun y : E n => ip y y) := continuous_ip.comp (continuous_id.prodMk continuous_id)
  fun_prop

def kr (ε t : ℝ) (u : E n) : ℂ := ∫ y, gam ε y * Complex.exp (Complex.I * t * ip y u)

theorem norm_kr_le (ε t : ℝ) (hε : 0 < ε) (u : E n) : ‖kr ε t u‖ ≤ ∫ y, ‖gam (n := n) ε y‖ := by
  unfold kr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext y
  rw [norm_mul, norm_cexp_It, mul_one]

theorem continuous_kr (ε t : ℝ) (hε : 0 < ε) : Continuous (kr (n := n) ε t) := by
  unfold kr
  refine continuous_of_dominated (bound := fun y => ‖gam (n := n) ε y‖) ?_ ?_
    (integrable_gauss ε hε).norm ?_
  · intro u
    exact ((continuous_gam ε).mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_id.prodMk continuous_const)))))).aestronglyMeasurable
  · intro u; refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_cexp_It, mul_one]
  · refine Eventually.of_forall fun y => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_const.prodMk continuous_id)))))

theorem finrank_E : Module.finrank ℝ (E n) = n ^ 2 := by
  simp [E, Module.finrank_pi_fintype, sq]

def mM (ψ : E n → ℂ) (l : ℝ) (w : E n) : ℂ := ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)

theorem norm_mM_le (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) (w : E n) :
    ‖mM ψ l w‖ ≤ B := by
  unfold mM
  calc ‖∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)‖ ≤ ∫ v, B * gK (n := n) v := by
        refine norm_integral_le_of_norm_le (integrable_gK.const_mul B) (Eventually.of_forall fun v => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
        exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
    _ = B := by rw [integral_const_mul, integral_gK, mul_one]

theorem continuous_mM (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℝ) :
    Continuous (mM ψ l) := by
  unfold mM
  refine continuous_of_dominated (bound := fun v => B * gK (n := n) v) ?_ ?_ (integrable_gK.const_mul B) ?_
  · intro w
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - l⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro w; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · exact Eventually.of_forall fun v => (by fun_prop : Continuous fun w : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ))

theorem tendsto_mM (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℕ → ℝ)
    (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) (w : E n) :
    Tendsto (fun k => mM ψ (l k) w) atTop (𝓝 (ψ w)) := by
  have hlim : ψ w = ∫ v, ψ (w - (0 : ℝ) • v) * (gK (n := n) v : ℂ) := by
    simp only [zero_smul, sub_zero]
    rw [integral_const_mul, integral_complex_ofReal, integral_gK, Complex.ofReal_one, mul_one]
  rw [hlim]
  unfold mM
  refine tendsto_integral_of_dominated_convergence (fun v => B * gK (n := n) v) ?_ (integrable_gK.const_mul B) ?_ ?_
  · intro k
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - (l k)⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · refine Eventually.of_forall fun v => ?_
    refine Tendsto.mul ?_ tendsto_const_nhds
    exact (hψ.tendsto _).comp (tendsto_const_nhds.sub (hl.smul_const v))

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end
