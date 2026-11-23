module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle053
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

theorem evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX P u) := by
  have hcoord : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u a i) := by
    intro a i
    exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ))).hasTemperateGrowth
  have hconj : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u a i)) := by
    intro a i
    have h := (Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
    convert h using 1
    funext u
    simp [Complex.conjCLE_apply]
  refine MvPolynomial.induction_on
    (motive := fun Q : PX m n =>
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX Q u)) P ?_ ?_ ?_
  · intro a
    convert Function.HasTemperateGrowth.const (E := Fin m → Fin n → ℂ) a using 1
    funext u
    simp [evX]
  · intro p q hp hq
    convert hp.add hq using 1
    funext u
    simp [evX]
  · intro p k hp
    obtain ⟨a, i, b⟩ := k
    cases b
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, false)) u) =
          (fun u => evX p u) * (fun u => u a i) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hcoord a i)
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, true)) u) =
          (fun u => evX p u) * (fun u => star (u a i)) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hconj a i)

private theorem hasTemperateGrowth_const_mul_sum_norm_sq {m n : ℕ} (c : ℝ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
  have hre : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).re) := fun a i =>
    (Complex.reCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have him : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).im) := fun a i =>
    (Complex.imCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have hsq : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) := by
    intro a i
    have e : (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) =
        fun u : Fin m → Fin n → ℂ => (u a i).re * (u a i).re + (u a i).im * (u a i).im := by
      funext u
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [e]
    exact ((hre a i).mul (hre a i)).add ((him a i).mul (him a i))
  have hin : ∀ a : Fin m, Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ i : Fin n, ‖u a i‖ ^ 2) := fun a =>
    Function.HasTemperateGrowth.sum fun i _ => hsq a i
  have hsum : Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) :=
    Function.HasTemperateGrowth.sum fun a _ => hin a
  exact (Function.HasTemperateGrowth.const c).mul hsum

private theorem norm_iteratedFDeriv_cexp_neg_eq_exp_neg (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s : ℝ => Complex.exp (-(s : ℂ))) t‖ = Real.exp (-t) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hit : iteratedDeriv i (fun s : ℝ => Complex.exp (-(s : ℂ))) =
      fun s : ℝ => (-1 : ℂ) ^ i * Complex.exp (-(s : ℂ)) := by
    induction i with
    | zero =>
      funext s
      simp
    | succ i ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
        simpa using (hasDerivAt_id s).ofReal_comp
      have hd : HasDerivAt (fun s : ℝ => -(s : ℂ)) (-1) s := h0.neg
      have he := (hd.cexp).const_mul ((-1 : ℂ) ^ i)
      rw [he.deriv]
      ring
  rw [hit]
  simp [Complex.norm_exp]

private theorem exists_bound_one_add_pow_mul_exp_neg_sq (c : ℝ) (hc : 0 < c) (j : ℕ) :
    ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ j * Real.exp (-(c * r ^ 2)) ≤ M := by
  refine ⟨2 ^ j * (1 + j.factorial / c ^ j), fun r hr => ?_⟩
  have hy : 0 ≤ c * r ^ 2 := by positivity
  have hexp := Real.pow_div_factorial_le_exp (c * r ^ 2) hy j
  have hE : 0 < Real.exp (c * r ^ 2) := Real.exp_pos _
  have hcj : 0 < c ^ j := pow_pos hc j
  have h2j : (0 : ℝ) < 2 ^ j := pow_pos two_pos j
  have hr2j : 0 ≤ (r ^ 2) ^ j := by positivity
  have h1 : (1 + r) ^ j ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by
    rcases le_total r 1 with h | h
    · calc (1 + r) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
    · calc (1 + r) ^ j ≤ (2 * r ^ 2) ^ j := pow_le_pow_left₀ (by linarith) (by nlinarith) j
        _ = 2 ^ j * (r ^ 2) ^ j := mul_pow _ _ _
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
  have h2 : (r ^ 2) ^ j * Real.exp (-(c * r ^ 2)) ≤ j.factorial / c ^ j := by
    rw [mul_pow, div_le_iff₀ (by positivity)] at hexp
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE hcj]
    nlinarith
  have h3 : Real.exp (-(c * r ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  calc (1 + r) ^ j * Real.exp (-(c * r ^ 2))
      ≤ 2 ^ j * (1 + (r ^ 2) ^ j) * Real.exp (-(c * r ^ 2)) := by gcongr
    _ = 2 ^ j * (Real.exp (-(c * r ^ 2)) + (r ^ 2) ^ j * Real.exp (-(c * r ^ 2))) := by ring
    _ ≤ 2 ^ j * (1 + j.factorial / c ^ j) :=
        mul_le_mul_of_nonneg_left (add_le_add h3 h2) h2j.le

theorem gs_sch {m n : ℕ} (c : ℝ) (hc : 0 < c) :
    ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, S u = gs c u := by
  have hqT := hasTemperateGrowth_const_mul_sum_norm_sq (m := m) (n := n) c
  have hhC : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Complex.exp (-(s : ℂ))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg)
  have hgs : (gs c : (Fin m → Fin n → ℂ) → ℂ) =
      (fun s : ℝ => Complex.exp (-(s : ℂ))) ∘
        (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
    funext u
    simp [gs]
  have hlow : ∀ u : Fin m → Fin n → ℂ, ‖u‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by
    intro u
    have hS0 : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by positivity
    have hb : ‖u‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      have h1 : ‖u a i‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
        calc ‖u a i‖ ^ 2 ≤ ∑ i' : Fin n, ‖u a i'‖ ^ 2 :=
              Finset.single_le_sum (f := fun i' => ‖u a i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ i)
          _ ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
              Finset.single_le_sum (f := fun a' => ∑ i' : Fin n, ‖u a' i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ a)
      have h2 := Real.abs_le_sqrt h1
      rwa [abs_of_nonneg (norm_nonneg _)] at h2
    calc ‖u‖ ^ 2 ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = _ := Real.sq_sqrt hS0
  refine ⟨⟨gs c, ?_, ?_⟩, fun u => rfl⟩
  · rw [hgs]
    exact hhC.comp hqT.1
  · intro k N
    obtain ⟨K, C, hC0, hC⟩ := hqT.norm_iteratedFDeriv_le_uniform N
    obtain ⟨M, hM⟩ := exists_bound_one_add_pow_mul_exp_neg_sq c hc (k + K * N)
    refine ⟨N.factorial * (C + 1) ^ N * M, fun u => ?_⟩
    have hu0 := norm_nonneg u
    have hD1 : 1 ≤ (C + 1) * (1 + ‖u‖) ^ K :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
    have hD : ∀ i : ℕ, 1 ≤ i → i ≤ N →
        ‖iteratedFDeriv ℝ i
          (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) u‖ ≤
          ((C + 1) * (1 + ‖u‖) ^ K) ^ i := by
      intro i hi1 hiN
      calc _ ≤ C * (1 + ‖u‖) ^ K := hC i hiN u
        _ ≤ (C + 1) * (1 + ‖u‖) ^ K := by gcongr; linarith
        _ ≤ _ := le_self_pow₀ hD1 (by omega)
    have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := N) hhC hqT.1
      (by exact_mod_cast le_top) u
      (C := Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)))
      (fun i _ => (norm_iteratedFDeriv_cexp_neg_eq_exp_neg i _).le) hD
    have hexp_le : Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ≤
        Real.exp (-(c * ‖u‖ ^ 2)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left (hlow u) hc.le
      linarith
    have hpow : ‖u‖ ^ k ≤ (1 + ‖u‖) ^ k := pow_le_pow_left₀ hu0 (by linarith) k
    rw [hgs]
    calc ‖u‖ ^ k * ‖iteratedFDeriv ℝ N _ u‖
        ≤ (1 + ‖u‖) ^ k * (N.factorial * Real.exp (-(c * ‖u‖ ^ 2)) *
            ((C + 1) * (1 + ‖u‖) ^ K) ^ N) := by
          refine mul_le_mul hpow (key.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = N.factorial * (C + 1) ^ N *
            ((1 + ‖u‖) ^ (k + K * N) * Real.exp (-(c * ‖u‖ ^ 2))) := by
          rw [mul_pow, ← pow_mul, pow_add]
          ring
      _ ≤ N.factorial * (C + 1) ^ N * M := by
          gcongr
          exact hM _ hu0

theorem schFP : SchFP := by
  intro m n c hc P
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => evX P u) S, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evX_temperate P)]
  funext u
  simp [fP, hS, smul_eq_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def Dv (X : Matrix (Fin m) (Fin m) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  MvPolynomial.mkDerivation ℂ (fun k : Fin m × Fin n × Bool => xyP X k.1 k.2.1 k.2.2)

theorem Dv_X (X : Matrix (Fin m) (Fin m) ℂ) (k : Fin m × Fin n × Bool) :
    Dv X (MvPolynomial.X k : PX m n) = xyP X k.1 k.2.1 k.2.2 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem Dv_eq (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    Dv X P = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k P := by
  let D₂ : Derivation ℂ (PX m n) (PX m n) :=
    ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • pderiv k
  have hs : ∀ Q : PX m n, D₂ Q = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k Q := by
    intro Q
    show (Derivation.coeFnAddMonoidHom (R := ℂ) (A := PX m n) (M := PX m n)
      (∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • (pderiv k : Derivation ℂ (PX m n) (PX m n)))) Q = _

    rw [map_sum, Finset.sum_apply]
    simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
  have h : Dv X P = D₂ P := by
    refine MvPolynomial.derivation_eq_of_forall_mem_vars (fun i _ => ?_)
    rw [hs, Dv_X]
    simp [pderiv_X, Pi.single_apply]
  rw [h, hs]

def Q2 (m n : ℕ) : PX m n := ∑ a, ∑ i, MvPolynomial.X (a, i, false) * MvPolynomial.X (a, i, true)

theorem derivation_quadraticForm_eq_sum (X : Matrix (Fin m) (Fin m) ℂ) :
    Dv X (Q2 m n) = ∑ a, ∑ i, (MvPolynomial.X (a, i, false) * xyP X a i true + MvPolynomial.X (a, i, true) * xyP X a i false) := by

  simp only [Q2, map_sum, Derivation.leibniz, Dv_X, smul_eq_mul]

theorem vfX_eq_Dv (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    vfX c X P = Dv X P - C (c : ℂ) * Dv X (Q2 m n) * P := by
  rw [Dv_eq, derivation_quadraticForm_eq_sum, vfX]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  ring

theorem eval_xyP (X : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (xyP X a i b) =
      if b then star (matL X u a i) else matL X u a i := by
  cases b <;> simp [xyP, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord, matL_apply, star_sum, star_mul']

theorem gs_eq (c : ℝ) (u : Fin m → Fin n → ℂ) :
    gs c u = Complex.exp (-(c : ℂ) * MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (Q2 m n)) := by
  rw [gs]
  congr 1

  simp only [Q2, map_sum, map_mul, MvPolynomial.eval_X, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord]
  push_cast
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Finset.mul_sum]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {σ : Type*} [Fintype σ] (g : ℝ → σ → ℂ) (g' : σ → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (Q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0 := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun Q => HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0) Q ?_ ?_ ?_
  · intro a
    simpa using hasDerivAt_const (0 : ℝ) a
  · intro p q hp hq
    refine ((hp.fun_add hq).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [mul_add, Finset.sum_add_distrib]
    · exact Filter.Eventually.of_forall (fun t => by simp)
  · intro p k hp
    refine ((hp.fun_mul (hg k)).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib,
        apply_ite, Finset.sum_ite_eq]
      rw [add_comm]
      congr 1
      · ring
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    · exact Filter.Eventually.of_forall (fun t => by simp)

theorem hasDerivAt_curve (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) (fP c (vfX c X P) x) 0 := by
  set u : ℝ → (Fin m → Fin n → ℂ) := fun t => matL (NormedSpace.exp ((t : ℂ) • X)) x with hu
  have hu0 : u 0 = x := by simp [hu, matL_one]
  clear_value u
  rw [show (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) =
    fun t => fP c P (u t) by rw [hu]]
  let e : (Fin m → Fin n → ℂ) → Fin m × Fin n × Bool → ℂ :=
    fun v k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k v
  have hg : ∀ k, HasDerivAt (fun t => e (u t) k) (MvPolynomial.eval (e x) (xyP X k.1 k.2.1 k.2.2)) 0 := by
    rintro ⟨a, i, b⟩
    have hlin : HasDerivAt (fun t => u t a i) (matL X x a i) 0 := by
      have hs := HasDerivAt.fun_sum (u := Finset.univ)
        (fun c (_ : c ∈ Finset.univ) => (hasDerivAt_entry X a c).mul_const (x c i))
      simpa only [hu, matL_apply] using hs
    rw [eval_xyP]
    cases b
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin.star
  have hf : (fun t : ℝ => fP c P (u t)) = fun t => MvPolynomial.eval (e (u t)) P *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e (u t)) (Q2 m n)) := by
    funext t
    rw [fP, gs_eq]
    rfl
  have hx : fP c (vfX c X P) x = MvPolynomial.eval (e x) (vfX c X P) *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e x) (Q2 m n)) := by
    rw [fP, gs_eq]
    rfl
  rw [hf, hx, vfX_eq_Dv, Dv_eq X P, Dv_eq X (Q2 m n)]
  have hP := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg P
  have hQ := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg (Q2 m n)
  have H := hP.fun_mul ((hQ.const_mul (-(c : ℂ))).cexp)
  rw [hu0] at H
  refine H.congr_deriv ?_

  simp only [map_sub, map_mul, map_sum, MvPolynomial.eval_C]
  ring

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def OpCLM : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ∃ L : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ),
        (ω (ι y) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩).1 = tens θ τ fr (L S) Ψ

def AwayFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), g = x * ι y ∧ ∀ Ψ, AwayCls θ τ fr Ψ → ∃ Ψ', AwayCls θ τ fr Ψ' ∧
      ∀ (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ) (hS : tens θ τ fr S Ψ ∈ schwartzA θ V.rank n),
        (ω x ⟨tens θ τ fr S Ψ, hS⟩).1 = tens θ τ fr S Ψ'

def SchDeriv : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n),
    ∃ (S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ) (S' : SchwartzMap (Fin m → Fin n → ℂ) ℂ),
      (∀ t y, S t y = fP c P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin m) (Fin m) ℂ) * (Matrix.of y : Matrix (Fin m) (Fin n) ℂ))) ∧
      (∀ y, S' y = fP c (vfX c X P) y) ∧
        Filter.Tendsto (fun t : ℝ => t⁻¹ • (S t - S 0)) (nhdsWithin 0 {0}ᶜ) (nhds S')

end PositivityTheory.Rg.Sw.Glob
end
end
