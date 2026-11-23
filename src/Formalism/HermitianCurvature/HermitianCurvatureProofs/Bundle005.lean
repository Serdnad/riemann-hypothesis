module

public import Formalism.HermitianCurvature.Bundle001
public import Formalism.HermitianCurvature.StatementG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.Cauchy

open Complex Metric Set

theorem iteratedDeriv_ofReal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {f : ℝ → ℝ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hfF : ∀ x : ℝ, F x = f x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧
      ∀ x : ℝ, iteratedDeriv p F x = (iteratedDeriv p f x : ℝ) := by
  induction p with
  | zero => simpa using ⟨hF, hfF⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h1 : HasDerivAt (fun y : ℝ => (iteratedDeriv p F y).re)
          (deriv (iteratedDeriv p F) x).re x := h0.real_of_complex
      have h2 : (fun y : ℝ => (iteratedDeriv p F y).re) = iteratedDeriv p f := by
        funext y; rw [he y]; simp
      rw [h2] at h1
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y)
          (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = fun y : ℝ => ((iteratedDeriv p f y : ℝ) : ℂ) := by
        funext y; rw [he y]
      rw [h4] at h3
      have h5 := h3.unique h1.ofReal_comp
      rw [h1.deriv]
      exact h5

theorem rpow_le_exp_one {σ : ℝ} (hσ : 4 ≤ σ) : (1 - 2 * (1 / (4 * σ))) ^ (-σ) ≤ Real.exp 1 := by
  have hσ0 : 0 < σ := by linarith
  have hx : 0 < 1 - 2 * (1 / (4 * σ)) := by
    have : 1 / (4 * σ) ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  have h1 := Real.one_sub_inv_le_log_of_pos hx
  have h2 : (1 - 2 * (1 / (4 * σ)))⁻¹ = 2 * σ / (2 * σ - 1) := by
    have h21 : 1 - 2 * (1 / (4 * σ)) = (2 * σ - 1) / (2 * σ) := by
      field_simp
      ring
    rw [h21, inv_div]
  rw [h2] at h1
  have h3 : 1 - 2 * σ / (2 * σ - 1) = -(1 / (2 * σ - 1)) := by
    have : 2 * σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h3] at h1
  have h4 : 1 / (2 * σ - 1) ≤ 1 / σ := by
    apply one_div_le_one_div_of_le <;> linarith
  have h5 : -(1 / σ) ≤ Real.log (1 - 2 * (1 / (4 * σ))) := by linarith
  have h6 : σ * -(1 / σ) ≤ σ * Real.log (1 - 2 * (1 / (4 * σ))) :=
    mul_le_mul_of_nonneg_left h5 hσ0.le
  have h7 : σ * -(1 / σ) = -1 := by field_simp
  nlinarith

theorem base_bound {ε : ℝ} (hε : 0 < ε) (u : ℝ) {ρ : ℝ} (hρ : ρ ≤ 1 / 16) {w : ℂ}
    (hw : ‖w - u‖ ≤ ρ) :
    (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ (1 + (ε : ℂ) * Complex.exp (-w)).re := by
  set a : ℝ := ε * Real.exp (-u) with ha
  have ha0 : 0 < a := by positivity
  have h1 : 1 + (ε : ℂ) * Complex.exp (-w) = ((1 + a : ℝ) : ℂ) + (a : ℂ) * (Complex.exp (-(w - u)) - 1) := by
    have : Complex.exp (-w) = Complex.exp (-(u : ℂ)) * Complex.exp (-(w - u)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this, ha]
    push_cast
    ring
  have h2 : ‖Complex.exp (-(w - u)) - 1‖ ≤ 2 * ρ := by
    have h := Complex.norm_exp_sub_one_le (x := -(w - u)) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h
    linarith
  have h3 : -(2 * ρ) ≤ (Complex.exp (-(w - u)) - 1).re := by
    have := Complex.abs_re_le_norm (Complex.exp (-(w - u)) - 1)
    have := neg_abs_le (Complex.exp (-(w - u)) - 1).re
    linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hw
  have h4 : a * -(2 * ρ) ≤ a * (Complex.exp (-(w - u)) - 1).re :=
    mul_le_mul_of_nonneg_left h3 ha0.le
  rw [h1, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  nlinarith

end Formalism.FourierDecayAlt.P.Cauchy

namespace Formalism.FourierDecayAlt.P

open Complex Metric Set Formalism.FourierDecayAlt.P.Cauchy

theorem cauchy_theta_identity : Formalism.FourierDecayAlt.E.CauchyTheta := by
  intro σ ε hσ hε p u
  set ρ : ℝ := 1 / (4 * σ) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ : ρ ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le <;> linarith
  set F : ℂ → ℂ := fun w => (1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ) with hF
  set f : ℝ → ℝ := fun v => (1 + ε * Real.exp (-v)) ^ (-σ) with hf
  set U : Set ℂ := {w | 0 < (1 + (ε : ℂ) * Complex.exp (-w)).re} with hUdef
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    fun_prop
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.cpow_const (by fun_prop)
    exact Or.inl hw
  have hpos : ∀ x : ℝ, 0 < 1 + ε * Real.exp (-x) := fun x => by positivity
  have hcast : ∀ x : ℝ, 1 + (ε : ℂ) * Complex.exp (-(x : ℂ)) = ((1 + ε * Real.exp (-x) : ℝ) : ℂ) := by
    intro x; push_cast; ring
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ U := by
    intro x
    show 0 < (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))).re
    rw [hcast, Complex.ofReal_re]
    exact hpos x
  have hfF : ∀ x : ℝ, F x = f x := by
    intro x
    show (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))) ^ ((-σ : ℝ) : ℂ) = _
    rw [hcast, ← Complex.ofReal_cpow (hpos x).le]
  have key := (iteratedDeriv_ofReal hU hFd hmem hfF p).2 u
  have hA : 0 < 1 + ε * Real.exp (-u) := hpos u
  have h12 : 0 < 1 - 2 * ρ := by linarith
  have hsub : closedBall (u : ℂ) ρ ⊆ U := by
    intro w hw
    have := base_bound hε u hρ (w := w) (by simpa [dist_eq_norm] using hw)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    exact lt_of_lt_of_le h0 this
  have hC : ∀ w ∈ sphere (u : ℂ) ρ, ‖F w‖ ≤ Real.exp 1 * (1 + ε * Real.exp (-u)) ^ (-σ) := by
    intro w hw
    have hb := base_bound hε u hρ (w := w) (by
      have : ‖w - u‖ = ρ := by simpa [dist_eq_norm] using hw
      exact this.le)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    have hn : (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ ‖1 + (ε : ℂ) * Complex.exp (-w)‖ :=
      hb.trans (Complex.re_le_norm _)
    show ‖(1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_cpow_real]
    calc ‖1 + (ε : ℂ) * Complex.exp (-w)‖ ^ (-σ)
        ≤ ((1 + ε * Real.exp (-u)) * (1 - 2 * ρ)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos h0 hn (by linarith)
      _ = (1 + ε * Real.exp (-u)) ^ (-σ) * (1 - 2 * ρ) ^ (-σ) :=
          Real.mul_rpow hA.le h12.le
      _ ≤ (1 + ε * Real.exp (-u)) ^ (-σ) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (rpow_le_exp_one hσ) (by positivity)
      _ = _ := mul_comm _ _
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le p hρ0
    (hFd.diffContOnCl_ball hsub) hC
  rw [key, Complex.norm_real, Real.norm_eq_abs] at hcau
  refine hcau.trans (le_of_eq ?_)
  rw [hρdef, one_div, inv_pow, div_inv_eq_mul]
  ring

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.E2

open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory

theorem bdd_add' {Λ : Type} {f g : Λ → ℂ} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨a + b, fun x => (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩

theorem bdd_smul' {Λ : Type} {f : Λ → ℂ} (c : ℂ) (hf : Bdd f) : Bdd (c • f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨‖c‖ * a, fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _)⟩

theorem bdd_zero' {Λ : Type} : Bdd (0 : Λ → ℂ) := ⟨0, fun x => by simp⟩

theorem bdd_sum' {Λ ι : Type} (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    Bdd (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using bdd_zero'
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact bdd_add' (hf a) ih

theorem lim_sum' {Λ ι : Type} (LIM : (Λ → ℂ) → ℂ)
    (h1 : ∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g)
    (h2 : ∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f)
    (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    LIM (∑ i ∈ T, f i) = ∑ i ∈ T, LIM (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := h2 0 0 bdd_zero'
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1 _ _ (hf a) (bdd_sum' s f hf), ih]

theorem mpd : MeanPosDef := by
  intro Λ _ H _ _ LIM h1 h2 h3 h4 u B hu S c
  have hB : ∀ a b : Λ, Bdd (fun x => inner ℂ (u (x + a)) (u (x + b))) := fun a b =>
    ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul (hu _) (hu _) (norm_nonneg _) ((norm_nonneg _).trans (hu (x+a))))⟩
  have hB0 : ∀ b : Λ, Bdd (fun x => inner ℂ (u x) (u (x + b))) := fun b => by simpa using hB 0 b
  have e1 : ∀ σ σ' : Λ, LIM (fun x => inner ℂ (u x) (u (x + (σ - σ'))))
      = LIM (fun x => inner ℂ (u (x + σ')) (u (x + σ))) := by
    intro σ σ'
    rw [← h4 _ σ' (hB0 (σ - σ'))]
    congr 1; funext x; congr 2; abel
  have e2 : (∑ σ ∈ S, ∑ σ' ∈ S,
        LIM (fun x => inner ℂ (u x) (u (x + (σ - σ')))) * c σ * starRingEnd ℂ (c σ'))
      = LIM (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) := by
    rw [lim_sum' LIM h1 h2 S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lim_sum' LIM h1 h2 S _ (fun σ' => bdd_smul' _ (hB σ' σ))]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [h2 _ _ (hB σ' σ), e1]; ring
  rw [e2]
  apply h3
  · exact bdd_sum' S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))
  · intro x
    have key : (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) x
        = inner ℂ (∑ σ ∈ S, c σ • u (x + σ)) (∑ σ ∈ S, c σ • u (x + σ)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [key]
    exact ⟨inner_self_nonneg (𝕜 := ℂ), inner_self_im (𝕜 := ℂ) _⟩

end Formalism.FourierDecayAlt.P.E2

theorem Formalism.FourierDecayAlt.P.mean_matrix_posDef : Formalism.FourierDecayAlt.E.MeanPosDef := Formalism.FourierDecayAlt.P.E2.mpd
end

section

open Matrix MeasureTheory

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.G5

open Formalism.FourierDecayAlt.G

instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

theorem wMat_mul_self (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  have key : ∀ k : Fin d, (if k = i.rev then (1:ℂ) else 0) * (if j = k.rev then (1:ℂ) else 0) =
      if k = i.rev then (if i = j then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = i.rev
    · simp [hk, eq_comm]
    · simp [hk]
  simp only [wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, key]
  simp

theorem norm_det_wMat (d : ℕ) : ‖(wMat d).det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (wMat_mul_self d)
  simp only [Matrix.det_mul, norm_mul, Matrix.det_one, norm_one] at h
  nlinarith [norm_nonneg (wMat d).det]

theorem det_upper {d : ℕ} (v : UT d → ℂ) : (upper v).det = 1 := by
  have h : (upper v).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    simp [upper, strictUpper, hij'.ne', not_lt.2 hij'.le]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper, strictUpper]

theorem continuous_upper (d : ℕ) : Continuous (upper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) := by
  refine continuous_matrix fun i j => ?_
  simp only [upper, strictUpper, Matrix.add_apply, Matrix.of_apply]
  refine continuous_const.add ?_
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem card_UT (n : ℕ) : Fintype.card (UT n) = ∑ i ∈ Finset.range n, i := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp_rw [← Finset.card_filter]
  have : ∀ y : Fin n, (Finset.univ.filter (fun x : Fin n => x < y)).card = (y : ℕ) := by
    intro y
    rw [show Finset.univ.filter (fun x : Fin n => x < y) = Finset.Iio y by ext; simp]
    exact Fin.card_Iio y
  simp_rw [this]
  exact Fin.sum_univ_eq_sum_range (fun i => i) n

theorem symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd (n := 1) i

theorem symm_last (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) :=
  finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  simp [blk, symm_castSucc]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  simp [blk, symm_last]

theorem continuous_inv_upper (d : ℕ) : Continuous (fun v : UT d → ℂ => (upper v)⁻¹) := by
  have h : (fun v : UT d → ℂ => (upper v)⁻¹) = fun v => (upper v).adjugate := by
    funext v
    rw [Matrix.inv_def, det_upper, Ring.inverse_one, one_smul]
  rw [h]
  exact (continuous_upper d).matrix_adjugate

theorem mp_comp_equiv (β : ℂ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι') :
    MeasurePreserving (fun v : ι' → ℂ => v ∘ σ) (muPi β ι') (muPi β ι) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : ι => ℂ) (fun _ : ι => mu β) σ.symm
  have he : (fun v : ι' → ℂ => v ∘ σ) = MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) σ.symm := by
    funext v i
    obtain ⟨j, rfl⟩ := σ.symm.surjective i
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    simp
  rw [he]
  exact h

theorem wMat_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (wMat n * A) i j = A i.rev j := by
  simp [wMat, Matrix.mul_apply]

theorem mul_wMat_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A * wMat n) i j = A i j.rev := by
  have h : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [wMat, Matrix.mul_apply, h]

end Formalism.FourierDecayAlt.P.G5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5

end Formalism.FourierDecayAlt.P
end

section

open Matrix
open Formalism.FourierDecayAlt.G

namespace Formalism.FourierDecayAlt.P.G4

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem upperUni_det {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u.det = 1 := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hu.1]

theorem superSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    superSum (blk A b a e) = superSum A + b (Fin.last m) := by
  unfold superSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_cl]

theorem subSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    subSum (blk A b a e) = subSum A + a (Fin.last m) := by
  unfold subSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_lc]

end Formalism.FourierDecayAlt.P.G4

namespace Formalism.FourierDecayAlt.P

open G4

end Formalism.FourierDecayAlt.P
end
