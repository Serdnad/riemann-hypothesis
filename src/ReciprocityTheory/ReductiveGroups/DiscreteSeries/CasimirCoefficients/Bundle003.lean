module

import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBInvar
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.SignedIdentityColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}

lemma prod_ofFn_sum {α : Type*} [Fintype α] : ∀ {p : ℕ} (f : Fin p → α → 𝒰),
    (List.ofFn fun j => ∑ a, f j a).prod = ∑ γ : Fin p → α, (List.ofFn fun j => f j (γ j)).prod
  | 0, f => by simp
  | p + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_sum (fun j => f j.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ : Fin (p + 1) => α).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun γ _ => ?_
    show _ = (List.ofFn fun j => f j (Fin.cons (α := fun _ => α) a γ j)).prod
    simp only [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

lemma prod_ofFn_smul : ∀ {p : ℕ} (s : Fin p → ℂ) (a : Fin p → 𝒰),
    (List.ofFn fun j => s j • a j).prod = (∏ j, s j) • (List.ofFn a).prod
  | 0, s, a => by simp
  | p + 1, s, a => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [prod_ofFn_smul (fun j => s j.succ) (fun j => a j.succ), Fin.prod_univ_succ, smul_mul_smul_comm]

lemma capEntry_ad (E : Fin n → Fin n → 𝒰) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ)
    (a b : Fin n) :
    capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x a b =
      ∑ c, ∑ d, (P c a * Q b d) • capEntry E x c d := by
  simp only [capEntry, smul_add, Finset.sum_add_distrib]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_smul]
  have h : ∑ c, P c a * Q b c = (Q * P) b a := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [h, hQP, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab, zero_smul]

lemma coef_det (P : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • ∏ j, P (c j) (σ j) = (P.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def]
  rfl

lemma sum_fun_perm {M : Type*} [AddCommMonoid M] (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) : ∑ c, f c = ∑ τ : Equiv.Perm (Fin n), f τ := by
  apply PositivityTheory.Rg.Sw.WR.K.GB.Inv.sum_perm_of_noninj <;> assumption

theorem capelliC_ad (E : Fin n → Fin n → 𝒰) (hE : GlRelR E) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) (x : ℂ) :
    capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x = capelliC E x := by
  classical
  have hstep : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun j : Fin n =>
        capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j).prod =
        ∑ γ : Fin n → Fin n × Fin n, (∏ j, (P (γ j).1 (σ j) * Q j (γ j).2)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
    intro σ
    have h1 : ∀ j : Fin n, capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j =
        ∑ cd : Fin n × Fin n, (P cd.1 (σ j) * Q j cd.2) • capEntry E (x - ((j : ℕ) : ℂ)) cd.1 cd.2 := by
      intro j
      rw [capEntry_ad E P Q hQP, Fintype.sum_prod_type]
    simp_rw [h1]
    rw [prod_ofFn_sum]
    exact Finset.sum_congr rfl (fun γ _ => prod_ofFn_smul _ _)
  have hdet : ∀ c : Fin n → Fin n, ¬ Function.Injective c → (P.submatrix c id).det = 0 := by
    intro c hc
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      by_contra h
      push_neg at h
      exact hc (fun i j hij => h i j hij)
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
  have hS : ∀ d : Fin n → Fin n,
      ∑ c : Fin n → Fin n, (P.submatrix c id).det •
        (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod =
        P.det • cminor E id d x := by
    intro d
    rw [sum_fun_perm _ (fun c hc => by rw [hdet c hc, zero_smul])]
    unfold cminor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Matrix.det_permute, mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul ℂ]
    simp only [id]
  have hQ : ∑ ρ : Equiv.Perm (Fin n), ((Equiv.Perm.sign ρ : ℤˣ) : ℤ) • ∏ j, Q j (ρ j) = Q.det := by
    have := coef_det Q id
    simpa using this
  calc capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x
      = ∑ γ : Fin n → Fin n × Fin n,
          ((P.submatrix (fun j => (γ j).1) id).det * ∏ j, Q j (γ j).2) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
        unfold capelliC cminor
        simp only [id]
        simp_rw [hstep, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        rw [← coef_det P (fun j => (γ j).1), Finset.sum_mul, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.prod_mul_distrib, smul_mul_assoc, smul_assoc]
    _ = ∑ d : Fin n → Fin n, ∑ c : Fin n → Fin n,
          ((P.submatrix c id).det * ∏ j, Q j (d j)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod := by
        let e : (Fin n → Fin n) × (Fin n → Fin n) ≃ (Fin n → Fin n × Fin n) :=
          ⟨fun cd j => (cd.1 j, cd.2 j), fun γ => (fun j => (γ j).1, fun j => (γ j).2),
            fun _ => rfl, fun _ => rfl⟩
        rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
        rfl
    _ = ∑ d : Fin n → Fin n, (∏ j, Q j (d j)) • (P.det • cminor E id d x) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [← hS d, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [smul_smul, mul_comm]
    _ = ∑ ρ : Equiv.Perm (Fin n), (∏ j, Q j (ρ j)) • (P.det • cminor E id ρ x) := by
        apply sum_fun_perm
        intro d hd
        rw [cminor_cols_not_inj E hE id d x hd, smul_zero, smul_zero]
    _ = (P.det * Q.det) • capelliC E x := by
        rw [← hQ, Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        have hc := cminor_perm_cols E hE id id ρ x
        unfold capelliC
        rw [show (id : Fin n → Fin n) ∘ ρ = ρ from rfl] at hc
        rw [hc, smul_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        congr 1
        rw [zsmul_eq_mul]
        ring
    _ = capelliC E x := by
        rw [← Matrix.det_mul, hPQ, Matrix.det_one, one_smul]

end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma ccb_JJ (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * A) = A := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]

lemma ccb_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add,
    show (Z - Jm ε * Zᴴ * Jm ε) + (Z + Jm ε * Zᴴ * Jm ε) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num

lemma ccb_inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart1 ε Z) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJH : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold inG cpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, smul_add, smul_sub, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg]
  abel

lemma ccb_inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart2 ε Z) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJH : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    first
    | (simp [Complex.conj_I]; ring)
    | (rw [star_div', star_one, star_mul', Complex.star_def, Complex.conj_I]; field_simp; ring)
    | (apply Complex.ext <;> simp [Complex.div_re, Complex.div_im])
  unfold inG cpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH,
    Matrix.conjTranspose_conjTranspose, hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc, hJ, ccb_JJ, Matrix.mul_one, neg_smul, smul_add, smul_neg,
    neg_one_smul, Matrix.neg_mul, Matrix.mul_neg, neg_add]
  abel

lemma ccb_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
    NormedSpace.exp_zero]

lemma ccb_exp_inUJ (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hXh : Xᴴ = -(Jm ε * X * Jm ε) := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left (show Xᴴ * Jm ε + Jm ε * X = 0 from hX)
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]
  have hs : star ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  have e2 : (t : ℂ) • -(Jm ε * X * Jm ε) = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hs, hXh, e2, Matrix.exp_conj _ _ hJu, hJinv]
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [Matrix.mul_assoc (Jm ε * _) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc]
    _ = Jm ε := by rw [ccb_exp_neg_mul, Matrix.mul_one]

lemma ccb_inUJ_mul (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hh : inUJ ε h) : inUJ ε (g * h) := by
  unfold inUJ at *
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

section Paths
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma ccb_path_right (X y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * y) (X * y) 0 :=
  (dga_exp X).mul_const y

lemma ccb_path_left (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  (dga_exp X).const_mul g

end Paths

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ccb_rdv (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {V W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ}
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V) (hW : IsOpen W)
    (hWV : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ g ∈ W, inUJ ε g → f g = F (g⁻¹ * m)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X)))
      (-(fderiv ℂ F (g⁻¹ * m) (X * (g⁻¹ * m)))) 0 := by
  set y := g⁻¹ * m with hy
  have hyV : y ∈ V := (hWV g hg).2
  have hΦ : HasFDerivAt F (fderiv ℂ F y) y := (hF.differentiableAt (hV.mem_nhds hyV)).hasFDerivAt
  have h0 : y = NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)) * y := by simp
  have h1 : HasDerivAt (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y))
      (fderiv ℂ F y (-X * y)) 0 :=
    (hΦ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (ccb_path_right (-X) y) h0
  have hcont : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
    (ccb_path_left g X).continuousAt
  have hW0 : W ∈ nhds ((fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) := by
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact hW.mem_nhds hg
  have hev : ∀ᶠ t : ℝ in nhds 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ W :=
    hcont.preimage_mem_nhds hW0
  have hfin : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • (-X)) * y) := by
    filter_upwards [hev] with t ht
    rw [hf _ ht (ccb_inUJ_mul ε hgu (ccb_exp_inUJ ε hX t)), Matrix.mul_inv_rev, smul_neg,
      Matrix.exp_neg, Matrix.mul_assoc]
  have h2 := h1.congr_of_eventuallyEq hfin
  rwa [Matrix.neg_mul, map_neg] at h2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def IsMu (lam : Fin n → ℝ) (μ : Fin n → ℤ) : Prop := ∀ a, (μ a : ℝ) = lam a + rho n a

def muNext (μ : Fin n → ℤ) (i : Fin n) : ℤ := if h : (i : ℕ) + 1 < n then μ ⟨(i : ℕ) + 1, h⟩ else 0

def lead (i : ℕ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if h : i ≤ n then (z.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def PhiM (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))

def OmegaSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {z | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}

lemma isClosed_Kset (ε : Fin n → Bool) : IsClosed (Kset ε) := by
  have h1 : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | star g * g = 1 ∧ g * star g = 1} :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  have h2 : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | g * Jm ε = Jm ε * g} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  convert h1.inter h2 using 1
  ext g
  simp only [Kset, Set.mem_ofPred_eq, Set.mem_inter_iff, Matrix.unitaryGroup]
  exact Iff.rfl

lemma isClosed_KG (ε : Fin n → Bool) : IsClosed ((KG ε : Set (UJ ε))) := by
  show IsClosed {g : UJ ε | toM g ∈ Kset ε}
  exact (isClosed_Kset ε).preimage (continuous_toM ε)

instance (ε : Fin n → Bool) : LocallyCompactSpace (KG ε) := (isClosed_KG ε).locallyCompactSpace

-- Keep the instance name stable across builds of the downstream Haar modules.
instance instMeasurableSpaceSubtypeUnitsMatrixFinComplexMemSubgroupUJKG
    (ε : Fin n → Bool) : MeasurableSpace (KG ε) := borel _

instance (ε : Fin n → Bool) : BorelSpace (KG ε) := ⟨rfl⟩

def muK (ε : Fin n → Bool) : Measure (KG ε) := Measure.haar

def projW {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.V →L[ℂ] T.V :=
  (innerSL ℂ T.w).smulRight T.w

def psM {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (x : Matrix (Fin n) (Fin n) ℂ) : T.V →L[ℂ] T.V :=
  ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
    ∫ k, PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)


open Classical in
def PsiM {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (g : Matrix (Fin n) (Fin n) ℂ) : T.V →L[ℂ] T.V :=
  if h : ∃ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = toMK k * NormedSpace.exp X then
    T.op h.choose * psM T μ (NormedSpace.exp h.choose_spec.choose)
  else 0

section Calc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IsLowerTri (c : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a b : Fin n, a < b → c a b = 0

def IsUpperTri (c : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a b : Fin n, b < a → c a b = 0

def IsBlock (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a b : Fin n, ε a ≠ ε b → X a b = 0

def lowMinusUp (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if b < a then B a b else if a < b then -B a b else 0

def posSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {x | x.PosDef}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Lhol (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => fderiv ℂ F z (X * z)

def Rhol (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => fderiv ℂ F z (z * X)

def casL (F : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) F) z

end Calc

def Gint {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : T.V →L[ℂ] T.V :=
  PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * projW T * T.op k⁻¹)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {ε : Fin n → Bool}

lemma exists_signVG (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (SgIxV ε s) = q0 ε := by
  unfold q0
  rcases le_total (pOf ε) (qOf ε) with h | h
  · refine ⟨true, ?_⟩
    rw [min_eq_left h]
    first
    | (rw [pOf, Fintype.card_subtype])
    | simp [SgIxV, pOf, Fintype.card_subtype]
  · refine ⟨false, ?_⟩
    rw [min_eq_right h]
    first
    | (rw [qOf, Fintype.card_subtype])
    | simp [SgIxV, qOf, Fintype.card_subtype]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
