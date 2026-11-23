module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Lemma
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

open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.Boost

theorem vmv_mulVec {m : ℕ} (u v w : Fin m → ℂ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem boost_exists : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := by
  intro m ε a b ha hb hn
  set c2 : ℝ := ∑ j, ‖a j‖ ^ 2 with hc2
  set nb : ℝ := ∑ j, ‖b j‖ ^ 2 with hnb
  have hnb0 : 0 ≤ nb := Finset.sum_nonneg fun _ _ => by positivity
  have hc1 : 1 ≤ c2 := by linarith
  have hJa : Jm ε *ᵥ a = a := by
    ext i; simp only [Jm, mulVec_diagonal]
    cases h : ε i <;> simp [ha i, h]
  have hJb : Jm ε *ᵥ b = -b := by
    ext i; simp only [Jm, mulVec_diagonal]
    cases h : ε i <;> simp [hb i, h]
  have hJa' : ∀ w, star a ⬝ᵥ (Jm ε *ᵥ w) = star a ⬝ᵥ w := by
    intro w; simp only [Jm, mulVec_diagonal, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [ha i, h]
  have hJb' : ∀ w, star b ⬝ᵥ (Jm ε *ᵥ w) = -(star b ⬝ᵥ w) := by
    intro w; simp only [Jm, mulVec_diagonal, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [hb i, h]
  have haa : star a ⬝ᵥ a = (c2 : ℂ) := by
    simp only [dotProduct, hc2, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
    push_cast; rfl
  have hbb : star b ⬝ᵥ b = (c2 : ℂ) - 1 := by
    have : star b ⬝ᵥ b = (nb : ℂ) := by
      simp only [dotProduct, hnb, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
      push_cast; rfl
    rw [this, hn]; push_cast; ring
  have hab : star a ⬝ᵥ b = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]
  have hba : star b ⬝ᵥ a = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]

  set s : ℝ := Real.sqrt c2 with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hc1
  have hss : s ^ 2 = c2 := Real.sq_sqrt (by linarith)
  set S : ℂ := (s : ℂ) with hS
  have hS0 : S ≠ 0 := by rw [hS]; exact_mod_cast (by linarith : s ≠ 0)
  have hS1 : S + 1 ≠ 0 := by rw [hS]; exact_mod_cast (by linarith : s + 1 ≠ 0)
  have hSS : S ^ 2 = (c2 : ℂ) := by rw [hS]; exact_mod_cast hss
  set α : ℂ := (S - 1) / S ^ 2 with hα
  set β : ℂ := 1 / (S + 1) with hβ
  set γ : ℂ := 1 / S with hγ
  have hsα : star α = α := by simp [hα, hS, Complex.conj_ofReal]
  have hsβ : star β = β := by simp [hβ, hS, Complex.conj_ofReal]
  have hsγ : star γ = γ := by simp [hγ, hS, Complex.conj_ofReal]
  set A : Matrix (Fin m) (Fin m) ℂ := 1 + α • vecMulVec a (star a) + β • vecMulVec b (star b) + γ • (vecMulVec b (star a) + vecMulVec a (star b)) with hA
  have hmul : ∀ w, A *ᵥ w = w + (α * (star a ⬝ᵥ w) + γ * (star b ⬝ᵥ w)) • a + (β * (star b ⬝ᵥ w) + γ * (star a ⬝ᵥ w)) • b := by
    intro w
    simp only [hA, add_mulVec, smul_mulVec, one_mulVec, vmv_mulVec]
    module
  have hherm : Aᴴ = A := by
    simp only [hA, conjTranspose_add, conjTranspose_smul, conjTranspose_one, conjTranspose_vecMulVec, star_star, hsα, hsβ, hsγ]
    rw [add_comm (vecMulVec a (star b))]
  have hU : A ∈ UJset ε := by
    show Aᴴ * Jm ε * A = Jm ε
    rw [hherm, Matrix.ext_iff_mulVec]
    intro v
    rw [← mulVec_mulVec, ← mulVec_mulVec, hmul, hmul]
    simp only [mulVec_add, mulVec_smul, hJa, hJb, dotProduct_add, dotProduct_smul, dotProduct_neg, hJa', hJb', haa, hbb, hab, hba, smul_eq_mul]
    set p := star a ⬝ᵥ v
    set q := star b ⬝ᵥ v
    have hX : α * p + γ * q + α * (p + (α * p + γ * q) * (c2 : ℂ)) + γ * (-q - (β * q + γ * p) * ((c2 : ℂ) - 1)) = 0 := by
      rw [hα, hβ, hγ, ← hSS]; field_simp; ring
    have hY : -(β * q + γ * p) + β * (-q - (β * q + γ * p) * ((c2 : ℂ) - 1)) + γ * (p + (α * p + γ * q) * (c2 : ℂ)) = 0 := by
      rw [hα, hβ, hγ, ← hSS]; field_simp; ring
    linear_combination (norm := module) hX • a + hY • b

  have hAa : A *ᵥ a = S • (a + b) := by
    rw [hmul, haa, hba]
    have e1 : α * (c2 : ℂ) + 1 = S := by rw [hα, ← hSS]; field_simp; try ring
    have e2 : γ * (c2 : ℂ) = S := by rw [hγ, ← hSS]; field_simp; try ring
    linear_combination (norm := module) e1 • a + e2 • b
  have hsq : A * A = 1 + (2 * α + α ^ 2 * (c2 : ℂ) + γ ^ 2 * ((c2 : ℂ) - 1)) • vecMulVec a (star a)
      + (2 * β + β ^ 2 * ((c2 : ℂ) - 1) + γ ^ 2 * (c2 : ℂ)) • vecMulVec b (star b)
      + (2 * γ + α * γ * (c2 : ℂ) + γ * β * ((c2 : ℂ) - 1)) • (vecMulVec a (star b) + vecMulVec b (star a)) := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← mulVec_mulVec, hmul, hmul]
    simp only [add_mulVec, smul_mulVec, one_mulVec, vmv_mulVec, dotProduct_add, dotProduct_smul, haa, hbb, hab, hba, smul_eq_mul]
    module
  have htr : trace (A * A) = (m : ℂ) + 4 * (c2 : ℂ) - 4 := by
    have e1 : a ⬝ᵥ star a = (c2 : ℂ) := by rw [dotProduct_comm]; exact haa
    have e2 : b ⬝ᵥ star b = (c2 : ℂ) - 1 := by rw [dotProduct_comm]; exact hbb
    have e3 : a ⬝ᵥ star b = 0 := by rw [dotProduct_comm]; exact hba
    have e4 : b ⬝ᵥ star a = 0 := by rw [dotProduct_comm]; exact hab
    rw [hsq]
    simp only [trace_add, trace_smul, trace_one, trace_vecMulVec, Fintype.card_fin, smul_eq_mul, e1, e2, e3, e4]
    rw [hα, hβ, hγ, ← hSS]; field_simp; try ring
  have hT : ∑ i, ∑ j, ‖A i j‖ ^ 2 = (m : ℝ) + 4 * c2 - 4 := by
    have : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = trace (A * A) := by
      push_cast
      simp only [trace, Matrix.diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.mul_conj']
      congr 1
      have := congrFun (congrFun hherm j) i
      rw [conjTranspose_apply] at this
      show _ = A j i
      exact this
    rw [htr] at this
    exact_mod_cast this
  have hab2 : ∑ i, ‖a i + b i‖ ^ 2 = c2 + nb := by
    rw [hc2, hnb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases h : ε i <;> simp [ha i, hb i, h]
  refine ⟨A, hU, fun i => ?_, ?_⟩
  · have := congrFun hAa i
    rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    exact this
  · have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    unfold hsn
    rw [Real.sq_sqrt h0, hT, hab2]
    linarith

end GlobalTheory.Boost
end
end

section

namespace GlobalTheory.SepReal

private def optSumLeft (α β : Type) : Option (α ⊕ β) ≃ Option α ⊕ β where
  toFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  invFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro ((_ | _) | _) <;> rfl

theorem exists_signs_equiv {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (h : (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card) :
    ∃ e : Option (Fin n) ≃ Fin (n + 1), Signs e ε ε' := by
  classical
  have hF : Fintype.card {a // ¬ ε a = true} = Fintype.card {i // ¬ ε' i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [Bool.not_eq_true] using h
  have hT : Fintype.card {a // ε a = true} = Fintype.card (Option {i // ε' i = true}) := by
    have h1 := Fintype.card_subtype_compl (fun a => ε a = true)
    have h2 := Fintype.card_subtype_compl (fun i => ε' i = true)
    have h3 := Fintype.card_subtype_le (fun a => ε a = true)
    have h4 := Fintype.card_subtype_le (fun i => ε' i = true)
    simp only [Fintype.card_fin] at h1 h2 h3 h4
    rw [Fintype.card_option]
    omega
  let eT := Fintype.equivOfCardEq hT
  let eF := Fintype.equivOfCardEq hF
  let e : Option (Fin n) ≃ Fin (n + 1) :=
    ((Equiv.optionCongr (Equiv.sumCompl fun i => ε' i = true).symm).trans
      (optSumLeft _ _)).trans ((Equiv.sumCongr eT.symm eF.symm).trans (Equiv.sumCompl fun a => ε a = true))
  refine ⟨e, ?_, ?_⟩
  · show ε ((eT.symm none : {a // ε a = true}) : Fin (n + 1)) = true
    exact (eT.symm none).2
  · intro i
    by_cases hi : ε' i = true
    · have : e (some i) = ((eT.symm (some ⟨i, hi⟩) : {a // ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this, (eT.symm (some ⟨i, hi⟩)).2, hi]
    · have : e (some i) = ((eF.symm ⟨i, hi⟩ : {a // ¬ ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this]
      have := (eF.symm ⟨i, hi⟩).2
      simp only [Bool.not_eq_true] at this hi
      rw [this, hi]

end GlobalTheory.SepReal
end

section

noncomputable section
namespace GlobalTheory.PolarU.SinhcPres
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

variable {p q : ℕ}

theorem ad_sq_pY (B C : Fin p → Fin q → ℂ) : ∃ D,
    pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B = pY D := by
  refine ⟨fun i j => (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)
    (Sum.inl i) (Sum.inr j), ?_⟩
  have hh : (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)ᴴ =
      pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B := by
    simp only [conjTranspose_sub, conjTranspose_mul, pY_conjTranspose]
    noncomm_ring
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]
  · simp only [pY, pOf, fromBlocks_apply₁₂, of_apply]
  · have := congrFun (congrFun hh (Sum.inr i)) (Sum.inl j)
    rw [← this]
    rfl
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]

theorem adMat_pow_pY (B C : Fin p → Fin q → ℂ) (k : ℕ) : ∃ D,
    adMat (pY B) ^ (2 * k) *ᵥ vecM (pY C) = vecM (pY D) := by
  induction k with
  | zero => exact ⟨C, by simp⟩
  | succ k ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨E, hE⟩ := ad_sq_pY B D
    refine ⟨E, ?_⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ', pow_succ', ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hD, adMat_mulVec, adMat_mulVec, hE]

theorem summable_sinhc {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  open scoped Matrix.Norms.Operator in
  refine Summable.of_norm_bounded (g := fun k : ℕ => ‖((k.factorial : ℂ)⁻¹) • (A ^ 2) ^ k‖)
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) (A ^ 2)) fun k => ?_
  rw [norm_smul, norm_smul, ← pow_mul, norm_inv, norm_inv, Complex.norm_natCast,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine inv_anti₀ (by exact_mod_cast k.factorial_pos) ?_
  exact_mod_cast Nat.factorial_le (by omega)

theorem hasSum_sAd (Y V : Mat p q) (a b : Ix p q) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) * (adMat Y ^ (2 * k) *ᵥ vecM V) (a, b))
      (sAd Y V a b) := by
  have h := (summable_sinhc (adMat Y)).hasSum
  let f : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ ℂ :=
    { toFun := fun M => (M *ᵥ vecM V) (a, b)
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.add_mulVec] }
  have hf : Continuous f := by
    show Continuous fun M : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ => (M *ᵥ vecM V) (a, b)
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have h2 := h.map f hf
  convert (preTransparency := .reducible) h2 using 1
  · funext k
    simp [f, Matrix.smul_mulVec]
  · rfl

theorem sAd_pY : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ),
    sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  intro p q B C
  choose D hD using adMat_pow_pY B C
  have h := hasSum_sAd (pY B) (pY C)
  simp only [hD, vecM] at h
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · have := h (Sum.inl i) (Sum.inl j)
    simp only [pY, pOf, fromBlocks_apply₁₁, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero
  · rfl
  · have h1 := h (Sum.inr i) (Sum.inl j)
    have h2 := (h (Sum.inl j) (Sum.inr i)).star
    show _ = star (sAd (pY B) (pY C) (Sum.inl j) (Sum.inr i))
    refine h1.unique ?_
    convert h2 using 2 with k
    simp [pY, pOf]
  · have := h (Sum.inr i) (Sum.inr j)
    simp only [pY, pOf, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero

end GlobalTheory.PolarU.SinhcPres
end
end

section

noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
open scoped Kronecker

section general
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def kronLeftHom (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun Y := Y ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker _ _ _

def kronRightHom (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun Z := (1 : Matrix m m ℂ) ⊗ₖ Z
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ _ _

theorem continuous_kronLeftHom : Continuous (kronLeftHom m n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun Y : Matrix m m ℂ => Y i.1 j.1 * (1 : Matrix n n ℂ) i.2 j.2
  exact (continuous_apply_apply i.1 j.1).mul continuous_const

theorem continuous_kronRightHom : Continuous (kronRightHom m n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun Z : Matrix n n ℂ => (1 : Matrix m m ℂ) i.1 j.1 * Z i.2 j.2
  exact continuous_const.mul (continuous_apply_apply i.2 j.2)

theorem exp_kronecker_one (Y : Matrix m m ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix n n ℂ)) = NormedSpace.exp Y ⊗ₖ (1 : Matrix n n ℂ) := by

  open Norms.Operator in
  exact (NormedSpace.map_exp (kronLeftHom m n) continuous_kronLeftHom Y).symm

theorem exp_one_kronecker (Z : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix m m ℂ) ⊗ₖ Z) = (1 : Matrix m m ℂ) ⊗ₖ NormedSpace.exp Z := by
  open Norms.Operator in
  exact (NormedSpace.map_exp (kronRightHom m n) continuous_kronRightHom Z).symm

end general

theorem kronecker_transpose_mulVec_vecM {p q : ℕ} (A B V : Mat p q) :
    (A ⊗ₖ Bᵀ) *ᵥ vecM V = vecM (A * V * B) := by
  funext ab
  obtain ⟨a, b⟩ := ab
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem exp_adMat_mulVec (p q : ℕ) (Y V : Mat p q) :
    NormedSpace.exp (adMat Y) *ᵥ vecM V =
      vecM (NormedSpace.exp Y * V * NormedSpace.exp (-Y)) := by

  have hsplit : adMat Y = Y ⊗ₖ (1 : Mat p q) + (1 : Mat p q) ⊗ₖ (-Yᵀ) := by
    rw [adMat, sub_eq_add_neg]
    congr 1
    ext i j
    simp [Matrix.kronecker_apply, Matrix.kroneckerMap_apply]
  have hcomm : Commute (Y ⊗ₖ (1 : Mat p q)) ((1 : Mat p q) ⊗ₖ (-Yᵀ)) := by
    show _ * _ = _ * _
    simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_kronecker_one, exp_one_kronecker,
    ← Matrix.mul_kronecker_mul, mul_one, one_mul, ← Matrix.transpose_neg, Matrix.exp_transpose]
  exact kronecker_transpose_mulVec_vecM _ _ _

end GlobalTheory.PolarU
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open scoped ComplexOrder in
theorem det_ne_zero_of_add_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (h : P + Pᴴ = (2 : ℂ) • (1 : Matrix n n ℂ)) : P.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0

  have hquad : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 2 * (star v ⬝ᵥ v) := by
    rw [h]
    first
      | simp [smul_mulVec, dotProduct_smul, smul_eq_mul]
      | simp [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
      | simp [dotProduct_smul, smul_eq_mul]

  have hzero : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 0 := by
    have hstar : star v ᵥ* Pᴴ = star (P *ᵥ v) := (star_mulVec P v).symm
    rw [add_mulVec, dotProduct_add, dotProduct_mulVec (star v) Pᴴ v, hstar, hv]
    simp
  have hnorm : star v ⬝ᵥ v = 0 := by
    have h2 : (2 : ℂ) * (star v ⬝ᵥ v) = 0 := hquad.symm.trans hzero
    rcases mul_eq_zero.mp h2 with h2 | h2
    · norm_num at h2
    · exact h2
  exact dotProduct_star_self_eq_zero.mp hnorm

private lemma isLeft_ne_of_posIx_eq {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) (h1 : posIx y.1 = posIx x.1)
    (h2 : posIx y.2 = posIx x.2) : x.1.isLeft ≠ y.1.isLeft := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases x1 with i | i <;> rcases x2 with j | j <;> rcases y1 with k | k <;> rcases y2 with l | l <;>
    simp_all [sameBlock, posIx, Fin.ext_iff]

private lemma eigP_add_star_eigP_eq_zero {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) : eigP x y + star (eigP y x) = 0 := by
  unfold eigP
  rw [if_neg hne, if_neg (Ne.symm hne)]
  by_cases h : posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2
  · have c1 : ¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2 := ⟨hy, h⟩
    have c2 : ¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2 :=
      ⟨hx, h.1.symm, h.2.symm⟩
    rw [if_pos c1, if_pos c2]
    have hL := isLeft_ne_of_posIx_eq x y hx hy hne h.1 h.2
    generalize x.1.isLeft = s at hL ⊢
    generalize y.1.isLeft = t at hL ⊢
    cases s <;> cases t <;> simp at hL ⊢
  · have c1 : ¬ (¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2) :=
      fun h' => h ⟨h'.2.1, h'.2.2⟩
    have c2 : ¬ (¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2) :=
      fun h' => h ⟨h'.2.1.symm, h'.2.2.symm⟩
    rw [if_neg c1, if_neg c2]
    simp

theorem eigenvectorMatrix_add_star {p q : ℕ} (ab cd : PIx p q) :
    eigP ab.1 cd.1 + star (eigP cd.1 ab.1) = if cd = ab then 2 else 0 := by
  by_cases hc : cd = ab
  · subst hc
    rw [if_pos rfl]
    norm_num [eigP]
  · rw [if_neg hc]
    exact eigP_add_star_eigP_eq_zero ab.1 cd.1 ab.2 cd.2 (fun h => hc (Subtype.ext h))

theorem det_eigenvectorMatrix_ne_zero :
    ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  intro p q
  apply det_ne_zero_of_add_conjTranspose
  ext cd ab
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [eigenvectorMatrix_add_star]
  split_ifs <;> norm_num

end GlobalTheory.PolarU
end
