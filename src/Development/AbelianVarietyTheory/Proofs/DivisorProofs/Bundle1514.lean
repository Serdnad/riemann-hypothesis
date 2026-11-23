module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle267
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.schwartz_bruhat_sum_split_tensor : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → Af F) → ℂ), g ∈ SB (κ ⊕ κ' → Af F) → ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧ (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  first | exact @GlobalTheory.SBBlocks.sum_prod_blocks | exact GlobalTheory.SBBlocks.sum_prod_blocks | (intros; apply GlobalTheory.SBBlocks.sum_prod_blocks <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.idempotent_block_unipotent_identity : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (β : Type) [Fintype β] [DecidableEq β]
    (J : Matrix β β A), IsUnit J.det → ∀ e : R, e * e = e → ∀ g k : UG c J,
    (1 - e) • ((g.1.1 : Matrix β β A) - 1) = 0 → (1 - e) • ((k.1.1 : Matrix β β A) - 1) = 0 →
    ∀ a b : Matrix β β A, e • a = a → e • b = b →
    a * (1 - (k.1.1 : Matrix β β A)) = e • (1 : Matrix β β A) → (1 - (k.1.1 : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) = e • (1 : Matrix β β A) →
    (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ gd kd : UG c (dbl J), (gd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (g.1.1 : Matrix β β A) 0 0 1 →
    (kd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (k.1.1 : Matrix β β A) 0 0 1 →
    ∃ (p₁ p₂ : UG c (dbl J)) (t₁ t₂ : GL β A), (1 - e) • ((p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (1 - e) • ((p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₁.val ∧
      (p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₂.val ∧ gd = kd * p₁ * kd⁻¹ * p₂ := by
  first | exact @GlobalTheory.SiegelDiagDecomp.diag_decomp | exact GlobalTheory.SiegelDiagDecomp.diag_decomp | (intros; apply GlobalTheory.SiegelDiagDecomp.diag_decomp <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.SignatureOneForms

theorem form_re_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v : Fin n → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).re = ∑ i, hA.eigenvalues i *
      Complex.normSq ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := RCLike.ofReal ∘ hA.eigenvalues with hd
  set c := star U *ᵥ v with hc
  have hspec : A = U * diagonal d * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hd]
  have h0 := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) hspec
  have h1 : star v ⬝ᵥ A *ᵥ v = star c ⬝ᵥ (diagonal d *ᵥ c) := by
    rw [h0, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [h1]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, hd, Function.comp_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem form_re_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0)
    (i₀ : Fin n) (hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀) (v : Fin n → ℂ) (hv : v ≠ 0)
    (hv0 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i₀ = 0) :
    (star v ⬝ᵥ A *ᵥ v).re < 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set c := star U *ᵥ v with hc
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hcne : c ≠ 0 := by
    intro h0
    apply hv
    have : U *ᵥ c = v := by
      rw [hc, mulVec_mulVec, hU, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec]
    rw [← this, h0, mulVec_zero]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hcne
  have hji : j ≠ i₀ := by
    rintro rfl
    exact hj hv0
  have hjneg : hA.eigenvalues j < 0 :=
    lt_of_le_of_ne (not_lt.mp fun h => hji (hpos j h)) (hne j)
  rw [form_re_eq_sum hA v]
  have key : ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = i₀
      · subst hi
        simp [hv0]
      · have : hA.eigenvalues i ≤ 0 := not_lt.mp fun h => hi (hpos i h)
        nlinarith [Complex.normSq_nonneg (c i)]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      exact mul_neg_of_neg_of_pos hjneg (Complex.normSq_pos.mpr hj)
  simpa using key

end GlobalTheory.SignatureOneForms

namespace GlobalTheory

theorem re_form_neg_of_orth_of_sigPosH_eq_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro n A hA hdet hsig x y hx hxy hy
  unfold sigPosH at hsig
  obtain ⟨⟨i₀, hi₀⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hsig
  have hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀ := fun i h => congrArg Subtype.val (huniq ⟨i, h⟩)
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hyx : star y ⬝ᵥ A *ᵥ x = 0 := by
    have h := congrArg star hxy
    rw [star_zero] at h
    rw [← h, star_dotProduct, star_mulVec, hA.eq, ← dotProduct_mulVec]
  by_contra hQ
  push_neg at hQ
  set a₀ := (star U *ᵥ x) i₀ with ha₀
  set b₀ := (star U *ᵥ y) i₀ with hb₀
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  by_cases ha : a₀ = 0
  · exact absurd (GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos x hx0 ha) (not_lt.mpr hx.le)
  set w := b₀ • x - a₀ • y with hw
  have hw0 : (star U *ᵥ w) i₀ = 0 := by
    simp only [hw, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← ha₀, ← hb₀]
    ring
  have hQw : star w ⬝ᵥ A *ᵥ w = (Complex.normSq b₀ : ℂ) * (star x ⬝ᵥ A *ᵥ x)
      + (Complex.normSq a₀ : ℂ) * (star y ⬝ᵥ A *ᵥ y) := by
    simp only [hw, star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, hxy, hyx, smul_eq_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  by_cases hw' : w = 0
  · have h1 : star x ⬝ᵥ A *ᵥ w = b₀ * (star x ⬝ᵥ A *ᵥ x) := by
      simp [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxy]
    rw [hw', mulVec_zero, dotProduct_zero] at h1
    have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hx; simp at hx
    have hb : b₀ = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hQx
    have : a₀ • y = 0 := by
      have hw2 : b₀ • x - a₀ • y = 0 := hw ▸ hw'
      rw [hb, zero_smul, zero_sub, neg_eq_zero] at hw2
      exact hw2
    exact hy ((smul_eq_zero.mp this).resolve_left ha)
  · have hneg := GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos w hw' hw0
    rw [hQw, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hneg
    nlinarith [Complex.normSq_nonneg a₀, Complex.normSq_nonneg b₀,
      mul_nonneg (Complex.normSq_nonneg b₀) hx.le, mul_nonneg (Complex.normSq_nonneg a₀) hQ]

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HermCongruence

def signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : Fin n → ℂ :=
  fun i => if 0 < hA.eigenvalues i then 1 else -1

theorem eigenvalues_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (i : Fin n) : hA.eigenvalues i ≠ 0 := by
  intro h
  apply hd
  rw [hA.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

theorem exists_congr_signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    ∃ V : GL (Fin n) ℂ, (V : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * V = diagonal (signVec hA) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := hA.eigenvectorUnitary.2.1
    simpa [hU, Matrix.star_eq_conjTranspose] using this
  have hspec : A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hA.spectral_theorem
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  set c : Fin n → ℂ := fun i => ((Real.sqrt |hA.eigenvalues i|)⁻¹ : ℝ) with hc
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    have h1 : 0 < |hA.eigenvalues i| := abs_pos.2 (eigenvalues_ne_zero hA hd i)
    simp [hc, Real.sqrt_eq_zero', not_le.2 h1, eigenvalues_ne_zero hA hd i]
  set V := U * diagonal c with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV, det_mul, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hc0 i)
    intro h
    have := congrArg det hUU
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨GeneralLinearGroup.mkOfDetNeZero V hVdet, ?_⟩
  show Vᴴ * A * V = _
  have hcs : (diagonal c)ᴴ = diagonal c := by
    rw [diagonal_conjTranspose]
    congr 1; funext i; simp [hc]
  rw [hV, conjTranspose_mul, hcs]
  conv_lhs => rw [hspec]
  have : diagonal c * Uᴴ * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal c) =
      diagonal c * (Uᴴ * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal c := by
    simp only [Matrix.mul_assoc]
  rw [this, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  have hne := eigenvalues_ne_zero hA hd i
  have hpos : 0 < |hA.eigenvalues i| := abs_pos.2 hne
  have hsq : Real.sqrt |hA.eigenvalues i| * Real.sqrt |hA.eigenvalues i| = |hA.eigenvalues i| :=
    Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt |hA.eigenvalues i| ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : (Real.sqrt |hA.eigenvalues i|)⁻¹ * hA.eigenvalues i * (Real.sqrt |hA.eigenvalues i|)⁻¹ =
      if 0 < hA.eigenvalues i then 1 else -1 := by
    rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
    split_ifs with h
    · rw [abs_of_pos h]; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hne)]; field_simp
  simp only [signVec, hc]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key]
  split_ifs <;> simp

end GlobalTheory.HermCongruence

namespace GlobalTheory.HermCongruence

theorem exists_equiv_pos {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : sigPosH hA = sigPosH hB) :
    ∃ e : Fin n ≃ Fin n, ∀ i, (0 < hA.eigenvalues (e i) ↔ 0 < hB.eigenvalues i) := by
  have h1 : Fintype.card {i // 0 < hB.eigenvalues i} = Fintype.card {i // 0 < hA.eigenvalues i} := h.symm
  have h2 : Fintype.card {i // ¬ 0 < hB.eigenvalues i} = Fintype.card {i // ¬ 0 < hA.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun i => ?_⟩
  by_cases hi : 0 < hB.eigenvalues i
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h1) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_true ((Fintype.equivOfCardEq h1) ⟨i, hi⟩).2 hi
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h2) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_false ((Fintype.equivOfCardEq h2) ⟨i, hi⟩).2 hi

theorem perm_congr {n : ℕ} (d : Fin n → ℂ) (e : Fin n ≃ Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * diagonal d * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e =
      diagonal (d ∘ e) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  split_ifs with h <;> simp [h]

theorem congr_of_sigPosH_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian),
    A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB →
      ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  intro n A B hA hB hdA hdB hs
  obtain ⟨VA, hVA⟩ := exists_congr_signVec hA hdA
  obtain ⟨VB, hVB⟩ := exists_congr_signVec hB hdB
  obtain ⟨e, he⟩ := exists_equiv_pos hA hB hs
  set P : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e with hP
  have hPP : P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e.symm = 1 := by
    ext i j; simp [hP, Matrix.mul_apply, Matrix.one_apply]
  have hPdet : P.det ≠ 0 := by
    intro h
    have := congrArg det hPP
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  have hsig : signVec hA ∘ e = signVec hB := by
    funext i
    simp only [Function.comp_apply, signVec]
    by_cases hi : 0 < hB.eigenvalues i
    · rw [if_pos hi, if_pos ((he i).2 hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((he i).1 h))]
  refine ⟨VA * GeneralLinearGroup.mkOfDetNeZero P hPdet * VB⁻¹, ?_⟩
  set W : Matrix (Fin n) (Fin n) ℂ := ((VB⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hW
  have hVW : (VB : Matrix (Fin n) (Fin n) ℂ) * W = 1 := by
    rw [hW, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWV : Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, hVW, conjTranspose_one]
  have hP' : ((GeneralLinearGroup.mkOfDetNeZero P hPdet : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = P := rfl
  rw [Units.val_mul, Units.val_mul, hP', ← hW, conjTranspose_mul, conjTranspose_mul]
  have : Wᴴ * (Pᴴ * (VA : Matrix (Fin n) (Fin n) ℂ)ᴴ) * A * (VA * P * W) =
      Wᴴ * (Pᴴ * ((VA : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * VA) * P) * W := by
    simp only [Matrix.mul_assoc]
  rw [this, hVA, hP, perm_congr, hsig, ← hVB]
  have : Wᴴ * ((VB : Matrix (Fin n) (Fin n) ℂ)ᴴ * B * VB) * W =
      (Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ) * B * ((VB : Matrix (Fin n) (Fin n) ℂ) * W) := by
    simp only [Matrix.mul_assoc]
  rw [this, hWV, hVW, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.HermCongruence
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_ne (G : HTGroup p) : ∃ x ∈ G.Kq, IsCMField.complexConj G.F x ≠ x := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  obtain ⟨x, hx, him⟩ := G.hKq.2 v.embedding
  refine ⟨x, hx, fun h => him ?_⟩
  have h2 := IsCMField.complexEmbedding_complexConj G.F v.embedding x
  rw [h] at h2
  have := congrArg Complex.im h2
  simp only [Complex.conj_im] at this
  linarith

end GlobalTheory.CentAtP
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem herm_negDef_of_sigPosH_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    A.det ≠ 0 → sigPosH hA = 0 → ∀ y : Fin n → ℂ, y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro hdet hsig y hy
  have hneg : ∀ i, hA.eigenvalues i < 0 := by
    intro i
    have hnp : ¬ 0 < hA.eigenvalues i := by
      intro h
      have : IsEmpty {i : Fin n // 0 < hA.eigenvalues i} := Fintype.card_eq_zero_iff.mp hsig
      exact this.false ⟨i, h⟩
    have hne : hA.eigenvalues i ≠ 0 := by
      intro h0
      apply hdet
      rw [hA.det_eq_prod_eigenvalues]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
    exact lt_of_le_of_ne (not_lt.mp hnp) hne
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set z : Fin n → ℂ := star U *ᵥ y with hz
  have hyz : y = U *ᵥ z := by rw [hz, mulVec_mulVec, hUU', one_mulVec]
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [hyz, h, mulVec_zero]
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have key : star y ⬝ᵥ A *ᵥ y = star z ⬝ᵥ diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ z := by
    conv_lhs => rw [hspec]
    rw [hz, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, dotProduct_mulVec, vecMul_vecMul]
  rw [key]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Complex.re_sum]
  have hterm : ∀ i, (star z i * ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * z i)).re =
      hA.eigenvalues i * Complex.normSq (z i) := by
    intro i
    rw [show (RCLike.ofReal (hA.eigenvalues i) : ℂ) = (hA.eigenvalues i : ℂ) from rfl,Pi.star_apply, mul_left_comm, Complex.re_ofReal_mul]
    congr 1
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin n)))]
  refine Finset.sum_lt_sum (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hneg i).le (Complex.normSq_nonneg _))
    ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos (hneg j) (Complex.normSq_pos.mpr hj)⟩

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.CentTorus.AdelicSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

end Tmap

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.AdelicSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (exact GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (intros; apply GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective  <;> assumption)
end
