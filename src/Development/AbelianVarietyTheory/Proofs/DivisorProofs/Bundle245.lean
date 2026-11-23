module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

namespace GlobalTheory

theorem scalar_of_triangular_moves_open :
  ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  intro E _ _ _ r X m W hW hne _ hact
  classical
  cases r with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ n =>
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : σ ∈ X.Ψ
    · exact ⟨σ, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ, ?_⟩
      by_contra h'
      exact h ((X.cmType σ).2 h')
  obtain ⟨τ0, hτ0⟩ := hτ
  let τ : X.Ψ := ⟨τ0, hτ0⟩
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := (m : Matrix (Fin (n+1)) (Fin (n+1)) E).map τ0
  have key : ∀ y ∈ W, ∀ i j : Fin (n+1),
      (M *ᵥ (fun k => y τ k 0)) i * y τ j 0 = (M *ᵥ (fun k => y τ k 0)) j * y τ i 0 := by
    intro y hy i j
    obtain ⟨b, hb, he⟩ := hact y hy
    have hcol : ∀ a : Fin (n+1), (M *ᵥ (fun k => y τ k 0)) a = y τ a 0 * b τ 0 0 := by
      intro a
      have := congrFun (congrFun (congrFun he τ) a) 0
      simp only [lact, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at this
      have hs : ∑ k, y τ a k * b τ k 0 = y τ a 0 * b τ 0 0 := by
        rw [Finset.sum_eq_single (0 : Fin (n+1))]
        · intro k _ hk
          rw [(hb τ).2 k 0 (Fin.pos_of_ne_zero hk), mul_zero]
        · simp
      rw [hs] at this
      simp only [Matrix.mulVec, dotProduct]
      exact this
    rw [hcol i, hcol j]; ring
  obtain ⟨x0, hx0⟩ := hne
  have hq : ∀ w : Fin (n+1) → ℂ, ∀ i j : Fin (n+1), (M *ᵥ w) i * w j = (M *ᵥ w) j * w i := by
    intro w i j
    let pert : ℂ → Frame X.Ψ (n+1) := fun t σ a c => x0 σ a c + if σ = τ ∧ c = 0 then t * w a else 0
    have hc : Continuous pert := by
      apply continuous_pi; intro σ; apply continuous_pi; intro a; apply continuous_pi; intro c
      by_cases h : σ = τ ∧ c = 0
      · simp only [pert, h, and_self, if_true]; fun_prop
      · simp only [pert, h, if_false]; fun_prop
    have h0 : pert 0 = x0 := by funext σ a c; simp [pert]
    have hO : IsOpen (pert ⁻¹' W) := hW.preimage hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 (by simp [h0, hx0])
    set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht_def
    have htn : t ≠ 0 := by
      rw [ht_def]; exact_mod_cast (by positivity : ε / 2 ≠ 0)
    have hnorm : ‖t‖ < ε := by
      rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have h1 : pert t ∈ W := hball (by simpa using hnorm)
    have h2 : pert (-t) ∈ W := hball (by simpa using hnorm)
    have hcolp : ∀ s : ℂ, (fun k => pert s τ k 0) = (fun k => x0 τ k 0) + s • w := by
      intro s; funext k; simp [pert]
    have e1 := key _ h1 i j
    have e2 := key _ h2 i j
    have e0 := key _ hx0 i j
    have hpt : ∀ s : ℂ, ∀ k, pert s τ k 0 = x0 τ k 0 + s * w k := by
      intro s k; simp [pert]
    rw [hcolp] at e1 e2
    simp only [hpt, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have : t ^ 2 * ((M *ᵥ w) i * w j - (M *ᵥ w) j * w i) = 0 := by
      linear_combination (1/2 : ℂ) * e1 + (1/2 : ℂ) * e2 - e0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) htn
    · exact sub_eq_zero.mp h
  have hoff : ∀ i j : Fin (n+1), i ≠ j → M i j = 0 := by
    intro i j hij
    have := hq (Pi.single j 1) i j
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hij] using this
  have hsv : ∀ j k : Fin (n+1), (M *ᵥ Pi.single j (1:ℂ)) k = M k j := by
    intro j k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdiag : ∀ i j : Fin (n+1), M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have := hq (Pi.single i 1 + Pi.single j 1) i j
    have hji : j ≠ i := Ne.symm hij
    rw [Matrix.mulVec_add] at this
    simp only [Pi.add_apply, hsv, Pi.single_apply, hij, hji, if_true, if_false, mul_one, add_zero, zero_add, hoff i j hij, hoff j i hji] at this
    exact this
  refine ⟨(m : Matrix (Fin (n+1)) (Fin (n+1)) E) 0 0, ?_⟩
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    apply τ0.injective
    have := hdiag i 0
    simpa [M] using this
  · apply τ0.injective
    have := hoff i j hij
    simpa [M] using this

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

open scoped ComplexOrder ComplexConjugate Matrix

namespace GlobalTheory.FlagDomain

theorem gram_eq_transpose_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_transpose_mul, gram_eq_transpose_mul, Matrix.transpose_mul,
    Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem dmin_sign_of_definite (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (h : X.p0 = 0 ∨ X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (i : Fin (r + 1)) :
    0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  obtain ⟨ε, hε, hsgn⟩ : ∃ ε : ℝ, ε ^ 2 = 1 ∧ ∀ a : ℕ, a < r → sgn X.p0 a = ε := by
    rcases h with h | h
    · exact ⟨-1, by norm_num, fun a _ => by simp [sgn, h]⟩
    · exact ⟨1, by norm_num, fun a ha => by simp [sgn, h, ha]⟩
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hps : psgn X.p0 i = ε ^ (i : ℕ) := by
    unfold psgn
    rw [Finset.prod_congr rfl (g := fun _ => ε), Finset.prod_const, Finset.card_range]
    intro a ha
    exact hsgn a (lt_of_lt_of_le (Finset.mem_range.1 ha) hi)
  obtain ⟨P, hPdet, hP⟩ := X.signature τ
  set M := mat x τ with hM
  set Q := P⁻¹ * M with hQ
  have hPQ : P * Q = M := Matrix.mul_nonsing_inv_cancel_left P M (isUnit_iff_ne_zero.2 hPdet)
  have hQdet : Q.det ≠ 0 := by
    intro h0
    apply hx
    rw [← hPQ, Matrix.det_mul, h0, mul_zero]
  set N := Q.map (starRingEnd ℂ) with hN
  have hNdet : N.det ≠ 0 := by
    rw [hN, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hQdet
  have hNinj : Function.Injective N.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det N).2 (isUnit_iff_ne_zero.2 hNdet))
  have hH : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hNinj
  have hNt : Nᴴ = Qᵀ := by
    ext a b
    simp [hN, Matrix.conjTranspose_apply]
  have hdiag : Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) = (ε : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    rw [hsgn a a.isLt]
  have hgram : gram τ.1 X.Gm M = (ε : ℂ) • (Nᴴ * N) := by
    rw [← hPQ, GlobalTheory.FlagDomain.gram_mul, hP, hdiag, hNt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  set e := Fin.castLE hi with he
  have hsub : ((Nᴴ * N).submatrix e e).PosDef := hH.submatrix (Fin.castLE_injective hi)
  have hdpos := Complex.pos_iff.1 hsub.det_pos
  have hd : dmin X.Gm x τ i = ((ε ^ (i : ℕ) : ℝ) : ℂ) * ((Nᴴ * N).submatrix e e).det := by
    simp only [dmin, lminor]
    have hs : ((ε : ℂ) • (Nᴴ * N)).submatrix e e = (ε : ℂ) • ((Nᴴ * N).submatrix e e) := by
      ext a b
      simp
    rw [← hM, hgram, ← he, hs, Matrix.det_smul, Fintype.card_fin]
    push_cast
    rfl
  rw [hd, Complex.re_ofReal_mul, hps, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, hε, one_pow,
    one_mul]
  exact hdpos.1

theorem definite_frame_leading_minors_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ (x : Frame X.Ψ r) (τ : X.Ψ), (mat x τ).det ≠ 0 →
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re :=
  fun E _ _ _ r X h x τ hx i => dmin_sign_of_definite E r X h x τ hx i

end GlobalTheory.FlagDomain
end
