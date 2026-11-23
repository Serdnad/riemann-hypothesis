module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem inst_mem_frameSet {I : Formalism.MainNotions.S.AutInst} {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (j : Fin r ⊕ Fin r ⊕ Unit) : instFvec e f z j ∈ frameSet I e f z := by
  rcases j with a | a | u <;> simp [instFvec, frameSet]

theorem inst_col {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (j : Fin r ⊕ Fin r ⊕ Unit) :
    instBmat I v e f z *ᵥ Pi.single j 1 = rv I v (instFvec e f z j) := by
  ext i
  rw [Matrix.mulVec_single_one]
  simp [instBmat]

theorem inst_fix_of {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (m : Matrix (Fin I.n) (Fin I.n) ℂ) (hm : m * instBmat I v e f z = instBmat I v e f z) :
    ∀ x ∈ frameSet I e f z, m *ᵥ rv I v x = rv I v x := by
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, instFvec e f z j = x := by
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr (Sum.inl a), rfl⟩
    · exact ⟨Sum.inr (Sum.inr ()), (Set.mem_singleton_iff.1 hx).symm⟩
  rw [← inst_col v e f z j, Matrix.mulVec_mulVec, hm]

theorem inst_fixB_of {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (m : Matrix (Fin I.n) (Fin I.n) ℂ)
    (hm : ∀ x ∈ frameSet I e f z, m *ᵥ rv I v x = rv I v x) : m * instBmat I v e f z = instBmat I v e f z := by
  have hcol : ∀ j, (m * instBmat I v e f z) *ᵥ Pi.single j 1 = instBmat I v e f z *ᵥ Pi.single j 1 := by
    intro j
    rw [← Matrix.mulVec_mulVec, inst_col v e f z j, hm _ (inst_mem_frameSet e f z j)]
  ext i j
  have h := congrFun (hcol j) i
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h

theorem instDecomp_of (hP : InstPlaceDecomp) (hG : InstFrameGram) : InstDecomp := by
  intro I r e f z hF h hh
  have key := fun v : InfinitePlace I.F =>
    hP I.n (I.ε v) (Fin r ⊕ Fin r ⊕ Unit) (instBmat I v e f z) (hG I r e f z hF v)
      (Formalism.MainNotions.S.uMat (h v)) (h v).2 (inst_fixB_of v e f z _ (hh v))
  choose k p σ hk hp hσ hkB hpB hσB hkp hσσ hσp C hCc hC1 hCk using key
  have Jsq : ∀ v, Formalism.REAL.Jm (I.ε v) * Formalism.REAL.Jm (I.ε v) = 1 := by
    intro v
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hε : I.ε v a <;> simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, hε]
    · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.one_apply, hab]
  have hU : ∀ v (m : Matrix (Fin I.n) (Fin I.n) ℂ), Formalism.REAL.inUJ (I.ε v) m →
      ∃ u : Formalism.REAL.UJ (I.ε v), (((u : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) = m := by
    intro v m hm
    have hl : (Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v)) * m = 1 := by
      have : Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v) * m =
          Formalism.REAL.Jm (I.ε v) * (mᴴ * Formalism.REAL.Jm (I.ε v) * m) := by
        simp only [Matrix.mul_assoc]
      rw [this, show mᴴ * Formalism.REAL.Jm (I.ε v) * m = Formalism.REAL.Jm (I.ε v) from hm, Jsq v]
    have hr : m * (Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v)) = 1 := by
      first
      | exact mul_eq_one_comm.1 hl
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hl
    exact ⟨⟨⟨m, _, hr, hl⟩, hm⟩, rfl⟩
  choose ku hku using fun v => hU v (k v) (hk v)
  choose pu hpu using fun v => hU v (p v) (hp v)
  choose su hsu using fun v => hU v (σ v) (hσ v)
  let K : I.Ginf := fun v => ku v
  let P : I.Ginf := fun v => pu v
  let S : I.Ginf := fun v => su v
  have memH : ∀ (X : I.Ginf) (m : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ),
      (∀ v, (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) = m v) →
      (∀ v, m v * instBmat I v e f z = instBmat I v e f z) → X ∈ Hset I (frameSet I e f z) := by
    intro X m hX hmB v x hx
    show (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) *ᵥ _ = _
    rw [hX v]
    exact inst_fix_of v e f z (m v) (hmB v) x hx
  have ext' : ∀ X Y : I.Ginf, (∀ v, (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (((Y v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ)) → X = Y := by
    intro X Y hXY
    funext v
    exact Subtype.ext (Units.ext (hXY v))
  have hSS : S * S = 1 := ext' _ _ fun v => by
    simp only [Pi.mul_apply, Pi.one_apply, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, S, hsu]
    exact hσσ v
  have hSPSP : S * P * S * P = 1 := ext' _ _ fun v => by
    simp only [Pi.mul_apply, Pi.one_apply, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, S, P, hsu, hpu]
    exact hσp v
  refine ⟨K, memH K k hku hkB, P, memH P p hpu hpB, S, memH S σ hsu hσB, ?_, ?_, ?_⟩
  · refine ext' _ _ fun v => ?_
    simp only [Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, K, P, hku, hpu]
    exact hkp v
  · have hSi : S⁻¹ = S := inv_eq_of_mul_eq_one_right hSS
    rw [hSi]
    exact eq_inv_of_mul_eq_one_left hSPSP
  · refine ⟨Set.pi Set.univ C, isCompact_univ_pi hCc, ?_, ?_⟩
    · rw [interior_pi_set Set.finite_univ]
      intro v _
      exact hC1 v
    · intro x
      simp only [Set.mem_univ_pi]
      refine forall_congr' fun v => hCk v _ _ ?_
      have hg : (K * x * K⁻¹) v * ku v = ku v * x v := by
        simp [K]
      have := congrArg (fun g : Formalism.REAL.UJ (I.ε v) =>
        (((g : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ)) hg
      simp only [Subgroup.coe_mul, Units.val_mul, hku] at this
      exact this

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem inst_exp_real_entry (l : ℝ) (y : ℂ) :
    NormedSpace.exp (l : ℂ) * y = y ↔ (l : ℂ) * y = 0 := by
  have hE : NormedSpace.exp (l : ℂ) = ((Real.exp l : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    first
      | rw [Complex.exp_eq_exp_ℂ]
  rw [hE]
  constructor
  · intro h
    by_cases hy : y = 0
    · simp [hy]
    · have h1 : ((Real.exp l : ℝ) : ℂ) = 1 := mul_right_cancel₀ hy (h.trans (one_mul y).symm)
      have h2 : Real.exp l = 1 := by exact_mod_cast h1
      have h3 : l = 0 := Real.exp_eq_one_iff l |>.mp h2
      simp [h3]
  · intro h
    rcases mul_eq_zero.mp h with hl | hy
    · have h3 : l = 0 := by exact_mod_cast hl
      simp [h3]
    · simp [hy]

private theorem exists_unitary_diagonal_of_isHermitian {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), star U * U = 1 ∧ U * star U = 1 ∧
      X = U * diagonal (fun i => (d i : ℂ)) * star U := by
  have h1 : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.1
  have h2 : (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    first
      | exact hX.eigenvectorUnitary.2.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_⟩
  first
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def]
    | (conv_lhs => rw [hX.spectral_theorem]); simp [Function.comp_def, Unitary.conjStarAlgAut_apply]
    | (have h3 := hX.star_mul_self_mul_eq_diagonal
       calc X = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
              (star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * X *
                (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) *
              star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
             simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
             rw [Matrix.mul_assoc, h2, Matrix.mul_one]
         _ = _ := by rw [h3]; simp [Function.comp_def])

theorem exponent_fixed_instance : InstExpFix := by
  intro n X hX w
  obtain ⟨U, d, hUU, hUU', hX'⟩ := exists_unitary_diagonal_of_isHermitian X hX
  have hexp : NormedSpace.exp X = U * diagonal (fun i => NormedSpace.exp (d i : ℂ)) * star U := by
    have hunit : IsUnit U := ⟨⟨U, star U, hUU', hUU⟩, rfl⟩
    have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hUU
    rw [hX', ← hinv]
    have hd : NormedSpace.exp (diagonal (fun i => (d i : ℂ))) =
        diagonal (fun i => NormedSpace.exp (d i : ℂ)) := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext i
      first
        | exact Pi.exp_apply _ _
        | simp [Pi.exp_def]
    first
      | rw [Matrix.exp_conj _ _ hunit, hd]
  have inj : ∀ a b : Fin n → ℂ, U *ᵥ a = U *ᵥ b → a = b := by
    intro a b h
    have h2 := congrArg (fun v => star U *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec] using h2
  obtain ⟨y, hy⟩ : ∃ y, y = star U *ᵥ w := ⟨_, rfl⟩
  have hw : w = U *ᵥ y := by rw [hy, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec]
  have hXw : X *ᵥ w = U *ᵥ (fun i => (d i : ℂ) * y i) := by
    rw [hX', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  have hEw : NormedSpace.exp X *ᵥ w = U *ᵥ (fun i => NormedSpace.exp (d i : ℂ) * y i) := by
    rw [hexp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hy]
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
  constructor
  · intro h
    have h1 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      apply inj
      rw [← hEw, h]
      exact hw
    rw [hXw]
    have h0 : (fun i => (d i : ℂ) * y i) = 0 := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mp (congrFun h1 i)
    rw [h0, Matrix.mulVec_zero]
  · intro h
    rw [hXw] at h
    have h2 : (fun i => (d i : ℂ) * y i) = 0 := inj _ 0 (by rw [h, Matrix.mulVec_zero])
    rw [hEw]
    have h3 : (fun i => NormedSpace.exp (d i : ℂ) * y i) = y := by
      funext i
      exact (inst_exp_real_entry (d i) (y i)).mpr (congrFun h2 i)
    rw [h3, ← hw]

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

section

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem gram_entry (I : Formalism.MainNotions.S.AutInst) (v : NumberField.InfinitePlace I.F) {r : ℕ}
    (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (j k : Fin r ⊕ Fin r ⊕ Unit) :
    ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z) j k =
      hJ (I.ε v) (rv I v (instFvec e f z j)) (rv I v (instFvec e f z k)) := by
  unfold instBmat hJ
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum]

theorem frame_gram_instance : InstFrameGram := by
  intro I r e f z hF v
  obtain ⟨hee, hff, hef, hz, hzz⟩ := rv_frame (I := I) hF v
  have hJH : (Formalism.REAL.Jm (I.ε v))ᴴ = Formalism.REAL.Jm (I.ε v) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : I.ε v a <;> simp [h]
  have hH : ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z)ᴴ =
      (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.mul_assoc]
  have hent := gram_entry I v e f z
  generalize (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z = G at hH hent ⊢
  have hS : ∀ j k, G j k = star (G k j) := by
    intro j k
    have hjk := congrFun (congrFun hH j) k
    rw [Matrix.conjTranspose_apply] at hjk
    exact hjk.symm
  have h1 : ∀ a b, G (Sum.inl a) (Sum.inl b) = 0 := fun a b => by rw [hent]; exact hee a b
  have h3 : ∀ a b, G (Sum.inl a) (Sum.inr (Sum.inl b)) = if a = b then 1 else 0 :=
    fun a b => by rw [hent]; exact hef a b
  have h4 : ∀ a (u : Unit), G (Sum.inl a) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).1
  have h5 : ∀ a (u : Unit), G (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).2
  have h3' : ∀ a b, G (Sum.inr (Sum.inl a)) (Sum.inl b) = if b = a then 1 else 0 := by
    intro a b
    rw [hS, h3]
    split_ifs <;> simp
  have h4' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inl a) = 0 := by
    intro a u
    rw [hS, h4, star_zero]
  have h5' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inl a)) = 0 := by
    intro a u
    rw [hS, h5, star_zero]
  have h6 : ∀ u u' : Unit, G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr u')) ≠ 0 := by
    intro u u'
    rw [hent]
    exact hzz
  have hker : ∀ w, G *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hf : ∀ a, w (Sum.inr (Sum.inl a)) = 0 := by
      intro a
      have := congrFun hw (Sum.inl a)
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h1, h3, h4] using this
    have he : ∀ a, w (Sum.inl a) = 0 := by
      intro a
      have := congrFun hw (Sum.inr (Sum.inl a))
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h3', h5, hf] using this
    have hzw : ∀ u : Unit, w (Sum.inr (Sum.inr u)) = 0 := by
      intro u
      have := congrFun hw (Sum.inr (Sum.inr u))
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h4', h5', zero_mul,
        Finset.sum_const_zero, zero_add, Pi.zero_apply] at this
      rw [Fintype.sum_unique] at this
      rcases (mul_eq_zero.mp this) with h | h
      · exact absurd h (h6 _ _)
      · cases u
        exact h
    funext j
    rcases j with a | a | u
    · exact he a
    · exact hf a
    · exact hzw u
  refine Matrix.mulVec_injective_iff_isUnit.mp ?_
  intro w₁ w₂ h
  have h0 : G *ᵥ (w₁ - w₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (hker _ h0)

end PI.ScMuExists.UnitaryGroupMassFormula
end
end
