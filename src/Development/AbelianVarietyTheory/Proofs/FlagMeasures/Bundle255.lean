module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle052
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.GroupTheory.Commensurable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

namespace GlobalTheory.SignCount

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

private theorem qEps_eq_star_dotProduct_Jm_mulVec {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    ((GlobalTheory.GaussMean.qEps ε x : ℝ) : ℂ) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  simp only [GlobalTheory.GaussMean.qEps, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]
  split_ifs <;> push_cast <;> ring

private theorem qEps_mulVec_of_conjTranspose_mul_Jm_mul {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x := by
  apply Complex.ofReal_injective
  rw [qEps_eq_star_dotProduct_Jm_mulVec, qEps_eq_star_dotProduct_Jm_mulVec, ← h, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

private theorem qEps_not_eq_neg {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps (fun a => !ε a) x = - GlobalTheory.GaussMean.qEps ε x := by
  simp only [GlobalTheory.GaussMean.qEps, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a = true <;> simp [h]

private theorem card_true_add_card_false_le_of_qEps_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : ∀ x, GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x) :
    Fintype.card {a // η a = true} + Fintype.card {a // ε a = false} ≤ m := by
  classical
  let E₁ : ({a // η a = true} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun u a => if h : η a = true then u ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : η a = true <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : η a = true <;> simp [h] }
  let E₂ : ({a // ε a = false} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun w a => if h : ε a = false then w ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : ε a = false <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : ε a = false <;> simp [h] }
  let Φ := (C.mulVecLin ∘ₗ E₁).coprod E₂
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, w⟩ hp
    have hp' : C *ᵥ E₁ u = -(E₂ w) := by
      have : C *ᵥ E₁ u + E₂ w = 0 := by simpa [Φ] using hp
      exact eq_neg_of_add_eq_zero_left this
    have hnn : ∀ a, 0 ≤ (if η a then (1 : ℝ) else -1) * ‖E₁ u a‖ ^ 2 := by
      intro a
      by_cases h : η a = true
      · simp [h]
      · simp [E₁, h]
    have hnp : GlobalTheory.GaussMean.qEps ε (-(E₂ w)) ≤ 0 := by
      unfold GlobalTheory.GaussMean.qEps
      refine Finset.sum_nonpos fun a _ => ?_
      by_cases h : ε a = false
      · simp [h]
      · simp [E₂, h]
    have hq : GlobalTheory.GaussMean.qEps η (E₁ u) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg fun a _ => hnn a)
      rw [← hC, hp']
      exact hnp
    have hu : u = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hq
      funext b
      have := hz b.1 (Finset.mem_univ _)
      simpa [E₁, b.2] using this
    have hw : w = 0 := by
      have h0 : E₂ w = 0 := by
        have : C *ᵥ E₁ u = 0 := by simp [hu]
        rw [hp'] at this
        exact neg_eq_zero.1 this
      funext b
      have := congrFun h0 b.1
      simpa [E₂, b.2] using this
    simp [hu, hw]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using this

theorem card_true_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) :
    Nat.card {a // ε a = true} = Nat.card {a // η a = true} := by
  classical
  have hC := qEps_mulVec_of_conjTranspose_mul_Jm_mul C h
  have h₁ := card_true_add_card_false_le_of_qEps_eq C hC
  have hC' : ∀ x, GlobalTheory.GaussMean.qEps (fun a => !ε a) (C *ᵥ x) =
      GlobalTheory.GaussMean.qEps (fun a => !η a) x := by
    intro x; rw [qEps_not_eq_neg, qEps_not_eq_neg, hC]
  have h₂ := card_true_add_card_false_le_of_qEps_eq C hC'
  simp only [Fintype.card_subtype] at h₁ h₂
  simp only [Bool.not_eq_true', Bool.not_eq_false'] at h₂
  have hε : (Finset.univ.filter fun a => ε a = true).card +
      (Finset.univ.filter fun a => ε a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases ε a <;> simp
    simp [this]
  have hη : (Finset.univ.filter fun a => η a = true).card +
      (Finset.univ.filter fun a => η a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if η a = true then 1 else 0) + (if η a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases η a <;> simp
    simp [this]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  omega

theorem card_true_cons {n : ℕ} (s : Bool) (ε' : Fin n → Bool) :
    Nat.card {a // (Fin.cons s ε' : Fin (n + 1) → Bool) a = true} =
      (if s = true then 1 else 0) + Nat.card {a // ε' a = true} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

private theorem conjTranspose_mul_Jm_mul_apply {m : ℕ} {ι : Type*} (ε : Fin m → Bool) (M : Matrix (Fin m) ι ℂ)
    (k l : ι) :
    (Mᴴ * Formalism.REAL.Jm ε * M) k l = ∑ i, star (M i k) * ((if ε i then 1 else -1) * M i l) := by
  rw [Matrix.mul_apply]
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, mul_assoc]

theorem gram_cons {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {s : Bool}
    {x₀ : Fin (n + 1) → ℂ} {B : Matrix (Fin (n + 1)) (Fin n) ℂ}
    (h0 : GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s)
    (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ))ᴴ * Formalism.REAL.Jm ε *
      (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ)) =
      Formalism.REAL.Jm (Fin.cons s ε') := by
  have e0 := qEps_eq_star_dotProduct_Jm_mulVec ε x₀
  rw [h0] at e0
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply] at e0
  have e1 : ∀ l, ∑ i, star (x₀ i) * ((if ε i then 1 else -1) * B i l) = 0 := by
    intro l
    have := congrFun h1 l
    simpa [Matrix.vecMul, dotProduct, Formalism.REAL.Jm, Matrix.diagonal_mul] using this
  ext k l
  rw [conjTranspose_mul_Jm_mul_apply]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
  · rw [← e0]
    cases s <;> simp [Formalism.REAL.Jm, GlobalTheory.GaussMean.sgn]
  · rw [e1]
    simp [Formalism.REAL.Jm, (Fin.succ_ne_zero l).symm]
  · have := congrArg star (e1 k)
    rw [star_sum, star_zero] at this
    rw [show (Formalism.REAL.Jm (Fin.cons s ε') : Matrix _ _ ℂ) k.succ 0 = 0 by
      simp [Formalism.REAL.Jm, Fin.succ_ne_zero k]]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp [mul_comm]
  · rw [← conjTranspose_mul_Jm_mul_apply ε B k l, h2]
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply]

theorem exists_signCompat : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  intro n ε ε' s x₀ B h0 h1 h2 P Q P' Q' f f' hf hf'
  have hc := card_true_eq _ (gram_cons h0 h1 h2)
  rw [card_true_cons, hf.card_true, hf'.card_true] at hc
  have hPQ := Sorts.add_eq f
  have hPQ' := Sorts.add_eq f'
  cases s
  · simp at hc
    let eL : Fin P' ≃ Fin P := finCongr (by omega)
    let eR : Option (Fin Q') ≃ Fin Q := (finSuccEquiv Q').symm.trans (finCongr (by omega))
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Fin P' ⊕ Option (Fin Q') :=
      { toFun := fun o => o.elim (Sum.inr none) (Sum.elim Sum.inl (fun b => Sum.inr (some b)))
        invFun := Sum.elim (fun a => some (Sum.inl a)) (fun ob => ob.map Sum.inr)
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro (_ | _ | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]
  · simp at hc
    let eL : Option (Fin P') ≃ Fin P := (finSuccEquiv P').symm.trans (finCongr (by omega))
    let eR : Fin Q' ≃ Fin Q := finCongr (by omega)
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Option (Fin P') ⊕ Fin Q' :=
      { toFun := fun o => o.elim (Sum.inl none) (Sum.elim (fun a => Sum.inl (some a)) Sum.inr)
        invFun := Sum.elim (fun oa => oa.map Sum.inl) (fun b => some (Sum.inr b))
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro ((_ | _) | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]

end GlobalTheory.SignCount
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem map_phi_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P Q : MatKR k r} (hP : IsCayley k r ε P)
    (hQ : IsCayley k r ε Q) : (Formalism.REAL.muG ε).map (phi ε P) = (Formalism.REAL.muG ε).map (phi ε Q) := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hQu, hQJ⟩ := hQ

  set Pu := hPu.unit with hPu_def
  set Qu := hQu.unit with hQu_def
  have hQQ : Q * Q⁻¹ = 1 := by
    rw [← hQu.unit_spec, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmJ : (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = Formalism.REAL.Jm ε := by
    have h1 : (Q⁻¹)ᴴ * Qᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
    calc (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = (Q⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Q⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * Q⁻¹) := by
          rw [hPJ, ← hQJ]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h1, hQQ, Matrix.one_mul, Matrix.mul_one]
  have hmem : Pu * Qu⁻¹ ∈ Formalism.REAL.UJ ε := by
    have hv : ((Pu * Qu⁻¹ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = P * Q⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv, hPu_def, hQu_def, hPu.unit_spec, hQu.unit_spec]
    show Formalism.REAL.inUJ ε _
    rw [hv]
    exact hmJ
  set m : Formalism.REAL.UJ ε := ⟨Pu * Qu⁻¹, hmem⟩ with hm_def
  have hval : ∀ (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hA : IsUnit A)
      (u : Formalism.REAL.UJ ε), phi ε A u = ((hA.unit⁻¹ * (u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) * hA.unit :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
    intro A hA u
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hA.unit_spec]
    rfl
  have hconj : phi ε Q = phi ε P ∘ (fun u => m * u * m⁻¹) := by
    funext u
    rw [Function.comp_apply, hval Q hQu, hval P hPu]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm_def]
    rw [hPu_def, hQu_def]
    group <;> rfl
  have hcont : ∀ A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Continuous (phi ε A) := by
    intro A
    have : Continuous (fun u : Formalism.REAL.UJ ε =>
        ((u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  have hinv : (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹) = Formalism.REAL.muG ε := by
    have hL : Measurable (fun u : Formalism.REAL.UJ ε => m * u) := measurable_const_mul m
    have hR : Measurable (fun u : Formalism.REAL.UJ ε => u * m⁻¹) := measurable_mul_const m⁻¹
    calc (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹)
        = ((Formalism.REAL.muG ε).map (fun u => m * u)).map (fun u => u * m⁻¹) := by
          rw [Measure.map_map hR hL]; rfl
      _ = (Formalism.REAL.muG ε).map (fun u => u * m⁻¹) := by
          rw [MeasureTheory.map_mul_left_eq_self (Formalism.REAL.muG ε) m]
      _ = Formalism.REAL.muG ε := Formalism.REAL.indefinite_unitary_unimodular _ ε m⁻¹
  rw [hconj, ← Measure.map_map (hcont P).measurable (by
    exact (measurable_const_mul m).mul_const m⁻¹), hinv]

theorem deg_eq_mul_fdegH : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW

  by_cases hC : ∃ P0 : MatKR D.R.k D.R.rS, IsCayley D.R.k D.R.rS (epsSH D.R) P0
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact absurd ⟨P, hP⟩ hC
  obtain ⟨P0, hP0⟩ := hC
  have hP0det : IsUnit P0.det := (Matrix.isUnit_iff_isUnit_det P0).1 hP0.1
  obtain ⟨c, hc0, hctop, hμ⟩ :=
    GlobalTheory.BesselDegree.haar_eq_smul (ε := epsSH D.R) hP0det hP0.2 W.μG hW.2.2.2.2.2.2.1
  set cd : NNReal := D.s.cdScale _ (epsSH D.R) with hcd_def

  have hI : ∀ (P : MatKR D.R.k D.R.rS), IsCayley D.R.k D.R.rS (epsSH D.R) P →
      ∀ (F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ),
        ∫ x, F x ∂W.μG = c.toReal * ∫ u, F (phi (epsSH D.R) P u) ∂(Formalism.REAL.muG (epsSH D.R)) := by
    intro P hP F
    have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    let h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ ≃ₜ
        Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
      { toFun := fun x => P⁻¹ * x * P
        invFun := fun x => P * x * P⁻¹
        left_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
        right_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP', Matrix.mul_one]
        continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
        continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
    have hemb : Topology.IsClosedEmbedding (phi (epsSH D.R) P) :=
      h.isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ (epsSH D.R)).1
    rw [hμ, map_phi_eq hP0 hP, integral_smul_measure, smul_eq_mul,
      hemb.measurableEmbedding.integral_map]
  by_cases hcd : cd = 0
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA v hv
    obtain ⟨P, -, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
    have h2 := (hF.2 v v v v).2
    rw [← hcd_def] at h2
    rw [hcd, ENNReal.coe_zero, zero_smul, integral_zero_measure] at h2
    have hv' : (⟪v, v⟫_ℂ : ℂ) ≠ 0 := inner_self_ne_zero.2 hv
    have hd : (A.deg : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
    exact absurd h2.symm (div_ne_zero (mul_ne_zero hv' hv') hd)
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hcdpos : (0 : ℝ) < cd := by
    rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hcd
  refine ⟨c.toReal / cd, div_pos hcpos hcdpos, ?_⟩
  intro lam A hA v hv
  obtain ⟨P, hP, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, hF.1⟩
  have h2 := (hF.2 v v v v).2
  rw [← hcd_def] at h2

  set J := ∫ u, ‖⟪v, A.σ (P⁻¹ * ((u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ) :
      Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) * P) v⟫_ℂ‖ ^ 2
      ∂(Formalism.REAL.muG (epsSH D.R)) with hJ
  have hJc : ((cd : ℝ) * J : ℂ) = (‖v‖ ^ 4 / A.deg : ℝ) := by
    have hin : (⟪v, v⟫_ℂ : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hint : ∫ g, coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g * star (coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g)
        ∂(Formalism.REAL.muG (epsSH D.R)) = ((J : ℝ) : ℂ) := by
      rw [hJ, ← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [integral_smul_measure, hint, hin, ENNReal.coe_toReal, Complex.real_smul] at h2
    rw [h2]
    push_cast
    ring
  have hJr : (cd : ℝ) * J = ‖v‖ ^ 4 / A.deg := by exact_mod_cast hJc
  have hIv := hI P hP (fun x => ‖⟪v, A.σ (Matrix.of x) v⟫_ℂ‖ ^ 2)
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hdeg := hF.1
  unfold PI.BesselPeriodGGP.fdegH
  rw [hIv]
  change A.deg = c.toReal / cd * (‖v‖ ^ 4 / (c.toReal * J))
  have hJ' : J = ‖v‖ ^ 4 / A.deg / cd := by
    rw [← hJr]; field_simp
  rw [hJ']
  field_simp

end GlobalTheory.DegreeTie

end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocComm

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrel d τ hτ
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hrel
  obtain ⟨hUW, -, -, -, hAut, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, -, -, hStab, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨hTC, -, -⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have key : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.IsTerm (c.dat d) (c.lat τ.abelian₂) := fun d τ h => (hTC d τ h).1
  have eA : ∀ Λ, P.UW0 ⊓ LocNG.Aut Λ =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat Λ)).comap c.grp.toMonoidHom := by
    intro Λ
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rw [hUW, hAut]
  have eS : ∀ d : LocNG.Datum P, LocNG.Datum.Stab d =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom := by
    intro d
    ext g
    rw [Subgroup.mem_comap, hStab]
    rfl
  have rel : ∀ A B : Subgroup S.GLV,
      (A.comap c.grp.toMonoidHom).relIndex (B.comap c.grp.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective c.grp.surjective]
  have fixd : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂) ≤ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d) := by
    intro d τ h x hx
    obtain ⟨hx0, hxs⟩ := Subgroup.mem_inf.mp hx
    have ht := key d τ h
    have h1 := (GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms M.L r k S _ _ ht x hx0).1
    rw [MulAction.mem_stabilizer_iff.mp hxs] at h1
    have h2 := (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ ht).2.2.2.2.2.2.2 _ h1
    exact Subgroup.mem_inf.mpr ⟨hx0, MulAction.mem_stabilizer_iff.mpr h2⟩
  have volH := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement M.L r k S
  have cLam : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂)) := by
    intro d τ h
    have := volH.1 _ (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ (key d τ h)).1.1
    exact ⟨⟨this.1⟩, ⟨this.2.1⟩⟩
  have cDat : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
    intro d τ h
    obtain ⟨h1, h2⟩ := volH.2 _ _ (key d τ h)
    exact ⟨⟨h1⟩, ⟨h2⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [eA, eS]
    exact Subgroup.comap_mono (fixd d τ hτ)
  · rw [eA, eS, rel]
    exact ((cLam d τ hτ).symm.trans (cDat d τ hτ)).1.relIndex_ne_zero
  · intro d' τ' hτ'
    rw [eS, eS, rel]
    exact ((cDat d τ hτ).symm.trans (cDat d' τ' hτ')).1.relIndex_ne_zero

end GlobalTheory.HL.LocComm
end
