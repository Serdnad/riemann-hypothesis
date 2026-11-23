module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.Bundle017
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.AdelDefs
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.TruncatedCuspIrreducibility.ScatteringLimits
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.Bundle003
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem rankOne {F : Type} [Field F] (b d : Fin 2 → F) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : d 0 * b 0 + d 1 * b 1 = 0) :
    ∃ m : GL (Fin 2) F, Matrix.vecMulVec b d = (m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val := by
  have key : ∀ u0 u1 : F, u0 * b 0 + u1 * b 1 = 1 → ∃ m : GL (Fin 2) F,
      Matrix.vecMulVec b d = (m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val := by
    intro u0 u1 hu
    have hdet : (!![u0, u1; d 0, d 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      intro h0
      apply hd
      funext i
      fin_cases i
      · show d 0 = 0
        linear_combination (-d 0) * hu + u0 * h - b 1 * h0
      · show d 1 = 0
        linear_combination (-d 1) * hu + u1 * h + b 0 * h0
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
    rw [Matrix.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.single_apply]
    · linear_combination d 0 * hu
    · linear_combination d 1 * hu
    · linear_combination d 0 * h
    · linear_combination d 1 * h
  by_cases h0 : b 0 = 0
  · have h1 : b 1 ≠ 0 := fun h1 => hb (by funext i; fin_cases i <;> simpa)
    exact key 0 (b 1)⁻¹ (by simp [h1])
  · exact key (b 0)⁻¹ 0 (by simp [h0])

private theorem core {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) (r : ℕ) (p q : Fin (2 + 2) → F)
    (hp : ∀ i : Fin (2 + 2), r ≤ (i : ℕ) → (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec p i = 0)
    (hq : ∀ j : Fin (2 + 2), (j : ℕ) < r → Matrix.vecMul q γ.val j = 0)
    (h : ((fun i => q (Fin.castAdd 2 i)) = 0 ∧ (fun i => q (Fin.natAdd 2 i)) ≠ 0 ∧ (fun i => p (Fin.natAdd 2 i)) ≠ 0) ∨
      ((fun i => p (Fin.natAdd 2 i)) = 0 ∧ (fun i => p (Fin.castAdd 2 i)) ≠ 0 ∧ (fun i => q (Fin.castAdd 2 i)) ≠ 0)) :
    ∃ (X₀ : UPos (2 + 2) r → F) (m : GL (Fin 2) F) (C : Matrix (Fin 2) (Fin 2) F),
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 C 0 ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val)) ∨
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val) C 0 0) := by
  set l := (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec p with hl
  set v := Matrix.vecMul q γ.val with hv
  have hX : blockEntry (fun s : UPos (2 + 2) r => l s.1.1 * v s.1.2) = Matrix.vecMulVec l v := by
    ext i j
    rw [blockEntry_apply, Matrix.vecMulVec_apply]
    split_ifs with hij
    · rfl
    · by_cases hi : (i : ℕ) < r
      · rw [hq j (by omega), mul_zero]
      · rw [hp i (by omega), zero_mul]
  have hE : (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry (fun s : UPos (2 + 2) r => l s.1.1 * v s.1.2) *
      (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.vecMulVec p q := by
    rw [hX, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hl, hv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul,
      Units.mul_inv, Matrix.one_mulVec, Matrix.vecMul_one]
  have hdot : q ⬝ᵥ p = 0 := by
    have h1 : v ⬝ᵥ l = q ⬝ᵥ p := by
      rw [hl, hv, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) < r
    · rw [hq i hi, zero_mul]
    · rw [hp i (by omega), mul_zero]
  rw [dotProduct, Fin.sum_univ_add, Fin.sum_univ_two, Fin.sum_univ_two] at hdot
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have h1' : ∀ i, q (Fin.castAdd 2 i) = 0 := congrFun h1
    obtain ⟨m, hm⟩ := rankOne _ _ h3 h2 (by simpa only [h1', zero_mul, zero_add] using hdot)
    refine ⟨_, m, Matrix.vecMulVec (fun i => p (Fin.castAdd 2 i)) (fun i => q (Fin.natAdd 2 i)), Or.inl (hE.trans ?_)⟩
    rw [← hm]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.vecMulVec_apply, h1', mul_zero,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]
  · have h1' : ∀ i, p (Fin.natAdd 2 i) = 0 := congrFun h1
    obtain ⟨m, hm⟩ := rankOne _ _ h2 h3 (by simpa only [h1', mul_zero, add_zero] using hdot)
    refine ⟨_, m, Matrix.vecMulVec (fun i => p (Fin.castAdd 2 i)) (fun i => q (Fin.natAdd 2 i)), Or.inr (hE.trans ?_)⟩
    rw [← hm]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.vecMulVec_apply, h1', zero_mul,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]

private theorem perp {F : Type} [Field F] (a : Fin 2 → F) (ha : a ≠ 0) :
    ∃ c : Fin 2 → F, c ≠ 0 ∧ ∑ i, c i * a i = 0 := by
  refine ⟨![a 1, -a 0], fun h => ha ?_, ?_⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    funext i
    fin_cases i
    · simpa using h1
    · simpa using h0
  · simp [Fin.sum_univ_two]
    ring

private theorem halves {F : Type} [Field F] (p : Fin (2 + 2) → F) (h1 : (fun i => p (Fin.castAdd 2 i)) = 0)
    (h2 : (fun i => p (Fin.natAdd 2 i)) = 0) : p = 0 := by
  funext i
  exact Fin.addCases (fun i => congrFun h1 i) (fun i => congrFun h2 i) i

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.linAlg :
    ∀ {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) (r : ℕ), (r = 1 ∨ r = 3 ∨ (r = 2 ∧
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2) ≠ 0 ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det = 0)) →
      ∃ (X₀ : UPos (2 + 2) r → F) (m : GL (Fin 2) F) (C : Matrix (Fin 2) (Fin 2) F),
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 C 0 ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val)) ∨
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val) C 0 0) := by
  intro F _ γ r hr
  have hcol : ∀ k i : Fin (2 + 2), (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec (fun s => γ.val s k) i =
      (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) i k := fun k i => by
    rw [← Units.inv_mul γ]; rfl
  have hrow : ∀ k j : Fin (2 + 2), Matrix.vecMul (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val k s) γ.val j =
      (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) k j := fun k j => by
    rw [← Units.inv_mul γ]; rfl
  rcases hr with rfl | rfl | ⟨rfl, hne, hdet⟩
  · have hp : ∀ i : Fin (2 + 2), 1 ≤ (i : ℕ) →
        (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec (fun s => γ.val s 0) i = 0 := fun i hi => by
      rw [hcol, Matrix.one_apply_ne]
      rintro rfl
      simp at hi
    have h0 : ∀ j : Fin (2 + 2), (j : ℕ) < 1 → j = 0 := fun j hj => Fin.ext (by simpa using hj)
    by_cases hb : (fun i => γ.val (Fin.natAdd 2 i) 0) = 0
    · have ha : (fun i => γ.val (Fin.castAdd 2 i) 0) ≠ 0 := fun ha => by
        have := hcol 0 0
        rw [halves (fun s => γ.val s 0) ha hb] at this
        simp at this
      obtain ⟨c, hc, hs⟩ := perp _ ha
      refine core γ 1 _ (Fin.append c 0) hp (fun j hj => ?_) (Or.inr ⟨hb, ha, by simpa only [Fin.append_left] using hc⟩)
      rw [h0 j hj, Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using hs
    · obtain ⟨c, hc, hs⟩ := perp _ hb
      refine core γ 1 _ (Fin.append 0 c) hp (fun j hj => ?_)
        (Or.inl ⟨by funext i; simp only [Fin.append_left], by simpa only [Fin.append_right] using hc, hb⟩)
      rw [h0 j hj, Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] using hs
  · have hq : ∀ j : Fin (2 + 2), (j : ℕ) < 3 →
        Matrix.vecMul (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 s) γ.val j = 0 := fun j hj => by
      rw [hrow, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hj
    have h0 : ∀ j : Fin (2 + 2), 3 ≤ (j : ℕ) → j = 3 := fun j hj => Fin.ext (by
      have := j.2
      show (j : ℕ) = 3
      omega)
    by_cases ha : (fun i => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 (Fin.castAdd 2 i)) = 0
    · have hb : (fun i => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 (Fin.natAdd 2 i)) ≠ 0 := fun hb => by
        have := hrow 3 3
        rw [halves (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 s) ha hb, Matrix.zero_vecMul, Matrix.one_apply_eq] at this
        exact zero_ne_one this
      obtain ⟨c, hc, hs⟩ := perp _ hb
      refine core γ 3 (Fin.append 0 c) _ (fun j hj => ?_) hq (Or.inl ⟨ha, hb, by simpa only [Fin.append_right] using hc⟩)
      rw [h0 j hj, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
        mul_comm] using hs
    · obtain ⟨c, hc, hs⟩ := perp _ ha
      refine core γ 3 (Fin.append c 0) _ (fun j hj => ?_) hq
        (Or.inr ⟨by funext i; simp only [Fin.append_right], by simpa only [Fin.append_left] using hc, ha⟩)
      rw [h0 j hj, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        mul_comm] using hs
  · obtain ⟨c, hc, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, (fun i => γ.val (Fin.natAdd 2 i) (Fin.castAdd 2 k)) ≠ 0 := by
      by_contra hall
      apply hne
      ext i k
      by_contra hik
      exact hall ⟨k, fun h => hik (congrFun h i)⟩
    refine core γ 2 (fun s => γ.val s (Fin.castAdd 2 k)) (Fin.append 0 c) (fun i hi => ?_) (fun j hj => ?_)
      (Or.inl ⟨by funext i; simp only [Fin.append_left], by simpa only [Fin.append_right] using hc, hk⟩)
    · rw [hcol, Matrix.one_apply_ne]
      rintro rfl
      have := k.2
      simp only [Fin.val_castAdd] at hi
      omega
    · have hj' : j = Fin.castAdd 2 ⟨j, hj⟩ := rfl
      rw [hj', Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      exact congrFun hs ⟨j, hj⟩
end

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem row_two {K : Type} [Field K] {n : ℕ} {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) (i : Fin n) {a b : Fin n} (hab : a ≠ b) : ‖k i a‖ ^ 2 + ‖k i b‖ ^ 2 ≤ 1 := by
  classical
  have h := mem_archCompact.1 hk (Pi.single i 1)
  rw [Matrix.single_one_vecMul] at h
  have h1 : euclidNorm (Pi.single i (1 : w.Completion)) = 1 := by
    rw [euclidNorm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp only [Pi.single_eq_same, norm_one, one_pow, Real.sqrt_one]
  rw [h1, euclidNorm, Real.sqrt_eq_one] at h
  rw [← h, ← Finset.sum_pair (f := fun j => ‖k i j‖ ^ 2) hab]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.subDet :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (k : AdelicGLn.AdelicGL K n), k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) → ∀ (r c : Fin 2 → Fin n), Function.Injective r → Function.Injective c →
      (∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1) ∧
      ∀ m : AdelicGLn.AdelicGL K 2, (m : Matrix (Fin 2) (Fin 2) 𝔸[K]) = (k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c → (detModule K 2 m).1 ≤ 1 := by
  intro K _ _ n k hk r c _ hc
  have hc01 : c 0 ≠ c 1 := fun h => absurd (hc h) (by decide)
  have H1 : ∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1 := by
    intro w
    have h0 := row_two ((mem_maxCompact.1 hk).1 w) (r 0) hc01
    have h1 := row_two ((mem_maxCompact.1 hk).1 w) (r 1) hc01
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w =
        infAt w k (r 0) (c 0) * infAt w k (r 1) (c 1) - infAt w k (r 0) (c 1) * infAt w k (r 1) (c 0) := by
      rw [← infEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [sq_nonneg (‖infAt w k (r 0) (c 0)‖ - ‖infAt w k (r 1) (c 1)‖),
      sq_nonneg (‖infAt w k (r 0) (c 1)‖ - ‖infAt w k (r 1) (c 0)‖)]
  have H2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1 := by
    intro v
    have hv := (mem_maxCompact.1 hk).2 v
    rw [GLnLocal.mem_integralGL_iff] at hv
    simp only [GroundTheory.Global.mem_valuationInteger_iff] at hv
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v =
        finAt v k (r 0) (c 0) * finAt v k (r 1) (c 1) - finAt v k (r 0) (c 1) * finAt v k (r 1) (c 0) := by
      rw [← finEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    exact norm_le_one_of_mem v (sub_mem (mul_mem (hv.1 _ _) (hv.1 _ _)) (mul_mem (hv.1 _ _) (hv.1 _ _)))
  refine ⟨H1, H2, fun m hm => ?_⟩
  rw [← hm] at H1 H2
  change (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 m) : ℝ) ≤ 1
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  refine mul_le_one₀ (Finset.prod_le_one₀ (fun _ _ => by positivity)
    fun w _ => pow_le_one₀ (norm_nonneg _) (H1 w)) (finprod_nonneg fun _ => norm_nonneg _) ?_
  exact finprod_induction (fun x : ℝ => 0 ≤ x ∧ x ≤ 1) ⟨zero_le_one, le_rfl⟩
    (fun x y hx hy => ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩)
    (fun v => ⟨norm_nonneg _, H2 v⟩) |>.2
end

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem tens_interp {X : Type} (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (a : ℕ) (φ : Fin a → X → ℂ) (x : Fin a → X), (∀ i, φ i ∈ E) ∧
      ∀ f ∈ E, ∀ u, f u = ∑ i, f (x i) * φ i u := by
  classical
  let ev : X → Module.Dual ℂ E := fun u => (LinearMap.proj u).comp E.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext u
    by_contra hu
    exact h ⟨ev u, ⟨u, rfl⟩, hu⟩
  obtain ⟨κ, c, -, hc, hli⟩ := exists_linearIndependent' ℂ ev
  haveI : Finite κ := hli.finite
  obtain ⟨a, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  let b0 : Module.Basis κ ℂ (Module.Dual ℂ E) := Module.Basis.mk hli (by rw [hc, hspan])
  let b : Module.Basis (Fin a) ℂ (Module.Dual ℂ E) := b0.reindex e
  have hb : ∀ i, b i = ev (c (e.symm i)) := by
    intro i
    simp [b, b0]
  refine ⟨a, fun i => ((Module.evalEquiv ℂ E).symm (b.coord i) : E), fun i => c (e.symm i),
    fun i => Subtype.property _, ?_⟩
  intro f hf u
  have h1 := b.sum_repr (ev u)
  have h2 := congrArg (fun l : Module.Dual ℂ E => l ⟨f, hf⟩) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb] at h2
  have h3 : ∀ i, (((Module.evalEquiv ℂ E).symm (b.coord i) : E) : X → ℂ) u = b.repr (ev u) i := by
    intro i
    have : ev u ((Module.evalEquiv ℂ E).symm (b.coord i)) = b.coord i (ev u) :=
      Module.apply_evalEquiv_symm_apply ℂ E _ _
    exact this
  change ev u ⟨f, hf⟩ = _
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h3, mul_comm]
  rfl

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tens :
    ∀ {X Y : Type} (E₁ : Submodule ℂ (X → ℂ)) (E₂ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ E₁] [FiniteDimensional ℂ E₂],
      ∃ (a b : ℕ) (φ : Fin a → X → ℂ) (ψ : Fin b → Y → ℂ) (x : Fin a → Fin a → X) (y : Fin b → Fin b → Y) (s : Fin a → Fin a → ℂ) (t : Fin b → Fin b → ℂ),
        (∀ i, φ i ∈ E₁) ∧ (∀ j, ψ j ∈ E₂) ∧ ∀ Φ : X → Y → ℂ, (∀ v, (fun u => Φ u v) ∈ E₁) → (∀ u, Φ u ∈ E₂) →
          ∀ u v, Φ u v = ∑ i, ∑ j, (∑ p, ∑ q, s i p * t j q * Φ (x i p) (y j q)) * φ i u * ψ j v := by
  intro X Y E₁ E₂ _ _
  obtain ⟨a, φ, x, hφ, hx⟩ := tens_interp E₁
  obtain ⟨b, ψ, y, hψ, hy⟩ := tens_interp E₂
  refine ⟨a, b, φ, ψ, fun _ p => x p, fun _ q => y q, fun i p => if p = i then 1 else 0,
    fun j q => if q = j then 1 else 0, hφ, hψ, ?_⟩
  intro Φ h1 h2 u v
  have hs : ∀ i j, (∑ p, ∑ q, (if p = i then (1 : ℂ) else 0) * (if q = j then (1 : ℂ) else 0) *
      Φ (x p) (y q)) = Φ (x i) (y j) := by
    intro i j
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro q _ hq; simp [hq]
    · simp
    · intro p _ hp; simp [hp]
    · simp
  simp only [hs]
  rw [hx _ (h1 v) u]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy _ (h2 (x i)) v, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end
