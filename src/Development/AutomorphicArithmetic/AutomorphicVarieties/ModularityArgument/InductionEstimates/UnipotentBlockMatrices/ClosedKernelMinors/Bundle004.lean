module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Ring

variable {R : Type} [CommRing R]

private def Low (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) : Prop :=
  ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 → M i j = 0

private theorem low_mul {M N : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R} (hM : Low M) (hN : Low N) : Low (M * N) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < 2
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j (not_lt.1 hk) hj, mul_zero]

private theorem low_blocks (A B D : Matrix (Fin 2) (Fin 2) R) :
    Low (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)) := by
  intro i j hi hj
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rcases i with i | i
  · exact absurd (show 2 ≤ (i : ℕ) from hi) (not_le.2 i.2)
  rcases j with j | j
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
  · exact absurd (show 2 + (j : ℕ) < 2 from hj) (by omega)

private def xm (X : UPos (2 + 2) 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j => X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), i.2, Nat.le_add_right 2 j⟩

private theorem unip_eq (X : UPos (2 + 2) 2 → R) :
    unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 (xm X) 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply, xm] <;> rfl

private theorem xm_bij : Function.Bijective (xm : (UPos (2 + 2) 2 → R) → _) := by
  constructor
  · intro X Y h
    apply unipGL_injective
    apply Units.ext
    rw [coe_unipGL, coe_unipGL, unip_eq, unip_eq, h]
  · intro B
    refine ⟨fun p => B ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩, ?_⟩
    ext i j
    simp [xm]

private theorem unip_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    ((unipGL X * blk a b : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val (xm X * b.val) 0 b.val) := by
  rw [Units.val_mul, coe_unipGL, unip_eq]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem unip_blk_inj {X X' : UPos (2 + 2) 2 → R} {a b a' b' : GL (Fin 2) R}
    (h : unipGL X * blk a b = unipGL X' * blk a' b') : X = X' ∧ a = a' ∧ b = b' := by
  have h1 := congrArg Units.val h
  rw [unip_blk, unip_blk] at h1
  obtain ⟨ha, hx, -, hb⟩ := Matrix.fromBlocks_inj.1 ((Matrix.reindex _ _).injective h1)
  obtain rfl : b = b' := Units.ext hb
  exact ⟨xm_bij.1 ((Units.mul_left_inj b).1 hx), Units.ext ha, rfl⟩

private theorem low_inv_unip_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    Low (((unipGL X * blk a b)⁻¹ : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) := by
  rw [mul_inv_rev, Units.val_mul, coe_unipGL_inv, unip_eq]
  exact low_mul (low_blocks _ _ _) (low_blocks _ _ _)

end Ring

private theorem low_decomp {K : Type} [Field K] (g : GL (Fin (2 + 2)) K) (hg : Low g.val) :
    ∃ (X : UPos (2 + 2) 2 → K) (a b : GL (Fin 2) K), g = unipGL X * blk a b := by
  set M := (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm g.val with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact hg _ _ (Nat.le_add_right 2 i) j.2
  have hb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hd : M.det ≠ 0 := by
    rw [hM, Matrix.reindex_symm, Matrix.det_reindex_self]
    exact g.det_ne_zero
  rw [hb, Matrix.det_fromBlocks_zero₂₁, mul_ne_zero_iff] at hd
  let a := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd.1
  let b := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd.2
  obtain ⟨X, hX⟩ := xm_bij.2 (M.toBlocks₁₂ * (b⁻¹).val)
  refine ⟨X, a, b, Units.ext ?_⟩
  rw [unip_blk, hX, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  change _ = Matrix.reindex _ _ (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂)
  rw [← hb, hM, Equiv.apply_symm_apply]

variable {K : Type} [Field K] [NumberField K]

private theorem diag_blk (a b : GL (Fin 2) K) :
    AdelicGLn.diagonal K (2 + 2) (blk a b) = blk (AdelicGLn.diagonal K 2 a) (AdelicGLn.diagonal K 2 b) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rw [AdelicGLn.diagonal_apply]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp

private theorem zt_zero : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  congr 1
  exact Subtype.ext Real.exp_zero

private theorem low_diag (g : GL (Fin (2 + 2)) K) : Low (AdelicGLn.diagonal K (2 + 2) g).val ↔ Low g.val :=
  forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ => by
    rw [AdelicGLn.diagonal_apply]
    exact map_eq_zero_iff _ (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K)

private theorem gam_cases {n : ℕ} (γ : Gam K n) : ∃ g : GL (Fin n) K,
    γ = ⟨⟨AdelicGLn.diagonal K n g, rationalGL_le_normOneGL ⟨g, rfl⟩⟩, g, rfl⟩ := by
  obtain ⟨g, hg⟩ := γ.2
  exact ⟨g, Subtype.ext (Subtype.ext hg.symm)⟩

private def lowΓ (K : Type) [Field K] [NumberField K] : Subgroup (Gam K (2 + 2)) where
  carrier := {γ | Low ((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)).val}
  one_mem' := by
    intro i j hi hj
    exact Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' ha hb := low_mul ha hb
  inv_mem' := by
    intro γ hg
    obtain ⟨g, rfl⟩ := gam_cases γ
    obtain ⟨X, a, b, rfl⟩ := low_decomp g ((low_diag g).1 hg)
    change Low (AdelicGLn.diagonal K (2 + 2) (unipGL X * blk a b))⁻¹.val
    rw [← map_inv, low_diag]
    exact low_inv_unip_blk X a b

private theorem par_eq : ParΓ K 2 2 = lowΓ K := Subgroup.closure_eq (lowΓ K)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pkLaws :
    ∀ {K : Type} [Field K] [NumberField K], (∀ γ : Gam K (2 + 2), γ ∈ ParΓ K 2 2 ↔ ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 →
        (((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) i j = 0) ∧
      (∀ γ : G1 K (2 + 2), γ ∈ PK K ↔ ∃ (ξ : unipLattice K (2 + 2) 2) (γ₁ : Gam K 2) (γ₂ : Gam K 2),
        γ = unipOne (K := K) (n := 2 + 2) 2 ξ.1 * lv γ₁ γ₂ 0) ∧
      (∀ (ξ ξ' : UPos (2 + 2) 2 → 𝔸[K]) (a b a' b' : G1 K 2) (t t' : ℝ),
        unipOne (K := K) (n := 2 + 2) 2 ξ * lv a b t =
          unipOne (K := K) (n := 2 + 2) 2 ξ' * lv a' b' t' → ξ = ξ' ∧ a = a' ∧ b = b' ∧ t = t') ∧
      ∀ γ : Gam K (2 + 2), ∃ δ ∈ PK K, (((Quotient.mk _ γ : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) = δ * γ := by
  intro K _ _
  have hlv := (blkLaws (K := K)).1
  have hco : ∀ (ξ : UPos (2 + 2) 2 → 𝔸[K]) (a b : G1 K 2) (t : ℝ),
      ((unipOne (K := K) (n := 2 + 2) 2 ξ * lv a b t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        unipGL ξ * blk ((a : AdelicGLn.AdelicGL K 2) * zt K t) ((b : AdelicGLn.AdelicGL K 2) * zt K (-t)) :=
    fun ξ a b t => by rw [Subgroup.coe_mul, hlv, coe_unipOne]
  have hdg : ∀ (X : UPos (2 + 2) 2 → K) (a b : GL (Fin 2) K) (h₁ h₂),
      ((unipOne (K := K) (n := 2 + 2) 2 (fun p => algebraMap K 𝔸[K] (X p)) *
        lv ⟨AdelicGLn.diagonal K 2 a, h₁⟩ ⟨AdelicGLn.diagonal K 2 b, h₂⟩ 0 :
        G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = AdelicGLn.diagonal K (2 + 2) (unipGL X * blk a b) :=
    fun X a b h₁ h₂ => by rw [hco, neg_zero, zt_zero, mul_one, mul_one, map_mul, diag_blk, diagonal_unipGL]
  refine ⟨fun γ => by rw [par_eq]; rfl, fun γ => ⟨?_, ?_⟩, ?_, fun γ => ?_⟩
  · rintro ⟨γ, hg, rfl⟩
    obtain ⟨g, rfl⟩ := gam_cases γ
    rw [par_eq] at hg
    obtain ⟨X, a, b, rfl⟩ := low_decomp g ((low_diag g).1 hg)
    exact ⟨⟨_, X, rfl⟩, ⟨⟨_, rationalGL_le_normOneGL ⟨a, rfl⟩⟩, a, rfl⟩, ⟨⟨_, rationalGL_le_normOneGL ⟨b, rfl⟩⟩, b, rfl⟩,
      Subtype.ext (hdg X a b _ _).symm⟩
  · rintro ⟨⟨_, X, rfl⟩, γ₁, γ₂, rfl⟩
    obtain ⟨a, rfl⟩ := gam_cases γ₁
    obtain ⟨b, rfl⟩ := gam_cases γ₂
    have h₁ : AdelicGLn.diagonal K 2 a ∈ normOneGL (K := K) (n := 2) := rationalGL_le_normOneGL ⟨a, rfl⟩
    have h₂ : AdelicGLn.diagonal K 2 b ∈ normOneGL (K := K) (n := 2) := rationalGL_le_normOneGL ⟨b, rfl⟩
    refine ⟨⟨_, unipGL X * blk a b, (hdg X a b h₁ h₂).symm⟩, ?_, rfl⟩
    rw [par_eq]
    change Low (Units.val _)
    have h := (low_diag (unipGL X * blk a b)).2 (by rw [unip_blk]; exact low_blocks _ _ _)
    rw [← hdg X a b h₁ h₂] at h
    exact h
  · intro ξ ξ' a b a' b' t t' h
    have h1 := congrArg Subtype.val h
    rw [hco, hco] at h1
    obtain ⟨hx, ha, hb⟩ := unip_blk_inj h1
    have h2 := congrArg (detModule K 2) ha
    rw [map_mul, map_mul, mem_normOneGL_iff_detModule.1 a.2, mem_normOneGL_iff_detModule.1 a'.2, one_mul, one_mul,
      zt, zt, detModule_centralSection two_pos, detModule_centralSection two_pos] at h2
    obtain rfl : t = t' := Real.exp_injective (congrArg Subtype.val h2)
    exact ⟨hx, Subtype.ext (mul_right_cancel ha), Subtype.ext (mul_right_cancel hb), rfl⟩
  · have h : (QuotientGroup.rightRel (ParΓ K 2 2)) γ (Quotient.mk _ γ : Cos K).out :=
      Quotient.exact (Quotient.out_eq _).symm
    rw [QuotientGroup.rightRel_apply] at h
    refine ⟨_, ⟨_, h, rfl⟩, ?_⟩
    simp
end

section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_blocks {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_onto {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_blocks]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem dec {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R), (c.val = (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ ∧
      c⁻¹.val = (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁) ∧
      (d.val = (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ ∧
      d⁻¹.val = (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂) ∧
      ∃ X : UPos (a + b) a → R, g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_onto (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem of_low {K : Type} [Field K] [NumberField K] (s : G1 K (2 + 2))
    (h : ((s : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : ((s : AdelicGLn.AdelicGL K (2 + 2))⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ X m₁ m₂ t, s = unipOne (K := K) (n := 2 + 2) 2 X * lv m₁ m₂ t := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  obtain ⟨a, d, -, -, X, hX⟩ := dec (s : AdelicGLn.AdelicGL K (2 + 2)) h h'
  refine ⟨X, retractOne a, retractOne d, Real.log (detModule K 2 a).1, ?_⟩
  have h1 : detModule K 2 a * detModule K 2 d = 1 := by
    have := mem_normOneGL_iff_detModule.1 s.2
    rwa [hX, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 d) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, coe_unipOne, hlv, z1, z2, coe_retractOne, coe_retractOne,
    inv_mul_cancel_right, inv_mul_cancel_right]
  exact hX

private theorem low_borel {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.iwa :
    ∀ {K : Type} [Field K] [NumberField K] (g : G1 K (2 + 2)),
      ∃ (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (t : ℝ),
        ∃ k ∈ KG K (2 + 2), g = unipOne (K := K) (n := 2 + 2) 2 X * lv m₁ m₂ t * k := by
  intro K _ _ g
  obtain ⟨b, hb, k, hk, e⟩ := exists_adelicBorel_mul_maxCompact (g : AdelicGLn.AdelicGL K (2 + 2))
  let k' : G1 K (2 + 2) := ⟨k, maxCompact_le_normOneGL hk⟩
  have hs : ((g * k'⁻¹ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = b := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, e]
    exact mul_inv_cancel_right b k
  obtain ⟨X, m₁, m₂, t, h⟩ := of_low (g * k'⁻¹) (by rw [hs]; exact low_borel hb) (by rw [hs]; exact low_borel (inv_mem hb))
  exact ⟨X, m₁, m₂, t, k', hk, by rw [← h, inv_mul_cancel_right]⟩
end
