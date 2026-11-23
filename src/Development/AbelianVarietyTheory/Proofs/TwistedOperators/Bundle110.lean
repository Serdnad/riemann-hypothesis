module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle005
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle780
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.RealPlaceAnalysis.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle117
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle103
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.CoverKGen

open GlobalTheory.RealPar GlobalTheory.RealPar.KStabLie GlobalTheory.RealPar.TorusWt Matrix

variable {p q : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have hlt : a < b := hab
    simp only [finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd]
    exact Fin.lt_def.mp hlt
  · simp [posC] at hab
  · simp [posC] at hab
  · have hlt : a < b := hab
    have := Fin.lt_def.mp hlt
    simp only [finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd]
    omega

theorem exists_log (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ X, X ∈ upq p q ∧ IsKC X ∧ T.cov (T.expt X) = T.cov k := by
  have hB := blockOrd_std p q
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exponential_surjective _ _ _ (mem_Kset hB T hk)
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Mat p q) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Mat p q) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Mat p q) := FiniteDimensional.complete ℂ (Mat p q)
  letI : NormedRing (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := p) (n := q))
  have hφc : Continuous φ := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact continuous_id.matrix_reindex _ _
  have hφX : φ (φ.symm Y) = Y := φ.apply_symm_apply Y
  have hJ : φ (Jm p q) = Formalism.REAL.Jm (fun i => (finSumFinEquiv.symm i).isLeft) := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact hB.reindex_Jm
  have hstar : ∀ M : Mat p q, φ Mᴴ = (φ M)ᴴ := fun M =>
    (Matrix.conjTranspose_reindex _ _ M).symm
  have hX : φ.symm Y ∈ upq p q := by
    show (φ.symm Y)ᴴ * Jm p q + Jm p q * φ.symm Y = 0
    apply φ.injective
    rw [map_add (f := _), map_mul, map_mul, hstar, hJ, hφX, map_zero]
    exact hY.1
  refine ⟨φ.symm Y, hX, ?_, ?_⟩
  · rw [isKC_iff]
    apply φ.injective
    rw [map_mul, map_mul, hJ, hφX]
    exact hY.2
  · apply Units.ext
    rw [T.expt_cov _ hX]
    apply φ.injective
    have hm : φ (NormedSpace.exp (φ.symm Y)) = NormedSpace.exp (φ (φ.symm Y)) :=
      NormedSpace.map_exp φ hφc _
    rw [hm, hφX, hexp]
    rfl

theorem torX_isKC (θ : Ix p q → ℝ) : IsKC (torX θ) := by
  intro a b hab
  have hne : a ≠ b := by
    rintro rfl
    exact hab (by cases a <;> trivial)
  simp [torX, Matrix.diagonal_apply_ne _ hne]

theorem cov_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.cov (T.expt (torX θ)) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem θ)]
  unfold torX
  rw [Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

private theorem sq_expt_torX_sq_eq_exp (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) ^ 2 =
      Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) ^ 2 := by
  rw [T.sq_sq, cov_expt_torX, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_nat_mul]
  congr 1
  rw [← Finset.sum_mul]
  push_cast
  ring

theorem sq_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) = Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) := by
  let f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • torX θ)) : ℂˣ) : ℂ)
  let g : ℝ → ℂ := fun t => Complex.exp ((∑ a, ((t * θ a : ℝ) : ℂ)) * Complex.I / 2)
  have hsq : ∀ t, f t ^ 2 = g t ^ 2 := fun t => by
    simp only [f, g]
    rw [smul_torX]
    exact sq_expt_torX_sq_eq_exp T _
  have hg : ∀ t, g t ≠ 0 := fun t => Complex.exp_ne_zero _
  have hfc : Continuous f := by
    have h1 : Continuous fun t : ℝ => T.expt (t • torX θ) :=
      T.expt_cont.comp_continuous (continuous_id.smul continuous_const)
        (fun t => smul_mem_upq (torX_mem θ) t)
    have h2 : Continuous fun x : T.G => T.sq x := continuous_snd.comp T.emb.continuous
    exact Units.continuous_val.comp (h2.comp h1)
  have hgc : Continuous g := by fun_prop
  have hh : ∀ t, f t / g t = 1 ∨ f t / g t = -1 := fun t => by
    have h2 : (f t / g t) ^ 2 = 1 := by
      rw [div_pow, hsq t, div_self (pow_ne_zero 2 (hg t))]
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
  have h0 : f 0 / g 0 = 1 := by
    simp [f, g, T.expt_zero]
  have hcont : Continuous fun t => f t / g t := hfc.div hgc hg
  have h1 : f 1 / g 1 = 1 := by
    rcases hh 1 with h1 | h1
    · exact h1
    exfalso
    have hre : Continuous fun t => (f t / g t).re := Complex.continuous_re.comp hcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((f 1 / g 1).re) ((f 0 / g 0).re) := by
      rw [h0, h1]
      norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hre.continuousOn hmem
    rcases hh t with h2 | h2 <;> simp only [h2] at ht <;> norm_num at ht
  have hfg : f 1 = g 1 := (div_eq_one_iff_eq (hg 1)).mp h1
  simpa [f, g] using hfg

theorem kset_gen : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset,
    k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  intro p q hpq T k hk
  have mem : ∀ X, X ∈ upq p q → IsKC X →
      T.expt X ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) :=
    fun X h1 h2 => Subgroup.subset_closure ⟨X, ⟨h1, h2⟩, rfl⟩
  obtain ⟨a0⟩ : Nonempty (Ix p q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  have hc := mem _ (torX_mem (Pi.single a0 (2 * Real.pi))) (torX_isKC (Pi.single a0 (2 * Real.pi)))
  have hcov : T.cov (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = 1 := by
    apply Units.ext
    rw [cov_expt_torX, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = a0
    · subst ha
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_eq_of_ne ha]
  have hsqc : T.sq (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = -1 := by
    apply Units.ext
    rw [sq_expt_torX]
    have hs : (∑ a, (((Pi.single a0 (2 * Real.pi) : Ix p q → ℝ) a : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) := by
      rw [Finset.sum_eq_single a0 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp
    have hpi : 2 * (Real.pi : ℂ) * Complex.I / 2 = Real.pi * Complex.I := by ring
    rw [hs, hpi, Complex.exp_pi_mul_I]
    simp
  obtain ⟨X, hX, hXK, hcovX⟩ := exists_log T hk
  have hy := mem X hX hXK
  have huniq : ∀ x : T.G, T.cov x = T.cov k → T.sq x = T.sq k → x = k := fun x h1 h2 =>
    (T.bij (T.cov k) (T.cov_mem k) (T.sq k) (T.sq_sq k)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  have hsq2 : ((T.sq (T.expt X) : ℂˣ) : ℂ) ^ 2 = ((T.sq k : ℂˣ) : ℂ) ^ 2 := by
    rw [T.sq_sq, T.sq_sq, hcovX]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
  · rw [← huniq _ hcovX (Units.ext h)]
    exact hy
  · have hk' : T.expt X * T.expt (torX (Pi.single a0 (2 * Real.pi))) = k := by
      apply huniq
      · rw [map_mul, hcov, mul_one, hcovX]
      · apply Units.ext
        rw [map_mul, hsqc]
        simp [h]
    rw [← hk']
    exact Subgroup.mul_mem _ hy hc

end GlobalTheory.CoverKGen

end
end

section

noncomputable section

open Matrix Formalism.L2.DIV

namespace GlobalTheory.ParIndex

variable {κ : Type} [Field κ] {r t : ℕ}

abbrev blkForm (g : GL (Fin (r + t)) κ) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) κ :=
  (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).submatrix finSumFinEquiv finSumFinEquiv

theorem blkForm_toBlocks₂₁ {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₁ = 0 := by
  ext i j
  simp only [toBlocks₂₁, blkForm, submatrix_apply, of_apply, Matrix.zero_apply, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]
  apply hg
  have hj : (Fin.castAdd t j).val < r := j.2
  have hi : ¬ (Fin.natAdd r i).val < r := by simp
  simp only [blk2, hj, hi, if_true, if_false]
  exact Nat.zero_lt_one

theorem blkForm_eq {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    blkForm g = fromBlocks (blkForm g).toBlocks₁₁ (blkForm g).toBlocks₁₂ 0 (blkForm g).toBlocks₂₂ := by
  rw [← blkForm_toBlocks₂₁ hg, fromBlocks_toBlocks]

theorem det_blkForm_toBlocks22_ne_zero_of_mem_blockTri {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    (blkForm g).toBlocks₂₂.det ≠ 0 := by
  have h1 : (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have h2 : (blkForm g).det = (g : Matrix (Fin (r + t)) (Fin (r + t)) κ).det := det_submatrix_equiv_self _ _
  rw [blkForm_eq hg, det_fromBlocks_zero₂₁] at h2
  intro h; rw [h, mul_zero] at h2; exact h1 h2.symm

def blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) : GL (Fin (r + t)) κ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm) (by
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact mul_ne_zero (A.isUnit.map Matrix.detMonoidHom).ne_zero (D.isUnit.map Matrix.detMonoidHom).ne_zero)

theorem blkForm_blkMk (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkForm (blkMk A D B) = fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin t) (Fin t) κ) := by
  ext i j
  simp [blkForm, blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem blkMk_mem (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    blkMk A D B ∈ blockTri (blk2 r) := by
  intro i j hij
  have key : r ≤ i.val ∧ j.val < r := by unfold blk2 at hij; split_ifs at hij <;> omega
  obtain ⟨i', rfl⟩ : ∃ i', i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, by ext; simp; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = Fin.castAdd t j' := ⟨⟨j.val, key.2⟩, by ext; simp⟩
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem topBlock_upperTriangularBlockGL (hr : r ≤ r + t) (A : GL (Fin r) κ) (D : GL (Fin t) κ) (B : Matrix (Fin r) (Fin t) κ) :
    upperLeftBlock hr (blkMk A D B) = A := by
  ext i j
  rw [upper_block_val_submatrix hr (blkMk_mem A D B)]
  have : Fin.castLE hr = Fin.castAdd t := rfl
  rw [this]
  simp [blkMk, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem upperLeftBlock_eq_blkForm_toBlocks11 (hr : r ≤ r + t) {g : GL (Fin (r + t)) κ} (hg : g ∈ blockTri (blk2 r)) :
    ((upperLeftBlock hr g : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = (blkForm g).toBlocks₁₁ := by
  rw [upper_block_val_submatrix hr hg]
  ext i j
  rfl

def parSubEquiv (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) :
    parSub hr H ≃ H × GL (Fin t) κ × Matrix (Fin r) (Fin t) κ where
  toFun g := (⟨upperLeftBlock hr g, g.2.2⟩,
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1), (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂)
  invFun x := ⟨blkMk x.1 x.2.1 x.2.2, blkMk_mem _ _ _, by rw [topBlock_upperTriangularBlockGL]; exact x.1.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    have h1 := blkForm_blkMk (r := r) (t := t) (κ := κ) (upperLeftBlock hr g)
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1)) (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂
    have h2 := blkForm_eq g.2.1
    rw [upperLeftBlock_eq_blkForm_toBlocks11 hr g.2.1] at h1
    have h3 : blkForm (blkMk (upperLeftBlock hr g) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_blkForm_toBlocks22_ne_zero_of_mem_blockTri g.2.1))
        (blkForm (g : GL (Fin (r + t)) κ)).toBlocks₁₂) = blkForm (g : GL (Fin (r + t)) κ) := by
      exact h1.trans h2.symm
    ext i j
    have := congrFun (congrFun h3 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
    simpa [blkForm] using this
  right_inv x := by
    obtain ⟨A, D, B⟩ := x
    refine Prod.ext (Subtype.ext (topBlock_upperTriangularBlockGL hr _ _ _)) (Prod.ext ?_ ?_)
    · apply Units.ext
      show (blkForm (blkMk A.1 D B)).toBlocks₂₂ = _
      rw [blkForm_blkMk]; rfl
    · show (blkForm (blkMk A.1 D B)).toBlocks₁₂ = _
      rw [blkForm_blkMk]; rfl

theorem card_parSub_eq (hr : r ≤ r + t) (H : Subgroup (GL (Fin r) κ)) [Finite κ] :
    Nat.card (parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  rw [Nat.card_congr (parSubEquiv hr H), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin t → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin t),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]

theorem card_parSub : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ) (hr : r ≤ n), n = r + t →
    ∀ H : Subgroup (GL (Fin r) κ),
      Nat.card (GlobalTheory.ParIndex.parSub hr H) = Nat.card H * Nat.card (GL (Fin t) κ) * Nat.card κ ^ (r * t) := by
  intro κ _ _ n r t hr hn H
  subst hn
  exact card_parSub_eq hr H

end GlobalTheory.ParIndex

end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem fock_casimir_apply (p q r s : ℕ) (P : Pol p q r s) :
    casimir (fockAct2 p q r s) P = casimir (fockAct1 p q r s) P -
      ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) • P := by
  have h := LinearMap.congr_fun (GlobalTheory.T.casimir_fockAct1_sub_casimir_fockAct2_eq_smul_one p q r s) P
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h
  rw [← h, sub_sub_cancel]

end GlobalTheory
end

section

open Formalism.L2.DIV MvPolynomial

theorem _root_.GlobalTheory.T.coeff_coefficientSpaceAction_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowRho.coeff_rhoVr_mem_range | exact GlobalTheory.RowRho.coeff_rhoVr_mem_range | (intros; apply GlobalTheory.RowRho.coeff_rhoVr_mem_range <;> assumption)
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

theorem vminus_coef : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  intro V _ _ n ε E Λ u hg hu hΛ F hF a b hab
  have hkr : KRel ε (arrE E 1) := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  have hku : KUnit ε E := isUnitary_kUnit ε E hu

  let φ : Arr V n 1 →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ u).comp ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V)
      (fun _ => (a, b))).comp (arrOf V n 1))
  suffices hle : Vminus ε E Λ u ≤ LinearMap.ker φ by
    have h0 : φ F = 0 := hle hF
    simpa [φ] using h0

  refine iSup₂_le fun y hy => ?_
  obtain ⟨-, μ, ⟨c, d, hdc, -, rfl⟩, hyh⟩ := hy
  rw [(kLow _ n ε (arrE E 1) _ y hkr hyh).1]
  refine Submodule.span_le.2 ?_
  rintro z ⟨w, hw, rfl⟩

  obtain ⟨ν, hht, hν⟩ := GlobalTheory.Jet.VminusComp.word_weight hkr hyh.1 w hw
  have hcw := GlobalTheory.Jet.VminusComp.comp_weight hν a b
  have hne : Λ ≠ ν - root a b := by
    intro h
    have h1 := congrArg GlobalTheory.Jet.VminusComp.ht h
    rw [GlobalTheory.Jet.VminusComp.ht_sub, GlobalTheory.Jet.VminusComp.ht_root] at h1
    rw [GlobalTheory.Jet.VminusComp.ht_add, GlobalTheory.Jet.VminusComp.ht_root] at hht
    have h2 : ((d : ℕ) : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast hdc
    have h3 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

  have h0 := kWtOrth V n ε E Λ (ν - root a b) u _ hku hΛ.1 hcw hne
  simpa [φ, arrOf] using h0

end GlobalTheory.SphJet
end
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

theorem _root_.GlobalTheory.T.exists_unitary_positiveBlock_column_eq : ∀ (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ), ε z = true → (∀ i, ε i = false → u i = 0) → ∑ i, ‖u i‖ ^ 2 = 1 → ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := by
  first | exact @GlobalTheory.Twist.Boost.exists_unitary_col | exact GlobalTheory.Twist.Boost.exists_unitary_col | (intros; apply GlobalTheory.Twist.Boost.exists_unitary_col <;> assumption)
end

end

section

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.negativeRootArray_highestVector_coeff_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  first | exact @GlobalTheory.SphJet.vminus_coef | exact GlobalTheory.SphJet.vminus_coef | (intros; apply GlobalTheory.SphJet.vminus_coef <;> assumption)

end
end
