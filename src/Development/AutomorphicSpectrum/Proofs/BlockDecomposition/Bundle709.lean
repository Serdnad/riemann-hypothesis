module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.Centre

open GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem centre_commutes_embedded_block {R : Type} [CommRing R] (hn : ρ + p = n) (z : Matrix (Fin ρ) (Fin ρ) R)
    (a b c d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (blk4 1 (bl hn z 0 0 0) 0 1)
        (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)) =
      HMul.hMul (blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d))
        (blk4 1 (bl hn z 0 0 0) 0 1) := by
  have h1 : HMul.hMul (bl hn z 0 0 0) (bl hn 0 0 0 c) = 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [bl]
  have h2 : HMul.hMul (bl hn z 0 0 0) (bl hn 1 0 0 d) = bl hn z 0 0 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have h3 : HMul.hMul (bl hn 1 0 0 a) (bl hn z 0 0 0) = bl hn z 0 0 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have h4 : HMul.hMul (bl hn 0 0 0 c) (bl hn z 0 0 0) = 0 := by
    simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [bl]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, h1, h2, h3, h4]
  congr 1 <;> simp [add_comm]

theorem nzx_add (M : Maps D hn) (a b : hermA D ρ) : M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0 := by
  rw [nzx_mul, add_zero]

theorem nzx_comm_sh (M : Maps D hn) (z : hermA D ρ) (y : Mx D ρ p) :
    M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0 := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.sh_mat, adj_zero]
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem nzx_comm_emb (M : Maps D hn) (z : hermA D ρ) (h : G D p) :
    M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0 := by
  obtain ⟨b, d, hb⟩ := SmallCell.exists_blocks (mat h)
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [mat_mul', mat_mul', M.nzx_mat, M.emb_mat h _ _ _ _ hb, adj_zero]
  exact centre_commutes_embedded_block hn z.1 _ _ _ _

theorem nzx_rat_mat (M : Maps D hn) (l : ratHerm D ρ) :
    ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 := by
  obtain ⟨b, hb⟩ := BigCell.exists_hermQ l
  have e : ∀ {a c : ℕ}, (0 : Matrix (Fin a) (Fin c) D.host.E).map (incA D) = 0 := rat_zero'
  refine ⟨b.1, hb, ?_⟩
  rw [blockMatrix_map₂, hb, e, e, e, M.nzx_mat, adj_zero]

theorem nzx_mem_GF (M : Maps D hn) (l : ratHerm D ρ) : M.nzx l.1 0 ∈ GF D n := by
  have h := nzx_rat M l.1 l.2 0
  rwa [rat_zero'] at h

end GlobalTheory.CompanionTheory.ZUnf.Centre

namespace GlobalTheory.CompanionTheory.ZUnf

theorem centre_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ a b, M.nzx (a + b) 0 = M.nzx a 0 * M.nzx b 0) ∧ (∀ z y, M.nzx z 0 * M.sh y = M.sh y * M.nzx z 0) ∧
    (∀ z h, M.nzx z 0 * M.emb h = M.emb h * M.nzx z 0) ∧
    ∀ l : ratHerm D ρ, M.nzx l.1 0 ∈ GF D n ∧ ∃ ζ : Matrix (Fin ρ) (Fin ρ) D.host.E,
      ζ.map (incA D) = l.1.1 ∧ mat (M.nzx l.1 0) = blk4 1 ((bl hn ζ 0 0 0).map (incA D)) 0 1 :=
  fun M => ⟨Centre.nzx_add M, Centre.nzx_comm_sh M, Centre.nzx_comm_emb M,
    fun l => ⟨Centre.nzx_mem_GF M l, Centre.nzx_rat_mat M l⟩⟩

end GlobalTheory.CompanionTheory.ZUnf
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn.Model

namespace GlobalTheory.CompanionTheory.PcB

open GlobalTheory.CompanionTheory.FourierN (mat_injective)

theorem blockMatrix_zero' {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl]
  rw [Matrix.fromBlocks_zero]
  rfl

theorem lowerUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 c 1) (bl hn 1 0 0 d) = bl hn 1 0 c d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_lowerUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 0 c 1) = bl hn 1 0 (HMul.hMul d c) d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem upperUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 y 0 1) (bl hn 1 0 0 d) = bl hn 1 (HMul.hMul y d) 0 d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_upperUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 y 0 1) = bl hn 1 y 0 d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem sh_emb_levi (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p)
    (a : GL (Fin p) (AE D)) (h : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) (y : Mx D ρ p) :
    M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  have hinv : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj a.1 : Mx D p p) = (1 : Mx D p p) := by
    have h1 : HMul.hMul (a.1 : Mx D p p) ((a⁻¹).1 : Mx D p p) = (1 : Mx D p p) := by
      exact congrArg Units.val (mul_inv_cancel a)
    rw [← adj_mul, h1]
    exact adj_one
  have diag_mul (A A' B B' : Mx D n n) :
      blk4 A 0 0 A' * blk4 B 0 0 B' = blk4 (A * B) 0 0 (A' * B') := by
    rw [submatrix_fromBlocks_mul]
    congr 1 <;> simp
  apply mat_injective
  rw [mat_mul', mat_mul', M.sh_mat, M.sh_mat, M.emb_mat g₀ _ _ _ _ h, blockMatrix_zero', diag_mul, diag_mul]
  congr 1
  · rw [upperUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_upperUnipotent]
  · have hk : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj (HMul.hMul y a.1 : Mx D ρ p)) = adj y := by
      rw [adj_mul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hk' : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (-adj (HMul.hMul y a.1 : Mx D ρ p)) = -adj y := by
      rw [Matrix.mul_neg, hk]
    rw [lowerUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_lowerUnipotent, hk']

end GlobalTheory.CompanionTheory.PcB
end
end
