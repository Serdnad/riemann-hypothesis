module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle697
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem adj_herm {D : D7} {ρ : ℕ} (b₀ : HermE D ρ) :
    adj (b₀.1.map (incA D) : Mx D ρ ρ) = b₀.1.map (incA D) := by
  have h := rat_conjTranspose b₀.1
  have e : b₀.1ᴴ = b₀.1 := b₀.2
  rw [e] at h
  exact h.symm

theorem chz_jc {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (y x : Mx D ρ p) :
    chz ψ b₀ (GlobalTheory.CompanionTheory.FJE.jc y x) = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y := by
  set B : Mx D ρ ρ := b₀.1.map (incA D) with hB
  have hadj : adj B = B := adj_herm b₀
  have e1 : Matrix.trace (B * (y * adj x)) = Matrix.trace (pr b₀ x y) := by
    show _ = Matrix.trace (adj x * (B * y))
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e2 : Matrix.trace (B * (x * adj y)) = cA D (Matrix.trace (pr b₀ x y)) := by
    rw [← GlobalTheory.CompanionTheory.FourierN.trace_adj]
    have h : adj (pr b₀ x y) = HMul.hMul (HMul.hMul (adj y) B : Mx D p ρ) x := by
      show adj (HMul.hMul (adj x) (HMul.hMul B y : Mx D ρ p) : Mx D p p) = _
      rw [adj_mul, adj_mul, adj_adj, hadj]
    rw [h, Matrix.trace_mul_comm, Matrix.mul_assoc x, Matrix.trace_mul_comm]
  have e3 : Matrix.trace (HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 : Mx D ρ ρ) =
      Matrix.trace (pr b₀ x y) + cA D (Matrix.trace (pr b₀ x y)) := by
    show Matrix.trace (B * (y * adj x + x * adj y)) = _
    rw [Matrix.mul_add, Matrix.trace_add, e1, e2]
  rw [chz, show HMul.hMul (b₀.1.map (incA D)) (GlobalTheory.CompanionTheory.FJE.jc y x).1 = HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 from rfl, e3,
    GlobalTheory.CompanionTheory.FourierN.halfTr_add_cA]
  rfl

end GlobalTheory.CompanionTheory.FJE
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

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

open GlobalTheory.StdUnn.Model
open GlobalTheory.CompanionTheory.JacobiMaps (b11 b12 b21 b22 block_matrix_of_blocks upperLeft_block upperRight_block lowerLeft_block_entry lowerRight_block continuous_block_matrix continuous_bl
  block_mul₂ bl_add block_sub blockRowSubstitution_one blockMatrix_zero blockMatrix_neg_one adj_bl adjoint_symplectic_block_product mkG isU_mat)

variable {D : D7} {n ρ p : ℕ}

def firstM (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ)) : Mx D (n + n) (n + n) :=
  blk4 (bl hn (b11 M) 0 0 1) (bl hn (b12 M) 0 0 0) (bl hn (b21 M) 0 0 0) (bl hn (b22 M) 0 0 1)

theorem first_block_embedding_block (hn : ρ + p = n) (a b c d : Mx D ρ ρ) :
    firstM hn (blk4 a b c d) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  rw [firstM, upperLeft_block, upperRight_block, lowerLeft_block_entry, lowerRight_block]

def firstMon (hn : ρ + p = n) : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n) where
  toFun := firstM hn
  map_one' := by
    rw [← block_matrix_one (R := AE D) (n := ρ), first_block_embedding_block, blockRowSubstitution_one]
    have e : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
    rw [e, block_matrix_one]
  map_mul' M N := by
    rw [← block_matrix_of_blocks M, ← block_matrix_of_blocks N]
    generalize b11 M = a
    generalize b12 M = b
    generalize b21 M = c
    generalize b22 M = d
    generalize b11 N = a'
    generalize b12 N = b'
    generalize b21 N = c'
    generalize b22 N = d'
    rw [submatrix_fromBlocks_mul, first_block_embedding_block, first_block_embedding_block, first_block_embedding_block, submatrix_fromBlocks_mul]
    simp only [block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem firstM_isU (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ))
    (h : (adj M * blk4 0 1 (-1) 0 * M : Mx D (ρ + ρ) (ρ + ρ)) = blk4 0 1 (-1) 0) :
    (adj (firstM hn M) * blk4 0 1 (-1) 0 * firstM hn M : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  rw [← block_matrix_of_blocks M] at h ⊢
  generalize b11 M = a at h ⊢
  generalize b12 M = b at h ⊢
  generalize b21 M = c at h ⊢
  generalize b22 M = d at h ⊢
  rw [adjoint_symplectic_block_product] at h
  obtain ⟨e1, e2, e3, e4⟩ := blockMatrixTwoByTwoFin_injective h
  have z : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Mx D ρ ρ) 0 0 (1 : Mx D p p) = 1 := blockRowSubstitution_one hn
  have m : bl hn (-1 : Mx D ρ ρ) 0 0 (-1 : Mx D p p) = -1 := blockMatrix_neg_one hn
  rw [first_block_embedding_block, adjoint_symplectic_block_product]
  simp only [adj_bl, adj_one, adj_zero, block_mul₂, block_sub, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, sub_zero, zero_sub, sub_self, e1, e2, e3, e4, z, o, m]

def firstF (hn : ρ + p = n) (g : G D ρ) : G D n :=
  mkG (Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g)) (firstM_isU hn _ (isU_mat g))

theorem matHom_firstF (hn : ρ + p = n) (g : G D ρ) :
    matHom _ D.sp.cm.sig (Jst D n) (firstF hn g) = Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) := rfl

def firstG (hn : ρ + p = n) : G D ρ →* G D n where
  toFun := firstF hn
  map_one' := matHom_injective _ D.sp.cm.sig (Jst D n) (by rw [matHom_firstF, map_one, map_one, map_one])
  map_mul' g h := matHom_injective _ D.sp.cm.sig (Jst D n) (by
    rw [map_mul, matHom_firstF, matHom_firstF, matHom_firstF, map_mul, map_mul])

theorem mat_firstG (hn : ρ + p = n) (h : G D ρ) : mat (firstG hn h) = firstM hn (mat h) := rfl

theorem continuous_firstM (hn : ρ + p = n) : Continuous (firstM (D := D) hn) :=
  continuous_block_matrix (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const
      continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)

theorem continuous_firstG (hn : ρ + p = n) : Continuous (firstG (D := D) hn) := by
  have h0 : Continuous (Units.map (firstMon (D := D) hn : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n))) :=
    Continuous.units_map _ (continuous_firstM hn)
  have h : Continuous fun g : G D ρ => Units.map (firstMon (D := D) hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) :=
    h0.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D ρ)).continuous
  exact (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff.2 h

end GlobalTheory.CompanionTheory.FirstBlockEmb

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

theorem exists_first_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), ∃ ι : G D ρ →* G D n, Continuous ι ∧
  ∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  intro D n ρ p hn
  refine ⟨firstG hn, continuous_firstG hn, fun h a b c d e => ?_⟩
  exact (mat_firstG hn h).trans ((congrArg (firstM hn) e).trans (first_block_embedding_block hn a b c d))

end GlobalTheory.CompanionTheory.FirstBlockEmb
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

namespace Integ

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem det_bl {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.det (bl hn 1 y 0 1 : Mx D n n) = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

def blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) :=
  ⟨bl hn 1 y 0 1, bl hn 1 (-y) 0 1, GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ rfl,
    GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ (neg_neg y).symm⟩

theorem det_blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 y 0 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, ha]
  exact det_bl hn y

theorem lintegral_comp_char_one {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (hc : addEquivAddHaarChar φ = 1) (g : A → ℝ≥0∞) :
    ∫⁻ y, g (φ y) ∂μ = ∫⁻ y, g y ∂μ := by
  have key := addEquivAddHaarChar_smul_map μ φ
  rw [hc, one_smul] at key
  have hp : MeasurePreserving φ μ μ := ⟨φ.continuous.measurable, key⟩
  exact hp.lintegral_comp_emb φ.toHomeomorph.measurableEmbedding g

theorem lintegral_bl {a r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (ν : Measure (Mx D a n))
    (hν : ν.IsAddHaarMeasure) (g : Mx D a n → ℝ≥0∞) :
    ∫⁻ U, g (mm U (bl hn 1 y 0 1)) ∂ν = ∫⁻ U, g U ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) a n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) (blU hn y)
  have hc : addEquivAddHaarChar φ = 1 := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a n
      (1 : GL (Fin a) (AE D)) (blU hn y)
    rw [det_blU hn y (blU hn y) rfl] at h
    simpa only [map_one, one_pow, mul_one] using h
  have e : ∀ U : Mx D a n, mm U (bl hn 1 y 0 1) = φ U := fun U => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
    rfl
  simp only [e]
  exact lintegral_comp_char_one ν φ hc g

theorem jn_first {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  simp [jn, Matrix.submatrix_apply, Matrix.fromCols]

theorem xu_bl (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    mm (XU d hn x₀ h U) (bl hn 1 y 0 1) =
      mm d.jX (mm U (bl hn 1 y 0 1)) + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1)) := by
  unfold XU
  simp only [mm]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]

theorem inner_eq (hIkL : IkLint) (hJn : JnBl) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) {θ : InfFam D}
    (hθ : IsInfFam θ) {M : Mx D B.rank n → ℂ} (hM : M ∈ schwartzA θ B.rank n)
    (hM0 : ∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W)
    (y : Mx D W.rank t) :
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK ∂I.μ₁ =
      ‖ikp I M (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))‖ₑ := by
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hb : mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1) = jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0) :=
    hJn D n t _ _ hn _ _ y
  rw [← hb, ← hIkL D n t B W d I θ hθ M hM hM0]
  simp only [xu_bl]
  exact lintegral_bl hn y I.μ₁ hf.1
    (fun U => ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1))))‖ₑ ∂I.νK)

theorem continuous_jn {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun u : Mx D a r × Mx D a t => jn hn u.1 u.2 := by
  refine continuous_matrix fun i j => ?_
  change Continuous fun u : Mx D a r × Mx D a t =>
    Matrix.fromCols u.1 u.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact continuous_fst.matrix_elem i k
  | inr k => exact continuous_snd.matrix_elem i k

theorem continuous_bl {r t n : ℕ} (hn : r + t = n) : Continuous fun y : Mx D r t => (bl hn 1 y 0 1 : Mx D n n) :=
  (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_submatrix _ _

theorem continuous_pt {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun p : I.l.K × Par D n t W =>
      mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨-, g2, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hT := (top_mx (D := D) B.rank n).1
  have hU : Continuous fun p : I.l.K × Par D n t W => p.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hh : Continuous fun p : I.l.K × Par D n t W => p.2.1 := continuous_fst.comp continuous_snd
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hX : Continuous fun p : I.l.K × Par D n t W => XU d hn x₀ p.2.1 p.2.2.1 :=
    (continuous_const.matrix_mul hU).add (continuous_const.matrix_mul
      ((continuous_jn hn).comp (((continuous_ww x₀).comp hh).prodMk continuous_const)))
  exact ((continuous_mt B).comp (continuous_subtype_val.comp continuous_fst).inv).matrix_mul
    (hX.matrix_mul ((continuous_bl hn).comp hy))

end Integ


open Integ in
theorem integrable_core : IkSch → Dom → OrbFin → Shift → IkLint → Fub4 → JnBl → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) := by
  intro hIk hDom hOrb _ hIkL hFub hJn D n t B W d hn I θ hθ μ hμ x₀ hx₀ Φ hΦ η hη
  obtain ⟨M, hM, hM0, hMd⟩ := hDom D θ hθ B.rank n n id Function.injective_id Φ hΦ
  have hΨ : ikp I M ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ M hM).2
  obtain ⟨N, hN, -, hNd⟩ := hDom D θ hθ W.rank n W.rank (fun j => finCongr hn (Fin.castAdd t j))
    (fun a b h => by simpa using h) (ikp I M) hΨ

  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hBG : BorelSpace (GA D W) := ⟨rfl⟩
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hcΦ : Continuous Φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hcη : Continuous η := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hpt := continuous_pt (d := d) hn I x₀
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hcore : Continuous (core hn I x₀ Φ η) :=
    (hcΦ.comp hpt).mul (Complex.continuous_conj.comp (hcη.comp hy))
  refine ⟨hcore.measurable.aestronglyMeasurable, ?_⟩

  set F : I.l.K × GA D W × Mx D t n × Mx D W.rank t → ℝ≥0∞ := fun p =>
    ‖M (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)))‖ₑ * ‖η p.2.2.2‖ₑ with hF
  have hFm : Measurable F :=
    (hcM.comp hpt).measurable.enorm.mul (hcη.comp hy).measurable.enorm
  have hle : ∀ p, ‖core hn I x₀ Φ η p‖ₑ ≤ F p := fun p => by
    simp only [core, hF, enorm_mul, RCLike.enorm_conj]
    gcongr
    rw [enorm_le_iff_norm_le]
    refine (hMd _).trans ?_
    simpa using Complex.re_le_norm _
  have hη' : ∫⁻ y, ‖η y‖ₑ ∂μ < ⊤ :=
    hasFiniteIntegral_iff_enorm.1 (GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar D θ hθ W.rank t μ η hη).2
  have hN' : ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m < ⊤ := hOrb D θ hθ W I.m I.haar x₀ hx₀ N hN
  have hin : ∀ y h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ≤ ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ := fun y h => by
    simp only [hF]
    have e : ∀ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ * ‖η y‖ₑ ∂I.νK =
        (∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK) * ‖η y‖ₑ := fun U =>
      lintegral_mul_const' _ _ enorm_ne_top
    simp only [e]
    rw [lintegral_mul_const' _ _ enorm_ne_top, inner_eq hIkL hJn hn I hθ hM hM0 x₀ h y]
    gcongr
    rw [enorm_le_iff_norm_le]
    have h3 := hNd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
    rw [jn_first] at h3
    exact h3.trans (Complex.re_le_norm _)
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ p, ‖core hn I x₀ Φ η p‖ₑ ∂(I.νK.prod (Q0 I μ))
      ≤ ∫⁻ p, F p ∂(I.νK.prod (Q0 I μ)) := lintegral_mono hle
    _ = ∫⁻ y, ∫⁻ h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ∂I.m ∂μ :=
        (hFub I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).2 F hFm
    _ ≤ ∫⁻ y, ∫⁻ h, ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ ∂I.m ∂μ :=
        lintegral_mono fun y => lintegral_mono fun h => hin y h
    _ = (∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m) * ∫⁻ y, ‖η y‖ₑ ∂μ := by
        simp only [lintegral_mul_const' _ _ enorm_ne_top]
        rw [lintegral_const_mul' _ _ hN'.ne]
    _ < ⊤ := ENNReal.mul_lt_top hN' hη'

end GlobalTheory.CompanionTheory.ColumnSplitting

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

namespace GlobalTheory.CompanionTheory.ConstN

open GlobalTheory.CompanionTheory.FourierN


open Pointwise in
theorem setIntegral_add_right {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (L : AddSubgroup A)
    [Countable L] (lam : Measure A) [lam.IsAddLeftInvariant] {𝓖 : Set A} (hFD : IsAddFundamentalDomain L 𝓖 lam)
    (φ : A → ℂ) (hper : ∀ γ ∈ L, ∀ x, φ (γ + x) = φ x) (b : A) :
    ∫ x in 𝓖, φ (x + b) ∂lam = ∫ x in 𝓖, φ x ∂lam := by
  have hFD' : IsAddFundamentalDomain L (b +ᵥ 𝓖) lam := hFD.vadd_of_comm b
  have hpre : (fun x : A => x + b) ⁻¹' (b +ᵥ 𝓖) = 𝓖 := by
    ext x
    rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [add_comm]
  have h := (measurePreserving_add_right lam b).setIntegral_preimage_emb
    (MeasurableEquiv.addRight b).measurableEmbedding φ (b +ᵥ 𝓖)
  rw [hpre] at h
  exact h.trans (hFD'.setIntegral_eq hFD fun γ x => hper γ.1 γ.2 x)




theorem nb_inv_of_const (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (nb : hermA D p → G D p)
    (lam : Measure (hermA D p)) (𝓖 : Set (hermA D p)) (hC : CoefData (D := D) (n := p) nb lam 𝓖)
    (F : G D p → ℂ) (_hF : Continuous F) (hinv : LeftInv (GF D p) F) (β : HermE D p) (hβ : β.1 = 0)
    (hfc : ∀ g, fc ψ lam 𝓖 nb F β g = F g) (b : hermA D p) (g : G D p) : F (nb b * g) = F g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D p p
  haveI : BorelSpace (Mx D p p) := ⟨rfl⟩
  haveI : BorelSpace (hermA D p) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D p) := discrete_ratHerm
  haveI : Countable (ratHerm D p) := countable_of_Lindelof_of_discrete
  have hone : ∀ h : G D p, fc ψ lam 𝓖 nb F β h = ∫ x in 𝓖, F (nb x * h) ∂lam := by
    intro h
    refine integral_congr_ae (.of_forall fun x => ?_)
    have e : (HMul.hMul (β.1.map (incA D)) x.1 : Mx D p p) = 0 := by
      rw [hβ, Matrix.map_zero _ (map_zero _)]
      exact Matrix.zero_mul _
    show F (nb x * h) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D p p))) = F (nb x * h)
    rw [e, Matrix.trace_zero, halfTr_zero, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have hper : ∀ γ ∈ ratHerm D p, ∀ x : hermA D p, F (nb (γ + x) * g) = F (nb x * g) := by
    intro γ hγ x
    rw [nb_add hnb, mul_assoc]
    exact hinv _ (nb_rat hnb γ hγ) _
  have e1 : F g = ∫ x in 𝓖, F (nb x * g) ∂lam := (hfc g).symm.trans (hone g)
  have e2 : F (nb b * g) = ∫ x in 𝓖, F (nb (x + b) * g) ∂lam := by
    refine (hfc _).symm.trans ((hone _).trans (integral_congr_ae (.of_forall fun x => ?_)))
    show F (nb x * (nb b * g)) = F (nb (x + b) * g)
    rw [nb_add hnb, mul_assoc]
  rw [e2, e1]
  exact setIntegral_add_right (ratHerm D p) lam hFD (fun y => F (nb y * g)) hper b

end GlobalTheory.CompanionTheory.ConstN
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.whittaker_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.whitHeredity | exact GlobalTheory.CompanionTheory.Rodier.whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Rodier.whitHeredity <;> assumption)
end
