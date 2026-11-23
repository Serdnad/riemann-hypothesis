module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SySmulRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ContinuousExpG
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.InFrameInvOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SigmaSigma
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.FrameOfSig
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
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

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
section Gen
variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') {α β : Type} [Fintype α]
  [DecidableEq α] [Fintype β] [DecidableEq β]
end Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₂
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = om (d.dd.e w) (d.dd.e w') :=
  d.dd.form w w'
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_left (w₁ w₂ w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (w₁ + w₂) w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w₁ w' + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w₂ w' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_add (f := _), om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right (w w₁ w₂ : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w (w₁ + w₂) = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w₁ + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w₂ := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_add (f := _), om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_smul_right (a : AF F) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w (a • w') = a * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_smul, om, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_sum_left {ι : Type} (s : Finset ι) (a : ι → AF F) (v : ι → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (∑ i ∈ s, a i • v i) w' = ∑ i ∈ s, a i * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (v i) w' := by

  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_sum, map_smul, om, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct,
  dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_antisymm (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = -_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w' w := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, om]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_diag (Z Z' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) (Z' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ (isLagr_diagCols (cA σ) (incM F d.Y.J)).1, mul_zero, map_zero]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.frame_iso : (d.b.1.toCols₂)ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := by
  obtain ⟨ε, h⟩ := d.ok.frame.1
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [Matrix.toBlocks_fromBlocks₂₂] at h2
  rw [← h2]
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame (X X' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (X' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = 0 := by
  have h : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d).map (cA σ) = 0 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, cA_incM, ← incM_dbl, ← incM_transpose, ← incM_mul, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.frame_iso, incM_zero']
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ h, mul_zero, map_zero]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.m) (Fin d.n) (AE F E) :=
  (w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_add (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (w + w') = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' := by
  ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.add_mul, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_smul (a : AF F) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (a • w) = a • _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w := by
  ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.smul_mul, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∃ Z : Matrix (Fin d.m) (Fin d.n) (AE F E), w = Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  set V := w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ with hV
  have h1 : w = V * (incM F d.b.1)ᵀ := by
    rw [hV, Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one', Matrix.transpose_one,
      Matrix.mul_one]
  have h2 : incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) := by
    ext i (j | j) <;> rfl
  refine ⟨V.toCols₁ * (incM F t.1)ᵀ, ?_⟩
  have h3 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w = V.toCols₂ := rfl
  rw [h3]
  conv_lhs => rw [h1, h2, ← Matrix.fromCols_toCols V]
  have ht' : incM F d.b.1.toCols₁ = @HMul.hMul (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      (Matrix (Fin d.n) (Fin d.n) (AE F E)) (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (diagCols (Fin d.n)) (incM F t.1) := by
    rw [ht, ← incM_diagCols (F := F) (E := E)]
    exact incM_mul _ _
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, ht', Matrix.transpose_mul, ← Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_frame (X : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = X := by
  have h1 : incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).toCols₂ := by
    have : (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * d.b.1.toCols₂ = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E).toCols₂ := by
      rw [← Units.inv_mul d.b]
      ext i j; simp [Matrix.mul_apply, Matrix.toCols₂]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, ← incM_mul, this]
    ext i j; simp [incM, Matrix.toCols₂, Matrix.one_apply]
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.mul_assoc, ← Matrix.transpose_mul, h1]
  ext i j
  simp [Matrix.toCols₂, Matrix.mul_apply, Matrix.one_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_split (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w' - _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w := by
  obtain ⟨Z, hZ⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w
  obtain ⟨Z', hZ'⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w'
  have a1 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) w' + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w' := by
    conv_lhs => rw [hZ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_left]
  have a2 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) := by
    conv_lhs => rw [hZ']
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_diag, zero_add]
  have a3 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) := by
    conv_lhs => rw [hZ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame, add_zero]
  rw [a1, a2, a3, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_antisymm d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)]
  ring
end Adp
end PositivityTheory.SiegelWeilFormula.TBij
end
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.thetaLift_weil_translate_equivariant :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → ∀ (a : UA σ X.J) (b h : UA σ W.J), lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = lift M om Φ φ (h * b) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ a b h
  have c : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have hTB := T.basic F E σ B n d X W M χX χW om n 0 d 0 hp
  let G : UA σ X.J → ℂ := fun x => theta om Φ x (h * b) * star (φ x)
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    have h1 := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (h * b)
    rw [one_mul] at h1
    simp only [G]
    rw [h1, hφ.2 γ hγ x]
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := c.right _ hp.good.haar
  haveI := c.cnt
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = ∫ x in M.dom, G (x * a) ∂M.μ := by
    unfold lift
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [G, theta]
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ a
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight a) G
    ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * a) ⁻¹' ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ a⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * a⁻¹ = γ.1 * (x * a⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd.setIntegral_eq hp.good.dom (f := G) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
theorem UpperTheory.continuous_thetaLift_of_definite :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → Continuous (lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ
  have cX : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have cW : Cpt σ W.J := T.cpt F E σ B d W d 0 hp.base (Or.inr hp.skew) (by simp)
  obtain ⟨t1, t2, -⟩ := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp).1 Φ hΦ
  obtain ⟨C, hC⟩ := cX.bdd₂ cW (f := fun x => theta om Φ x.1 x.2) t1 fun γ hγ δ hδ g g' => t2 γ hγ δ hδ g g'
  obtain ⟨C', hC'⟩ := cX.bdd hφ.1 hφ.2
  have hfin : M.μ M.dom < ⊤ := cX.fin _ _ hp.good.haar hp.good.dom
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI := cW.sc
  haveI : FirstCountableTopology (UA σ W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hs : Continuous fun g => star (φ g) := hφ.1.star
  unfold lift
  refine continuous_of_dominated (bound := fun _ => C * C') (fun h => ?_) (fun h => ?_) (integrable_const _) ?_
  · exact ((t1.comp (continuous_id.prodMk continuous_const)).mul hs).aestronglyMeasurable
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hC (g, h)) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC (g, h)))
  · refine Eventually.of_forall fun g => ?_
    exact (t1.comp (continuous_const.prodMk continuous_id)).mul continuous_const
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
namespace UpperTheory.TP.LiftLin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
theorem integrand_int_k (T : _root_.UpperTheory.TP.Tools_k) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) {φ : UA σ X.J → ℂ} (hφ : IsFn φ)
    (h : UA σ W.J) : IntegrableOn (fun g => theta om Φ g h * star (φ g)) M.dom M.μ := by
  have hc : Cpt σ X.J := T.cpt F E σ B n X n 0 hP.base (Or.inl hP.herm) (by simp)
  have ht := (T.basic F E σ B n d X W M χX χW om n 0 d 0 hP).1 Φ hΦ
  obtain ⟨h1, h2, -⟩ := ht
  have hcont : Continuous fun g => theta om Φ g h * star (φ g) :=
    (h1.comp (continuous_id.prodMk continuous_const)).mul (continuous_star.comp hφ.1)
  obtain ⟨C, hC⟩ := hc.bdd hcont fun γ hγ g => by
    have e := h2 γ hγ 1 (one_mem _) g h
    rw [one_mul] at e
    simp only [e, hφ.2 γ hγ g]
  exact Measure.integrableOn_of_bounded (M := C) (hc.fin M.μ M.dom hP.good.haar hP.good.dom).ne
    hcont.aestronglyMeasurable (Eventually.of_forall hC)
end UpperTheory.TP.LiftLin
open UpperTheory.TP.LiftLin in
theorem UpperTheory.thetaLift_linear_in_schwartz :
    _root_.UpperTheory.TP.Tools_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → (∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (Φ + Φ') φ = lift M om Φ φ + lift M om Φ' φ) ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (c • Φ) φ = c • lift M om Φ φ) ∧ (∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ φ' : UA σ X.J → ℂ, IsFn φ → IsFn φ' → lift M om Φ (φ + φ') = lift M om Φ φ + lift M om Φ φ') ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om Φ (c • φ) = (starRingEnd ℂ) c • lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  refine ⟨fun Φ hΦ Φ' hΦ' φ hφ => ?_, fun c Φ hΦ φ hφ => ?_, fun Φ hΦ φ φ' hφ hφ' => ?_, fun c Φ hΦ φ hφ => ?_⟩
  · funext h
    have e : ∀ g, theta om (Φ + Φ') g h * star (φ g) = theta om Φ g h * star (φ g) + theta om Φ' g h * star (φ g) := fun g => by
      have : theta om (Φ + Φ') g h = theta om Φ g h + theta om Φ' g h := by
        simp only [theta, map_add (f := _)]
        exact thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΦ')
      rw [this, add_mul]
    simp only [lift, Pi.add_apply, e]
    exact integral_add (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ hφ h) (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ' hφ h)
  · funext h
    have e : ∀ g, theta om (c • Φ) g h * star (φ g) = c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [theta, map_smul, thetaSum_smul, mul_assoc]
    simp only [lift, Pi.smul_apply, smul_eq_mul, e, integral_const_mul]
  · funext h
    have e : ∀ g, theta om Φ g h * star ((φ + φ') g) = theta om Φ g h * star (φ g) + theta om Φ g h * star (φ' g) := fun g => by
      simp only [Pi.add_apply, star_add, mul_add]
    simp only [lift, Pi.add_apply] at e ⊢
    simp only [e]
    exact integral_add (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ hφ h) (_root_.UpperTheory.TP.LiftLin.integrand_int_k T hP hΦ hφ' h)
  · funext h
    have e : ∀ g, theta om Φ g h * star ((c • φ) g) = (starRingEnd ℂ) c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring
    simp only [lift, Pi.smul_apply, smul_eq_mul] at e ⊢
    simp only [e, integral_const_mul]
end
end

section



section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
abbrev SD_k.LF (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := (Fin d.m → Fin d.n → ℂ) → ℂ
abbrev SD_k.MF (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := Mx F E d.m d.n → ℂ
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.StepOK (x : d.G) (A : d.LF → d.LF) (B : d.MF → d.MF) : Prop :=
  (∀ f, IsSw f → IsSw (A f)) ∧ ∀ Ψ, d.IsAwayW w Ψ → d.IsAwayW w (B Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w (A f) (B Ψ)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.Good (y : GR d.n) (g f : d.LF) : Prop :=
  ∀ Ψ, d.IsAwayW w Ψ → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w g Ψ
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.OkY (y : GR d.n) : Prop := ∀ f, IsSw f → ∃ g, IsSw g ∧ R.Good w y g f
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.Lc (y : GR d.n) (f : d.LF) : d.LF := if h : ∃ g, IsSw g ∧ R.Good w y g f then h.choose else 0
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isLocOp_of_ok (h : ∀ y, R.OkY w y) : R.IsLocOp w (R.Lc w) := by
  intro y f hf
  have hx := h y f hf
  have e : R.Lc w y f = hx.choose := by simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.Lc, dif_pos hx]
  rw [e]
  exact ⟨hx.choose_spec.1, fun Ψ hΨ Φ hΦ hT => hx.choose_spec.2 Ψ hΨ Φ hΦ hT⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_of_step {y : GR d.n} {A : d.LF → d.LF} (h : R.StepOK w (R.ι w y) A id) : R.OkY w y := by
  intro f hf
  exact ⟨A f, h.1 f hf, fun Ψ hΨ Φ hΦ hT => (h.2 Ψ hΨ).2 f hf Φ hΦ hT⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.step_comp (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {x x' : d.G} {A A' : d.LF → d.LF}
    {B B' : d.MF → d.MF} (h : R.StepOK w x A B) (h' : R.StepOK w x' A' B') :
    R.StepOK w (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun Ψ hΨ => ⟨(h.2 _ (h'.2 Ψ hΨ).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 Ψ hΨ).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' Ψ) (h'.2 Ψ hΨ).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (hsch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_mul (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {y y' : GR d.n} (h : R.OkY w y)
    (h' : R.OkY w y') : R.OkY w (y * y') := by
  intro f hf
  obtain ⟨g', hg', hG'⟩ := h' f hf
  obtain ⟨g, hg, hG⟩ := h g' hg'
  refine ⟨g, hg, fun Ψ hΨ Φ hΦ hT => ?_⟩
  rw [map_mul, map_mul, Module.End.mul_apply]
  exact hG Ψ hΨ _ (hsch _ Φ hΦ) (hG' Ψ hΨ Φ hΦ hT)
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem inFrame_inv_of_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : inFrame d.b x * N = 1) : inFrame d.b x⁻¹ = N := by
  calc inFrame d.b x⁻¹ = inFrame d.b x⁻¹ * (inFrame d.b x * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_one_k, Matrix.one_mul]
theorem adDecomp_k : _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k := by
  intro F E _ _ _ _ _ σ d ε w hw e he x hx
  obtain ⟨ε₀, hε₀⟩ := d.ok.frame.1
  have hcm : IsCMExt F E σ := d.ok.good.cm
  set X := inFrame d.b x with hXdef
  set A := X.toBlocks₁₁ with hA
  set B := X.toBlocks₁₂ with hB
  set C := X.toBlocks₂₁ with hC
  set D := X.toBlocks₂₂ with hD
  have hXb : X = fromBlocks A B C D := (fromBlocks_toBlocks X).symm
  have heA : e • A = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hA, ← smul_toBlocks₁₁, hx, smul_toBlocks₁₁, one_toBlocks₁₁]
  have heB : e • B = 0 := by
    rw [hB, ← smul_toBlocks₁₂, hx, smul_toBlocks₁₂, one_toBlocks₁₂, smul_zero]
  have heC : e • C = 0 := by
    rw [hC, ← smul_toBlocks₂₁, hx, smul_toBlocks₂₁, one_toBlocks₂₁, smul_zero]
  have heD : e • D = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hD, ← smul_toBlocks₂₂, hx, smul_toBlocks₂₂, one_toBlocks₂₂]
  have hε₀2 : (ε₀ : ℤ) * (ε₀ : ℤ) = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  obtain ⟨t, ht, het, hunit⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hcm (ε₀ : ℤ) hε₀2 X (_root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d x) e he heA
  obtain ⟨x₁, hx₁⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM t) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) t).2 ht)
  have hx₁i : inFrame d.b x₁⁻¹ = nM (-t) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₁ _ (by
    rw [hx₁, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  set A' := A - t * C with hA'
  set B' := B - t * D with hB'
  have hY : inFrame d.b (x₁⁻¹ * x) = fromBlocks A' B' C D := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hx₁i, ← hXdef, hXb, nM, fromBlocks_multiply]
    simp [hA', hB', sub_eq_add_neg]
  have h11 := upper_block_rank_one_update (cA σ).toRingHom (ε₀ : ℤ) _ (_root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ (x₁⁻¹ * x))
  rw [hY, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁] at h11
  have hA'u : IsUnit A'.det := hunit
  set c₀ := C * A'⁻¹ with hc₀
  set c := ((ε : ℤ) : AE F E) • c₀ with hcdef
  have hcc := cond_c (cA σ).toRingHom (ε₀ : ℤ) A' C hA'u hε₀2 h11 (ε : ℤ)
  obtain ⟨x₂, hx₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM c) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) c).2 hcc)
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hwi : inFrame d.b w⁻¹ = fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d w _ (by
    rw [hw, fromBlocks_multiply]; simp [smul_smul, hεε, fromBlocks_one])
  have hL : inFrame d.b (w * x₂ * w⁻¹) = fromBlocks 1 0 c₀ 1 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hw, hx₂, hwi, nM, fromBlocks_multiply, fromBlocks_multiply]
    simp [hcdef, smul_smul, hεε]
  have hLi : inFrame d.b (w * x₂ * w⁻¹)⁻¹ = fromBlocks 1 0 (-c₀) 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d _ _ (by
    rw [hL, fromBlocks_multiply]; simp [fromBlocks_one])
  have hcA : c₀ * A' = C := by rw [hc₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA'u, Matrix.mul_one]
  have hZ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x)) = fromBlocks A' B' 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hLi, hY, fromBlocks_multiply]
    simp [hcA, sub_eq_add_neg, add_comm]
  obtain ⟨hz1, hz2⟩ := blkUpper (cA σ).toRingHom (ε₀ : ℤ) A' B' (D - c₀ * B') (by rw [← hZ]; exact _root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ _)
  have hbb := cond_b (cA σ).toRingHom (ε₀ : ℤ) (cA_cA hcm) A' B' (D - c₀ * B') hA'u hz1 hz2
  obtain ⟨x₄, hx₄⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM (A'⁻¹ * B')) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) _).2 hbb)
  have hx₄i : inFrame d.b x₄⁻¹ = nM (-(A'⁻¹ * B')) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₄ _ (by
    rw [hx₄, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  have hx₃ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹) = fromBlocks A' 0 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hZ, hx₄i, nM, fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv_cancel_left _ _ hA'u]
  have hdet := _root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹)
  rw [hx₃, det_fromBlocks_zero₁₂] at hdet
  have hDu : IsUnit (D - c₀ * B').det := isUnit_of_mul_isUnit_right hdet
  have heB' : e • B' = 0 := by rw [hB', smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, heB, sub_zero]
  refine ⟨x₁, x₂, (w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹, x₄, t, c, A'⁻¹ * B', nonsingInvUnit A' hA'u,
    nonsingInvUnit (D - c₀ * B') hDu, by group, hx₁, hx₂, hx₃, hx₄, het, ?_, ?_, ?_, ?_⟩
  · rw [hcdef, smul_comm, hc₀, ← Matrix.smul_mul, heC, Matrix.zero_mul, smul_zero]
  · rw [← Matrix.mul_smul, heB', Matrix.mul_zero]
  · change e • (A - t * C) = _
    rw [smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, sub_zero, heA]
  · change e • (D - c₀ * B') = _
    rw [smul_sub, ← Matrix.mul_smul, heB', Matrix.mul_zero, sub_zero, heD]
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem epsEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  refine ⟨ε, hε, ?_⟩
  have hss : ∀ x, σ (σ x) = x := PositivityTheory.ThKG.Tow.Levi.sig_sig d.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  have key : ∀ c : E, (∀ i j, σ (d.Y.J j i) = c * d.Y.J i j) → ((ε : ℤ) : E) = c := fun c hc => by
    have e := congrFun (congrFun (conjT_frame c d.Y.J hc hss d.b.1) (Sum.inl i)) (Sum.inr i)
    rw [hε] at e
    simpa [Matrix.fromBlocks] using e
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · refine Or.inl ⟨hA, ?_⟩
    have e := key (-1) fun i j => by rw [hY, neg_one_mul]
    have e' : ((ε : ℤ) : E) = ((-1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
  · refine Or.inr ⟨hA, ?_⟩
    have e := key 1 fun i j => by rw [hY, one_mul]
    have e' : ((ε : ℤ) : E) = ((1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
theorem frEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    exact ⟨fr, sg, fun w => by rw [one_smul, hfr w]⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    refine ⟨fr, sg, fun w => ?_⟩
    rw [← hfr w, Matrix.mul_smul, Matrix.smul_mul]
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end
