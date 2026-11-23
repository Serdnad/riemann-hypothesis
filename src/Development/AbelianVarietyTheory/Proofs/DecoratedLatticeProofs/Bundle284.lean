module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilated
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTraceZeroLocalNormMulIntegralUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle269
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle243
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.CartStd

variable {D : D7}

theorem tauE_star_eq (τ : D.what₂.Tau) (x : D.host.E) : tauE D τ (star x) = star (tauE D τ x) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) ℂ) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rfl

theorem stdJ_mul_self (n : ℕ) : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg,
    Matrix.neg_mul, neg_zero]
  rw [blk4, show Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) ℂ) 0 0 (-1) = -1 by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]]
  rw [show ((-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
      -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) from rfl,
    Matrix.submatrix_one_equiv]

theorem stdJ_conjTranspose (n : ℕ) :
    (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ)ᴴ = -blk4 0 1 (-1) 0 := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
    show -((Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm) = (-(Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm from rfl, Matrix.fromBlocks_neg]
  simp

theorem map_Jst (τ : D.what₂.Tau) (n : ℕ) : (Jst D n).map (tauE D τ) = blk4 0 1 (-1) 0 := by
  unfold Jst blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  have h1 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
    rw [← RingHom.mapMatrix_apply, map_neg, map_one]
  simp [h1]

end GlobalTheory.CartStd

namespace GlobalTheory.CartStd

theorem isCartanInv_stdInv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ s : RealMat (dblSp A),
    IsStdInv A μ s → ∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (s τ) := by
  intro D A μ hμ s hs τ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  set f := tauE D τ with hf
  set T := (Tm A μ).map f with hT
  set J : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) ℂ := blk4 0 1 (-1) 0 with hJ
  set z := f μ with hz
  have hstar : Function.Semiconj f star star := fun x => tauE_star_eq τ x
  have hTG : Tᴴ * gramAt D (dblSp A) τ * T = z • J := by
    have h := congrArg (fun M => M.map f) hgram
    simp only [Matrix.map_mul] at h
    rw [Matrix.conjTranspose_map f hstar] at h
    rw [show gramAt D (dblSp A) τ = (dblSp A).gram.map f from rfl, h, hJ, ← map_Jst τ A.rank]
    ext i j
    simp [Matrix.smul_apply, hz, hf]
  have hTdet : IsUnit T.det := by
    rw [hT, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map f
  set U := T⁻¹ with hU
  have hTU : T * U = 1 := Matrix.mul_nonsing_inv T hTdet
  have hUT : U * T = 1 := Matrix.nonsing_inv_mul T hTdet
  have hUhTh : Uᴴ * Tᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hTU, Matrix.conjTranspose_one]

  have hz0 : z ≠ 0 := (map_ne_zero f).2 hμ.1
  have hzc : star z = -z := by rw [hz, ← tauE_star_eq, hμ.2, map_neg]
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hzz : z * z = -(((‖z‖ : ℝ) : ℂ) ^ 2) := by
    have h1 := Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, ← Complex.star_def, hzc] at h1
    push_cast at h1
    linear_combination -h1
  set c := z / ((‖z‖ : ℝ) : ℂ) with hc
  have hcc : c * c = -1 := by
    rw [hc]; field_simp; linear_combination hzz
  have hcstar : star c = -c := by
    rw [hc, star_div₀, hzc, Complex.star_def, Complex.conj_ofReal, neg_div]
  have hzc' : z * c = -((‖z‖ : ℝ) : ℂ) := by
    rw [hc]; field_simp; linear_combination hzz

  set S := c • J with hS
  have hJJ : J * J = -1 := stdJ_mul_self _
  have hSS : S * S = 1 := by
    rw [hS, smul_mul_smul_comm, hcc, hJJ, neg_one_smul, neg_neg]
  have hSh : Sᴴ = S := by
    rw [hS, Matrix.conjTranspose_smul, hJ, stdJ_conjTranspose, hcstar, smul_neg, neg_smul, neg_neg]
  have hsS : s τ = T * S * U := by
    have h := hs τ
    rw [show stdInv A.rank μ τ = S from rfl] at h
    calc s τ = s τ * T * U := by rw [Matrix.mul_assoc, hTU, Matrix.mul_one]
      _ = T * S * U := by rw [h]
  have hG : gramAt D (dblSp A) τ = Uᴴ * (z • J) * U := by
    rw [← hTG]
    calc gramAt D (dblSp A) τ = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * U) := by
          rw [hUhTh, hTU, Matrix.one_mul, Matrix.mul_one]
      _ = Uᴴ * (Tᴴ * gramAt D (dblSp A) τ * T) * U := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsS]
    calc T * S * U * (T * S * U) = T * S * (U * T) * S * U := by simp only [Matrix.mul_assoc]
      _ = T * U := by rw [hUT, Matrix.mul_one, Matrix.mul_assoc T S S, hSS, Matrix.mul_one]
      _ = 1 := hTU
  · rw [hsS, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh]
    have hSJS : S * (z • J) * S = z • J := by
      rw [hS, smul_mul_smul_comm, hJJ, smul_mul_smul_comm, Matrix.neg_mul, Matrix.one_mul,
        show c * z * c = -z by linear_combination z * hcc, neg_smul, smul_neg, neg_neg]
    calc Uᴴ * (S * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U)
        = Uᴴ * (S * (Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
      _ = gramAt D (dblSp A) τ := by rw [hTG, hSJS, hG]
  · have hGs : gramAt D (dblSp A) τ * s τ = Uᴴ * (((‖z‖ : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) * U := by
      rw [hsS]
      calc gramAt D (dblSp A) τ * (T * S * U) = (Uᴴ * Tᴴ) * gramAt D (dblSp A) τ * (T * S * U) := by
            rw [hUhTh, Matrix.one_mul]
        _ = Uᴴ * ((Tᴴ * gramAt D (dblSp A) τ * T) * S) * U := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hTG, hS, smul_mul_smul_comm, hJJ, hzc', neg_smul, smul_neg, neg_neg]
    rw [hGs]
    have hpos : (0 : ℂ) < ((‖z‖ : ℝ) : ℂ) := Complex.zero_lt_real.2 (norm_pos_iff.2 hz0)
    refine (Matrix.PosDef.one.smul hpos).conjTranspose_mul_mul_same ?_
    intro x y hxy
    have h := congrArg T.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hTU] using h

end GlobalTheory.CartStd
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank ∧ IsUnit (Tm A μ).det ∧ (Tm A μ)⁻¹ = (Matrix.fromRows (dblDec A).qX (μ⁻¹ • (dblDec A).qY)).submatrix finSumFinEquiv.symm id := by
  first | exact @GlobalTheory.StdUnn.Tm_gram_inv | exact GlobalTheory.StdUnn.Tm_gram_inv | (intros; apply GlobalTheory.StdUnn.Tm_gram_inv <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledFlatSection_eq_translate_standardSection : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A) (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f → ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) → s0 B A.rank = sZero A B ∧ (∀ (z : ℂ) (g : GA D (dblSp A)), flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z g = npow (absA D (aP A p)) (sZero A B - z) * sect omS (hgtStd A a κ p) Φ z (κ (g * p))) ∧ ∀ g : GA D (dblSp A), (omS (κ (g * p)) Φ).1 = sch ψ A B ν 𝓨 (omh (g, 1) f) := by
  first | exact @GlobalTheory.StdUnn.flat_swSec_eq_sect | exact GlobalTheory.StdUnn.flat_swSec_eq_sect | (intros; apply GlobalTheory.StdUnn.flat_swSec_eq_sect <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_idele_traceZero_norm_adjust_realComponents : ∀ (D : D7) (μ : D.host.E), IsSkew μ → ∀ u₀ : (AE D)ˣ, ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ (∀ v, compFin D.host.F D.host.E v u = compFin D.host.F D.host.E v u₀) ∧ ∀ w, compInf D.host.F D.host.E w (ε * cA D ε) = 4 := by
  first | exact @GlobalTheory.StdUnn.exists_scal_real | exact GlobalTheory.StdUnn.exists_scal_real | (intros; apply GlobalTheory.StdUnn.exists_scal_real <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∃ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ IsCharAF D.host.F (shift ψ lam) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ lam) θ l ∧ ∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖ := by
  first | exact @GlobalTheory.StdUnn.shift_char_realPar | exact GlobalTheory.StdUnn.shift_char_realPar | (intros; apply GlobalTheory.StdUnn.shift_char_realPar <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.standardUnitaryChart_weylElement_rational : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g : GA D (dblSp A), mat (κ g) = blk4 0 1 (-1) 0 → IsWeyl A g ∧ mt (dblSp A) g ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) ∧ mt (dblSp A) g ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX := by
  first | exact @GlobalTheory.StdUnn.chart_weyl | exact GlobalTheory.StdUnn.chart_weyl | (intros; apply GlobalTheory.StdUnn.chart_weyl <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ siegel A ↔ κ g ∈ P D A.rank := by
  first | exact @GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P | exact GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P | (intros; apply GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_polynomial_mul_gaussian_of_annihilated : ∀ (D : D7) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ) (f : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → ℂ), ContDiff ℝ ∞ f → (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annC V l s q.1 q.2 g) f = 0) → ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ z, f z = evalPoly p (fun τ => Matrix.of (z τ)) * gauss V l s (fun τ => Matrix.of (z τ)) := by
  first | exact @GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC | exact GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC | (intros; apply GlobalTheory.StdUnn.exists_poly_mul_gauss_of_annC <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_traceZero_localNorm_mul_integralUnit : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ IntA (ε : AE D) ∧ IntA ((ε⁻¹ : (AE D)ˣ) : AE D) := by
  first | exact @GlobalTheory.StdUnn.SkewNorm.exists_skew_norm_mul_unit | exact GlobalTheory.StdUnn.SkewNorm.exists_skew_norm_mul_unit | (intros; apply GlobalTheory.StdUnn.SkewNorm.exists_skew_norm_mul_unit <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockPolynomialSchwartz_killed_by_longAnnihilation : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ φ ∈ fockA θ V n l s, ∃ N : ℕ, ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ = 0 := by
  first | exact @GlobalTheory.FockAnnKill.fockA_killed_by_annS | exact GlobalTheory.FockAnnKill.fockA_killed_by_annS | (intros; apply GlobalTheory.FockAnnKill.fockA_killed_by_annS <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ZetaNeProof

variable {D : D7}

theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    coefW p.ω m X (p.pt φ) (b * κ) = Lev.levChi s.V s.β s.L κ * coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ, map_smul]
  unfold coefW
  rw [hv, ← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ)
    (hstab : ∀ k ∈ Lev.levG s.V s.β s.L, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

theorem zetaNe_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  intro D hMet hLev hLaw hSupp hRZ
  intro hng c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ hng c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ D.R.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨_, _, hLF3, _, _, hLF6⟩ := hLev c hc k hkm s hs
  obtain ⟨hmOff, _, hAsub, _, mR, hmR, hint⟩ := GlobalTheory.T.pushforward_haar_realPoints_times_level D hLev c hc k hkm s hs
  have hpet := GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate D c hc k hkm s hs ipD ip hip
  have hlaw := (hLaw hng c hc k hk s s' hs hs' p hp φ).1
  have hsupp := hSupp hng c hc k hk s s' hs hs' p hp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet u v b κ hκ]
    have hn : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hLF6 κ hκ]
      norm_num
    simp only [map_mul]
    linear_combination (conj (ip u u) * coefW p.ω m X (p.pt φ) (b : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn

  have hoff : ∀ g ∈ intOff c s \ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L},
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    rw [hsupp g hg hgA, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hLF3 a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.ChainOnto.ZetaNeProof
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBound D := by
  first | exact @GlobalTheory.ChainOnto.parBound_of_rapidDecay | exact GlobalTheory.ChainOnto.parBound_of_rapidDecay | (intros; apply GlobalTheory.ChainOnto.parBound_of_rapidDecay <;> assumption)
end
