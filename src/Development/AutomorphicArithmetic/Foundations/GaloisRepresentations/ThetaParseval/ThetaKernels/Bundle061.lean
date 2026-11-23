module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle046
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle043
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle053
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle006
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle054
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle045
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle003
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.frame_diag (y : GR d.n) (A D : Matrix (Fin d.n) (Fin d.n) ℂ) (hy : mR y = Matrix.fromBlocks A 0 0 D) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (inFrame d.b (R.ι w y)).toBlocks₁₁ 0 0 (inFrame d.b (R.ι w y)).toBlocks₂₂ ∧
    d.cw w (inFrame d.b (R.ι w y)).toBlocks₁₁ = A ∧ d.cw w (inFrame d.b (R.ι w y)).toBlocks₂₂ = D ∧
    (∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)).toBlocks₁₁ = 1 ∧ d.cw w' (inFrame d.b (R.ι w y)).toBlocks₂₂ = 1) ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₁₁ = finOne F • 1 ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₂₂ = finOne F • 1 := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set M := inFrame d.b (R.ι w y) with hM
  have hw : d.cw w M = Matrix.fromBlocks A 0 0 D := by rw [hM, R.cw_iota_pf w y, hy, dZ_conj_diag hζ0]
  have ho : ∀ w', w' ≠ w → d.cw w' M = 1 := fun w' h => R.off_w w w' y h
  have hf : finOne F • M = finOne F • 1 := R.off_f w y
  have o1 := one_blocks (n := d.n) (1 : ℂ)
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  simp only [one_smul] at o1
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
    rw [hf, smul_one_smul]
  have z0 : ∀ w', d.cw w' (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = 0 := fun w' => Matrix.map_zero _ (map_zero _)
  have e12 : M.toBlocks₁₂ = 0 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [z0]
      show (d.cw w' M).toBlocks₁₂ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp
      · rw [ho w' h]; exact o1.2.1
    · show (finOne F • M).toBlocks₁₂ = _
      rw [hf', of.2.1, smul_zero]
  have e21 : M.toBlocks₂₁ = 0 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [z0]
      show (d.cw w' M).toBlocks₂₁ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp
      · rw [ho w' h]; exact o1.2.2.1
    · show (finOne F • M).toBlocks₂₁ = _
      rw [hf', of.2.2.1, smul_zero]
  refine ⟨?_, ?_, ?_, fun w' h => ⟨?_, ?_⟩, ?_, ?_⟩
  · conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [e12, e21]
  · show (d.cw w M).toBlocks₁₁ = _
    rw [hw]; simp
  · show (d.cw w M).toBlocks₂₂ = _
    rw [hw]; simp
  · show (d.cw w' M).toBlocks₁₁ = _
    rw [ho w' h]; exact o1.1
  · show (d.cw w' M).toBlocks₂₂ = _
    rw [ho w' h]; exact o1.2.2.2
  · show (finOne F • M).toBlocks₁₁ = _
    rw [hf', of.1, smul_one_smul]
  · show (finOne F • M).toBlocks₂₂ = _
    rw [hf', of.2.2.2, smul_one_smul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ c : ℂ, c ≠ 0 ∧ R.StepOK w (R.ι w y) (fun f u => c * f (Matrix.of u * a)) id := by
  intro y a ha hy
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ := by
    have h1 : mR y * mR y⁻¹ = 1 := by
      show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1
      rw [mul_inv_cancel]; rfl
    have h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1 := by
      rw [hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]
    calc mR y⁻¹ = (Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y) * mR y⁻¹ := by rw [h2, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨hM, -, -, -, -, -⟩ := R.frame_diag w y a (aᴴ)⁻¹ hy
  obtain ⟨hM', -, hD', hO', -, hF'⟩ := R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi
  set M := inFrame d.b (R.ι w y) with hMdef
  set M' := inFrame d.b (R.ι w y⁻¹) with hM'def
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]
  have hMM' : M' * M = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]
  have bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)},
      P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ →
      P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1 := by
    intro P Q hP hQ hPQ
    rw [hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hPQ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.mp hPQ
    exact ⟨h1, h4⟩
  obtain ⟨t1, u1⟩ := bl hM hM' hMM
  obtain ⟨t2, u2⟩ := bl hM' hM hMM'
  let t : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩
  let u : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩
  have hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1 := hM
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  refine ⟨c, ?_, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · rw [hc]
    refine mul_ne_zero (Circle.coe_ne_zero _) ?_
    rw [Complex.ofReal_ne_zero]
    exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne _).symm) _).ne'
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ
    exact ⟨ψ, hψ⟩
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]
    have hui : (u⁻¹).1 = M'.toBlocks₂₂ := rfl
    rw [hui]
    set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ
    have hZo : ∀ w', w' ≠ w → d.cw w' Z = 0 := by
      intro w' h
      rw [hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by
        rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]; exact Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,
        Matrix.mul_one, sub_self]
    have hZf : finOne F • Z = 0 := by
      rw [hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one, sub_self]
    have hX : X * (M'.toBlocks₂₂)ᵀ = X + Z := by rw [hZ]; abel
    have hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a := by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
      rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, hD', ← Matrix.mul_assoc, mapStar_mulR]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    rw [hloc, hX, hΨ X Z hZo hZf, hc]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem iota_vg_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y))
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) :
    ∃ c : ℂ, d.T (d.om (R.ι w y) Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R (c • g) := by
  obtain ⟨L, hL⟩ := hO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hld, -, hk⟩ := hI F E σ d R w L hL
  have h1 := (hL y _ _root_.PositivityTheory.SiegelWeilFormula.Avac.isSchwartz_fourierProjection_one).2 (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_indep_k R g w) Φ hΦ (hT.trans (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R g w))
  refine ⟨F0 p q e y, ?_⟩
  rw [h1, hk y 1 hy, hld.kvac y hy, _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R _ w]
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.Avac.fP_smul_one_k]
  ring
theorem dZ_conjT_k {ζ : ℂ} : (dZ d.n ζ)ᴴ = dZ d.n (star ζ) := by
  simp [dZ, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul]
theorem star_zeta_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : star R.ζ = R.ζ⁻¹ := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
theorem kdec_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G)
    (hk : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) :
    ∃ y : GR d.n, InK (mR y) ∧ d.cw w (inFrame d.b (R.ι w y)) = d.cw w (inFrame d.b k) := by
  have hζ0 := Krd.zeta_ne R.hζ
  obtain ⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b k) := ⟨_, rfl⟩
  have hY := Krd.inG_conj R.hζ M (hM ▸ _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_w_k d R w k)
  have hMM : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (hM ▸ hk)
  refine ⟨mkGR _ hY, ⟨hY, ?_⟩, ?_⟩
  · show (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)ᴴ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) = 1
    have hA : (dZ d.n R.ζ)ᴴ = dZ d.n R.ζ⁻¹ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k]
    have hB : (dZ d.n R.ζ⁻¹)ᴴ = dZ d.n R.ζ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, star_inv₀, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k, inv_inv]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB]
    calc dZ d.n R.ζ * (Mᴴ * dZ d.n R.ζ⁻¹) * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)
        = dZ d.n R.ζ * (Mᴴ * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * M) * dZ d.n R.ζ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, hMM, Matrix.mul_one, Krd.dZ_mul_inv hζ0]
  · rw [← hM]
    have h := R.at_w w (mkGR _ hY)
    calc d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))
        = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))) := by
          rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
      _ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]; rfl
      _ = M := by
          simp only [Matrix.mul_assoc]
          rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
theorem cw_inv_iota_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (k : d.G) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b (R.ι w y)⁻¹) * d.cw w' (inFrame d.b k) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k]
theorem peel_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : Finset (InfinitePlace F)) :
    ∀ k : d.G, (∀ w ∈ S, d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) →
      (∀ w ∉ S, d.cw w (inFrame d.b k) = 1) → ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∀ Φ ∈ d.sch,
        d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g → ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _ h1 g hg Φ hΦ hT
    obtain ⟨g', hg', H⟩ := hA F E σ d k (fun w => h1 w (Finset.notMem_empty w)) g hg
    exact ⟨g', hg', H _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_indep_k R) Φ hΦ hT⟩
  | insert w S hw ih =>
    intro k h0 h1 g hg Φ hΦ hT
    obtain ⟨y, hy, hyw⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.kdec_k R w k (h0 w (Finset.mem_insert_self w S))
    have hinv : ∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)⁻¹) = 1 := fun w' h => by
      rw [← map_inv]; exact R.off_w w w' y⁻¹ h
    have e1 : d.cw w (inFrame d.b (R.ι w y)⁻¹) * d.cw w (inFrame d.b (R.ι w y)) = 1 := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_one_k]
    have hkw : d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, ← hyw, e1]
    have hkw' : ∀ w', w' ≠ w → d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b k) := fun w' h => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, hinv w' h, Matrix.one_mul]
    obtain ⟨g₁, hg₁, e₁⟩ := ih ((R.ι w y)⁻¹ * k)
      (fun w' h => by
        rw [hkw' w' (fun e => hw (e ▸ h))]
        exact h0 w' (Finset.mem_insert_of_mem h))
      (fun w' h => by
        by_cases e : w' = w
        · rw [e, hkw]
        · rw [hkw' w' e]
          exact h1 w' fun h' => (Finset.mem_insert.1 h').elim e h)
      g hg Φ hΦ hT
    obtain ⟨c, e₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.iota_vg_k hO hI R w y hy (d.ok.dbl.weil.2.1.pres _ Φ hΦ) e₁
    refine ⟨c • g₁, Submodule.smul_mem _ c hg₁, ?_⟩
    rw [show k = R.ι w y * ((R.ι w y)⁻¹ * k) from (mul_inv_cancel_left _ _).symm, map_mul, Module.End.mul_apply]
    exact e₂
theorem vg_K'_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g)
    {k : d.G} (hk : k ∈ d.K) : ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' :=
  _root_.PositivityTheory.SiegelWeilFormula.Avac.peel_k hO hI hA R Finset.univ k (fun w _ => ((d.ok.stdK k).1 hk).1 w) (fun w h => absurd (Finset.mem_univ w) h) g hg Φ hΦ hT
theorem vac_K'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac := by
  let S' : Submodule ℂ d.Fn :=
    { carrier := {Φ | Φ ∈ d.sch ∧ ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac}
      zero_mem' := ⟨zero_mem _, fun k _ => by
        rw [map_zero]
        have : d.T 0 = 0 := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_zero
        rw [this]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun k hk => by
        rw [map_add (f := _)]
        have : d.T (d.om k a + d.om k b) = d.T (d.om k a) + d.T (d.om k b) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_add _ _
        rw [this]; exact add_mem (ha.2 k hk) (hb.2 k hk)⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun k hk => by
        rw [map_smul]
        have : d.T (c • d.om k a) = c • d.T (d.om k a) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_smul _ _
        rw [this]; exact Submodule.smul_mem _ c (ha.2 k hk)⟩ }
  have hle : R.vac ≤ S'.map (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    have hm : _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g ∈ d.schM := (hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg))
    obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ hm
    refine ⟨Φ, ⟨hΦ, fun k hk => ?_⟩, e⟩
    obtain ⟨g', hg', e'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_K'_k hO hI hA R hg hΦ e hk
    rw [e']; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg'
  intro Φ hΦ hv k hk
  obtain ⟨Φ', hΦ', e⟩ := hle hv
  have : Φ' = Φ := _root_.PositivityTheory.SiegelWeilFormula.Avac.T_inj_k hT.1 hΦ'.1 hΦ e
  rw [← this]
  exact hΦ'.2 k hk
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rel_aniso_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (hη : η ≠ 0) (y : Fin d.m → E)
    (hy : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = 0) : y = 0 := by
  by_contra hy0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (d.B.emb w).1
  have hτ : ∀ x, τ (σ x) = star (τ x) := d.ok.good.cm.2.2.2 τ
  let z : Fin d.m → ℂ := fun i => τ (y i)
  have hz : z ≠ 0 := by
    intro h
    apply hy0
    funext i
    apply τ.injective
    simpa [z] using congrFun h i
  have key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z) := by

    simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [z]
    rw [show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]
    ring
  rw [hy, map_zero] at key
  have hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact rel_definite _ (hA.sig w) d.ok.aniso z hz
    · have h1 := rel_definite _ (hA.sig w) d.ok.aniso z hz
      intro h0
      apply h1
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      change Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0
      rw [h0, smul_zero]
  have hτη : τ η ≠ 0 := (map_ne_zero τ).mpr hη
  exact (mul_ne_zero hτη hQ) key.symm
theorem unipotentParam_rational_matrix (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) : ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ := by
  obtain ⟨T, hT⟩ := T
  induction hT using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by ext i j; simp [incM]⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, ?_⟩
    change x.1 + y.1 = _
    rw [hX, hY]
    ext i j
    simp [incM]
  | neg x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨-X, ?_⟩
    change -x.1 = _
    rw [hX]
    ext i j
    simp [incM]
def relH_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  -(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹ • β.1ᵀ)
theorem relH_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n := by
  intro a b
  have hn := congrFun (congrFun (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε β) a) b
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hn
  have he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹) := by
    rw [map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]
  have hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by
    intro x
    simp [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]
  linear_combination (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn
theorem relH_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (hη : η ≠ 0) (β : nA σ d.Y d.b) :
    β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * (_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β)ᵀ) := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hη, map_one]
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]
  rw [mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]
theorem rel_Td_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (T : nF σ d.Y d.b) (hT : IsND T) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (h0 : T.1.1 = incM F T₀) : (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0 := by
  have hn := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε T.1
  rw [h0, rel_cA_incM] at hn
  have hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0 := by
    have e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 := by
      ext i j
      simp [incM]
    rw [e0, ← hn]
    ext i j
    simp [incM]
  have hz := rel_incM_injective hn'
  refine ⟨fun a b => ?_, ?_⟩
  · have he := congrFun (congrFun hz a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    simp only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_mul, map_neg, map_ofNat, hση]
    linear_combination (2 * η) * he
  · have hdet : T₀.det ≠ 0 := by
      intro h
      apply hT
      show (T.1.1).det = 0
      rw [h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    simp only [Td, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet
theorem relAlg_pf_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelAlg_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨η, hη, hση, hherm⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_eta_k d ε hε
  refine ⟨η, fun β => ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β, _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_mem_k d ε hε η hη hση β⟩, hη, hherm, fun β => _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_eq_k d η hη β,
    fun y hy => _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_aniso_k d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hherm j i
  · intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_aniso_k d η hη y
    have h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = ∑ i, σ (y i) * (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η *ᵥ y) i := by
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rfl
    rw [h2, hy]
    simp
  · obtain ⟨T₀, h0⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.unipotentParam_rational_matrix d T
    exact ⟨T₀, h0, _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_Td_k d ε hε η hη hση T hT T₀ h0⟩
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
