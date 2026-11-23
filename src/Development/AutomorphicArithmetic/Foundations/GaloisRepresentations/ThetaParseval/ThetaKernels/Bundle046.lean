module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ParabolicThetaScalar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle003
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem par_topleft_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ tb : GL (Fin d.n) E, (inFrame d.b p).toBlocks₁₁ = incM F (tb⁻¹).1 * t.1 * incM F tb.1 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  refine ⟨tb, ?_⟩
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hp' : mat2 p * DC = DC * t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M * E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p * E1 = E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 * mat2 p * incM F d.b.1 := rfl
    calc inFrame d.b p * E1 = incM F (d.b⁻¹).1 * (mat2 p * (incM F d.b.1 * E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((mat2 p * DC) * incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((DC * t.1) * incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inl i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₁₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq] using this
theorem inFrame_form_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (y : d.G) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (∃ ε : ℤˣ, C' = ((ε : ℤ) : AE F E) • 1) ∧
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (inFrame d.b y).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨((ε : ℤ) : AE F E) • 1, ⟨ε, rfl⟩, ?_⟩
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hM
  rw [← hF]
  exact this
theorem levi_tu_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1) :
    t.1ᵀ * u.1.map (cA σ) = 1 := by
  obtain ⟨C', -, h⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d x
  rw [hx] at h
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h
  exact h.2.1
theorem frame_iwa_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : d.G) : ∃ (D : GL (Fin d.n) (AE F E)) (k : d.G), k ∈ d.K ∧
    d.a g = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ)⁻¹ ∧
    (inFrame d.b g).toBlocks₂₁ = D.1 * (inFrame d.b k).toBlocks₂₁ ∧
    (inFrame d.b g).toBlocks₂₂ = D.1 * (inFrame d.b k).toBlocks₂₂ := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t' hp
  obtain ⟨tb, htl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.par_topleft_k d p t' hp
  set A := (inFrame d.b p).toBlocks₁₁ with hA
  set B := (inFrame d.b p).toBlocks₁₂ with hB
  set D₀ := (inFrame d.b p).toBlocks₂₂ with hD₀
  have hPb : inFrame d.b p = Matrix.fromBlocks A B 0 D₀ := by rw [← h21, Matrix.fromBlocks_toBlocks]
  obtain ⟨C', ⟨ε, hC'⟩, hform⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d p
  rw [hPb, hC'] at hform
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at hform
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hDA : D₀ᵀ * A.map (cA σ) = 1 := by
    have h3 := hform.2.2.1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h3
    have := congrArg (fun M => ((ε : ℤ) : AE F E) • M) h3
    simpa [smul_smul, hεε] using this
  have hdet : D₀.det * cA σ A.det = 1 := by
    have := congrArg Matrix.det hDA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      show (A.map (cA σ)).det = cA σ A.det from (AlgHom.map_det (cA σ) A).symm] at this
    exact this
  have hDu : IsUnit D₀ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, hdet⟩)
  refine ⟨hDu.unit, k, hk, ?_, ?_, ?_⟩
  · rw [d.ok.hgt.val p t' hp k hk]
    have hAt : A.det = (Matrix.GeneralLinearGroup.det t').1 := by
      rw [htl, Matrix.det_mul, Matrix.det_mul]
      have hinv : (incM F (tb⁻¹).1).det * (incM F tb.1).det = 1 := by
        rw [← Matrix.det_mul]
        have e : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
          simp only [incM, ← Matrix.map_mul, Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        rw [e, Matrix.det_one]
      simp only [Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination (t'.1.det) * hinv
    have hU : Matrix.GeneralLinearGroup.det hDu.unit *
        GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det t') = 1 := by
      ext
      simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec,
        GlobalTheory.Doubling.conjUnit, Units.coe_map]
      change D₀.det * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ t'.1.det = 1
      rw [sigR_eq_cA, ← Matrix.GeneralLinearGroup.val_det_apply, ← hAt]
      exact hdet
    have := congrArg (GlobalTheory.Doubling.absE F E) hU
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at this
    have hpos : (0 : ℝ≥0) < GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit) := by
      rcases eq_or_ne (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit)) 0 with h | h
      · rw [h, zero_mul] at this; exact absurd this zero_ne_one
      · exact pos_iff_ne_zero.2 h
    rw [eq_inv_of_mul_eq_one_right this, NNReal.coe_inv]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
theorem bottom_rows_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1)
    (nb : nA σ d.Y d.b → d.G) (hnb : IsNMap d.b nb) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) (β : nA σ d.Y d.b) :
    (inFrame d.b (w * nb β * x)).toBlocks₂₁ = (((ε : ℤ) : AE F E) • t.1) ∧
    (inFrame d.b (w * nb β * x)).toBlocks₂₂ = (((ε : ℤ) : AE F E) • (β.1 * u.1)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hw, hnb β, hx]
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]
  constructor <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_eq,
    Finset.mul_sum, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KWhit.Ht
end
end
end

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
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := by
  apply d.inFrame_inj
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [d.inFrame_mul, d.inFrame_mul, d.inFrame_mul, hW, d.inFrame_one, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_iota_pf (y : GR d.n) : d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  calc d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
        rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
    _ = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by rw [R.at_w w y, Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b w₀) = wM d.n ((ε : ℤ) : ℂ) := by
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [hW]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, wM, Matrix.one_apply] <;> split_ifs <;> simp
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt (x : Matrix (Fin d.n) (Fin d.n) ℂ) (hx : xᴴ = x) : GR d.n :=
  ⟨⟨nU x, nU (-x), by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one],
    by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]⟩,
    by
      show InG (nU x)
      simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hx]⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.nbar_conj_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, x, hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.oppositeUnipotent_weylConj {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ y' : GR d.n, mR y' = nU ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
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
open GlobalTheory.Doubling (absE)
theorem par_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ (n0 m0 : d.G) (A D : GL (Fin d.n) (AE F E)),
      inFrame d.b n0 = Matrix.fromBlocks 1 ((inFrame d.b p).toBlocks₁₂ * (inFrame d.b p).toBlocks₂₂⁻¹) 0 1 ∧
      inFrame d.b m0 = Matrix.fromBlocks A.1 0 0 D.1 ∧ A.1 = (inFrame d.b p).toBlocks₁₁ ∧
      D.1 = (inFrame d.b p).toBlocks₂₂ ∧ p = n0 * m0 := by
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := KWhit.form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := KWhit.block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, hAu.unit, hDu.unit, ?_, ?_, IsUnit.unit_spec hAu, IsUnit.unit_spec hDu,
    (inv_mul_cancel_right p m0).symm⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
theorem q_T'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (i₀ : Fin d.n) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E i₀ (inFrame d.b q) lam) :
    ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → d.T (d.om q Φ) X = c * d.T Φ X := by
  set M := inFrame d.b q with hM
  obtain ⟨n0, m0, A, D, hn, hm, hA, hD, hp⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.par_frame_k d q (isQ_21 hq)
  refine ⟨(d.χ (Matrix.GeneralLinearGroup.det A) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det A) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ), fun Φ hΦ X hX => ?_⟩
  have hD1 : ∀ j k, k ≠ i₀ → D.1 j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k := by
    rw [hD]; exact isQ_22 hq
  have hDu : IsUnit M.toBlocks₂₂.det := by
    rw [← hD]; exact (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  have hDi : ∀ j k, k ≠ i₀ → M.toBlocks₂₂⁻¹ j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k :=
    inv_col (isQ_22 hq) (Matrix.nonsing_inv_mul _ hDu)
  have hβ : ∀ i j, i ≠ i₀ → j ≠ i₀ → (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) i j = 0 := by
    intro i j hi hj
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i₀
    · subst hk; rw [hDi _ _ hj, Matrix.one_apply_ne (Ne.symm hj), mul_zero]
    · rw [isQ_12 hq i k hi hk, zero_mul]
  have hG : ∀ i j, (i = i₀ ∨ j = i₀) → d.gram X X i j = 0 := by
    intro i j hij
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases hij with rfl | rfl
    · rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hX a, zero_mul, zero_mul]
    · rw [hX b, map_zero, mul_zero]
  have htt : d.tt ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
    have : Matrix.trace ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
      simp only [Matrix.trace, Matrix.diag]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h : i = i₀ ∨ j = i₀
      · rw [hG j i (h.symm), mul_zero]
      · push_neg at h
        rw [hβ i j h.1 h.2, zero_mul]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, this, map_zero]
  have hXD : X * (D⁻¹).1ᵀ = X := by
    have h1 : X * D.1ᵀ = X := by
      ext a j
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Matrix.transpose_apply]
        by_cases hj : j = i₀
        · subst hj; rw [hX a, zero_mul]
        · rw [hD1 j j hj, Matrix.one_apply_eq, mul_one]
      · intro k _ hk
        rw [Matrix.transpose_apply]
        by_cases hk0 : k = i₀
        · subst hk0; rw [hX a, zero_mul]
        · rw [hD1 j k hk0, Matrix.one_apply_ne (Ne.symm hk), mul_zero]
      · simp
    calc X * (D⁻¹).1ᵀ = X * D.1ᵀ * (D⁻¹).1ᵀ := by rw [h1]
      _ = X * ((D⁻¹).1 * D.1)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = X := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  have hm0s : d.om m0 Φ ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d m0 hΦ
  rw [hp, map_mul, Module.End.mul_apply, (hT.2.1 F E σ d _ hm0s).1 n0 _ hn X, htt, mul_zero, neg_zero,
    AddChar.map_zero_eq_one, one_mul, (hT.2.1 F E σ d Φ hΦ).2.1 m0 A D hm X, hXD]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem kStd_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.KStd_k := by
  intro F E _ _ _ _ _ σ d n h Y b j hb hj
  have hX : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  intro k
  rw [Subgroup.mem_comap, d.ok.stdK (j k)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ← map_inv, hX]
  refine and_congr (forall_congr' fun w => ?_) (and_congr (int_blk h _) (int_blk h _))
  rw [blk_map _ _ _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), blk_conjTranspose,
    Matrix.conjTranspose_one, blk_mul, Matrix.one_mul, blk_eq_one_iff]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
