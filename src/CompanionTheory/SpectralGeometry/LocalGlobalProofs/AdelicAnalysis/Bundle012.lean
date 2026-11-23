module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle009
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.fourier_transform_lattice_indicator : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V, fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y = ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset | exact GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset | (intros; apply GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.SL2_bruhat_decompositions_and_w_inv : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | exact GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.theta_function_modularity : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaUD.main | exact GlobalTheory.CompanionTheory.SW.ThetaUD.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaUD.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq (InfinitePlace F)]

theorem det_EM_sq {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) :
    (EM ρ (fun v => b v)).det ^ 2 = (discr F : ℝ) := by
  let B : Module.Basis (InfinitePlace F) ℚ F := b.localizationLocalization ℚ ℤ⁰ F
  have hB : ∀ i, B i = (b i : F) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ ℤ⁰ F b i
  have hd : Algebra.discr ℚ B = (discr F : ℚ) := by
    rw [← NumberField.discr_eq_discr F b]
    exact (Algebra.discr_localizationLocalization ℤ ℤ⁰ F b).trans (by simp)
  have hm : (EM ρ (fun v => b v))ᵀ * EM ρ (fun v => b v) =
      (algebraMap ℚ ℝ).mapMatrix (Algebra.traceMatrix ℚ B) := by
    ext u v
    simp only [Matrix.mul_apply, Matrix.transpose_apply, EM, RingHom.mapMatrix_apply,
      Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, hB]
    simp_rw [← map_mul]
    rw [sum_rho_eq_trace hT hρ]
    simp
  have h2 : (EM ρ (fun v => b v)).det ^ 2 =
      ((EM ρ (fun v => b v))ᵀ * EM ρ (fun v => b v)).det := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  rw [h2, hm, ← RingHom.map_det, ← Algebra.discr_def, hd]
  simp

theorem abs_det_gM {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) :
    |(gM (ι := ι) ρ (fun v => b v) N).det| =
      ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι := by
  have hfr : Module.finrank ℚ F = Fintype.card (InfinitePlace F) :=
    Module.finrank_eq_card_basis (b.localizationLocalization ℚ ℤ⁰ F)
  have hE : |(EM ρ (fun v => b v)).det| = Real.sqrt |(discr F : ℝ)| := by
    rw [← det_EM_sq hT hρ b, abs_of_nonneg (sq_nonneg (EM ρ (fun v => b v)).det), Real.sqrt_sq_eq_abs]
  rw [gM, Matrix.det_smul, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul,
    Fintype.card_prod, abs_mul, abs_pow, abs_pow, hE, hfr, Nat.abs_cast]
  ring

theorem abs_det_gM_all : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F →
    (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ),
    |(gM (ι := ι) ρ (fun v => b v) N).det| =
      ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι :=
  fun _ _ _ _ _ _ _ _ hT hρ b N => abs_det_gM hT hρ b N

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb_apply {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (y : ι → F) (i : ι) (w : InfinitePlace F) :
    (DM B ρ *ᵥ emb ρ y) (i, w) = ρ w ((B *ᵥ y) i) := by
  have h : ρ w ((B *ᵥ y) i) = ∑ j, ρ w (B i j) * ρ w (y j) := by

    simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h]
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type_right, blockDiagonal_apply]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · simp

theorem emb_dotProduct_DM {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (a y : ι → F) :
    emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) = ∑ w, ρ w (a ⬝ᵥ (B *ᵥ y)) := by
  have h : ∀ w, ρ w (a ⬝ᵥ (B *ᵥ y)) = ∑ i, ρ w (a i) * ρ w ((B *ᵥ y) i) := by
    intro w

    simp [dotProduct, map_sum, map_mul]
  simp only [h]
  rw [dotProduct, Fintype.sum_prod_type_right]
  simp only [DM_mulVec_emb_apply, emb]

theorem toA_dotProduct_Bf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (B : Matrix ι ι F) (a y : ι → F) :
    toA a ⬝ᵥ (Bf B *ᵥ toA y) = algebraMap F (A F) (a ⬝ᵥ (B *ᵥ y)) := by

  simp only [dotProduct, mulVec, toA, Bf, map_sum, map_mul, Matrix.map_apply]

theorem chiB_toA_eq_exp (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ)
    (hψ : IsStdChar F ψ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (hQ : QSetup M B ρ P) (a y : ι → F) :
    chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
      ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  rw [chiB, toA_dotProduct_Bf, hψ.2, emb_dotProduct_DM, sum_rho_eq_trace hT hρ]
  norm_cast

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem dotProduct_blockDiagonal_mulVec {R ι W : Type} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (f : W → Matrix ι ι R) (y : ι × W → R) :
    y ⬝ᵥ (blockDiagonal f *ᵥ y) = ∑ w, (fun i => y (i, w)) ⬝ᵥ (f w *ᵥ fun i => y (i, w)) := by
  simp only [dotProduct, mulVec]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single w]
  · simp [blockDiagonal_apply]
  · intro v _ hv
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [blockDiagonal_apply, hv.symm]
  · simp

theorem dotProduct_block_ofReal {ι : Type} [Fintype ι] (a b : ℝ) (C P : Matrix ι ι ℝ)
    (y : ι → ℝ) :
    (fun i => (y i : ℂ)) ⬝ᵥ
        ((Matrix.of fun i j => (a : ℂ) * ((C i j : ℝ) : ℂ) +
          Complex.I * (b : ℂ) * ((P i j : ℝ) : ℂ)) *ᵥ fun i => (y i : ℂ)) =
      (a : ℂ) * ((y ⬝ᵥ (C *ᵥ y) : ℝ) : ℂ) + Complex.I * (b : ℂ) * ((y ⬝ᵥ (P *ᵥ y) : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def ZB {F : Type} [Field F] {ι : Type} {W : Type} (B : Matrix ι ι F) (ρ : W → (F →+* ℝ))
    (P : W → Matrix ι ι ℝ) (τ : W → ℂ) (w : W) : Matrix ι ι ℂ :=
  Matrix.of fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

theorem ZM_eq_blockDiagonal {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) : ZM B ρ P τ = blockDiagonal (ZB B ρ P τ) := rfl

theorem ZM_map_im {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    (ZM B ρ P τ).map Complex.im = blockDiagonal fun w => (τ w).im • P w := by
  rw [ZM_eq_blockDiagonal]
  ext ⟨i, v⟩ ⟨j, u⟩
  by_cases h : v = u
  · subst h
    simp [ZB, blockDiagonal_apply]
  · simp [ZB, blockDiagonal_apply, h]

theorem ZM_symm_posDef_gauss (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) :
    QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) →
      (ZM B ρ P τ).IsSymm ∧ ((ZM B ρ P τ).map Complex.im).PosDef ∧
        ∀ x : ι × InfinitePlace F → ℝ,
          Complex.exp ((Real.pi : ℂ) * Complex.I *
            ((fun i => (x i : ℂ)) ⬝ᵥ (ZM B ρ P τ *ᵥ fun i => (x i : ℂ)))) =
              gauss B ρ P τ (cur x) := by
  rintro ⟨-, -, hB, -, -, hP, -⟩ τ hτ
  have hPs : ∀ w i j, P w j i = P w i j := fun w i j => by
    simpa using (hP w).isHermitian.apply i j
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [Matrix.IsSymm, ZM_eq_blockDiagonal, blockDiagonal_transpose]
    congr 1
    funext w
    ext i j
    simp only [transpose_apply, ZB, Matrix.of_apply]
    rw [hB.apply i j, hPs w i j]
  · rw [ZM_map_im]
    have hq : ∀ w (y : ι → ℝ), y ≠ 0 → 0 < y ⬝ᵥ (P w *ᵥ y) := fun w y hy => by
      simpa using (hP w).dotProduct_mulVec_pos hy
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext ⟨i, v⟩ ⟨j, u⟩
      by_cases h : v = u
      · subst h
        simp [blockDiagonal_apply, hPs v i j]
      · have h' : ¬ u = v := fun e => h e.symm
        simp [blockDiagonal_apply, h, h']
    · obtain ⟨⟨i, w⟩, hiw⟩ := Function.ne_iff.1 hx
      have hstar : star x = x := by
        funext p
        simp
      rw [hstar, dotProduct_blockDiagonal_mulVec]
      have hterm : ∀ v, (fun i => x (i, v)) ⬝ᵥ (((τ v).im • P v) *ᵥ fun i => x (i, v)) =
          (τ v).im * ((fun i => x (i, v)) ⬝ᵥ (P v *ᵥ fun i => x (i, v))) := fun v => by
        simp [smul_mulVec, dotProduct_smul]
      simp only [hterm]
      refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ w, ?_⟩
      · by_cases hy : (fun i => x (i, v)) = 0
        · simp [hy]
        · exact (mul_pos (hτ v) (hq v _ hy)).le
      · refine mul_pos (hτ w) (hq w _ fun h0 => hiw ?_)
        simpa using congrFun h0 i
  · unfold gauss
    congr 1
    rw [ZM_eq_blockDiagonal, dotProduct_blockDiagonal_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := dotProduct_block_ofReal (τ w).re (τ w).im (B.map (ρ w)) (P w) (cur x w)
    simp only [Matrix.map_apply] at h
    have h2 : (fun i => ((x (i, w) : ℝ) : ℂ)) = fun i => ((cur x w i : ℝ) : ℂ) := rfl
    have h3 : ZB B ρ P τ w = Matrix.of fun i j => ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) +
        Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ) := rfl
    rw [h2, h3, h]
    linear_combination ((Real.pi : ℂ) * ((τ w).im : ℂ) * ((cur x w ⬝ᵥ (P w *ᵥ cur x w) : ℝ) : ℂ)) *
      Complex.I_mul_I

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (y : ι → F) : DM B ρ *ᵥ emb ρ y = emb ρ (B *ᵥ y) := by
  funext p
  obtain ⟨i, w⟩ := p
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type, blockDiagonal_apply]
  rw [Finset.sum_comm]

  simp [map_sum, map_mul]

theorem gM_transpose_mulVec {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) (z : ι × InfinitePlace F → ℝ) (i : ι)
    (v : InfinitePlace F) :
    ((gM ρ b N)ᵀ *ᵥ z) (i, v) = (N : ℝ) * ∑ w, ρ w (b v : F) * z (i, w) := by
  simp only [mulVec, dotProduct, gM, transpose_apply, Matrix.smul_apply, kroneckerMap_apply, EM,
    Matrix.one_apply, Fintype.sum_prod_type, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Finset.sum_ite_eq, mul_assoc]

theorem gM_DM_emb_eq_trace : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  intro F _ _ ι _ _ _ M B ρ P hQ b N y
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  funext p
  obtain ⟨i, v⟩ := p
  rw [DM_mulVec_emb, gM_transpose_mulVec]
  have h := sum_rho_eq_trace hT hρ ((b v : F) * (B *ᵥ y) i)
  simp only [emb, ← map_mul]
  rw [h]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Rescale

theorem isFibreFamily_rescale (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y)
    (ι : X → Y) (U : Set V) (B : Set X) (fib : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) (a c : ℝ≥0) (hc : c ≠ 0) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (a • μ) f ι U (c • ν) B (fun b => (a / c) • fib b) := by
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h ⊢
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · rw [Measure.smul_apply, h.1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [h.2.1 φ hφ, lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_comm c, div_mul_cancel₀ a hc]
  · obtain ⟨h1, h2⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨fun b hb => (h1 b hb).smul_measure_nnreal, ?_⟩
    have e : (fun b => ∫ v, φ v ∂((a / c) • fib b)) = fun b => ((a / c : ℝ≥0) : ℝ) • ∫ v, φ v ∂fib b := by
      funext b
      rw [integral_smul_nnreal_measure, NNReal.smul_def]
    rw [e]
    exact h2.const_smul ((a / c : ℝ≥0) : ℝ)

end GlobalTheory.CompanionTheory.SW.Rescale
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.hermitian_unit_form_diagonalizes : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by
  first | exact @GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise | exact GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise | (intros; apply GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.lattice_ball_count_ratio_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type) [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) * ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | exact GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | (intros; apply GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | exact GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.invariant_measure_compact_cover_bound : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | exact GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | (intros; apply GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel <;> assumption)
end
