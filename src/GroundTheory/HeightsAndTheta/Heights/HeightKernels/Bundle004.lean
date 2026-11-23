module

public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Fourier.FourierTransform
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def thetaSummand {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ)
    (k : Fin g → ℤ) : ℂ :=
  Complex.exp (π * Complex.I *
      ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
    2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (u i : ℂ))

def ThetaSummandNorm.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ) (k : Fin g → ℤ), Y.IsSymm →
    ‖thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ *
        exp (-π * qf Y u₁) = exp (-π * qf Y (intVec k + a + u₁))

def ThetaNormMajorant.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ), Y.PosDef →
    thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁))

def ThetaCharIntegral.Statement : Prop :=
  ∀ (g : ℕ) (m : Fin g → ℤ),
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, torusChar m u = if m = 0 then 1 else 0

def ThetaCubeParseval.Statement : Prop :=
  ∀ (g : ℕ) (c : (Fin g → ℤ) → ℂ), Summable (fun k => ‖c k‖) →
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ‖∑' k, c k * torusChar k u‖ ^ 2 = ∑' k, ‖c k‖ ^ 2

def ThetaInnerMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ : Fin g → ℝ), Y.PosDef →
    ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
      ∑' k : Fin g → ℤ, exp (-(2 * π) * qf Y (intVec k + a + u₁))

def ThetaMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ), Y.PosDef →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ))

def ThetaFirstCoordSplit.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ), Y.PosDef → 0 < ρ →
    Y⁻¹ 0 0 = ρ ^ 2 →
    ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁)))

def ThetaConstants.Statement : Prop :=
  ∀ C₃ : ℝ, 0 < C₃ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (ρ d : ℝ), 1 ≤ g → 0 < ρ → 0 < d → ρ ^ 2 ≤ 2 * g → d⁻¹ ≤ ρ ^ 2 * (2 * g) ^ (g - 1) →
      (C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g ≤
        ((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) * exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform

noncomputable section

def gaussLattice {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin g)) :=
  Submodule.span ℤ (Set.range fun i : Fin g => WithLp.toLp 2 (B *ᵥ Pi.single i 1))

def gaussShellConst (n : ℕ) : ℝ :=
  3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π))

def GaussSqrt.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∃ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ * B = Y

def GaussLatticeIsLattice.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    DiscreteTopology (gaussLattice B) ∧ ∀ [DiscreteTopology (gaussLattice B)], IsZLattice ℝ (gaussLattice B)

def GaussLatticeCovolume.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ZLattice.covolume (gaussLattice B) = |B.det|

def GaussLatticeCoords.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    (∀ k : Fin g → ℤ, WithLp.toLp 2 (B *ᵥ intVec k) ∈ gaussLattice B) ∧
    (∀ x ∈ gaussLattice B, ∃ k : Fin g → ℤ, x = WithLp.toLp 2 (B *ᵥ intVec k)) ∧
    Function.Injective fun k : Fin g → ℤ => B *ᵥ intVec k

def GaussFourierSelf.Statement : Prop :=
  ∀ (g : ℕ) (w : EuclideanSpace ℝ (Fin g)),
    𝓕 (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) w =
      ((Real.exp (-π * ‖w‖ ^ 2) : ℝ) : ℂ)

def GaussPoissonBound.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 → ∀ a : Fin g → ℝ,
    Summable (fun k : Fin g → ℤ =>
      Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))) ∧
    Summable (fun μ : GroundTheory.Global.dualLattice (gaussLattice B) =>
      Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)) ∧
    ∑' k : Fin g → ℤ, Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a)))) ≤
      |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
        Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussDualMin.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ∀ μ ∈ GroundTheory.Global.dualLattice (gaussLattice B), μ ≠ 0 →
      ∃ l : Fin g → ℤ, l ≠ 0 ∧ qf (Bᵀ * B)⁻¹ (intVec l) ≤ ‖μ‖ ^ 2

def GaussDetFactor.Statement : Prop :=
  ∀ (g : ℕ) (Y B : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → Bᵀ * B = (1 / 2 : ℝ) • Y →
    |B.det|⁻¹ = √2 ^ g * Y.det ^ (-(1 / 2 : ℝ))

def GaussPoissonDual.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∃ Λ : Submodule ℤ (EuclideanSpace ℝ (Fin g)), (∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖) ∧
        ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) ≤
          √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussPacking.Statement : Prop :=
  ∀ (n : ℕ) (s : Finset (EuclideanSpace ℝ (Fin n))) (δ r : ℝ), 0 < δ → 0 ≤ r →
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) → (∀ x ∈ s, ‖x‖ ≤ r) →
    (s.card : ℝ) ≤ (1 + 2 * r / δ) ^ n

def GaussTermBound.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
    ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2) ≤
      √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))

def GaussShell.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) → ∀ (F : Finset Λ) (m : ℕ),
      ∑ μ ∈ F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ))

def GaussShellSum.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) →
      Summable (fun μ : Λ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)) ∧
      ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        2 * gaussShellConst n * (1 + 1 / δ) ^ n

def GaussConstant.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → √2 ^ n * (2 * gaussShellConst n) ≤ (72 * Real.exp 4 * n) ^ ((n : ℝ) / 2)

abbrev gaussUnit : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (Pi.single 0 1)

theorem gaussUnit_norm : ‖gaussUnit‖ = 1 := by
  simp [gaussUnit]

theorem mem_gaussLattice_one {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ) ↔ ∃ a : ℤ, a • gaussUnit = x := by
  have h : (Set.range fun i : Fin 1 => WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
      Pi.single i 1)) = {gaussUnit} := by
    rw [Set.range_unique, Matrix.one_mulVec]
    rfl
  rw [gaussLattice, h, Submodule.mem_span_singleton]

theorem gaussLattice_one_min : ∀ v ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ), v ≠ 0 →
    (1 : ℝ) ≤ ‖v‖ := by
  intro v hv hv0
  obtain ⟨a, rfl⟩ := mem_gaussLattice_one.1 hv
  have ha : a ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, gaussUnit_norm, mul_one, Real.norm_eq_abs]
  exact_mod_cast Int.one_le_abs ha

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset
open scoped ComplexOrder

namespace HadamardPSDAux

theorem det_eq_zero_of_diag_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    {i : Fin n} (hi : A i i = 0) : A.det = 0 := by
  have h0 : star (Pi.single i (1 : ℂ)) ⬝ᵥ A *ᵥ Pi.single i 1 = 0 := by
    simpa using hi
  have hcol := (hA.dotProduct_mulVec_zero_iff).mp h0
  refine det_eq_zero_of_column_eq_zero i fun k => ?_
  simpa using congrFun hcol k

theorem le_of_diag_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hpos : ∀ i, 0 < (A i i).re) : ‖A.det‖ ≤ ∏ i, ‖A i i‖ := by
  set d : Fin n → ℝ := fun i => (A i i).re with hd_def
  have hAd : ∀ i, A i i = (d i : ℂ) := by
    intro i
    obtain ⟨-, him⟩ := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
    exact Complex.ext (by simp [d]) (by simp [← him])
  set c : Fin n → ℝ := fun i => (Real.sqrt (d i))⁻¹ with hc_def
  have hc : ∀ i, 0 < c i := fun i => inv_pos.mpr (Real.sqrt_pos.mpr (hpos i))
  have hcd : ∀ i, c i * c i * d i = 1 := by
    intro i
    simp only [c]
    rw [← mul_inv, Real.mul_self_sqrt (hpos i).le, inv_mul_cancel₀ (hpos i).ne']
  obtain ⟨D, hD_def⟩ : ∃ D : Matrix (Fin n) (Fin n) ℂ, D = diagonal fun i => (c i : ℂ) := ⟨_, rfl⟩
  have hD : Dᴴ = D := by simp [hD_def, diagonal_conjTranspose]
  have hB : (D * A * D).PosSemidef := by simpa [hD] using hA.conjTranspose_mul_mul_same D
  have hBdiag : ∀ i, (D * A * D) i i = 1 := by
    intro i
    simp only [hD_def, diagonal_mul, mul_diagonal, hAd]
    exact_mod_cast (by linarith [hcd i] : c i * d i * c i = 1)
  have htr : ∑ i, hB.1.eigenvalues i = n := by
    have h := hB.1.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag_apply, hBdiag] at h
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    simpa using (congrArg Complex.re h).symm
  have hprod : ∏ i, hB.1.eigenvalues i ≤ 1 := by
    calc ∏ i, hB.1.eigenvalues i ≤ ∏ i, Real.exp (hB.1.eigenvalues i - 1) :=
          prod_le_prod₀ (fun i _ => hB.eigenvalues_nonneg i)
            (fun i _ => by linarith [Real.add_one_le_exp (hB.1.eigenvalues i - 1)])
      _ = Real.exp (∑ i, (hB.1.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
      _ = 1 := by simp [sum_sub_distrib, htr]
  have hnormB : ‖(D * A * D).det‖ ≤ 1 := by
    have h1 : (D * A * D).det = ((∏ i, hB.1.eigenvalues i : ℝ) : ℂ) := by
      rw [hB.1.det_eq_prod_eigenvalues]; push_cast; rfl
    rw [h1, Complex.norm_of_nonneg (prod_nonneg fun i _ => hB.eigenvalues_nonneg i)]
    exact hprod
  have hdetB : (D * A * D).det = (((∏ i, c i) ^ 2 : ℝ) : ℂ) * A.det := by
    simp only [det_mul, hD_def, det_diagonal]
    push_cast
    ring
  have key : ‖(D * A * D).det‖ * ∏ i, d i = ‖A.det‖ := by
    rw [hdetB, norm_mul, Complex.norm_of_nonneg (by positivity)]
    calc (∏ i, c i) ^ 2 * ‖A.det‖ * ∏ i, d i = ‖A.det‖ * ∏ i, (c i * c i * d i) := by
          rw [prod_mul_distrib, prod_mul_distrib]; ring
      _ = ‖A.det‖ := by simp [hcd]
  have hnd : ∀ i, ‖A i i‖ = d i := fun i => by rw [hAd i, Complex.norm_of_nonneg (hpos i).le]
  rw [← key, prod_congr rfl fun i _ => hnd i]
  calc ‖(D * A * D).det‖ * ∏ i, d i ≤ 1 * ∏ i, d i :=
        mul_le_mul_of_nonneg_right hnormB (prod_nonneg fun i _ => (hpos i).le)
    _ = ∏ i, d i := one_mul _

end HadamardPSDAux

theorem HadamardPSD.proof : HadamardPSD.Statement := by
  intro n A hA
  by_cases h : ∃ i, A i i = 0
  · obtain ⟨i, hi⟩ := h
    rw [HadamardPSDAux.det_eq_zero_of_diag_eq_zero hA hi, norm_zero]
    exact prod_nonneg fun _ _ => norm_nonneg _
  · push Not at h
    refine HadamardPSDAux.le_of_diag_pos hA fun i => ?_
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))
    rcases hre.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq.symm him.symm) (h i)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset
open scoped ComplexOrder

namespace PlueckerUnitBoundAlt

theorem posSemidef_one_add {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) :
    (1 + Z * Zᴴ).PosSemidef :=
  Matrix.PosSemidef.one.add (Matrix.posSemidef_self_mul_conjTranspose Z)

theorem diag_eq {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, ‖Z a b‖ = 1) (a : Fin j) :
    (1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a = (((1 + m : ℝ)) : ℂ) := by
  have hb : ∀ b, Z a b * Zᴴ b a = 1 := by
    intro b
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      hZ a b]
    norm_num
  rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

end PlueckerUnitBoundAlt


open PlueckerUnitBoundAlt in
theorem PlueckerUnitBound.proof (h : HadamardPSD.Statement) : PlueckerUnitBound.Statement := by
  intro j m Z hZ
  calc ‖(1 + Z * Zᴴ).det‖ ≤ ∏ a, ‖(1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a‖ := h j _ (posSemidef_one_add Z)
    _ = ∏ _a : Fin j, (1 + m : ℝ) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [diag_eq Z hZ a, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ = (1 + m : ℝ) ^ j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset Equiv

namespace CauchyBinetAlt

variable {R : Type*} [CommRing R] {j N : ℕ}

theorem det_mul_eq_sum (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R) :
    (A * B).det = ∑ p : Fin j → Fin N, (∏ i, B (p i) i) * (A.submatrix id p).det := by
  simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [prod_mul_distrib]
  ring

theorem det_submatrix_eq_zero (A : Matrix (Fin j) (Fin N) R) {p : Fin j → Fin N}
    (hp : ¬ Function.Injective p) : (A.submatrix id p).det = 0 := by
  simp only [Function.Injective, not_forall, exists_prop] at hp
  obtain ⟨a, b, hab, hne⟩ := hp
  exact det_zero_of_column_eq hne fun k => by simp [hab]

theorem minor_mul (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) :
    (colsOf A I).det * (rowsOf B I).det =
      ∑ w : Perm (Fin j), (∏ i, B (I.1.orderEmbOfFin I.2 (w i)) i) *
        (A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w)).det := by
  rw [det_apply' (rowsOf B I), mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w) = (colsOf A I).submatrix id w := by
    ext a b
    rfl
  rw [h, det_permute']
  simp only [rowsOf, submatrix_apply, id]
  ring

theorem sum_reindex {M : Type*} [AddCommMonoid M] (g : (Fin j → Fin N) → M)
    (hg : ∀ p, ¬ Function.Injective p → g p = 0) :
    ∑ p, g p = ∑ I : {I : Finset (Fin N) // I.card = j}, ∑ w : Perm (Fin j),
      g (I.1.orderEmbOfFin I.2 ∘ w) := by
  rw [← Finset.sum_filter_of_ne (p := Function.Injective)
    (fun p _ h => by_contra fun hp => h (hg p hp))]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij (fun x _ => x.1.1.orderEmbOfFin x.1.2 ∘ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨I, w⟩ _
    simp only [mem_filter, mem_univ, true_and]
    exact (I.1.orderEmbOfFin I.2).injective.comp w.injective
  · rintro ⟨I, w⟩ _ ⟨J, w'⟩ _ h
    simp only at h
    have key : ∀ (K : {I : Finset (Fin N) // I.card = j}) (v : Perm (Fin j)) (x : Fin N),
        x ∈ K.1 ↔ ∃ a, (K.1.orderEmbOfFin K.2 ∘ v) a = x := by
      intro K v x
      rw [← Finset.mem_coe, ← range_orderEmbOfFin K.1 K.2, Set.mem_range]
      exact ⟨fun ⟨a, ha⟩ => ⟨v.symm a, by simpa using ha⟩, fun ⟨a, ha⟩ => ⟨v a, ha⟩⟩
    have hIJ : I = J := by
      apply Subtype.ext
      ext x
      rw [key I w x, key J w' x, h]
    subst hIJ
    have hw : w = w' := Equiv.ext fun a => (I.1.orderEmbOfFin I.2).injective (congrFun h a)
    rw [hw]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hI : (univ.image p).card = j := by
      rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
    let w0 : Fin j → Fin j := fun a =>
      ((univ.image p).orderIsoOfFin hI).symm ⟨p a, mem_image_of_mem p (mem_univ a)⟩
    have hw0 : Function.Injective w0 := by
      intro a b hab
      exact hp (congrArg Subtype.val (((univ.image p).orderIsoOfFin hI).symm.injective hab))
    refine ⟨(⟨univ.image p, hI⟩, Equiv.ofBijective w0 (Finite.injective_iff_bijective.mp hw0)),
      mem_univ _, ?_⟩
    funext a
    show ((univ.image p).orderEmbOfFin hI) (w0 a) = p a
    rw [← coe_orderIsoOfFin_apply]
    simp only [w0, OrderIso.apply_symm_apply]
  · intro x _
    rfl

end CauchyBinetAlt

theorem CauchyBinet.proof : CauchyBinet.Statement := by
  intro R _ j N A B
  rw [CauchyBinetAlt.det_mul_eq_sum, CauchyBinetAlt.sum_reindex _ (fun p hp => by
    rw [CauchyBinetAlt.det_submatrix_eq_zero A hp, mul_zero])]
  exact Finset.sum_congr rfl fun I _ => (CauchyBinetAlt.minor_mul A B I).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

theorem gramAt_single {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by
  have he : ∀ j : Fin k, embVec σ (Pi.single j 1 : Fin k → K) = Pi.single j 1 := fun j => by
    funext i
    by_cases hij : i = j
    · subst hij; simp [embVec]
    · simp [embVec, hij]
  ext a b
  simp [gramAt, he, mulVec_single, single_dotProduct]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end
