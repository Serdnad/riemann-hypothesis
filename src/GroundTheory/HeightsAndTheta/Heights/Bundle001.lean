module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix Module

theorem covolume_eq_sqrt_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L = Real.sqrt (gram ℝ fun i ↦ (b i : V)).det := by
  have hcard : Fintype.card ι = finrank ℝ V := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hcard).symm
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, measureReal_def, o.volume_parallelepiped, ENNReal.toReal_one,
    mul_one, gram_eq_conjTranspose_mul o, det_mul, det_conjTranspose, star_trivial,
    ← sq, Real.sqrt_sq_eq_abs, Basis.det_apply]
  congr 2

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)

def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

def SymplecticReduction.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      ρsq ≤ 2 * g ∧
      ∃ P ∈ symplecticGroup (Fin g) ℤ,
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁.det ≤
          ρsq * (2 * g) ^ (g - 1)

def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)

def SiegelCoordinates.Statement : Prop :=
  ∀ g : ℕ,
    (∀ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm → Y.PosDef →
      siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef) ∧
    ∀ G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
      ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
        XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2

def GaussianSum.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) →
    ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g

def periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (↑) + Complex.I • Y.map (↑)

def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (π * Complex.I *
        ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
          (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
      2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def thetaNorm {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ))‖ *
    exp (-π * qf Y u₁)

structure IsReducedImaginaryPart {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) :
    Prop where
  pos : 0 < ρ
  sq_le : ρ ^ 2 ≤ 2 * g
  first : Y⁻¹ 0 0 = ρ ^ 2
  min : ∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)
  det_le : Y⁻¹.det ≤ ρ ^ 2 * (2 * g) ^ (g - 1)

def ThetaBound.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) [NeZero g] (X Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ)
    (a b : Fin g → ℝ), X.IsSymm → Y.PosDef → IsReducedImaginaryPart Y ρ →
    (∀ i, ∃ m : ℤ, a i = m / 2) → (∀ i, ∃ m : ℤ, b i = m / 2) →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) ∧
    ∀ u₁ u₂ : Fin g → ℝ,
      thetaNorm X Y a b u₁ u₂ ≤ ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
        exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2 +
          (g * log (1 + 1 / ρ) + C * g * log (2 * g)))

def finMean {S : Type*} [Fintype S] (f : S → ℝ) : ℝ := (∑ s, f s) / Fintype.card S

def WeakMatrixArithmetic.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) [NeZero g] (S : Type) [Fintype S] [Nonempty S] (ρ : S → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ √(2 * g)) → 0 ≤ Φ →
      finMean (fun s => π / 96 * (ρ s ^ 2)⁻¹ - (g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g))) ≤ Φ →
      finMean (fun s => (ρ s ^ 2)⁻¹) ≤ C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g)) ≤
        C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => posLog (1 / ρ s)) ≤ 1 / 2 * log (1 + finMean (fun s => (ρ s ^ 2)⁻¹))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]

instance : TopologicalSpace (ℙ K V) :=
  TopologicalSpace.coinduced (Projectivization.mk' K) inferInstance

namespace ProjTopology

lemma continuous_mk' : Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_coinduced_rng

lemma isOpen_iff {s : Set (ℙ K V)} :
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) :=
  isOpen_coinduced

lemma continuous_iff {Y : Type*} [TopologicalSpace Y] {g : ℙ K V → Y} :
    Continuous g ↔ Continuous (g ∘ Projectivization.mk' K) :=
  continuous_coinduced_dom

end ProjTopology

instance compactSpace_projectivization_complex (N : ℕ) : CompactSpace (ℙ ℂ (Fin (N + 1) → ℂ)) := by
  have hS : IsCompact (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_sphere 0 1
  have : CompactSpace (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_iff_compactSpace.mp hS
  have hne : ∀ w : Metric.sphere (0 : Fin (N + 1) → ℂ) 1, (w : Fin (N + 1) → ℂ) ≠ 0 := by
    intro w h
    have := w.2
    rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this
    exact zero_ne_one this
  let g : Metric.sphere (0 : Fin (N + 1) → ℂ) 1 → ℙ ℂ (Fin (N + 1) → ℂ) := fun w =>
    Projectivization.mk' ℂ ⟨w.1, hne w⟩
  have hg : Continuous g :=
    ProjTopology.continuous_mk'.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hsurj : Function.Surjective g := by
    intro v
    induction v using Projectivization.ind with
    | h w hw =>
      have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      refine ⟨⟨(‖w‖⁻¹ : ℂ) • w, ?_⟩, ?_⟩
      · rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ hn]
      · change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ w hw
        rw [Projectivization.mk_eq_mk_iff]
        exact ⟨Units.mk0 (‖w‖⁻¹ : ℂ) (inv_ne_zero (by exact_mod_cast hn)), rfl⟩
  refine ⟨?_⟩
  rw [← hsurj.range_eq]
  exact isCompact_range hg

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Real

noncomputable section

def alternant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) : MvPolynomial ι ℚ :=
  (Matrix.of fun i i' : ι => (X i : MvPolynomial ι ℚ) ^ e i').det

def antisym {ι : Type*} [Fintype ι] [DecidableEq ι] (H : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  ∑ w : Equiv.Perm ι, ((Equiv.Perm.sign w : ℤ) : ℚ) • rename w H

def frobDim {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ((∑ a, la a).factorial : ℚ) *
      (∏ a : Fin r, ∏ b : Fin r,
        if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1) /
    ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ)

def FrobeniusRectangleBound.Statement : Prop :=
  ∀ (r s : ℕ) (ν : Fin r → ℕ), Antitone ν →
    frobDim (fun a => s + ν a) ≤
      ((r * s + ∑ a, ν a).choose (∑ a, ν a) : ℚ) * frobDim (fun _ : Fin r => s) * frobDim ν

abbrev RootPoly (f j k : ℕ) : Type := MvPolynomial (Fin f × (Fin j ⊕ Fin k)) ℝ

variable (f j k : ℕ)

def flagDim : ℕ := f * ((j + k) * (j + k - 1) / 2)

def rootPsum (m : ℕ) (τ : Fin f) : RootPoly f j k := ∑ i, X (τ, i) ^ m

def lieClass (m : ℕ) : Fin f × Bool → RootPoly f j k
  | (τ, false) => ∑ a : Fin j, X (τ, Sum.inl a) ^ m
  | (τ, true) => (-1) ^ m * ∑ b : Fin k, X (τ, Sum.inr b) ^ m

def vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) : R :=
  (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det

def fibre : RootPoly f j k :=
  ∏ τ : Fin f, if k ≤ j then
      vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Sum.inl a) : RootPoly f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Sum.inl a) : RootPoly f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Sum.inr b) : RootPoly f j k))

structure IsFlagIntegral (I : RootPoly f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : RootPoly f j k), 1 ≤ m → m ≤ flagDim f j k →
    G.IsHomogeneous (flagDim f j k - m) → I (rootPsum f j k m τ * G) = 0
  ne_zero : ∃ G : RootPoly f j k, G.IsHomogeneous (flagDim f j k) ∧ I G ≠ 0

def IsPowerSumDecomposition (F : RootPoly f j k) (Q : Fin f → ℕ → RootPoly f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (flagDim f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), rootPsum f j k m τ * Q τ m

def restAt (I : RootPoly f j k →ₗ[ℝ] ℝ) (vol : ℝ) (φ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → RootPoly f j k) (p : ℕ) : ℝ :=
  log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ,
    (((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m))

end

end GroundTheory.Heights₂.Heights
end
