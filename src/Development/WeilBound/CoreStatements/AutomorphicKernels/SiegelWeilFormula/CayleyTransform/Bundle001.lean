module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Matrix
open PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd

variable {n : ℕ}

def Qc (n : ℕ) (ε : ℤˣ) : M2 n := Matrix.fromBlocks 0 1 (((ε : ℤ) : ℂ) • 1) 0

theorem mapStar_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) : (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem mapStar_one {ι : Type} [DecidableEq ι] : (1 : Matrix ι ι ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem dZ_mul (a b : ℂ) : dZ n a * dZ n b = dZ n (a * b) := by
  simp [dZ, Matrix.fromBlocks_multiply, smul_smul, mul_comm]

theorem dZ_one : dZ n 1 = 1 := by
  simp [dZ, Matrix.fromBlocks_one]

theorem dZ_transpose (a : ℂ) : (dZ n a)ᵀ = dZ n a := by
  simp [dZ, Matrix.fromBlocks_transpose]

theorem dZ_map_star (a : ℂ) : (dZ n a).map star = dZ n (star a) := by
  unfold dZ
  rw [Matrix.fromBlocks_map]
  simp [mapStar_one]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem dZ_inv_mul {ζ : ℂ} (h : ζ ≠ 0) : dZ n ζ⁻¹ * dZ n ζ = 1 := by
  rw [dZ_mul, inv_mul_cancel₀ h, dZ_one]

theorem dZ_mul_inv {ζ : ℂ} (h : ζ ≠ 0) : dZ n ζ * dZ n ζ⁻¹ = 1 := by
  rw [dZ_mul, mul_inv_cancel₀ h, dZ_one]

theorem zeta_ne {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) : ζ ≠ 0 := by
  rcases hζ with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact one_ne_zero
  · exact Complex.I_ne_zero

theorem mid {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    dZ n ζ⁻¹ * Qc n ε * dZ n (star ζ⁻¹) = ζ • JJ n := by
  rcases hζ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, smul_smul, Complex.inv_I]

theorem outer {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    dZ n ζ * (ζ • JJ n) * dZ n (star ζ) = Qc n ε := by
  rcases hζ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  · simp [Qc, JJ, dZ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, smul_smul]

theorem key {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (g : M2 n) :
    (dZ n ζ⁻¹ * g * dZ n ζ)ᵀ * Qc n ε * (dZ n ζ⁻¹ * g * dZ n ζ).map star =
      dZ n ζ * (ζ • (gᵀ * JJ n * g.map star)) * dZ n (star ζ) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, dZ_transpose, dZ_transpose, mapStar_mul, mapStar_mul,
    dZ_map_star, dZ_map_star]
  have e : ζ • (gᵀ * JJ n * g.map star) = gᵀ * (ζ • JJ n) * g.map star := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, ← mid (n := n) hζ]
  simp only [Matrix.mul_assoc]

theorem conj_JJ (g : M2 n) : gᵀ * JJ n * g.map star = JJ n ↔ gᴴ * JJ n * g = JJ n := by
  have key2 : ∀ A : M2 n, (A.map star).map star = A := fun A => by
    ext i j
    simp
  have hJ : (JJ n).map star = JJ n := by
    unfold JJ
    rw [Matrix.fromBlocks_map]
    simp [mapStar_one]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have e : (gᵀ * JJ n * g.map star).map star = gᴴ * JJ n * g := by
    rw [mapStar_mul, mapStar_mul, hJ, key2]
    rfl
  constructor
  · intro h
    rw [← e, h, hJ]
  · intro h
    rw [← e] at h
    rw [← key2 (gᵀ * JJ n * g.map star), h, hJ]

theorem unitary_iff {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (g : M2 n) :
    (dZ n ζ⁻¹ * g * dZ n ζ)ᵀ * Qc n ε * (dZ n ζ⁻¹ * g * dZ n ζ).map star = Qc n ε ↔ InG g := by
  have hz := zeta_ne hζ
  have hs : star ζ ≠ 0 := star_ne_zero.mpr hz
  have canc : ∀ A : M2 n, dZ n ζ⁻¹ * (dZ n ζ * A * dZ n (star ζ)) * dZ n (star ζ)⁻¹ = A := by
    intro A
    simp only [Matrix.mul_assoc, dZ_mul_inv hs, Matrix.mul_one]
    rw [← Matrix.mul_assoc, dZ_inv_mul hz, Matrix.one_mul]
  have hI : InG g ↔ gᵀ * JJ n * g.map star = JJ n := (conj_JJ g).symm
  rw [key hζ, ← outer (n := n) hζ, hI]
  constructor
  · intro h
    have h2 := canc (ζ • (gᵀ * JJ n * g.map star))
    rw [h, canc] at h2
    exact smul_right_injective _ hz h2.symm
  · intro h
    rw [h]

theorem inG_conj {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (Z : M2 n)
    (hZ : Zᵀ * Qc n ε * Z.map star = Qc n ε) : InG (dZ n ζ * Z * dZ n ζ⁻¹) := by
  have hz := zeta_ne hζ
  have e : dZ n ζ⁻¹ * (dZ n ζ * Z * dZ n ζ⁻¹) * dZ n ζ = Z := by
    simp only [Matrix.mul_assoc, dZ_inv_mul hz, Matrix.mul_one]
    rw [← Matrix.mul_assoc, dZ_inv_mul hz, Matrix.one_mul]
  rw [← unitary_iff hζ, e]
  exact hZ

end PositivityTheory.SiegelWeilFormula.Krd

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd

def EpsEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ),
  ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    (d.A.IsHerm σ d.B d.r d.s ∧ ε = -1 ∨ d.A.IsSkew σ d.B d.r d.s ∧ ε = 1)

def FrEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ),
  (d.A.IsHerm σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, (1 : ℂ) • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1) ∧
  (d.A.IsSkew σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, Complex.I • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1)

def IotaEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ),
  ∀ (ε : ℤˣ) (ζ : ℂ), d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 →
    (ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) →
    ∃ ι : InfinitePlace F → (GR d.n →* d.G), (∀ w, Continuous (ι w)) ∧
      (∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ) ∧
      (∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1) ∧
      ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))

theorem rdEx_of (h1 : EpsEx) (h2 : FrEx) (h3 : IotaEx) : RDEx := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε, hs⟩ := h1 F E σ d
  rcases hs with ⟨hA, rfl⟩ | ⟨hA, rfl⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).1 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d (-1) 1 hε (Or.inl ⟨rfl, rfl⟩)
    exact ⟨⟨-1, 1, fr, sg, ι, hε, Or.inl ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).2 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d 1 Complex.I hε (Or.inr ⟨rfl, rfl⟩)
    exact ⟨⟨1, Complex.I, fr, sg, ι, hε, Or.inr ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩

end PositivityTheory.SiegelWeilFormula.Krd

end
end
