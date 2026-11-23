module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle002
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

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def ProjOp : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)],
    ∀ W : Submodule ℂ (PX m n), FiniteDimensional ℂ W → (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) →
      ∃ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν ∧ Continuous κ ∧
        (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) ∧
        ∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y

def TSGen : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (W : Submodule ℂ (PX m n)), FiniteDimensional ℂ W →
        (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) → ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν →
        Continuous κ → (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
        (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
        ∀ (g : G) (y : GR n) (Q : PX m n), Q ∈ W → (∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y') →
          ∫ k, κ k * I 1 (g * ι ((k : GR n) * y)) ∂ν = I Q g

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

def kM {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (a + b)) ((Complex.I / 2) • (a - b)) (-((Complex.I / 2) • (a - b))) ((1 / 2 : ℂ) • (a + b))

def KIso : Prop := ∀ n : ℕ,
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, a ∈ unitaryGroup (Fin n) ℂ → b ∈ unitaryGroup (Fin n) ℂ →
      ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b) ∧
  (∀ a b a' b' : Matrix (Fin n) (Fin n) ℂ, kM a b * kM a' b' = kM (a * a') (b * b')) ∧ kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 ∧
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, u1 (kM a b) = a ∧ u2 (kM a b) = b) ∧
  (∀ a : Matrix (Fin n) (Fin n) ℂ, (kM a a).toBlocks₂₁ = 0) ∧
  ∀ k : GR n, k ∈ KR n → u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
    mR k = kM (u1 (mR k)) (u2 (mR k))

def RepKer : Prop := ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (V : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ V →
    (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ a : H, (fun x => φ (a * x)) ∈ V) →
    ∃ κ : H → ℂ, Continuous κ ∧ (∀ f : H → ℂ, Continuous f → (fun x => ∫ v, κ v * f (x * v) ∂μ) ∈ V) ∧
      ∀ φ ∈ V, ∀ x, ∫ v, κ v * φ (x * v) ∂μ = φ x

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Ac (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def holomorphicSectionExtension (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (h : GR n) (z : ℂ) : ℂ :=
  (mR h).det ^ e * (u1 (mR h * Ac X z)).det ^ (-(p : ℤ)) * (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))

def HelpA : Prop :=
  (∀ (n : ℕ) (X : Fin n → ℝ), ∃ a : ℝ → GR n, ∀ s, IsDil X s (a s)) ∧
  (∀ (n : ℕ) (X : Fin n → ℝ) (s : ℝ) (a a' : GR n), IsDil X s a → IsDil X s a' → a = a') ∧
  (∀ n : ℕ, IsCompact (univ : Set (KR n))) ∧
  (∀ (n : ℕ) (h : GR n), (u1 (mR h)).det ≠ 0 ∧ (u2 (mR h)).det ≠ 0) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) → ∀ (h : GR n) (s : ℝ),
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s)) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)), IsCompact S → ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
    ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧ ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V) ∧
  (∀ (n p q : ℕ) (e : ℤ), Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, k ∈ KR n → F0 p q e k ≠ 0)

def HelpC : Prop :=
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    ∀ (r : ℕ) (s : ℝ), iteratedDeriv r (fun t : ℝ => f t) s = iteratedDeriv r f s) ∧
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    (∀ r : ℕ, iteratedDeriv r f 0 = 0) → ∀ s : ℝ, f s = 0)

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def aZ {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def twistedScalarSection {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) : ℂ := M.det ^ e * f0 p q M

def TSBFacts : Prop :=
  CayleyBlocksInvertible → ∀ (n p q : ℕ) (e : ℤ),
    CompactSpace (KR n) ∧ Continuous (mR : GR n → M2 n) ∧ Continuous (F0 p q e : GR n → ℂ) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ), ∃ a : GR n, IsDil X t a) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ) (a : GR n), IsDil X t a → mR a = aZ X t) ∧
    ∀ (X : Fin n → ℝ) (C : Set (GR n)), IsCompact C → ∃ U : Set ℂ, IsOpen U ∧ (∀ t : ℝ, (t : ℂ) ∈ U) ∧
      ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U) ∧
      ∀ y ∈ C, DifferentiableOn ℂ (fun z => twistedScalarSection p q e (mR y * aZ X z)) U

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def VacOut : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → GoodSig n p q →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∃ (r σ : ℝ) (F : ℂ → G → ℂ), 0 < r ∧ Metric.ball s₀ r ⊆ {z | σ < z.re} ∪ Metric.ball s₀ r ∧
        ContinuousOn (fun y : ℂ × G => F y.1 y.2) (Metric.ball s₀ r ×ˢ univ) ∧
        (∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r)) ∧ (∀ g, F s₀ g = I 1 g) ∧
        (∀ g, GlobalTheory.Cont.HolValueAt
          (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g) s₀ (I 1 g)) ∧
        ∀ g, ∀ z ∈ Metric.ball s₀ r, GlobalTheory.Cont.HolValueAt
          (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z (F z g)

def ThSph : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
        (g : G) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * y)) ∂μ =
          I 1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * y) ∂μ

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw IwaPf

variable {n : ℕ}

theorem detU1 : CayleyBlocksInvertible := by
  intro n y
  have hg : InG (mR y) := y.2
  refine ⟨det_ne (mR y) hg Complex.I (by norm_num [Complex.ext_iff]), ?_⟩
  show (-(Complex.I • toBlocks₂₁ (mR y)) + toBlocks₂₂ (mR y)).det ≠ 0
  rw [← neg_smul]
  exact det_ne (mR y) hg (-Complex.I) (by norm_num [Complex.ext_iff])

theorem rows_blocks (g : M2 n) (h : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have hr := inG_rows g h
  rw [← fromBlocks_toBlocks g] at hr
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] at hr
  have h22 := congrArg Matrix.toBlocks₂₂ hr
  simp at h22
  exact (neg_add_eq_zero.mp h22).symm

def kmat (U1 U2 : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (U1 + U2)) ((Complex.I / 2) • (U1 - U2)) (-((Complex.I / 2) • (U1 - U2)))
    ((1 / 2 : ℂ) • (U1 + U2))

theorem kmat_unit (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) :
    (kmat U1 U2)ᴴ * kmat U1 U2 = 1 := by
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  rw [← fromBlocks_one]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

theorem kmat_inG (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) : InG (kmat U1 U2) := by
  unfold InG JJ
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, neg_neg, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

private theorem mul_inv_mul_proj_of_ker_iff (g : M2 n) (h : InG g) : u1 g * (u1 g)ᴴ = u2 g * (u2 g)ᴴ := by
  have hr := rows_blocks g h
  simp only [u1, u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hr]
  simp only [Complex.star_def, Complex.conj_I]
  module

private theorem proj_mul_mul_proj_of_ker_iff (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (Y : M2 n) :
    toBlocks₂₁ (Y * (kmat U1 U2)ᴴ) =
      (1 / 2 : ℂ) • (((-Complex.I) • u1 Y) * U1ᴴ + (Complex.I • u2 Y) * U2ᴴ) := by
  rw [← fromBlocks_toBlocks Y]
  simp only [u1, u2, kmat, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, conjTranspose_smul, conjTranspose_add, conjTranspose_sub, conjTranspose_neg,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_neg, smul_sub]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

private theorem inv_mul_unitary_of_mul_conjTranspose_eq (a b : Matrix (Fin n) (Fin n) ℂ) (hab : a * aᴴ = b * bᴴ) (h2d : b.det ≠ 0) :
    (b⁻¹ * a) * (b⁻¹ * a)ᴴ = 1 ∧ a * (b⁻¹ * a)ᴴ = b := by
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr h2d
  have hbH : IsUnit bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr h2d)
  have haV : a * (b⁻¹ * a)ᴴ = b := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, hab, Matrix.mul_assoc,
      mul_nonsing_inv _ hbH, Matrix.mul_one]
  refine ⟨?_, haV⟩
  rw [Matrix.mul_assoc, haV, nonsing_inv_mul b hbu]

theorem iwa : Iwa := by
  intro n y
  have hg : InG (mR y) := y.2
  obtain ⟨_, h2d⟩ := detU1 n y
  obtain ⟨hVV, haV⟩ := inv_mul_unitary_of_mul_conjTranspose_eq (u1 (mR y)) (u2 (mR y)) (mul_inv_mul_proj_of_ker_iff (mR y) hg) h2d
  have hVu := mul_eq_one_comm.mp hVV
  have h1' : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * 1 = 1 := by simp
  have hK := kmat_unit _ 1 hVu h1'
  have hK' := mul_eq_one_comm.mp hK
  let kGL : GL (Fin n ⊕ Fin n) ℂ := ⟨kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1, _, hK', hK⟩
  have hkG : kGL ∈ GR n := kmat_inG _ 1 hVu h1'
  let k : GR n := ⟨kGL, hkG⟩
  have hkK : k ∈ KR n := by
    show InK (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)
    exact ⟨kmat_inG _ 1 hVu h1', hK⟩
  refine ⟨y * k⁻¹, k, ?_, hkK, (inv_mul_cancel_right y k).symm⟩
  show toBlocks₂₁ (mR (y * k⁻¹)) = 0
  have hm : mR (y * k⁻¹) = mR y * (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)ᴴ := rfl
  rw [hm, proj_mul_mul_proj_of_ker_iff, Matrix.smul_mul, Matrix.smul_mul, haV, conjTranspose_one, Matrix.mul_one]
  simp

end PositivityTheory.Rg.Sw.AbsSt
end
end
