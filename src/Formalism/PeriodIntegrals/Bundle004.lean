module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

namespace PI.SwBig

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

def Nset (k r : ℕ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0)}

def bigCell (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if hj : j.val < r then (if i = esI k r ⟨j.val, hj⟩ then c ⟨j.val, hj⟩ else 0)
  else if hj2 : j.val ≤ r + k then
    (if hi : r ≤ i.val ∧ i.val ≤ r + k then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
  else
    (if i.val = 2 * r + k - j.val then (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹ else 0)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def w0B (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := bigCell k r 1 1

def LongWeylElementSquare : Prop := ∀ k r : ℕ, w0B k r * w0B k r = 1

def tv (k r : ℕ) (c : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then c ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - i.val, by have := i.isLt; omega⟩))⁻¹

def tM (k r : ℕ) (c : Fin r → ℂ) : Mat k r := Matrix.diagonal (tv k r c)

def dv (k r : ℕ) (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then x ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 0
  else -star (x ⟨2 * r + k - i.val, by have := i.isLt; omega⟩)

def tD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal (dv k r x)

def Phi (k r : ℕ) (X : Mat k r) (x : Fin r → ℂ) (Z X' : Mat k r) : Mat k r :=
  w0B k r * NormedSpace.exp X * w0B k r * tM k r (1 + x) * NormedSpace.exp Z * NormedSpace.exp (-X')

def LmL (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →ₗ[ℝ] Mat k r where
  toFun p := w0B k r * p.1 * w0B k r + tD k r p.2.1 + p.2.2.1 - p.2.2.2
  map_add' p q := by
    have : tD k r (p.2.1 + q.2.1) = tD k r p.2.1 + tD k r q.2.1 := by
      unfold tD; rw [Matrix.diagonal_add]; congr 1; funext i; unfold dv
      split_ifs <;> simp [star_add] <;> ring
    simp only [Prod.fst_add, Prod.snd_add, this, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c p := by
    have : tD k r (c • p.2.1) = c • tD k r p.2.1 := by
      have hd : ∀ i, dv k r (c • p.2.1) i = (c : ℂ) * dv k r p.2.1 i := by
        intro i; unfold dv; split_ifs <;> simp [Complex.real_smul]
      unfold tD; ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, hd]
      split_ifs <;> simp [Complex.real_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, this, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add,
      smul_sub]

def Lm (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LmL k r)

def GaussUniq : Prop := ∀ (k r : ℕ) (n₁ n₂ m₁ m₂ u₁ u₂ : Mat k r) (c₁ c₂ : Fin r → ℂ),
  n₁ ∈ Nset k r → n₂ ∈ Nset k r → m₁ ∈ UWb k r → m₂ ∈ UWb k r →
  u₁ ∈ Nset k r → u₂ ∈ Nset k r → (∀ a, c₂ a ≠ 0) →
  n₁ * bigCell k r c₁ 1 * m₁ * u₁⁻¹ = n₂ * bigCell k r c₂ 1 * m₂ * u₂⁻¹ →
  n₁ = n₂ ∧ c₁ = c₂ ∧ m₁ = m₂ ∧ u₁ = u₂

def PhiForm : Prop := ∀ (k r : ℕ) (X : Mat k r) (x : Fin r → ℂ) (Z X' : Mat k r),
  Phi k r X x Z X' =
    w0B k r * (NormedSpace.exp X * bigCell k r (1 + x) 1 * NormedSpace.exp Z * (NormedSpace.exp X')⁻¹)

def BigCellG : Prop := ∀ (k r : ℕ) (c : Fin r → ℂ), (∀ a, c a ≠ 0) → bigCell k r c 1 ∈ UH (Hpk k r)

def PhiDeriv : Prop := ∀ k r : ℕ,
  HasStrictFDerivAt (fun p : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r => Phi k r p.1 p.2.1 p.2.2.1 p.2.2.2)
    (Lm k r) 0

end PI.SwBig
end
end

section

noncomputable section

namespace PI

def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}

def area (Λ : AddSubgroup ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, a = |((starRingEnd ℂ) w₁ * w₂).im|}

def U1 (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + ω) * Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2

def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3

def discr (Λ : AddSubgroup ℂ) : ℂ := g2 Λ ^ 3 - 27 * g3 Λ ^ 2

end PI

end
end

section

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI

abbrev MtM (m : ℕ) := Fin m → Fin m → ℂ

def lmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := a * Matrix.of x

def rmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := Matrix.of x * a

def IsMatGroup {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G ∧ (∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) ∧
    ∀ a ∈ G, a⁻¹ ∈ G ∧ a * a⁻¹ = 1

def IsHaarOnM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulQ s) = μ

def IsRightInvM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  ∀ s ∈ S, μ.map (rmulQ s) = μ

def IsQuotM {m : ℕ} (μG μS ν : Measure (MtM m)) : Prop :=
  ∀ f : MtM m → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν

def QuotientSetting {m : ℕ} (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)) : Prop :=
  IsMatGroup G ∧ IsMatGroup S ∧ S ⊆ G ∧ IsHaarOnM G μG ∧ IsHaarOnM S μS ∧ IsRightInvM G μG ∧ IsRightInvM S μS ∧
    IsQuotM μG μS ν

def QuotInv : Prop :=
  ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)), QuotientSetting G S μG μS ν →
    ∀ F : MtM m → ℝ≥0∞, Measurable F →
      (∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) →
      ∀ g ∈ G, ∫⁻ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫⁻ x, F x ∂ν

end PI

end
end

section

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhConvProj

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ

def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def ConvProj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → IsRowProj π m T

end PI.PhConvProj
end
end

section

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhSchurConv

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ

def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def SchurConv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (Hσ : Type) [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
    (σ : G → (Hσ →L[ℂ] Hσ)) (d : ℝ) (w : Hσ),
    IsURep σ → IsFdegG μ σ d → ‖w‖ = 1 →
      PhConv μ (phOf σ w d) (coefM σ w) ∧
      ∀ u u' : Hσ, Integrable (fun g => phOf σ w d g * ⟪u', σ g u⟫_ℂ) μ ∧
        ∫ g, phOf σ w d g * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ

end PI.PhSchurConv
end
end

section

open Matrix
open scoped ComplexOrder

namespace PI

def UnitaryDense : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
    (∀ u : Matrix (Fin n) (Fin n) ℂ, uᴴ * u = 1 →
      MvPolynomial.eval (fun x : Fin n × Fin n => u x.1 x.2) P = 0) → P = 0

def FramesDense : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (G τ).PosDef) →
    ∀ P : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * G τ * y τ = 1) →
        MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) → P = 0

end PI
end

section

open NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.HermLatFin

def herm {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def IsLat {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def admitted {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm σ J x y)) ∧
    ∀ y : Fin n → E, (∀ x ∈ L, IsIntegral ℤ (herm σ J x y)) → (T : E) • y ∈ L

def IsUJ {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J g : Matrix (Fin n) (Fin n) E) : Prop :=
  (g.map σ)ᵀ * J * g = J

def HermLatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ),
    (∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) →
    0 < T →
    ∃ S : Set (Submodule (𝓞 E) (Fin n → E)), S.Finite ∧
      ∀ L, admitted σ J T L → ∃ L' ∈ S, ∃ g : Matrix (Fin n) (Fin n) E, IsUJ σ J g ∧
        (fun x => g *ᵥ x) '' (L' : Set (Fin n → E)) = (L : Set (Fin n → E))

end PI.HermLatFin
end
end

section

namespace PI

open Matrix ComplexOrder

def UnitKron : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
  ∀ (k : ℕ) (J γ : Matrix (Fin k) (Fin k) E),
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef) →
    (γ.map c)ᵀ * J * γ = J → (∀ i, IsIntegral ℤ (γ.charpoly.coeff i)) →
    ∃ n : ℕ, 0 < n ∧ γ ^ n = 1

end PI
end

section

open scoped InnerProductSpace

noncomputable section

namespace PI

def TransferenceCoverDiv : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y : V, (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)

def dualLat {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  {y | ∀ x ∈ L, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}

end PI
end
end

section

noncomputable section

namespace PI.WwInjective

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def WwInjective : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N : ℕ) (nu : Lt → YoungDiagram)
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l])),
    (∀ y, ph (DeX N nu y) = 0) → ∀ J, ph (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0

end PI.WwInjective
end
end

section

namespace PI

def SumAntidiagonalTuple : Prop :=
  ∀ D T : ℕ, D < T →
    ∑ k ∈ Finset.range (T - D), (Finset.Nat.antidiagonalTuple D k).card = Nat.choose (T - 1) D

end PI
end
