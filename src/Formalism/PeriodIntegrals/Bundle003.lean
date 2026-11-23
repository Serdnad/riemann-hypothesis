module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Classical

namespace PI.CubicExponentialFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def phAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a (-logMv E : PowerSeries ℂ_[p])

def eAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a E

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq l ex E : PowerSeries ℂ_[p])
    (T : MvPowerSeries (Fin 3) ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff E = 1 →
    T * eAt E (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 * eAt E (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 *
        eAt E (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) ^ 3 =
      eAt wq (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) * eAt wq (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) *
        eAt wq (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) *
        (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * eAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2))) *
        (sub l ex (Xv 0) (Xv 1) * eAt E (sub l ex (Xv 0) (Xv 1))) *
        (sub l ex (Xv 1) (Xv 2) * eAt E (sub l ex (Xv 1) (Xv 2))) *
        (sub l ex (Xv 2) (Xv 0) * eAt E (sub l ex (Xv 2) (Xv 0))) →
    (∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T = add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2) * sub l ex (Xv 0) (Xv 1) * sub l ex (Xv 1) (Xv 2) *
        sub l ex (Xv 2) (Xv 0) * n) →
    Simeq (phAt E (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) + phAt E (sub l ex (Xv 0) (Xv 1)) +
        phAt E (sub l ex (Xv 1) (Xv 2)) + phAt E (sub l ex (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (phAt E (Xv 0) + phAt E (Xv 1) + phAt E (Xv 2)))

end PI.CubicExponentialFactor
end
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI

namespace PhMeasCore

variable {n : ℕ}

def Jm (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1

def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε}

def UH (Hm : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Hm * g = Hm}

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def SmoothOnH {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Hm : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, g₀ᴴ * Hm * g₀ = Hm → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ UH Hm → f g = F g

end Smooth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def smoothVecs (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | SmoothOnH Hm (fun g => σ g v)}

def InLie (Hm X : Matrix (Fin n) (Fin n) ℂ) : Prop := Xᴴ * Hm + Hm * X = 0

def dsig (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp] (Hm : Matrix (Fin n) (Fin n) ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLie Hm X) ∧
    ∀ v ∈ smoothVecs Hm σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

end PhMeasCore


open PhMeasCore in
def PhMeasCore : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (B : H → Wp) (w : H),
    (∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P ∧ Pᴴ * Jm ε * P = Hm ∧
      (σ (P⁻¹ * 1 * P) = 1 ∧ ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) ∧
      ∀ v : H, ContinuousOn (fun g => σ (P⁻¹ * g * P) v) (UJset ε)) →
    (∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v + v') = B v + B v') →
    (∀ c : ℂ, ∀ v ∈ smoothVecs Hm σ, B (c • v) = c • B v) →
    IsCWCont Hm σ B →
    w ∈ smoothVecs Hm σ →
    Measurable (Set.indicator {x : Fin n → Fin n → ℂ | Matrix.of x ∈ UH Hm} (fun x => ‖B (σ (Matrix.of x) w)‖))

end PI

end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ContDiff

namespace PI.RhsWLim

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

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def Hb (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then -1 else 1

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def IsSection (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Prop :=
  (∀ i j : Fin (k + 1), ContDiffOn ℝ ∞ (fun ζ => μsec ζ i j) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
    Matrix.conjTranspose (μsec ζ) * Hb k * μsec ζ = Hb k ∧ herm (Hb k) (μsec ζ *ᵥ wbPart k r z') (wbPart k r z) = ζ

def embWb (k r : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) then 1 else 0

def zWeight (k : ℕ) (T T' : ℝ) (ζ : ℂ) : ℝ :=
  if T * T' ≤ Complex.normSq ζ then (Complex.normSq ζ - T * T') ^ (k - 1) else 0

def volU (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (2 * Real.pi) ^ (i + 1) / (i.factorial : ℝ)

def wbConst (k : ℕ) (T T' a a' : ℝ) : ℝ :=
  2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1) * a * a')

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def rhsW (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
    ∫⁻ h, ∫⁻ h', φ (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW

def zeta0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ := ((2 * Real.sqrt (Tz k r z * Tz k r z') : ℝ) : ℂ)

def mBase (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  embWb k r (μsec (zeta0 k r z z'))

def bBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UWb k r) ρ

def mBall (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ρ : ℝ) :
    Set (Mt k r) :=
  {x | (fun i j => ((mBase k r z z' μsec)⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}

def bVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : lieE (UWb k r)) ρ)).toReal

structure WbData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop where
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  haarW : IsHaarOn (UWset k r z) μW
  haarW' : IsHaarOn (UWset k r z') μW'
  a_pos : 0 < a
  a'_pos : 0 < a'
  massW : μW Set.univ = ENNReal.ofReal a
  massW' : μW' Set.univ = ENNReal.ofReal a'
  sec : IsSection k r z z' μsec

def RhsWLim : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    Tendsto (fun ρ : ℝ => (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ)
      (𝓝[>] 0) (𝓝 (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹)

end PI.RhsWLim
end
end

section

namespace PI

def DiscFactor : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r R₁ : ℝ), 0 < R₁ → R₁ < r →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
      (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
      ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z

def DiscLog : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), DifferentiableOn ℂ f (Metric.ball z₀ R) →
    (∀ z ∈ Metric.ball z₀ R, f z ≠ 0) →
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ Metric.ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ Metric.ball z₀ R, f z = f z₀ * Complex.exp (g z)

end PI
end

section

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhProdConv

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def ProdConv : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, SecondCountableTopology (G i)] (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsInvInvariant] (ph m : ∀ i, G i → ℂ),
    (∀ i, Integrable (ph i) (μ i)) → (∀ i, PhConv (μ i) (ph i) (m i)) →
      Integrable (fun g : ∀ i, G i => ∏ i, ph i (g i)) (Measure.pi μ) ∧
      PhConv (Measure.pi μ) (fun g => ∏ i, ph i (g i)) (fun g => ∏ i, m i (g i))

end PI.PhProdConv
end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.ExistsGaugeMeasureForEachRank

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

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def IsGaugeOn (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (μ : Measure (Mt k r)) : Prop :=
  IsHaarOn S μ ∧
    Tendsto (fun ρ : ℝ => (μ (expBall S ρ)).toReal / (volume (Metric.ball (0 : lieE S) ρ)).toReal)
      (𝓝[>] 0) (𝓝 1)

def ExistsGaugeMeasureForEachRank : Prop := ∀ r : ℕ, ∃ μ : Measure (Mt 0 r), IsGaugeOn (UWb 0 r) μ

end PI.ExistsGaugeMeasureForEachRank
end
end

section

open Matrix

noncomputable section

namespace PI

def ExpTri : Prop :=
  ∀ (n : ℕ) (X Y Z U : Matrix (Fin n) (Fin n) ℂ), Xᴴ = X → Yᴴ = Y → Zᴴ = Z →
    U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    NormedSpace.exp X * NormedSpace.exp Y = U * NormedSpace.exp Z →
    Real.sqrt (∑ i, ∑ j, ‖Z i j‖ ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) + Real.sqrt (∑ i, ∑ j, ‖Y i j‖ ^ 2)

end PI

end
end
