module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Mathlib.NumberTheory.Padics.Complex
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights TensorProduct

structure LinPt (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] where

  ρ : 𝓞 E →+* Module.End L V

  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)

  Λ : Submodule (𝓞 L) V
  fg : Λ.FG
  span : Submodule.span L (Λ : Set V) = ⊤
  stable : ∀ a, ∀ x ∈ Λ, ρ a x ∈ Λ

  I : AddSubgroup V
  I_le : ∀ x ∈ I, x ∈ Λ
  I_stable : ∀ a, ∀ x ∈ I, ρ a x ∈ I
  I_basis : ∃ (r : ℕ) (e : Fin r → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I

  Bq : HermitianBundle.{0} L

  f : Λ →ₗ[𝓞 L] Bq.carrier
  ker : ∀ x : Λ, f x = 0 ↔ (x : V) ∈ Submodule.span (𝓞 L) (I : Set V)
  full : ∀ y : Bq.carrier, ∃ (a : 𝓞 L) (x : Λ), a ≠ 0 ∧ f x = a • y
  orth : ∀ s s', s ≠ s' → OrthAt Bq (((eigSp ρ (σ s)).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)
    (((eigSp ρ (σ s')).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)

namespace LinPt

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

def eig (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := A.Λ ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def tor (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := Submodule.span (𝓞 L) (A.I : Set V) ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def img (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) A.Bq.carrier := ((A.eig s).comap A.Λ.subtype).map A.f

def fam (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Fin (r + k) → V :=
  Fin.append (fun a => eigComp A.ρ (A.σ s) (v a)) fun c => (q c : V)

def IsAdapted (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Prop :=
  LinearIndependent L (A.fam s v q) ∧ Submodule.span L (Set.range (A.fam s v q)) = eigSp A.ρ (A.σ s)

def gramDet (ι : L →+* ℂ) {k : ℕ} (q : Fin k → A.Λ) : ℝ :=
  (Matrix.of fun c c' => (A.Bq.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c))
    ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c'))).det.re

def labDeg (s : Ψ ⊕ Ψ) (F : Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : ℝ :=
  (logIdx F (A.fam s v q) - (∑ ι : L →+* ℂ, Real.log (A.gramDet ι q)) / 2) / Module.finrank ℚ L

def phiDeg [Fintype Ψ] (lab : Ψ → Ψ ⊕ Ψ) (F : Ψ → Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V)
    (q : Ψ → Fin k → A.Λ) : ℝ :=
  ∑ τ, A.labDeg (lab τ) (F τ) v (q τ) - Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / 2 +
    Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi)

end LinPt

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix Metric GroundTheory.Heights₂.Heights.Regular

structure LogPeriods (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] where
  a_le : a ≤ n
  free : Module.Free ℤ Λ
  fin : Module.Finite ℤ Λ
  rank : Module.finrank ℤ Λ = 2 * g

  E : LinearMap.BilinForm ℤ Λ
  alt : ∀ x, E x x = 0
  unimod : Function.Bijective E

  P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))
  hol : ∀ x, DifferentiableOn ℂ (fun w => P w x) (logCover a_le)

  H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  herm : ∀ w ∈ logCover a_le, (H (expCover a w)).IsHermitian
  pos : ∀ w ∈ logCover a_le, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H (expCover a w) *ᵥ star z).re
  im : ∀ w ∈ logCover a_le, ∀ x y, (P w x ⬝ᵥ H (expCover a w) *ᵥ star (P w y)).im = E x y

  T : Fin a → (Λ →ₗ[ℤ] Λ)
  mono : ∀ i, ∀ w ∈ logCover a_le, ∀ x,
    P (w + Pi.single (Fin.castLE a_le i) (2 * Real.pi * Complex.I)) x = P w (T i x)

  W : Submodule ℤ Λ
  coiso : ∀ x, (∀ y ∈ W, E x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W

  s : W → (Fin n → ℂ) → (Fin g → ℂ)
  s_hol : ∀ x, DifferentiableOn ℂ (s x) (ball 0 1)
  s_eq : ∀ x, ∀ w ∈ logCover a_le, s x (expCover a w) = P w x
  span : Submodule.span ℂ (Set.range fun x => s x 0) = ⊤

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptsOver (𝕜 : Type) [Field 𝕜] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → 𝕜) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, aeval z f = 0}

def algPts (p : ℕ) [Fact p.Prime] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → PadicAlgCl p) :=
  {z | z ∈ ptsOver (PadicAlgCl p) P ∧ ∀ q, IsAlgebraic ℚ (z q)}

def HasVal (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (w : 𝕜) : Prop :=
  ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
    aeval y g = s * aeval y h ∧ aeval z h ≠ 0 ∧ aeval z g = w * aeval z h

def ValLe (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [NormedField 𝕜] (z : (Σ k, ι k) → 𝕜) (r : ℝ) :
    Prop :=
  ∀ w, HasVal y a s z w → ‖w‖ ≤ r

def supMet {𝕜 : Type} [NormedField 𝕜] (a : K → ℤ) (z : (Σ k, ι k) → 𝕜) : ℝ :=
  ∏ k, ‖fun i : ι k => z ⟨k, i⟩‖ ^ a k

def IsFormOff (P : Ideal (MRing ι)) (u : MRing ι) : Prop :=
  (∃ d, IsMultiHomog u d) ∧ u ∉ P

def powH (A : HermLine ι) (q : ℕ) : HermLine ι where
  a := fun k => (q : ℤ) * A.a k
  h z := A.h z ^ q
  pos z hz := pow_pos (A.pos z hz) q
  smul c z hc := by
    rw [A.smul c z hc, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]

def shiftH (A : HermLine ι) (t : ℝ) : HermLine ι where
  a := A.a
  h z := Real.exp t * A.h z
  pos z hz := mul_pos (Real.exp_pos t) (A.pos z hz)
  smul c z hc := by rw [A.smul c z hc]; ring

def normHt (II : IntersectionSystem) (P : Ideal (MRing ι)) (A : HermLine ι) (D : ℕ) : ℝ :=
  II K ι P (D + 1) (fun _ => A) / (((D : ℝ) + 1) * geomDeg P A D)

structure IsNefH (P : Ideal (MRing ι)) (M : HermLine ι) : Prop where
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P M
  conj : IsConjInvariantH M
  nef : NefOnFibres P M.a

structure IsGenH (P : Ideal (MRing ι)) (L : HermLine ι) (Λ : ℝ) : Prop where
  pos : 0 < Λ
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P L
  conj : IsConjInvariantH L
  mono : ∃ a : K → ℕ, (L.a = fun k => (a k : ℤ)) ∧ ∀ z ∈ mcPts P, ∀ μ : (Σ k, ι k) →₀ ℕ,
    (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ * L.h z

end GlobalTheory.CompanionTheory.Ar.Small
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory

def SamePot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P Q : LocPot X) : Prop :=
  ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
    ∀ y ∈ V, P.φ x y - Q.φ x y = (G y).re

def sumPot {X : Type} [TopologicalSpace X] {σ : Type} [Fintype σ] (c : σ → ℝ) (P : σ → LocPot X) : LocPot X where
  U x := ⋂ a, (P a).U x
  isOpen_U x := isOpen_iInter_of_finite fun a => (P a).isOpen_U x
  mem_U x := Set.mem_iInter.2 fun a => (P a).mem_U x
  φ x y := ∑ a, c a * (P a).φ x y

structure AnSys (e : ℕ) (σ : Type) where

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  Θ : LocPot X

  L : LocPot X

  s : X → X → ℂ

  nb : ℕ

  m : Fin nb → ℕ

  W : Fin nb → Set X
  potΘ : IsPotential A Θ
  posΘ : IsPosPot A Θ
  potL : IsPotential A L
  sec : IsSection A L s
  snc : IsSNC A L s m W
  norm_le : ∀ y, logNormSec L s y ≤ 0

  th : σ → LocPot X

  ph : σ → X → ℝ

  phT : σ → ℝ → X → ℝ

  C₅ : ℝ

  C : ℝ

  t₀ : ℝ
  sing : ∀ a, IsSingWeight A L s (th a) (ph a) C₅
  reg : ∀ a, IsRegFamily A Θ L s (th a) (ph a) (phT a) C t₀
  c2 : ∀ a, IsRegFamilyC2 A s (ph a) (phT a)

attribute [instance] AnSys.top AnSys.compact AnSys.t2

namespace AnSys

variable {e : ℕ} {σ : Type} (S : AnSys e σ)

def open' : Set S.X := (bdry S.s)ᶜ

def potT (a : σ) (t : ℝ) : LocPot S.X := S.th a + LocPot.ofFun (S.phT a t)

def potH (a : σ) : LocPot S.X := S.th a + LocPot.ofFun (S.ph a)

def degNum (w : Fin e → σ) : ℝ := ReciprocityTheory.AnForm.M.mInt S.A (fun j => S.th (w j)) fun _ => 1

def degPoly [Fintype σ] : MvPolynomial σ ℝ := formPoly e S.degNum

def comap {σ' : Type} (f : σ' → σ) : AnSys e σ' :=
  { S with
    th := fun a => S.th (f a), ph := fun a => S.ph (f a), phT := fun a => S.phT (f a)
    sing := fun a => S.sing (f a), reg := fun a => S.reg (f a), c2 := fun a => S.c2 (f a) }

end AnSys

section Period

variable {e : ℕ} {X : Type} [TopologicalSpace X] {Ψ : Type} {N : ℕ}

def IsPeriodChart (A : FinHolAtlas e X) (j : ℕ) (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X)
    (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsOpen V ∧ x ∈ V ∧ (∀ τ a b, A.HoloOn V fun y => g τ y a b) ∧ (∀ τ, ∀ y ∈ V, InFlagDomain N j (g τ y)) ∧
    ∀ p : Ψ × Fin N, ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, (pot p).φ x y = stepPot N j p.2 (g p.1 y) + (G y).re

def IsFlagImmersionAt (A : FinHolAtlas e X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ) (x : X) : Prop :=
  ∀ k, x ∈ (A.chart k).source → ∀ v : Fin e → ℂ,
    (∀ τ, ((g τ x)⁻¹ * Matrix.of fun a b =>
        fderiv ℂ (fun z => g τ ((A.chart k).symm z) a b) (A.chart k x) v).BlockTriangular id) → v = 0

def IsUniformised (A : FinHolAtlas e X) (U : Set X) (j : ℕ) (pot : Ψ × Fin N → LocPot X) : Prop :=
  (∀ x ∈ U, ∃ V g, IsPeriodChart A j pot x V g) ∧
    ∃ x ∈ U, ∃ V g, IsPeriodChart A j pot x V g ∧ IsFlagImmersionAt A g x

end Period

section Param

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def IsNull (A : FinHolAtlas e X) (N : Set X) : Prop :=
  ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N) = 0

def IsParam (A : FinHolAtlas e X) (V : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) : Prop :=
  IsOpen V ∧ ContinuousOn Φ V ∧ Set.InjOn Φ V ∧
    ∀ j, AnalyticOnNhd ℂ (A.chart j ∘ Φ) (V ∩ Φ ⁻¹' (A.chart j).source)

def IsParamCover (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ)) (Φ : ℕ → (Fin e → ℂ) → X) : Prop :=
  (∀ n, IsParam A (V n) (Φ n)) ∧ (∀ n, MeasurableSet (B n) ∧ B n ⊆ V n) ∧
    (Pairwise fun n n' => Disjoint (Φ n '' B n) (Φ n' '' B n')) ∧ IsNull A (⋃ n, Φ n '' B n)ᶜ

def paramDens (P : Fin e → LocPot X) (Φ : (Fin e → ℂ) → X) (z : Fin e → ℂ) : ℝ :=
  maDens (fun i z' => (P i).φ (Φ z) (Φ z')) z

def IsTwiceDifferentiableAt (A : FinHolAtlas e X) (P : LocPot X) (x : X) : Prop :=
  ∀ j, x ∈ (A.chart j).source → ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) (A.chart j x)

end Param

end GlobalTheory.CompanionTheory.Ar.PB
end
end
