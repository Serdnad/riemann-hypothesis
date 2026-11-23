module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def GenDegMatAct.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsInvMat B → genDeg (ι := GlobalTheory κ) (coordIdeal ℤ (matAct B x)) D 1 = genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockBirationalHilbert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → BlockBirational y k₀ → ∀ m : K → ℕ, ∃ c : ℕ, ∀ n : ℕ,
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else 0) ≤
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else m k) ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else m k) ≤
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then ((n + c : ℕ) : ℤ) else 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftAtPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ) (p : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime → KH.AmpleV (ZMod p) (fibreIdeal p y) N →
    ∃ q t₀ : ℕ, 1 ≤ q ∧ ∀ t : ℕ, t₀ ≤ t →
      ∃ (r : ℕ) (x' : Fin r → Ω), (∀ j, x' j ∈ chartLat y ((t * q) • N) 1) ∧
        ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (u : Fin r → Ω) (v : Ω), (∀ j, u j ∈ chartRingZ y c) ∧
          v ∈ chartRingZ y c ∧ ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k)) + p * v = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → KH.AmpleV ℚ (KH.genIdeal y) N →
    (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N - fun _ => 1)) →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) N) →
    ∃ (a : ℕ) (ι' : Type) (_ : Fintype ι') (x' : ι' → Ω),
      1 ≤ a ∧ (∀ j, x' j ∈ chartLat y (a • N) 1) ∧ KH.GeneratesOn y (a • N) x' ∧
        Birational (fun p : Σ _ : Unit, ι' => x' p.2)

section Inhabitant

end Inhabitant

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def MonomialShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (q τ n : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (A.a = fun k => (a k : ℤ)) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → MonomialsBounded (mCoordIdeal y) A a →
    1 ≤ q → τ ≤ q * n →
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1))
        (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def PerturbMonomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (q : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (A.a = fun k => (a k : ℤ)) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → MonomialsBounded (mCoordIdeal y) A a →
    1 ≤ q →
    IsSmallGeneratedDatum P0 y D (HermLine.zcomb A (fsH ι) q 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def ProjDegGenDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 = (projDeg x e : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def ReductionToProjectiveBlock.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d : HSMBlockDatum D K ι Ω),
    I.IsFamily →
    (fun n => hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n -
        (genDeg (mCoordIdeal d.y) D d.A.a : ℝ) * hsDefect D (chiP D) (hhOf I D) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SecondVeronese.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (κ : Type) (_ : Fintype κ) (d : HSMDatum D Ω κ),
      (∀ n : ℕ, resChi d n = chiP D (2 * n)) ∧
      (∀ I : AllFam, I.IsFamily → top I d.x d.m D = 2 ^ (D + 1) * hhOf I D) ∧
      genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 = 2 ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftDegreePolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (a b : K → ℤ),
    IsArithVar P (D + 1) →
    ∃ r : Polynomial ℝ, r.natDegree ≤ D ∧ r.coeff D = (genDeg P D a : ℝ) ∧
      ∀ q : ℕ, (genDeg P D ((q : ℤ) • a + b) : ℝ) = r.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftIntersectionPolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem) (P : Ideal (MRing ι))
    (n : ℕ) (A B : HermLine ι),
    IsIntersectionSystem II → IsArithVar P n → IsSmoothHerm A → IsSmoothHerm B →
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ p.coeff n = II K ι P n (fun _ => A) ∧
      ∀ q : ℕ, II K ι P n (fun _ => HermLine.zcomb A B (q : ℤ) 1) = p.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ShiftNefBig.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    ∀ q : ℕ, 1 ≤ q → IsNefBigDatum P0 y D (HermLine.zcomb A (fsH ι) (q : ℤ) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
