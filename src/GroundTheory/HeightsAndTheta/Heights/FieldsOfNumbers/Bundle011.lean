module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle009
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AsSubring
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FibreFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → (fibrePrimes j P' W).Finite

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FibreNonempty.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
    (fibrePrimes j P' W).Nonempty

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FibreRelDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → ∀ W' ∈ fibrePrimes j P' W, relDim W' = (n : ℕ)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def LocalIntegralClosureFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ s : Finset (FractionRing (MRing ι' F ⧸ P')),
        (∀ e ∈ s, e ∈ homFracDegZero P' ∧
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) e) ∧
        ∀ x ∈ homFracDegZero P',
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) x →
          x ∈ Submodule.span ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P'))
            (s : Set (FractionRing (MRing ι' F ⧸ P')))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def SemilocalFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Module.Finite (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def SemilocalFiniteRank.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Module.Finite (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.IsTorsionFree (degZeroLoc (contractPrime j P') {W})
          (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.finrank (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) =
          relDeg j P'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def SemilocalIntegral.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Algebra.IsIntegral (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a h : MRing (fun k => ι' (j k)) F), IsMultiHomog a c → IsMultiHomog h c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → h ∉ W →
    ∀ M : Ideal (MRing ι' F) → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      ∀ α : degZeroLoc (contractPrime j P') {W},
        (α : FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P')) =
            algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') a) /
              algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') h) →
          ∃ N : ℕ, Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸
                LinearMap.range (LinearMap.lsmul (degZeroLoc (contractPrime j P') {W})
                  (degZeroLoc P' (fibrePrimes j P' W)) α)) = N ∧
            cycEval M (divCycle P' (rename (blockIncl j ι') a)) = N

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalResidueLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
    haveI := hP'.isPrime
    ∀ W' (hW' : W' ∈ fibrePrimes j P' W),
      haveI := hW'.1.isPrime
      ∃ 𝔪 : Ideal (degZeroLoc P' (fibrePrimes j P' W)),
        (∀ x : degZeroLoc P' (fibrePrimes j P' W),
          x ∈ 𝔪 ↔ ¬ ∃ y ∈ degZeroLoc P' {W'}, (x : FractionRing (MRing ι' F ⧸ P')) * y = 1) ∧
        Module.length (degZeroLoc (contractPrime j P') {W})
            (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪) = (relDeg j W' : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Chart

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

def chartMonomial [Fintype K] (u : ∀ k, ι k) (b : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, u k⟩ ^ b k

def chartMap (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
  aeval fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))

def chartIdeal (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) : Ideal (MRing ι F) :=
  RingHom.ker (chartMap P u)

instance chartIdeal.isPrime (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartIdeal P u).IsPrime :=
  RingHom.ker_isPrime _

end Chart

def MChartDehomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
    ∀ (f : MRing ι F) (b : K → ℕ), IsMultiHomog f b →
      chartMap P u f = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartHomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (u : ∀ k, ι k) (p : MRing ι F), ∃ (b : K → ℕ) (h : MRing ι F), IsMultiHomog h b ∧
      ∀ (P : Ideal (MRing ι F)) [P.IsPrime], (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
        chartMap P u p = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P h) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartTrdeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime], IsMultiHomogIdeal P →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
      Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P)

def MChartLocDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime], P ≤ W →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) →
      ringKrullDim (degZeroLoc P {W}) =
        ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).height

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

section Cone

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem primeCompl_map_le_nonZeroDivisors (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) :
    W.primeCompl.map (Ideal.Quotient.mk P) ≤ nonZeroDivisors (MRing ι F ⧸ P) := by
  rintro _ ⟨s, hs, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hs (hPW h)

def coneLocal (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) :=
  Localization.subalgebra.ofField _ _ (primeCompl_map_le_nonZeroDivisors P W hPW)


omit [DecidableEq K] in
instance coneLocal.isLocalization (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) (coneLocal P W hPW) :=
  Localization.subalgebra.isLocalization_ofField _ _ _

theorem degZeroLoc_le_coneLocal (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    ∀ x ∈ degZeroLoc P {W}, x ∈ coneLocal P W hPW := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨b, f, g, -, -, -, hgW, rfl⟩ := hx
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, hgW W rfl, rfl⟩, div_eq_mul_inv _ _⟩
  | algebraMap r =>
    rw [IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P)]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

def degZeroLocToCone (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    degZeroLoc P {W} →+* coneLocal P W hPW :=
  (degZeroLoc P {W}).val.toRingHom.codRestrict (coneLocal P W hPW)
    (fun x => degZeroLoc_le_coneLocal P W hPW x x.2)

instance degZeroLoc.algebraCone (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Algebra (degZeroLoc P {W}) (coneLocal P W hPW) :=
  (degZeroLocToCone P W hPW).toAlgebra

theorem degZeroLoc.algebraMap_cone_coe (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) (x : degZeroLoc P {W}) :
    ((algebraMap (degZeroLoc P {W}) (coneLocal P W hPW) x : coneLocal P W hPW) :
      FractionRing (MRing ι F ⧸ P)) = x :=
  rfl

end Cone

def ConeLocalFlat.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W),
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∃ (_ : IsLocalRing (degZeroLoc P {W})) (_ : IsLocalRing (coneLocal P W hPW)),
      Module.Flat (degZeroLoc P {W}) (coneLocal P W hPW) ∧
        (maximalIdeal (degZeroLoc P {W})).map
            (algebraMap (degZeroLoc P {W}) (coneLocal P W hPW)) =
          maximalIdeal (coneLocal P W hPW)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
