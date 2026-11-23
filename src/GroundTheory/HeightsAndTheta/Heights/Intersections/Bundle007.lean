module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

section Cone

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem primeCompl_map_le_nonZeroDivisors_quot (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
    (hPW : P ≤ W) : W.primeCompl.map (Ideal.Quotient.mk P) ≤ nonZeroDivisors (MRing ι ⧸ P) := by
  rintro _ ⟨g, hg, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hg (hPW h)

def coneLocRing (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Subalgebra (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) :=
  Localization.subalgebra.ofField _ _ (primeCompl_map_le_nonZeroDivisors_quot P W hPW)

instance coneLocRing.isLocalization (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P)) (coneLocRing P W hPW) :=
  Localization.subalgebra.isLocalization_ofField _ _ _

theorem locRing_le_coneLocRing (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    ∀ x ∈ locRing P W, x ∈ coneLocRing P W hPW := by
  intro x hx
  have hle : locRing P W ≤ (coneLocRing P W hPW).toSubring := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨u, v, a, hv, hvW, -, -, rfl⟩
    exact ⟨Ideal.Quotient.mk P u, Ideal.Quotient.mk P v, ⟨v, hvW, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv]⟩
  exact hle hx

def locRingToCone (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    locRing P W →+* coneLocRing P W hPW :=
  (locRing P W).subtype.codRestrict (coneLocRing P W hPW)
    (fun x => locRing_le_coneLocRing P W hPW x x.2)

instance locRing.algebraCone (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) :
    Algebra (locRing P W) (coneLocRing P W hPW) :=
  (locRingToCone P W hPW).toAlgebra

theorem locRing.algebraMap_cone_coe (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W)
    (x : locRing P W) :
    ((algebraMap (locRing P W) (coneLocRing P W hPW) x : coneLocRing P W hPW) :
      FractionRing (MRing ι ⧸ P)) = x :=
  rfl

end Cone

def regularityLocalFlat_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (hP : IsMultiProjPrime P) (hW : IsMultiProjPrime W) (hPW : P ≤ W),
    haveI := hP.1
    haveI := hW.1
    ∃ (_ : IsLocalRing (locRing P W)) (_ : IsLocalRing (coneLocRing P W hPW)),
      Module.Flat (locRing P W) (coneLocRing P W hPW) ∧
        (maximalIdeal (locRing P W)).map (algebraMap (locRing P W) (coneLocRing P W hPW)) =
          maximalIdeal (coneLocRing P W hPW)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityDehomogenization_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsMultiProjPrime P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → IsMultiHomog t a → t ∉ W →
    y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    y ∈ locRing P W ∧
      multAt (P ⊔ Ideal.span {s}) W = (Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalDimension_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsLocalRing (locRing P W) ∧ IsNoetherianRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalResidue_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → ∀ [IsLocalRing (locRing P W)],
    Finite (IsLocalRing.ResidueField (locRing P W)) ∧
      Nat.card (IsLocalRing.ResidueField (locRing P W)) = charOf W ^ (geoNum 0 W b).toNat

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalCardinality_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    ((Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat : ℝ) *
        ((geoNum 0 W b : ℝ) * Real.log (charOf W)) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y))

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    Finite (locRing P W ⧸ locIdeal P W y)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def LocRingChartLoc.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) [P.IsPrime],
    W.IsPrime → P ≤ W → IsRelevant W →
    ∃ T : Finset (FractionRing (MRing ι ⧸ P)),
      Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))) ≤ locRing P W ∧
      ∀ z ∈ locRing P W, ∃ b ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))),
        ∃ c ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))), c ≠ 0 ∧ c⁻¹ ∈ locRing P W ∧ z * c = b

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    ∀ y ∈ locRing P W, ∃ (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W W' : Ideal (MRing ι)),
    P.IsPrime → IsMultiProjPrime W → IsMultiProjPrime W' → P ≤ W → P ≤ W' →
    locRing P W = locRing P W' → W = W'

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    IsLocalRing (locRing P W) ∧
      ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
        (y : FractionRing (MRing ι ⧸ P)) * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
        (IsUnit y ↔ u ∉ W)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingNoeth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W → IsRelevant W → IsNoetherianRing (locRing P W)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingPow.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ P))
    (u v : MRing ι) (b : K → ℕ) (y : FractionRing (MRing ι ⧸ P)),
    P.IsPrime → IsMultiHomogIdeal P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsMultiHomog t a → t ∉ W → x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    IsMultiHomog u b → IsMultiHomog v b → u ∈ W → v ∉ W → y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
    ∃ n : ℕ, ∃ z ∈ locRing P W, y ^ n = x * z

end

end GroundTheory.Heights₂.Heights.Inter
end
