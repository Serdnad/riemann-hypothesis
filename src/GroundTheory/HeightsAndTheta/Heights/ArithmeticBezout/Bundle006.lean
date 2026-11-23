module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Swap

variable {F : Type*} [Field F] {n k : ℕ}

theorem comp_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by
  obtain ⟨x, hx, hI, hlin⟩ := hu
  exact ⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩

theorem IsChowForm.dvd_rename {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by
  refine (hf.2 _).mp fun u hu => ?_
  rw [aeval_rename]
  exact (hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)

theorem rename_prodMap_mul (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by
  rw [rename_rename]
  rfl

theorem rename_prodMap_one (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by
  have : Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id := by
    funext ij
    rfl
  rw [this]
  exact rename_id_apply p

theorem IsChowForm.rename_eq_C_mul {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) :
    ∃ c : F, rename (Prod.map τ id) f = C c * f := by
  obtain ⟨a, ha⟩ := hf.dvd_rename τ
  obtain ⟨b, hb⟩ := hf.dvd_rename (τ⁻¹ : Equiv.Perm (Fin k))
  have hback : rename (Prod.map τ id) (rename (Prod.map ⇑(τ⁻¹ : Equiv.Perm (Fin k)) id) f) = f := by
    rw [← rename_prodMap_mul, mul_inv_cancel, rename_prodMap_one]
  have hab : a * rename (Prod.map τ id) b = 1 := by
    have h1 : f * (a * rename (Prod.map τ id) b) = f * 1 := by
      rw [mul_one, ← mul_assoc, ← ha]
      conv_rhs => rw [← hback, hb]
      rw [map_mul]
    exact mul_left_cancel₀ hf.1 h1
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (IsUnit.of_mul_eq_one _ hab)
  exact ⟨c, by rw [ha, mul_comm]⟩

theorem IsChowForm.rename_swap {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (x y : Fin k) :
    ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map (Equiv.swap x y) id) f = C c * f := by
  obtain ⟨c, hc⟩ := hf.rename_eq_C_mul (Equiv.swap x y)
  refine ⟨c, ?_, hc⟩
  have h2 : rename (Prod.map (Equiv.swap x y * Equiv.swap x y) id) f = C (c ^ 2) * f := by
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hc, ← mul_assoc, ← C_mul, sq]
  rw [Equiv.swap_mul_self, rename_prodMap_one] at h2
  have h3 : (C (c ^ 2) - 1) * f = 0 := by
    rw [sub_mul, ← h2, one_mul, sub_self]
  have h4 : C (c ^ 2) - 1 = (0 : MvPolynomial (Fin k × Fin n) F) :=
    (mul_eq_zero.mp h3).resolve_right hf.1
  rw [sub_eq_zero, ← C_1] at h4
  exact C_injective _ _ h4

theorem chowFormSwap : ChowFormSwap.Statement := by
  intro F _ n k I f hf τ
  induction τ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩
  | swap_mul σ x y _ ih =>
    obtain ⟨c, hc2, hc⟩ := ih
    obtain ⟨d, hd2, hd⟩ := hf.rename_swap x y
    refine ⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]
    ring

end Swap

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def BaseChangeAvoid.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → K) (σ : K →+* ℂ), IsProjPrime I → linForm u ∉ I →
      ∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, linForm (fun j => σ (u j)) ∉ W

def coneBall {n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0}

def ConeBallFinite.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤

def ConeFsLogIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      IntegrableOn (fun y => fsLog h u (h.pointOf y)) (coneBall h W)
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))

def ConeHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) = 0

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ConeIntegralMass.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      coneIntegral h W e (fun _ => 1) = δ

def ChowFormBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I k f →
      (∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, IsProjPrime W) ∧
        IsChowFormCycle (fundCycle (I.map (MvPolynomial.map σ))) k (MvPolynomial.map σ f)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def RadicalBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (ι : Type)
    (I : Ideal (MvPolynomial ι K)), I.IsRadical → (I.map (MvPolynomial.map σ)).IsRadical

def ChowFormExtend.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n k : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin k × Fin n) K),
    IsChowForm I k f → IsChowForm (I.map (MvPolynomial.map σ)) k (MvPolynomial.map σ f)

def ChowFormReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) F))
    (h : MvPolynomial (Fin k × Fin n) F),
    IsHomogIdeal J → J.IsRadical → IsChowForm J k h → IsChowFormCycle (fundCycle J) k h

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def ChowFormSectionAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowFormSectionPerfect.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def FundCycleBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) K)),
      fundCycle (J.map (MvPolynomial.map σ)) =
        ∑ W ∈ (fundCycle J).support, fundCycle J W • fundCycle (W.map (MvPolynomial.map σ))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def SectionCycleReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, linForm u ∉ P) →
      fundCycle (J ⊔ Ideal.span {linForm u}) = ∑ P ∈ (fundCycle J).support, divCycle P u

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights


open Classical in
def SectionLengthSum.Statement : Prop := by
  classical
  exact
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J W : Ideal A) (f : A),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, f ∉ P) →
    W ∈ (J ⊔ Ideal.span {f}).minimalPrimes →
    (∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) →
      GroundTheory.Heights₂.Heights.localMult (J ⊔ Ideal.span {f}) W =
        ∑ P ∈ (J.finite_minimalPrimes_of_isNoetherianRing A).toFinset with P ≤ W,
          GroundTheory.Heights₂.Heights.localMult (P ⊔ Ideal.span {f}) W

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Ideal

theorem localMult_ne_zero_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {J P : Ideal A} (hP : P ∈ J.minimalPrimes) : localMult J P ≠ 0 := by
  have hPp : P.IsPrime := hP.1.1
  unfold localMult
  rw [dite_eq_left hPp]
  let R := Localization.AtPrime P
  let I : Ideal R := J.map (algebraMap A R)
  have hmin : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map P.primeCompl R J, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact hP
  have := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  have : IsArtinian R (R ⧸ I) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  have : IsNoetherian R (R ⧸ I) := isNoetherian_quotient I
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hmin.1.2
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [Ne, ENat.toNat_eq_zero, not_or]
  exact ⟨(Module.length_pos (R := R) (M := R ⧸ I)).ne', Module.length_ne_top⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjDegreeChow.Statement : Prop :=
  ∀ (n e δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      ComplexSets.IsFiniteProjection W A → ComplexSets.projDegree W A = δ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowDegreeClosedPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      chowDegree I 1 = Module.finrank F (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
