module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle019
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar PBlk oneLine isSmoothHerm_oneLine)
open ComplexSets

def SegreChartAbsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
      ∀ J ∈ segreChartComponents P σ i, ∀ A : Matrix (Fin e) (Fin m) ℂ, IsFiniteProjection J A →
        Integrable (chartAbsDens J A (chartWeight σ i g) (chartPot σ i L))

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm oneLine isSmoothHerm_oneLine)
open ComplexSets Matrix

def SegreChartSheetCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι), (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ J ∈ segreChartComponents P σ i, ∀ (A : Matrix (Fin e) (Fin m) ℂ) (x : Fin m → ℂ)
        (s : (Fin e → ℂ) → Fin m → ℂ), x ∈ zeroSet J → IsSheetAt J A x s →
          |ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ s) (A *ᵥ x)| ≤
            C * |ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x)|

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def CurveVertPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧
          (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) ∧
        ∀ (e : K → ℕ) (g : MRing ι), _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k)

def CurveVertPointInj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)

def CurveVertPointSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0 →
          ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m

def CurveVertPointMultChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W →
          (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
            multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
              locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})

def CurveSectionQuotLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (c : ∀ k, ι k), m.IsPrime → (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : Ω) * aeval y s = a * ∏ k, y ⟨k, c k⟩ ^ d k →
          locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) =
            locLen m (curveRing y ⧸ Ideal.span {a})

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar PBlk)

def GoodChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) →
      ∀ J ∈ (projChartIdeal P σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal PBlk)
open ComplexSets

def GoodChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsMultiHomogIdeal P → zeroSet (projChartIdeal P σ Ψ) = projChartSet P σ Ψ

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem PoincareLelongAlt.of_found (hSt : StokesStatement) (hReg : PoincareLelongRegularised.Statement)
    (hLim : PoincareLelongLimit.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε) := by
    intro ε hε
    have h := hSt K ι P n L (regLine A s ε ha hsa) B hP hL (isSmoothHerm_regLine hA hε ha hsa) hB
      (regLine_a A s ε ha hsa) hBa
    rw [log_regLine] at h
    exact h.symm
  exact tendsto_nhds_unique (hReg K ι P n L A B s hP hL hA hB hBa hs)
    ((hLim K ι P n L A B s hP hL hA hB hBa hs).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal)

def ChartDehomIdeal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal P →
      segreChartIdeal P σ i =
        (((P.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).radical).comap (segreDehom σ i)

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

def ConeRingLaurent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) (i : (k : K) → ι k),
    (ratioMap i).Flat ∧ ∀ 𝔮 : Ideal (DehomRing i), 𝔮.IsPrime → (𝔮.map (ratioMap i)).IsPrime

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm pot segre oneLine isSmoothHerm_oneLine)

def SegreSheetFormCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
      ∃ C : ℝ, ∀ (z : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ)) (y : Fin e → ℂ),
        IsOpen U → y ∈ U → DifferentiableOn ℂ z U → (∀ k, ∃ j, z y ⟨k, j⟩ ≠ 0) →
          |ReciprocityTheory.AnForm.maDens (fun j => pot L j ∘ z) y| ≤
            C * ReciprocityTheory.AnForm.maDens
              (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) y

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem Multilin.of_found
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u})
    (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u})
    (hAdd : FieldNumbers.IntNumAdd.Statement.{u})
    {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι := by
  classical
  intro I hI V n L j a b hV
  have e : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of hBase hCut hEx hDiv I hI V n L' hV
  have hP : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  rw [e, e, e]
  exact hAdd F K ι V hP.multiHomog hP.relevant n (relDim_eq_of_ringKrullDim V n hV.2) L j a b

theorem Multilin.full {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι :=
  Multilin.of_found FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full FieldNumbers.IntNumAdd.full F ι

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

universe u

namespace ProjContract

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

section Theory

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [DecidableEq K] in
theorem ratDiv_eq (P : Ideal (NumbersDVR.MRing ι F)) (f g : NumbersDVR.MRing ι F)
    (W : Ideal (NumbersDVR.MRing ι F)) :
    NumbersDVR.ratDiv P f g W = AI.I1.ratDiv P f g W := by
  simp only [NumbersDVR.ratDiv, AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
  rw [Bridge.divCycle_eq, Bridge.divCycle_eq]

theorem isIntersectionTheory (I : AI.I1.IFamily F ι) (hI : AI.I1.IsFieldIntersection I) :
    FieldNumbers.IsIntersectionTheory F I := by
  constructor
  · intro P hP h0
    choose i hi using hP.relevant
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P 0).mp h0
    have hV : AI.I1.IsProjVarF P 0 := ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
    have h1 := hI.1 P ![] i hV hi
    have h2 := NumbersDVR.IntNumPoint.proof FieldNumbers.IntNumBase.full F K ι P i hP hd hi
    have h3 := (FieldNumbers.IntNumBase.full F K ι P hP h0).2
    have h4 : FieldNumbers.resDeg P = Module.finrank F
        (@FieldNumbers.homFracDegZero _ _ _ _ _ P hP.isPrime) := by
      rw [FieldNumbers.resDeg, dite_eq_left hP.isPrime]
    rw [h1, ← h2, h3, h4]
  · intro P n hP hn bf bg f g hf hg hfP hgP bs
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P (n + 1)).mp hn
    rw [hI.2 P n bs _ f g ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
      ⟨bf, bg, (Bridge.isMultiHomog_iff f bf).mp hf, (Bridge.isMultiHomog_iff g bg).mp hg, hfP, hgP,
        fun k => rfl⟩]
    simp only [NumbersDVR.cycEval, AI.I1.cycEval, ratDiv_eq]
    exact (finsum_mul_eq_sum _ _).symm

end Theory

section Image

variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

def emb (hv : AI.I1.IsBlockMap κ v) : K ↪ K' := ⟨κ, hv.1⟩

theorem range_eq (hv : AI.I1.IsBlockMap κ v) :
    Set.range v = Set.range (FieldNumbers.blockIncl (emb hv) ι') := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    have h := hv.2.2.1 p
    revert h
    generalize v p = q
    obtain ⟨a, b⟩ := q
    rintro (rfl : a = κ p.1)
    exact ⟨⟨p.1, b⟩, rfl⟩
  · rintro ⟨⟨k, x⟩, rfl⟩
    exact hv.2.2.2 _ ⟨k, rfl⟩

def blockEquiv (hv : AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (emb hv k)) :=
  (Equiv.ofInjective v hv.2.1).trans ((Set.equivOfEq (range_eq hv)).trans
    (Equiv.ofInjective _ (FieldNumbers.PFContracted.blockIncl_injective_of_embedding (emb hv) ι')).symm)

theorem blockIncl_blockEquiv (hv : AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    FieldNumbers.blockIncl (emb hv) ι' (blockEquiv hv p) = v p := by
  simp [blockEquiv, Equiv.apply_ofInjective_symm]

theorem imageVar_eq (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    AI.I1.imageVar F v V' = (FieldNumbers.contractPrime (emb hv) V').comap
      (rename (blockEquiv hv) : Geo.MRingOver F ι →ₐ[F] _).toRingHom := by
  ext x
  simp only [AI.I1.imageVar, FieldNumbers.contractPrime, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_rename]
  have : (FieldNumbers.blockIncl (emb hv) ι' ∘ blockEquiv hv) = v := funext (blockIncl_blockEquiv hv)
  rw [this]

theorem ringKrullDim_imageVar (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    ringKrullDim (Geo.MRingOver F ι ⧸ AI.I1.imageVar F v V') =
      ringKrullDim (NumbersDVR.MRing (fun k => ι' (emb hv k)) F ⧸
        FieldNumbers.contractPrime (emb hv) V') := by
  rw [imageVar_eq hv]
  set J := FieldNumbers.contractPrime (emb hv) V'
  let e := (renameEquiv F (blockEquiv hv)).toRingEquiv
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ J e ?_)
  exact (Ideal.map_comap_of_surjective _ e.surjective J).symm

end Image

end ProjContract


open ProjContract in
theorem ProjContract.full :
    ∀ (F : Type u) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjContractStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  classical
  intro I' hI' κ v V' e d L hv hV' hVd hde
  have hrel : FieldNumbers.relDim V' = e := (FieldNumbers.relDim_eq_iff_hasRelDim V' e).mpr hV'.2
  have hV'f : NumbersDVR.IsMultiProjPrime V' := (Bridge.isMultiProjPrime_iff V').mpr hV'.1
  rw [FieldNumbers.IntNumUnique.full F K' ι' I' (isIntersectionTheory I' hI') V' hV'f e hrel]
  have hc : FieldNumbers.relDim (FieldNumbers.contractPrime (emb hv) V') = d := by
    refine (FieldNumbers.relDim_eq_iff_hasRelDim _ d).mpr ?_
    show ringKrullDim _ = _
    rw [← ringKrullDim_imageVar hv]
    exact hVd.2
  exact FieldNumbers.ProjectionFormulaContracted.full F K K' (emb hv) ι' V' hV'f e hrel
    (lt_of_eq_of_lt hc (FieldNumbers.PFContracted.natCast_lt_withBotWithTop hde)) L

end

end GroundTheory.Heights₂.Heights.Targets
end
