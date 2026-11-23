module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure AnRes (P J : Ideal (MRing ι)) (e : ℕ) where

  homog : IsMultiHomogIdeal J

  nondeg : ¬ J ≤ P

  X : Type
  [top : TopologicalSpace X]
  [compact : CompactSpace X]
  [t2 : T2Space X]

  A : FinHolAtlas e X

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  lift : X → X → (Σ k, ι k) → ℂ
  holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p)
  mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P

  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)

  surj : ∀ z ∈ mcPts P, z ∉ mcPts J → ∃ x, SameOrbit (lift x x) z

  inj : ∀ x x', lift x x ∉ mcPts J → SameOrbit (lift x x) (lift x' x') → x = x'

  null : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts J}) = 0

attribute [instance] AnRes.top AnRes.compact AnRes.t2

def _root_.ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes.toAnRes {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) :
    AnRes P J e where
  homog := R.homog
  nondeg := R.nondeg
  X := R.X
  A := R.A
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  lift := R.lift
  holo := R.holo
  mem := R.mem
  compat := R.compat
  surj := R.surj
  inj := R.inj
  null := R.null

def IsSmoothVolume {e : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (A : FinHolAtlas e X)
    (dV : Measure X) : Prop :=
  IsProbabilityMeasure dV ∧ ∀ j, ∃ ν : (Fin e → ℂ) → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν (A.chart j).target ∧ (∀ y ∈ (A.chart j).target, 0 < ν y) ∧
    ∀ S : Set X, MeasurableSet S → S ⊆ (A.chart j).source →
      dV S = ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S, ENNReal.ofReal (ν y)

structure HSMDatum (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] where

  x : Ix κ → Ω

  m : ConeMetric ℂ (Ix κ)

  P0 : Ideal (MRing (GlobalTheory κ))

  J : Ideal (MRing (GlobalTheory κ))

  R : AnRes (ι := GlobalTheory κ) (coordIdeal ℤ x) J D
  [meas : MeasurableSpace R.X]
  [borel : BorelSpace R.X]

  dV : Measure R.X
  one_le : 1 ≤ D
  arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
  indep : LinearIndependent ℤ x
  smooth : IsSmoothMetric m
  conjInv : IsConjInvariant m
  normalForm_baseLattice_le_dualSpan_sup_line : P0 ≤ coordIdeal ℤ x
  semipos : IsSemipositiveRel P0 (coordIdeal ℤ x) (HermLine.ofCone m)
  vol : IsSmoothVolume R.A dV

attribute [instance] HSMDatum.meas HSMDatum.borel

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resPt (d : HSMDatum D Ω κ) (y : d.R.X) : Ix κ → ℂ := d.R.lift y y

def pairVal (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) : ℂ :=
  eval z (map (algebraMap ℚ ℂ) b) * conj (eval z (map (algebraMap ℚ ℂ) b')) / ((m.ρ z ^ (2 * n) : ℝ) : ℂ)

def resGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun k l => (1 / 2) * ((∫ y, pairVal d.m n (b k) (b l) (resPt d y) ∂d.dV).re +
    (∫ y, pairVal d.m n (b k) (b l) (conjPt (resPt d y)) ∂d.dV).re)


open Classical in
def resChi (d : HSMDatum D Ω κ) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 then
    -(1 / 2) * Real.log (resGram d n h.choose.2).det
  else 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def CoordArithOfFnField.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (d : ℕ),
    Nonempty K' → (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y = blockFnField y' →
    IsArithVar (mCoordIdeal y) d → IsArithVar (mCoordIdeal y') d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def TopConstantTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (c : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → IsSmoothHerm A →
    II K ι P (D + 1) (fun _ => A.tensor (constLine c)) =
      II K ι P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

section Def

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def HermLine.constShift (A : HermLine ι) (η : ℝ) : HermLine ι :=
  A.tensor (HermLine.ofWeight (fun _ => η) (fun _ _ _ => rfl))

end Def

def ConstantShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (η : ℝ),
    IsIntersectionFamily I → IsArithVar P (D + 1) → IsSmoothHerm A →
    I P (D + 1) (fun _ => HermLine.constShift A η) =
      I P (D + 1) (fun _ => A) - ((D : ℝ) + 1) * η * geomDeg P A D

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def LocalRep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ),
    s ∈ chartLat y a n → z ∈ mcPts (mCoordIdeal y) →
    ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + n * a k) ∧ aeval y g = s * aeval y h ∧
      eval z (map (Int.castRingHom ℂ) h) ≠ 0

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def HasCommonZeroModP (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∃ z : (Σ k, ι k) → AlgebraicClosure (ZMod p), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
    (∀ f ∈ mCoordIdeal y, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) = 0) ∧
    ∀ j, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) (L j)) = 0

end Defs

def FibreNormBadPrimesFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    {p : ℕ | ∃ hp : p.Prime, HasCommonZeroModP y L p hp}.Finite

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionLatticeFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (chartLat y a n).FG

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def pullField (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {x | ∃ i j, aeval y (L j) ≠ 0 ∧ x = aeval y (L i) / aeval y (L j)}

end Defs

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def intsIn (F Ω : Type*) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] : Subalgebra ℤ Ω :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.range

def ChartConstantsDetermined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ w w' : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : chartRingZ y c ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def ConstantsRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (θ : 𝓞 F) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (N : Ω) * algebraMap F Ω (θ : F) ∈ chartRingZ y c

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def EmbeddingWeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (Λ : (F →+* ℂ) → ℝ),
    (∀ sg, 0 < Λ sg) → (∀ sg, Λ (NumberField.ComplexEmbedding.conjugate sg) = Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧
      ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField

def TwistMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (u : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ c : ℝ, ∀ δ : ℝ, 0 < δ → ∃ A' : HermLine ι, A'.a = A.a ∧
      IsSemipositiveRel P0 (mCoordIdeal y) A' ∧ IsConjInvariantH A' ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
        A'.h z = Real.exp (u sg + δ) * A.h z) ∧
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A') ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + c * δ

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
