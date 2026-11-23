module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle094
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle004
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj ptsIntegralAt pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def PtsIntegralSegreChartProj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin (e + 1) → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin (e + 1) → (Fin m → ℂ) → ℝ),
    IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
    IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ptsIntegralAt P Ψ (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def SegreChartIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin (e + 1) → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin (e + 1) → (Fin m → ℂ) → ℝ),
    IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g → 0 < δ →
    ((∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) ∨
      ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → pot L 0 z = 0) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ptsIntegral P (pot L) g = ∑ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def SegreChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (u v : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth u → IsDegZeroSmooth v →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → u z = 0) →
      ∃ (m : ℕ) (Js : Finset (Ideal (MvPolynomial (Fin m) ℂ))) (U V : (Fin m → ℂ) → ℝ)
        (Φ : Fin n → (Fin m → ℂ) → ℝ),
        (∀ J ∈ Js, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (n + 1 : ℕ) ∧
          SmoothNear (ComplexSets.zeroSet J) U ∧ SmoothNear (ComplexSets.zeroSet J) V ∧
          ∀ j, SmoothNear (ComplexSets.zeroSet J) (Φ j)) ∧
        HasCompactSupport U ∧
        ptsIntegral P (Fin.cons v (pot L)) u = ∑ J ∈ Js, varInt J (n + 1) U (Matrix.vecCons V Φ) ∧
        ptsIntegral P (Fin.cons u (pot L)) v = ∑ J ∈ Js, varInt J (n + 1) V (Matrix.vecCons U Φ)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt PBlk oneLine fsLine Xc)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift planeBump)

def ChartDivisorCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (δ : ℝ)
    (G : (Fin m → ℂ) → ℝ) (Φ : Fin n → (Fin m → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSectionOn P A s →
    IsDegZeroSmooth g → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    (∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) →
      ∑ J ∈ segreChartComponents P σ i,
          ∑ᶠ (W : Ideal (MvPolynomial (Fin m) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {chartSection σ i s}) W : ℝ) * varInt W n G Φ =
        ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def AmpleCountAlongMultiples.StatementAmple : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    KH.AmpleV ℚ (KH.genIdeal y) N.a →
    (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N.a - fun _ => 1)) →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (_root_.GroundTheory.Heights₂.Heights.HilbertSamuel.fibreIdeal ℓ y) N.a) →
    ∀ ε : ℝ, 0 < ε → ∃ b : ℕ, 1 ≤ b ∧ ∀ᶠ k : ℕ in atTop,
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
          (((b * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (b * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem MoriwakiBig.of_found (hG6 : HilbertSamuel.ArithmeticVolumeBig.Statement) (hC : MoriwakiBigCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact hC K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen
  · exact hG6 K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology Matrix ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet)

namespace PtsGenericCount

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e m : ℕ}

theorem mem_fibre_iff {P : Ideal (MRing ι)} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) (x : Fin m → ℂ) :
    (fun i' => x (σ.symm i')) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y ↔
      x ∈ projChartSet P σ Ψ ∧ chartProjMatrix σ Ψ *ᵥ x = y := by
  constructor
  · rintro ⟨z, hz, hzw, hΨ⟩
    have hx : x = fun a => segre z (σ a) := by
      funext a
      rw [hzw]
      simp
    refine ⟨⟨z, hz, by rw [hzw, hΨ]; rfl, hx⟩, ?_⟩
    funext r
    rw [chartProjMatrix_mulVec, hΨ]
    rfl
  · rintro ⟨⟨z, hz, h0, rfl⟩, hA⟩
    have hw : (fun i' => segre z (σ (σ.symm i'))) = segre z := by
      funext i'
      simp
    refine ⟨z, hz, hw.symm, ?_⟩
    rw [hw]
    funext j
    refine Fin.cases ?_ (fun r => ?_) j
    · rw [h0]
      rfl
    · have h := congrFun hA r
      rw [chartProjMatrix_mulVec, hw] at h
      rw [h]
      rfl

theorem proof (hA : GoodChartModel.Statement) (hB : ComponentsGenericCount.Statement)
    (hC : SheetLift.Statement) : PtsGenericCount.Statement := by
  classical
  intro K _ ι _ P e Ψ hP hΨ
  set σ := (Fintype.equivFin ((k : K) → ι k)).symm
  obtain ⟨hZ, hJ⟩ := hA K ι P e _ σ Ψ hP hΨ
  set I := projChartIdeal P σ Ψ
  set F := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).toFinset
  set A := chartProjMatrix σ Ψ
  have hF : ∀ J, J ∈ F ↔ J ∈ I.minimalPrimes := fun J => Set.Finite.mem_toFinset _

  have hU : ∀ x, (∃ J ∈ F, x ∈ zeroSet J) ↔ x ∈ projChartSet P σ Ψ := by
    intro x
    rw [← hZ]
    constructor
    · rintro ⟨J, hJF, hx⟩ q hq
      exact hx q (((hF J).1 hJF).1.2 hq)
    · intro hx
      have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => RingHom.mem_ker.2 (hx q hq)
      have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
      obtain ⟨J, hJm, hJle⟩ := Ideal.exists_minimalPrimes_le hle
      exact ⟨J, (hF J).2 hJm, fun q hq => RingHom.mem_ker.1 (hJle hq)⟩
  obtain ⟨hle, Δ, hΔ, hgen⟩ := hB _ e F A
    (fun J hJF => ⟨((hF J).1 hJF).1.1, hJ J ((hF J).1 hJF)⟩)
    (fun J hJF J' hJ'F hJJ' => le_antisymm hJJ' (((hF J').1 hJ'F).2 ((hF J).1 hJF).1 hJJ'))

  have hfib : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y = (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) ''
      {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} := by
    intro y
    ext w
    constructor
    · intro hw
      have hw' : (fun i' => (fun a => w (σ a)) (σ.symm i')) = w := by
        funext i'
        simp
      rw [← hw'] at hw
      obtain ⟨hxS, hxA⟩ := (mem_fibre_iff (P := P) σ Ψ y (fun a => w (σ a))).1 hw
      exact ⟨_, ⟨(hU _).2 hxS, hxA⟩, hw'⟩
    · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
      exact (mem_fibre_iff σ Ψ y x).2 ⟨(hU x).1 hxU, hxA⟩
  have hinj : Function.Injective (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) := by
    intro x x' h
    funext a
    simpa using congrFun h (σ a)
  have henc : ∀ y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).encard = {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard :=
    fun y => by rw [hfib y, hinj.injOn.encard_image]
  refine ⟨∑ J ∈ F, projDegree J A, fun y => (henc y).trans_le (hle y), ?_⟩
  refine measure_mono_null (fun y hy => ?_) (DiscriminantSheetCover.volume_zero_set Δ hΔ)
  by_contra h0
  obtain ⟨hcount, hsec⟩ := hgen y h0
  refine hy ⟨(henc y).trans hcount, fun w hw => ?_⟩
  rw [hfib y] at hw
  obtain ⟨x, ⟨hxU, hxA⟩, rfl⟩ := hw
  obtain ⟨U, g, hUo, hyU, hg, hgy, hgU⟩ := hsec x hxU hxA
  rw [← hgy]
  refine hC K ι P e Ψ y (fun y' i' => g y' (σ.symm i')) hP.2.1.2.1 ?_
  filter_upwards [hUo.mem_nhds hyU] with y' hy'
  obtain ⟨hAg, J, hJF, hgJ⟩ := hgU y' hy'
  obtain ⟨z, hz, hzw, hΨz⟩ := (mem_fibre_iff σ Ψ y' (g y')).2 ⟨(hU _).1 ⟨J, hJF, hgJ⟩, hAg⟩
  have hgd : DifferentiableAt ℂ g y' := hg.differentiableAt (hUo.mem_nhds hy')
  exact ⟨differentiableAt_pi.2 fun i' => differentiableAt_pi.1 hgd (σ.symm i'), ⟨z, hz, hzw⟩, hΨz⟩

end PtsGenericCount

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

universe u v w

theorem SegreComponent.full : SegreComponent.Statement.{u, v, w} :=
  SegreComponent.proof ChartDimBound.proof ChartFiniteIrrel.proof

theorem SegreDivisor.full : SegreDivisor.Statement.{u, v, w} :=
  SegreDivisor.proof SegreComponent.full

theorem Positivity.full {K : Type u} [Fintype K] (F : Type w) [Field F] (ι : K → Type v)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  Positivity.of_found SegreDivisor.full F ι

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsBilinear.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (T : Type) [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ)
    (v : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ t, IsDegZeroSmooth (u t)) →
    IsDegZeroSmooth v →
    ptsIntegral P (Fin.cons v (pot L)) (fun z => ∑ t, u t z) =
        ∑ t, ptsIntegral P (Fin.cons v (pot L)) (u t) ∧
      ptsIntegral P (Fin.cons (fun z => ∑ t, u t z) (pot L)) v =
        ∑ t, ptsIntegral P (Fin.cons (u t) (pot L)) v

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj ptsIntegralAt pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsIntegralProjIndep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    IsDegZeroSmooth g → ptsIntegralAt P Ψ (pot L) g = ptsIntegralAt P Ψ' (pot L) g

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u v w

theorem intNum_comp_perm {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)) :
    intNum F P (bs ∘ σ) = intNum F P bs := by
  unfold intNum
  rw [FieldNumbers.mixedDiff_comp_perm]

theorem SymmStatement.of_type (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] : SymmStatement F ι := by
  classical
  intro I hI V n L σ hV
  have hA : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI V n L' hV
  rw [hA (L ∘ σ), hA L]
  exact intNum_comp_perm V L σ

theorem SymmStatement.of_found (hR : SymmRelabel.Statement.{u, v, w, 0, 0}) {K : Type v}
    [Fintype K] (F : Type u) [Field F] (ι : K → Type w) [∀ k, Fintype (ι k)] :
    SymmStatement F ι := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  refine hR F K ι (Fin (Fintype.card K)) (fun j => Fin (Fintype.card (ι (e.symm j)))) e
    (fun k => (Fintype.equivFin (ι k)).trans (finCongr ?_)) (SymmStatement.of_type F _)
  exact congrArg (fun x => Fintype.card (ι x)) (e.symm_apply_apply k).symm

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj sheetDensity pot PBlk oneLine
  isSmoothHerm_oneLine)
open ComplexSets

def PtsSegreChartFibreSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth g →
    IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
      ∀ᵐ y, ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (pot L) g y w =
        ∑ J ∈ segreChartComponents P σ i,
          chartDens J (chartProjMatrix σ Ψ) (chartWeight σ i g) (chartPot σ i L) y

end GroundTheory.Heights₂.Heights
end
end
