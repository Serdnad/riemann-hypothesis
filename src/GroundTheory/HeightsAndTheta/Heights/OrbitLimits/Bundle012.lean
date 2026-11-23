module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle076
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal multAt PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartComponents localMult)


open Classical in
def ChartDivisorLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        ∑ J ∈ (segreChartComponents P σ i).filter (fun J => J ≤ W'),
            localMult (J ⊔ Ideal.span {chartSection σ i s}) W' =
          multAt (P ⊔ Ideal.span {s}) W

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal multAt PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents localMult)

def ChartSectionLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
          multAt (P ⊔ Ideal.span {s}) W

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

namespace LelongWeightDiff

variable {n d : ℕ}

theorem abs_half_log_sub_le {a ε κ : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hκ : 0 < κ) :
    |Real.log (a + ε * κ ^ 2) / 2 - Real.log (a + ε) / 2| ≤ |Real.log κ| := by
  have hb : 0 < a + ε := by linarith
  have hc : 0 < a + ε * κ ^ 2 := by positivity
  have hk2 : Real.log (κ ^ 2) = 2 * Real.log κ := by rw [Real.log_pow]; norm_num
  rcases le_total 1 κ with h1 | h1
  · have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ h1
    have l1 : Real.log (a + ε) ≤ Real.log (a + ε * κ ^ 2) := Real.log_le_log hb (by nlinarith)
    have l2 : Real.log (a + ε * κ ^ 2) ≤ Real.log (κ ^ 2) + Real.log (a + ε) := by
      rw [← Real.log_mul (by positivity) hb.ne']; exact Real.log_le_log hc (by nlinarith)
    rw [abs_of_nonneg (Real.log_nonneg h1), abs_le]; constructor <;> linarith
  · have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le h1
    have l1 : Real.log (a + ε * κ ^ 2) ≤ Real.log (a + ε) := Real.log_le_log hc (by nlinarith)
    have l2 : Real.log (κ ^ 2) + Real.log (a + ε) ≤ Real.log (a + ε * κ ^ 2) := by
      rw [← Real.log_mul (by positivity) hb.ne']; exact Real.log_le_log (by positivity) (by nlinarith)
    rw [abs_of_nonpos (Real.log_nonpos hκ.le h1), abs_le]; constructor <;> linarith

theorem exists_poly_of_linEval_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (u : Fin n → ℂ) (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) P = 0 := by
  classical
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  have hs0 : Ideal.Quotient.mk J (linForm u) ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hex : ∃ m, ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g.Monic ∧ g.natDegree = m ∧
      Polynomial.aeval (Ideal.Quotient.mk J (linForm u)) g = 0 := by
    obtain ⟨g, hgm, -, hg⟩ := FibreBound.exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (linForm u))
    exact ⟨_, g, hgm, rfl, hg⟩
  obtain ⟨g, hgm, hgd, hg⟩ := Nat.find_spec hex
  have hc : g.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hgm
    rw [map_mul, Polynomial.aeval_X] at hg
    refine Nat.find_min hex (m := q.natDegree) ?_ ⟨q, hqm, rfl, (mul_eq_zero.mp hg).resolve_left hs0⟩
    rw [← hgd, Polynomial.natDegree_mul Polynomial.X_ne_zero hqm.ne_zero, Polynomial.natDegree_X]
    omega
  refine ⟨g.coeff 0, hc, fun x hx hux => ?_⟩
  have hmem : Polynomial.eval₂ (pullback A).toRingHom (linForm u) g ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
    rw [Polynomial.aeval_def] at hg
    exact hg
  have h0 := hx _ hmem
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A *ᵥ x) :=
    RingHom.ext fun P => FibreBound.eval_pullback A x P
  have hl : eval x (linForm u) = linEval u x := by simp [linForm, linEval]
  rwa [Polynomial.hom_eval₂, hcomp, hl, hux, Polynomial.eval₂_at_zero] at h0

theorem measurable_chartDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hf : ContinuousOn f (zeroSet J)) (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) :
    Measurable (chartDens J A f ψ) := by
  classical
  rw [CutOffDominated.chartDens_congr_zeroSet (g := (zeroSet J).piecewise f 0)
    (fun x hx => (Set.piecewise_eq_of_mem _ _ _ hx).symm)]
  exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA
    (hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet) hψ).1

theorem abs_chartDens_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite) :
    |chartDens J A f ψ y| ≤ chartAbsDens J A f ψ y := by
  classical
  unfold chartDens chartAbsDens
  simp only [CutOffDominated.sheetSum_eq_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs <;> simp

theorem chartDens_sub {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f f' : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (_root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite) :
    chartDens J A f ψ y - chartDens J A f' ψ y = chartDens J A (fun x => f x - f' x) ψ y := by
  classical
  unfold chartDens
  simp only [CutOffDominated.sheetSum_eq_sum _ hfin, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem tendsto_finset_sum_zero {ι α : Type*} {l : Filter α} (s : Finset ι) (f : ι → α → ℝ)
    (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 0)) : Tendsto (fun a => ∑ i ∈ s, f i a) l (𝓝 0) := by
  simpa using tendsto_finsetSum s h

end LelongWeightDiff

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix

section Proj

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


open Classical in
def chartProjMatrix {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) : Matrix (Fin d) (Fin m) ℂ :=
  fun r a => Ψ (fun i' => if σ a = i' then 1 else 0) r.succ

theorem chartProjMatrix_mulVec {m d : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) (x : Fin m → ℂ) (r : Fin d) :
    (chartProjMatrix σ Ψ *ᵥ x) r = Ψ (fun i' => x (σ.symm i')) r.succ := by
  classical
  have hv : (fun i' => x (σ.symm i')) = ∑ a, x a • fun i' => if σ a = i' then (1 : ℂ) else 0 := by
    rw [pi_eq_sum_univ (fun i' => x (σ.symm i'))]
    exact (Equiv.sum_comp σ _).symm.trans (by simp)

  rw [hv, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, chartProjMatrix]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

end Proj

section Chart

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def chartLiftDom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∀ k, ∃ j, chartLift σ i x ⟨k, j⟩ ≠ 0}

theorem isOpen_chartLiftDom {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    IsOpen (chartLiftDom σ i) :=
  ReciprocityTheory.ChartRestriction.G.Geo.isOpen_blockNonzero.preimage (contDiff_chartLift σ i (n := 0)).continuous

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_chartLiftDom_of_coord {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) : x ∈ chartLiftDom σ i :=
  chartLift_blockNonzero σ i hx


open Classical in
def chartWeight {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : (Fin m → ℂ) → ℝ :=
  (chartLiftDom σ i).piecewise (g ∘ chartLift σ i) 0

def chartPot {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (L : Fin e → HermLine ι) :
    Fin e → (Fin m → ℂ) → ℝ :=
  fun j => pot L j ∘ chartLift σ i

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartWeight_of_mem {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x ∈ chartLiftDom σ i) :
    chartWeight σ i g x = g (chartLift σ i x) := by
  classical
  simp only [chartWeight]
  rw [Set.piecewise_eq_of_mem _ _ _ hx]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartWeight_of_coord {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) :
    chartWeight σ i g x = g (chartLift σ i x) :=
  chartWeight_of_mem g (mem_chartLiftDom_of_coord hx)

theorem measurable_chartWeight {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) : Measurable (chartWeight σ i g) := by
  classical
  have hc : ContinuousOn (g ∘ chartLift σ i) (chartLiftDom σ i) :=
    hg.1.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn fun _ hx => hx
  unfold chartWeight
  exact hc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) (isOpen_chartLiftDom σ i).measurableSet

theorem smoothNear_chartPot {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Set (Fin m → ℂ)}
    (hT : ∀ x ∈ T, x (σ.symm i) = 1) (j : Fin e) : SmoothNear T (chartPot σ i L j) := by
  refine ⟨chartLiftDom σ i, isOpen_chartLiftDom σ i, fun x hx => mem_chartLiftDom_of_coord (hT x hx), ?_⟩
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (L j).h (chartLift σ i x)) (chartLiftDom σ i) :=
    (hL j).comp (contDiff_chartLift σ i).contDiffOn fun _ hx => hx
  exact hh.log fun x hx => ((L j).pos _ hx).ne'

end Chart

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveClosedPointChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
        ∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 → Module.Finite ℤ (curveRing y)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def CurveVertIndex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s =
        Real.log (genIndex (chartLat y (fun k => (d k : ℤ)) 1) (curveMul y (aeval y s)))

namespace CurveVertIndex

end CurveVertIndex

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartDehomogPrime.proof : ChartDehomogPrime.Statement := by
  intro F _ n W t hW ht
  have := hW.isPrime
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  have : IsDomain A := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    exact (DFunLike.congr_fun (MvPolynomial.aeval_unique φ) g).symm
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g :=
    fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _
  have hℓ : (linForm t).IsHomogeneous 1 := ChartLocDomain.linForm_isHomogeneous t
  have hspan : Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      hhom hℓ, pow_one]
    have : φ (linForm t) = algebraMap _ A a := rfl
    rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  have hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) hspan

    rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hhom (homogeneousComponent_isHomogeneous k g)]
    have : φ (homogeneousComponent k g) = 0 := by
      simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hW.isHomog g hg k)]
    rw [this, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hker : RingHom.ker ψ ≤ W ⊔ Ideal.span {linForm t - 1} := by
    intro g hg
    obtain ⟨G, D, hG, hGg⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) g hℓ
    have hψG : ψ G = 0 := by
      have h1 : ψ (G - g) = 0 := hspan hGg
      rw [map_sub, RingHom.mem_ker.mp hg, sub_zero] at h1
      exact h1
    rw [hhom hG] at hψG
    have h1 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 :=
      calc algebraMap _ A (Ideal.Quotient.mk W G)
          = (algebraMap _ A a * v) ^ D * φ G := by
            rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul]; rfl
        _ = algebraMap _ A a ^ D * (v ^ D * φ G) := by ring
        _ = 0 := by rw [hψG, mul_zero]
    have hGW : G ∈ W := Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm))
    have e : g = G - (G - g) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
  rw [← le_antisymm hker hle]
  exact RingHom.ker_isPrime ψ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem ChartDimBound.proof : ChartDimBound.Statement.{u, v, w} := by
  intro K _ ι _ F _ V i hV hi
  classical
  obtain ⟨hVp, hVh, -⟩ := hV
  let f : K → MRingOver F ι := fun k => X ⟨k, i k⟩ - 1
  let t : Set (MRingOver F ι ⧸ V) := Set.range (Ideal.Quotient.mk V ∘ f)
  have hspan : Ideal.span t = (Ideal.span (Set.range f)).map (Ideal.Quotient.mk V) := by
    rw [Ideal.map_span, ← Set.range_comp]
  let e : (MRingOver F ι ⧸ V) ⧸ Ideal.span t ≃+* MRingOver F ι ⧸ _root_.ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i :=
    (Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup V _)
  have : IsDomain (MRingOver F ι ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType F (MRingOver F ι ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F V) (Ideal.Quotient.mkₐ_surjective F V)
  have : IsNoetherianRing (MRingOver F ι ⧸ V) := Algebra.FiniteType.isNoetherianRing F _
  have hne : Ideal.span t ≠ ⊤ := by
    have : Nontrivial (MRingOver F ι ⧸ _root_.ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) :=
      Ideal.Quotient.nontrivial_iff.mpr (chartIdeal_ne_top hVh hi)
    have : Nontrivial ((MRingOver F ι ⧸ V) ⧸ Ideal.span t) := e.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp this
  obtain ⟨M, hM, htM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs⟩ := DimF.exists_height_of_isMaximal_of_field F (MRingOver F ι ⧸ V)
  have : M.IsPrime := hM.isPrime
  have h1 := Ideal.height_le_ringKrullDim_quotient_add_encard (p := M) t
    (fun x hx => htM (Ideal.subset_span hx))
  rw [ringKrullDim_eq_of_ringEquiv e] at h1
  have h2 : t.encard ≤ Fintype.card K := by
    calc t.encard = ((Ideal.Quotient.mk V ∘ f) '' Set.univ).encard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set K).encard := Set.encard_image_le _ _
      _ = Fintype.card K := by simp [Set.encard_univ]
  refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun N hN => ?_
  rw [hs N hN, ← hs M hM]
  refine h1.trans ?_
  gcongr
  exact_mod_cast h2

end GroundTheory.Heights₂.Heights.Targets
end
