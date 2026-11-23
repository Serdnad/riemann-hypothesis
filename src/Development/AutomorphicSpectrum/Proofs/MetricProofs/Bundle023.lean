module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle015
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminant
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicGroupLawGerm
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle013
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle016
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeakConvergenceOffZeroSet
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle017
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem analyticAt_entry_tail {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ) (p q : Fin 2) :
    AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => g (Fin.tail z') p q) z := by
  have hT : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => (Fin.tail z' : Fin d → ℂ)) z := by
    rw [analyticAt_pi_iff]
    intro i
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).analyticAt z
  have hA : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail z) :=
    ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
  exact hA.comp hT

theorem analyticAt_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ)
    (h : den (g (Fin.tail z)) (z 0) ≠ 0) : AnalyticAt ℂ (mob1 g) z := by
  have hc0 : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => z' 0) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt z
  have e := analyticAt_entry_tail g hg z
  have hnum : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ =>
      g (Fin.tail z') 1 0 + g (Fin.tail z') 1 1 * z' 0) z := (e 1 0).add ((e 1 1).mul hc0)
  have hden : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => den (g (Fin.tail z')) (z' 0)) z :=
    (e 0 0).add ((e 0 1).mul hc0)
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hnum.div hden h
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) j.succ).analyticAt z

theorem hasDerivAt_mob_shift (m : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den m a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob m (a + t)) (mobD m a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => m 1 0 + m 1 1 * (a + t)) (m 1 1 * 1) 0 :=
    (hl.const_mul (m 1 1)).const_add (m 1 0)
  have hd : HasDerivAt (fun t : ℂ => den m (a + t)) (m 0 1 * 1) 0 :=
    (hl.const_mul (m 0 1)).const_add (m 0 0)
  have h0 : den m (a + 0) ≠ 0 := by simpa using h
  have hq := hn.div hd h0
  have e1 : (m 1 1 * 1 * den m (a + 0) - (m 1 0 + m 1 1 * (a + 0)) * (m 0 1 * 1)) / den m (a + 0) ^ 2 =
      mobD m a := by
    simp only [add_zero, mobD, Matrix.det_fin_two]
    congr 1
    simp only [den]
    ring
  rw [e1] at hq
  exact hq

theorem det_jacobian_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a : ℂ)
    (h : den (g y) a ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob1 g) (Fin.cons a y : Fin (d + 1) → ℂ)).det = mobD (g y) a := by
  set z : Fin (d + 1) → ℂ := Fin.cons a y with hz
  have htail : (Fin.tail z : Fin d → ℂ) = y := Fin.tail_cons _ _
  have hz0 : z 0 = a := Fin.cons_zero _ _
  have hF : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z) z :=
    (analyticAt_mobius_first g hg z (by rwa [htail, hz0])).differentiableAt.hasFDerivAt

  have hrow : ∀ (i : Fin d) (v : Fin (d + 1) → ℂ), fderiv ℂ (mob1 g) z v i.succ = v i.succ := by
    intro i v
    have h1 := (hasFDerivAt_pi'.1 hF) i.succ
    have h2 : HasFDerivAt (fun z' : Fin (d + 1) → ℂ => mob1 g z' i.succ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ) z :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).hasFDerivAt
    exact DFunLike.congr_fun (h1.unique h2) v

  have hcorner : fderiv ℂ (mob1 g) z (Pi.single 0 1) 0 = mobD (g y) a := by
    have hc : HasDerivAt (fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ))
        (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single 0 1 : Fin (d + 1) → ℂ)).const_add z
    have hF' : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z)
        (z + (0 : ℂ) • (Pi.single 0 1 : Fin (d + 1) → ℂ)) := by simpa using hF
    have hcomp := hF'.comp_hasDerivAt (0 : ℂ) hc
    have h0 := (hasDerivAt_pi.1 hcomp) 0
    have hline : ∀ t : ℂ, (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0 =
        mob (g y) (a + t) := by
      intro t
      have ht : (Fin.tail (z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) : Fin d → ℂ) = y := by
        rw [← htail]
        funext i
        simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
      simp only [Function.comp, mob1, Fin.cons_zero, ht]
      simp [hz0]
    have h3 : HasDerivAt (fun t : ℂ => (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0)
        (mobD (g y) a) 0 := by
      simpa only [hline] using hasDerivAt_mob_shift (g y) a h
    exact h0.unique h3
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz1 : ∀ i : Fin d, ReciprocityTheory.AnForm.A.jacC (mob1 g) z i.succ 0 = 0 := by
    intro i
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Fin.succ_ne_zero]
  have hminor : (ReciprocityTheory.AnForm.A.jacC (mob1 g) z).submatrix (Fin.succAbove 0) Fin.succ = 1 := by
    ext i j
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Matrix.one_apply, Fin.succ_inj]
  simp only [hz1, hminor]
  simp [ReciprocityTheory.AnForm.A.jacC, hcorner]

theorem analyticAt_mobius_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧
      (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det =
        GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  intro d g hg y a h
  refine ⟨analyticAt_mobius_first g hg _ ?_, det_jacobian_mobius_first g hg y a h⟩
  rwa [Fin.tail_cons, Fin.cons_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.normalized_degree_le_rank_mul_slope : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | exact GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | (intros; apply GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.regular_chart_data_properties : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A), IsOpen R.Yo ∧ (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yoᶜ) = 0) ∧ ContinuousOn R.r R.Yo ∧ ∀ ℓ : ℝ, IsCompact {x | x ∈ R.Yo ∧ R.r x ≤ ℓ} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part | exact GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part <;> assumption)
end

section

open Set Filter Topology

theorem _root_.GlobalTheory.T.holomorphic_group_law_germ : ∀ (n g : ℕ) (b₀ : Fin n → ℂ) (μ : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ μ (b₀, 0, 0) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), μ (p.1, p.2, 0) = p.2 ∧ μ (p.1, 0, p.2) = p.2) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1)) → (∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0, 0), μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) → ∃ L : (Fin n → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧ HasFDerivAt (fun s => L (b, s)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ ∀ᶠ p : (Fin n → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0), L (p.1, μ p) = L (p.1, p.2.1) + L (p.1, p.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_local_log_of_commutative_law <;> assumption)
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near :
    ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) →
      (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) →
      ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧
        IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧
        (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧
        (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  intro d G y hpd hC
  let Gh : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ := fun y' => (1 / 2 : ℂ) • (G y' + (G y')ᴴ)
  have hent : ∀ y' p q, Gh y' p q = (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) := by
    intro y' p q
    simp [Gh, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
    ring
  have hherm : ∀ y', (Gh y').IsHermitian := by
    intro y'
    ext p q
    rw [Matrix.conjTranspose_apply, hent, hent]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      apply Complex.ext <;> simp
    simp only [RCLike.star_def, map_mul, map_add (f := _), Complex.conj_conj, hhalf]
    ring
  have hEq : ∀ᶠ y' in 𝓝 y, Gh y' = G y' := by
    filter_upwards [hpd] with y' h
    have e : (G y')ᴴ = G y' := h.isHermitian.eq
    ext p q
    simp only [Gh, e, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hy : Gh y = G y := hEq.self_of_nhds
  have hpdy : (Gh y).PosDef := by
    rw [hy]
    exact hpd.self_of_nhds
  have hCh : ∀ p q, ContDiffAt ℝ 2 (fun y' => Gh y' p q) y := by
    intro p q
    have h1 := hC p q
    have h2 : ContDiffAt ℝ 2 (fun y' => (starRingEnd ℂ) (G y' q p)) y :=
      Complex.conjCLE.contDiff.contDiffAt.comp y (hC q p)
    have e : (fun y' => Gh y' p q) = fun y' => (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) :=
      funext fun y' => hent y' p q
    rw [e]
    exact contDiffAt_const.mul (h1.add h2)
  obtain ⟨g, hg, hu, h1, hd⟩ := GlobalTheory.T.exists_holomorphic_normal_frame d Gh y hpdy hherm hCh
  refine ⟨g, hg, hu, ?_, GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry G g y hC hg, ?_, ?_⟩
  · have hc : ∀ p q, ContinuousAt (fun y' => g y' p q) y := fun p q => (hg p q).continuous.continuousAt
    have hdetc : ContinuousAt (fun y' => (g y').det) y := by
      simp only [Matrix.det_fin_two]
      exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
    have hne : ∀ᶠ y' in 𝓝 y, (g y').det ≠ 0 := hdetc.eventually_ne hu.ne_zero
    filter_upwards [hpd, hne] with y' ha hb
    exact (GlobalTheory.T.log_sine_mobius_transform (G y') (g y') ha (isUnit_iff_ne_zero.mpr hb)).1
  · rw [← hy]
    exact h1
  · intro p q
    have hev : (fun y' => ((g y')ᴴ * G y' * g y') p q) =ᶠ[𝓝 y] fun y' => ((g y')ᴴ * Gh y' * g y') p q := by
      filter_upwards [hEq] with y' h
      rw [h]
    rw [hev.fderiv_eq]
    exact hd p q
end

section

open Set

theorem _root_.GlobalTheory.T.holomorphic_lattice_family_local : ∀ (n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Countable Λ] (B : Set (Fin n → ℂ)), IsOpen B → Convex ℝ B → ∀ (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ) (e : Λ → Λ → ℝ), (∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) N) ∧ ∀ b ∈ N, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y) → ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_global_marking_of_local | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_global_marking_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_global_marking_of_local <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem gram_grad_scale_arith (D c P Q a : ℝ) (ha : 0 < a) (hP : 0 < P) (hQ : 0 < Q)
    (h : P / Q * D ≤ c * P ^ 3 / a) : D ≤ c * P ^ 2 * Q / a := by
  have h1 : D = Q / P * (P / Q * D) := by field_simp
  have h2 : 0 ≤ Q / P := (div_pos hQ hP).le
  calc D = Q / P * (P / Q * D) := h1
    _ ≤ Q / P * (c * P ^ 3 / a) := mul_le_mul_of_nonneg_left h h2
    _ = c * P ^ 2 * Q / a := by field_simp

theorem gram_grad_comp_smul (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x' : E) (a P t : ℝ)
    (ha : 0 < a) (hP : 0 < P)
    (h1 : ∀ p q, DifferentiableAt ℝ (fun y => G (t • y) p q) x')
    (h2 : ∀ p q, DifferentiableAt ℝ (fun y => V (t • y) p q) x')
    (h3 : ∀ᶠ y in nhds x', (G (t • y)).PosDef ∧ LinearIndependent ℂ (V (t • y))ᵀ)
    (h4 : ((V (t • x'))ᴴ * G (t • x') * V (t • x') -
      (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef)
    (h5 : ∀ p q, ‖G (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G (t • y) p q) x'‖ ≤ P)
    (h6 : ∀ p q, ‖V (t • x') p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V (t • y) p q) x'‖ ≤ P) :
    ‖fderiv ℝ (fun y => Real.log ((V (t • y))ᴴ * G (t • y) * V (t • y)).det.re) x'‖ ≤
      3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 3 / a :=
  GlobalTheory.T.log_det_gram_subharmonic n k E (fun u => G (t • u)) (fun u => V (t • u)) x' a P ha hP.le h1 h2 h3 h4 h5 h6

theorem gram_grad_scaled : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a P Q : ℝ), 0 < a → 0 < P → P ≤ Q → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ Q) → (∀ p q, ‖V x p q‖ ≤ P ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ Q) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * P ^ 2 * Q / a := by
  intro n k E _ _ G V x a P Q ha hP hPQ hGd hVd hev hH hGb hVb
  have hQ : 0 < Q := lt_of_lt_of_le hP hPQ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = P / Q := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ div_pos hP hQ
  have htne : t ≠ 0 := ht0.ne'
  obtain ⟨x', hx'⟩ : ∃ x' : E, x' = t⁻¹ • x := ⟨_, rfl⟩
  have hcx : t • x' = x := by rw [hx', smul_smul, mul_inv_cancel₀ htne, one_smul]
  have hL : DifferentiableAt ℝ (fun u : E => t • u) x' := (differentiableAt_id).const_smul t
  have hdiff : ∀ f : E → ℂ, DifferentiableAt ℝ f x →
      DifferentiableAt ℝ (fun u => f (t • u)) x' := by
    intro f hf
    have hf' : DifferentiableAt ℝ f (t • x') := by rw [hcx]; exact hf
    exact hf'.comp x' hL
  have hfd : ∀ f : E → ℂ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hfdR : ∀ f : E → ℝ, fderiv ℝ (fun u => f (t • u)) x' = t • fderiv ℝ f x := by
    intro f
    rw [fderiv_comp_smul, hcx]
  have hbound : ∀ f : E → ℂ, ‖fderiv ℝ f x‖ ≤ Q →
      ‖fderiv ℝ (fun u => f (t • u)) x'‖ ≤ P := by
    intro f hf
    rw [hfd, norm_smul, Real.norm_of_nonneg ht0.le, ht]
    calc P / Q * ‖fderiv ℝ f x‖ ≤ P / Q * Q := mul_le_mul_of_nonneg_left hf (div_pos hP hQ).le
      _ = P := by field_simp
  have htend : Tendsto (fun u : E => t • u) (nhds x') (nhds x) := by
    have := hL.continuousAt.tendsto
    rwa [hcx] at this
  have key := gram_grad_comp_smul n k E G V x' a P t ha hP
    (fun p q => hdiff (fun y => G y p q) (hGd p q))
    (fun p q => hdiff (fun y => V y p q) (hVd p q))
    (htend.eventually hev)
    (by rw [hcx]; exact hH)
    (fun p q => ⟨by rw [hcx]; exact (hGb p q).1, hbound (fun y => G y p q) (hGb p q).2⟩)
    (fun p q => ⟨by rw [hcx]; exact (hVb p q).1, hbound (fun y => V y p q) (hVb p q).2⟩)
  have hk := hfdR (fun y => Real.log ((V y)ᴴ * G y * V y).det.re)
  rw [hk, norm_smul, Real.norm_of_nonneg ht0.le, ht] at key
  exact gram_grad_scale_arith _ _ P Q a ha hP hQ key

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.C2_tendsto_pullback_through_chart : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ)) (g : ℝ → (Fin e → ℂ) → ℝ) (p : (Fin e → ℂ) → ℝ) (K' : Set (Fin e → ℂ)), K' ⊆ c.target → (TendstoUniformlyOn g p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (g t))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (g t) z - fderiv ℝ p z‖ ≤ M * t) → (TendstoUniformlyOn (fun t => (g t ∘ c) ∘ c.symm) p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ ((g t ∘ c) ∘ c.symm)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((g t ∘ c) ∘ c.symm))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ ((g t ∘ c) ∘ c.symm) z - fderiv ℝ p z‖ ≤ M * t) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback | exact GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback | (intros; apply GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback <;> assumption)
end

section

open Complex Metric

theorem _root_.GlobalTheory.T.removable_log_growth_singularity : ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ → DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} → (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) → ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.weak_convergence_off_zero_set : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (μT : ℝ → Measure X) (N : X → ℝ), IsFiniteMeasure μ → (∀ᶠ t in 𝓝[>] (0 : ℝ), IsFiniteMeasure (μT t)) → Continuous N → (∀ y, 0 ≤ N y ∧ N y ≤ 1) → μ {y | N y = 0} = 0 → (∀ᶠ t in 𝓝[>] (0 : ℝ), μT t {y | N y = 0} = 0) → (∀ (g : X → ℝ) (B : ℝ), Continuous g → (∀ y, |g y| ≤ B) → Tendsto (fun t => ∫ y, g y ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, g y ∂μ))) → (∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (fun y => Real.log (1 + ε / N y ^ 2)) (μT t) ∧ ∫ y, Real.log (1 + ε / N y ^ 2) ∂μT t ≤ η) → Integrable (fun y => -Real.log (N y)) μ ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable (fun y => -Real.log (N y)) (μT t)) ∧ Tendsto (fun t => ∫ y, -Real.log (N y) ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, -Real.log (N y) ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small | exact GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.log_bound_transfer_between_radii : ∀ (C₅ M : ℝ), ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.BoundConv.bound_conv | exact GlobalTheory.CompanionTheory.Metric.BoundConv.bound_conv | (intros; apply GlobalTheory.CompanionTheory.Metric.BoundConv.bound_conv <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.Moebius

private theorem transcendental_of_mul_add_eq_mul {S K : Type*} [CommRing S] [IsDomain S] [Field K]
    [Algebra S K] {x t : K} {p q r : S} (hx : Transcendental S x)
    (hp : algebraMap S K p ≠ 0) (hr : algebraMap S K r ≠ 0)
    (h : t * (algebraMap S K p + x * algebraMap S K q) = x * algebraMap S K r) :
    Transcendental S t := by
  intro ht
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isAlgebraic_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact mul_ne_zero hx0 hr h.symm
  have hE : algebraMap S K r - t * algebraMap S K q ≠ 0 := by
    intro hE
    have h2 : t * algebraMap S K p = x * (algebraMap S K r - t * algebraMap S K q) := by
      linear_combination h
    rw [hE, mul_zero] at h2
    exact mul_ne_zero ht0 hp h2
  have hxe : x = t * algebraMap S K p * (algebraMap S K r - t * algebraMap S K q)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hE]
    linear_combination -h
  apply hx
  rw [hxe]
  exact (ht.mul (isAlgebraic_algebraMap p)).mul
    ((isAlgebraic_algebraMap r).sub (ht.mul (isAlgebraic_algebraMap q))).inv

theorem exists_ratFunc_embedding_moebius : ∀ (Φ S : Type) [Field Φ] [CommRing S] [IsDomain S] [Algebra Φ S] (p q r : S), p ≠ 0 → r ≠ 0 → ∃ θ : RatFunc Φ →+* FractionRing (Polynomial S), (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a))) ∧ algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 ∧ θ RatFunc.X * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
  intro Φ S _ _ _ _ p q r hp hr
  have hinj : Function.Injective (algebraMap (Polynomial S) (FractionRing (Polynomial S))) :=
    IsFractionRing.injective _ _
  have hs : ∀ s : S, algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C s) =
      algebraMap S (FractionRing (Polynomial S)) s := fun s => by
    rw [IsScalarTower.algebraMap_apply S (Polynomial S) (FractionRing (Polynomial S)),
      Polynomial.algebraMap_eq]
  have hpoly : Polynomial.C p + Polynomial.X * Polynomial.C q ≠ 0 := fun h =>
    hp (by simpa using congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) h)
  have hD : algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 := by
    rw [← map_mul, ← map_add (f := _)]
    exact (map_ne_zero_iff _ hinj).2 hpoly
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) /
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) := ⟨_, rfl⟩
  have htD : t * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) =
      algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
    rw [ht]
    exact div_mul_cancel₀ _ hD
  have htr : Transcendental S t := by
    refine transcendental_of_mul_add_eq_mul (p := p) (q := q) (r := r)
      ((transcendental_algebraMap_iff hinj).2 (Polynomial.transcendental_X S)) ?_ ?_ ?_
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hp)
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hr)
    · simpa only [hs] using htD
  let φ : Polynomial Φ →+* FractionRing (Polynomial S) :=
    (Polynomial.aeval t).toRingHom.comp (Polynomial.mapRingHom (algebraMap Φ S))
  have hφinj : Function.Injective φ := by
    intro P Q hPQ
    apply Polynomial.map_injective _ (algebraMap Φ S).injective
    exact (transcendental_iff_injective.1 htr) hPQ
  have hφC : ∀ a : Φ, φ (Polynomial.C a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a)) := by
    intro a
    rw [hs]
    simp [φ]
  have hφX : φ Polynomial.X = t := by
    simp [φ]
  refine ⟨RatFunc.liftRingHom φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj),
    fun a => ?_, hD, ?_⟩
  · rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, RatFunc.liftRingHom_algebraMap, hφC]
  · rw [← RatFunc.algebraMap_X, RatFunc.liftRingHom_algebraMap, hφX, htD]

end GlobalTheory.CompanionTheory.Ar.Moebius
end
