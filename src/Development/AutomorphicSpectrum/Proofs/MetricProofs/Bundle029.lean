module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle020
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle003
public import Development.WeilBound.CoreStatements.RationalSupMetrics.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
public import Mathlib.Geometry.Manifold.IsManifold.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001

@[expose] public section

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem det_eq_mul_minor_of_col_zero {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h : ∀ i : Fin n, J i.succ 0 = 0) : J.det = J 0 0 * (J.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

theorem hasDerivAt_mob_line (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den G a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob G (a + t)) (mobD G a) 0 := by
  apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.hasDerivAt_mob_shift <;> assumption

theorem jacC_apply_of_line {D E : ℕ} (F : (Fin D → ℂ) → Fin E → ℂ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F z) (a : Fin E) (k : Fin D) (c : ℂ)
    (h : HasDerivAt (fun t : ℂ => F (z + t • (Pi.single k 1 : Fin D → ℂ)) a) c 0) :
    ReciprocityTheory.AnForm.A.jacC F z a k = c := by
  have hl : HasDerivAt (fun t : ℂ => z + t • (Pi.single k 1 : Fin D → ℂ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single k 1 : Fin D → ℂ)).const_add z
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • (Pi.single k 1 : Fin D → ℂ)) := by
    simpa using hF.hasFDerivAt
  have h2 := hF'.comp_hasDerivAt (0 : ℂ) hl
  have h3 := (hasDerivAt_pi.1 h2) a
  exact h3.unique h

theorem mobius_pair_line_first_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 0 1 : Fin (d + 2) → ℂ) =
      Fin.cons (a₀ + t) (Fin.cons a₁ y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.single_apply, Fin.succ_ne_zero]

theorem mobius_pair_line_second_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 1 1 : Fin (d + 2) → ℂ) =
      Fin.cons a₀ (Fin.cons (a₁ + t) y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Pi.single_apply]
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp [Pi.single_apply]
    · have : (l.succ.succ : Fin (d + 2)) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [Pi.single_apply, this]

theorem mobius_pair_cons {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ) (b₀ b₁ : ℂ) :
    mob2 g (Fin.cons b₀ (Fin.cons b₁ y)) = Fin.cons (mob (g y) b₀) (Fin.cons (mob (g y) b₁) y) := rfl

theorem analyticAt_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    AnalyticAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) := by
  set z₀ : Fin (d + 2) → ℂ := Fin.cons a₀ (Fin.cons a₁ y) with hz₀
  have hcoord : ∀ i : Fin (d + 2), AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => z i) z₀ := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 2) => ℂ) i).analyticAt z₀
  have hT : AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) z₀ := by
    rw [analyticAt_pi_iff]
    intro i
    exact hcoord i.succ.succ
  have hTz : Fin.tail (Fin.tail z₀) = y := by
    simp [hz₀]
  have hga : ∀ p q, AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => g (Fin.tail (Fin.tail z)) p q) z₀ := by
    intro p q
    have h1 : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail (Fin.tail z₀)) :=
      ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
    exact AnalyticAt.comp (f := fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) h1 hT
  have hm : ∀ i : Fin (d + 2), den (g y) (z₀ i) ≠ 0 →
      AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => mob (g (Fin.tail (Fin.tail z))) (z i)) z₀ := by
    intro i hi
    unfold mob den
    refine AnalyticAt.div ?_ ?_ ?_
    · exact (hga 1 0).add ((hga 1 1).mul (hcoord i))
    · exact (hga 0 0).add ((hga 0 1).mul (hcoord i))
    · rw [hTz]
      exact hi
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hm 0 (by simpa [hz₀] using h₀)
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact hm 1 (by simpa [hz₀] using h₁)
    · exact hcoord l.succ.succ

theorem det_jacobian_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      mobD (g y) a₀ * mobD (g y) a₁ := by
  have hdiff : DifferentiableAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) :=
    (analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁).differentiableAt
  set J := ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) with hJ
  have hJ00 : J 0 0 = mobD (g y) a₀ := by
    refine jacC_apply_of_line _ _ hdiff 0 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₀ h₀
  have hJ11 : J 1 1 = mobD (g y) a₁ := by
    refine jacC_apply_of_line _ _ hdiff 1 1 _ ?_
    simp only [mobius_pair_line_second_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₁ h₁
  have hJ10 : J 1 0 = 0 := by
    refine jacC_apply_of_line _ _ hdiff 1 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_const (0 : ℂ) (mob (g y) a₁)
  have hJss : ∀ (i : Fin d) (k : Fin (d + 2)), J i.succ.succ k = (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
    intro i k
    refine jacC_apply_of_line _ _ hdiff _ _ _ ?_
    have e : (fun t : ℂ => mob2 g ((Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) +
        t • (Pi.single k 1 : Fin (d + 2) → ℂ)) i.succ.succ) =
        fun t : ℂ => y i + t * (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
      funext t
      simp [mob2, Fin.tail]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ)).const_add (y i)
  have hc0 : ∀ i : Fin (d + 1), J i.succ 0 = 0 := by
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact hJ10
    · rw [hJss]
      simp [Pi.single_apply, Fin.succ_ne_zero]
  have hc1 : ∀ i : Fin d, (J.submatrix Fin.succ Fin.succ) i.succ 0 = 0 := by
    intro i
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    have : (i.succ.succ : Fin (d + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [Pi.single_apply, this]
  have hlast : ((J.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    simp [Pi.single_apply, Matrix.one_apply]
  rw [det_eq_mul_minor_of_col_zero J hc0, det_eq_mul_minor_of_col_zero _ hc1, hlast, Matrix.det_one, mul_one,
    hJ00]
  simp only [Matrix.submatrix_apply]
  congr 1

theorem mobius_pair_analyticAt_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a₀ a₁ : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) ∧
    (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀ * GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁ :=
  fun _ g hg y a₀ a₁ h₀ h₁ => ⟨analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁, det_jacobian_mobius_pair g hg y a₀ a₁ h₀ h₁⟩

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.nef_threshold_gap_condition : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum | exact GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold.gapCond_and_lmuNum <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open scoped ContDiff

theorem GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics : ∀ (e : ℕ) (σ : Type) (S : AnSys e σ), IsOpen S.open' ∧ IsNull S.A S.open'ᶜ ∧ (∀ a, ∀ x ∈ S.open', IsTwiceDifferentiableAt S.A (S.potH a) x) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → IsPotential S.A (S.potT a t)) ∧ ∀ y ∈ S.open', Real.exp 1 ≤ rW S.L S.s y := by
  intro e σ S
  have hcl : IsClosed (bdry S.s) := LeviFormBoundaryTopology.isClosed_bdry S.sec
  refine ⟨hcl.isOpen_compl, ?_, ?_, ?_, fun y _ => rW_ge S.L S.s S.norm_le y⟩
  · have hAn : S.A.IsAnalyticSubset (bdry S.s) := by
      intro x
      refine ⟨S.L.U x, S.L.isOpen_U x, S.L.mem_U x, 1, fun _ => S.s x, fun _ => S.sec.1 x, ?_⟩
      ext z
      constructor
      · rintro ⟨hz, hzU⟩
        exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff S.sec hzU).1 hz⟩
      · rintro ⟨hzU, hz⟩
        exact ⟨(LeviFormBoundaryTopology.bdry_iff S.sec hzU).2 (hz 0), hzU⟩
    have hInt := LeviFormBoundaryTopology.interior_bdry_eq_empty S.sec S.snc
    intro j
    have h := analyticNull S.A (bdry S.s) hAn hInt j
    have hc : S.open'ᶜ = bdry S.s := compl_compl _
    rw [hc]
    rw [Set.inter_comm, (S.A.chart j).image_source_inter_eq'] at h
    exact h
  · intro a x hx j hj
    obtain ⟨hth, hph, -, -⟩ := S.sing a
    have h1 := hth.1 x j
    have h2 := hph j
    have hO1 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x) :=
      (S.A.chart j).isOpen_inter_preimage_symm ((S.th a).isOpen_U x)
    have hO2 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ) :=
      (S.A.chart j).isOpen_inter_preimage_symm hcl.isOpen_compl
    have hm1 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x :=
      ⟨(S.A.chart j).map_source hj, by
        simpa [(S.A.chart j).left_inv hj] using (S.th a).mem_U x⟩
    have hm2 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ :=
      ⟨(S.A.chart j).map_source hj, by
        have hx' : x ∈ (bdry S.s)ᶜ := hx
        simpa [(S.A.chart j).left_inv hj] using hx'⟩
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
    have hA := (h1.contDiffAt (hO1.mem_nhds hm1)).of_le hle
    have hB := (h2.contDiffAt (hO2.mem_nhds hm2)).of_le hle
    exact hA.add hB
  · intro a t ht ht'
    exact isPotentialAdd S.A _ _ (S.sing a).1 (isPotential_ofFun S.A _ ((S.reg a).2.2 t ht ht').1)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.monge_ampere_integral_congr_potentials : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ → (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) → mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot | exact GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.monge_ampere_chart_density_integral : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (j : Fin A.n), IsParam A V Φ → MeasurableSet B → B ⊆ V → (∀ z ∈ B, Φ z ∈ (A.chart j).source) → (∀ z ∈ B, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) → MeasurableSet ((A.chart j ∘ Φ) '' B) ∧ (IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A P j y) ((A.chart j ∘ Φ) '' B) ↔ IntegrableOn (fun z => g (Φ z) * paramDens P Φ z) B) ∧ ∫ y in (A.chart j ∘ Φ) '' B, g ((A.chart j).symm y) * locDens A P j y = ∫ z in B, g (Φ z) * paramDens P Φ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables | exact GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem an_two_weights_close : ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e (σ ⊕ σ)) (d : σ → S.X → ℝ), (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → ∀ (a : σ) (w : Fin e → σ ⊕ σ), Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x)) (𝓝[>] 0) (𝓝 0) :=
  @PositivityTheory.Xgp.t_an_two

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem exists_form_hasVal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), Birational y → IsRelevant (mCoordIdeal y) → ∀ (a : K → ℤ) (s : Ω), ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜), aeval z h ≠ 0 → ∃ w, HasVal y a s z w :=
  @MultiProjectiveCoordinates.exists_form_with_valuation

end GlobalTheory.CompanionTheory.Ar.Small
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.xi_potential_hessian_decomposition : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → ∃ T : Fin 3 → Matrix (Fin d) (Fin d) ℂ, ∀ a : ℂ, ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) ∧ hessC (fun z : Fin (d + 1) → ℂ => xiPot (G (Fin.tail z)) (z 0)) (Fin.cons a y) = Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (-(((1 + ‖a‖ ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => ∑ i, (((fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)) a i : ℝ) : ℂ) * T i p' q') q) p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition | exact GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition | (intros; apply GlobalTheory.CompanionTheory.Relay.xi_potential_hessian_decomposition <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem derivation_prod_erase_xt {σ ι : Type*} [DecidableEq ι]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : ι → MvPolynomial σ ℝ) (S : Finset ι) :
    D (∏ i ∈ S, a i) = ∑ i ∈ S, D (a i) * ∏ j ∈ S.erase i, a j := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, D.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, mul_comm (∏ j ∈ S, a j), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij,
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h))]
    ring

theorem derivation_prod_succAbove_xt {σ : Type*} {n : ℕ}
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : Fin (n + 1) → MvPolynomial σ ℝ) :
    D (∏ r, a r) = ∑ r, D (a r) * ∏ s, a (r.succAbove s) := by
  rw [derivation_prod_erase_xt]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [Fin.univ_succAbove _ r, Finset.cons_eq_insert, Finset.erase_insert (by simp), Finset.prod_map]
  rfl

theorem pderiv_rowW_zero_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 0) (rowW u v) = C (u 0) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_rowW_one_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 1) (rowW u v) = C (u 1) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_C_mul_xt {σ : Type*} [DecidableEq σ] (j : σ) (a : ℝ) (p : MvPolynomial σ ℝ) :
    pderiv j (C a * p) = C a * pderiv j p := by
  simp [Derivation.leibniz, pderiv_C]

theorem linear_form_linear_combination (a b : ℝ) (n m : Fin 3 → ℝ) :
    lin4 (fun i => a * n i + b * m i) = C a * lin4 n + C b * lin4 m := by

  simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Finset.mul_sum,
  ← Finset.sum_add_distrib, map_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem evalW_C_xt (n₀ n₁ : Fin 3 → ℝ) (a : ℝ) : evalW n₀ n₁ (C a) = C a := by
  simp [evalW]

theorem evalW_rowW_xt (n₀ n₁ : Fin 3 → ℝ) (u : Fin 2 → ℝ) (v : ℝ) :
    evalW n₀ n₁ (rowW u v) = lin4 (fun i => u 0 * n₀ i + u 1 * n₁ i) + C v * X none := by
  rw [linear_form_linear_combination]
  simp [evalW, rowW]

theorem mdisc_extract_two : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  intro d T H L hL u v n₀ n₁ e₀ e₁
  have hLC : ∀ (a : ℝ) (p : MvPolynomial (Option (Fin 3)) ℝ), L (C a * p) = (a : ℂ) * L p := by
    intro a p
    rw [← smul_eq_C_mul, map_smul, Complex.real_smul]
  let M : Fin (d + 2) → Matrix (Fin d) (Fin d) ℂ := fun r =>
    (∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H
  have h1 : ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) =
      ∑ r, ((u r 0 : ℂ) * e₀) * (((d + 1).factorial : ℂ) *
        mdisc fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) :=
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion (d + 1)).1 (fun r => (u r 0 : ℂ) * e₀) (fun r => blk ((u r 1 : ℂ) * e₁) (M r))
  have h2 : ∀ r : Fin (d + 2), ((d + 1).factorial : ℂ) *
      mdisc (fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) =
      ∑ s, ((u (r.succAbove s) 1 : ℂ) * e₁) * ((d.factorial : ℂ) *
        mdisc fun t => M (r.succAbove (s.succAbove t))) := fun r =>
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun s => (u (r.succAbove s) 1 : ℂ) * e₁) (fun s => M (r.succAbove s))
  have h3 : ∀ (r : Fin (d + 2)) (s : Fin (d + 1)),
      (d.factorial : ℂ) * mdisc (fun t => M (r.succAbove (s.succAbove t))) =
      L (∏ t, evalW n₀ n₁ (rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))))) := by
    intro r s
    simp only [evalW_rowW_xt]
    exact hL (fun t i => u (r.succAbove (s.succAbove t)) 0 * n₀ i + u (r.succAbove (s.succAbove t)) 1 * n₁ i)
      (fun t => v (r.succAbove (s.succAbove t)))
  have h4 : pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))) =
      ∑ r, C (u r 0) * ∑ s, C (u (r.succAbove s) 1) *
        ∏ t, rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))) := by
    rw [derivation_prod_succAbove_xt]

    simp only [pderiv_rowW_zero_xt, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pderiv_C_mul_xt, derivation_prod_succAbove_xt]
    simp only [pderiv_rowW_one_xt]
  show ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) = _
  rw [h1, h4]

  simp only [h2, h3, map_sum, map_mul, map_prod, evalW_C_xt, hLC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.polydisc_poisson_reproduces_harmonic : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R → ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) → ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.complex_hessian_block_combination : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p e : ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (s v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p y) → ContDiffAt ℝ 2 α y → hessC f (Fin.cons p y) = blk e B →
    hessC (fun z : Fin (d + 1) → ℂ => s * f z + v * α (Fin.tail z)) (Fin.cons p y) =
    blk ((s : ℂ) * e) ((s : ℂ) • B + (v : ℂ) • hessC α y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.mixed_discriminant_linear_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly.exists_functional <;> assumption)
end
