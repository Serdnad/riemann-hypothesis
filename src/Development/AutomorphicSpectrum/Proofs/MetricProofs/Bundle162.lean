module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle119
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle152
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle157
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle121
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle117
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle156
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle158
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle159
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_base_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X) (hc : Continuous pr), IsWAtlas M BM.Rb τ a k₀ ca cb RW pr → ∃ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (Dg : Set RW.X) (cst : ℝ), IsPotential RW.A L' ∧ IsSection RW.A L' v ∧ IsSNC RW.A L' v ![1] ![Dg] ∧ IsSNC RW.A (BM.L.pullback pr hc + L') (fun x y => BM.s (pr x) (pr y) * v x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) Dg) ∧ (∀ w, logNormSec L' v w ≤ 0) ∧ IsNormFn M τ a k₀ ca cb RW fun x => logNormSec L' v x + cst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr.two_projections <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.log_period_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ), M.IsFrame F → basePart M.blk (fstPt k₀ z) ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z))) → (∀ k, basePart M.blk (fstPt k₀ z) ⟨k, F.c k⟩ = 1) → (z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ↔ ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFlagOf F (fstPt k₀ z) h ∧ M.IsFlagOf F (sndPt k₀ z) (Function.update h τ (h τ * (1 + Matrix.single cb ca t)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_finTail {d : ℕ} (u : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) u := by
  have h : (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [h]
  exact ContinuousLinearMap.analyticAt _ _

theorem analyticAt_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : Type} [Fintype n]
    [DecidableEq n] (A : E → Matrix n n ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x) :
    AnalyticAt ℂ (fun u => (A u).det) x := by
  simp only [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_minorIJ_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    (A : E → Matrix (Fin N) (Fin N) ℂ) (x : E) (h : ∀ r s, AnalyticAt ℂ (fun u => A u r s) x)
    (I J : Finset (Fin N)) : AnalyticAt ℂ (fun u => minorIJ (A u) I J) x := by
  by_cases e : I.card = J.card
  · simp only [minorIJ, dif_pos e]
    exact analyticAt_det_of_entries _ x fun r s => h _ _
  · simp only [minorIJ, dif_neg e]
    exact analyticAt_const

theorem analyticAt_flagAt_entry {Ψ : Type} [DecidableEq Ψ] {N d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (u₀ : Fin (d + 1) → ℂ)
    (hH : ∀ τ'' r s, AnalyticAt ℂ (fun w => H τ'' w r s) (Fin.tail u₀)) (r s : Fin N) :
    AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => flagAt H τ ca cb (u 0) (Fin.tail u) τ' r s) u₀ := by
  have hHt : ∀ τ'' r s, AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => H τ'' (Fin.tail u) r s) u₀ :=
    fun τ'' r s => (hH τ'' r s).comp (analyticAt_finTail u₀)
  have h0 : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => u 0) u₀ :=
    (ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℂ) →L[ℂ] ℂ).analyticAt _
  unfold flagAt
  by_cases h : τ' = τ
  · simp only [if_pos h, Matrix.mul_apply, Matrix.add_apply]
    refine Finset.analyticAt_fun_sum _ fun t _ => (hHt _ _ _).mul (analyticAt_const.add ?_)
    by_cases e : cb = t ∧ ca = s
    · simpa only [Matrix.single_apply, if_pos e] using h0
    · simpa only [Matrix.single_apply, if_neg e] using analyticAt_const
  · simp only [if_neg h]
    exact hHt _ _ _

theorem sameOrbit_basePart {K : Type} {ι : K → Type} {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem coord_ne_zero_of_X_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun h0 => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem exists_normalised_exact {M : FlagModel y Ψ N j} (F : FrameData ι Ψ N M.Ω M.blk) (z₀ : (Σ k, ι k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, F.c k⟩ ≠ 0)
    (hex : ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₀ (h τ')) :
    ∃ z : (Σ k, ι k) → ℂ, SameOrbit z₀ z ∧ (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z (h τ') := by
  by_cases hp : Nonempty (Ψ × Fin N)
  · obtain ⟨⟨τ₀, i₀⟩⟩ := hp
    exact ⟨z₀, ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩, (hex τ₀ i₀).1, hex⟩
  · have hb : ∀ (k : K) p, M.blk p ≠ some k := fun k p => (hp ⟨p⟩).elim
    refine ⟨fun q => z₀ q / z₀ ⟨q.1, F.c ⟨q.1, hb q.1⟩⟩,
      ⟨fun k => z₀ ⟨k, F.c ⟨k, hb k⟩⟩, fun k => hne ⟨k, hb k⟩, ?_⟩, ?_, fun τ' i => (hp ⟨(τ', i)⟩).elim⟩
    · funext q
      rw [mul_div_cancel₀ _ (hne ⟨q.1, hb q.1⟩)]
    · rintro ⟨k, hk⟩
      exact div_self (hne ⟨k, hb k⟩)

theorem exact_points_holomorphic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a ca cb X q Un Gn ΦYn ΦWn l H bp hUn hD
  obtain ⟨hH, hbc, hba, hbp, -, hex, -⟩ := hD
  have hbij := realis_bijective_of_degree_one K ι (d + 1) _ FA.S _ FA.Re FA.deg_one FA.br_empty
  have hyh : IsMultiHomogIdeal (mCoordIdeal y) :=
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y
  have key : ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → ∃ z : (Σ k, ι k) → ℂ,
      z ∈ mcPts (mCoordIdeal y) ∧ (∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) z) ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧
      (∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z (flagAt H τ ca cb (u 0) (Fin.tail u) τ')) ∧
      ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1 := by
    intro u hu
    obtain ⟨x₀, hx₀⟩ := hbij.2 (ΦYn u)
    obtain ⟨z₀, ho, hb, he⟩ := hex u hu x₀ hx₀
    have hgood := BM.good l _ (hbp _ hu).1.1
    have hne : ∀ k : NonPluckerBlocks M.blk, z₀ ⟨k.1, (BM.F l).c k⟩ ≠ 0 := by
      intro k
      obtain ⟨c, hc, hcz⟩ := hb
      have h1 := congrFun hcz ⟨k, (BM.F l).c k⟩
      have h2 : basePart M.blk z₀ ⟨k, (BM.F l).c k⟩ = z₀ ⟨k.1, (BM.F l).c k⟩ := rfl
      rw [← h2, h1]
      exact mul_ne_zero (hc k) (coord_ne_zero_of_X_notMem (hgood.1 k))
    obtain ⟨z, hz, hn, hz'⟩ := exists_normalised_exact (BM.F l) z₀ _ hne he
    refine ⟨z, ?_, ?_, ?_, hz', hn⟩
    · exact mem_mcPts_of_sameOrbit hyh (orbit_symm (orbit_trans ho hz))
        (FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀))
    · intro x₁ hx₁
      obtain rfl := hbij.1 (hx₁.trans hx₀.symm)
      exact orbit_trans ho hz
    · exact orbit_trans (orbit_symm (sameOrbit_basePart M.blk hz)) hb
  choose! zex hz using key
  refine ⟨zex, ?_, fun u hu => ⟨(hz u hu).1, fun x₀ hx =>
    ⟨(hz u hu).2.1 x₀ hx, (hz u hu).2.2.1, (hz u hu).2.2.2.1⟩⟩⟩
  rintro ⟨k, m⟩ u₀ hu₀
  have hu₀' : (Fin.tail u₀ : Fin d → ℂ) ∈ Un := hu₀
  have htail : Tendsto (fun u : Fin (d + 1) → ℂ => (Fin.tail u : Fin d → ℂ)) (𝓝 u₀) (𝓝 (Fin.tail u₀)) :=
    (analyticAt_finTail u₀).continuousAt
  have hevU : ∀ᶠ u : Fin (d + 1) → ℂ in 𝓝 u₀, (Fin.tail u : Fin d → ℂ) ∈ Un := htail (hUn.mem_nhds hu₀')
  have hgood₀ := BM.good l _ (hbp _ hu₀').1.1
  by_cases hk : ∃ p, M.blk p = some k
  · obtain ⟨p, hp⟩ := hk
    have hval : ∀ s, RegAt M.x (mCoordIdeal (BM.Rb.lift (bp (Fin.tail u₀)) (bp (Fin.tail u₀)))) s →
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => valAt M.x s (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u)))) u₀ :=
      fun s hs => (analyticAt_valAt_lift_family (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x s d n BM.Rb Un bp (Fin.tail u₀)
        hUn hu₀' hbc hba hs).comp (analyticAt_finTail u₀)
    have hsum : AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => ∑ I,
        valAt M.x ((BM.F l).u ⟨k, m⟩ I) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) *
          minorIJ (flagAt H τ ca cb (u 0) (Fin.tail u) p.1) I (stepCols N j p.2)) u₀ :=
      Finset.analyticAt_fun_sum _ fun I _ => (hval _ ((hgood₀.2.1 _ I).1)).mul
        (analyticAt_minorIJ_of_entries _ _ (analyticAt_flagAt_entry H τ ca cb p.1 u₀
          (fun τ'' r s => hH τ'' r s _ hu₀')) _ _)
    refine hsum.congr ?_
    filter_upwards [hevU] with u hu
    obtain ⟨-, -, hb, he, -⟩ := hz u hu
    rw [(he p.1 p.2).2 k hp m]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [valAt_eq_of_sameOrbit (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _))
      (orbit_symm hb)]
  · have hkb : ∀ p, M.blk p ≠ some k := fun p hp => hk ⟨p, hp⟩
    set kb : NonPluckerBlocks M.blk := ⟨k, hkb⟩ with hkb'
    set b₀ := bp (Fin.tail u₀) with hb₀
    have hlift : ∀ q : Σ k, baseIdx ι M.blk k,
        AnalyticAt ℂ (fun u : Fin (d + 1) → ℂ => BM.Rb.lift b₀ (bp (Fin.tail u)) q) u₀ :=
      fun q => (analyticAt_comp_of_holo_in_charts d n BM.Rb.X BM.Rb.A Un bp (Fin.tail u₀) (BM.Rb.U b₀)
        (fun x => BM.Rb.lift b₀ x q) hUn hu₀' hbc hba (BM.Rb.isOpen_U _) (BM.Rb.mem_U _)
        (BM.Rb.holo b₀ q)).comp (analyticAt_finTail u₀)
    have hden : BM.Rb.lift b₀ (bp (Fin.tail u₀)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 :=
      coord_ne_zero_of_X_notMem (hgood₀.1 kb)
    refine ((hlift ⟨kb, m⟩).div (hlift ⟨kb, (BM.F l).c kb⟩) hden).congr ?_
    have hca : ContinuousAt bp (Fin.tail u₀) := hbc.continuousAt (hUn.mem_nhds hu₀')
    filter_upwards [hevU, htail (hca ((BM.Rb.isOpen_U b₀).mem_nhds (BM.Rb.mem_U b₀)))] with u hu hbu
    obtain ⟨-, -, hb, -, hn⟩ := hz u hu
    obtain ⟨c, hc, hcz⟩ := orbit_trans hb (BM.Rb.compat (bp (Fin.tail u)) b₀ (bp (Fin.tail u)) ⟨BM.Rb.mem_U _, hbu⟩)
    have h1 : c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = 1 := by
      rw [← hn kb, hcz]
    have h2 : zex u ⟨k, m⟩ = c kb * BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ := congrFun hcz ⟨kb, m⟩
    have h3 : BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ ≠ 0 := right_ne_zero_of_mul_eq_one h1
    show BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩ / BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, (BM.F l).c kb⟩ = zex u ⟨k, m⟩
    rw [h2, div_eq_iff h3]
    linear_combination (-(BM.Rb.lift b₀ (bp (Fin.tail u)) ⟨kb, m⟩)) * h1

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.conjugation_antiholomorphic_charts : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.conj_analytic | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.conj_analytic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.conj_analytic <;> assumption)
end

section

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem pot_holoOn_mono {V W : Set X} {g : X → ℂ} (h : A.HoloOn V g) (hW : W ⊆ V) :
    A.HoloOn W g :=
  fun j w hw => h j w ⟨hw.1, hW hw.2⟩

theorem pot_holoOn_continuousOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h1 := (h j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (fun y' => (g ∘ (A.chart j).symm) (A.chart j y')) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem pot_holoOn_sub_add {V : Set X} {g₁ g₂ g₃ : X → ℂ} (h₁ : A.HoloOn V g₁)
    (h₂ : A.HoloOn V g₂) (h₃ : A.HoloOn V g₃) :
    A.HoloOn V (fun y => g₁ y - g₂ y + g₃ y) :=
  fun j w hw => ((h₁ j w hw).sub (h₂ j w hw)).add (h₃ j w hw)

theorem pot_holoOn_div {V : Set X} {g₁ g₂ : X → ℂ} (h₁ : A.HoloOn V g₁) (h₂ : A.HoloOn V g₂)
    (hne : ∀ y ∈ V, g₂ y ≠ 0) : A.HoloOn V (fun y => g₁ y / g₂ y) :=
  fun j w hw => (h₁ j w hw).div (h₂ j w hw) (hne _ hw.2)

theorem pot_holoOn_sum_log {K : Type} [Fintype K] {V : Set X} {g : K → X → ℂ} (m : K → ℤ)
    (r : K → ℝ) (h : ∀ k, A.HoloOn V (g k)) (hs : ∀ k, ∀ y ∈ V, g k y ∈ Complex.slitPlane) :
    A.HoloOn V (fun y => ∑ k, (m k : ℂ) * (Complex.log (g k y) + (r k : ℂ))) := by
  intro j w hw
  have : ∀ k, AnalyticAt ℂ (fun z => (m k : ℂ) *
      (Complex.log (g k ((A.chart j).symm z)) + (r k : ℂ))) w := fun k =>
    analyticAt_const.mul ((AnalyticAt.clog (h k j w hw) (hs k _ hw.2)).add analyticAt_const)
  exact Finset.analyticAt_fun_sum _ fun k _ => this k

end Holo

theorem pot_re_sum_log {K : Type} [Fintype K] (m : K → ℤ) (u v : K → ℂ) (hu : ∀ k, u k ≠ 0)
    (hv : ∀ k, v k ≠ 0) :
    (∑ k, (m k : ℂ) * (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ))).re =
      ∑ k, (m k : ℝ) * Real.log ‖u k‖ := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ)).re = Real.log ‖u k‖ := by
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hv k))]
    ring
  simp [Complex.mul_re, h1]

theorem pot_log_h_conj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (f : HermLine ι)
    (hf : IsConjInvariantH f) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) :
    Real.log (f.h (fun p => a p.1 * cj z p)) - Real.log (f.h z) =
      ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ := by
  have hP : ∀ k ∈ (Finset.univ : Finset K), ‖a k‖ ^ f.a k ≠ 0 := fun k _ =>
    (zpow_pos (norm_pos_iff.mpr (ha k)) _).ne'
  have hP' : (∏ k, ‖a k‖ ^ f.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 hP
  rw [f.smul a (cj z) ha, show f.h (cj z) = f.h z from hf z,
    Real.log_mul hP' (f.pos z hz).ne', Real.log_prod hP]
  simp [Real.log_zpow]

theorem pot_conj_pluriharmonic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  intro K _ ι _ e X _ A P U lift hL c horb hcc hanti f hf th hth x
  obtain ⟨hUo, hUm, hUh, hUpts, hUor, -, -, -⟩ := hL
  choose i hi using (hUpts x x (hUm x)).1
  obtain ⟨V₁, hV₁o, hxV₁, G₁, hG₁, hφ₁⟩ := hth x
  obtain ⟨V₂, hV₂o, hxV₂, G₂, hG₂, hφ₂⟩ := hth (c x)

  have horbit : ∀ y ∈ U x, c y ∈ U (c x) → ∃ a : K → ℂ, (∀ k, a k ≠ 0) ∧
      lift (c x) (c y) = fun p => a p.1 * cj (lift x y) p := fun y hy hcy =>
    sameOrbit_trans (sameOrbit_trans (hUor (c x) (c y) (c y) ⟨hcy, hUm (c y)⟩) (horb y))
      (sameOrbit_cj (hUor y x y ⟨hUm y, hy⟩))

  let b : K → X → ℂ := fun k y =>
    starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩
  let D : K → Set X := fun k => U x ∩ (fun y => lift x y ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hDo : ∀ k, IsOpen (D k) := fun k =>
    (pot_holoOn_continuousOn (hUo x) (hUh x _)).isOpen_inter_preimage (hUo x) isOpen_compl_singleton
  let W₁ : Set X := (U x ∩ c ⁻¹' U (c x)) ∩ ⋂ k, D k
  have hW₁o : IsOpen W₁ :=
    ((hUo x).inter ((hUo (c x)).preimage hcc)).inter (isOpen_iInter_of_finite hDo)
  have hxW₁ : x ∈ W₁ :=
    ⟨⟨hUm x, hUm (c x)⟩, Set.mem_iInter.2 fun k => ⟨hUm x, hi k⟩⟩
  have hden : ∀ y ∈ W₁, ∀ k, lift x y ⟨k, i k⟩ ≠ 0 := fun y hy k =>
    (Set.mem_iInter.1 hy.2 k).2

  have hba : ∀ y ∈ W₁, ∀ a : K → ℂ, lift (c x) (c y) = (fun p => a p.1 * cj (lift x y) p) →
      ∀ k, b k y = starRingEnd ℂ (a k) := fun y hy a ha k => by
    change starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩ = _
    rw [ha]
    simp only [cj, map_mul, Complex.conj_conj]
    exact mul_div_cancel_right₀ _ (hden y hy k)
  have hbne : ∀ y ∈ W₁, ∀ k, b k y ≠ 0 := fun y hy k => by
    obtain ⟨a, ha, hl⟩ := horbit y hy.1.1 hy.1.2
    rw [hba y hy a hl k]
    simpa using ha k
  have hbH : ∀ k, A.HoloOn W₁ (b k) := fun k =>
    pot_holoOn_div
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti (hUh (c x) ⟨k, i k⟩)) fun y hy => hy.1.2)
      (pot_holoOn_mono (hUh x ⟨k, i k⟩) fun y hy => hy.1.1) fun y hy => hden y hy k
  have hqH : ∀ k, A.HoloOn W₁ (fun y => b k y / b k x) := fun k =>
    pot_holoOn_div (hbH k) (fun j w _ => analyticAt_const) fun _ _ => hbne x hxW₁ k
  let B : K → Set X := fun k => W₁ ∩ (fun y => b k y / b k x) ⁻¹' Metric.ball 1 1
  have hBo : ∀ k, IsOpen (B k) := fun k =>
    (pot_holoOn_continuousOn hW₁o (hqH k)).isOpen_inter_preimage hW₁o Metric.isOpen_ball
  let W₂ : Set X := W₁ ∩ ⋂ k, B k
  let V : Set X := (W₂ ∩ V₁) ∩ c ⁻¹' V₂
  have hVo : IsOpen V :=
    ((hW₁o.inter (isOpen_iInter_of_finite hBo)).inter hV₁o).inter (hV₂o.preimage hcc)
  have hVW : V ⊆ W₁ := fun y hy => hy.1.1.1
  have hxV : x ∈ V := by
    refine ⟨⟨⟨hxW₁, Set.mem_iInter.2 fun k => ⟨hxW₁, ?_⟩⟩, hxV₁⟩, hxV₂⟩
    simp [div_self (hbne x hxW₁ k)]
  have hslit : ∀ k, ∀ y ∈ V, b k y / b k x ∈ Complex.slitPlane := fun k y hy => by
    have h1 : b k y / b k x ∈ Metric.ball (1 : ℂ) 1 := (Set.mem_iInter.1 hy.1.1.2 k).2
    have h2 : ‖b k y / b k x - 1‖ < 1 := by simpa [dist_eq_norm] using h1
    simpa using Complex.mem_slitPlane_of_norm_lt_one h2
  refine ⟨V, hVo, hxV,
    fun y => G₁ y - starRingEnd ℂ (G₂ (c y)) +
      ∑ k, (f.a k : ℂ) * (Complex.log (b k y / b k x) + ((Real.log ‖b k x‖ : ℝ) : ℂ)), ?_, ?_⟩
  · refine pot_holoOn_sub_add (pot_holoOn_mono hG₁ fun y hy => hy.1.2)
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti hG₂) fun y hy => hy.2) ?_
    exact pot_holoOn_sum_log f.a _ (fun k => pot_holoOn_mono (hqH k) hVW) fun k => hslit k
  · intro y hy
    have hyW := hVW hy
    obtain ⟨a, ha, hl⟩ := horbit y hyW.1.1 hyW.1.2
    have e₁ := hφ₁ y hy.1.2
    have e₂ := hφ₂ (c y) hy.2
    have e₃ := pot_log_h_conj f hf (hUpts x y hyW.1.1).1 ha
    rw [← hl] at e₃
    have e₄ := pot_re_sum_log f.a (fun k => b k y) (fun k => b k x) (hbne y hyW) (hbne x hxW₁)
    have e₅ : ∑ k, (f.a k : ℝ) * Real.log ‖b k y‖ = ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ :=
      Finset.sum_congr rfl fun k _ => by rw [hba y hyW a hl k, RCLike.norm_conj]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
    rw [e₄, e₅, ← e₃]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_cover_arithmetic_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w, CovMap.IsImg Cv z w → SameOrbit (basePart M.blk w) (basePart M'.blk z ∘ Cv.v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

theorem _root_.GlobalTheory.T.points_integrable_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK <;> assumption)
end

section


theorem _root_.GlobalTheory.T.intersection_exists_of_poincare_lelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | exact GlobalTheory.CompanionTheory.Ar.Pub.thmIExists | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.thmIExists <;> assumption)
end
