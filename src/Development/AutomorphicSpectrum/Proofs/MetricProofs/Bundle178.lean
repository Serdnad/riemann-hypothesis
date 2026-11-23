module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMap
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle177
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle166
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

private theorem chernIntegrableOn_and_chernInt_congr {k : Type} [CommRing k] {Y : Scheme} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} (φ : GlobalTheory.Weight q σ B) (d : ℕ) {S : Set (GlobalTheory.CxPts q σ)}
    (hS : MeasurableSet S) {f g : GlobalTheory.CxPts q σ → ℝ} (h : Set.EqOn f g S) :
    (φ.ChernIntegrableOn d S f ↔ φ.ChernIntegrableOn d S g) ∧ φ.chernInt d S f = φ.chernInt d S g := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.Weight.ChernIntegrableOn
    rw [integrableOn_congr_fun h hS, integrableOn_congr_fun h hS]
  · unfold GlobalTheory.Weight.chernInt
    rw [setIntegral_congr_fun hS h, setIntegral_congr_fun hS h]

theorem archInt_over_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (ψ : Weight t τ N.B) (ν : Weight t τ M.B), WOver N.φ ψ → WOver M.φ ν → ψ.IsCInf → ∀ (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → ψ.chernInt e (offSupp t τ (M.div hr)) (logNorm ν r) = N.archInt M e hr) := by
  intro k _ X _ p t τ D hX N M ψ ν hψN hνM hψ e r hr
  by_cases hσ : Nonempty (k →+* ℂ)
  · obtain ⟨σ₀⟩ := hσ
    haveI : CharZero k := σ₀.charZero
    haveI := hX.isDomain
    haveI := hX.finite
    have hS : MeasurableSet (offSupp t τ (M.div hr)) := (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    obtain ⟨h1, h2⟩ := GlobalTheory.T.chernIntegrableOn_iff_sheets k X p t τ hX.isProjOver e N.B N.φ ψ hψN N.cInf hψ _ hS (logNorm ν r)
    have hmeas : ∀ σ : k →+* ℂ, MeasurableSet (offSupp p σ (M.div hr)) :=
      fun σ => (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    have hEq : ∀ σ : k →+* ℂ, Set.EqOn (fun z => logNorm ν r (GlobalTheory.CompanionTheory.Ar.BaseZ.sheet t τ z))
        (logNorm (M.φ σ) r) (offSupp p σ (M.div hr)) :=
      fun σ y hy => GlobalTheory.T.logNorm_sheet_eq k X p t τ M.B M.φ ν hνM r hr σ y hy
    have hiff : ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr := by
      rw [h1]
      unfold GlobalTheory.HermLB.ArchIntegrable
      exact forall_congr' fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).1
    refine ⟨hiff, fun hInt => ?_⟩
    rw [h2 (hiff.mpr hInt)]
    unfold GlobalTheory.HermLB.archInt
    exact finsum_congr fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).2
  · have hE : IsEmpty (k →+* ℂ) := not_nonempty_iff.mp hσ
    haveI : IsEmpty (GlobalTheory.CxPts t τ) := ⟨fun y => hE.false (Spec.preimage (Subtype.val y ≫ p)).hom⟩
    have hS0 : offSupp t τ (M.div hr) = ∅ := Set.eq_empty_of_isEmpty _
    have hA : N.ArchIntegrable M e hr := by
      unfold GlobalTheory.HermLB.ArchIntegrable
      intro σ
      exact hE.elim σ
    refine ⟨⟨fun _ => hA, fun _ => ?_⟩, fun _ => ?_⟩
    · unfold GlobalTheory.Weight.ChernIntegrableOn
      rw [hS0]
      exact ⟨integrableOn_empty, integrableOn_empty⟩
    · unfold GlobalTheory.HermLB.archInt GlobalTheory.Weight.chernInt
      rw [hS0, finsum_of_isEmpty]
      simp

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_bundle_partial_block_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.main <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_analytic_data_uniformised : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), n = Fintype.card Ψ * j * (N - j) → d + 1 = antisymDegree Ψ N → IsUniformised (FA.S.comap some).A (FA.S.comap some).open' j (FA.S.comap some).potH := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised | exact GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.fibreSquare_atlas <;> assumption)
end
