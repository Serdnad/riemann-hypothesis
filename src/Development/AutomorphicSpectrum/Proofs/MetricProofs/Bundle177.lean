module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCUnif
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle171
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle167
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle176
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle172
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle174
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle124
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle166
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle165
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle161
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle131
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle141
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
import Mathlib.Tactic.Basify
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

theorem _root_.GlobalTheory.T.chernIntegrableOn_iff_sheets : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (S : Set (CxPts t τ)), MeasurableSet S → ∀ f : CxPts t τ → ℝ, (ψ.ChernIntegrableOn D S f ↔ ∀ σ, (φ σ).ChernIntegrableOn D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) ∧ (ψ.ChernIntegrableOn D S f → ψ.chernInt D S f = ∑ᶠ σ, (φ σ).chernInt D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets | exact GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets | (intros; apply GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), n = Fintype.card Ψ * j * (N - j) → d + 1 = antisymDegree Ψ N → IsUniformised (FA.S.comap some).A (FA.S.comap some).open' j (FA.S.comap some).potH := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA _ _
  refine ⟨?_, ?_⟩
  · intro x hx
    have hb := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).1 hx
    obtain ⟨l, hl⟩ := BM.O_cover (FA.pr x)
    obtain ⟨V, Pi, hxV, hP⟩ := BM.period l (FA.pr x) ⟨hl, hb⟩
    obtain ⟨V', g, hc, -⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hl, hb⟩ hxV hP
    exact ⟨V', g, hc⟩
  · obtain ⟨l, b, ⟨hbO, hbs⟩, V, Pi, hbV, hP, himm⟩ := BM.immersion
    obtain ⟨x, rfl⟩ := PositivityTheory.Xgp.c_unif.exists_over FA hbO
    have hx : x ∈ (FA.S.comap some).open' := (PositivityTheory.Xgp.c_unif.mem_open_iff FA x).2 hbs
    obtain ⟨V', g, hc, hi⟩ := PositivityTheory.Xgp.c_unif.chart_over FA x ⟨hbO, hbs⟩ hbV hP
    exact ⟨x, hx, V', g, hc, hi himm⟩
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_seventh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ l : Fin BM.q, IsNull RW.A {x | FA.pr (q 0 x) ∈ BM.O l ∧ (FA.pr (q 0 x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p = 0 ∨ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p = 0)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_w | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_w | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_w <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (Un : Set (Fin d → ℂ)) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) → ∃ (ΦY : (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : (Fin (d + 2) → ℂ) → RW.X), ContinuousOn ΦY {z | Fin.tail z ∈ Un} ∧ (∀ k, AnalyticOnNhd ℂ (FA.S.A.chart k ∘ ΦY) ({z | Fin.tail z ∈ Un} ∩ ΦY ⁻¹' (FA.S.A.chart k).source)) ∧ ContinuousOn ΦW {z | Fin.tail (Fin.tail z) ∈ Un} ∧ (∀ k, AnalyticOnNhd ℂ (RW.A.chart k ∘ ΦW) ({z | Fin.tail (Fin.tail z) ∈ Un} ∩ ΦW ⁻¹' (RW.A.chart k).source)) ∧ (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → FA.pr (ΦY z) = bp (Fin.tail z) ∧ ∀ x₀, FA.Re.π x₀ = ΦY z → SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (bp (Fin.tail z))) (Function.update (fun τ' => H τ' (Fin.tail z)) τ (H τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)))))) ∧ (∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → SameOrbit (RW.lift (ΦW z) (ΦW z)) (FC.wVec M (BM.F l) (FC.bvec BM l (bp (Fin.tail (Fin.tail z)))) (Function.update (fun τ' => H τ' (Fin.tail (Fin.tail z))) τ (H τ (Fin.tail (Fin.tail z)) * (1 + Matrix.single cb ca (z 0)))) τ a k₀ ca cb (z 1 - z 0)) ∧ q 0 (ΦW z) = ΦY (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦW z) = ΦY (Fin.tail z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FamCh.charts | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FamCh.charts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FamCh.charts <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_analytic_bad_locus_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q), IsNull FA.Re.R.A {x | FA.pr (FA.Re.π x) ∈ BM.O l ∧ (FA.pr (FA.Re.π x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x))) (FA.Re.R.lift x x) p = 0)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_off_bigCell_resolution | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_off_bigCell_resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_off_bigCell_resolution <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_baseOf {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (baseOf M k₀ z) (baseOf M k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k.1), fun k => hc _, rfl⟩

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases e : k = k₀
    · subst e
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (show (⟨k, m⟩ : Σ k, ι k).1 ≠ k₀ from e), if_neg e]

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem fibreSquare_atlas : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy hd
  have hA := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  obtain ⟨ε⟩ := GlobalTheory.T.flag_dimension_index_equiv Ψ N j n d M.j_le hd
  have hcov := GlobalTheory.T.flag_adjacent_arithmetic_height K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h →
      ∃ C : OrbitChart (wP M τ a k₀ ca cb) (d + 2), C.D = wD ε V ∧ C.φ = wPhi M F bl h ε k₀ τ ca cb ∧
        C.O = wO M Rb τ a k₀ ca cb F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.2.2.2.2.1.1
    have hh := GlobalTheory.T.flag_adjacent_chart_first K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hm := GlobalTheory.T.wPhi_mem_mcPts_wP K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hr := GlobalTheory.T.flag_adjacent_chart_fourth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ho := GlobalTheory.T.flag_adjacent_chart_fifth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hO := GlobalTheory.T.flag_adjacent_chart_sixth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
    have hb' := GlobalTheory.T.flag_adjacent_chart_seventh K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ht := GlobalTheory.T.flag_adjacent_chart_eighth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hi := GlobalTheory.T.flag_adjacent_chart_ninth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    exact ⟨{ D := wD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := wPhi M F bl h ε k₀ τ ca cb
             holo := hh
             mem := hm
             O := wO M Rb τ a k₀ ca cb F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := wRho M Rb τ k₀ ca cb F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := GlobalTheory.T.log_resolution_from_orbit_charts (Option K) (fun o => ι (o.getD k₀)) (wP M τ a k₀ ca cb) (d + 2) hA.1 hA.2.1.2.1
    (fun h => hA.2.1.1.ne_top (top_le_iff.mp h)) (fun z hz => by
      obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
      obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
      exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = wD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (baseOf M k₀ (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    refine ⟨(Rb.A.chart kb).symm (wB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := sameOrbit_baseOf M (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ψ.target = wD ε V → x ∈ ψ.source →
      SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x)) (R.lift x x) →
      pr x ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    have h1 : SameOrbit (bl (wB ε (ψ x))) (baseOf M k₀ (R.lift x x)) := by
      have := sameOrbit_baseOf M hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (wB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_mcPts_top _) h2
    have hwt : wB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨(Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  refine ⟨R, pr, ?_, hpr, fun x => ?_⟩
  · refine GlobalTheory.T.holoMap_of_local_product_charts (d + 2) n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    exact ⟨ψ, kb, fun i => ε (Sum.inl i), hC, hx, fun x' hx' => hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')⟩
  · obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    have hE := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hB := hc.2.2.2.2.2.2.2.1
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun i i' e => Sum.inl_injective (ε.injective e)⟩, ε (Sum.inr (Sum.inr ())), F,
      fun τ' => wH h ε τ', hx, hC, hc.2.2.2.2.2.2.1, fun i e => Sum.inl_ne_inr (ε.injective e), fun x' hx' =>
        hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx'), fun τ' r' s' => hT ▸ hE.1 τ' r' s', fun x' hx' => ?_⟩
    have hw : ψ x' ∈ wD ε V := hT ▸ ψ.map_source hx'
    obtain ⟨e1, e2, e3⟩ := hE.2 _ hw
    have h1 := sameOrbit_baseOf M (hs x' hx')
    rw [e2] at h1
    refine ⟨e1, ?_, fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')), sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')),
      sameOrbit_fstPt (hs x' hx'), sameOrbit_sndPt (hs x' hx'), e3⟩
    have h2 : mCoordIdeal (bl (wB ε (ψ x'))) = mCoordIdeal (basePart M.blk (fstPt k₀ (R.lift x' x'))) :=
      GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit h1
    exact h2 ▸ (hB.2.2.2.2 _ hw).2.2.1

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end
