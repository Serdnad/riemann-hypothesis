module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamily
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle174
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle165
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle163
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle167
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Metric

theorem chernInt_eq_finsum_sheets : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (S : Set (CxPts t τ)), MeasurableSet S → ∀ f : CxPts t τ → ℝ, (ψ.ChernIntegrableOn D S f ↔ ∀ σ, (φ σ).ChernIntegrableOn D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) ∧ (ψ.ChernIntegrableOn D S f → ψ.chernInt D S f = ∑ᶠ σ, (φ σ).chernInt D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) := by
  intro k _ _ _ _ X p t τ hP D B φ ψ hW hφ hψ S hS f
  have hemb : ∀ σ : k →+* ℂ, MeasurableEmbedding (sheet (p := p) (σ := σ) t τ) := fun σ =>
    (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1.measurableEmbedding
  have huniq : ∀ y : CxPts t τ, ∃! σ : k →+* ℂ, y ∈ Set.range (sheet (p := p) (σ := σ) t τ) := by
    intro y
    refine ⟨emb p y, ?_, ?_⟩
    · show y ∈ Set.range (sheet (p := p) (σ := emb p y) t τ)
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ _).2]
      rfl
    · intro σ hσ
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).2] at hσ
      exact hσ.symm
  have hfin : Finite (k →+* ℂ) := Sheet.finite_ringHom k
  have key := fun ε : ℤˣ => integrableOn_and_setIntegral_of_embeddings (k →+* ℂ) (CxPts t τ)
    (fun σ => CxPts p σ) (fun σ => sheet (p := p) (σ := σ) t τ) hemb huniq (ψ.chernPart D ε)
    (fun σ => (φ σ).chernPart D ε) (fun σ S' hS' => GlobalTheory.T.chernPart_sheet_image_eq k X p t τ hP σ D B φ ψ hW hφ hψ ε S' hS') S hS f
  obtain ⟨h1, h1'⟩ := key 1
  obtain ⟨h2, h2'⟩ := key (-1)
  refine ⟨?_, ?_⟩
  · simp only [GlobalTheory.Weight.ChernIntegrableOn]
    rw [h1, h2]
    exact forall_and.symm
  · intro hI
    simp only [GlobalTheory.Weight.chernInt]
    rw [h1' hI.1, h2' hI.2, finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]

end GlobalTheory.CompanionTheory.Metric
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_adjacent_rows_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => c (some k), fun k => hc _, ?_⟩
  funext p
  show z (v₀ k₀ p) = c (some p.1) * z' (v₀ k₀ p)
  rw [e]
  rfl

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k₀ : K)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · by_cases hk : k = k₀
    · simpa [hk] using hc none
    · simpa [hk] using hc (some k)
  · funext p
    show z (v₁ k₀ p) = (if p.1 = k₀ then c none else c (some p.1)) * z' (v₁ k₀ p)
    rw [e]
    by_cases hk : p.1 = k₀
    · obtain ⟨k, m⟩ := p
      obtain rfl : k = k₀ := hk
      simp [v₁_self]
    · rw [if_neg hk, v₁_ne hk]

theorem null_w : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ l : Fin BM.q, IsNull RW.A {x | FA.pr (q 0 x) ∈ BM.O l ∧ (FA.pr (q 0 x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p = 0 ∨ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hpr : HoloMap RW.A BM.Rb.A (FA.pr ∘ q 0) := Pr.holoMap_comp' (hq 0) FA.pr_holo
  have hdens := GlobalTheory.T.flag_adjacent_twisted_resolution_sixth K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hab hj hblk hca hcb RW q hq h0 h1 hinj l
  have hn0 := GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => fstPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₀ k₀ p))
    (fun x y' hy => sameOrbit_fstPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).1⟩)
  have hn1 := GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM (d + 2) RW.X RW.A RW.U
    (fun x y' => sndPt k₀ (RW.lift x y')) (FA.pr ∘ q 0) l hpr RW.isOpen_U RW.mem_U
    (fun x p => RW.holo x (v₁ k₀ p))
    (fun x y' hy => sameOrbit_sndPt k₀ (RW.compat x y' y' ⟨hy, RW.mem_U y'⟩))
    (fun x hx V hV hxV => by
      obtain ⟨x', hx', hb, hp⟩ := hdens x hx V hV hxV
      exact ⟨x', hx', hb, fun p => (hp p).2⟩)
  intro i
  refine measure_mono_null ?_ (measure_union_null (hn0 i) (hn1 i))
  rintro w ⟨hw, hw'⟩
  obtain ⟨hO, hs | ⟨p, hp | hp⟩⟩ := hw'
  · exact Or.inl ⟨hw, hO, Or.inl hs⟩
  · exact Or.inl ⟨hw, hO, Or.inr ⟨p, hp⟩⟩
  · exact Or.inr ⟨hw, hO, Or.inr ⟨p, hp⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem null_off_bigCell_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q), IsNull FA.Re.R.A {x | FA.pr (FA.Re.π x) ∈ BM.O l ∧ (FA.pr (FA.Re.π x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x))) (FA.Re.R.lift x x) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l
  exact GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM _ FA.Re.R.X FA.Re.R.A FA.Re.R.U FA.Re.R.lift
    (FA.pr ∘ FA.Re.π) l (Pr.holoMap_comp' FA.Re.holo FA.pr_holo) (fun x => FA.Re.R.isOpen_U x)
    (fun x => FA.Re.R.mem_U x) (fun x p => FA.Re.R.holo x p)
    (fun x y' hy => FA.Re.R.compat x y' y' ⟨hy, FA.Re.R.mem_U y'⟩)
    (fun x hx V hV hxV => GlobalTheory.T.flag_analytic_dense_good_points K ι Φ y Ψ N j M n d BM FA l x hx V hV hxV)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.flag_adjacent_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Flag

variable {Ψ : Type} {N j n e : ℕ}

theorem analytic_pMat (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ PIdx j keep ≃ Fin e)
    (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pMat keep (pL ε w) τ a b) s := by
  unfold pMat lowMat
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · simp only [hc, dite_true]
    by_cases hs : Sep keep (⟨(τ, a, b), hc⟩ : LowIdx Ψ N j)
    · simp only [cExt, hs, dite_true, pL]
      exact analytic_coord _
    · simp only [cExt, hs, dite_false]
      exact analyticOnNhd_const
  · simp only [hc, dite_false]
    exact analyticOnNhd_const

theorem analytic_pH (keep : Ψ × Fin N → Prop) (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => pH keep h ε τ w a b) s := by
  unfold pH
  exact analytic_mul_entry (fun _ => h τ) _ (fun _ _ => analyticOnNhd_const)
    (analytic_pMat keep s ε τ) a b

theorem analytic_pB {Λ : Type} (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (pB ε) (pD ε V) := by
  have : pB ε = ⇑(ContinuousLinearMap.pi (R := ℂ) fun i : Fin n =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (ε (Sum.inl i))) := by
    funext w i
    rfl
  rw [this]
  exact fun w _ => ContinuousLinearMap.analyticAt _ w

end Flag

theorem pPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => pPhi M F keep v bl h ε w p) (pD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc p
  obtain ⟨-, -, -, hb, -⟩ := hc
  obtain ⟨-, -, hbl, hval, -⟩ := hb
  have hmap : Set.MapsTo (pB ε) (pD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (pB ε w) q) (pD ε V) := fun q =>
    (hbl q).comp (analytic_pB ε V) hmap
  have hv : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (pB ε w))) (pD ε V) := fun q I =>
    (hval q I).comp (analytic_pB ε V) hmap
  exact analytic_flagZ M F (fun w => bl (pB ε w)) (fun w τ' => pH keep h ε τ' w) hzb hv
    (fun τ' => analytic_pH keep _ h ε τ') (v p)

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo
end
end
