module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle136
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle163
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle164
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle161
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticEighth
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle014
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle165
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

theorem _root_.GlobalTheory.T.sheet_isOpenEmbedding_range : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ), Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) ∧ Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet.isOpenEmbedding_and_range | exact GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet.isOpenEmbedding_and_range | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet.isOpenEmbedding_and_range <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.exists_base_chart_at_good_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X), M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀)) → ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ), x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.flag_adjacent_chart_eighth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.wRho_continuousOn <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.flag_adjacent_chart_tenth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.norm | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.norm | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto.norm <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem continuous_upV (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (upV v) := by
  refine continuous_pi fun q => ?_
  unfold upV
  by_cases h : ∃ q', v q' = q
  · simp only [dif_pos h]
    exact continuous_apply _
  · simp only [dif_neg h]
    exact continuous_const

theorem continuous_pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (pBase M v) := by
  refine continuous_pi fun q => ?_
  exact (continuous_apply (⟨q.1.1, q.2⟩ : Σ k, ι k)).comp (continuous_upV v)

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∃ O' : Set ((Σ k, ιk k) → ℂ), IsOpen O' ∧ pO M Rb keep v F kb V r h = O' ∩ mcPts (mCoordIdeal (y ∘ v)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc
  obtain ⟨hBM, hkp, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (pBase M v) (mcPts (mCoordIdeal (y ∘ v))) (mcPts (mCoordIdeal M.x)) :=
    (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hBM hkp).1
  have key : ∀ z₀ ∈ pO M Rb keep v F kb V r h,
      pO M Rb keep v F kb V r h ∈ 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (pBase M v z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (pBase M v z)) (mcPts (mCoordIdeal (y ∘ v))) z₀ :=
      (hrc _ hbm).comp (continuous_pBase M v).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.continuousWithinAt_twMinor M F (continuous_pBase M v) (continuous_upV v) hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀, ∀ p k, keep p → M.blk p = some k →
        twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : keep p ∧ M.blk p = some k
      · exact ((tw p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm p k hp.1 hp.2)).mono fun _ hz _ _ => hz
      · exact Eventually.of_forall fun _ h₁ h₂ => absurd ⟨h₁, h₂⟩ hp
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃] with z h₀ h₁ h₂ h₃
    exact ⟨h₀, h₁, h₂, h₃⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ pO M Rb keep v F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ pO M Rb keep v F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont

theorem continuous_upV {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Kk : Type} [Fintype Kk]
    {ιk : Kk → Type} [∀ k, Fintype (ιk k)] (v : (Σ k, ιk k) → (Σ k, ι k)) :
    Continuous (upV v) := by
  refine continuous_pi fun q => ?_
  by_cases hq : ∃ q', v q' = q
  · simp only [upV, dif_pos hq]
    exact continuous_apply _
  · simp only [upV, dif_neg hq]
    exact continuous_const

theorem pSgn_ne_zero {Ψ : Type} {N j : ℕ} (hj : j ≤ N) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) :
    pSgn (stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)) q.1.1.2.1 q.1.1.2.2 ≠ 0 := by
  obtain ⟨-, -, hb, ha, hc⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q hj
  have hX : IsLowerUni (pMat (j := j) keep (fun _ => (0 : ℂ)) q.1.1.1) := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · unfold pMat lowMat
      rw [dif_neg (fun h => lt_irrefl _ h.1), if_pos rfl]
    · unfold pMat lowMat
      rw [dif_neg (fun h => lt_asymm hab h.1), if_neg hab.ne]
  exact (GlobalTheory.T.minorIJ_lowerUni_swap N _ _ _ _ hX ha hb q.1.2.1 (hc fun _ => 0).2).2

section Flag

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ContinuousOn (pRho M Rb keep v F kb r h ε) (pO M Rb keep v F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε H
  obtain ⟨hv, hcov, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (pBase M v) (pO M Rb keep v F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hv hcov).1 z hz.1
  have cU : Continuous (upV v) := continuous_upV v
  have cB : Continuous (pBase M v) := continuous_pi fun q =>
    (continuous_apply (⟨q.1.1, q.2⟩ : Σ k, ι k)).comp cU
  have hgood : ∀ z ∈ pO M Rb keep v F kb V r h, M.GoodAt F (mCoordIdeal (pBase M v z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  intro z hz
  have hz₄ : ∀ p k, keep p → M.blk p = some k →
      twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0 := hz.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q
  · simp only [pRho, e]
    have c2 : ContinuousWithinAt (r ∘ pBase M v) (pO M Rb keep v F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ pBase M v) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [pRho, e]
    obtain ⟨hk, -, -, -, -⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q M.j_le
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase
      (hbase hz) (hgood z hz) cU.continuousWithinAt (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ J
    cases e' : M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) with
    | none =>
      simp only [pRead, e', Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [pRead, e', Option.elim_some]
      have hd := mul_ne_zero (pSgn_ne_zero M.j_le keep q) (hz₄ _ k hk e')
      exact ContinuousWithinAt.div (cT k _) (ContinuousWithinAt.mul continuousWithinAt_const (cT k _)) hd

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_cover_arithmetic_eighth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w₀ ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w₀ → ∀ (V : Set ((Σ k, baseIdx ι M.blk k) → ℂ)) (V' : Set ((Σ k, baseIdx ι' M'.blk k) → ℂ)) (s : ((Σ k, baseIdx ι M.blk k) → ℂ) → (Σ k, baseIdx ι' M'.blk k) → ℂ), IsOpen V → basePart M.blk w₀ ∈ V → IsOpen V' → basePart M'.blk z ∈ V' → AnalyticOnNhd ℂ s V → (∀ b'' ∈ V' ∩ mcPts (mCoordIdeal M'.x), ∀ w' ∈ V, SameOrbit w' (b'' ∘ Cv.v) → SameOrbit (s w') b'') → ∃ (U : Set ((Σ k, ι k) → ℂ)) (U' : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι k) → ℂ) → (Σ k, ι' k) → ℂ), IsOpen U ∧ w₀ ∈ U ∧ IsOpen U' ∧ z ∈ U' ∧ AnalyticOnNhd ℂ f U ∧ ∀ z'' ∈ U' ∩ mcPts (mCoordIdeal y'), ∀ w ∈ U ∩ mcPts (mCoordIdeal y), CovMap.IsImg Cv z'' w → SameOrbit (f w) z'' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovLift.lift_inverse | exact GlobalTheory.CompanionTheory.Ar.PB.CovLift.lift_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovLift.lift_inverse <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_cover_arithmetic_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ w ∈ mcPts (mCoordIdeal y), {O | ∃ z ∈ mcPts (mCoordIdeal y'), O = {z'' | SameOrbit z'' z} ∧ CovMap.IsImg Cv z w}.ncard = (GroundTheory.Heights₂.Heights.Inter.ptsOverPt (mCoordIdeal M'.x) Cv.v (basePart M.blk w)).ncard := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibreCount.fibre_count | exact GlobalTheory.CompanionTheory.Ar.PB.FibreCount.fibre_count | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibreCount.fibre_count <;> assumption)
end

section


theorem _root_.GlobalTheory.T.arith_intersection_system_of_poincare_lelong : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.arithIntersectionSystem_of_poincareLelong_resK | exact GlobalTheory.CompanionTheory.Ar.Pub.arithIntersectionSystem_of_poincareLelong_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.arithIntersectionSystem_of_poincareLelong_resK <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.embedding_pieces_of_intersection_and_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.embeddingPieces_of_resK <;> assumption)
end
