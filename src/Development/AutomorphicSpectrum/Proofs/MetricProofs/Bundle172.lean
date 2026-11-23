module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle168
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle136
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle167
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle129
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle161
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.flag_point_in_multiprojective_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.flagPt M (BM.F l) (FC.bvec BM l b) h ∈ mcPts (mCoordIdeal y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flagPt_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flagPt_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flagPt_mem_mcPts <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.base_chart_holomorphic_composition : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q) (e : ℕ) (V : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → BM.Rb.X), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V) ∧ ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) → AnalyticOnNhd ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.exists_flag_point_in_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) (BM.Rb.lift b b) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.flagPt M (BM.F l) (FC.bvec BM l b) h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem _root_.GlobalTheory.T.lower_unipotent_orbit_equality : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.flag_adjacent_chart_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, wPhi M F bl h ε k₀ τ ca cb w ∈ wO M Rb τ a k₀ ca cb F kb V r h ∧ wRho M Rb τ k₀ ca cb F kb r h ε (wPhi M F bl h ε k₀ τ ca cb w) = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Read.chart_reads | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Read.chart_reads | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Read.chart_reads <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_smul {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (c : K → ℂ)
    (z : (Σ k, ιk k) → ℂ) (q : Σ k, ι k) :
    upV v (fun p => c (κ p.1) * z p) q = c q.1 * upV v z q := by
  unfold upV
  by_cases h : ∃ q', v q' = q
  · rw [dif_pos h, dif_pos h]
    have e : κ h.choose.1 = q.1 := by
      rw [← hb.2.2.1, h.choose_spec]
    show c (κ h.choose.1) * z h.choose = _
    rw [e]
  · rw [dif_neg h, dif_neg h, mul_zero]

end Scale

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h ∧ z ∈ pO M Rb keep v F kb V r h := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n Rb keep Kk _ ιk _ κ v hbm hrange z hz
  obtain ⟨bs, -⟩ := GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange
  obtain ⟨-, fr, -⟩ := CPts.main K ι Φ y Ψ N j M
  have hzb : pBase M v z ∈ mcPts (mCoordIdeal M.x) := bs z hz
  obtain ⟨F, hF, hG⟩ := fr _ hzb
  have hnon : Nonempty Rb.X := by
    obtain ⟨x, -⟩ := Rb.surj _ hzb fun h => by
      have := h.2 1 Submodule.mem_top
      simp at this
    exact ⟨x⟩
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.T.exists_continuous_orbit_section _ _ _ n Rb hnon
  have hx0 := hr1 _ hzb
  obtain ⟨kb, V, bl, hsrc, hV, hBC⟩ := GlobalTheory.T.exists_base_chart_at_good_point K ι Φ y Ψ N j M n Rb F (r (pBase M v z))
    (by rw [CovMap.mCoordIdeal_eq_of_sameOrbit hx0]; exact hG)
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hsrc] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (pBase M v z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (pBase M v z) := orbit_trans (orbit_symm hblorb) hx0
  have hval : ∀ s, (∃ u, IsValueAt M.x s zc u) → valAt M.x s (pBase M v z) = valAt M.x s zc :=
    fun s hs => valAt_eq_of_orbit hblm hzb (orbit_symm horb) hs
  obtain ⟨c₀, hc₀, he⟩ := horb
  let c : K → ℂ := fun k => if h : ∀ p, M.blk p ≠ some k then c₀ ⟨k, h⟩ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M.blk p ≠ some k
    · simp only [c, dif_pos h]
      exact hc₀ _
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z' : (Σ k, ιk k) → ℂ := fun p => c (κ p.1) * z p
  have hz' : z' ∈ mcPts (mCoordIdeal (y ∘ v)) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) (fun k => c (κ k)) (fun k => hc _) hz
  have hbp : pBase M v z' = zc := by
    rw [he]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    show upV v z' ⟨k, m⟩ = c₀ ⟨k, hk⟩ * upV v z ⟨k, m⟩
    rw [upV_smul hbm c z ⟨k, m⟩]
    simp only [c, dif_pos hk]
  obtain ⟨h, hh, H⟩ := GlobalTheory.T.blockMap_frame_restriction_regular K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange F z' hF hz'
    (hbp ▸ hblgood) (hbp ▸ hblnorm)
  refine ⟨F, kb, V, bl, r, h, ⟨hbm, hrange, hF, hBC, hr1, hr2, hh⟩, hz, hsrc, ?_, ?_⟩
  · rw [hzc] at *
    exact hV
  · intro p k hkeep hp
    obtain ⟨A, hA0, hA'⟩ := H p k hkeep hp
    have hk : c k = 1 := dif_neg fun e => e p hp
    have hw : ∀ m : ι k, upV v z ⟨k, m⟩ =
        A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (h p.1) I (stepCols N j p.2) := fun m => by
      have e : upV v z' ⟨k, m⟩ = upV v z ⟨k, m⟩ := by
        rw [upV_smul hbm c z ⟨k, m⟩]
        show c k * _ = _
        rw [hk, one_mul]
      rw [← e, hA' m, hbp]
      refine congrArg (fun s => A * s) (Finset.sum_congr rfl fun I _ => ?_)
      rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    rw [twMinor_of_flag M hF hzb hG hp (hh p.1).1 hw, Matrix.nonsing_inv_mul _ (hh p.1).2.isUnit, CPts.minorIJ_one,
      mul_one]
    exact hA0

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover
end
end
