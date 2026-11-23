module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle145
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle147
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem orbit_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z' z) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem eq_of_orbit_of_normalised {u v : (Σ k, ι k) → ℂ} (h : SameOrbit u v) (e : ∀ k, ι k)
    (hu : ∀ k, u ⟨k, e k⟩ = 1) (hv : ∀ k, v ⟨k, e k⟩ = 1) : u = v := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : ∀ k, c k = 1 := fun k => by
    have h2 : c k * v ⟨k, e k⟩ = 1 := hu k
    rwa [hv k, mul_one] at h2
  funext p
  show c p.1 * v p = v p
  rw [h1 p.1, one_mul]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem base_of_orbit (M : FlagModel y Ψ N j) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z')
    (hz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) :
    mCoordIdeal (basePart M.blk z') = mCoordIdeal (basePart M.blk z) ∧
      basePart M.blk z' ∈ mcPts (mCoordIdeal M.x) := by
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho
  have h := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k => c k.1) (fun k => hc k.1)
  exact ⟨h.1, (h.2 hz).1⟩

theorem normRhs_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀ z₁ z₀' z₁' h h' t t' hmc hn₀ hn₁ hbase
    hF hF' hG hG' ho₀ ho₁ hh hd hh' hd' ht ht' hE₀ hE₁ hE₀' hE₁'
  obtain ⟨hid, hmc'⟩ := base_of_orbit M ho₀ hmc
  have hn₀' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₀) hn₀
  have hn₁' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁) hn₁
  have hbase' : basePart M.blk z₁' = basePart M.blk z₀' := by
    have h1 : SameOrbit (basePart M.blk z₁') (basePart M.blk z₁) :=
      basePart_orbit M.blk (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁)
    rw [hbase] at h1
    exact eq_of_orbit_of_normalised
      (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans h1 (basePart_orbit M.blk ho₀)) F'.c (hE₁' a).1 (hE₀' a).1
  obtain ⟨w₀, w₁, S, hw₀, hw₁, hS, hSd, hX₀, hX₁, hnorm⟩ :=
    GlobalTheory.T.flag_adjacent_frame_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀' z₁' h' t' hmc' hn₀' hn₁' hbase'
      hF hF' (by rw [hid]; exact hG) hG' hh' hd' ht' hE₀' hE₁'
  rw [← hnorm]
  exact GlobalTheory.T.flag_adjacent_orbit_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F z₀ z₁ w₀ w₁ h (S * h') t t' hmc hn₀ hn₁
    hbase hF hG (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₀ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₀))
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₁ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₁)) hh hd (hS.mul hh')
    (by rw [Matrix.det_mul]; exact mul_ne_zero hSd hd') ht ht' hE₀ hE₁ hX₀ hX₁

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix


theorem _root_.GlobalTheory.T.mixed_integral_limit_on_model : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv <;> assumption)
end
