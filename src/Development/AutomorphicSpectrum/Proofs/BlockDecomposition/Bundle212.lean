module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Aesop.Main
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle202
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle204
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle027
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaModular
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

private theorem conj_apply_lemma (k : Type) [Field k] {N : ℕ} (w : Equiv.Perm (Fin N))
    (A : GL (Fin N) k) (u v : Fin N) :
    (↑(permGL k w * A * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) (w u) (w v) =
      (↑A : Matrix (Fin N) (Fin N) k) u v := by
  have hv : ∀ σ : Equiv.Perm (Fin N),
      (↑(permGL k σ) : Matrix (Fin N) (Fin N) k) = (σ⁻¹).toPEquiv.toMatrix := fun σ => rfl
  rw [← map_inv, Units.val_mul, Units.val_mul, hv, hv, inv_inv, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  simp [Matrix.submatrix_apply]

theorem GlobalTheory.CompanionTheory.GeomCell.innerMat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (e' : (Σ j, m' j) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (w : Equiv.Perm (Fin N)) (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) (p : Levi k m') (hp : p ∈ relParab k g) (hx : permGL k w * leviEmb k e' p * (permGL k w)⁻¹ ∈ blockUpper k N β), ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨_, hx⟩ : levi k N β) : GL (Fin N) k) = leviEmb k e (relEmb k f (swapBlocks k c (relProj k g ⟨p, hp⟩))) := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ m' _ _ c _ _ e β hβ e' f g w hcell p hp hx
  have key : ∀ a b : Fin N, β a = β b ↔ blk e a = blk e b := by
    intro a b
    constructor
    · intro h
      rcases lt_trichotomy (blk e a) (blk e b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mpr h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mpr h'))
    · intro h
      rcases lt_trichotomy (β a) (β b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mp h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mp h'))
  have hL : ∀ x y, (↑(↑((GroundTheory.Automorphic.Parabolic.leviProj k N β) ⟨_, hx⟩ : levi k N β) :
      GL (Fin N) k) : Matrix (Fin N) (Fin N) k) x y = if β x = β y then
      (↑(permGL k w * leviEmb k e' p * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) x y else 0 :=
    fun x y => rfl
  have hrel : ∀ (Q : ∀ i, Levi k (c i)) (i : α), relEmb k f Q i = leviEmb k (f i) (Q i) :=
    fun Q i => rfl
  have hsw : ∀ (R : ∀ j, Levi k (fun i => c i j)) (i : α) (j : β'), swapBlocks k c R i j = R j i :=
    fun R i j => rfl
  have hproj : ∀ (j : β') (i : α) (s s' : c i j),
      (↑((relProj k g ⟨p, hp⟩) j i) : Matrix (c i j) (c i j) k) s s' =
        (↑(p j) : Matrix (m' j) (m' j) k) (g j ⟨i, s⟩) (g j ⟨i, s'⟩) :=
    fun j i s s' => leviProj_apply k (g j) _ i s s'
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := (f i).surjective a
  obtain ⟨⟨i', a'⟩, rfl⟩ := e.surjective y
  obtain ⟨⟨j', t'⟩, rfl⟩ := (f i').surjective a'
  rw [hL]
  by_cases hii : i = i'
  · subst hii
    rw [if_pos ((key _ _).mpr (by rw [blk_apply, blk_apply])), ← hcell i j t, ← hcell i j' t',
      conj_apply_lemma, hcell i j t, hcell i j' t', leviEmb_apply_same, hrel]
    by_cases hjj : j = j'
    · subst hjj
      rw [leviEmb_apply_same, leviEmb_apply_same, hsw, hproj]
    · rw [leviEmb_apply_ne k e' p hjj, leviEmb_apply_ne k (f i) _ hjj]
  · rw [if_neg (fun h => hii (by rw [key, blk_apply, blk_apply] at h; exact h)),
      leviEmb_apply_ne k e _ hii]
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.IntDeriv

variable {n : ℕ}

theorem hasDerivAt_fderiv {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => ρ r y) (fderiv ℝ (Function.uncurry ρ) (s, y) (1, 0)) s := by
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod isOpen_GLs
  have hd : DifferentiableAt ℝ (Function.uncurry ρ) (s, y) :=
    ((h.contDiffAt (hopen.mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt (by simp))
  have hc : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : Mat n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have hd' : HasFDerivAt (Function.uncurry ρ) (fderiv ℝ (Function.uncurry ρ) (s, y))
      ((fun r : ℝ => (r, y)) s) := hd.hasFDerivAt
  exact hd'.comp_hasDerivAt s hc

theorem hasDerivAt_dt {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => ρ r y) (dt ρ s y) s := by
  have h2 := hasDerivAt_fderiv h s hy
  have : dt ρ s y = fderiv ℝ (Function.uncurry ρ) (s, y) (1, 0) := h2.deriv
  rw [this]; exact h2

theorem continuousOn_dt {ρ : ℝ → Mat n → ℝ} (h : Sm ρ) :
    ContinuousOn (Function.uncurry (dt ρ)) (Set.univ ×ˢ GLs n) := by
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) := isOpen_univ.prod isOpen_GLs
  have hc : ContinuousOn (fderiv ℝ (Function.uncurry ρ)) (Set.univ ×ˢ GLs n) :=
    ContDiffOn.continuousOn_fderiv_of_isOpen h hopen (by simp)
  have h1 : ContinuousOn (fun p : ℝ × Mat n => fderiv ℝ (Function.uncurry ρ) p (1, 0))
      (Set.univ ×ˢ GLs n) := hc.clm_apply continuousOn_const
  refine h1.congr ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact (hasDerivAt_fderiv h s hy).deriv

theorem continuous_val_G : Continuous (fun y : G n => (y.val : Mat n)) := Units.continuous_val

theorem continuous_comp_val {W : Type} [TopologicalSpace W] {f : ℝ → Mat n → W}
    (h : ContinuousOn (Function.uncurry f) (Set.univ ×ˢ GLs n)) :
    Continuous (fun p : ℝ × G n => f p.1 p.2.val) := by
  have hm : Continuous (fun p : ℝ × G n => ((p.1, p.2.val) : ℝ × Mat n)) :=
    continuous_fst.prodMk (continuous_val_G.comp continuous_snd)
  exact h.comp_continuous hm (fun p => ⟨Set.mem_univ _, val_mem_GLs p.2⟩)

theorem hasDerivAt_integral_compact {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (ρ : ℝ → Mat n → ℝ) (hρ : Sm ρ) (K : Set (G n)) (hK : IsCompact K)
    (s₀ ε : ℝ) (hε : 0 < ε)
    (hv : ∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → ρ s y.val = 0) :
    HasDerivAt (fun s => ∫ y : G n, ρ s y.val ∂μ) (∫ y : G n, dt ρ s₀ y.val ∂μ) s₀ := by
  have hF : Continuous (fun p : ℝ × G n => ρ p.1 p.2.val) := continuous_comp_val hρ.continuousOn
  have hF' : Continuous (fun p : ℝ × G n => dt ρ p.1 p.2.val) :=
    continuous_comp_val (continuousOn_dt hρ)
  have hFs : ∀ s, Continuous (fun y : G n => ρ s y.val) := fun s =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hFs' : ∀ s, Continuous (fun y : G n => dt ρ s y.val) := fun s =>
    hF'.comp (continuous_const.prodMk continuous_id)
  have hKm : MeasurableSet K := hK.measurableSet
  have hv' : ∀ s ∈ Metric.ball s₀ ε, ∀ y : G n, y ∉ K → dt ρ s y.val = 0 := by
    intro s hs y hy
    have hev : (fun r => ρ r y.val) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hs] with r hr using hv r hr y hy
    have : dt ρ s y.val = deriv (fun r => ρ r y.val) s := rfl
    rw [this, hev.deriv_eq]; simp
  have hint : ∀ s ∈ Metric.ball s₀ ε, Integrable (fun y : G n => ρ s y.val) μ := by
    intro s hs
    refine (hFs s).integrable_of_hasCompactSupport (HasCompactSupport.intro hK ?_)
    exact fun y hy => hv s hs y hy
  have hint' : Integrable (fun y : G n => dt ρ s₀ y.val) μ := by
    refine (hFs' s₀).integrable_of_hasCompactSupport (HasCompactSupport.intro hK ?_)
    exact fun y hy => hv' s₀ (Metric.mem_ball_self hε) y hy
  have hs₀ : s₀ ∈ Metric.ball s₀ ε := Metric.mem_ball_self hε
  obtain ⟨M, hM⟩ := ((isCompact_closedBall s₀ (ε / 2)).prod hK).exists_bound_of_continuousOn
    hF'.continuousOn
  have hball : Metric.ball s₀ (ε / 2) ⊆ Metric.ball s₀ ε := Metric.ball_subset_ball (by linarith)
  have hbound : ∀ᵐ y ∂μ, ∀ s ∈ Metric.ball s₀ (ε / 2),
      ‖dt ρ s (y : G n).val‖ ≤ K.indicator (fun _ => M) y := by
    refine Filter.Eventually.of_forall fun y s hs => ?_
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      exact hM (s, y) ⟨Metric.ball_subset_closedBall hs, hy⟩
    · rw [Set.indicator_of_notMem hy, hv' s (hball hs) y hy]; simp
  have hbi : Integrable (K.indicator (fun _ : G n => M)) μ :=
    (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s (y : G n) => ρ s y.val) (F' := fun s (y : G n) => dt ρ s y.val)
    (x₀ := s₀) (s := Metric.ball s₀ (ε / 2)) (bound := K.indicator (fun _ => M))
    (Metric.ball_mem_nhds s₀ (by linarith))
    (Filter.Eventually.of_forall fun s => (hFs s).aestronglyMeasurable)
    (hint s₀ hs₀) hint'.aestronglyMeasurable hbound hbi
    (Filter.Eventually.of_forall fun y s _ => hasDerivAt_dt hρ s (val_mem_GLs y))
  exact this.2

end GlobalTheory.CompanionTheory.WaveSpd.IntDeriv
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.DensDeriv

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def tD (u : ℝ → E → W) : ℝ → E → W := fun s y => deriv (fun r => u r y) s

def rD (L : E →L[ℝ] E) (u : ℝ → E → W) : ℝ → E → W := fun s y => fderiv ℝ (u s) y (L y)

variable {U : Set E} {u : ℝ → E → W}

theorem contDiffAt_F (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) :=
  hu.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _, hy⟩)

theorem hasFDerivAt_F (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((contDiffAt_F hU hu s hy).differentiableAt (by simp)).hasFDerivAt

theorem hasDerivAt_line (y : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ((r, y) : ℝ × E)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem hasDerivAt_time (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasDerivAt (fun r => u r y) (fderiv ℝ (Function.uncurry u) (s, y) (1, 0)) s :=
  by
  have h : HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y))
      ((fun r : ℝ => ((r, y) : ℝ × E)) s) := hasFDerivAt_F hU hu s hy
  exact h.comp_hasDerivAt s (hasDerivAt_line y s)

theorem tD_eq (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    tD u s y = fderiv ℝ (Function.uncurry u) (s, y) (1, 0) :=
  (hasDerivAt_time hU hu s hy).deriv

theorem rD_eq (L : E →L[ℝ] E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    rD L u s y = fderiv ℝ (Function.uncurry u) (s, y) (0, L y) := by
  have h2 := (hasFDerivAt_F hU hu s hy).comp y (hasFDerivAt_prodMk_right s y)
  have h3 : fderiv ℝ (u s) y = _ := HasFDerivAt.fderiv (f := u s) h2
  simp only [rD]
  rw [h3]
  simp

theorem contDiffOn_fderivF (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ U) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hU) (by simp)

theorem contDiffOn_tD (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (Function.uncurry (tD u)) (Set.univ ×ˢ U) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ (Function.uncurry u) p (1, 0))
      (Set.univ ×ˢ U) :=
    (contDiffOn_fderivF hU hu).clm_apply contDiffOn_const
  refine h.congr ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact tD_eq hU hu s hy

theorem tD_rD (L : E →L[ℝ] E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ U)) (s : ℝ) {y : E} (hy : y ∈ U) :
    HasDerivAt (fun r => rD L u r y) (fderiv ℝ (tD u s) y (L y)) s := by
  set F := Function.uncurry u with hF
  have hD : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (s, y)) (s, y) :=
    (((contDiffOn_fderivF hU hu).contDiffAt
      ((isOpen_univ.prod hU).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
      (by simp)).hasFDerivAt
  have hL : HasDerivAt (fun r => rD L u r y)
      (fderiv ℝ (fderiv ℝ F) (s, y) (1, 0) (0, L y)) s := by
    have h2 : HasDerivAt (fun r => fderiv ℝ F (r, y))
        (fderiv ℝ (fderiv ℝ F) (s, y) (1, 0)) s :=
      hD.comp_hasDerivAt s (hasDerivAt_line y s)
    have h3 := h2.clm_apply (hasDerivAt_const s ((0 : ℝ), L y))
    simp only [ContinuousLinearMap.map_zero, add_zero] at h3
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    exact rD_eq L hU hu r hy
  have hR : HasFDerivAt (tD u s)
      (((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        (fderiv ℝ (fderiv ℝ F) (s, y))).comp (ContinuousLinearMap.inr ℝ ℝ E)) y := by
    have h2 := (ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt.comp y
      (hD.comp y (hasFDerivAt_prodMk_right s y))
    refine HasFDerivAt.congr_of_eventuallyEq h2 ?_
    filter_upwards [hU.mem_nhds hy] with z hz
    exact tD_eq hU hu s hz
  have hsym : IsSymmSndFDerivAt ℝ F (s, y) :=
    (contDiffAt_F hU hu s hy).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [hR.fderiv]
  have e : fderiv ℝ (fderiv ℝ F) (s, y) (1, 0) (0, L y)
      = fderiv ℝ (fderiv ℝ F) (s, y) (0, L y) (1, 0) := hsym _ _
  simpa [e] using hL

end Generic

section Mat

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g * X
      map_add' := fun a b => Matrix.add_mul a b X
      map_smul' := fun c a => by simp }

theorem sm_dt {u : ℝ → Mat n → W} (hu : Sm u) : Sm (dt u) :=
  contDiffOn_tD isOpen_GLs hu

theorem hasDerivAt_dt {u : ℝ → Mat n → W} (hu : Sm u) (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun r => u r y) (dt u s y) s := by
  have h := hasDerivAt_time isOpen_GLs hu s hy
  rwa [← tD_eq isOpen_GLs hu s hy] at h

theorem hasDerivAt_Rt {u : ℝ → Mat n → W} (hu : Sm u) (X : Mat n) (s : ℝ) {y : Mat n}
    (hy : y ∈ GLs n) : HasDerivAt (fun r => Rt X u r y) (Rr X (dt u s) y) s :=
  tD_rD (mulR X) isOpen_GLs hu s hy

end Mat

end GlobalTheory.CompanionTheory.WaveSpd.DensDeriv


open GlobalTheory.CompanionTheory.WaveSpd.DensDeriv in
theorem GlobalTheory.CompanionTheory.WaveSpd.hasDerivAt_dens {n : ℕ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (u : ℝ → Mat n → W) (hu : Sm u) (s : ℝ) (y : Mat n)
    (hy : y ∈ GLs n) :
    HasDerivAt (fun r => dens u r y)
      (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ
        + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ
        + 2 * ⟪dt u s y, u s y⟫_ℝ) s := by
  have h1 := (hasDerivAt_dt (sm_dt hu) s hy).norm_sq
  have h3 := (hasDerivAt_dt hu s hy).norm_sq
  have h2 : HasDerivAt (fun r => ∑ p : Ix n, ‖Rt (hm p) u r y‖ ^ 2)
      (∑ p : Ix n, 2 * ⟪Rt (hm p) u s y, Rr (hm p) (dt u s) y⟫_ℝ) s := by
    have := HasDerivAt.fun_sum (u := Finset.univ)
      (fun (p : Ix n) _ => (hasDerivAt_Rt hu (hm p) s hy).norm_sq)
    exact this
  have h := (h1.add (h2.const_mul (1 / 4 : ℝ))).add h3
  refine (h.congr_deriv ?_)
  rw [real_inner_comm (dt (dt u) s y), real_inner_comm (dt u s y) (u s y), ← Finset.mul_sum]
  simp only [real_inner_comm (Rt _ u s y)]
  ring
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.pairing_iso_of_component_isos : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | exact GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_product_local_coords : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | exact GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem hasCompactSupport_of_isBump {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) fun x hx => hg.2.2 x ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
  exact hx

theorem isBump_gconv : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  intro g g' T T' hg hg'
  refine ⟨?_, ?_, ?_⟩
  · have hconv : gconv g g' = MeasureTheory.convolution g g' (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext r
      simp [gconv, MeasureTheory.convolution]
    rw [hconv]
    exact (hasCompactSupport_of_isBump hg').contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hg.1.continuous.locallyIntegrable hg'.1
  · intro r
    unfold gconv
    calc ∫ t, g t * g' (-r - t) = ∫ t, g (-t) * g' (-r - -t) := (integral_neg_eq_self _ _).symm
      _ = ∫ t, g t * g' (r - t) := by
        congr 1
        funext t
        rw [hg.2.1 t, show -r - -t = -(r - t) by ring, hg'.2.1]
  · intro r hr
    have hzero : ∀ t, g t * g' (r - t) = 0 := by
      intro t
      by_cases ht : T < |t|
      · rw [hg.2.2 t ht, zero_mul]
      · rw [hg'.2.2 (r - t) ?_, mul_zero]
        have h1 := abs_sub_abs_le_abs_sub r t
        have ht' := not_lt.mp ht
        linarith
    simp [gconv, hzero]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem gser_mul_prod : ∀ (n : ℕ) (c : Fin n → ℂ),
    (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  intro n c
  have h := GlobalTheory.Dec.GelfSepProof.gen (fun a => c a + ((n : ℂ) - 1) / 2)
  have e : gser c = PowerSeries.mk (fun k => ∑ a, ∑ b,
      (Formalism.REAL.Amat (fun a => c a + ((n : ℂ) - 1) / 2) ^ k) a b) := rfl
  rw [e]
  simpa only [map_add (f := _), map_one] using h

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.card_unimodular_hermitian_reps_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_one | exact GlobalTheory.CompanionTheory.UnrDens.solCount_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_one <;> assumption)
end

end

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.levi_double_coset_intersection : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (e' : (Σ j, m' j) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (w : Equiv.Perm (Fin N)) (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) (p : Levi k m') (hp : p ∈ relParab k g) (hx : permGL k w * leviEmb k e' p * (permGL k w)⁻¹ ∈ blockUpper k N β), ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨_, hx⟩ : levi k N β) : GL (Fin N) k) = leviEmb k e (relEmb k f (swapBlocks k c (relProj k g ⟨p, hp⟩))) := by
  first | exact @GlobalTheory.CompanionTheory.GeomCell.innerMat | exact GlobalTheory.CompanionTheory.GeomCell.innerMat | (intros; apply GlobalTheory.CompanionTheory.GeomCell.innerMat <;> assumption)

end
end
