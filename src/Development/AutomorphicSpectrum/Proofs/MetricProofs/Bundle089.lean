module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenLatticesDifferentStatementHolds
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.exists_eigenComponent_polynomial : ∀ (E : Type) [Field E] [NumberField E] (s₀ : 𝓞 E →+* ℂ), ∃ c : 𝓞 E →₀ ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V), (∀ x, eigComp ρ s₀ x = ∑ a ∈ c.support, c a • ρ a x) ∧ (∀ x, eigComp ρ s₀ x ∈ eigSp ρ s₀) ∧ ∀ x ∈ eigSp ρ s₀, eigComp ρ s₀ x = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def pairV {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) : (Σ k, Sum.elim ι ι' k) → R
  | ⟨.inl k, i⟩ => a ⟨k, i⟩
  | ⟨.inr k, i⟩ => b ⟨k, i⟩

theorem pairV_inl {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι k) :
    pairV a b (inlV p) = a p := rfl

theorem pairV_inr {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι' k) :
    pairV a b (inrV p) = b p := rfl

def stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) : Ψ × Fin N :=
  Classical.choose (not_forall_not.1 (by simpa using h) : ∃ p, M.blk p = some k)

theorem blk_stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) :
    M.blk (stepOf M k h) = some k := by
  unfold stepOf
  exact Classical.choose_spec (p := fun p => M.blk p = some k) _

def transPt {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) : (Σ k, ι k) → Φ' := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then algebraMap M'.Ω Φ' (Cv.φ (M.x ⟨⟨q.1, h⟩, q.2⟩))
  else ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef q I)) *
    minorIJ (M'.g (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem transPt_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (q : Σ k, baseIdx ι M.blk k) :
    transPt Cv ⟨q.1.1, q.2⟩ = algebraMap M'.Ω Φ' (Cv.φ (M.x q)) :=
  dif_pos q.1.2

theorem transPt_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (m : ι k) :
    transPt Cv ⟨k, m⟩ = ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef ⟨k, m⟩ I)) * minorIJ (M'.g p.1) I (stepCols N j p.2) := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun H => H p hp
  have e : stepOf M k h = p := M.blk_inj _ _ k (blk_stepOf M k h) hp
  rw [transPt, dite_eq_right h, e]

def trMat {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) : Matrix (Fin N) (Fin N) M'.Ω :=
  ((F.T τ).map Cv.φ)⁻¹ * F'.T τ

def coE {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N)
    (q : Σ k, ι k) (r : Σ k, ι' k) : M'.Ω :=
  ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
    Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

def grMat (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (I₀ : Finset (Fin N)) (w : Finset (Fin N) → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  C + ∑ I, (w I / w I₀) • B I

def IsGrChart (N j : ℕ) (i : Fin N) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ)
    (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (w : Finset (Fin N) → ℂ), IsBlockDiag j h → h.det ≠ 0 → a ≠ 0 →
    (∀ I, IsStepRows N j i I → w I = a * minorIJ h I (stepCols N j i)) → w I₀ ≠ 0 →
      IsBlockDiag j (grMat C B I₀ w) ∧ (grMat C B I₀ w).det ≠ 0 ∧
        ∀ I, minorIJ (grMat C B I₀ w) I (stepCols N j i) * w I₀ = a * minorIJ h I (stepCols N j i)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (k₀ : K) (z : (Σ k, ι k) → ℂ)
    (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) (basePart M.blk z) * z ⟨k₀, m⟩

def baseMono (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℂ :=
  ∏ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ^ M.dy p k.1

def stepGap (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((BM.hom p).h z) - Real.log ((fsHerm ι (M.dy p)).h z)

def stepPh (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x : R.X) : ℝ :=
  if h : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x then stepGap M BM p h.2.choose else 0

def IsStepHyp (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  IsBlockMap κ v ∧ (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) ∧
    HoloMap R.A BM.Rb.A pr ∧
    ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))

def IsStepChart (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x y₀ : R.X) (W : Set R.X) (l : Fin BM.q)
    (H : R.X → Matrix (Fin N) (Fin N) ℂ) (D : R.X → ℂ) : Prop :=
  IsOpen W ∧ y₀ ∈ W ∧ W ⊆ R.U x ∧ (∀ y' ∈ W, pr y' ∈ BM.O l) ∧
    (∀ a b, R.A.HoloOn W fun y' => H y' a b) ∧ (∀ y' ∈ W, IsBlockDiag j (H y') ∧ (H y').det ≠ 0) ∧
    R.A.HoloOn W D ∧ (∀ y' ∈ W, D y' ≠ 0) ∧
    ∀ y' ∈ W, pr y' ∉ bdry BM.s →
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' =
        blockPot j p.2 (BM.G l p.1 (pr y')) (H y') + Real.log ‖D y'‖

def HasStepCharts (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  ∀ x y₀, y₀ ∈ R.U x → ∃ W l H D, IsStepChart M BM p κ v R pr x y₀ W l H D

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

abbrev PartialFlagBlocks (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : Type :=
  {k : K // (∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k}

instance (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : Fintype (PartialFlagBlocks M p) := Fintype.ofFinite _

abbrev stepIdx (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : PartialFlagBlocks M p → Type := fun k => ι k.1

def stepV (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : (Σ k, stepIdx M p k) → Σ k, ι k :=
  fun q => ⟨q.1.1, q.2⟩

theorem isBlockMap_stepV (M : FlagModel y Ψ N j) (p : Ψ × Fin N) :
    IsBlockMap (Subtype.val : PartialFlagBlocks M p → K) (stepV M p) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨k, hk⟩, m⟩ ⟨⟨k', hk'⟩, m'⟩ h
    simp only [stepV, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h2⟩ := h
    cases h2
    rfl
  · rintro ⟨k, m⟩ ⟨k', rfl⟩
    exact ⟨⟨k', m⟩, rfl⟩

theorem mem_range_step (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k : K) :
    k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) ↔
      ((∀ p', M.blk p' ≠ some k) ∨ ∃ p', p' = p ∧ M.blk p' = some k) := by
  constructor
  · rintro ⟨⟨k', hk'⟩, rfl⟩
    rcases hk' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨p, rfl, h⟩
  · rintro (h | ⟨p', rfl, h⟩)
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · exact ⟨⟨k, Or.inr h⟩, rfl⟩

def IsStepMember {M : FlagModel y Ψ N j} {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (p : Ψ × Fin N) (ph : R.X → ℝ)
    (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine ι) (C₅ C t₀ : ℝ) : Prop :=
  IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y))
      (potOf R (fsHerm ι (M.dy p))) ph C₅ ∧
    IsRegFamily R.A (potOf R (fsHerm ι fun _ => 1)) (BM.L.pullback pr hp.1)
      (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ι (M.dy p))) ph phT C t₀ ∧
    IsRegFamilyC2 R.A (fun x y => BM.s (pr x) (pr y)) ph phT ∧
    (∀ t, (line t).a = M.dy p) ∧
    (∀ t, M.OnStep p (line t)) ∧
    (∀ t, 0 < t → t ≤ t₀ → IsSmoothHerm (line t) ∧ ∀ x, Real.log ((line t).h (R.lift x x)) =
      Real.log ((fsHerm ι (M.dy p)).h (R.lift x x)) + phT t x) ∧
    (∀ x, pr x ∉ bdry BM.s → Real.log ((BM.hom p).h (R.lift x x)) =
      Real.log ((fsHerm ι (M.dy p)).h (R.lift x x)) + ph x) ∧
    (∀ x x', pr x = pr x' →
      (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, R.lift x x ⟨k, m⟩ = a * R.lift x' x' ⟨k, m⟩) →
        ph x = ph x' ∧ ∀ t, phT t x = phT t x') ∧
    ((p.2 : ℕ) + 1 = N → ∀ t, IsPsh R.A ((potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (phT t)).rsmul (-1)) ∧
      IsPsh R.A (potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (phT t)) ∧ phT t = ph)

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}

theorem mConeMap_rename {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv.2.2.1 n]

theorem rename_mem_iff {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    rename v g ∈ mCoordIdeal y ↔ g ∈ mCoordIdeal (y ∘ v) := by
  change mConeMap y (rename v g) = 0 ↔ mConeMap (y ∘ v) g = 0
  rw [mConeMap_rename hv]
  exact map_eq_zero_iff _ (rename_injective κ hv.1)

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap]

theorem mCoordIdeal_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) :
    mCoordIdeal (φ ∘ x) = mCoordIdeal x := by
  ext g
  change mConeMap (φ ∘ x) g = 0 ↔ mConeMap x g = 0
  rw [mConeMap_comp]
  exact map_eq_zero_iff _ (map_injective φ φ.injective)

theorem eval_rename_eq (z : (Σ k, ι' k) → ℂ) (g : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v g)) = eval (z ∘ v) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]

theorem sum_mapDomain_block (hv : ∀ p, (v p).1 = κ p.1) [DecidableEq K'] (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename_block (hb : IsBlockMap κ v) {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  classical
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨⟨k₀, i⟩, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hv.1 ((hv.2.2.1 ⟨k₀, i⟩).symm.trans (congrArg Sigma.fst hp))
    subst hk
    exact ⟨i, by simpa [hp] using hi'⟩
  · have h1 : rename v f ∈ mCoordIdeal x' := by
      rw [rename_mem_iff hv, show x' ∘ v = φ ∘ x from funext hx, mCoordIdeal_comp]
      exact hf
    rw [← eval_rename_eq]
    exact hz.2 _ h1

theorem aeval_rename_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'}
    (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q)) (f : MRing ι) :
    aeval x' (rename v f) = φ (aeval x f) := by
  rw [aeval_rename, show x' ∘ v = φ ∘ x from funext hx, aeval_def, aeval_def, algebraMap_int_eq,
    algebraMap_int_eq, eval₂_comp_left φ, RingHom.ext_int (φ.comp (Int.castRingHom Ω)) (Int.castRingHom Ω')]

theorem regAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal (z ∘ v)) s) :
    RegAt x' (mCoordIdeal z) (φ s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh,
    fun hm => hn ((rename_mem_iff hv z h).1 hm), ?_⟩
  rw [aeval_rename_pull φ hx, aeval_rename_pull φ hx, heq, map_mul]

theorem isValueAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} {w : ℂ} (hs : IsValueAt x s (z ∘ v) w) : IsValueAt x' (φ s) z w := by
  obtain ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩ := hs
  have hpull := aeval_rename_pull (v := v) φ hx
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh, ?_, ?_, ?_, ?_⟩
  · rw [hpull]; exact (map_ne_zero φ).2 hy
  · rw [hpull, hpull, heq, map_mul]
  · rwa [eval_rename_eq]
  · rw [eval_rename_eq, eval_rename_eq]

end General

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) ∧ ∀ s : M.Ω, RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hzb
  have hz := comp_mem_mcPts Cv.block Cv.φ Cv.x_eq hzb
  refine ⟨hz, fun s hs => ?_⟩
  obtain ⟨w, hw⟩ := ValRing.exists_isValueAt hz hs
  have hw' := isValueAt_pull Cv.block Cv.φ Cv.x_eq hw
  exact ⟨regAt_pull Cv.block Cv.φ Cv.x_eq hs, by rw [valAt_eq hzb hw', valAt_eq hz hw]⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem anSys_proportional : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (S : AnSys D (Ψ × Fin N)), j ≤ N → D = antisymDegree Ψ N → IsUniformised S.A S.open' j S.potH → ∃ v : ℝ, 0 < v ∧ toWt S.degPoly = C v * antisymDelta Ψ N := by
  intro hI Ψ _ _ N j D S hj hD hU
  obtain ⟨hO, hNull, -, -, -⟩ := anSys_open_basics D (Ψ × Fin N) S
  have hInt := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned D (Ψ × Fin N) S
  have hmain := GlobalTheory.T.uniformised_potential_integral_formula D S.X S.A Ψ N j S.open' S.th S.ph hj hD hO hNull
    (fun p => (S.sing p).1) (fun p => (S.sing p).2.1) hU (fun w => (hInt w).1)
  obtain ⟨v, hv, hEq⟩ := hmain
  refine ⟨v, hv, ?_⟩
  have hfun : (fun w : Fin D → Ψ × Fin N => mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) (fun _ => 1)) = S.degNum :=
    funext fun w => (hInt w).2
  rw [hfun] at hEq
  exact hEq

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.exists_generic_triangular_factorization : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω), IsGenFam Ω G u → (∀ s, IsUnit (A s).det) → ∃ u' B : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G, IsGenFam Ω G u' ∧ (∀ s, IsUnit (B s).det) ∧ (∀ s a b, b < a → B s a b = 0) ∧ ∀ s, (A s).map (algebraMap Ω G) * u s = u' s * B s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_const_mul_eq_mul_upper | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_const_mul_eq_mul_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_const_mul_eq_mul_upper <;> assumption)
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.chartSection_not_mem_components : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.local_holomorphic_section_of_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (B : HermLine ι), IsSmoothHerm B → ∃ Φ : LocPot M.Xc, IsPotential M.atlas Φ ∧ ∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (B.h z)) (s y') = (G y').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm | exact GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm <;> assumption)
end

section

open NumberField GroundTheory.Heights₂.Heights.NineStatements

theorem _root_.GlobalTheory.T.eigen_lattices_different_statement_holds : GroundTheory.Heights₂.Heights.NineStatements.EigenLatDifferent.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat | exact GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat | (intros; apply GlobalTheory.CompanionTheory.Ar.EigLat.eigenLat_eq_diffLat <;> assumption)
end
