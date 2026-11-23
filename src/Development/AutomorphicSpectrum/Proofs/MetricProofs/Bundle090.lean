module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriod
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreDegreeSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
public import Mathlib.Topology.Algebra.MvPolynomial
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def v₀ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) := ⟨some p.1, p.2⟩

def v₁ (k₀ : K) (p : Σ k, ι k) : Σ o : Option K, ι (o.getD k₀) :=
  if h : p.1 = k₀ then ⟨none, cast (congrArg ι h) p.2⟩ else ⟨some p.1, p.2⟩

theorem v₁_ne {k₀ : K} {p : Σ k, ι k} (h : p.1 ≠ k₀) : v₁ k₀ p = ⟨some p.1, p.2⟩ := dif_neg h

theorem v₁_self (k₀ : K) (m : ι k₀) : v₁ k₀ ⟨k₀, m⟩ = ⟨none, m⟩ := dif_pos rfl

def fstPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₀ k₀

def sndPt (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : (Σ k, ι k) → ℂ := z ∘ v₁ k₀

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def normRhs (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : ℝ :=
  Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) *
      (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
        else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ +
    (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁))

def IsNormFn (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (f : RW.X → ℝ) : Prop :=
  ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F →
    M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ (fstPt k₀ (RW.lift x x)) →
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 →
    (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) →
    f x = normRhs M τ a F z₀ z₁ h t

def IsWChart (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e)
    (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsCompatChart RW.A ψ ∧ M.IsFrame F ∧ (∀ i, σ i ≠ i₀) ∧
    (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) ∧
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) ψ.target) ∧
    ∀ x' ∈ ψ.source, (∀ τ', IsBlockDiag j (H τ' (ψ x')) ∧ (H τ' (ψ x')).det ≠ 0) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x' x')))) ∧
      ∃ z₀ z₁ : (Σ k, ι k) → ℂ, SameOrbit z₀ (fstPt k₀ (RW.lift x' x')) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift x' x')) ∧
        ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₀ (H τ' (ψ x')) ∧
          ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₁ (if τ' = τ then H τ (ψ x') * (1 + Matrix.single cb ca (ψ x' i₀)) else H τ' (ψ x'))

def IsWAtlas (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) : Prop :=
  HoloMap RW.A Rb.A pr ∧
    (∀ x, SameOrbit (Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) ∧
    ∀ x, ∃ ψ kb σ i₀ F H, x ∈ ψ.source ∧ IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H

def IsFibreChart {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) : Prop :=
  ∃ (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X),
    (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z₀
        (if τ' = τ then H τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)) else H τ' (Fin.tail z))) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem pullback_pullback {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (P : LocPot X)
    (f : Y → X) (g : Z → Y) (r : Z → X) (hf : Continuous f) (hg : Continuous g) (hr : Continuous r) (h : f ∘ g = r) :
    (P.pullback f hf).pullback g hg = P.pullback r hr := by
  subst h
  rfl

theorem orbit_symm {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem orbit_trans {κ : Type} [Fintype κ] {ρ : κ → Type} {z z' z'' : (Σ k, ρ k) → ℂ}
    (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.exists_isKerProj' : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.exists_isKerProj | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.exists_isKerProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.exists_isKerProj <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.chartW_saturated_and_continuous_section : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (k : ℤ), k ≠ 0 → k • x ∈ chartW bas B → x ∈ chartW bas B) ∧ (∀ x ∈ chartW bas B, ContinuousAt (chartS bas A T0 x) 0 ∧ ∀ w ∈ logCover L.a_le, chartS bas A T0 x (expCover a w) = L.P w x) ∧ Function.Injective (chartPer bas A T0 B) ∧ Submodule.span ℂ (Set.range (chartPer bas A T0 B)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.noMonodromy_lattice <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.mem_chartW_of_continuous_period : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 → (∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) → x ∈ chartW bas B) ∧ ∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre | exact GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods.periods_at_centre <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem normSq_pos {z : (Σ k, ι k) → ℂ} {k : K} (h : ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩

theorem proj_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    proj (fun q => c q.1 * z q) = proj z := by
  funext q
  obtain ⟨k, i, j⟩ := q
  simp only [proj, norm_mul, mul_pow, ← Finset.mul_sum, map_mul]
  have h1 : ((‖c k‖ ^ 2 : ℝ) : ℂ) = c k * starRingEnd ℂ (c k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : c k * starRingEnd ℂ (c k) ≠ 0 := mul_ne_zero (hc k) (by simpa using hc k)
  rw [Complex.ofReal_mul, h1, ← mul_div_mul_left (z ⟨k, i⟩ * starRingEnd ℂ (z ⟨k, j⟩)) _ h2]
  congr 1
  ring

theorem continuousOn_proj :
    ContinuousOn (proj (ι := ι)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine continuousOn_pi.2 fun q => ?_
  refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun z hz => ?_
  exact Complex.ofReal_ne_zero.2 (normSq_pos (hz q.1)).ne'

theorem compactSpace_pts {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    CompactSpace (Pts P) := by
  let S : Set ((Σ k, ι k) → ℂ) := {z | (∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1) ∧ ∀ f ∈ P, eval z f = 0}
  have hne : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    by_contra h
    push Not at h
    have := hz.1 k
    simp [h] at this
  have hS : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · simp only [S, Set.setOf_and, Set.setOf_forall]
      refine IsClosed.inter (isClosed_iInter fun k => isClosed_eq (by fun_prop) continuous_const)
        (isClosed_iInter fun f => isClosed_iInter fun _ =>
          isClosed_eq (MvPolynomial.continuous_eval f) continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      rintro ⟨k, i⟩
      have h1 : ‖z ⟨k, i⟩‖ ^ 2 ≤ 1 := by
        rw [← hz.1 k]
        exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ i)
      nlinarith [norm_nonneg (z ⟨k, i⟩)]
  have hE : Pts P = proj '' S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => normSq_pos (hz.1 k)
      let c : K → ℂ := fun k => (((√(∑ i, ‖z ⟨k, i⟩‖ ^ 2))⁻¹ : ℝ) : ℂ)
      have hc : ∀ k, c k ≠ 0 := fun k =>
        Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hpos k)).ne')
      refine ⟨fun q => c q.1 * z q, ⟨fun k => ?_, eval_eq_zero_of_smul hP c z hz.2⟩, proj_smul c hc z⟩
      simp only [norm_mul, mul_pow, ← Finset.mul_sum, c, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        inv_pow]
      rw [Real.sq_sqrt (hpos k).le, inv_mul_cancel₀ (hpos k).ne']
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, ⟨hne z hz, hz.2⟩, rfl⟩
  rw [← isCompact_iff_compactSpace, hE]
  exact hS.image_of_continuousOn (continuousOn_proj.mono hne)

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem mem_src_iff (p : (k : K) → ι k) (x : Pts P) :
    x ∈ src P p ↔ ∀ k, x.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
  refine forall_congr' fun k => ?_
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  rw [← proj_rep x]
  simp only [proj, ne_eq, div_eq_zero_iff, h, or_false, mul_eq_zero, map_eq_zero, or_self]

theorem isOpen_alt_bis (p : (k : K) → ι k) : IsOpen (src P p) := by
  have : src P p = ⋂ k, {x : Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x; simp [mem_src_iff]
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const

theorem affCoord_rep (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    affCoord p (rep x) q = x.1 ⟨q.1, (q.2, p q.1)⟩ / x.1 ⟨q.1, (p q.1, p q.1)⟩ := by
  obtain ⟨k, i⟩ := q
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  have h1 : rep x ⟨k, p k⟩ ≠ 0 := hx k
  have h2 : starRingEnd ℂ (rep x ⟨k, p k⟩) ≠ 0 := by simpa using h1
  rw [← proj_rep x]
  simp only [proj, affCoord]
  rw [div_div_div_cancel_right₀ h, mul_div_mul_right _ _ h2]

theorem proj_affCoord (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    proj (affCoord p (rep x)) = x.1 := by
  have hA : affCoord p (rep x) = fun q => (rep x ⟨q.1, p q.1⟩)⁻¹ * rep x q := by
    funext q; simp [affCoord, div_eq_inv_mul]
  rw [hA, proj_smul (fun k => (rep x ⟨k, p k⟩)⁻¹) (fun k => inv_ne_zero (hx k)), proj_rep]

theorem isEmbedding_affCoord (p : (k : K) → ι k) :
    Topology.IsEmbedding (fun x : src P p => affCoord p (rep x.1)) := by
  have hc : Continuous (fun x : src P p => affCoord p (rep x.1)) := by
    refine continuous_pi fun q => ?_
    simp only [affCoord_rep p _ (Subtype.prop _)]
    have hv : ∀ r : (Σ k, ι k × ι k), Continuous fun a : src P p => a.1.1 r := fun r =>
      (continuous_apply r).comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.div (hv _) (hv _) fun x => (mem_src_iff p x.1).1 x.2 q.1
  let U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  have hU : ∀ x : src P p, affCoord p (rep x.1) ∈ U := fun x k =>
    ⟨p k, by simpa [affCoord] using x.2 k⟩
  let f : src P p → U := fun x => ⟨_, hU x⟩
  have hf : Continuous f := hc.subtype_mk _
  have hg : Continuous (U.restrict proj) := continuousOn_proj.restrict
  have hgf : U.restrict proj ∘ f = Subtype.val ∘ Subtype.val := by
    funext x; exact proj_affCoord p x.1 x.2
  have he : Topology.IsEmbedding f :=
    Topology.IsEmbedding.of_comp hf hg
      (hgf ▸ Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  exact Topology.IsEmbedding.subtypeVal.comp he

theorem isEmbedding_coord (p : (k : K) → ι k) :
    Topology.IsEmbedding (fun x : src P p => coord P p x) := by
  have h : Topology.IsEmbedding
      (fun y : (Σ k, ι k) → ℂ => (renPt y : Fin (Fintype.card (Σ k, ι k)) → ℂ)) :=
    Function.LeftInverse.isEmbedding (f := fun t => t ∘ Fintype.equivFin (Σ k, ι k))
      (fun y => by funext q; simp [renPt]) (by fun_prop) (by fun_prop)
  exact h.comp (isEmbedding_affCoord p)

theorem compact_open_embedding (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    CompactSpace (Pts P) ∧ ∀ p : (k : K) → ι k,
      IsOpen (src P p) ∧ Topology.IsEmbedding (fun x : src P p => coord P p x) :=
  ⟨compactSpace_pts hP, fun p => ⟨isOpen_alt_bis p, isEmbedding_coord p⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
end
end

section

noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono

theorem exists_unit_mul_monomial_of_primes {m e : ℕ} (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (hI : ∀ h ∈ I, eval t h = 0) [hreg : IsRegularLocalRing (locRing I t)]
    (hdim : ringKrullDim (locRing I t) = e) (r : Fin e → MvPolynomial (Fin m) ℂ) (J : Finset (Fin e))
    (hspan : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t))
    (hpr : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t →
      (Dc ≤ 𝔮 ↔ ∃ i ∈ J, r i ∈ 𝔮))
    (g : MvPolynomial (Fin m) ℂ)
    (hg : ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → g ∈ 𝔮 → Dc ≤ 𝔮) :
    ∃ (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ J → mm i = 0) ∧
      algebraMap _ (locRing I t) g = u * ∏ i ∈ J, algebraMap _ (locRing I t) (r i) ^ mm i := by
  classical
  letI : IsDomain (locRing I t) :=
    ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing (R := locRing I t)
  letI : IsLocalRing (locRing I t) := hreg.toIsLocalRing
  have hKt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := by
    rw [hspan, maximalIdeal_locRing hKt]
  have hdim' : (e : WithBot ℕ∞) = ringKrullDim (locRing I t) := hdim.symm
  have hprime : ∀ i, Prime (algebraMap _ (locRing I t) (r i)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim'

  have hcontr : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t))).IsPrime ∧
      I ≤ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ∧
      𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) ≤ ptIdeal t := by
    intro 𝔓 h𝔓
    refine ⟨Ideal.comap_isPrime _ _, ?_, ?_⟩
    · intro h hh
      rw [Ideal.mem_comap]
      have : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
      rw [this]
      exact 𝔓.zero_mem
    · intro h hh
      rw [Ideal.mem_comap] at hh
      by_contra hne
      have hne' : eval t h ≠ 0 := fun h0 => hne (RingHom.mem_ker.mpr h0)
      have hu := (IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI h).mpr hne'
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ hh hu)
  have hg0 : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g ≠ 0 := by
    intro h0
    obtain ⟨h1, h2, h3⟩ := hcontr ⊥ Ideal.isPrime_bot
    have hgm : g ∈ (⊥ : Ideal (locRing I t)).comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap, h0]; exact Ideal.zero_mem _
    obtain ⟨i, -, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    rw [Ideal.mem_comap, Ideal.mem_bot] at hi
    exact (hprime i).ne_zero hi
  have hrad : (∏ i ∈ J, algebraMap _ (locRing I t) (r i)) ∈
      (Ideal.span {algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro 𝔓 ⟨hle, h𝔓⟩
    obtain ⟨h1, h2, h3⟩ := hcontr 𝔓 h𝔓
    have hgm : g ∈ 𝔓.comap (algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t)) := by
      rw [Ideal.mem_comap]; exact hle (Ideal.mem_span_singleton_self _)
    obtain ⟨i, hiJ, hi⟩ := (hpr _ h1 h2 h3).1 (hg _ h1 h2 h3 hgm)
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hiJ) hi
  exact eq_unit_mul_monomial (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim' J hg0 hrad

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ideal_sup_le_of_mem (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (hP : IsMultiHomogIdeal P) (f : MvPolynomial (Σ k, ι k) ℂ)
    (hf : ∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D)
    (𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) (h𝔮 : 𝔮.IsPrime)
    (hI : SncRes.ideal P p ≤ 𝔮) (hg : bind₁ (SncRes.lift p) f ∈ 𝔮) :
    SncRes.ideal (P ⊔ D) p ≤ 𝔮 := by
  classical
  intro h hh
  have hvan : h ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
    rw [mem_vanishingIdeal_iff]
    intro w hw
    have hw0 : ∀ c ∈ 𝔮, eval w c = 0 := fun c hc => by simpa using hw c hc
    let w' : (Σ k, ι k) → ℂ := w ∘ Fintype.equivFin (Σ k, ι k)
    have hpt : renPt w' = w := by
      funext j
      simp [renPt, w']
    have hren : ∀ x, eval w (renC (Σ k, ι k) x) = eval w' x := fun x => by
      rw [← eval_renC w' x, hpt]
    have hchart : ∀ c ∈ chartIdeal P p, eval w' c = 0 := fun c hc => by
      rw [← hren]
      have hs : (renR (Σ k, ι k)).symm (renC (Σ k, ι k) c) = c := (renR (Σ k, ι k)).symm_apply_apply c
      have hm : renC (Σ k, ι k) c ∈ SncRes.ideal P p := by
        unfold SncRes.ideal
        rw [mem_map_renR_iff, hs]
        exact hc
      exact hw0 _ (hI hm)
    obtain ⟨hcone, h1, -⟩ := conePts_of_chartIdeal hP p w' hchart
    have hlift : (fun q => eval w (SncRes.lift p q)) = w' := by
      funext q
      unfold SncRes.lift
      split_ifs with hq
      · obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        simp [h1 k]
      · simp [w']
    have hfz : eval w' f = 0 := by
      have h2 : eval w (bind₁ (SncRes.lift p) f) = eval (fun q => eval w (SncRes.lift p q)) f :=
        eval₂Hom_bind₁ _ _ _ _
      rw [← hlift, ← h2]
      exact hw0 _ hg
    have hD := hf w' hcone hfz
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval w') := by
      refine sup_le (sup_le (fun c hc => RingHom.mem_ker.mpr (hcone.2 c hc))
        (fun c hc => RingHom.mem_ker.mpr (hD.2 c hc))) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval w' _ = 0
      simp [h1 k]
    have h3 : eval w' ((renR (Σ k, ι k)).symm h) = 0 :=
      RingHom.mem_ker.mp (hle ((mem_map_renR_iff _ h).1 hh))
    have e1 : renC (Σ k, ι k) ((renR (Σ k, ι k)).symm h) = h := (renR (Σ k, ι k)).apply_symm_apply h
    show eval w h = 0
    rw [← e1, hren, h3]
  rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮.radical] at hvan

theorem exists_unit_mul_monomial : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → IsMultiHomog f a → (∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D) → ∃ (u : (locRing (SncRes.ideal P p) (renPt (affCoord p z)))ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ Jf → mm i = 0) ∧ algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (bind₁ (SncRes.lift p) f) = u * ∏ i ∈ Jf, algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r i) ^ mm i := by
  intro K _ ι _ P D e p z r Jf f a hP _ _ _ hI hreg hdim hspan hpr _ hf
  exact exists_unit_mul_monomial_of_primes (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) _ hI hdim r Jf
    hspan hpr _ fun 𝔮 h𝔮 hle _ hg => ideal_sup_le_of_mem P D p hP f hf 𝔮 h𝔮 hle hg

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degreeGeneric_of_degree :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement → GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement := by
  intro hDeg K _ _ ι _ P e L hP hL
  classical
  rw [hDeg K ι P e L 2 hP hL Nat.prime_two,
    GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e (fun j => (L j).a) 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end
