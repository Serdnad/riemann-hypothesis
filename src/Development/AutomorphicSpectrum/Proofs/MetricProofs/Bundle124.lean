module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle117
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle114
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle113
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle115
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle088
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_sub_eq_of_sameOrbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (ho : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hP : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A.smul c z' hc, B.smul c z' hc, ← hab, Real.log_mul hP (A.pos z' hz').ne',
    Real.log_mul hP (B.pos z' hz').ne']
  ring

theorem exactLine_not_mem_mcPts_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have h1 := hz.2 1 Submodule.mem_top
  simp at h1

theorem exactLine_basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

end SlopeTestRemainingChoices

theorem log_fsHerm_add_ph_eq_potAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x₀ : FA.Re.R.X) (z₀ : (Σ k, ι k) → ℂ) (b : BM.Rb.X) (p : Ψ × Fin N) (hm : Matrix (Fin N) (Fin N) ℂ), b ∈ BM.O l \ bdry BM.s → SameOrbit (FA.Re.R.lift x₀ x₀) z₀ → SameOrbit (basePart M.blk z₀) (BM.Rb.lift b b) → ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) p z₀ hm → IsBlockDiag j hm → hm.det ≠ 0 → Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (FA.Re.π x₀) = potAt BM l p b hm := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x₀ z₀ b p hm hb hx hbase hex hbd hdet
  have hsymm : ∀ {K' : Type} {ι' : K' → Type} {u v : (Σ k, ι' k) → ℂ}, SameOrbit u v → SameOrbit v u := by
    intro K' ι' u v h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k),
      funext fun q => (inv_mul_cancel_left₀ (hc q.1) (v q)).symm⟩
  have htrans : ∀ {K' : Type} {ι' : K' → Type} {u v w : (Σ k, ι' k) → ℂ},
      SameOrbit u v → SameOrbit v w → SameOrbit u w := by
    intro K' ι' u v w h h'
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨e, he, rfl⟩ := h'
    exact ⟨fun k => c k * e k, fun k => mul_ne_zero (hc k) (he k),
      funext fun q => (mul_assoc _ _ _).symm⟩
  have hmemx : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  have hmem : z₀ ∈ mcPts (mCoordIdeal y) :=
    ReciprocityTheory.ChartRestriction.G.Geo.mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) (hsymm hx) hmemx
  have hpr : FA.pr (FA.Re.π x₀) = b := by
    apply BM.Rb.inj
    · exact exactLine_not_mem_mcPts_top _
    · exact htrans (hsymm (FA.pr_eq x₀)) (htrans (exactLine_basePart_orbit M.blk hx) hbase)
  have hopen : FA.Re.π x₀ ∈ FA.S.open' := by
    show FA.Re.π x₀ ∈ (bdry FA.S.s)ᶜ
    rw [Set.mem_compl_iff]
    intro h
    apply hb.2
    have h' : FA.S.s (FA.Re.π x₀) (FA.Re.π x₀) = 0 := h
    simp only [FA.s_eq, hpr] at h'
    show BM.s b b = 0
    exact h'
  have hhom := FA.hom_eq p x₀ hopen
  rw [FA.ref_some p] at hhom
  have hz0 : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0 := hmem.1
  have hsub := log_h_sub_eq_of_sameOrbit (BM.hom p) (fsHerm ι (M.dy p)) (BM.hom_deg p) hz0 hx
  have hind := BM.induced l b hb p z₀ hmem hbase hex.1 hm hbd hdet
  have hval : valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b) = valAt M.x ((BM.F l).υ p) (basePart M.blk z₀) :=
    valAt_eq_of_sameOrbit _ _ _ M.x _ _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) (hsymm hbase)
  unfold potAt upsLogAt upsVal
  by_cases hblk : M.blk p = none
  · have h1 := hind.2 hblk
    rw [if_pos hblk, hval]
    linarith
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hblk
    have h1 := hind.1 k hk (hex.2 k hk)
    rw [if_neg hblk, sub_zero]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.twisted_chart_coordinates_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsSNC RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) ![1] ![diagSet k₀ RW] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.secPot_isPotential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.twisted_chart_transition_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem _root_.GlobalTheory.T.twisted_metric_log_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
open GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Read

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)


include M in
theorem off_step {p : Ψ × Fin N} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) (I : Finset (Fin N))
    (hI : ¬ IsStepRows N j p.2 I) : minorIJ A I (stepCols N j p.2) = 0 :=
  ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 A I hA hI).resolve_right
    (Finset.nonempty_iff_ne_empty.1 (stepCols_nonempty M.j_le p.2))

theorem pluck_eq {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) {z : (Σ k, ι k) → ℂ} {α : ℂ}
    (hz : ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2))
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j p.2 I₀) :
    pluck M F zb k z I₀ = α * minorIJ A I₀ (stepCols N j p.2) := by
  let val := regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I₀ = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I₀ ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I₀ = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I₀ I' hI₀ hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg val e

    rw [map_sum] at e'
    simp only [map_mul] at e'
    rw [e']
    split_ifs <;> simp
  have key : ∀ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) =
      if I = I₀ then minorIJ A I₀ (stepCols N j p.2) else 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · rw [rel I hI]
      by_cases e : I = I₀
      · subst e; simp
      · simp [e, Ne.symm e]
    · have e : I ≠ I₀ := fun e => hI (e ▸ hI₀)
      rw [off_step M hA I hI, if_neg e, mul_zero]
  have read : ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2) =
      minorIJ A I₀ (stepCols N j p.2) := by
    calc _ = ∑ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => ?_
          rw [mul_assoc]
          rfl
      _ = _ := by simp only [key]; simp
  rw [← read, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hz m, mul_left_comm]
  rfl

end Read

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (p : Ψ × Fin N) (k : K) (A g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (α : ℂ) (J : Finset (Fin N)), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → M.blk p = some k → IsBlockDiag j A → (∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2)) → twMinor M F zb p.2 k g z J = α * minorIJ (g * A) J (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F zb p k A g z α J hF hzb hG hp hA hz
  unfold twMinor
  rw [(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).1 g A J (stepCols N j p.2), Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · rw [pluck_eq M hF hzb hG hp hA hz I hI]
    ring
  · rw [off_step M hA I hI]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.flag_adjacent_chart_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) (wD ε V)) ∧ ∀ w ∈ wD ε V, (∀ τ', IsBlockDiag j (wH h ε τ' w) ∧ (wH h ε τ' w).det ≠ 0) ∧ baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (wH h ε τ' w) ∧ ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (if τ' = τ then wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) else wH h ε τ' w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan


theorem _root_.GlobalTheory.T.lower_unipotent_minor_formula : ∀ (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N), j ≤ N → IsBlockDiag j X → IsLowerUni X → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧ minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem _root_.GlobalTheory.T.orbit_chart_transition_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (C₁ C₂ : OrbitChart P e), AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w)) {w | w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LU

variable {N j : ℕ}

theorem mem_stepCols_stepOf (hj : j ≤ N) (a b : Fin N) :
    a ∈ stepCols N j (stepOf N j b) ↔ a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  have ha := a.2
  have hb := b.2
  rw [Fin.le_def, stepCols, Finset.mem_filter]
  have hv : ((stepOf N j b : Fin N) : ℕ) = if N - j ≤ (b : ℕ) then (b : ℕ) - (N - j) else (b : ℕ) + j := rfl
  generalize ((stepOf N j b : Fin N) : ℕ) = i at hv ⊢
  simp only [Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem det_subtype_eq_minorIJ (G : Matrix (Fin N) (Fin N) ℂ) (C : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, a ∈ C ↔ P a) :
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ G C C := by
  let e : Fin C.card ≃ {a // P a} := (C.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight hP)
  rw [minorIJ, dite_eq_left rfl, ← Matrix.det_submatrix_equiv_self e
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val)]
  rfl

theorem minor_stepOf_ne_zero (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : IsBlockDiag j G) (hd : G.det ≠ 0)
    (hs : ∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) (b : Fin N) :
    minorIJ G (stepCols N j (stepOf N j b)) (stepCols N j (stepOf N j b)) ≠ 0 := by
  by_cases hp : IsProperStep N j (stepOf N j b)
  · exact hs _ hp
  have hb := b.2
  have hlast : (b : ℕ) + 1 = N ∨ (b : ℕ) + 1 = N - j := by
    simp only [IsProperStep, stepOf, not_and_or, not_not] at hp
    split_ifs at hp <;> omega
  have hD := GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hG hd
  rw [detFac, if_pos (by simp only; omega), if_pos (by simp only; omega)] at hD
  by_cases h : N - j ≤ (b : ℕ)
  · have e : stepCols N j (stepOf N j b) = wIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact left_ne_zero_of_mul hD
  · have e : stepCols N j (stepOf N j b) = omIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact right_ne_zero_of_mul hD

theorem exists_lower_upper : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) →
    ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧
      (∀ c, U c c ≠ 0) ∧ G = L * U := by
  intro N j G hj hG hd hs
  have hu : ∀ b : Fin N, IsUnit (G.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := fun b => by
    rw [det_subtype_eq_minorIJ G (stepCols N j (stepOf N j b)) _ fun a => mem_stepCols_stepOf hj a b]
    exact (minor_stepOf_ne_zero hj hG hd hs b).isUnit
  obtain ⟨B, hB, hBt, hL⟩ := hG.exists_upper hu
  have hdB : B.det ≠ 0 := fun h => by
    have := hL.det
    rw [Matrix.det_mul, h, mul_zero] at this
    exact zero_ne_one this
  have huB : IsUnit B.det := hdB.isUnit
  letI := Matrix.invertibleOfIsUnitDet B huB
  refine ⟨G * B, B⁻¹, hG.mul hB, hL, hB.inv huB, blockTriangular_inv_of_blockTriangular hBt, fun c => ?_, ?_⟩
  · have h1 : (B⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det B huB).ne_zero
    rw [Matrix.det_of_upperTriangular (blockTriangular_inv_of_blockTriangular hBt)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) c (Finset.mem_univ c)
  · rw [Matrix.mul_nonsing_inv_cancel_right _ _ huB]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LU
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep

theorem stepCols_subset_of_le {N j : ℕ} (hj : j ≤ N) {m i b x : Fin N} (hmi : m ≤ i)
    (hb : b ∈ stepCols N j m) (hb' : b ∈ stepCols N j i) (hx : x ∈ stepCols N j m) : x ∈ stepCols N j i := by
  have h1 := m.2
  have h2 := i.2
  have h3 := b.2
  have h4 := x.2
  have h5 : (m : ℕ) ≤ i := hmi
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb' hx ⊢
  split_ifs at hb hb' hx ⊢ <;> omega

theorem pStep_reads (Ψ : Type) (N j : ℕ) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) (hj : j ≤ N) :
    keep (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) ∧ IsProperStep N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.2 ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.1 ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      ∀ c : PIdx j keep → ℂ, pMat keep c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q ∧
        ∀ x ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2), x ≠ q.1.1.2.2 →
          pMat keep c q.1.1.1 x q.1.1.2.2 = 0 := by
  obtain ⟨⟨⟨τ, a, b⟩, hlt, hblk⟩, hsep⟩ := q
  obtain ⟨i, hk, hp, hb, ha⟩ := id hsep
  dsimp only at hk hp hb ha hlt hblk ⊢
  have hne : (pSteps j keep τ b).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩⟩
  have hm : pStep j keep τ b ∈ pSteps j keep τ b := by
    unfold pStep
    rw [dite_eq_left hne]
    exact Finset.min'_mem _ _
  have hmin : ∀ i' ∈ pSteps j keep τ b, pStep j keep τ b ≤ i' := by
    intro i' hi'
    unfold pStep
    rw [dite_eq_left hne]
    exact Finset.min'_le _ _ hi'
  obtain ⟨hmk, hmp, hmb⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨hmk, hmp, hmb, fun hx => ha (stepCols_subset_of_le hj (hmin i ?_) hmb hb hx), fun c => ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩
  · unfold pMat lowMat
    rw [dite_eq_left (⟨hlt, hblk⟩ : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))]
    unfold cExt
    rw [dite_eq_left hsep]
  · intro x hx hxb
    unfold pMat lowMat
    by_cases hc : b < x ∧ ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [dite_eq_left hc]
      unfold cExt
      refine dif_neg ?_
      rintro ⟨i', hk', hp', hb', hx'⟩
      exact hx' (stepCols_subset_of_le hj
        (hmin i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk', hp', hb'⟩)) hmb hb' hx)
    · rw [_root_.dite_eq_right hc, if_neg hxb]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact

theorem chart_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, (∀ τ, IsBlockDiag j (pH keep h ε τ w) ∧ (pH keep h ε τ w).det ≠ 0) ∧ pBase M v (pPhi M F keep v bl h ε w) = bl (pB ε w) ∧ ∀ p k, keep p → M.blk p = some k → ∀ m : ι k, upV v (pPhi M F keep v bl h ε w) ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (bl (pB ε w)) * minorIJ (pH keep h ε p.1 w) I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc w hw
  obtain ⟨hbm, hran, -, -, -, -, hh⟩ := hc
  have key : ∀ q : Σ k, ι k, q.1 ∈ Set.range κ → upV v (pPhi M F keep v bl h ε w) q =
      flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w) q := by
    intro q hq
    obtain ⟨q', rfl⟩ := hbm.2.2.2 q hq
    rw [upV_apply hbm.2.1]
    rfl
  refine ⟨fun τ => ⟨?_, ?_⟩, ?_, fun p k hk hp m => ?_⟩
  · exact isBlockDiag_mul (hh τ).1 (WMan.Exact.lowMat_isBlockDiag _ _)
  · rw [pH, Matrix.det_mul, pMat, WMan.Exact.lowMat_det, mul_one]
    exact (hh τ).2
  · funext q
    obtain ⟨k, m⟩ := q
    show upV v (pPhi M F keep v bl h ε w) ⟨k.1, m⟩ = _
    rw [key ⟨k.1, m⟩ ((hran k.1).2 (Or.inl k.2))]
    exact WMan.Exact.flagZ_base k m
  · rw [key ⟨k, m⟩ ((hran k).2 (Or.inr ⟨p, hk, hp⟩))]
    exact WMan.Exact.flagZ_step hp m

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact
end
end
