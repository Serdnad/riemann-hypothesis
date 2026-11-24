module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesPropertiesStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAt

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CWDeriv

open Filter Topology PI.UpqRep
open scoped ContDiff

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothOnH_continuousOn {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) : ContinuousOn f (Formalism.QuantumDeterminants.UH H) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have h1 : ContinuousWithinAt F (Formalism.QuantumDeterminants.UH H) g :=
    (hF.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (hfF g hgU hg)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with x hx hx'
  exact hfF x hx hx'

theorem left_hasDerivAt {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hg : g ∈ U) (hgH : inUH H g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, inUH H x → f x = F x) (hX : AAInvW.inLH H X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 := by
  apply _root_.Gp91.GlobalTheory.CWDeriv.left_hasDerivAt <;> assumption

theorem left_smooth {H : Matrix (Fin n) (Fin n) ℂ} (hH : AAInvW.HInvol H)
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : AAInvW.inLH H X)
    (hf' : ∀ g, inUH H g → ∀ D, HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) D 0 → D = f' g) :
    SmoothOnH H f' ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (f' g) 0 := by
  apply _root_.Gp91.GlobalTheory.CWDeriv.left_smooth <;> assumption

end Smooth

section Rep

variable {k r : ℕ}

def DerFacts (R : Rep k r) : Prop :=
  ∀ X, InLieHpk k r X →
    (∀ v ∈ R.sm, dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧
      HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) R.σ X v) 0) ∧
    ∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, dsig (k := k) (r := r) R.σ X w⟫_ℂ

theorem hInvol (k r : ℕ) : AAInvW.HInvol (Hpk k r) :=
  ⟨Formalism.QuantumDeterminants.GBasic.Hpk_herm k r, Formalism.QuantumDeterminants.GBasic.Hpk_sq k r⟩

theorem dsigW_mem {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    ∀ u ∈ R.sm, dsigW (k := k) (r := r) R.σ W u ∈ R.sm := by
  induction W with
  | nil => intro u hu; exact hu
  | cons X W ih =>
    intro u hu
    exact ((hD X (hW X (by simp))).1 _ (ih (fun Y hY => hW Y (by simp [hY])) u hu)).1

theorem dsigW_append {R : Rep k r} (W : List (Mx k r)) (Y : Mx k r) (u : R.H) :
    dsigW (k := k) (r := r) R.σ (W ++ [Y]) u =
      dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y u) := by
  induction W with
  | nil => rfl
  | cons X W ih => simp only [List.cons_append, dsigW, ih]

theorem dsigW_adjoint {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    ∀ w ∈ R.sm, ∃ w' : R.H, ∀ u ∈ R.sm, ⟪w, dsigW (k := k) (r := r) R.σ W u⟫_ℂ = ⟪w', u⟫_ℂ := by
  induction W with
  | nil => intro w _; exact ⟨w, fun u _ => rfl⟩
  | cons X W ih =>
    intro w hw
    have hX := hD X (hW X (by simp))
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (by simp [hY])
    obtain ⟨w', hw'⟩ := ih hW' _ (hX.1 w hw).1
    refine ⟨-w', fun u hu => ?_⟩
    have h := hX.2 w hw _ (dsigW_mem hD W hW' u hu)
    rw [hw' u hu] at h
    rw [inner_neg_left, h, neg_neg]
    rfl

theorem eq_zero_of_closure {R : Rep k r} {x : R.H} (hx : x ∈ closure R.sm) (h : ∀ w ∈ R.sm, ⟪w, x⟫_ℂ = 0) :
    x = 0 := by
  have hc : IsClosed {w : R.H | ⟪w, x⟫_ℂ = 0} := isClosed_eq (by fun_prop) continuous_const
  exact inner_self_eq_zero.mp (closure_minimal (t := {w : R.H | ⟪w, x⟫_ℂ = 0}) h hc hx)

theorem sm_comb {R : Rep k r} (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    a • (x - y) - z ∈ R.sm :=
  R.smSub.sub_mem (R.smSub.smul_mem a (R.smSub.sub_mem hx hy)) hz

theorem dsigW_comb {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • (x - y) - z) =
      a • (dsigW (k := k) (r := r) R.σ W x - dsigW (k := k) (r := r) R.σ W y) - dsigW (k := k) (r := r) R.σ W z := by
  rw [← sub_eq_zero]
  have hm := dsigW_mem hD W hW
  refine eq_zero_of_closure (subset_closure
    (R.smSub.sub_mem (hm _ (sm_comb a hx hy hz)) (sm_comb a (hm _ hx) (hm _ hy) (hm _ hz)))) ?_
  intro w hw
  obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
  simp only [inner_sub_right, inner_smul_right, hw' _ (sm_comb a hx hy hz), hw' _ hx, hw' _ hy, hw' _ hz,
    sub_self]

theorem dsigW_deriv_eq {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    {c : ℝ → R.H} {c' D : R.H} (hc : ∀ t, c t ∈ R.sm) (hc' : c' ∈ R.sm) (hd : HasDerivAt c c' 0)
    (hD' : HasDerivAt (fun t => dsigW (k := k) (r := r) R.σ W (c t)) D 0) :
    D = dsigW (k := k) (r := r) R.σ W c' := by
  rw [← sub_eq_zero]
  have hm := dsigW_mem hD W hW
  refine eq_zero_of_closure ?_ ?_
  · have h1 := (hasDerivAt_iff_tendsto_slope.mp hD').sub_const (dsigW (k := k) (r := r) R.σ W c')
    refine mem_closure_of_tendsto h1 (Eventually.of_forall fun t => ?_)
    have := sm_comb (((t - 0)⁻¹ : ℝ) : ℂ) (hm _ (hc t)) (hm _ (hc 0)) (hm _ hc')
    rw [Complex.coe_smul] at this
    exact this
  · intro w hw
    obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
    have h1 : HasDerivAt (fun t => ⟪w, dsigW (k := k) (r := r) R.σ W (c t)⟫_ℂ) ⟪w, D⟫_ℂ 0 :=
      ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD'
    have h2 : HasDerivAt (fun t => ⟪w', c t⟫_ℂ) ⟪w', c'⟫_ℂ 0 :=
      ((innerSL ℂ w').restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simp only [hw' _ (hc _)] at h1
    rw [inner_sub_right, h1.unique h2, hw' _ hc', sub_self]

theorem dsigW_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDS ε mu) (hD : DerFacts R) {v : R.H} (hv : v ∈ R.sm) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X)
    (hs : SmoothOnH (Hpk k r) (fun g => dsigW (k := k) (r := r) R.σ W (R.σ g v)))
    (Y : Mx k r) (hY : InLieHpk k r Y) :
    SmoothOnH (Hpk k r)
        (fun g => dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y (R.σ g v))) ∧
      ∀ g, inUH (Hpk k r) g → HasDerivAt
        (fun t : ℝ => dsigW (k := k) (r := r) R.σ W (R.σ (NormedSpace.exp ((t : ℂ) • Y) * g) v))
        (dsigW (k := k) (r := r) R.σ W (dsig (k := k) (r := r) R.σ Y (R.σ g v))) 0 := by
  exact _root_.Gp91.GlobalTheory.CWDeriv.dsigW_orbit_of_isDS hR hD hv W hW hs Y hY

theorem dsigW_orbit_smooth {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDS ε mu) (hD : DerFacts R) {v : R.H} (hv : v ∈ R.sm) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) :
    SmoothOnH (Hpk k r) (fun g => dsigW (k := k) (r := r) R.σ W (R.σ g v)) := by
  exact _root_.Gp91.GlobalTheory.CWDeriv.dsigW_orbit_smooth_of_isDS hR hD hv W hW

theorem cw_tendsto {R : Rep k r} {V : Type} [NormedAddCommGroup V] {Bm : R.H → V}
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {α : Type} {l : Filter α} {u : α → R.H}
    (hu : ∀ᶠ a in l, u a ∈ R.sm)
    (h : ∀ W : List (Mx k r), (∀ X ∈ W, InLieHpk k r X) →
      Tendsto (fun a => dsigW (k := k) (r := r) R.σ W (u a)) l (𝓝 0)) :
    Tendsto (fun a => Bm (u a)) l (𝓝 0) := by
  apply _root_.Gp91.GlobalTheory.CWDeriv.cw_tendsto <;> assumption

theorem lin_comb {R : Rep k r} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Bm : R.H → V}
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (a : ℂ) {x y z : R.H} (hx : x ∈ R.sm) (hy : y ∈ R.sm) (hz : z ∈ R.sm) :
    Bm (a • (x - y) - z) = a • (Bm x - Bm y) - Bm z := by
  have hsub : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v - w) = Bm v - Bm w := by
    intro v hv w hw
    have := ha _ (R.smSub.sub_mem hv hw) w hw
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  rw [hsub _ (R.smSub.smul_mem a (R.smSub.sub_mem hx hy)) _ hz, hs a _ (R.smSub.sub_mem hx hy), hsub _ hx _ hy]

end Rep

end GlobalTheory.CWDeriv

namespace GlobalTheory

open Filter Topology CWDeriv

theorem cwCont_continuousOn_hasDerivAt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ v ∈ R.sm, ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → HasDerivAt (fun t : ℝ => Bm (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) (Bm (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) 0 := by
  exact _root_.Gp91.GlobalTheory.cwCont_continuousOn_hasDerivAt_of_isDS

end GlobalTheory

end
