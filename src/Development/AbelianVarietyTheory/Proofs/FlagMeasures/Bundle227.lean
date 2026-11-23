module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle064
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.HarderNarasimhan.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle198
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle215
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle216
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CWIntegral

open PI.UpqRep GlobalTheory.CWDeriv

theorem exists_functional {S E : Type} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : S →ₗ[ℂ] E) (φ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ s, ‖φ s‖ ≤ C * ‖T s‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ s, Λ (T s) = φ s := by
  have hker : LinearMap.ker T ≤ LinearMap.ker φ := by
    intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    have h1 := h s
    rw [hs, norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  let ψ : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ φ hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hψT : ∀ s, ψ ⟨T s, LinearMap.mem_range_self T s⟩ = φ s := by
    intro s
    have hq : T.quotKerEquivRange.symm ⟨T s, LinearMap.mem_range_self T s⟩ = (LinearMap.ker T).mkQ s :=
      LinearMap.quotKerEquivRange_symm_apply_image T s _
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hbd : ∀ y : LinearMap.range T, ‖ψ y‖ ≤ max C 0 * ‖y‖ := by
    rintro ⟨y, s, rfl⟩
    rw [hψT]
    calc ‖φ s‖ ≤ C * ‖T s‖ := h s
      _ ≤ max C 0 * ‖T s‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range T) (ψ.mkContinuous (max C 0) hbd)
  refine ⟨Λ, fun s => ?_⟩
  have := hΛ ⟨T s, LinearMap.mem_range_self T s⟩
  rw [LinearMap.mkContinuous_apply, hψT] at this
  exact this

variable {k r : ℕ}

def linOn (R : Rep k r) {V : Type} [AddCommGroup V] [Module ℂ V] (B : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, B (v + w) = B v + B w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, B (a • v) = a • B v) :
    R.smSub →ₗ[ℂ] V where
  toFun v := B v
  map_add' v w := ha _ v.2 _ w.2
  map_smul' a v := hs a _ v.2

theorem dsigW_smul {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (a : ℂ) (v : R.H) (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v) = a • dsigW (k := k) (r := r) R.σ W v := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (a • v)) =
      a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hd := ((hD X hX).1 _ hv').2.const_smul a
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) (a • dsigW (k := k) (r := r) R.σ W v))
        (a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)) 0 := by
      simpa only [map_smul, Pi.smul_def] using hd
    exact hd'.deriv

theorem dsigW_add {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (v : R.H) (hv : v ∈ R.sm) (w : R.H) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (v + w) =
      dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (v + w)) =
      dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
        dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hw' := dsigW_mem hD W hW' w hw
    have hd := ((hD X hX).1 _ hv').2.add ((hD X hX).1 _ hw').2
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X))
        (dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w))
        (dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
          dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)) 0 := by
      simpa only [map_add (f := _), Pi.add_def] using hd
    exact hd'.deriv

theorem dsigW_integral {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → R.H) (hf : ∀ x, f x ∈ R.sm)
    (hi : Integrable f μ) (hi' : Integrable (fun x => dsigW (k := k) (r := r) R.σ W (f x)) μ)
    (hu : (∫ x, f x ∂μ) ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) = ∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ := by
  have hmem : ∀ x, dsigW (k := k) (r := r) R.σ W (f x) ∈ R.smSub := fun x => dsigW_mem hD W hW _ (hf x)
  have hcl : ((R.smSub.topologicalClosure : Submodule ℂ R.H) : Set R.H) = closure R.sm :=
    Submodule.topologicalClosure_coe _
  have hy : (∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ) ∈ R.smSub.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro z hz
    rw [← integral_inner hi']
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Submodule.inner_left_of_mem_orthogonal (hmem x) hz
  have hd : dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) ∈ R.smSub := dsigW_mem hD W hW _ hu
  refine sub_eq_zero.mp (eq_zero_of_closure ?_ ?_)
  · rw [← hcl]
    exact Submodule.sub_mem _ (R.smSub.le_topologicalClosure hd) hy
  · intro w hw
    obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
    rw [inner_sub_right, hw' _ hu, ← integral_inner hi, ← integral_inner hi', sub_eq_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (hw' _ (hf x)).symm

end GlobalTheory.CWIntegral

namespace GlobalTheory

open PI.UpqRep GlobalTheory.CWDeriv GlobalTheory.CWIntegral

theorem cwCont_integral_comm : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  intro hKS k r ε mu R hR V indexVFirst indexVSecond indexVThird indexVFourth Bm hadd hsmul hcw X iX1 iX2 iX3 iX4 iX5 μ iμ κ p hκ hκG hp v hv hu
  have hD : DerFacts R := fun Y hY =>
    ⟨(GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).1, (GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).2.2.2.2⟩
  have hσ : ∀ x, R.σ (κ x) v ∈ R.sm := fun x => (rep_basic_of_isDS hKS k r ε mu R hR).2.2.2.1 _ (hκG x) v hv
  have hf : ∀ x, p x • R.σ (κ x) v ∈ R.sm := fun x => R.smSub.smul_mem (p x) (hσ x)
  have hint : ∀ {E : Type} [NormedAddCommGroup E] (g : X → E), Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (Set.subset_univ _))
  have hcW : ∀ W : List (Mx k r), (∀ Y ∈ W, InLieHpk k r Y) →
      Continuous (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ W (R.σ (κ x) v)) := fun W hW =>
    (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW)).comp_continuous hκ hκG
  have hBc : Continuous (fun x => Bm (R.σ (κ x) v)) :=
    (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1.comp_continuous hκ hκG
  obtain ⟨C, Ws, hWs, hB⟩ := hcw
  have hWi : ∀ i : Fin Ws.length, ∀ Y ∈ Ws.get i, InLieHpk k r Y := fun i => hWs _ (List.get_mem Ws i)
  let T : R.smSub →ₗ[ℂ] (Fin Ws.length → R.H) :=
    linOn R (fun u i => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) u)
      (fun a ha b hb => funext fun i => dsigW_add hD _ (hWi i) a ha b hb)
      (fun c a ha => funext fun i => dsigW_smul hD _ (hWi i) c a ha)
  refine ext_inner_left ℂ (fun e => ?_)
  let φ : R.smSub →ₗ[ℂ] ℂ := (innerSL ℂ e : V →L[ℂ] ℂ).toLinearMap.comp (linOn R Bm hadd hsmul)
  have hφ : ∀ s, φ s = ⟪e, Bm s⟫_ℂ := fun s => rfl
  have hbound : ∀ s, ‖φ s‖ ≤ (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by
    intro s
    have h1 : ‖Bm s‖ ≤ C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum := hB s s.2
    have h2 : (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum ≤ Ws.length * ‖T s‖ := by
      have h3 := List.sum_le_card_nsmul (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖) ‖T s‖
        (by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
          obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
          exact norm_le_pi_norm (T s) i)
      rwa [List.length_map, nsmul_eq_mul] at h3
    have h0 : 0 ≤ (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum :=
      List.sum_nonneg (fun y hy => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hy
        exact norm_nonneg _)
    have h4 : ‖Bm s‖ ≤ |C| * (Ws.length * ‖T s‖) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) h0).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    rw [hφ]
    calc ‖⟪e, Bm s⟫_ℂ‖ ≤ ‖e‖ * ‖Bm s‖ := norm_inner_le_norm _ _
      _ ≤ ‖e‖ * (|C| * (Ws.length * ‖T s‖)) := mul_le_mul_of_nonneg_left h4 (norm_nonneg e)
      _ = (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by ring
  obtain ⟨Λ, hΛ⟩ := exists_functional T φ _ hbound
  let F : X → (Fin Ws.length → R.H) := fun x i =>
    p x • PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (R.σ (κ x) v)
  have hFi : Integrable F μ := hint F (continuous_pi fun i => hp.smul (hcW _ (hWi i)))
  have hTu : T ⟨_, hu⟩ = ∫ x, F x ∂μ := by
    funext i
    have hpi := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin Ws.length => R.H) i).integral_comp_comm hFi
    simp only [ContinuousLinearMap.proj_apply] at hpi
    rw [← hpi]
    show PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, F x i ∂μ
    have hi0 : Integrable (fun x => p x • R.σ (κ x) v) μ := hint _ (hp.smul (hcW [] (by simp)))
    have hi1 : Integrable (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (p x • R.σ (κ x) v)) μ :=
      (hint _ (hp.smul (hcW _ (hWi i)))).congr
        (Filter.Eventually.of_forall fun x => (dsigW_smul hD _ (hWi i) (p x) _ (hσ x)).symm)
    rw [dsigW_integral hD _ (hWi i) μ _ hf hi0 hi1 hu]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => dsigW_smul hD _ (hWi i) (p x) _ (hσ x))
  calc ⟪e, Bm (∫ x, p x • R.σ (κ x) v ∂μ)⟫_ℂ = φ ⟨_, hu⟩ := (hφ ⟨_, hu⟩).symm
    _ = Λ (T ⟨_, hu⟩) := (hΛ ⟨_, hu⟩).symm
    _ = Λ (∫ x, F x ∂μ) := by rw [hTu]
    _ = ∫ x, Λ (F x) ∂μ := (Λ.integral_comp_comm hFi).symm
    _ = ∫ x, ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hF : F x = p x • T ⟨_, hσ x⟩ := rfl
        show Λ (F x) = ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ
        rw [hF, map_smul, hΛ, hφ, inner_smul_right, smul_eq_mul]
    _ = ⟪e, ∫ x, p x • Bm (R.σ (κ x) v) ∂μ⟫_ℂ := integral_inner (hint _ (hp.smul hBc)) e

end GlobalTheory

end
end

section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.SubquotCover

theorem sum_normSq_eq_trace {a b : Type} [Fintype a] [Fintype b] (M : Matrix a b ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Mᴴ * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem sum_normSq_mul {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq b] [DecidableEq c]
    (P : Matrix a b ℂ) (M : Matrix b c ℂ) (Q : Matrix c d ℂ) (hP : Pᴴ * P = 1)
    (hQ : Q * Qᴴ = 1) :
    ∑ i, ∑ j, ‖(P * M * Q) i j‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace, conjTranspose_mul, conjTranspose_mul]
  have hmid : Qᴴ * (Mᴴ * Pᴴ) * (P * M * Q) = Qᴴ * (Mᴴ * M * Q) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, hP, Matrix.one_mul]
  rw [hmid, Matrix.trace_mul_comm, Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem vecAt_mulVec {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (w : InfinitePlace K) (M : Matrix (Fin a) (Fin b) K) (y : Fin b → K) :
    vecAt (Pi.basisFun K (Fin a)) w (M *ᵥ y)
      = M.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin b)) w y := by
  funext i

  simp only [vecAt, Pi.basisFun_repr, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
  map_mul]

theorem mulVec_fcoord {K : Type} [Field K] [NumberField K] [StarRing K] {a : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (w : InfinitePlace K) (hX : IsUnit (X w).det) (y : Fin a → K) :
    X w *ᵥ fcoord (Pi.basisFun K (Fin a)) X w y = vecAt (Pi.basisFun K (Fin a)) w y := by
  rw [fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]

theorem subquot_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S R : Submodule (𝓞 K) (Fin n → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (Pi.basisFun K (Fin n)) X N S) → largestSize (Pi.basisFun K (Fin n)) X R ≤ hi → ∀ T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ S, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = 0) → (∀ w, ∀ y ∈ A, T w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))) → ∃ φ : Matrix (Fin n) (Fin n) K, (∀ y ∈ S, φ *ᵥ y = 0) ∧ (∀ y ∈ A, φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ w, ∀ y ∈ A, D w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y = (T w - (X w)⁻¹ * φ.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ Real.sqrt (∑ w, Formalism.REAL.hs (D w)) ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt (nPl K) * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (nPl K : ℝ))) * hi / (2 * lo) := by
  intro K _ _ _ _ n X A S R lo hi hX hA hSat hR hlo hhi hsize hlarge T hTS hTR
  obtain ⟨m, q, X', Q, hm, hX', hQ, hqf, -, hQS, hqS, hspan, hN⟩ :=
    GlobalTheory.T.quotient_lattice_realized_isometrically K n X A S hX hA hSat
  obtain ⟨r, e, X'', P, B, hr, hX'', hP, hPe, hB, hBspan, heB, hRB, hlB⟩ :=
    GlobalTheory.T.exists_isometric_realisation_of_sublattice' K n X R hX hR
  obtain ⟨φ', hφ'B, hbound⟩ := GlobalTheory.T.lattice_pair_volume_bounds K m r X' X''
    (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) B lo hi hX' hX'' (hA.map _) hB hspan
    hBspan hlo hhi
    (fun N' hN' hN'0 => by
      obtain ⟨N, hSN, hNA, heq⟩ := hN N' hN' hN'0
      rw [← heq]
      exact hsize N hSN hNA)
    (by rw [hlB]; exact hlarge) (fun w => (P w)ᴴ * T w * (Q w)ᴴ)
  refine ⟨e * φ' * q, ?_, ?_,
    fun w => P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w,
    ?_, ?_⟩
  · intro y hy
    rw [← Matrix.mulVec_mulVec, hqS y hy, Matrix.mulVec_zero]
  · intro y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    apply heB
    apply hφ'B
    exact Submodule.mem_map.mpr ⟨y, hy, by simp [Matrix.toLin'_apply]⟩
  · intro w y hy
    set u := fcoord (Pi.basisFun K (Fin n)) X w y with hu
    have hQu : Q w *ᵥ u = fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) := (hqf w y hy).symm
    have hXu : X w *ᵥ u = vecAt (Pi.basisFun K (Fin n)) w y := mulVec_fcoord X w (hX w) y
    have hX'u : X' w *ᵥ (Q w *ᵥ u) = q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y := by
      rw [hQu, mulVec_fcoord X' w (hX' w), vecAt_mulVec]

    have hTQ : T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u)) = T w *ᵥ u := by
      have hmem : u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈
          Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) :=
        hQS w u (Submodule.subset_span ⟨y, hy, rfl⟩)
      have hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))
          ≤ LinearMap.ker (Matrix.mulVecLin (T w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        exact hTS w z hz
      have h0 := hker hmem
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, sub_eq_zero] at h0
      exact h0.symm

    have hPP : ∀ v ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K))),
        P w *ᵥ ((P w)ᴴ *ᵥ v) = v := by
      intro v hv
      have hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (R : Set (Fin n → K)))
          ≤ LinearMap.range (Matrix.mulVecLin (P w)) := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨z, -, rfl⟩ := hRB x hx
        refine ⟨(X'' w)⁻¹ *ᵥ vecAt (Pi.basisFun K (Fin r)) w z, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hPe w, ← Matrix.mulVec_mulVec,
          ← vecAt_mulVec]
        rfl
      obtain ⟨z, rfl⟩ := hle hv
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec _ (P w)ᴴ, hP w, Matrix.one_mulVec]
    calc (P w * ((P w)ᴴ * T w * (Q w)ᴴ - (X'' w)⁻¹ * φ'.map w.embedding * X' w) * Q w) *ᵥ u
        = P w *ᵥ ((P w)ᴴ *ᵥ (T w *ᵥ ((Q w)ᴴ *ᵥ (Q w *ᵥ u))))
          - (P w * (X'' w)⁻¹) *ᵥ (φ'.map w.embedding *ᵥ (X' w *ᵥ (Q w *ᵥ u))) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc]
      _ = T w *ᵥ u - ((X w)⁻¹ * e.map w.embedding) *ᵥ (φ'.map w.embedding *ᵥ
            (q.map w.embedding *ᵥ vecAt (Pi.basisFun K (Fin n)) w y)) := by
          rw [hTQ, hPP _ (hTR w y hy), hX'u, hPe w]
      _ = (T w - (X w)⁻¹ * (e * φ' * q).map w.embedding * X w) *ᵥ u := by
          rw [Matrix.sub_mulVec, ← hXu, Matrix.map_mul, Matrix.map_mul]
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have hm' : (m : ℝ) = (rkK A : ℝ) - rkK S := by rw [← hm]; push_cast; ring
    have hr' : (r : ℝ) = rkK R := by rw [hr]
    rw [← hm', ← hr']
    refine Eq.trans_le ?_ hbound
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Formalism.REAL.hs]
    exact sum_normSq_mul (P w) _ (Q w) (hP w) (hQ w)

end GlobalTheory.SubquotCover
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric

noncomputable section

namespace GlobalTheory.GaugeSubChartSurj

theorem exists_ball_subset {V M : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] (ι : V →L[ℝ] M) (p : M →L[ℝ] V)
    (hp : ∀ x, p (ι x) = x) {f : M → M} (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) 0)
    (h0 : f 0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : V, ‖x‖ < ρ → ∃ y : V, ‖f (ι y)‖ < δ ∧ p (f (ι y)) = x := by
  have hf' : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) (ι 0) := by rwa [map_zero]
  have h1 := hf'.comp (0 : V) ι.hasStrictFDerivAt
  have h2 := p.hasStrictFDerivAt.comp (0 : V) h1
  have h3 : p.comp ((ContinuousLinearMap.id ℝ M).comp ι) =
      (ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V) := by
    ext1 x; exact hp x
  rw [h3] at h2
  have h4 := h2.map_nhds_eq_of_equiv
  simp only [map_zero, h0] at h4
  have h5 : Tendsto (fun y => f (ι y)) (𝓝 0) (𝓝 0) := by
    have := h1.continuousAt.tendsto
    simpa only [map_zero, h0] using this
  have h6 : (fun y => f (ι y)) ⁻¹' ball 0 δ ∈ 𝓝 (0 : V) := h5 (ball_mem_nhds 0 hδ)
  have h7 := image_mem_map (m := fun y => p (f (ι y))) h6
  rw [h4] at h7
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 h7
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hsub (mem_ball_zero_iff.2 hx)
  exact ⟨y, mem_ball_zero_iff.1 hy, hyx⟩

variable {n d : ℕ}

def comb (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x := ∑ i, x i • E i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

def coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun X := WithLp.toLp 2 (fun i => ((X * (E i)ᴴ).trace).re)
  map_add' X Y := by ext i; simp [Matrix.add_mul]
  map_smul' c X := by ext i; simp

theorem coord_comb (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (x : EuclideanSpace ℝ (Fin d)) :
    coord E (comb E x) = x := by
  ext k
  change (((∑ i, x i • E i) * (E k)ᴴ).trace).re = x k
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
    Complex.smul_re, hE]
  simp


open scoped Matrix.Norms.Frobenius in
theorem chart_surj : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ → ∃ g : Formalism.REAL.UJ ε, uMat g - 1 ∈ A ∧ Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ ∧ (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = x := by
  intro n ε A d E hA hE hs δ hδ
  obtain ⟨ρ, hρ, h⟩ := exists_ball_subset (LinearMap.toContinuousLinearMap (comb E))
    (LinearMap.toContinuousLinearMap (coord E)) (coord_comb E hE)
    (f := fun Y => NormedSpace.exp Y - 1)
    (HasStrictFDerivAt.sub_const (f := NormedSpace.exp) 1 CompactDualExists.exp_strict)
    (sub_eq_zero.2 (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))) hδ
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := h x hx
  have hm : comb E y ∈ A ∧ Formalism.REAL.inG ε (comb E y) :=
    (hs (∑ i, y i • E i)).2 (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  refine ⟨GaugeConst.expJ ε ⟨comb E y, hm.2⟩, GaugeSubExists.exp_sub_one_mem A hA hm.1, ?_, hyx⟩
  rw [GaugeConst.sqrt_hs]
  exact hy

end GlobalTheory.GaugeSubChartSurj
end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftedFlag_lattice_chain_spans : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Thp Λ F F' ≤ La Λ g F F' ∧ La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') ∧ spanE S (Thp Λ F F') = Hp Λ F F' ∧ ∀ (F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), spanE S (Mlat Λ F F' F'' β g) = Th Λ F F' F'' β := by
  first | exact @GlobalTheory.LoopC.LatChain.lattice_chain_spans | exact GlobalTheory.LoopC.LatChain.lattice_chain_spans | (intros; apply GlobalTheory.LoopC.LatChain.lattice_chain_spans <;> first | assumption | (letI := ‹Submodule.IsFullLattice _ _›; infer_instance))
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  first | exact @GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | exact GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | (intros; apply GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latDetH_map_injective_isometry : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  first | exact @GlobalTheory.LoopC.DetMap.latDetH_map | exact GlobalTheory.LoopC.DetMap.latDetH_map | (intros; apply GlobalTheory.LoopC.DetMap.latDetH_map <;> assumption)
end
