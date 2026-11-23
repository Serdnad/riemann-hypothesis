module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle019
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle020
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle241
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle065
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle044
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle308
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle292
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Submodule.IsLattice I.E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ xf : I.Gf, lamX I (1, xf) = Λ := by
  first | exact @GlobalTheory.SelfDualPoint.exists_lamX_eq | exact GlobalTheory.SelfDualPoint.exists_lamX_eq | (intros; apply GlobalTheory.SelfDualPoint.exists_lamX_eq <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
  {σ : Mat k r → (H →L[ℂ] H)} {w : H} {a : ℝ} {μG : Measure (Mt k r)} {d : ℝ}
  {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {μS : Measure (Mt k r)}

theorem afun_add (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u u' : H} (hu : u ∈ DD σ w) (hu' : u' ∈ DD σ w) {x : Mat k r} (hx : x ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (u + u') v ξ x =
      Afun (psiGen k r z c) π μS σ u v ξ x + Afun (psiGen k r z c) π μS σ u' v ξ x := by
  have hst := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have h1 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).1
  have h2 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u') (hst x hx u' hu') v hv).1
  simp only [Afun, be, map_add (f := _), coef_add_left, add_smul]
  rw [integral_add h1 h2, ContinuousLinearMap.add_apply]

theorem afun_smul (b : ℂ) (u v : H) (ξ : Wp) (x : Mat k r) :
    Afun (psiGen k r z c) π μS σ (b • u) v ξ x = b • Afun (psiGen k r z c) π μS σ u v ξ x := by
  simp only [Afun, be, map_smul, coef_smul_left, mul_smul]
  rw [integral_smul, ContinuousLinearMap.smul_apply]

theorem afun_mul_right (hσ : IsURepOn (GG k r) σ) (u v : H) (ξ : Wp) {x y : Mat k r}
    (hx : x ∈ GG k r) (hy : y ∈ GG k r) :
    Afun (psiGen k r z c) π μS σ (σ y u) v ξ x = Afun (psiGen k r z c) π μS σ u v ξ (x * y) := by
  simp only [Afun, hσ.1.2 x hx y hy, ContinuousLinearMap.comp_apply]

theorem afun_mul_left (hStd : Std σ w a μG d) (hSide : Side z π μS) {v : H} (hv : v ∈ DD σ w) (ξ : Wp)
    {u : H} (hu : u ∈ DD σ w) {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r)
    (hSG : Sset k r z ⊆ GG k r) :
    Afun (psiGen k r z c) π μS σ u v ξ (s * x) =
      PiS (psiGen k r z c) π s (Afun (psiGen k r z c) π μS σ u v ξ x) := by
  have hst := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have h := ((GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hst hStd.2.2.2.2.2.2.2.1
    (σ x u) (hst x hx u hu) v hv).2.1 s hs).1
  simp only [Afun]
  rw [hStd.2.1.1.2 s (hSG hs) x hx, ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.comp_apply]

theorem continuous_lmulM' (s : Mat k r) : Continuous (lmulM s : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem lintegral_comp_le_image {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] {μ : Measure X} {φ : X → X} (hmp : MeasurePreserving φ μ μ) (hφ : Continuous φ)
    (f : X → ENNReal) {K : Set X} (hK : IsCompact K) (hf : AEMeasurable f μ) :
    ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x in φ '' K, f x ∂μ := by
  have hm : MeasurableSet (φ '' K) := (hK.image hφ).isClosed.measurableSet
  have hmap : μ.map φ = μ := hmp.map_eq
  calc ∫⁻ x in K, f (φ x) ∂μ ≤ ∫⁻ x, (φ '' K).indicator f (φ x) ∂μ := by
        rw [← lintegral_indicator hK.isClosed.measurableSet]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · simp [Set.indicator, hx, Set.mem_image_of_mem φ hx]
        · simp [Set.indicator, hx]
    _ = ∫⁻ y, (φ '' K).indicator f y ∂μ := by
        have := lintegral_map' (μ := μ) (f := (φ '' K).indicator f) (g := φ)
          (by rw [hmap]; exact hf.indicator hm) hφ.aemeasurable
        rw [hmap] at this
        exact this.symm
    _ = ∫⁻ y in φ '' K, f y ∂μ := lintegral_indicator hm _

end GlobalTheory.SgInf.BesselExt


open GlobalTheory.SgInf.BesselExt in
theorem GlobalTheory.SgInf.bessel_ext_bounded : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ T : H → Mat k r → Wp, (∀ u ∈ DD σ w, T u = Afun (psiGen k r z c) π μS σ u v ξ) ∧ (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) ∧ (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) ∧ (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) ∧ (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) ∧ (∀ s ∈ Sset k r z, ∀ u : H, (fun x : Mt k r => T u (s * Matrix.of x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T u (Matrix.of x))) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hw0 : w ≠ 0 := by
    intro h; have h1 := hStd.2.2.2.1; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hDD := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hσ
  have hst : ∀ g ∈ GG k r, ∀ u ∈ DD σ w, σ g u ∈ DD σ w := hDD.1
  have hdense : Dense (DD σ w : Set H) := hDD.2.1 hStd.2.2.1 hw0
  have hconc : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by
    rw [ae_iff]; exact hHaar.2.2.1
  let F : H → Mt k r → Wp := fun u x => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)
  let K : ℕ → Set (Mt k r) := fun n => Metric.closedBall 0 n
  have hKm : ∀ n, MeasurableSet (K n) := fun n => Metric.isClosed_closedBall.measurableSet
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_closedBall 0 n
  have hcov : ⋃ n, K n = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈‖x‖⌉₊, ?_⟩
    simp only [K, Metric.mem_closedBall, dist_zero_right]; exact Nat.le_ceil _
  have hsub : ∀ L : Set (Mt k r), IsCompact L → ∃ n, L ⊆ K n := by
    intro L hL
    obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
    exact ⟨⌈R⌉₊, hR.trans (Metric.closedBall_subset_closedBall (Nat.le_ceil R))⟩
  have hadd : ∀ u ∈ DD σ w, ∀ u' ∈ DD σ w, F (u + u') =ᵐ[μG] fun x => F u x + F u' x := by
    intro u hu u' hu'
    filter_upwards [hconc] with x hx
    exact afun_add hStd hSide hv ξ hu hu' hx
  have hsmul : ∀ (b : ℂ), ∀ u ∈ DD σ w, F (b • u) =ᵐ[μG] fun x => b • F u x :=
    fun b u _ => Filter.Eventually.of_forall fun x => afun_smul b u v ξ _
  obtain ⟨T0, hT0D, hT0add, hT0smul, hT0b⟩ := GlobalTheory.T.extend_ae_linear_of_local_sq_bound_dense μG K hKm hcov (DD σ w) hdense F hadd hsmul
    (fun n => GlobalTheory.T.lintegral_besselCoefficient_compact_le k r σ w a μG d z c π μS hStd hSide v hv ξ (K n) (hKc n))
  have hT0m : ∀ u, AEStronglyMeasurable (T0 u) μG := by
    intro u
    have h : AEStronglyMeasurable (T0 u) (μG.restrict (⋃ n, K n)) :=
      aestronglyMeasurable_iUnion_iff.2 fun n => ((hT0b n).choose_spec u).1
    rwa [hcov, Measure.restrict_univ] at h
  have hT0bK : ∀ L : Set (Mt k r), IsCompact L → ∃ C : ℝ, ∀ u,
      ∫⁻ x in L, (‖T0 u x‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
    intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => (lintegral_mono_set hn).trans (hC u).2⟩
  have hT0sub : ∀ u u', (fun x => T0 u x - T0 u' x) =ᵐ[μG] T0 (u - u') := by
    intro u u'
    filter_upwards [hT0add (u - u') u'] with x hx
    rw [sub_add_cancel] at hx
    rw [hx]; simp
  have hmeasn : ∀ u, AEMeasurable (fun x => (‖T0 u x‖₊ : ENNReal) ^ 2) μG := fun u =>
    (hT0m u).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2
  refine ⟨fun u M => T0 u (Matrix.of.symm M), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; funext M; show T0 u _ = _; rw [hT0D u hu]; rfl
  · intro u u'; exact hT0add u u'
  · intro b u; exact hT0smul b u
  · intro L hL
    obtain ⟨n, hn⟩ := hsub L hL
    obtain ⟨C, hC⟩ := hT0b n
    exact ⟨C, fun u => ⟨(hC u).1.mono_measure (Measure.restrict_mono hn le_rfl),
      (lintegral_mono_set hn).trans (hC u).2⟩⟩
  · intro y hy u
    have hmp : MeasurePreserving (rmulM y) μG μG :=
      ⟨(continuous_rmulM y).measurable, (GlobalTheory.T.isUnimodular_besselModelUnitaryGroup k r μG hHaar).1 y hy⟩
    refine GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 (σ y u) x) (fun u x => T0 u (rmulM y x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'
      filter_upwards [hT0sub (σ y u) (σ y u')] with x hx
      rw [hx, map_sub]
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(hC (σ y u)).1, ?_⟩⟩
      rw [← hσ.2.1 y hy u]; exact (hC (σ y u)).2
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_rmulM y))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_rmulM y) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro u hu
      show (fun x => T0 (σ y u) x) =ᵐ[μG] fun x => T0 u (rmulM y x)
      rw [hT0D _ (hst y hy u hu), hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_right hσ u v ξ hx hy
  · intro s hs u
    have hmp : MeasurePreserving (lmulM s : Mt k r → Mt k r) μG μG :=
      ⟨(continuous_lmulM' s).measurable, hHaar.2.2.2 s (hSG hs)⟩
    have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hSide.1 hSide.2.1 hSide.2.2.1
    have hPin : ‖PiS (psiGen k r z c) π s‖ ≤ 1 := (hPi.2.2.1 s hs).1
    have hnorm : ∀ e : Wp, ‖PiS (psiGen k r z c) π s e‖₊ ≤ ‖e‖₊ := fun e => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      exact ((PiS (psiGen k r z c) π s).le_opNorm e).trans
        (mul_le_of_le_one_left (norm_nonneg _) hPin)
    refine GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt μG K hKm hcov (DD σ w : Set H) hdense
      (fun u x => T0 u (lmulM s x)) (fun u x => PiS (psiGen k r z c) π s (T0 u x)) ?_ ?_ ?_ ?_ ?_ u
    · intro u u'; exact hmp.quasiMeasurePreserving.ae (hT0sub u u')
    · intro u u'
      filter_upwards [hT0sub u u'] with x hx
      rw [← map_sub, hx]
    · intro n
      obtain ⟨C, hC⟩ := hT0bK _ ((hKc n).image (continuous_lmulM' s))
      refine ⟨C, fun u => ⟨((hT0m u).comp_measurePreserving hmp).restrict, ?_⟩⟩
      exact (lintegral_comp_le_image hmp (continuous_lmulM' s) _ (hKc n) (hmeasn u)).trans (hC u)
    · intro n
      obtain ⟨C, hC⟩ := hT0b n
      refine ⟨C, fun u => ⟨(PiS (psiGen k r z c) π s).continuous.comp_aestronglyMeasurable (hC u).1, ?_⟩⟩
      refine le_trans (lintegral_mono fun x => ?_) (hC u).2
      exact pow_le_pow_left₀ (by positivity) (ENNReal.coe_le_coe.2 (hnorm _)) 2
    · intro u hu
      show (fun x => T0 u (lmulM s x)) =ᵐ[μG] fun x => PiS (psiGen k r z c) π s (T0 u x)
      rw [hT0D u hu]
      filter_upwards [hconc] with x hx
      exact afun_mul_left hStd hSide hv ξ hu hs hx hSG
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllBound

theorem exists_inner_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {v : E}
    (hv : v ≠ 0) : ∃ ξ : E, ⟪v, ξ⟫_ℂ = 1 ∧ ⟪ξ, v⟫_ℂ = 1 := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  refine ⟨(⟪v, v⟫_ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [inner_smul_right]
    exact inv_mul_cancel₀ hvv
  · rw [inner_smul_left, map_inv₀, inner_conj_symm]
    exact inv_mul_cancel₀ hvv

theorem lintegral_hsNormSq_ell_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∫⁻ γ, ENNReal.ofReal (hsNormSq ((d : ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal d⁻¹ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν l l' hl hl'

  obtain ⟨w₀, hw₀, hlw₀⟩ := hl.2.1
  obtain ⟨w₀', hw₀', hlw₀'⟩ := hl'.2.1
  obtain ⟨ξ, hξ₁, hξ₂⟩ := exists_inner_eq_one hlw₀
  obtain ⟨ξ', hξ₁', hξ₂'⟩ := exists_inner_eq_one hlw₀'

  have hbe : (⟪ξ, be (psiGen k r z c) π μS σ w₀ w₀ ξ⟫_ℂ).re = 1 := by
    rw [hl.2.2 w₀ hw₀ w₀ hw₀, rankOneInnerOperator_apply, inner_smul_right, hξ₁, hξ₂]
    simp
  have hbe' : (⟪ξ', be (psiGen k r z' c') π' μS' σ w₀' w₀' ξ'⟫_ℂ).re = 1 := by
    rw [hl'.2.2 w₀' hw₀' w₀' hw₀', rankOneInnerOperator_apply, inner_smul_right, hξ₁', hξ₂']
    simp
  have hbound := GlobalTheory.T.lintegral_hsNormSq_doubleCoset_le_fatou k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' ν hν
    w₀' hw₀' w₀ hw₀ ξ ξ'
  rw [hbe, hbe', mul_one, mul_one] at hbound
  refine le_trans (le_of_eq ?_) hbound

  have hreg : ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' := ae_iff.mpr hν.2.1
  refine lintegral_congr_ae ?_
  filter_upwards [hreg] with γ hγ
  rw [(GlobalTheory.T.iint_eq_ell_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' _ hγ).2
    w₀ hw₀ w₀' hw₀' ξ ξ', hξ₁, hξ₂']
  simp

end GlobalTheory.SgInf.EllBound
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.SpaceMass

theorem nondeg_of_PD {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

theorem PD_of_ortho {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (I : Submodule (𝓞 K) V) (n : ℕ)
    (hI : IsOrthoLattice h I n) : PD h := by
  obtain ⟨e, -, hsp, -, hort⟩ := hI
  intro τ x hx
  have hx' : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
  have e1 : h (∑ i, a i • e i) (∑ i, a i • e i) = ∑ i, star (a i) * a i := by

    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    hort, smul_eq_mul, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have e2 : (τ (∑ i, star (a i) * a i)).re = ∑ i, Complex.normSq (τ (a i)) := by

    rw [map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hK.2.1, Complex.normSq_eq_conj_mul_self.symm]
    simp
  rw [e1, e2]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (by simp [hc])
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.2 ((map_ne_zero τ).2 hi)

theorem mem_genus_self {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsFullLattice K M) : M ∈ genus h M := by
  refine ⟨hM, fun p _ => ⟨1, (isom h).one_mem, ?_⟩⟩
  exact one_smul (isom h) (loc (K := K) p M)

theorem real_bound (n' i : ℕ) (j l c m : ℝ) (hn : 1 ≤ n') (hl : 0 ≤ l) (hc : 0 ≤ c)
    (hm : m ≤ c * (n' : ℝ) ^ (j / 2)) :
    (i : ℝ) ^ (j + l) * m ≤ c * ((n' * i ^ 2 : ℕ) : ℝ) ^ ((j + l) / 2) := by
  have h1 : (n' : ℝ) ^ (j / 2) ≤ (n' : ℝ) ^ ((j + l) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have h2 : ((n' * i ^ 2 : ℕ) : ℝ) ^ ((j + l) / 2) = (n' : ℝ) ^ ((j + l) / 2) * (i : ℝ) ^ (j + l) := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2
    push_cast
    ring
  have h3 : (0 : ℝ) ≤ (i : ℝ) ^ (j + l) := by positivity
  rw [h2]
  calc (i : ℝ) ^ (j + l) * m ≤ (i : ℝ) ^ (j + l) * (c * (n' : ℝ) ^ ((j + l) / 2)) :=
        mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left h1 hc)) h3
    _ = _ := by ring

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ n : ℕ, 1 ≤ n → orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h' I * (n : ℝ) ^ (((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hj V' _ _ _ _ _ h' hs' I hI n hn
  have hnd := nondeg_of_PD h hp
  have hp' := PD_of_ortho h' hK I _ hI
  have hnd' := nondeg_of_PD h' hp'
  rcases (latsDisc (R := 𝓞 K) h n).eq_empty_or_nonempty with hE | ⟨M₁, hM₁⟩
  · rw [hE]
    unfold orbMass orbSum
    refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun q => q.2.elim) zero_le
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨M₀, hM₀, hle₀⟩ := hex M₁ hM₁.1

  obtain ⟨c, hc⟩ := hMM K hK _ hj
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  have hIfull : Submodule.IsFullLattice K I := by
    refine { toIsLattice := hIl, span_eq_top := ?_ }
    obtain ⟨e, -, hspan, rfl, -⟩ := hI
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIfull hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hcpos : 0 < c := hcI ▸ (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V' h' hK hs' hp' I hIfull).2.1
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  obtain ⟨hi0, hn₀⟩ := (hdisc M₁ hM₁.1).2.2.1 M₀ hM₀.1 hle₀
  have hn'0 := (hdisc M₀ hM₀.1).1
  set n' := discN h M₀ with hn'
  set i := idxN M₀ M₁ with hi
  have hnn : n = n' * i ^ 2 := hM₁.2 ▸ hn₀
  have hm₀ : mass h M₀ ≤ c * (n' : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
    rw [hc V h hs hp rfl M₀ hM₀]
    exact mul_le_mul_of_nonneg_left (GlobalTheory.T.maximalLatticeLocalFactorProduct_pos_and_le K V h hK hs hnd hj M₀ hM₀).2 hcpos.le
  have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
    intro g M hM
    have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M (mem_genus_self h M hM.1.1)
    have h2 := (hdisc M hM.1).2.2.2.1 _ h1
    exact ⟨h2.1, h2.2.trans hM.2⟩
  let X : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
    {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
  have hXst : Stable (isom h) X := by
    rintro g p ⟨h1, h2, h3⟩
    exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
  have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
    (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
  have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
    (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
  obtain ⟨mono, hconst, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) X := by
    rw [f1]
    refine mono _ _ _ _ subset_rfl fun M hM => ?_
    obtain ⟨M', hM', hle⟩ := hex M hM.1
    have hne : (X ∩ Prod.fst ⁻¹' {M}).Nonempty :=
      ⟨(M, M'), ⟨hM, (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
    have := Set.one_le_encard_iff_nonempty.2 hne
    exact_mod_cast this
  have s2 : orbMass (isom h) X ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) +
      Real.logb 2 (Module.finrank ℚ K))) * orbMass (isom h) (genus h M₀) := by
    rw [f2, ← hconst]
    refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
    refine le_trans ?_ (GlobalTheory.T.encard_sublattices_of_index_le K V h hK hs hnd M' hM'.1.toIsLattice i (Nat.one_le_iff_ne_zero.2 hi0))
    have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
    have : (X ∩ Prod.snd ⁻¹' {M'}).encard ≤
        {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N = i}.encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        refine ⟨h3, ?_⟩
        have h5 := ((hdisc N h1.1).2.2.1 N' hM''.1 h3).2
        rw [h1.2, hM''.2, hnn] at h5
        have h6 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn'0) h5
        exact ((Nat.pow_left_injective (by norm_num)) h6).symm
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine s1.trans (s2.trans ?_)
  rw [← hmass, ← ENNReal.ofReal_mul (by positivity), hcI, hnn]
  refine ENNReal.ofReal_le_ofReal (real_bound n' i _ _ c _ (Nat.one_le_iff_ne_zero.2 hn'0) ?_ hcpos.le hm₀)
  refine Real.logb_nonneg (by norm_num) ?_
  exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)

end GlobalTheory.Mass.SpaceMass
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.discreteSeries_counting_of_finite_and_bounds : (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) → GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  first | exact @GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds | exact GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds | (intros; apply GlobalTheory.CountSum.countingTheorem_of_finite_of_bounds <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem iwasawaFormula : IwasawaFormula := by
  intro n ε p q hp hq a j hj W hW c μN μM μK hc hN hM hK0 hK1 hKinv φ hφ
  obtain ⟨κ, -, -, hκ⟩ := GlobalTheory.T.iwasawa_integration_formula_up_to_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv
  have hconst := GlobalTheory.T.iwasawa_integration_formula_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hκ
  rw [hκ φ hφ, ← mul_assoc, hconst]

end GlobalTheory.FlagMeas
end
