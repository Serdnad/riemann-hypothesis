module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
import Aesop.Main
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.CptSobProof

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Van {V : Type} [Zero V] (R : ℝ) (f : Mat n → V) : Prop := ∀ y ∈ GLs n, R < lg y → f y = 0

theorem isOpen_GLs : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_far (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (R : ℝ) :
    IsOpen {y : Mat n | y ∈ GLs n ∧ R < lg y} := by
  have h := hlg.isOpen_inter_preimage isOpen_GLs (isOpen_Ioi (a := R))
  exact h

section Vanish

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {R : ℝ} {f : Mat n → V}

theorem Van.rd (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (X : Mat n) : Van R (Rd X f) := by
  intro y hy hR
  have he : f =ᶠ[𝓝 y] fun _ => (0 : V) := by
    filter_upwards [(isOpen_far hlg R).mem_nhds ⟨hy, hR⟩] with z hz using h z hz.1 hz.2
  simp [Rd, he.fderiv_eq]

theorem Van.eu (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (a b : Fin n) :
    Van R (Eu s a b f) := by
  intro y hy hR
  have h1 := h.rd hlg (Matrix.single a b 1) y hy hR
  have h2 := h.rd hlg (Matrix.single a b Complex.I) y hy hR
  cases s <;> simp [Eu, h1, h2]

theorem Van.epow (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) (a b : Fin n) :
    Van R (Epow s m a b f) := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, h y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => (ih c b).eu hlg s a c y hy hR

theorem Van.gel (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) :
    Van R (gel s m f) := by
  intro y hy hR
  simp only [PositivityTheory.RgBcC.gel, Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => h.epow hlg s m a a y hy hR

theorem Van.om (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) : Van R (Om f) := by
  intro y hy hR
  have h1 := h.gel hlg true 2 y hy hR
  have h2 := h.gel hlg false 2 y hy hR
  simp [Om, h1, h2]

theorem Van.rw (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (w : List (Bool × Fin n × Fin n)) :
    Van R (Rw w f) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ih.rd hlg (bs p)

theorem rw_smooth (hC : RCalc) (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hC n).1 V _ ih).1 (bs p)

end Vanish

theorem memLp_of_van [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {R : ℝ} {g : Mat n → V}
    (hK : IsCompact {y : G n | lg y.val ≤ R}) (hc : ContinuousOn g (GLs n)) (hv : Van R g) :
    MemLp (fun y : G n => g y.val) 2 μ := by
  have hcont : Continuous (fun y : G n => g y.val) :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  have hsupp : HasCompactSupport (fun y : G n => g y.val) :=
    HasCompactSupport.intro hK fun y hy => hv y.val (val_mem_GLs y) (not_le.1 hy)
  exact hcont.memLp_of_hasCompactSupport hsupp

theorem cptSob : CptSob := by
  intro n _ _ μ _ V _ _ hL hC f hf hcpt
  obtain ⟨-, -, -, hs, hk, -⟩ := hL n
  obtain ⟨R, hR⟩ := hcpt
  have hv : Van R f := hR
  exact ⟨⟨hf, fun w => memLp_of_van μ (hk R) (rw_smooth hC hf w).continuousOn (hv.rw hs.continuousOn w)⟩,
    R, hv.om hs.continuousOn⟩

end GlobalTheory.CompanionTheory.CptSobProof
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

namespace GlobalTheory.CompanionTheory.DenseCpt

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

theorem val_emb (n : ℕ) : IsOpenEmbedding (Units.val : G n → Mat n) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℂ) (α := ℂ)
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem continuous_extend {n : ℕ} {V : Type} [NormedAddCommGroup V] {b : G n → V} (hb : Continuous b)
    (hs : HasCompactSupport b) : Continuous (Function.extend (Units.val : G n → Mat n) b 0) := by
  have he := val_emb n
  refine continuous_of_tsupport fun x h => ?_
  obtain ⟨u, -, rfl⟩ := hs.tsupport_extend_zero_subset he.continuous h
  rw [← he.continuousAt_iff]
  have : Function.extend (Units.val : G n → Mat n) b 0 ∘ Units.val = b :=
    funext fun y => he.injective.extend_apply _ _ _
  rw [this]
  exact hb.continuousAt

theorem exists_smooth {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : G n → V}
    (hb : Continuous b) (hs : HasCompactSupport b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : Mat n → V, ContDiff ℝ ∞ f ∧ (∀ y : G n, dist (b y) (f y.val) ≤ δ) ∧
      ∀ y, y ∉ (Units.val : G n → Mat n) '' tsupport b → f y = 0 := by
  have he := val_emb n
  obtain ⟨f, hf, hd, hsu⟩ := (continuous_extend hb hs).exists_contDiff_approx ⊤ (ε := fun _ => δ)
    continuous_const fun _ => hδ
  refine ⟨f, hf, fun y => ?_, fun y hy => ?_⟩
  · have := hd y.val
    rw [show Function.extend (Units.val : G n → Mat n) b 0 y.val = b y from he.injective.extend_apply _ _ _] at this
    rw [dist_comm]; exact this.le
  · by_contra hne
    have h1 := hsu (Function.mem_support.2 hne)
    exact hy (hs.tsupport_extend_zero_subset he.continuous (subset_tsupport _ h1))

theorem cpt_of {n : ℕ} {V : Type} [Zero V] (hL : LgFacts) {K : Set (G n)} (hK : IsCompact K) {f : Mat n → V}
    (hf : ∀ y, y ∉ (Units.val : G n → Mat n) '' K → f y = 0) : Cpt f := by
  have he := val_emb n
  have hc : IsCompact ((Units.val : G n → Mat n) '' K) := hK.image he.continuous
  have hsub : (Units.val : G n → Mat n) '' K ⊆ GLs n := by
    rintro _ ⟨u, -, rfl⟩; exact val_mem u
  have hcont : ContinuousOn (lg : Mat n → ℝ) ((Units.val : G n → Mat n) '' K) :=
    ((hL n).2.2.2.1.continuousOn).mono hsub
  obtain ⟨R, hR⟩ := (hc.image_of_continuousOn hcont).bddAbove
  refine ⟨R, fun y _ hy => hf y fun hm => ?_⟩
  exact absurd (hR ⟨y, hm, rfl⟩) (not_le.2 hy)

theorem denseD : DenseD := by
  intro n _ _ μ _ V _ _ hL
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (G n) := (val_emb n).isInducing.secondCountableTopology
  haveI : LocallyCompactSpace (G n) := (val_emb n).locallyCompactSpace
  intro x
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨b, hbs, hbd, hbc, hbm⟩ := (Lp.memLp x).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε2)
  set K := tsupport b with hKdef
  have hKc : IsCompact K := hbs
  set m : ℝ≥0∞ := μ K ^ (1 / (2 : ℝ≥0∞).toReal) with hm
  have hmt : m ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hKc.measure_lt_top.ne
  set c : ℝ := (ε / 2) / (m.toReal + 1) with hc
  have hm0 : 0 ≤ m.toReal := ENNReal.toReal_nonneg
  have hcpos : 0 < c := by positivity
  obtain ⟨f, hf, hd, hz⟩ := exists_smooth hbc hbs hcpos
  have hcf : Continuous fun y : G n => f y.val := hf.continuous.comp Units.continuous_val
  have hsupp : Function.support (fun y : G n => f y.val) ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hz _ fun ⟨u, hu, he⟩ => hyK (Units.ext he ▸ hu))
  have hcs : HasCompactSupport fun y : G n => f y.val :=
    HasCompactSupport.of_support_subset_isCompact hKc hsupp
  have hg : MemLp (fun y : G n => f y.val) 2 μ := hcf.memLp_of_hasCompactSupport hcs
  have hbg : eLpNorm (b - fun y : G n => f y.val) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_sub_le_of_dist_bdd μ hp hKc.measurableSet.nullMeasurableSet hcpos.le
      (hbm.aestronglyMeasurable.sub hg.aestronglyMeasurable) hd (subset_tsupport b) hsupp).trans ?_
    change ENNReal.ofReal c * m ≤ _
    conv_lhs => rw [← ENNReal.ofReal_toReal hmt]
    rw [← ENNReal.ofReal_mul hcpos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨hg.toLp _, ⟨f, hf.contDiffOn, cpt_of hL hKc hz, ?_⟩, ?_⟩
  · simp only [cls]; rw [dite_eq_left hg]
  · rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
      ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp x).sub (Lp.memLp (hg.toLp _))).eLpNorm_ne_top hε.le]
    have h1 : eLpNorm (⇑x - ⇑(hg.toLp _)) 2 μ = eLpNorm (⇑x - fun y : G n => f y.val) 2 μ :=
      eLpNorm_congr_ae (by filter_upwards [hg.coeFn_toLp] with y hy; simp [hy])
    rw [h1]
    have h2 : (⇑x - fun y : G n => f y.val) = (⇑x - b) + (b - fun y : G n => f y.val) := by
      ext y; simp
    rw [h2]
    refine (eLpNorm_add_le (p := 2) (by norm_num)).trans ?_
    calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hbd hbg
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end GlobalTheory.CompanionTheory.DenseCpt
end
end

section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ParamInt

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] {ν : Measure X} [IsFiniteMeasureOnCompacts ν]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuousOn_of_iteratedFDeriv_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W}
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ 0 (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => F p.1 p.2) =
      fun p => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) W (fun _ => 0)
        (iteratedFDeriv ℝ 0 (F p.1) p.2) := by
    funext p; simp
  rw [e]
  exact (ContinuousLinearMap.continuous _).comp_continuousOn h

theorem continuousOn_iteratedFDeriv_fderiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W} (m : ℕ)
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) =
      fun p : X × E => continuousMultilinearCurryRightEquiv' ℝ m E W
        (iteratedFDeriv ℝ (m + 1) (F p.1) p.2) := by
    funext p
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [e]
  exact (LinearIsometryEquiv.continuous _).comp_continuousOn h

theorem integrable_bound {K : Set X} (hK : IsCompact K) (C : ℝ) :
    Integrable ((toMeasurable ν K).indicator fun _ => C) ν := by
  rw [integrable_indicator_iff (measurableSet_toMeasurable ν K)]
  refine integrableOn_const ?_
  rw [measure_toMeasurable]
  exact hK.measure_lt_top.ne

theorem le_bound {W : Type} [NormedAddCommGroup W] {K : Set X} {C : ℝ} {t : X} {w : W}
    (h1 : t ∈ K → ‖w‖ ≤ C) (h2 : t ∉ K → w = 0) :
    ‖w‖ ≤ (toMeasurable ν K).indicator (fun _ => max C 0) t := by
  by_cases ht : t ∈ K
  · rw [indicator_of_mem (subset_toMeasurable ν K ht)]
    exact (h1 ht).trans (le_max_left _ _)
  · rw [h2 ht, norm_zero]
    exact indicator_nonneg (fun _ _ => le_max_right _ _) _

theorem hasFDerivAt_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) {F : X → E → V}
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h0 : ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U))
    (hd : ContinuousOn (fun p : X × E => fderiv ℝ (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0)
    {x₀ : E} (hx : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
  obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
  have hN : U ∩ interior U' ∈ 𝓝 x₀ := inter_mem (hU.mem_nhds hx) (interior_mem_nhds.2 hU')
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hN
  have hBc : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hKB := hK.prod hBc
  have hsub : K ×ˢ Metric.closedBall x₀ r ⊆ univ ×ˢ U :=
    fun p hp => ⟨mem_univ _, (hball hp.2).1⟩
  obtain ⟨C, hC⟩ := hKB.exists_bound_of_continuousOn (hd.mono hsub)
  obtain ⟨C₀, hC₀⟩ := hKB.exists_bound_of_continuousOn (h0.mono hsub)
  have hx₀B : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  have hdz : ∀ t ∉ K, ∀ x ∈ Metric.closedBall x₀ r, fderiv ℝ (F t) x = 0 := by
    intro t ht x hxB
    have : F t =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_interior.mem_nhds (hball hxB).2] with y hy
      exact hz t ht y (interior_subset hy)
    rw [this.fderiv_eq]
    simp
  have hct : ∀ x ∈ U, Continuous fun t => F t x := fun x hxU =>
    h0.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  have hcd : ∀ x ∈ U, Continuous fun t => fderiv ℝ (F t) x := fun x hxU =>
    hd.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => F t x)
    (F' := fun x t => fderiv ℝ (F t) x) (s := Metric.closedBall x₀ r)
    (bound := (toMeasurable ν K).indicator fun _ => max C 0)
    (Metric.closedBall_mem_nhds x₀ hr) ?_ ?_ ?_ ?_ (integrable_bound hK _) ?_
  · filter_upwards [hU.mem_nhds hx] with x hxU
    exact (hct x hxU).aestronglyMeasurable
  · refine Integrable.mono' (integrable_bound (ν := ν) hK (max C₀ 0))
      (hct x₀ hx).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    exact le_bound (fun ht => hC₀ (t, x₀) ⟨ht, hx₀B⟩) (fun ht => hz t ht x₀ (interior_subset (hball hx₀B).2))
  · exact (hcd x₀ hx).aestronglyMeasurable
  · refine ae_of_all _ fun t x hxB => ?_
    exact le_bound (fun ht => hC (t, x) ⟨ht, hxB⟩) (fun ht => hdz t ht x hxB)
  · refine ae_of_all _ fun t x hxB => ?_
    exact (((h1 t).contDiffAt (hU.mem_nhds (hball hxB).1)).differentiableAt (by simp)).hasFDerivAt

theorem contDiffOn_integral_nat {U : Set E} (hU : IsOpen U) (m : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : X → E → V),
      (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ContDiffOn ℝ m (fun x => ∫ t, F t x ∂ν) U := by
  have key : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (F : X → E → V), (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ∀ x₀ ∈ U, HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
    intro V _ _ _ F h1 h2 h3 x₀ hx
    exact hasFDerivAt_integral hU h1 (continuousOn_of_iteratedFDeriv_zero (h2 0))
      (continuousOn_of_iteratedFDeriv_zero (F := fun t => fderiv ℝ (F t))
        (continuousOn_iteratedFDeriv_fderiv 0 (h2 1))) h3 hx
  induction m with
  | zero =>
    intro V _ _ _ F h1 h2 h3
    have : ContinuousOn (fun x => ∫ t, F t x ∂ν) U := fun x hx =>
      (key V F h1 h2 h3 x hx).continuousAt.continuousWithinAt
    have h : ContDiffOn ℝ 0 (fun x => ∫ t, F t x ∂ν) U := contDiffOn_zero.2 this
    simpa using h
  | succ m ih =>
    intro V _ _ _ F h1 h2 h3
    have hG1 : ∀ t, ContDiffOn ℝ ∞ (fderiv ℝ (F t)) U := fun t =>
      (h1 t).fderiv_of_isOpen hU (by simp)
    have hG2 : ∀ k : ℕ, ContinuousOn
        (fun p : X × E => iteratedFDeriv ℝ k (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := fun k =>
      continuousOn_iteratedFDeriv_fderiv k (h2 (k + 1))
    have hG3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧
        ∀ t ∉ K, ∀ x ∈ U', fderiv ℝ (F t) x = 0 := by
      intro x₀ hx
      obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
      refine ⟨interior U', interior_mem_nhds.2 hU', K, hK, fun t ht x hxU => ?_⟩
      have : F t =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isOpen_interior.mem_nhds hxU] with y hy
        exact hz t ht y (interior_subset hy)
      rw [this.fderiv_eq]
      simp
    have hI := ih (E →L[ℝ] V) (fun t => fderiv ℝ (F t)) hG1 hG2 hG3
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (key V F h1 h2 h3 x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hI.congr fun x hx => (key V F h1 h2 h3 x hx).fderiv

theorem contDiffOn_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) (F : X → E → V)
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h2 : ∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, F t x ∂ν) U :=
  contDiffOn_infty.2 fun m => contDiffOn_integral_nat hU m V F h1 h2 h3

theorem intSmooth : PositivityTheory.RgBcC.VC.IntSmooth := by
  intro n X _ _ _ _ ν _ V _ _ _ F h1 h2 h3
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hU : IsOpen (PositivityTheory.RgBcC.GLs n) := by
    have h : Continuous fun g : PositivityTheory.RgTw.Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne_fun h continuous_const
  exact contDiffOn_integral hU F h1 h2 h3

end GlobalTheory.CompanionTheory.ParamInt
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Sym

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.RCalc (Rd_add Rd_smul differentiableAt_of_smooth Rd_contDiffOn isOpen_GLs)
open GlobalTheory.CompanionTheory.WaveSpd (val_mem_GLs)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Expand

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Expand

section Pairing

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem integrable_of_cpt (hL : LgFacts) {F : Mat n → ℂ} (hc : ContinuousOn F (GLs n)) (hF : Cpt F) :
    Integrable (fun y : G n => F y.val) μ := by
  obtain ⟨R, hR⟩ := hF
  have hc' : Continuous fun y : G n => F y.val :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  refine hc'.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem cpt_inner_left {u v : Mat n → V} (hu : Cpt u) : Cpt fun y => ⟪u y, v y⟫_ℂ := by
  obtain ⟨R, hR⟩ := hu
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem integrable_inner (hL : LgFacts) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n))
    (hv : ContDiffOn ℝ ∞ v (GLs n)) (hc : Cpt fun y => ⟪u y, v y⟫_ℂ) :
    Integrable (fun y : G n => ⟪u y.val, v y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (F := fun y => ⟪u y, v y⟫_ℂ) (hu.inner ℂ hv).continuousOn hc

end Pairing

end GlobalTheory.CompanionTheory.WaveK.Sym
end
end
