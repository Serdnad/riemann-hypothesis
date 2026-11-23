module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp Filter Topology
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LenCont

theorem eucl_eq {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucl, Complex.normSq_eq_norm_sq]

theorem eucl_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    eucl (A *ᵥ v) ≤ opn A * eucl v := by
  rw [eucl_eq, eucl_eq, opn, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem opn_continuous {n : ℕ} : Continuous (opn (n := n)) := by
  unfold opn
  refine continuous_norm.comp ?_
  exact LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)

theorem opn_one {n : ℕ} : opn (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  rw [opn, map_one, norm_one]

def len {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))}

theorem len_le {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g h : Matrix (Fin n) (Fin n) ℂ)
    (hh : IsUnit h.det) : len Y f g ≤ opn (g⁻¹ * h) * len Y f h := by
  have hb : BddBelow {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))} :=
    ⟨0, by rintro t ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  have hne : {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}.Nonempty := ⟨_, 0, Y.zero_mem, rfl⟩
  have key : ∀ t ∈ {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}, len Y f g ≤ opn (g⁻¹ * h) * t := by
    rintro t ⟨y, hy, rfl⟩
    refine (csInf_le hb ⟨y, hy, rfl⟩).trans ?_
    have := eucl_mulVec_le (g⁻¹ * h) (h⁻¹ *ᵥ (f - y))
    rwa [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one] at this
  have h0 : 0 ≤ opn (g⁻¹ * h) := norm_nonneg _
  rcases h0.eq_or_lt with h0 | h0
  · obtain ⟨t, ht⟩ := hne
    have := key t ht
    rw [← h0] at this ⊢
    simpa using this
  · rw [mul_comm, ← div_le_iff₀ h0]
    refine le_csInf hne fun t ht => ?_
    rw [div_le_iff₀ h0, mul_comm]
    exact key t ht

theorem len_continuousOn {n : ℕ} (Y : Submodule ℂ (Fin (n + 1) → ℂ)) (f : Fin (n + 1) → ℂ) :
    ContinuousOn (len Y f) {g | IsUnit g.det} := by
  intro x₀ hx₀
  have hx₀' : IsUnit x₀.det := hx₀
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → _) x₀ := by
    refine continuousAt_matrix_inv x₀ ?_
    obtain ⟨u, hu⟩ := hx₀'
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have h1 : Tendsto (fun x => opn (x⁻¹ * x₀)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x⁻¹ * x₀)) x₀ :=
      opn_continuous.continuousAt.comp (hinv.mul continuousAt_const)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have h2 : Tendsto (fun x => opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x₀⁻¹ * x)) x₀ :=
      opn_continuous.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have hU : Tendsto (fun x => opn (x⁻¹ * x₀) * len Y f x₀) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    simpa using h1.mul_const (len Y f x₀)
  have hL : Tendsto (fun x => len Y f x₀ / opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    have := (tendsto_const_nhds (x := len Y f x₀)).div h2 one_ne_zero
    rw [div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.mono_left nhdsWithin_le_nhds)
    (hU.mono_left nhdsWithin_le_nhds) ?_ (Eventually.of_forall fun x => len_le Y f x x₀ hx₀')
  filter_upwards [self_mem_nhdsWithin, (h2.eventually (lt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds]
    with x hx hpos
  rw [div_le_iff₀ hpos, mul_comm]
  exact len_le Y f x₀ x hx

theorem fold_continuousOn {X ι : Type*} [TopologicalSpace X] [DecidableEq ι] (S : Set X) (F : ι → X → ℝ)
    (hF : ∀ a, ContinuousOn (F a) S) (s : Finset ι) :
    ContinuousOn (fun x => s.fold max 1 fun a => F a x) S := by
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact continuous_max.comp_continuousOn ((hF a).prodMk ih)

theorem lA_Sg_continuousOn : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)),
    (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  intro k r z
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have h : ∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r) := fun a =>
    (len_continuousOn _ (fvec k r z a)).mono fun g hg => ((uHGroup _ _ hH).2.2 g hg).1
  exact ⟨h, fold_continuousOn (GG k r) (fun a x => lA k r z x a) h Finset.univ⟩

end GlobalTheory.Amp.LenCont
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ inUJ isClosedEmbeddingMatrix)

noncomputable section

namespace GlobalTheory.LeviIso

theorem measurable_matInv (m : ℕ) :
    Measurable fun x : Fin m → Fin m → ℂ => (fun r s => (Matrix.of x)⁻¹ r s : Fin m → Fin m → ℂ) := by

  have hdet : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_det
  have hadj : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).adjugate :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_adjugate
  refine Measurable.of_eval fun r => Measurable.of_eval fun s => ?_
  have key : (fun x : Fin m → Fin m → ℂ => (Matrix.of x)⁻¹ r s) =
      fun x => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate r s := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [key]
  exact (hdet.measurable.inv).mul
    (((continuous_apply s).comp ((continuous_apply r).comp hadj)).measurable)

theorem measurableEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) := by

  have h : Topology.IsClosedEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) :=
    (isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem measurable_lev {n n₀ a : ℕ} {j : Fin a → ℕ} (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) :
    Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ) := by

  let Φ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) →
      Fin n → Fin n → ℂ := fun w r s =>
    (∑ i, B i * Matrix.of (w.1 i) * (B i)ᴴ + ∑ i, Jm ε * B i * (Matrix.of (w.2.1 i))ᴴ * (B i)ᴴ * Jm ε +
      B₀ * Matrix.of w.2.2 * B₀ᴴ) r s
  have hΦ : Continuous Φ := by
    refine continuous_pi fun r => continuous_pi fun s => ?_
    refine Continuous.matrix_elem ?_ r s
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · refine continuous_finsetSum _ fun i _ => ?_
      exact (continuous_const.matrix_mul
        ((continuous_apply i).comp continuous_fst : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of (w.1 i)))).matrix_mul
        continuous_const
    · refine continuous_finsetSum _ fun i _ => ?_
      exact ((continuous_const.matrix_mul
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd) : Continuous fun w :
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) =>
            (Matrix.of (w.2.1 i))).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
        continuous_const
    · exact (continuous_const.matrix_mul
        ((continuous_snd.comp continuous_snd) : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of w.2.2))).matrix_mul
        continuous_const
  have hinv : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun i r s => (Matrix.of (z.1 i))⁻¹ r s : ∀ i, Fin (j i) → Fin (j i) → ℂ) :=
    Measurable.of_eval fun i =>
      (measurable_matInv (j i)).comp ((measurable_pi_apply i).comp measurable_fst)
  have hg : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => uMat z.2 r s : Fin n₀ → Fin n₀ → ℂ) :=
    (measurableEmbedding_uMat ε₀).measurable.comp measurable_snd
  have hcomp := hΦ.measurable.comp (measurable_fst.prodMk (hinv.prodMk hg))
  convert hcomp using 1
  funext z r s
  simp only [Function.comp_apply, Φ, lev]
  rfl

theorem exists_measurable_levMap (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (h : IsFrame ε ε₀ B B₀) :
    ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε, Measurable θ ∧
      ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
        uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  classical

  let S : Set ((∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀) := {z | ∀ i, (Matrix.of (z.1 i)).det ≠ 0}
  have hex : ∀ z ∈ S, ∃ g : UJ ε, uMat g = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    have hU : inUJ ε (lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) := h.inUJ_lev _ _ hz z.2.2
    have hr : lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) ∈
        Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact hU
    obtain ⟨g, hg⟩ := hr
    exact ⟨g, hg⟩
  let θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε := fun z =>
    if hz : z ∈ S then (hex z hz).choose else 1
  have hθ : ∀ z ∈ S, uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    simp only [θ, dif_pos hz]
    exact (hex z hz).choose_spec
  refine ⟨θ, ?_, fun z hz => hθ z hz⟩
  have hdet : ∀ i, Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det :=
    fun i =>
      have hc : Continuous fun x : Fin (j i) → Fin (j i) → ℂ => (Matrix.of x).det :=
        (continuous_id (X := Matrix (Fin (j i)) (Fin (j i)) ℂ)).matrix_det
      hc.measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  have hS : MeasurableSet S := by
    have : S = ⋂ i, (fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det) ⁻¹' {0}ᶜ := by
      ext z
      simp [S]
    rw [this]
    exact MeasurableSet.iInter fun i => (hdet i) (measurableSet_singleton 0).compl
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have heq : ((fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ)) ∘ θ) = fun z =>
      if z ∈ S then (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ)
      else (fun r s => uMat (1 : UJ ε) r s) := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Function.comp_apply, if_pos hz, hθ z hz]
    · simp only [Function.comp_apply, if_neg hz, θ, dif_neg hz]
  rw [heq]
  exact Measurable.ite hS (measurable_lev ε ε₀ B B₀) measurable_const

end GlobalTheory.LeviIso
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

private lemma continuous_det_of' (j : ℕ) :
    Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := by
  fun_prop

theorem measurable_haarLoc_density (j : ℕ) :
    Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) := by
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_det_of' j).measurable
  exact ENNReal.measurable_ofReal.comp ((hd.norm.pow_const 2).inv.pow_const j)

theorem measurePreserving_withDensity_of_invariant {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) {g : X → ENNReal} (hg : Measurable g) (hfg : ∀ x, g (f x) = g x) :
    MeasurePreserving f (μ.withDensity g) (μ.withDensity g) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  conv_rhs => rw [← hf.map_eq]
  rw [setLIntegral_map hs hg hf.measurable]
  simp only [hfg]

theorem haarLoc_conj_and_null : ∀ j : ℕ, MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (haarLoc j) (haarLoc j) ∧ haarLoc j {x | (Matrix.of x).det = 0} = 0 := by
  intro j
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (show Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det by fun_prop).measurable
  constructor
  ·
    have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
      have h := Complex.conjLIE.measurePreserving
      have e : (⇑Complex.conjLIE : ℂ → ℂ) = ⇑(starRingEnd ℂ) := funext Complex.conjLIE_apply
      rwa [e] at h
    have hv : MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s))
        (volume : Measure (Fin j → Fin j → ℂ)) volume :=
      volume_preserving_pi fun _ => volume_preserving_pi fun _ => hc
    refine measurePreserving_withDensity_of_invariant hv (measurable_haarLoc_density j) ?_
    intro x
    have hdet : (Matrix.of fun r s => starRingEnd ℂ (x r s)).det = starRingEnd ℂ (Matrix.of x).det :=
      ((starRingEnd ℂ).map_det (Matrix.of x)).symm
    simp only [hdet, Complex.norm_conj]
  ·
    have hS : MeasurableSet {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} :=
      measurableSet_eq_fun hd measurable_const
    rw [haarLoc, withDensity_apply _ hS, ← lintegral_indicator hS]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have : ({x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0}.indicator
          fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)) = 0 := by
        funext x
        by_cases hx : (Matrix.of x).det = 0
        · simp [hx, zero_pow hj.ne']
        · simp [Set.indicator_of_notMem (show x ∉ {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} from hx)]
      rw [this, Pi.zero_def, lintegral_zero]

end GlobalTheory.LeviIso
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Size

theorem detOn_of_frame {n : ℕ} {m : Type} [Fintype m] [DecidableEq m] (g : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) m ℂ) (X : Matrix m m ℂ) (W : Submodule ℂ (Fin n → ℂ)) (hC : Cᴴ * C = 1)
    (hW : ∀ y, y ∈ W ↔ ∃ u, y = C *ᵥ u) (hg : g * C = C * X) : detOn g W = ‖X.det‖ := by
  have hst : ∀ y ∈ W, Matrix.toLin' g y ∈ W := by
    intro y hy
    obtain ⟨u, rfl⟩ := (hW y).1 hy
    exact (hW _).2 ⟨X *ᵥ u, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]⟩
  let f : (m → ℂ) →ₗ[ℂ] W := (Matrix.toLin' C).codRestrict W fun u => (hW _).2 ⟨u, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun y => ?_⟩
    · have h1 : C *ᵥ u = C *ᵥ v := congrArg Subtype.val h
      have h2 := congrArg (fun y => Cᴴ *ᵥ y) h1
      simpa only [Matrix.mulVec_mulVec, hC, Matrix.one_mulVec] using h2
    · obtain ⟨u, hu⟩ := (hW y).1 y.2
      exact ⟨u, Subtype.ext hu.symm⟩
  let e := LinearEquiv.ofBijective f hf
  have he : (Matrix.toLin' g).restrict hst =
      (e : (m → ℂ) →ₗ[ℂ] W) ∘ₗ Matrix.toLin' X ∘ₗ (e.symm : W →ₗ[ℂ] (m → ℂ)) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨u, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    change g *ᵥ (C *ᵥ u) = C *ᵥ (X *ᵥ u)
    rw [Matrix.mulVec_mulVec, hg, Matrix.mulVec_mulVec]
  unfold detOn
  rw [dite_eq_left hst, he, LinearMap.det_conj, LinearMap.det_toLin']

theorem detOn_blocks {n a : ℕ} {j : Fin a → ℕ} (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : Fin a → Prop) [DecidablePred p] (W : Submodule ℂ (Fin n → ℂ))
    (h1 : ∀ i, (B i)ᴴ * B i = 1) (h2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0)
    (hW : ∀ y, y ∈ W ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i, ¬ p i → u i = 0) ∧ y = ∑ i, B i *ᵥ u i)
    (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ)
    (hg : ∀ i, g * B i = B i * x i) :
    detOn g W = ∏ i ∈ Finset.univ.filter p, ‖(x i).det‖ := by
  let C : Matrix (Fin n) (Σ i : {i // p i}, Fin (j i)) ℂ := Matrix.of fun r s => B s.1 r s.2
  have hCv : ∀ u, C *ᵥ u = ∑ i : {i // p i}, B i *ᵥ fun s => u ⟨i, s⟩ := by
    intro u
    funext r
    simp [C, Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [detOn_of_frame g C (Matrix.blockDiagonal' fun i : {i // p i} => x i) W ?_ ?_ ?_]
  · rw [ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', norm_prod,
      Finset.prod_subtype (Finset.univ.filter p) (p := p) (by simp)]
  · ext ⟨i, s⟩ ⟨k, t⟩
    change ((B i)ᴴ * B k) s t = _
    by_cases h : i = k
    · subst h
      rw [h1]
      simp [Matrix.one_apply]
    · rw [h2 i k (fun e => h (Subtype.ext e)), Matrix.one_apply_ne (fun e => h (congrArg Sigma.fst e))]
      rfl
  · intro y
    rw [hW]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun s => u s.1 s.2, ?_⟩
      rw [hCv, ← Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun i => B i *ᵥ u i),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · rw [hu i h, Matrix.mulVec_zero]
    · rintro ⟨u, rfl⟩
      refine ⟨fun i => if h : p i then fun s => u ⟨⟨i, h⟩, s⟩ else 0, fun i h => dif_neg h, ?_⟩
      rw [hCv, ← Finset.sum_subset (Finset.filter_subset p Finset.univ) ?_,
        Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
      · refine Finset.sum_congr rfl fun i _ => ?_
        beta_reduce
        rw [dite_eq_left i.2]
      · intro i _ hi
        beta_reduce
        rw [dif_neg (by simpa using hi), Matrix.mulVec_zero]
  · ext r ⟨k, t⟩
    change (g * B k) r t = _
    rw [hg, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [C]
    · intro i _ hi
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hi]
    · simp

theorem locSize_blocks : ∀ (n a : ℕ) (j : Fin a → ℕ) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → SpansFlag B W → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ), (∀ i, (x i).det ≠ 0) → (∀ i, g * B i = B i * x i) → ∀ i, locSize j W g i = ‖(x i).det‖ ^ (-(1 : ℝ) / j i) := by
  intro n a j B W h1 h2 hW g x hx hg i
  unfold locSize
  rw [detOn_blocks B _ _ h1 h2 (hW i.succ) g x hg, detOn_blocks B _ _ h1 h2 (hW i.castSucc) g x hg]
  have e : (Finset.univ.filter fun k : Fin a => k.castSucc < i.succ) =
      insert i (Finset.univ.filter fun k : Fin a => k.castSucc < i.castSucc) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def, Fin.ext_iff,
      Fin.val_succ, Fin.val_castSucc]
    omega
  rw [e, Finset.prod_insert (by simp), mul_div_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hx k)

end GlobalTheory.LeviIso.Size
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem exists_sum_mulVec_of_triangular {n a : ℕ} {j : Fin a → ℕ} (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (hp : ∀ k i, i < k → p k i = 0)
    (hA : ∀ i, A i = ∑ k, B k * p k i) (l : Fin (a + 1)) (u : ∀ i, Fin (j i) → ℂ)
    (hu : ∀ i : Fin a, ¬ i.castSucc < l → u i = 0) :
    ∃ v : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < l → v i = 0) ∧
      ∑ i, A i *ᵥ u i = ∑ i, B i *ᵥ v i := by
  refine ⟨fun k => ∑ i, p k i *ᵥ u i, ?_, ?_⟩
  · intro k hk
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hik : i < k
    · rw [hp k i hik, Matrix.zero_mulVec]
    · have hki : k ≤ i := not_lt.mp hik
      have hi : ¬ i.castSucc < l := fun hi =>
        hk (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hki) hi)
      rw [hu i hi, Matrix.mulVec_zero]
  · simp_rw [hA, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sum]
    exact Finset.sum_comm

theorem spansFlag_of_triangular (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (hpq : ∀ k i, i < k → p k i = 0 ∧ q k i = 0) (hA : ∀ i, A i = ∑ k, B k * p k i)
    (hB : ∀ i, B i = ∑ k, A k * q k i) (h : SpansFlag A W) : SpansFlag B W := by
  intro k y
  rw [h k y]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact exists_sum_mulVec_of_triangular A B p (fun k i hik => (hpq k i hik).1) hA k u hu
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, he⟩ :=
      exists_sum_mulVec_of_triangular B A q (fun k i hik => (hpq k i hik).2) hB k v hv
    exact ⟨w, hw, he⟩

end GlobalTheory.LeviIso
end

section

open NumberField ReciprocityTheory.Aut

theorem _root_.GlobalTheory.T.exists_adelicUnitary_trivialOutside_splitPlace_loc_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (M : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))), ∃ x : Formalism.AUTREP.GAf L n, ReciprocityTheory.Aut.TrivOutside {s.v} x ∧ s.loc n x = M := by
  first | exact @GlobalTheory.SplitLift.exists_trivOutside_loc_eq | exact GlobalTheory.SplitLift.exists_trivOutside_loc_eq | (intros; apply GlobalTheory.SplitLift.exists_trivOutside_loc_eq <;> assumption)
end
