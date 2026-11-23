module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst

open Filter Topology

def prodFns (V W : Type) [TopologicalSpace V] [TopologicalSpace W] : Submonoid C(V × W, ℝ) where
  carrier := {g | ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2}
  one_mem' := ⟨1, 1, fun z => by simp⟩
  mul_mem' := by
    rintro g h ⟨a, b, hg⟩ ⟨a', b', hh⟩
    exact ⟨a * a', b * b', fun z => by simp [hg, hh]; ring⟩

theorem prodFns_separates (V W : Type) [MetricSpace V] [MetricSpace W] :
    (Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ))).SeparatesPoints := by
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
    let g : C(V × W, ℝ) := ⟨fun z => dist z.2 q.2, by fun_prop⟩
    have hg : g ∈ (prodFns V W : Set C(V × W, ℝ)) := by
      show ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2
      exact ⟨1, ⟨fun y => dist y q.2, by fun_prop⟩, fun z => by simp [g]⟩
    refine ⟨g, ⟨g, Algebra.subset_adjoin hg, rfl⟩, ?_⟩
    simpa [g] using h2
  · let g : C(V × W, ℝ) := ⟨fun z => dist z.1 q.1, by fun_prop⟩
    have hg : g ∈ (prodFns V W : Set C(V × W, ℝ)) := by
      show ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2
      exact ⟨⟨fun x => dist x q.1, by fun_prop⟩, 1, fun z => by simp [g]⟩
    refine ⟨g, ⟨g, Algebra.subset_adjoin hg, rfl⟩, ?_⟩
    simpa [g] using h1

theorem hasCompactSupport_prod_mul {V W : Type} [MetricSpace V] [MetricSpace W] {a : V → ℝ} {b : W → ℝ}
    (ha : HasCompactSupport a) (hb : HasCompactSupport b) :
    HasCompactSupport (fun z : V × W => a z.1 * b z.2) := by
  refine HasCompactSupport.intro (ha.isCompact.prod hb.isCompact) fun z hz => ?_
  rcases not_and_or.mp (show ¬(z.1 ∈ tsupport a ∧ z.2 ∈ tsupport b) from hz) with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem tendsto_integral_of_prod {ι V W : Type} [MetricSpace V] [MetricSpace W] [ProperSpace V] [ProperSpace W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] (l : Filter ι)
    (M : ι → Measure (V × W)) (M₀ : Measure (V × W)) [∀ i, IsFiniteMeasureOnCompacts (M i)]
    [IsFiniteMeasureOnCompacts M₀]
    (h : ∀ (a : V → ℝ) (b : W → ℝ), Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b →
      Tendsto (fun i => ∫ z, a z.1 * b z.2 ∂M i) l (𝓝 (∫ z, a z.1 * b z.2 ∂M₀)))
    (F : V × W → ℝ) (hF : Continuous F) (hFc : HasCompactSupport F) :
    Tendsto (fun i => ∫ z, F z ∂M i) l (𝓝 (∫ z, F z ∂M₀)) := by
  have hKc : IsCompact (tsupport F) := hFc
  obtain ⟨χ₁, h1K, -, h1c, h1b⟩ := exists_continuous_one_zero_of_isCompact
    (hKc.image continuous_fst) isClosed_empty (Set.disjoint_empty _)
  obtain ⟨χ₂, h2K, -, h2c, h2b⟩ := exists_continuous_one_zero_of_isCompact
    (hKc.image continuous_snd) isClosed_empty (Set.disjoint_empty _)
  set χ : V × W → ℝ := fun z => χ₁ z.1 * χ₂ z.2 with hχ
  have hχc : Continuous χ := (χ₁.continuous.comp continuous_fst).mul (χ₂.continuous.comp continuous_snd)
  have hχs : HasCompactSupport χ := hasCompactSupport_prod_mul h1c h2c
  have hχ0 : ∀ z, 0 ≤ χ z := fun z => mul_nonneg (h1b _).1 (h2b _).1
  have hχF : ∀ z, χ z * F z = F z := by
    intro z
    by_cases hz : z ∈ tsupport F
    · have e1 : χ₁ z.1 = 1 := by simpa using h1K ⟨z, hz, rfl⟩
      have e2 : χ₂ z.2 = 1 := by simpa using h2K ⟨z, hz, rfl⟩
      simp [hχ, e1, e2]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hX : IsCompact (tsupport χ₁ ×ˢ tsupport χ₂) := h1c.isCompact.prod h2c.isCompact
  have hχX : ∀ z, z ∉ tsupport χ₁ ×ˢ tsupport χ₂ → χ z = 0 := by
    intro z hz
    rcases not_and_or.mp (show ¬(z.1 ∈ tsupport χ₁ ∧ z.2 ∈ tsupport χ₂) from hz) with h | h
    · simp [hχ, image_eq_zero_of_notMem_tsupport h]
    · simp [hχ, image_eq_zero_of_notMem_tsupport h]
  have hint : ∀ (G : C(V × W, ℝ)) (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
      Integrable (fun z => χ z * G z) m := fun G m _ =>
    (hχc.mul G.continuous).integrable_of_hasCompactSupport (hχs.mul_right (f' := G))
  have key : ∀ G ∈ Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ)),
      Tendsto (fun i => ∫ z, χ z * G z ∂M i) l (𝓝 (∫ z, χ z * G z ∂M₀)) := by
    intro G hG
    have hG' : G ∈ Submodule.span ℝ (prodFns V W : Set C(V × W, ℝ)) := by
      have : G ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ))) := hG
      rwa [Algebra.adjoin_eq_span, Submonoid.closure_eq] at this
    clear hG
    induction hG' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, b, hab⟩ : ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2 := hg
      have e : (fun z => χ z * g z) = fun z : V × W => (χ₁ z.1 * a z.1) * (χ₂ z.2 * b z.2) := by
        funext z
        rw [hab, hχ]
        ring
      rw [e]
      exact h (fun x => χ₁ x * a x) (fun y => χ₂ y * b y) (χ₁.continuous.mul a.continuous)
        (h1c.mul_right (f' := a)) (χ₂.continuous.mul b.continuous) (h2c.mul_right (f' := b))
    | zero =>
      have e : ∀ m : Measure (V × W), ∫ z, χ z * (0 : C(V × W, ℝ)) z ∂m = 0 := fun m => by simp
      simp only [e]
      exact tendsto_const_nhds
    | add g g' _ _ hg hg' =>
      have e : ∀ (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
          ∫ z, χ z * (g + g') z ∂m = ∫ z, χ z * g z ∂m + ∫ z, χ z * g' z ∂m := by
        intro m _
        rw [← integral_add (hint g m) (hint g' m)]
        congr 1
        funext z
        simp [mul_add]
      rw [e M₀]
      exact (hg.add hg').congr fun i => (e (M i)).symm
    | smul k g _ hg =>
      have e : ∀ m : Measure (V × W), ∫ z, χ z * (k • g) z ∂m = k * ∫ z, χ z * g z ∂m := by
        intro m
        rw [← integral_const_mul]
        congr 1
        funext z
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [e M₀]
      exact (hg.const_mul k).congr fun i => (e (M i)).symm
  obtain ⟨L, hLdef⟩ : ∃ L, L = ∫ z, χ z ∂M₀ := ⟨_, rfl⟩
  have hL : Tendsto (fun i => ∫ z, χ z ∂M i) l (𝓝 L) := by
    rw [hLdef]
    exact h χ₁ χ₂ χ₁.continuous h1c χ₂.continuous h2c
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : (0 : ℝ) < |L| + 1 := by positivity
  set δ := ε / 3 / (|L| + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ3 : δ * (|L| + 1) = ε / 3 := div_mul_cancel₀ _ (ne_of_gt hpos)
  obtain ⟨G, hGA, hGK⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (prodFns_separates V W) ⟨F, hF⟩ hX hδpos
  have hb : ∀ z, ‖F z - χ z * G z‖ ≤ δ * χ z := by
    intro z
    have e : F z - χ z * G z = χ z * (F z - G z) := by rw [mul_sub, hχF]
    rw [e, norm_mul, Real.norm_of_nonneg (hχ0 z)]
    by_cases hz : z ∈ tsupport χ₁ ×ˢ tsupport χ₂
    · have hz' : ‖F z - G z‖ ≤ δ := by
        have := (hGK z hz).le
        rwa [norm_sub_rev] at this
      calc χ z * ‖F z - G z‖ ≤ χ z * δ := mul_le_mul_of_nonneg_left hz' (hχ0 z)
        _ = δ * χ z := mul_comm _ _
    · simp [hχX z hz]
  have hbI : ∀ (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
      ‖∫ z, F z ∂m - ∫ z, χ z * G z ∂m‖ ≤ δ * ∫ z, χ z ∂m := by
    intro m _
    rw [← integral_sub (hF.integrable_of_hasCompactSupport hFc) (hint G m), ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((hχc.integrable_of_hasCompactSupport hχs).const_mul δ)
      (Eventually.of_forall hb)
  filter_upwards [hL.eventually (gt_mem_nhds (lt_add_one L)),
    Metric.tendsto_nhds.mp (key G hGA) (ε / 3) (by positivity)] with i hi1 hi2
  have e1 := hbI (M i)
  have e2 := hbI M₀
  rw [← hLdef] at e2
  rw [Real.norm_eq_abs, abs_le] at e1 e2
  rw [Real.dist_eq, abs_lt] at hi2 ⊢
  have h3 : δ * ∫ z, χ z ∂M i < ε / 3 := by
    calc δ * ∫ z, χ z ∂M i < δ * (|L| + 1) :=
          mul_lt_mul_of_pos_left (by linarith [le_abs_self L]) hδpos
      _ = ε / 3 := hδ3
  have h4 : δ * L < ε / 3 := by
    calc δ * L ≤ δ * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) hδpos.le
      _ < δ * (|L| + 1) := by linarith
      _ = ε / 3 := hδ3
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hi2.1, hi2.2]

theorem vag_prod (α β V W : Type) [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : α → V) (c' : β → W) (lam : Measure V) (lam' : Measure W)
    [IsLocallyFiniteMeasure lam] [IsLocallyFiniteMeasure lam'] (d d' : ℕ) (hc : Measurable c) (hc' : Measurable c')
    (h : Vag μ c lam d) (h' : Vag ν c' lam' d') :
    Vag (μ.prod ν) (Prod.map c c') (lam.prod lam') (d + d') := by
  intro φ hφ hφc
  let M : ℝ → Measure (V × W) := fun r =>
    Real.toNNReal ((r ^ (d + d'))⁻¹) • (μ.prod ν).map (fun g => (r⁻¹ • c g.1, r⁻¹ • c' g.2))
  have : ∀ r, IsFiniteMeasureOnCompacts (M r) := fun r => by dsimp only [M]; infer_instance
  have hmeas : ∀ r : ℝ, Measurable (fun g : α × β => (r⁻¹ • c g.1, r⁻¹ • c' g.2)) := fun r =>
    (((continuous_const_smul r⁻¹).measurable.comp hc).comp measurable_fst).prodMk
      (((continuous_const_smul r⁻¹).measurable.comp hc').comp measurable_snd)
  have hint : ∀ r : ℝ, 0 < r → ∀ f : V × W → ℝ, Continuous f →
      ∫ z, f z ∂M r = (r ^ (d + d'))⁻¹ * ∫ g, f (r⁻¹ • c g.1, r⁻¹ • c' g.2) ∂(μ.prod ν) := by
    intro r hr f hf
    dsimp only [M]
    rw [integral_smul_nnreal_measure, integral_map (hmeas r).aemeasurable hf.aestronglyMeasurable,
      NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity)]
  have key := tendsto_integral_of_prod (nhdsWithin (0 : ℝ) (Set.Ioi 0)) M (lam.prod lam') ?_ φ hφ hφc
  · refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hint r hr φ hφ]
    rfl
  · intro a b ha hac hb hbc
    have hprod := (h a ha hac).mul (h' b hb hbc)
    rw [integral_prod_mul a b]
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hint r hr (fun z => a z.1 * b z.2) ((ha.comp continuous_fst).mul (hb.comp continuous_snd))]
    have e := integral_prod_mul (μ := μ) (ν := ν) (fun x => a (r⁻¹ • c x)) (fun y => b (r⁻¹ • c' y))
    simp only at e ⊢
    rw [e, pow_add, mul_inv]
    ring

end GlobalTheory.IwConst
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwTangent

variable {n : ℕ}

open scoped Matrix.Norms.Frobenius

theorem coe_smul_eq (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : (t : ℂ) • X = t • X := by
  ext i j; simp

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have hs' := (hasSum_nat_add_iff' 1).2 hs
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_smul] at hs'
  have hc : IsClosed (A : Set (Matrix (Fin n) (Fin n) ℂ)) := A.closed_of_finiteDimensional
  exact hc.mem_of_tendsto hs'.tendsto_sum_nat (Filter.Eventually.of_forall fun m =>
    A.sum_mem fun k _ => A.smul_mem _ (hp k))

theorem mem_of_exp_sub_one_mem (T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) - 1 ∈ T) : X ∈ T := by
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
  have hc : IsClosed (T : Set (Matrix (Fin n) (Fin n) ℂ)) := T.closed_of_finiteDimensional
  refine hc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  simp only [zero_add, zero_smul, NormedSpace.exp_zero]
  exact T.smul_mem _ (h t)

theorem exists_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (t : ℝ) :
    ∃ g : Formalism.REAL.UJ ε, uMat g = NormedSpace.exp (t • X) :=
  ⟨GlobalTheory.GaugeConst.expJ ε ⟨t • X, (GlobalTheory.GaugeConst.lieJ ε).smul_mem t hX⟩, rfl⟩

theorem lie_algebra_of_isCut : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  rintro n ε S d E ⟨A, hA, -, hE, rfl⟩
  simp only [coe_smul_eq]
  have h1 : ∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ,
      ∃ g ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A}, uMat g = NormedSpace.exp (t • X) := by
    intro X hX t
    obtain ⟨hXA, hXG⟩ := (hE X).2 hX
    obtain ⟨g, hg⟩ := exists_exp hXG t
    refine ⟨g, ?_, hg⟩
    change uMat g - 1 ∈ A
    rw [hg]
    exact exp_sub_one_mem A hA (A.smul_mem t hXA)
  refine ⟨h1, fun T hT i => mem_of_exp_sub_one_mem T _ fun t => ?_, fun X hX h => (hE X).1 ⟨?_, hX⟩⟩
  · obtain ⟨g, hg, hg'⟩ := h1 (E i) (Submodule.subset_span ⟨i, rfl⟩) t
    rw [← hg']
    exact hT g hg
  · refine mem_of_exp_sub_one_mem A _ fun t => ?_
    obtain ⟨g, hg⟩ := exists_exp hX t
    rw [← hg]
    exact h t g hg

end GlobalTheory.IwTangent
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.CovPi

open GlobalTheory.HomCovolume

theorem hasCov_pi {β : Type} [Fintype β] {V : β → Type} [∀ b, NormedAddCommGroup (V b)]
    [∀ b, NormedSpace ℝ (V b)] [∀ b, FiniteDimensional ℝ (V b)] [∀ b, MeasurableSpace (V b)]
    [∀ b, BorelSpace (V b)] {μ : ∀ b, Measure (V b)} [∀ b, (μ b).IsAddHaarMeasure]
    {L : ∀ b, Submodule ℤ (V b)} {c : β → ℝ} (h : ∀ i, HasCov (μ i) (L i) (c i)) :
    HasCov (Measure.pi μ) (Submodule.pi Set.univ L) (∏ i, c i) := by
  classical
  have hd : ∀ i, DiscreteTopology (L i) := fun i => (h i).1
  have hz : ∀ i, IsZLattice ℝ (L i) := fun i => (h i).2.1
  have hc : ∀ i, ZLattice.covolume (L i) (μ i) = c i := fun i => (h i).2.2
  let B : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex ℤ (L i)) ℝ (V i) := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis ℝ
  have hBmem : ∀ i j, B i j ∈ L i := fun i j => by
    simp only [B, Module.Basis.ofZLatticeBasis_apply]
    exact (Module.Free.chooseBasis ℤ (L i) j).2
  have hBspan : ∀ i, Submodule.span ℤ (Set.range (B i)) = L i := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis_span ℝ
  have hspan : Submodule.pi Set.univ L = Submodule.span ℤ (Set.range (Pi.basis B)) := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_pi] at hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hxi : x i ∈ Submodule.span ℤ (Set.range (B i)) := by
        rw [hBspan]; exact hx i (Set.mem_univ i)
      refine Submodule.span_induction
        (p := fun y _ => Pi.single i y ∈ Submodule.span ℤ (Set.range (Pi.basis B))) ?_ ?_ ?_ ?_ hxi
      · rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨⟨i, j⟩, by simp⟩
      · simp
      · intro y z _ _ hy hz
        rw [Pi.single_add]; exact add_mem hy hz
      · intro a y _ hy
        rw [Pi.single_smul]; exact Submodule.smul_mem _ a hy
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_pi]
      intro i' _
      rw [Pi.basis_apply]
      by_cases hi : i' = i
      · subst hi; simpa using hBmem i' j
      · simp [hi]
  rw [hspan]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (Pi.basis B) _)]
  have hfd : ZSpan.fundamentalDomain (Pi.basis B) = Set.univ.pi fun i => ZSpan.fundamentalDomain (B i) := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Sigma.forall]
  rw [hfd, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hc i, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (L i)) (μ i)), measureReal_def]

theorem measurePreserving_of_sum_sq {κ σ : Type} [Fintype κ] [Fintype σ]
    (e : (κ → ℂ) ≃L[ℝ] (σ → ℂ)) (he : ∀ z, ∑ j, ‖e z j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    MeasurePreserving e volume volume := by
  let T : EuclideanSpace ℂ κ ≃L[ℝ] (κ → ℂ) := ((EuclideanSpace.equiv κ ℂ).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hnorm : ∀ v : EuclideanSpace ℂ κ, ‖v‖ ^ 2 = ∑ i, ‖T v i‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have hT : MeasurePreserving T volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ κ T hnorm
  have hTe : MeasurePreserving (T.trans e) volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ σ (T.trans e) fun v => by
      rw [hnorm v, ContinuousLinearEquiv.trans_apply, he]
  have hTs := MeasurePreserving.symm T.toHomeomorph.toMeasurableEquiv hT
  have hfun : (⇑e) = (T.trans e) ∘ T.toHomeomorph.toMeasurableEquiv.symm := by
    funext z
    simp
  rw [hfun]
  exact hTe.comp hTs

private theorem measurePreserving_piCurry_complex {I : Type} [Fintype I] {K : I → Type} [∀ i, Fintype (K i)] :
    MeasurePreserving (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) volume volume := by
  refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
  symm
  show Measure.pi (fun i : I => Measure.pi fun _ : K i => (volume : Measure ℂ)) = _
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.pi Set.univ '' Set.pi Set.univ fun _ : K i => {s : Set ℂ | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℂ).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hst using hs
  obtain rfl : s = fun i => Set.univ.pi (t i) := funext fun i => (hst i).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) ⁻¹'
      Set.univ.pi (fun i => Set.univ.pi (t i)) = Set.univ.pi fun p : (Σ i, K i) => t p.1 p.2 := by
    ext f
    simp [MeasurableEquiv.coe_piCurry, Sigma.forall]
    exact Iff.rfl
  rw [hpre, volume_pi, Measure.pi_pi, Fintype.prod_sigma]
  simp only [Measure.pi_pi]

attribute [local instance] haar_two haar_three

theorem covolume_pi_unitary : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  intro ι κ β _ _ _ r s Φ hΦ M hM L hL
  classical
  let Ψ : (ι → κ → ℂ) ≃ₗ[ℂ] (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun z b v => Φ v (z v) b
      invFun := fun w v => (Φ v).symm fun b => w b v
      map_add' := fun x y => by funext b v; simp
      map_smul' := fun c x => by funext b v; simp
      left_inv := fun z => by funext v; simp
      right_inv := fun w => by funext b v; simp }
  let F : ((Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)) → ℂ) ≃ₗ[ℂ]
      (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun w b v p q => w ⟨b, v, p, q⟩
      invFun := fun u x => u x.1 x.2.1 x.2.2.1 x.2.2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := LinearEquiv.piCurry ℂ fun (_ : ι) (_ : κ) => ℂ
  let E := G.trans (Ψ.trans F.symm)
  have hE : MeasurePreserving (E.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    apply measurePreserving_of_sum_sq
    intro z
    have hz : ∀ j : (Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)),
        (E.restrictScalars ℝ).toContinuousLinearEquiv z j =
          Φ j.2.1 (fun k => z ⟨j.2.1, k⟩) j.1 j.2.2.1 j.2.2.2 := fun j => rfl
    simp only [hz, Fintype.sum_sigma]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => hΦ v _
  have hG : MeasurePreserving (MeasurableEquiv.piCurry fun (_ : ι) (_ : κ) => ℂ) volume volume :=
    measurePreserving_piCurry_complex
  have hF : MeasurePreserving F volume volume := by
    have h := (volume_preserving_pi fun b => volume_preserving_pi fun (_ : ι) =>
        measurePreserving_piCurry_complex (I := Fin (r b)) (K := fun _ => Fin (s b))).comp
      ((volume_preserving_pi fun b =>
        measurePreserving_piCurry_complex (I := ι) (K := fun _ => Σ _ : Fin (r b), Fin (s b))).comp
        (measurePreserving_piCurry_complex (I := β) (K := fun b => Σ _ : ι, Σ _ : Fin (r b), Fin (s b))))
    exact h
  have hΨ : MeasurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    have h := hF.comp (hE.comp (MeasurePreserving.symm _ hG))
    convert h using 1
    funext z
    rfl
  have := haar_two ι κ
  have hB3 : ∀ b, (volume : Measure (ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure :=
    fun b => haar_three ι _ _
  have : (volume : Measure (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure := by
    rw [← hΨ.map_eq]; infer_instance
  show HasCov volume L _
  refine HasCov.of_measurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv hΨ
    (L' := Submodule.pi Set.univ M) ?_ ?_
  · intro z
    rw [hL, Submodule.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact Iff.rfl
  · exact hasCov_pi (μ := fun _ => volume) fun b => by
      obtain ⟨hd, hz⟩ := hM b
      exact ⟨hd, hz, rfl⟩

end GlobalTheory.CovPi
end
end
