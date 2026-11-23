module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.Normed.Operator.Extend
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

open Filter Topology

theorem exists_measurable_invariant_index {G : Type} [Group G] [MetricSpace G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G) (y : ℕ → G)
    (r : ℝ) (Q : ℕ → G → Prop) (hQm : ∀ n, MeasurableSet {x | Q n x})
    (hQi : ∀ n, ∀ l ∈ L, ∀ x, Q n (l * x) ↔ Q n x)
    (hex : ∀ x, ∃ n, (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x) :
    ∃ s : G → ℕ, Measurable s ∧ (∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < r) ∧
      (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧ ∀ x, Q (s x) x := by
  classical
  have hPm : ∀ n, MeasurableSet {x : G | (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x} := by
    intro n
    have hset : {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} =
        ⋃ l : L, {x : G | dist (y n) ((l : G) * x) < r} := by
      ext x; simp
    have hopen : IsOpen {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} := by
      rw [hset]
      exact isOpen_iUnion fun l =>
        isOpen_lt (continuous_const.dist (continuous_const.mul continuous_id)) continuous_const
    exact hopen.measurableSet.inter (hQm n)
  have hinv : ∀ l ∈ L, ∀ x n, ((∃ l' ∈ L, dist (y n) (l' * (l * x)) < r) ∧ Q n (l * x)) ↔
      ((∃ l' ∈ L, dist (y n) (l' * x) < r) ∧ Q n x) := by
    intro l hl x n
    refine and_congr ⟨?_, ?_⟩ (hQi n l hl x)
    · rintro ⟨m, hm, hd⟩
      exact ⟨m * l, L.mul_mem hm hl, by rwa [mul_assoc]⟩
    · rintro ⟨m, hm, hd⟩
      refine ⟨m * l⁻¹, L.mul_mem hm (L.inv_mem hl), ?_⟩
      simpa [mul_assoc] using hd
  refine ⟨fun x => Nat.find (hex x), measurable_find hex hPm, fun x => (Nat.find_spec (hex x)).1,
    fun l hl x => ?_, fun x => (Nat.find_spec (hex x)).2⟩
  exact le_antisymm (Nat.find_min' _ ((hinv l hl x _).2 (Nat.find_spec (hex x))))
    (Nat.find_min' _ ((hinv l hl x _).1 (Nat.find_spec (hex (l * x)))))

theorem exists_measurable_coset_section_metric {G : Type} [Group G] [MetricSpace G]
    [CompleteSpace G] [SecondCountableTopology G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : ℕ → G, DenseRange y := TopologicalSpace.exists_dense_seq G
  let S : ℕ → Type := fun k => {s : G → ℕ // Measurable s ∧ (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧
    ∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < (1 / 2 : ℝ) ^ k}
  have hy_meas : ∀ s : G → ℕ, Measurable s → Measurable (fun x => y (s x)) :=
    fun s hs => measurable_from_nat.comp hs

  have h0 : Nonempty (S 0) := by
    obtain ⟨s, hs, hclose, hinv, -⟩ := exists_measurable_invariant_index L y 1 (fun _ _ => True)
      (fun _ => MeasurableSet.univ) (fun _ _ _ _ => Iff.rfl) (fun x => by
        obtain ⟨n, hn⟩ := hy.exists_dist_lt x one_pos
        exact ⟨n, ⟨1, L.one_mem, by rw [one_mul, dist_comm]; exact hn⟩, trivial⟩)
    exact ⟨⟨s, hs, hinv, fun x => by simpa using hclose x⟩⟩

  have hstep : ∀ k (s : S k), ∃ s' : S (k + 1),
      ∀ x, dist (y (s'.1 x)) (y (s.1 x)) < 2 * (1 / 2 : ℝ) ^ k := by
    intro k s
    obtain ⟨s, hsm, hsi, hsc⟩ := s
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    have hhalf : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by ring
    obtain ⟨s', hs'm, hclose, hinv, hQ⟩ := exists_measurable_invariant_index L y ((1 / 2 : ℝ) ^ (k + 1))
      (fun n x => dist (y n) (y (s x)) < 2 * (1 / 2 : ℝ) ^ k)
      (fun n => measurableSet_lt (measurable_const.dist (hy_meas s hsm)) measurable_const)
      (fun n l hl x => by simp only [hsi l hl x])
      (fun x => by
        obtain ⟨l, hl, hd⟩ := hsc x
        obtain ⟨n, hn⟩ := hy.exists_dist_lt (l * x) hpos
        refine ⟨n, ⟨l, hl, by rw [dist_comm]; exact hn⟩, ?_⟩
        have hk : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
        calc dist (y n) (y (s x)) ≤ dist (y n) (l * x) + dist (l * x) (y (s x)) := dist_triangle _ _ _
          _ < 2 * (1 / 2 : ℝ) ^ k := by
            rw [hhalf] at hn
            have e1 := dist_comm (y n) (l * x)
            have e2 := dist_comm (l * x) (y (s x))
            linarith)
    exact ⟨⟨s', hs'm, hinv, hclose⟩, hQ⟩
  choose step hstep using hstep
  let seq : (k : ℕ) → S k := fun k => Nat.rec (motive := S) h0.some (fun k s => step k s) k
  let f : ℕ → G → G := fun k x => y ((seq k).1 x)
  have hf_succ : ∀ k x, dist (f k x) (f (k + 1) x) ≤ 2 * (1 / 2 : ℝ) ^ k := fun k x => by
    rw [dist_comm]; exact (hstep k (seq k) x).le
  have hcauchy : ∀ x, CauchySeq (fun k => f k x) := fun x =>
    cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num) (hf_succ · x)
  choose σ hσ using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun k => hy_meas _ (seq k).2.1) (tendsto_pi_nhds.2 hσ)
  · intro x
    have hC : IsClosed {z : G | z * x⁻¹ ∈ L} := hL.preimage (continuous_id.mul continuous_const)
    suffices h : σ x ∈ closure {z : G | z * x⁻¹ ∈ L} by rwa [hC.closure_eq] at h
    rw [Metric.mem_closure_iff]
    intro ε hε
    have h1 : ∀ᶠ k in atTop, dist (f k x) (σ x) < ε / 2 :=
      (hσ x).eventually (Metric.ball_mem_nhds _ (half_pos hε))
    have h2 : ∀ᶠ k in atTop, (1 / 2 : ℝ) ^ k < ε / 2 :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds (half_pos hε))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    obtain ⟨l, hl, hd⟩ := (seq k).2.2.2 x
    refine ⟨l * x, by simpa using hl, ?_⟩
    calc dist (σ x) (l * x) ≤ dist (σ x) (f k x) + dist (f k x) (l * x) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm] at hk1; change dist (f k x) (l * x) < _ at hd; linarith
  · intro l hl x
    have hfx : (fun k => f k (l * x)) = fun k => f k x := by
      funext k; simp only [f, (seq k).2.2.1 l hl x]
    have := hσ (l * x)
    rw [hfx] at this
    exact tendsto_nhds_unique this (hσ x)

theorem exists_measurable_coset_section (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable G
  exact exists_measurable_coset_section_metric L hL

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem lintegral_enorm_sq_Lp {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (f : Lp E 2 ν) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
    (Lp.aestronglyMeasurable f)
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem eLpNorm_two_le_of_lintegral {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (g : Q → E) (B : ℝ) (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm' g 2 ν ≤ ENNReal.ofReal B := by
  have e := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (f := g) (μ := ν) (q := 2) (by norm_num)
  simp only [ENNReal.rpow_ofNat] at e
  have e := e.symm
  rw [← e, ENNReal.ofReal_pow hB] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem extend_ae_linear_of_local_sq : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (D : Submodule ℂ H), Dense (D : Set H) → ∀ F : H → X → E,
    (∀ u ∈ D, ∀ u' ∈ D, F (u + u') =ᵐ[μ] fun x => F u x + F u' x) →
    (∀ (b : ℂ), ∀ u ∈ D, F (b • u) =ᵐ[μ] fun x => b • F u x) →
    (∀ n, ∃ C : ℝ, ∀ u ∈ D, AEStronglyMeasurable (F u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖F u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    ∃ T : H → X → E, (∀ u ∈ D, T u = F u) ∧
      (∀ u u' : H, T (u + u') =ᵐ[μ] fun x => T u x + T u' x) ∧
      (∀ (b : ℂ) (u : H), T (b • u) =ᵐ[μ] fun x => b • T u x) ∧
      (∀ n, ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (T u) (μ.restrict (K n)) ∧
        ∫⁻ x in K n, (‖T u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) := by
  intro X _ μ K hK hcov H _ _ E _ _ _ D hD F hadd hsmul hbd
  classical
  choose C hC using hbd
  set w : ℕ → ℝ := fun n => (2:ℝ)⁻¹ ^ n / (1 + max (C n) 0) with hw
  have hwpos : ∀ n, 0 < w n := fun n =>
    div_pos (pow_pos (by norm_num) n) (by have := le_max_right (C n) 0; linarith)
  have hw0 : ∀ n, ENNReal.ofReal (w n) ≠ 0 := fun n => by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hwpos n
  set ν : Measure X := Measure.sum (fun n => ENNReal.ofReal (w n) • μ.restrict (K n)) with hν
  have hint : ∀ f : X → ENNReal,
      ∫⁻ x, f x ∂ν = ∑' n, ENNReal.ofReal (w n) * ∫⁻ x in K n, f x ∂μ := by
    intro f
    rw [hν, lintegral_sum_measure]
    congr 1; funext n
    rw [lintegral_smul_measure, smul_eq_mul]
  have hνμ : ν ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul,
      measure_mono_null Set.inter_subset_left h0, mul_zero]
  have hμν : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [hν, Measure.sum_apply _ hs, ENNReal.tsum_eq_zero] at h0
    have h1 : ∀ n, μ (s ∩ K n) = 0 := fun n => by
      have := h0 n
      rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (hw0 n)
    have : s = ⋃ n, s ∩ K n := by rw [← Set.inter_iUnion, hcov, Set.inter_univ]
    rw [this]; exact measure_iUnion_null h1
  have hsq : ∀ u ∈ D, ∫⁻ x, ‖F u x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((Real.sqrt 2 * ‖u‖) ^ 2) := by
    intro u hu
    rw [hint]
    have hB : (Real.sqrt 2 * ‖u‖) ^ 2 = ∑' n : ℕ, (2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2 := by
      rw [tsum_mul_right, tsum_geometric_inv_two, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [hB, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    have h2 : ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C n * ‖u‖ ^ 2) := (hC n u hu).2
    have hM : 0 ≤ max (C n) 0 := le_max_right _ _
    calc ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖F u x‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (w n) * ENNReal.ofReal (max (C n) 0 * ‖u‖ ^ 2) := by
          gcongr
          exact h2.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
      _ = ENNReal.ofReal (w n * (max (C n) 0 * ‖u‖ ^ 2)) := (ENNReal.ofReal_mul (hwpos n).le).symm
      _ ≤ ENNReal.ofReal ((2:ℝ)⁻¹ ^ n * ‖u‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hw]
          simp only
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹) n) (sq_nonneg ‖u‖)]
  have hae : ∀ u ∈ D, AEStronglyMeasurable (F u) ν := fun u hu =>
    aestronglyMeasurable_sum_measure_iff.2 fun n => (hC n u hu).1.smul_measure _
  have hmem : ∀ u ∈ D, MemLp (F u) 2 ν := by
    intro u hu
    have hb : eLpNorm (F u) 2 ν ≤ ENNReal.ofReal (Real.sqrt 2 * ‖u‖) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (hae u hu)]
      exact eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u hu)
    exact hb.trans_lt ENNReal.ofReal_lt_top
  let L : D →ₗ[ℂ] Lp E 2 ν :=
    { toFun := fun u => (hmem u u.2).toLp (F u)
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hadd u u.2 v v.2))
      map_smul' := fun b u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hνμ.ae_le (hsmul b u u.2)) }
  have hL : ∀ u (hu : u ∈ D), L ⟨u, hu⟩ = (hmem u hu).toLp (F u) := fun _ _ => rfl
  have hLb : ∃ c, ∀ u : D, ‖L u‖ ≤ c * ‖D.subtype u‖ := by
    refine ⟨Real.sqrt 2, fun u => ?_⟩
    rw [show L u = (hmem u u.2).toLp (F u) from rfl, Lp.norm_toLp]
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (hae u u.2)]
    exact eLpNorm_two_le_of_lintegral ν _ _ (by positivity) (hsq u u.2)
  have hdense : DenseRange D.subtype := hD.denseRange_val
  set Ext : H →L[ℂ] Lp E 2 ν := L.extendOfNorm D.subtype with hExtdef
  have hExt : ∀ u (hu : u ∈ D), Ext u = (hmem u hu).toLp (F u) := fun u hu => by
    rw [← hL u hu]
    exact LinearMap.extendOfNorm_eq hdense hLb ⟨u, hu⟩
  let T : H → X → E := fun u => if u ∈ D then F u else ⇑(Ext u)
  have hTae : ∀ u, T u =ᵐ[ν] Ext u := by
    intro u
    by_cases hu : u ∈ D
    · simp only [T, if_pos hu]
      rw [hExt u hu]
      exact (MemLp.coeFn_toLp _).symm
    · simp only [T, if_neg hu]
      rfl
  have hres : ∀ n, μ.restrict (K n) ≪ ν := fun n =>
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hμν
  refine ⟨T, fun u hu => if_pos hu, fun u u' => ?_, fun b u => ?_, fun n => ?_⟩
  · refine hμν.ae_le ?_
    filter_upwards [hTae (u + u'), hTae u, hTae u', Lp.coeFn_add (Ext u) (Ext u')]
      with x h1 h2 h3 h4
    rw [h1, map_add (f := _), h4, Pi.add_apply, ← h2, ← h3]
  · refine hμν.ae_le ?_
    filter_upwards [hTae (b • u), hTae u, Lp.coeFn_smul b (Ext u)] with x h1 h2 h4
    rw [h1, map_smul, h4, Pi.smul_apply, ← h2]
  · refine ⟨‖Ext‖ ^ 2 / w n, fun u => ⟨?_, ?_⟩⟩
    · exact ((Lp.aestronglyMeasurable (Ext u)).congr (hTae u).symm).mono_ac (hres n)
    · have e1 : ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ = ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ :=
        lintegral_congr_ae ((hres n).ae_le ((hTae u).mono fun x hx => by simp only [hx]))
      have e2 : ENNReal.ofReal (w n) * ∫⁻ x in K n, ‖Ext u x‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) := by
        calc _ ≤ ∑' m, ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ :=
              ENNReal.le_tsum (f := fun m => ENNReal.ofReal (w m) * ∫⁻ x in K m, ‖Ext u x‖ₑ ^ 2 ∂μ) n
          _ = ∫⁻ x, ‖Ext u x‖ₑ ^ 2 ∂ν := (hint _).symm
          _ = ENNReal.ofReal (‖Ext u‖ ^ 2) := lintegral_enorm_sq_Lp ν _
          _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (Ext.le_opNorm u) 2
      have hd : ENNReal.ofReal (‖Ext‖ ^ 2 / w n * ‖u‖ ^ 2)
          = ENNReal.ofReal (‖Ext‖ ^ 2 * ‖u‖ ^ 2) / ENNReal.ofReal (w n) := by
        rw [← ENNReal.ofReal_div_of_pos (hwpos n)]
        congr 1; ring
      change ∫⁻ x in K n, ‖T u x‖ₑ ^ 2 ∂μ ≤ _
      rw [e1, hd, ENNReal.le_div_iff_mul_le (Or.inl (hw0 n)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact e2

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory.IndicatorSumEncard

theorem tsum_indicator_one_eq_encard {ι : Type} (A : Set ι) :
    ∑' i : ι, A.indicator (fun _ => (1 : ENNReal)) i = (A.encard : ENNReal) := by
  rw [← tsum_subtype A (fun _ => (1 : ENNReal))]
  exact ENNReal.tsum_set_one A

theorem setLIntegral_le_mul_of_encard_le {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [Measure.IsMulLeftInvariant μ] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G}
    (hD : IsFundamentalDomain (↥Γ) D μ) {f : G → ENNReal} (hf : AEMeasurable f μ)
    (hinv : ∀ᵐ (y : G) ∂μ, ∀ (γ : ↥Γ), f ((↑γ : G) * y) = f y) {S : Set G}
    (hS : MeasurableSet S) (N : ENNReal) (hN : N ≠ ⊤)
    (hcount : ∀ (z : G), (↑(Set.encard {γ : ↥Γ | (↑γ : G) * z ∈ S}) : ENNReal) ≤ N) :
    ∫⁻ (y : G) in S, f y ∂μ ≤ N * ∫⁻ (y : G) in D, f y ∂μ := by

  have key : ∀ x : G, ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) ≤ N := by
    intro x
    rw [← (Equiv.inv ↥Γ).tsum_eq (fun γ => S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x))]
    simp only [Equiv.inv_apply, inv_inv]
    calc ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ • x)
        = ∑' γ : ↥Γ, {γ : ↥Γ | (↑γ : G) * x ∈ S}.indicator (fun _ => (1 : ENNReal)) γ := by
          congr 1
      _ = _ := tsum_indicator_one_eq_encard _
      _ ≤ N := hcount x

  calc ∫⁻ y in S, f y ∂μ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator f (γ⁻¹ • x) ∂μ := by
        rw [← lintegral_indicator hS]
        exact hD.lintegral_eq_tsum' _
    _ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) * f x ∂μ := by
        congr 1
        ext γ
        refine lintegral_congr_ae ((ae_restrict_of_ae hinv).mono fun x hx => ?_)
        have h1 : f (γ⁻¹ • x) = f x := hx γ⁻¹
        dsimp only
        by_cases hm : γ⁻¹ • x ∈ S
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul, h1]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]
    _ = ∫⁻ x in D, (∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x)) * f x ∂μ := by
        rw [← lintegral_tsum]
        · congr 1
          ext x
          rw [ENNReal.tsum_mul_right]
        · intro γ
          exact (((measurable_const.indicator hS).comp (measurable_const_smul γ⁻¹)).aemeasurable).mul
            hf.restrict
    _ ≤ ∫⁻ x in D, N * f x ∂μ := lintegral_mono fun x => by gcongr; exact key x
    _ = N * ∫⁻ x in D, f x ∂μ := lintegral_const_mul' N _ hN

end GlobalTheory.IndicatorSumEncard
end

section

open MeasureTheory

namespace GlobalTheory


open MeasureTheory in
open scoped ENNReal in
open scoped Pointwise in
theorem _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one
    (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  let K := CompactExhaustion.choice G
  set a : ℕ → ℝ≥0∞ := fun n => ν (j ⁻¹' (K n * (K n)⁻¹)) with ha_def
  have ha : ∀ n, a n ≠ ∞ := fun n =>
    (hj.isCompact_preimage ((K.isCompact n).mul (K.isCompact n).inv)).measure_lt_top.ne
  set c : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ n / (a n + 1) with hc_def
  have hc_pos : ∀ n, c n ≠ 0 := fun n =>
    (ENNReal.div_pos (pow_ne_zero _ (by simp)) (by simp [ha n])).ne'
  have hc_le : ∀ n, c n ≤ 2⁻¹ ^ n := fun n =>
    ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' le_add_self)
  have hca : ∀ n, c n * a n ≤ 2⁻¹ ^ n := fun n => by
    calc c n * a n ≤ c n * (a n + 1) := by gcongr; exact le_self_add
      _ = 2⁻¹ ^ n := ENNReal.div_mul_cancel (by simp) (by simp [ha n])
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (K.isCompact n).isClosed.measurableSet
  set f : G → ℝ≥0∞ := fun y => ∑' n, (K n).indicator (fun _ => c n) y with hf_def
  have hf : Measurable f := Measurable.tsum fun n => measurable_const.indicator (hKm n)
  have hf_pos : ∀ y, f y ≠ 0 := by
    intro y
    obtain ⟨n, hn⟩ := K.exists_mem y
    refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (hc_pos n)) ?_)
    calc c n = (K n).indicator (fun _ => c n) y := (Set.indicator_of_mem hn (fun _ => c n)).symm
      _ ≤ f y := by
        change (K n).indicator (fun _ => c n) y ≤ ∑' i, (K i).indicator (fun _ => c i) y
        exact le_tsum (fun i => (K i).indicator (fun _ => c i) y) n
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  have hmeas : ∀ g, Measurable fun h => f (j h * g) := fun g => hf.comp (hjg g)
  set F : G → ℝ≥0∞ := fun g => ∫⁻ h, f (j h * g) ∂ν with hF_def
  have hF : Measurable F :=
    Measurable.lintegral_prod_right' (ν := ν) (f := fun p : G × H => f (j p.2 * p.1))
      (hf.comp ((hj.continuous.measurable.comp measurable_snd).mul measurable_fst))
  have hF_inv : ∀ h' g, F (j h' * g) = F g := by
    intro h' g
    have e : ∀ h, f (j h * (j h' * g)) = (fun k => f (j k * g)) (h * h') := by
      intro h; simp only [map_mul, mul_assoc]
    calc F (j h' * g) = ∫⁻ h, (fun k => f (j k * g)) (h * h') ∂ν := lintegral_congr e
      _ = F g := lintegral_mul_right_eq_self (μ := ν) (fun k => f (j k * g)) h'
  have hF0 : ∀ g, F g ≠ 0 := by
    intro g h0
    rw [hF_def, lintegral_eq_zero_iff (hmeas g), Filter.EventuallyEq, ae_iff] at h0
    have : ν Set.univ = 0 := by simpa [hf_pos] using h0
    exact NeZero.ne ν (Measure.measure_univ_eq_zero.1 this)
  have hFtop : ∀ g, F g ≠ ∞ := by
    intro g
    obtain ⟨m, hm⟩ := K.exists_mem g
    have hterm : ∀ n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
        ≤ (1 + a m) * 2⁻¹ ^ n := by
      intro n
      have hsub : (fun h => j h * g) ⁻¹' K n ⊆ j ⁻¹' (K (max n m) * (K (max n m))⁻¹) := by
        intro h hh
        have h1 : j h * g ∈ K (max n m) := K.subset (le_max_left n m) hh
        have h2 : g ∈ K (max n m) := K.subset (le_max_right n m) hm
        have e : j h = (j h * g) * g⁻¹ := by group
        rw [Set.mem_preimage, e]
        exact Set.mul_mem_mul h1 (Set.inv_mem_inv.2 h2)
      have hle : ν ((fun h => j h * g) ⁻¹' K n) ≤ a n + a m := by
        refine (measure_mono hsub).trans ?_
        rcases le_total n m with hnm | hnm
        · rw [max_eq_right hnm]; exact le_add_self
        · rw [max_eq_left hnm]; exact le_self_add
      calc ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
          = ∫⁻ h, ((fun h => j h * g) ⁻¹' K n).indicator (fun _ => c n) h ∂ν := rfl
        _ = c n * ν ((fun h => j h * g) ⁻¹' K n) :=
            lintegral_indicator_const (hjg g (hKm n)) _
        _ ≤ c n * (a n + a m) := by gcongr
        _ = c n * a n + c n * a m := mul_add _ _ _
        _ ≤ 2⁻¹ ^ n + 2⁻¹ ^ n * a m := by gcongr; exacts [hca n, hc_le n]
        _ = (1 + a m) * 2⁻¹ ^ n := by ring
    have hF_eq : F g = ∑' n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν :=
      lintegral_tsum fun n =>
        ((measurable_const.indicator (hKm n)).comp (hjg g)).aemeasurable
    rw [hF_eq]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (by simp [ha m]) (by simp)
  refine ⟨fun g => f g * (F g)⁻¹, hf.mul hF.inv, fun g => ?_⟩
  simp only [hF_inv]
  rw [lintegral_mul_const _ (hmeas g)]
  exact ENNReal.mul_inv_cancel (hF0 g) (hFtop g)

end GlobalTheory
end
