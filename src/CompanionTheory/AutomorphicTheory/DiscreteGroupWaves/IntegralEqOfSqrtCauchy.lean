module


import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.TypeStar
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section

namespace CompanionTheory.NFCpt

open MeasureTheory Filter Topology

theorem ae_coords_ne_zero (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ a, c a ≠ 0 := by
  rw [ae_all_iff]
  intro a
  have h : (volume : Measure (Fin n → ℂ)) {c | c a = 0} = 0 := Measure.pi_hyperplane _ a 0
  rw [ae_iff]
  simpa using h

theorem ae_ne_zero_c : ∀ᵐ t : ℂ, t ≠ 0 := by
  rw [ae_iff]
  simp

theorem tower_integral : ∀ (n : ℕ) (E : (j : ℕ) → (Fin j → ℂ) → ℝ),
    AEStronglyMeasurable (E n) volume → (∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c) →
    (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ a, c a ≠ 0) →
      Integrable (fun t : ℂ => E (j + 1) (Fin.snoc c t)) ∧ ∫ t : ℂ, E (j + 1) (Fin.snoc c t) = E j c) →
    Integrable (E n) ∧ ∫ c, E n c = E 0 (fun a => a.elim0)
  | 0, E, _, _, _ => by
    have e : E 0 = fun _ => E 0 (fun a => a.elim0) := funext fun c => congrArg _ (Subsingleton.elim _ _)
    refine ⟨by rw [e]; exact integrable_const _, ?_⟩
    rw [e, integral_const]
    simp [Measure.real, volume_pi]
  | n + 1, E, hm, h0, hs => by
    let e : (Fin (n + 1) → ℂ) ≃ᵐ (Fin n → ℂ) × ℂ :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last n)).trans MeasurableEquiv.prodComm
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n))
    have he : ∀ q : (Fin n → ℂ) × ℂ, e.symm q = Fin.snoc q.1 q.2 := by
      intro q
      apply e.injective
      rw [e.apply_symm_apply]
      simp [e, MeasurableEquiv.piFinSuccAbove]
      ext <;> rfl
    set G : (Fin n → ℂ) × ℂ → ℝ := fun q => E (n + 1) (Fin.snoc q.1 q.2) with hG
    have hGe : G = E (n + 1) ∘ e.symm := funext fun q => by simp [hG, he]
    have hGm : AEStronglyMeasurable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [hGe]
      exact hm.comp_measurePreserving (hmp.symm e)
    have hGpos : ∀ c : Fin n → ℂ, (∀ a, c a ≠ 0) → ∀ᵐ t : ℂ, 0 ≤ G (c, t) := by
      intro c hc
      filter_upwards [ae_ne_zero_c] with t ht
      refine h0 _ fun a => ?_
      induction a using Fin.lastCases with
      | last => simpa using ht
      | cast i => simpa using hc i
    have hae : (fun c : Fin n → ℂ => ∫ t, G (c, t)) =ᵐ[volume] E n := by
      filter_upwards [ae_coords_ne_zero n] with c hc
      exact (hs n (Nat.lt_succ_self n) c hc).2
    have hmn : AEStronglyMeasurable (E n) volume := hGm.integral_prod_right'.congr hae
    have h0n : ∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c := by
      intro c hc
      rw [← (hs n (Nat.lt_succ_self n) c hc).2]
      exact integral_nonneg_of_ae (hGpos c hc)
    have ih : Integrable (E n) ∧ ∫ c, E n c = E 0 (fun a => a.elim0) :=
      tower_integral n E hmn h0n fun j hj => hs j (Nat.lt_succ_of_lt hj)
    have hGI : Integrable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff hGm]
      refine ⟨?_, ?_⟩
      · filter_upwards [ae_coords_ne_zero n] with c hc
        exact (hs n (Nat.lt_succ_self n) c hc).1
      · refine (And.left ih).congr ?_
        filter_upwards [ae_coords_ne_zero n] with c hc
        rw [← (hs n (Nat.lt_succ_self n) c hc).2]
        refine integral_congr_ae ?_
        filter_upwards [hGpos c hc] with t ht
        exact (Real.norm_of_nonneg ht).symm
    refine ⟨?_, ?_⟩
    · have : E (n + 1) = G ∘ e := funext fun c => by simp [hGe]
      rw [this]
      exact (hmp.integrable_comp_emb e.measurableEmbedding).2 hGI
    · have h1 : ∫ c, E (n + 1) c = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
        have := hmp.integral_comp' G
        rw [← show ∫ q, G q = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) from rfl, ← this]
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        simp [hGe]
      rw [h1, integral_prod G hGI, integral_congr_ae hae, And.right ih]

theorem abs_sub_le_of_sqrt {a b d δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hδ : 0 < δ)
    (h : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt d) : |a - b| ≤ d / δ + δ * (a + b) := by
  set x := Real.sqrt a
  set y := Real.sqrt b
  set z := Real.sqrt d
  have hx : a = x ^ 2 := (Real.sq_sqrt ha).symm
  have hy : b = y ^ 2 := (Real.sq_sqrt hb).symm
  have hz : d = z ^ 2 := (Real.sq_sqrt hd).symm
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have e : |a - b| = |x - y| * (x + y) := by
    rw [hx, hy, show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, abs_of_nonneg (add_nonneg hx0 hy0)]
  rw [e, hx, hy, hz]
  have h1 : |x - y| * (x + y) ≤ z * (x + y) := mul_le_mul_of_nonneg_right h (add_nonneg hx0 hy0)
  refine h1.trans ?_
  rw [div_add' _ _ _ hδ.ne', le_div_iff₀ hδ]
  nlinarith [sq_nonneg (z - δ * x), sq_nonneg (z - δ * y), sq_nonneg (δ * x), sq_nonneg (δ * y), sq_nonneg z]

theorem integral_eq_of_sqrt_cauchy {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℕ → α → ℝ} {v : α → ℝ}
    {d : ℕ → ℕ → α → ℝ} {a : ℝ} (hq : ∀ n, Integrable (q n) μ) (hq0 : ∀ n x, 0 ≤ q n x)
    (hd : ∀ n m, Integrable (d n m) μ) (hd0 : ∀ n m x, 0 ≤ d n m x)
    (htri : ∀ n m x, |Real.sqrt (q n x) - Real.sqrt (q m x)| ≤ Real.sqrt (d n m x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (v x)))
    (ha : Tendsto (fun n => ∫ x, q n x ∂μ) atTop (𝓝 a))
    (hC : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → ∫ x, d n m x ∂μ ≤ η) :
    Integrable v μ ∧ ∫ x, v x ∂μ = a := by
  -- The integrals of q n are the squared L² norms of their square roots.
  let root (f : α → ℝ) : α → ℝ := fun x => Real.sqrt (f x)
  have root_mem {f : α → ℝ} (hf : Integrable f μ) (hf₀ : ∀ x, 0 ≤ f x) : MemLp (root f) 2 μ := by
    refine (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1)).2 ?_
    simpa only [root, Real.sq_sqrt (hf₀ _)] using hf
  have root_norm {f : α → ℝ} (hf : MemLp f 2 μ) :
      eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    simp only [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow, ← Real.rpow_natCast, Nat.cast_ofNat]
    congr 2
    · exact integral_congr_ae (ae_of_all _ fun x => by simp [sq_abs])
    · norm_num
  have hq₂ : ∀ n, MemLp (root (q n)) 2 μ := fun n => root_mem (hq n) (hq0 n)
  have hv := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hq n).1) hlim
  have hvroot := Real.continuous_sqrt.comp_aestronglyMeasurable hv
  have hsqrt : ∀ᵐ x ∂μ, Tendsto (fun n => root (q n) x) atTop (𝓝 (root v x)) :=
    hlim.mono fun x hx => (Real.continuous_sqrt.tendsto _).comp hx
  have htail : Tendsto (fun n => eLpNorm (root (q n) - root v) 2 μ) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
    have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
    obtain ⟨N, hN⟩ := hC ((r : ℝ) ^ 2) (sq_pos_of_pos hr')
    refine ⟨N, fun n hn => (Lp.eLpNorm_le_of_ae_tendsto
      (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
      (fun m => (hq₂ n).aestronglyMeasurable.sub (hq₂ m).aestronglyMeasurable)
      ((hq₂ n).aestronglyMeasurable.sub hvroot)
      (hsqrt.mono fun x hx => tendsto_const_nhds.sub hx)).trans hrε.le⟩
    have hd₂ := root_mem (hd n m) (hd0 n m)
    refine (eLpNorm_mono (g := root (d n m))
      ((hq₂ n).aestronglyMeasurable.sub (hq₂ m).aestronglyMeasurable) (fun x => ?_)).trans ?_
    · simpa [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), root] using htri n m x
    rw [root_norm hd₂]
    simp only [root, Real.sq_sqrt (hd0 n m _)]
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt (hN n m hn hm)).trans_eq (Real.sqrt_sq r.coe_nonneg))
  have hv₂ : MemLp (root v) 2 μ := Lp.memLp_of_cauchy_tendsto (by norm_num) hq₂ _ htail
  have hv_sq : (fun x => root v x ^ 2) =ᵐ[μ] v := hlim.mono fun x hx =>
    Real.sq_sqrt (ge_of_tendsto' hx fun n => hq0 n x)
  refine ⟨hv₂.integrable_sq.congr hv_sq, tendsto_nhds_unique ?_ ha⟩
  have hLp : Tendsto (fun n => (hq₂ n).toLp _) atTop (𝓝 (hv₂.toLp _)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => root (q n)) hq₂ (root v) hv₂).2 htail
  have norm_sq {f : α → ℝ} (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp, root_norm hf,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  simpa only [norm_sq, root, Real.sq_sqrt (hq0 _ _), integral_congr_ae hv_sq] using hLp.norm.pow 2

end CompanionTheory.NFCpt
