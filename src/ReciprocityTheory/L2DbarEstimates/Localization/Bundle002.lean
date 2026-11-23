module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem dens (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCut : CutoffStatement n M) (hUR : UnweightRelStatement n M)
    (hUB : UnweightBackStatement n M) (hLoc : LocalizeStatement n M)
    (hCh : ChartFlatStatement n M) : DensStatement n M := by
  intro z hz e ph ψ he hph hψ hcut f w σ hf hw hσ hadj hone
  refine hCut z hz e ph ψ he hph hψ hcut ?_ f w σ hf hw hσ hadj hone
  intro f w σ hf hw hσ hadj hone hcf hcw hcσ
  obtain ⟨hG, hD, hS, hdiv, hdbar, hcG, hcD, hcS⟩ :=
    hUR z hz ph ψ f w σ hph hψ hf hw hσ hadj hone
  refine hUB z hz ph ψ f w σ hph hψ hf hw hσ hcf hcw hcσ ?_
  exact hLoc z hz (fun e' G D S he' => hCh z hz e' G D S he') _ _ _ hG hD hS hdiv hdbar
    (hcG hcf) (hcD hcw) (hcS hcf hcσ)

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem extend_support_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (q : M)
    (hq : e.source.indicator (G ∘ e) q ≠ 0) : q ∈ e.symm '' tsupport G := by
  have hq' : q ∈ e.source := by
    by_contra h; exact hq (Set.indicator_of_notMem h _)
  rw [Set.indicator_of_mem hq'] at hq
  exact ⟨e q, subset_tsupport _ hq, e.left_inv hq'⟩

theorem extend_eventuallyEq {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (he : IsChart n z e)
    (he' : IsChart n z e') (y : V n) (hy : y ∈ e'.target) (hs : e'.symm y ∈ e.source) :
    (e.source.indicator (G ∘ e) ∘ e'.symm) =ᶠ[𝓝 y] G := by
  have hopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) :=
    e'.isOpen_inter_preimage_symm e.open_source
  filter_upwards [hopen.mem_nhds ⟨hy, hs⟩] with w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hw3 : e'.symm w ∈ e'.source := e'.map_target hw1
  rw [Function.comp_apply, Set.indicator_of_mem (show e'.symm w ∈ e.source from hw2), Function.comp_apply, ← he hw2, he' hw3,
    e'.right_inv hw1]

theorem extend (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ExtendStatement n M := by
  intro z _hz e G he hG hGc hGt
  have hK : IsCompact (e.symm '' tsupport G) :=
    hGc.image_of_continuousOn (e.continuousOn_symm.mono hGt)
  have hKs : e.symm '' tsupport G ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hGt hy)
  have hts : tsupport (e.source.indicator (G ∘ e)) ⊆ e.symm '' tsupport G :=
    closure_minimal (fun q hq => extend_support_subset e G q hq) hK.isClosed
  have hw : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → ∀ x ∈ e''.source, x ∈ e.source →
      (e.source.indicator (G ∘ e) ∘ e''.symm) =ᶠ[𝓝 (z x)] G ∧ z x = e x := by
    intro e'' h1 x h2 hx
    have hzx : z x = e'' x := h1 h2
    refine ⟨?_, he hx⟩
    rw [hzx]
    refine extend_eventuallyEq z e e'' G he h1 (e'' x) (e''.map_source h2) ?_
    rw [e''.left_inv h2]; exact hx
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKs, ?_⟩
  · intro e' he' y hy
    by_cases hs : e'.symm y ∈ e.source
    · exact (hG.contDiffAt.congr_of_eventuallyEq
        (extend_eventuallyEq z e e' G he he' y hy hs)).contDiffWithinAt
    · have hq : e'.symm y ∉ tsupport (e.source.indicator (G ∘ e)) := fun h => hs (hKs (hts h))
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hq
      have h0' := h0.comp_tendsto (e'.continuousAt_symm hy).tendsto
      exact (contDiffAt_const.congr_of_eventuallyEq h0').contDiffWithinAt
  · intro j x hx
    have key : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → x ∈ e''.source →
        wd n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wd n j G (e x) ∧
        wdb n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wdb n j G (e x) := by
      intro e'' h1 h2
      obtain ⟨hev, hzx⟩ := hw e'' h1 x h2 hx
      constructor
      · unfold wd; rw [hev.fderiv_eq, hzx]
      · unfold wdb; rw [hev.fderiv_eq, hzx]
    have hex : ∃ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' ∧ x ∈ e''.source := ⟨e, he, hx⟩
    constructor
    · simp only [d, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).1
    · simp only [db, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).2

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

namespace EulerCharacteristicLength

def prim (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0:ℝ)..t, f x

theorem prim_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (prim f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem prim_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (prim f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (prim_hasDerivAt hf.continuous t).differentiableAt, ?_⟩
  have : deriv (prim f) = f := funext fun t => (prim_hasDerivAt hf.continuous t).deriv
  rw [this]; exact hf

theorem prim_zero_of_nonpos {f : ℝ → ℝ} (hf : ∀ x, x ≤ 0 → f x = 0) {t : ℝ} (ht : t ≤ 0) :
    prim f t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
  · simp
  intro x hx
  rw [uIcc_of_ge ht] at hx
  exact hf x hx.2

theorem prim_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, x ≤ 0 → f x = 0) (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ prim f t := by
  rcases le_total t 0 with ht | ht
  · rw [prim_zero_of_nonpos hf0 ht]
  · exact intervalIntegral.integral_nonneg ht (fun x _ => hf x)

theorem prim_pos {f : ℝ → ℝ} (hc : Continuous f) (hf : ∀ x, 0 < x → 0 < f x) {t : ℝ}
    (ht : 0 < t) : 0 < prim f t :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
    (fun x hx => hf x hx.1) ht

def P : ℝ → ℝ := prim expNegInvGlue

def sig : ℝ → ℝ := prim P

theorem rho_contDiff : ContDiff ℝ ∞ expNegInvGlue := expNegInvGlue.contDiff
theorem primitive_contDiff₂ : ContDiff ℝ ∞ P := prim_contDiff rho_contDiff
theorem sig_contDiff : ContDiff ℝ ∞ sig := prim_contDiff primitive_contDiff₂
theorem primitive_hasDerivAt (t : ℝ) : HasDerivAt P (expNegInvGlue t) t :=
  prim_hasDerivAt rho_contDiff.continuous t
theorem sig_hasDerivAt (t : ℝ) : HasDerivAt sig (P t) t := prim_hasDerivAt primitive_contDiff₂.continuous t
theorem P_zero {t : ℝ} (ht : t ≤ 0) : P t = 0 :=
  prim_zero_of_nonpos (fun _ hx => expNegInvGlue.zero_of_nonpos hx) ht
theorem sig_zero {t : ℝ} (ht : t ≤ 0) : sig t = 0 := prim_zero_of_nonpos (fun _ hx => P_zero hx) ht
theorem P_nonneg (t : ℝ) : 0 ≤ P t :=
  prim_nonneg (fun _ hx => expNegInvGlue.zero_of_nonpos hx) expNegInvGlue.nonneg t
theorem sig_nonneg (t : ℝ) : 0 ≤ sig t := prim_nonneg (fun _ hx => P_zero hx) P_nonneg t
theorem twoPow_pos {t : ℝ} (ht : 0 < t) : 0 < P t :=
  prim_pos rho_contDiff.continuous (fun _ hx => expNegInvGlue.pos_of_pos hx) ht
theorem sig_pos {t : ℝ} (ht : 0 < t) : 0 < sig t :=
  prim_pos primitive_contDiff₂.continuous (fun _ hx => twoPow_pos hx) ht
theorem P_mono : Monotone P :=
  monotone_of_deriv_nonneg (fun t => (primitive_hasDerivAt t).differentiableAt)
    (fun t => by rw [(primitive_hasDerivAt t).deriv]; exact expNegInvGlue.nonneg t)
theorem sig_mono : Monotone sig :=
  monotone_of_deriv_nonneg (fun t => (sig_hasDerivAt t).differentiableAt)
    (fun t => by rw [(sig_hasDerivAt t).deriv]; exact P_nonneg t)

def Fs (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * sig (t - (a + k))
def Fs1 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * P (t - (a + k))
def Fs2 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, c k * expNegInvGlue (t - (a + k))

theorem Fs_hasDerivAt (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs c a m) (Fs1 c a m t) t := by
  unfold Fs Fs1
  apply HasDerivAt.fun_sum
  intro k _
  exact (HasDerivAt.comp_sub_const t (a + k) (sig_hasDerivAt _)).const_mul (c k)

theorem Fs1_hasDerivAt (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs1 c a m) (Fs2 c a m t) t := by
  unfold Fs1 Fs2
  apply HasDerivAt.fun_sum
  intro k _
  exact (HasDerivAt.comp_sub_const t (a + k) (primitive_hasDerivAt _)).const_mul (c k)

theorem Fs_contDiff (c : ℕ → ℝ) (a : ℝ) (m : ℕ) : ContDiff ℝ ∞ (Fs c a m) := by
  unfold Fs
  exact ContDiff.sum fun k _ => contDiff_const.mul (sig_contDiff.comp (contDiff_id.sub contDiff_const))

def chiF (c : ℕ → ℝ) (a : ℝ) (t : ℝ) : ℝ := ∑' k : ℕ, c k * sig (t - (a + k))

theorem chiF_eq {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) : chiF c a t = Fs c a m t := by
  unfold chiF Fs
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have : (m:ℝ) ≤ k := by exact_mod_cast hk
  rw [sig_zero (by linarith), mul_zero]

theorem chiF_eventuallyEq {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    chiF c a =ᶠ[𝓝 t] Fs c a m :=
  Filter.mem_of_superset (isOpen_Iio.mem_nhds ht) fun _ hs => chiF_eq hs

theorem deriv_chiF {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    deriv (chiF c a) t = Fs1 c a m t := by
  rw [(chiF_eventuallyEq ht).deriv_eq, (Fs_hasDerivAt c a m t).deriv]

theorem deriv2_chiF {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    deriv (deriv (chiF c a)) t = Fs2 c a m t := by
  have h : deriv (chiF c a) =ᶠ[𝓝 t] Fs1 c a m :=
    Filter.mem_of_superset (isOpen_Iio.mem_nhds ht) fun _ hs => deriv_chiF hs
  rw [h.deriv_eq, (Fs1_hasDerivAt c a m t).deriv]

theorem exists_m (a t : ℝ) : ∃ m : ℕ, t < a + m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (t - a)
  exact ⟨m, by linarith⟩

theorem chiF_contDiff (c : ℕ → ℝ) (a : ℝ) : ContDiff ℝ ∞ (chiF c a) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  obtain ⟨m, hm⟩ := exists_m a t
  exact (Fs_contDiff c a m).contDiffAt.congr_of_eventuallyEq (chiF_eventuallyEq hm)

end EulerCharacteristicLength

open EulerCharacteristicLength in
theorem chi : ChiStatement := by
  intro a R hR
  choose B hB using hR
  have hμpos : 0 < min (sig 1) (P 1) := lt_min (sig_pos one_pos) (twoPow_pos one_pos)
  set μ := min (sig 1) (P 1) with hμ
  set c : ℕ → ℝ := fun k => max 0 (B (a + k + 2)) / μ with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => div_nonneg (le_max_left _ _) hμpos.le
  refine ⟨chiF c a, chiF_contDiff c a, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h0 : ∀ k : ℕ, c k * sig (t - (a + k)) = 0 := fun k => by
      have := k.cast_nonneg (α := ℝ)
      rw [sig_zero (by linarith), mul_zero]
    simp only [chiF, h0, tsum_zero]
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [chiF_eq hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (sig_nonneg _)
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [deriv_chiF hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (P_nonneg _)
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [deriv2_chiF hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (expNegInvGlue.nonneg _)
  · intro t ht
    set k := ⌊t - a - 1⌋₊ with hk
    have hk1 : (k:ℝ) ≤ t - a - 1 := Nat.floor_le (by linarith)
    have hk2 : t - a - 1 < k + 1 := Nat.lt_floor_add_one _
    have hm : t < a + ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hkm : k ∈ Finset.range (k + 2) := Finset.mem_range.2 (by omega)
    have hRB : R t ≤ B (a + k + 2) := hB (a + k + 2) ⟨t, by simp only [mem_Iic]; linarith, rfl⟩
    have hcμ : c k * μ = max 0 (B (a + k + 2)) := by
      simp only [hcdef]; field_simp
    have hs1 : 1 ≤ t - (a + k) := by linarith
    have hbase : R t ≤ c k * μ := by rw [hcμ]; exact hRB.trans (le_max_right _ _)
    constructor
    · rw [chiF_eq hm]
      refine hbase.trans ((mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (sig_mono hs1))
        (hc0 k)).trans ?_)
      exact Finset.single_le_sum (f := fun k => c k * sig (t - (a + k)))
        (fun i _ => mul_nonneg (hc0 i) (sig_nonneg _)) hkm
    · rw [deriv_chiF hm]
      refine hbase.trans ((mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (P_mono hs1))
        (hc0 k)).trans ?_)
      exact Finset.single_le_sum (f := fun k => c k * P (t - (a + k)))
        (fun i _ => mul_nonneg (hc0 i) (P_nonneg _)) hkm

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem multA_integrable_of_sq {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (F : α → ℂ) (hF : AEStronglyMeasurable F ν) (h : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ⊤) :
    Integrable F ν := by
  have h2 : MemLp F 2 ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      two_ne_zero ENNReal.ofNat_ne_top hF]
    simpa using h
  exact h2.integrable one_le_two

theorem integrableOn_compact_of_locL2 {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasureOnCompacts μ] (u : M → ℂ) (hu : LocalL2Isometry μ u)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  unfold LocalL2Isometry at hu
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact multA_integrable_of_sq (μ.restrict K) u hu.1.restrict (hu.2 K hK)

private lemma localL2Isometry_comp_of_norm_le {M E F : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure M) (f : M → E) (g : E → F)
    (hg : Continuous g) (hb : ∀ e, ‖g e‖ ≤ ‖e‖) (hf : LocalL2Isometry μ f) :
    LocalL2Isometry μ (fun x => g (f x)) := by
  unfold LocalL2Isometry at hf ⊢
  refine ⟨hg.comp_aestronglyMeasurable hf.1, fun C hC => lt_of_le_of_lt ?_ (hf.2 C hC)⟩
  refine lintegral_mono fun x => ?_
  gcongr
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (hb _)

theorem locL2_form_component {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (f : M → V n) (hf : LocalL2Isometry μ f) (j : Fin n) :
    LocalL2Isometry μ (fun x => f x j) := by
  refine localL2Isometry_comp_of_norm_le μ f (fun v : V n => v j) (EuclideanSpace.proj (𝕜 := ℂ) j).continuous ?_ hf
  intro v
  rw [EuclideanSpace.norm_eq]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)))

theorem locL2_two_form_component {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (σ : M → Fin n → Fin n → ℂ) (hσ : LocalL2Isometry μ σ) (j k : Fin n) :
    LocalL2Isometry μ (fun x => σ x j k) := by
  refine localL2Isometry_comp_of_norm_le μ σ (fun s : Fin n → Fin n → ℂ => s j k)
    ((continuous_apply k).comp (continuous_apply j)) ?_ hσ
  intro s
  exact (norm_le_pi_norm (s j) k).trans (norm_le_pi_norm s j)

theorem multA_intOn_w {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (u : M → ℂ) (ph : M → ℝ) (hph : Continuous ph) (hu : AEStronglyMeasurable u μ)
    (h : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ < ⊤)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hph.continuousOn
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine multA_integrable_of_sq (μ.restrict K) u hu.restrict ?_
  have hpt : ∀ x ∈ K, ‖u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) := by
    intro x hx
    have hx' : ph x ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x hx)
    have h1 : 1 ≤ Real.exp C * Real.exp (-ph x) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_pos C).le]
    apply ENNReal.ofReal_le_ofReal
    calc ‖u x‖ ^ 2 = ‖u x‖ ^ 2 * 1 := by ring
      _ ≤ ‖u x‖ ^ 2 * (Real.exp C * Real.exp (-ph x)) := by gcongr
      _ = Real.exp C * (‖u x‖ ^ 2 * Real.exp (-ph x)) := by ring
  calc ∫⁻ x in K, ‖u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in K, ENNReal.ofReal (Real.exp C) *
          ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        setLIntegral_mono_ae' hK.measurableSet (Eventually.of_forall hpt)
    _ = ENNReal.ofReal (Real.exp C) *
          ∫⁻ x in K, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp C) *
          ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ := by
        gcongr; exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem multA_int_mul {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) (u c : M → ℂ)
    (hu : ∀ K, IsCompact K → IntegrableOn u K μ) (hc : Continuous c) (hcs : HasCompactSupport c) :
    Integrable (fun x => u x * c x) μ := by
  have h1 : IntegrableOn (fun x => u x * c x) (tsupport c) μ :=
    (hu _ hcs).mul_continuousOn hc.continuousOn hcs
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport c))).mp h1

theorem multA_contR {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, hze⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [hze]
  have hg := (hph e hc).continuousOn
  have h1 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x :=
    (hg.continuousAt (e.open_target.mem_nhds (e.map_source hx))).comp (e.continuousAt hx)
  have h2 : ((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e =ᶠ[𝓝 x] fun y => (ph y : ℂ) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  have h3 := Complex.continuous_re.continuousAt.comp (h1.congr h2)
  simpa [Function.comp_def] using h3

end

end ReciprocityTheory.L2DbarEstimates.F
end
