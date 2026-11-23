module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.SchurTotal

open Filter Topology

theorem span_ext {G H : Type} [MeasurableSpace G] (μ : Measure G) [AddCommGroup H] [Module ℂ H]
    (S : Set H) (f : H → G → ℂ) (r : H → ℂ) (φ : ℂ → ℂ)
    (hf0 : ∀ g, f 0 g = 0) (hr0 : r 0 = 0)
    (hfa : ∀ a b g, f (a + b) g = f a g + f b g) (hra : ∀ a b, r (a + b) = r a + r b)
    (hfs : ∀ (c : ℂ) a g, f (c • a) g = φ c * f a g) (hrs : ∀ (c : ℂ) a, r (c • a) = φ c * r a)
    (h : ∀ v ∈ S, Integrable (f v) μ ∧ ∫ g, f v g ∂μ = r v) :
    ∀ v ∈ Submodule.span ℂ S, Integrable (f v) μ ∧ ∫ g, f v g ∂μ = r v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have : f 0 = fun _ => 0 := funext hf0
    rw [this, hr0]
    exact ⟨integrable_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
    have : f (x + y) = fun g => f x g + f y g := funext (hfa x y)
    rw [this, hra]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2]⟩
  | smul c x _ hx =>
    have : f (c • x) = fun g => φ c * f x g := funext (hfs c x)
    rw [this, hrs]
    exact ⟨hx.1.const_mul _, by rw [integral_const_mul, hx.2]⟩

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (σ : G → (H →L[ℂ] H)) (d : ℝ)

def Rel (v w v' w' : H) : Prop :=
  Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

theorem rel_span (S : Set H) (h : ∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ S, Rel μ σ d v w v' w') :
    ∀ v ∈ Submodule.span ℂ S, ∀ w ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      ∀ w' ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
  have h1 : ∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
    intro v hv w hw v' hv'
    refine span_ext μ S (fun w' g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun w' => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => c) ?_ ?_ ?_ ?_ ?_ ?_ (h v hv w hw v' hv')
    · intro g; simp
    · simp
    · intro a b g; simp only [inner_add_left, star_add]; ring
    · intro a b; simp only [inner_add_right]; ring
    · intro c a g; simp only [inner_smul_left, star_mul', RCLike.star_def, Complex.conj_conj]; ring
    · intro c a; simp only [inner_smul_right]; ring
  have h2 : ∀ v ∈ S, ∀ w ∈ S, ∀ w' ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      Rel μ σ d v w v' w' := by
    intro v hv w hw w' hw'
    refine span_ext μ S (fun v' g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun v' => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => star c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun v' hv' => h1 v hv w hw v' hv' w' hw')
    · intro g; simp
    · simp
    · intro a b g; simp only [map_add (f := _), inner_add_right, star_add]; ring
    · intro a b; simp only [inner_add_left]; ring
    · intro c a g; simp only [map_smul, inner_smul_right, star_mul']; ring
    · intro c a; simp only [inner_smul_left, RCLike.star_def]; ring
  have h3 : ∀ v ∈ S, ∀ w' ∈ Submodule.span ℂ S, ∀ v' ∈ Submodule.span ℂ S,
      ∀ w ∈ Submodule.span ℂ S, Rel μ σ d v w v' w' := by
    intro v hv w' hw' v' hv'
    refine span_ext μ S (fun w g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun w => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => star c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun w hw => h2 v hv w hw w' hw' v' hv')
    · intro g; simp
    · simp
    · intro a b g; simp only [inner_add_left]; ring
    · intro a b; simp only [inner_add_left]; ring
    · intro c a g; simp only [inner_smul_left, RCLike.star_def]; ring
    · intro c a; simp only [inner_smul_left, RCLike.star_def]; ring
  intro v hv w hw v' hv' w' hw'
  revert v
  refine span_ext μ S (fun v g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ)
      (fun v => ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) (fun c => c) ?_ ?_ ?_ ?_ ?_ ?_
      (fun v hv => h3 v hv w' hw' v' hv' w hw)
  · intro g; simp
  · simp
  · intro a b g; simp only [map_add (f := _), inner_add_right]; ring
  · intro a b; simp only [inner_add_right]; ring
  · intro c a g; simp only [map_smul, inner_smul_right]; ring
  · intro c a; simp only [inner_smul_right]; ring

theorem mul_star_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem lint_of_rel (v w : H) (h : Rel μ σ d v w v w) :
    ∫⁻ g, ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) ∂μ = ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨h1, h2⟩ := h
  simp only [mul_star_eq] at h1 h2
  have h3 : Integrable (fun g => ‖⟪w, σ g v⟫_ℂ‖ ^ 2) μ := by
    have := h1.re
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using this
  rw [← ofReal_integral_eq_lintegral_ofReal h3 (ae_of_all _ fun g => by positivity)]
  congr 1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  apply Complex.ofReal_injective
  rw [h2]; push_cast; rfl

theorem lint_le (T : Set H) (hT : Dense T) (hm : ∀ v w : H, Measurable fun g => ⟪w, σ g v⟫_ℂ)
    (h : ∀ v ∈ T, ∀ w ∈ T, Rel μ σ d v w v w) (v w : H) :
    ∫⁻ g, ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) ∂μ ≤ ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨a, ha, hav⟩ := mem_closure_iff_seq_limit.1 (hT v)
  obtain ⟨b, hb, hbw⟩ := mem_closure_iff_seq_limit.1 (hT w)
  have h1 := lintegral_liminf_le (μ := μ) (u := atTop)
    (f := fun (n : ℕ) g => ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2))
    (fun n => ((hm (a n) (b n)).norm.pow_const 2).ennreal_ofReal)
  have h2 : ∀ g, liminf (fun n => ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2)) atTop
      = ENNReal.ofReal (‖⟪w, σ g v⟫_ℂ‖ ^ 2) := by
    intro g
    apply Tendsto.liminf_eq
    exact ENNReal.tendsto_ofReal
      ((hbw.inner (((σ g).continuous.tendsto v).comp hav)).norm.pow 2)
  have h3 : liminf (fun n => ∫⁻ g, ENNReal.ofReal (‖⟪b n, σ g (a n)⟫_ℂ‖ ^ 2) ∂μ) atTop
      = ENNReal.ofReal (‖v‖ ^ 2 * ‖w‖ ^ 2 / d) := by
    apply Tendsto.liminf_eq
    simp only [fun n => lint_of_rel μ σ d (a n) (b n) (h _ (ha n) _ (hb n))]
    exact ENNReal.tendsto_ofReal (((hav.norm.pow 2).mul (hbw.norm.pow 2)).div_const d)
  simpa only [h2, h3] using h1

theorem inner_toLp {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hg.toLp g, hf.toLp f⟫_ℂ = ∫ x, f x * star (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]; simp

theorem rel_dense (hd : 0 < d) (T : Set H) (hT : Dense T)
    (hm : ∀ v w : H, Measurable fun g => ⟪w, σ g v⟫_ℂ)
    (h : ∀ v ∈ T, ∀ w ∈ T, ∀ v' ∈ T, ∀ w' ∈ T, Rel μ σ d v w v' w') (v w v' w' : H) :
    Rel μ σ d v w v' w' := by
  have hle := lint_le μ σ d T hT hm (fun v hv w hw => h v hv w hw v hv w hw)
  have hint : ∀ v w : H, Integrable (fun g => ‖⟪w, σ g v⟫_ℂ‖ ^ 2) μ := by
    intro v w
    refine ⟨((hm v w).norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => by positivity)]
    exact (hle v w).trans_lt ENNReal.ofReal_lt_top
  have hL : ∀ v w : H, MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 μ := fun v w =>
    (memLp_two_iff_integrable_sq_norm (hm v w).aestronglyMeasurable).2 (hint v w)
  let C : H → H → Lp ℂ 2 μ := fun v w => (hL v w).toLp _
  have hC : ∀ v w, ‖C v w‖ ≤ ‖v‖ * ‖w‖ / √d := by
    intro v w
    have e1 : ((‖C v w‖ ^ 2 : ℝ) : ℂ) = ((∫ g, ‖⟪w, σ g v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      have := inner_toLp μ (hL v w) (hL v w)
      simp only [mul_star_eq] at this
      rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at this
      rw [← this]; push_cast; rfl
    have e2 := Complex.ofReal_injective e1
    have e3 : ∫ g, ‖⟪w, σ g v⟫_ℂ‖ ^ 2 ∂μ ≤ ‖v‖ ^ 2 * ‖w‖ ^ 2 / d := by
      have := hle v w
      rw [← ofReal_integral_eq_lintegral_ofReal (hint v w) (ae_of_all _ fun g => by positivity)] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    apply le_of_sq_le_sq _ (by positivity)
    rw [e2, div_pow, mul_pow, Real.sq_sqrt hd.le]
    exact e3
  have hsplit : ∀ v w v0 w0, C v w - C v0 w0 = C (v - v0) w + C v0 (w - w0) := by
    intro v w v0 w0
    simp only [C]
    rw [← MemLp.toLp_sub, ← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine ae_of_all _ fun g => ?_
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, inner_sub_left, inner_sub_right]
    ring
  have hcont : Continuous fun p : H × H => C p.1 p.2 := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hc : Continuous fun q : H × H =>
        ‖q.1 - p.1‖ * ‖q.2‖ / √d + ‖p.1‖ * ‖q.2 - p.2‖ / √d := by fun_prop
    have ht := hc.tendsto p
    simp only [sub_self, norm_zero, zero_mul, mul_zero, zero_div, add_zero] at ht
    refine squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) ht
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hC _ _) (hC _ _))
  refine ⟨?_, ?_⟩
  · exact (hL v w).integrable_mul (hL v' w').star
  · have key : ∀ x : (H × H) × (H × H), ⟪C x.2.1 x.2.2, C x.1.1 x.1.2⟫_ℂ
        = ⟪x.2.1, x.1.1⟫_ℂ * ⟪x.1.2, x.2.2⟫_ℂ / (d : ℂ) := by
      have hD : Dense ((T ×ˢ T) ×ˢ (T ×ˢ T)) := (hT.prod hT).prod (hT.prod hT)
      have := Continuous.ext_on hD
        (f := fun x : (H × H) × (H × H) => ⟪C x.2.1 x.2.2, C x.1.1 x.1.2⟫_ℂ)
        (g := fun x => ⟪x.2.1, x.1.1⟫_ℂ * ⟪x.1.2, x.2.2⟫_ℂ / (d : ℂ))
        ((hcont.comp continuous_snd).inner (hcont.comp continuous_fst))
        (by fun_prop) (by
          rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
          exact (inner_toLp μ (hL a b) (hL a' b')).trans (h a ha b hb a' ha' b' hb').2)
      exact congrFun this
    exact (inner_toLp μ (hL v w) (hL v' w')).symm.trans (key ((v, w), (v', w')))

end GlobalTheory.Dec.SchurTotal

theorem GlobalTheory.Dec.isFdegG_of_total : ∀ (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : G → (H →L[ℂ] H)) (d : ℝ) (S : Set H), IsURep σ → 0 < d → Dense (Submodule.span ℂ S : Set H) → (∀ v ∈ S, ∀ w ∈ S, ∀ v' ∈ S, ∀ w' ∈ S, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧ ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) → IsFdegG μ σ d := by
  intro G _ _ _ _ μ H _ _ σ d S hσ hd hS h
  refine ⟨hd, fun v w v' w' => ?_⟩
  exact GlobalTheory.Dec.SchurTotal.rel_dense μ σ d hd _ hS
    (fun v w => (continuous_const.inner (hσ.2.2.2 v)).measurable)
    (GlobalTheory.Dec.SchurTotal.rel_span μ σ d S h) v w v' w'
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ExtContRep

theorem comp_rep_ae_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Set G) (hΓ : Γ.Countable) (D : Set G) (hD : MeasurableSet D)
    (r : G → G) (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ r y ∈ D) (F f : G → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (h : F =ᵐ[μ.restrict D] f) :
    (fun y => F (r y)) =ᵐ[μ] f := by
  have h1 : ∀ᵐ x ∂μ, x ∈ D → F x = f x := (ae_restrict_iff' hD).1 h
  have h2 : ∀ᵐ x ∂μ, ∀ γ ∈ Γ, γ * x ∈ D → F (γ * x) = f (γ * x) :=
    (ae_ball_iff hΓ).2 fun γ _ => (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with x hx
  obtain ⟨γ, hγ, e, hm⟩ := hr x
  rw [e] at hm ⊢
  rw [hx γ hγ hm, hf γ hγ]

theorem ae_ae_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [SFinite μ] [SFinite ν] (p : G → Prop) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, p (m * x) := by
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have h0 : ∀ᵐ x ∂μ, x ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZ0
  have hm : MeasurableSet {z : G × G | z.2 * z.1 ∉ Z} :=
    (measurable_snd.mul measurable_fst) hZm.compl
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, m * x ∉ Z :=
    (Measure.ae_ae_comm (p := fun x m => m * x ∉ Z) hm).2
      (Filter.Eventually.of_forall fun m =>
        (measurePreserving_mul_left μ m).quasiMeasurePreserving.ae h0)
  filter_upwards [h1] with x hx
  filter_upwards [hx] with m hmx
  by_contra hp
  exact hmx (hZ hp)

theorem ext_ae_eq_contRep : ∀ (B : RowsAut) (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B y f → B.I.ext y =ᵐ[B.I.muA B.μf] f ∧ (∀ f', IsContRep B y f' → f' = f) ∧ (∀ g, IsContRep B (B.R g y) (fun x => f (x * g))) ∧ ∀ ν : Measure B.I.GA, IsFiniteMeasure ν → ∀ᵐ x ∂(B.I.muA B.μf), ∀ᵐ m ∂ν, B.I.ext y (m * x) = f (m * x) := by
  intro B y f hf
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨Γ, hΓ, hc, -, -⟩ := GlobalTheory.RatDiscrete.rational_points B.I
  obtain ⟨hl, hrt, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : (B.I.muA B.μf).IsMulRightInvariant := ⟨hrt⟩
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  have : SFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hcount : B.I.GFset.Countable := by
    rw [← hΓ]; exact Set.countable_coe_iff.1 hc
  have hr : ∀ z, ∃ γ ∈ B.I.GFset, B.I.rep B.fund z = γ * z ∧ B.I.rep B.fund z ∈ B.fund := by
    intro z
    have h := B.fund_spec.2.1 z
    have e : B.I.rep B.fund z = h.choose * z := by
      unfold AutInst.rep; exact dif_pos h
    exact ⟨h.choose, h.choose_spec.1, e, e ▸ h.choose_spec.2⟩
  have key : ∀ f', IsContRep B y f' → B.I.ext y =ᵐ[B.I.muA B.μf] f' := fun f' hf' =>
    comp_rep_ae_eq (B.I.muA B.μf) _ hcount _ B.fund_spec.1 _ hr _ f' hf'.2.1 hf'.2.2
  refine ⟨key f hf, fun f' hf' => ?_, fun g => ⟨?_, ?_, ?_⟩, fun ν hν => ?_⟩
  · exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hf'.1 hf.1).1 ((key f' hf').symm.trans (key f hf))
  · exact hf.1.comp (continuous_id.mul continuous_const)
  · intro γ hγ x
    simp only [mul_assoc]
    exact hf.2.1 γ hγ _
  · refine (B.R_spec g y).trans (ae_restrict_of_ae ?_)
    exact (measurePreserving_mul_right (B.I.muA B.μf) g).quasiMeasurePreserving.ae (key f hf)
  · exact ae_ae_mul (B.I.muA B.μf) ν (fun x => B.I.ext y x = f x) (key f hf)

end GlobalTheory.ExtContRep
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.HilbTensorUnitary

open GlobalTheory.HilbTensorRep

theorem isURep_tensor {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {tens : (∀ i, H i) → Hs} {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    {π : ∀ i, G i →* (H i →L[ℂ] H i)} {σs : (∀ i, G i) → (Hs →L[ℂ] Hs)}
    (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs))
    (hs : ∀ g x, σs g (tens x) = tens fun i => π i (g i) (x i))
    (hn : ∀ i g a, ‖π i g a‖ = ‖a‖) (hc : ∀ i a, Continuous fun g => π i g a) :
    IsURep σs := by
  classical
  have h1 : σs 1 = 1 := by
    apply ext_op hd
    intro x
    rw [hs]
    simp
  have hmul : ∀ a b, σs (a * b) = (σs a).comp (σs b) := by
    intro a b
    apply ext_op hd
    intro x
    rw [ContinuousLinearMap.comp_apply, hs, hs, hs]
    simp [Pi.mul_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hnorm : ∀ g u, ‖σs g u‖ = ‖u‖ := by
    intro g u
    have key : ⟪σs g u, σs g u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [← inner_inv hi hd hs hn g (σs g u) u, ← ContinuousLinearMap.comp_apply, ← hmul,
        inv_mul_cancel, h1, ContinuousLinearMap.one_apply]
    have h2 : ‖σs g u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), key]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  let S : Submodule ℂ Hs :=
    { carrier := {u | Continuous fun g => σs g u}
      add_mem' := fun {a b} ha hb => by
        show Continuous fun g => σs g (a + b)
        simp only [map_add (f := _)]
        exact ha.add hb
      zero_mem' := by
        show Continuous fun g => σs g 0
        simp only [map_zero]
        exact continuous_const
      smul_mem' := fun c a ha => by
        show Continuous fun g => σs g (c • a)
        simp only [map_smul]
        exact ha.const_smul c }
  have hmemS : ∀ u, u ∈ S ↔ Continuous fun g => σs g u := fun u => Iff.rfl
  have htens : ∀ x, tens x ∈ S := by
    intro x
    rw [hmemS]
    have e : (fun g => σs g (tens x)) = fun g => tens fun i => π i (g i) (x i) := by
      funext g
      exact hs g x
    rw [e]
    exact (continuous_tens hi).comp (continuous_pi fun i => (hc i (x i)).comp (continuous_apply i))
  have hclosed : IsClosed (S : Set Hs) := by
    apply isClosed_of_closure_subset
    intro u hu
    show Continuous fun g => σs g u
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hub⟩ := Metric.mem_closure_iff.1 hu (ε / 3) (by positivity)
    have hbc : Continuous fun g => σs g b := hb
    filter_upwards [Metric.tendsto_nhds.1 hbc.continuousAt (ε / 3) (by positivity)] with g hg
    have d1 : dist (σs g u) (σs g b) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm]
    have d2 : dist (σs g0 b) (σs g0 u) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm, dist_comm]
    calc dist (σs g u) (σs g0 u)
        ≤ dist (σs g u) (σs g b) + dist (σs g b) (σs g0 b) + dist (σs g0 b) (σs g0 u) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [d1, d2]; linarith
      _ = ε := by ring
  have hall : ∀ u, u ∈ S := by
    intro u
    have hle : (Submodule.span ℂ (Set.range tens) : Set Hs) ⊆ S :=
      Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact htens x)
    have hcl := closure_minimal hle hclosed
    rw [hd.closure_eq] at hcl
    exact hcl (Set.mem_univ u)
  exact ⟨h1, hmul, hnorm, fun u => hall u⟩

theorem isURep_rows :
    ∀ B : RowsAut, (∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) → IsURep B.σs := by
  intro B hB
  have hmem : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), uMat g ∈ UJset (B.I.ε v) := fun v g => g.2
  have hcu : ∀ v, Continuous fun g : Formalism.REAL.UJ (B.I.ε v) => uMat g :=
    fun v => Units.continuous_val.comp continuous_subtype_val
  exact isURep_tensor (H := B.H) (tens := B.tens)
    (π := fun v =>
      { toFun := fun g => B.σ v (uMat g)
        map_one' := (hB v).1.1
        map_mul' := fun a b => (hB v).1.2 _ (hmem v a) _ (hmem v b) })
    B.tens_spec.1 B.tens_spec.2.2 (fun g x => B.tens_spec.2.1 g x)
    (fun v g a => (hB v).2.1 _ (hmem v g) a)
    (fun v a => ((hB v).2.2 a).comp_continuous (hcu v) (hmem v))

end GlobalTheory.HilbTensorUnitary
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem layerProd_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) :
    layerProd n f j τ id = layerProd n 1 j (fun i => τ i ^ f) id := by
  unfold layerProd
  simp only [id, mul_one]
  congr 1
  · refine prod_congr rfl fun i _ => prod_congr rfl fun k _ => ?_
    ring
  · refine prod_congr rfl fun i _ => ?_
    ring

noncomputable def layerHom (n : ℕ) {a : ℕ} (j : Fin a → ℕ) : (Fin a → ℝ) →* ℝ where
  toFun τ := layerProd n 1 j τ id
  map_one' := by simp [layerProd]
  map_mul' σ τ := by
    unfold layerProd
    simp only [id, Pi.mul_apply]
    rw [mul_mul_mul_comm]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun k _ => ?_
      rw [mul_div_mul_comm, mul_mul_mul_comm (σ i) (τ i), mul_pow (σ i / σ k), mul_pow (σ i * σ k)]
      ring
    · rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [mul_pow (σ i) (τ i) 2, mul_pow (σ i), mul_pow (σ i ^ 2)]
      ring

theorem layerProd_mul_prod : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ)
    (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) →
    layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  intro ι _ n f a j s s₁ loc h

  have hs : (fun i => s i ^ f) = (fun i => s₁ i ^ f) * ∏ v, loc v := by
    funext i
    rw [h i, Pi.mul_apply, Finset.prod_apply]
  have key : ∀ τ : Fin a → ℝ, layerHom n j τ = layerProd n 1 j τ id := fun τ => rfl
  rw [layerProd_eq_pow, layerProd_eq_pow n f j s₁, ← key, ← key, hs, map_mul, map_prod]
  simp only [key]

end GlobalTheory.FlagMeas
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.rationalPoints_countable_discrete_subgroup_adelic : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite := by
  first | exact @GlobalTheory.RatDiscrete.subgroup_countable_discrete | exact GlobalTheory.RatDiscrete.subgroup_countable_discrete | (intros; apply GlobalTheory.RatDiscrete.subgroup_countable_discrete <;> assumption)
end
