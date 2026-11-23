module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mero_eq {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {e g : ℂ → ℂ} (he : MeromorphicOn e Set.univ)
    (hg : DifferentiableOn ℂ g U) {t : ℝ} (h : ∀ s : ℂ, t < s.re → s ∈ U ∧ e s = g s) {s : ℂ} (hs : s ∈ U) (hc' : ContinuousAt e s) :
    e s = g s := by
  have ha := hg.analyticOnNhd hU
  have m : MeromorphicOn (e - g) U := (he.mono_set (Set.subset_univ _)).sub ha.meromorphicOn
  have h1 : t < ((t + 1 : ℝ) : ℂ).re := by simp
  have z : meromorphicOrderAt (e - g) s = ⊤ := by
    by_contra hne
    refine m.meromorphicOrderAt_ne_top_of_isPreconnected hc hs (h _ h1).1 hne (meromorphicOrderAt_eq_top_iff.2 ?_)
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1)] with z hz
    exact sub_eq_zero.2 (h z hz).2
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s) (hc'.mono_left nhdsWithin_le_nhds)
    ((ha s hs).continuousAt.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 z] with z hz using sub_eq_zero.1 hz

theorem contAt_of_sphere {X : Type} [TopologicalSpace X] {g : ℂ → X → ℂ} {s₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x, DiffContOnCl ℂ (g · x) (Metric.ball s₀ ρ))
    (hc : ContinuousOn (fun y : ℂ × X => g y.1 y.2) (Metric.sphere s₀ ρ ×ˢ Set.univ)) (x₀ : X) :
    ContinuousAt (fun y : ℂ × X => g y.1 y.2) (s₀, x₀) := by
  have c0 : ContinuousAt (g · x₀) s₀ := ((hd x₀).differentiableAt Metric.isOpen_ball (Metric.mem_ball_self hρ)).continuousAt
  have : Tendsto (fun y : ℂ × X => g y.1 y.2 - g y.1 x₀) (𝓝 (s₀, x₀)) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have c1 : Continuous fun y : X × Metric.sphere s₀ ρ => ‖g y.2 y.1 - g y.2 x₀‖ :=
      ((hc.comp_continuous (f := fun y : X × Metric.sphere s₀ ρ => (y.2.1, y.1)) (by fun_prop) fun y => ⟨y.2.2, trivial⟩).sub
        (hc.comp_continuous (f := fun y : X × Metric.sphere s₀ ρ => (y.2.1, x₀)) (by fun_prop) fun y => ⟨y.2.2, trivial⟩)).norm
    have e1 : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ (Set.univ : Set (Metric.sphere s₀ ρ)), ‖g z x - g z x₀‖ < ε / 2 :=
      isCompact_univ.eventually_forall_of_forall_eventually fun z _ =>
        (isOpen_lt c1 continuous_const).mem_nhds (by simpa using hε)
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds s₀ hρ) e1] with y hy
    rw [dist_zero_right]
    refine (Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball ((hd y.2).sub (hd x₀)) (C := ε / 2)
      (fun z hz => ?_) (subset_closure hy.1)).trans_lt (half_lt_self hε)
    rw [frontier_ball _ hρ.ne'] at hz
    exact (hy.2 ⟨z, hz⟩ trivial).le
  have h2 := this.add (c0.tendsto.comp continuous_fst.continuousAt)
  simpa [ContinuousAt] using h2

theorem IsEisCont.update {f : ℂ → G2 σ Y → ℂ} {U : Set ℂ} {Ê : ℂ → G2 σ Y → ℂ} (h : IsEisCont f U Ê) {s₀ : ℂ} {k : ℕ}
    (hr : IsRegAt Ê s₀ k) {val : G2 σ Y → ℂ} (hv : EisValueAt f s₀ val) :
    IsEisCont f (insert s₀ U) (Function.update Ê s₀ val) := by
  obtain ⟨r, H, r0, hH, -, -, C, N, hC⟩ := hr
  obtain ⟨t, half⟩ := h.half
  have op : IsOpen (insert s₀ U) := isOpen_iff_mem_nhds.2 fun s hs => hs.elim
    (fun e => e ▸ insert_mem_nhds_iff.2 (h.disc s)) fun hs => mem_of_superset (h.isOpen.mem_nhds hs) (Set.subset_insert _ _)
  have ev : ∀ s ≠ s₀, ∀ᶠ z in 𝓝 s, Function.update Ê s₀ val z = Ê z := fun s hs => by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz using Function.update_of_ne hz _ _
  have hol : ∀ x, DifferentiableOn ℂ (Function.update Ê s₀ val · x) (insert s₀ U) := fun x s hs => by
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases e0 : s = s₀
    · obtain ⟨e, he, ⟨t', h1⟩, h2, h3⟩ := hv x
      subst e0
      refine h2.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [h2.eventually_analyticAt, op.mem_nhds hs] with z hz hz'
      by_cases e1 : z = s
      · rw [e1, Function.update_self, h3]
      · rw [Function.update_of_ne e1]
        exact (mero_eq h.isOpen h.conn he (h.hol x) (t := max t t') (fun s hs => ⟨(half s (max_lt_iff.1 hs).1).1,
          (h1 s (max_lt_iff.1 hs).2).unique ((half s (max_lt_iff.1 hs).1).2 x)⟩)
          (hz'.resolve_left e1) hz.continuousAt).symm
    · exact ((h.hol x).differentiableAt (h.isOpen.mem_nhds (hs.resolve_left e0))).congr_of_eventuallyEq
        ((ev s e0).mono fun z hz => congrFun hz x)
  obtain ⟨ρ, ρ0, hρ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (inter_mem (op.mem_nhds (Set.mem_insert _ _)) (Metric.ball_mem_nhds s₀ r0))
  have dc : ∀ x, DiffContOnCl ℂ (Function.update Ê s₀ val · x) (Metric.ball s₀ ρ) := fun x =>
    (hol x).diffContOnCl_ball fun z hz => (hρ hz).1
  have sp : ∀ z ∈ Metric.sphere s₀ ρ, z ≠ s₀ := fun z hz => Metric.ne_of_mem_sphere hz ρ0.ne'
  have ca : ∀ s ∈ U, s ≠ s₀ → ∀ x, ContinuousAt (fun y : ℂ × G2 σ Y => Function.update Ê s₀ val y.1 y.2) (s, x) := fun s hs e x =>
    (h.cont.continuousAt (prod_mem_nhds (h.isOpen.mem_nhds hs) univ_mem)).congr
      ((continuous_fst.continuousAt.eventually (ev s e)).mono fun y hy => (congrFun hy y.2).symm)
  refine ⟨op, h.conn.subset_closure (Set.subset_insert _ _) (Set.insert_subset ?_ subset_closure),
    fun s => (h.disc s).mono fun z hz => .inr hz, ⟨max t s₀.re, fun s hs => ⟨.inr (half s (max_lt_iff.1 hs).1).1, fun x => ?_⟩⟩, hol, fun y hy => ?_, fun s hs => ?_⟩
  · exact mem_closure_iff_frequently.2 ((h.disc s₀).frequently.filter_mono nhdsWithin_le_nhds)
  · rw [Function.update_of_ne fun e => (max_lt_iff.1 hs).2.ne (by rw [e])]; exact (half s (max_lt_iff.1 hs).1).2 x
  · refine ContinuousAt.continuousWithinAt ?_
    by_cases e0 : y.1 = s₀
    · rw [show y = (s₀, y.2) from Prod.ext e0 rfl]
      exact contAt_of_sphere ρ0 dc (fun z hz => (ca z.1 ((hρ (Metric.sphere_subset_closedBall hz.1)).1.resolve_left (sp _ hz.1))
        (sp _ hz.1) z.2).continuousWithinAt) _
    · exact ca y.1 (hy.1.resolve_left e0) e0 y.2
  · by_cases e0 : s = s₀
    · subst e0
      refine ⟨ρ, C / ρ ^ k, N, ρ0, fun z hz x => Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball (dc x)
        (fun w hw => ?_) (subset_closure hz)⟩
      rw [frontier_ball _ ρ0.ne'] at hw
      have b := (hρ (Metric.sphere_subset_closedBall hw)).2
      have := hC w b x
      rw [hH w b (sp w hw), norm_mul, norm_pow, mem_sphere_iff_norm.1 hw] at this
      rw [Function.update_of_ne (sp w hw), div_mul_eq_mul_div, le_div_iff₀' (pow_pos ρ0 k)]
      exact this
    · obtain ⟨ε, C', N', ε0, hb⟩ := h.grow s (hs.resolve_left e0)
      obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (inter_mem (ev s e0) (Metric.ball_mem_nhds s ε0))
      exact ⟨δ, C', N', δ0, fun z hz x => by rw [(hδ hz).1]; exact hb z (hδ hz).2 x⟩

theorem swFull_of (h1 : SWAniso) (h2 : EisContinues) (h3 : BoxSec) : SWFull := by
  intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n Y r' s' hB hn (.inr hY) χ hχ m hr K a hK ha _ _
    (h3 F E σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((m : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}


variable (σ) in
structure Cpt (J : Matrix (Fin n) (Fin n) E) : Prop where
  lc : LocallyCompactSpace (UA σ J)
  sc : SecondCountableTopology (UA σ J)
  t2 : T2Space (UA σ J)
  cnt : Countable (ratU σ J)
  cov : ∃ Ω : Set (UA σ J), IsCompact Ω ∧ ∀ g, ∃ γ ∈ ratU σ J, γ * g ∈ Ω
  hgt : ∃ C : ℝ≥0, ∀ g : UA σ J, qht g ≤ C
  ex : ∃ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ J) D μ
  fin : ∀ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ J) D μ → μ D < ⊤
  right : ∀ μ : Measure (UA σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def CptAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 → Cpt σ Y.J

theorem cptAll_of (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : PositivityTheory.ThKEst.EpsOf) (h3 : PositivityTheory.ThKEst.SiegelAll) (h4 : PositivityTheory.ThKEst.FinVolU)
    (h5 : PositivityTheory.ThKF.Unimod) : CptAll := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  obtain ⟨e, -, hr⟩ := h2 F E σ B hB n Y r s hY
  obtain ⟨a1, a2, a3, a4, -, -, -, a5⟩ := h1 F E σ hB.cm n Y.J e
  obtain ⟨fr, g, -, ⟨Ω, hΩ, hc⟩, -⟩ := h3 F E σ hB.cm n Y.J e
  have r0 : fr.r = 0 := by have := hr fr g; omega
  have a0 : ∀ t, fr.a t = 1 := fun t => by
    have : t + t = t := funext fun i => absurd i.2 (by omega)
    have e := g.add t t
    rw [this] at e
    exact left_eq_mul.1 e
  have cov : ∀ x, ∃ γ ∈ ratU σ Y.J, γ * x ∈ Ω := fun x => by
    obtain ⟨γ, hγ, t, -, κ, hκ, e⟩ := hc x
    exact ⟨γ, hγ, by rwa [e, a0, one_mul]⟩
  obtain ⟨C, hC⟩ := a5 Ω hΩ
  obtain ⟨-, u1, u2⟩ : Countable (ratU σ Y.J) ∧ _ ∧ _ := e.1.elim
    (fun h => h5 F E σ hB.cm n Y.J 1 (fun i j => by simp [h]) e.2) fun h => h5 F E σ hB.cm n Y.J (-1) (fun i j => by simp [h]) e.2
  refine ⟨a1, a2, a3, a4, ⟨Ω, hΩ, cov⟩, ⟨C, fun x => ?_⟩, u1, h4 F E σ hB.cm n Y.J e, u2⟩
  obtain ⟨γ, hγ, hx⟩ := cov x
  exact (ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ Y.J)).trans (hC _ hx)

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem fd_ne (hD : IsFundamentalDomain Γ D μ) : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)

theorem fd_eq_zero (hD : IsFundamentalDomain Γ D μ) {f : G → ℂ} (hc : Continuous f) (hi : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (h0 : (fun g => ‖f g‖ ^ 2) =ᵐ[μ.restrict D] 0) : f = 0 := by
  have h1 : μ {g | f g ≠ 0} = 0 := by
    refine hD.measure_zero_of_invariant _ (fun γ => Set.ext fun x => ?_) ?_
    · rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact (congrArg (· ≠ 0) (hi _ (γ⁻¹).2 x)).to_iff
    · rw [← Measure.restrict_apply (isOpen_ne_fun hc continuous_const).measurableSet]
      exact measure_mono_null (fun g hg => by simpa using hg) (ae_iff.1 h0)
  exact (hc.ae_eq_iff_eq μ continuous_const).1 h1

end Gen

variable {J : Matrix (Fin n) (Fin n) E}

instance borelUA : BorelSpace (UA σ J) := ⟨rfl⟩

instance topUA : IsTopologicalGroup (UA σ J) :=
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  Subgroup.instIsTopologicalGroupSubtypeMem _

theorem Cpt.bdd (h : Cpt σ J) {f : UA σ J → ℂ} (hc : Continuous f) (hi : ∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) :
    ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := by
  obtain ⟨Ω, hΩ, cov⟩ := h.cov
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, hg⟩ := cov g
  exact hi γ hγ g ▸ hC _ hg

theorem Cpt.bdd₂ {m : ℕ} {J' : Matrix (Fin m) (Fin m) E} (h : Cpt σ J) (h' : Cpt σ J') {f : UA σ J × UA σ J' → ℂ}
    (hc : Continuous f) (hi : ∀ γ ∈ ratU σ J, ∀ δ ∈ ratU σ J', ∀ g g', f (γ * g, δ * g') = f (g, g')) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨Ω, hΩ, cov⟩ := h.cov
  obtain ⟨Ω', hΩ', cov'⟩ := h'.cov
  obtain ⟨C, hC⟩ := (hΩ.prod hΩ').exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, hg⟩ := cov x.1
  obtain ⟨δ, hδ, hg'⟩ := cov' x.2
  exact (hi γ hγ δ hδ x.1 x.2 ▸ hC (γ * x.1, δ * x.2) ⟨hg, hg'⟩ :)

theorem Cpt.rapid {Y : Spc F E n} (h : Cpt σ Y.J) {f : UA σ Y.J → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ ratU σ Y.J, ∀ g, f (γ * g) = f g) : IsRapid f := by
  obtain ⟨C, hC⟩ := h.bdd hc hi
  obtain ⟨b, hb⟩ := h.hgt
  exact ⟨hc, hi, fun N => ⟨C * (b : ℝ) ^ N, fun g => mul_le_mul (hC g) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hb g) N)
    (by positivity) ((norm_nonneg _).trans (hC g))⟩⟩

theorem Cpt.vol_ne (h : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) : μ.real D ≠ 0 := by
  haveI := h.cnt
  exact ENNReal.toReal_ne_zero.2 ⟨fd_ne hD, (h.fin μ D hμ hD).ne⟩

theorem Cpt.eq_zero (h : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {f : UA σ J → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) (h0 : pet μ D f f = 0) : f = 0 := by
  haveI := h.cnt
  obtain ⟨C, hC⟩ := h.bdd hc hi
  have hi2 : IntegrableOn (fun g => ‖f g‖ ^ 2) D μ := Measure.integrableOn_of_bounded (M := C ^ 2) (h.fin μ D hμ hD).ne
    (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun g => by
      rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hC g) 2)
  have e : pet μ D f f = ((∫ g in D, ‖f g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun g => by simpa using Complex.mul_conj' (f g))
  rw [e, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi2] at h0
  exact fd_eq_zero hD hc hi h0

end GlobalTheory.ThK.Dbl

end
end
