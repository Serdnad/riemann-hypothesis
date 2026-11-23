module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModeAddLattice

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col Topology

noncomputable section

theorem tof_box_int_differentiable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {d : ℕ} {G : V → ℂ} (hG : Differentiable ℂ G)
    {φ : (Fin d → ℝ) → V} (hφ : Continuous φ) :
    Differentiable ℂ (fun v => ∫ t in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, G (v + φ t)) := by
  intro x₀
  have hcd : ContDiff ℂ (1 : ℕ) G := contDiff_of_differentiable_fd hG 1
  have hG' : Continuous (fderiv ℂ G) := hcd.continuous_fderiv (by norm_num)
  set B := {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} with hB
  have hBsub : B ⊆ Set.Icc 0 1 := fun x hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  have hIcc : IsCompact (Set.Icc (0 : Fin d → ℝ) 1) := isCompact_Icc
  have hBm : MeasurableSet B := tof_box_measurable d
  have hfin : volume B < ⊤ := (measure_mono hBsub).trans_lt hIcc.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hfin.ne
  have hKc : IsCompact ((fun p : V × (Fin d → ℝ) => p.1 + φ p.2) ''
      (Metric.closedBall x₀ 1 ×ˢ Set.Icc 0 1)) :=
    ((isCompact_closedBall x₀ 1).prod hIcc).image (continuous_fst.add (hφ.comp continuous_snd))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hG'.continuousOn
  have hcont : ∀ x, Continuous fun t => G (x + φ t) := fun x =>
    hG.continuous.comp (continuous_const.add hφ)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict B)
    (F := fun v t => G (v + φ t)) (F' := fun v t => fderiv ℂ G (v + φ t)) (x₀ := x₀)
    (bound := fun _ => C) (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    (((hcont x₀).continuousOn.integrableOn_compact hIcc).mono_set hBsub)
    ((hG'.comp (continuous_const.add hφ)).aestronglyMeasurable)
    ((ae_restrict_iff' hBm).2 (Filter.Eventually.of_forall fun t ht x hx =>
      hC _ ⟨(x, t), ⟨Metric.ball_subset_closedBall hx, hBsub ht⟩, rfl⟩))
    (integrable_const C)
    (Filter.Eventually.of_forall fun t x _ => by
      have h1 := (hG (x + φ t)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (φ t))
      simp only [ContinuousLinearMap.comp_id] at h1
      exact h1)
  exact h.differentiableAt

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem tb_continuous (hI : IsSplit P I) : Continuous (tb hI) := by
  unfold tb
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

theorem zeroMode_eq_fiber_integral (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    zmC hI s 0 = fun v => ∫ t in {x : Fin (Module.finrank ℝ (IR I)) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      zmG I s (v + tb hI t) := by
  funext v
  simp [zmC, zmBox]
  rfl

theorem zeroMode_differentiable (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Differentiable ℂ (zmC hI s 0) := by
  have hz : ∀ k, Differentiable ℂ (fun v : Vsp X.dim => Col.z (IR I) k v) := by
    intro k
    unfold Col.z Hf
    exact Differentiable.fun_sum fun i _ =>
      ((EuclideanSpace.proj i : Vsp X.dim →L[ℂ] ℂ).differentiable).mul_const _
  have hS : Differentiable ℂ (fun v => Col.S (IR I) v) := by
    unfold Col.S
    exact Differentiable.fun_sum fun k _ => (hz k).pow 2
  have hG : Differentiable ℂ (zmG I s) := by
    unfold zmG
    exact (hs.1.comp (differentiable_pi.2 fun _ => differentiable_id)).mul
      ((differentiable_const _).mul hS).cexp
  rw [zeroMode_eq_fiber_integral hI s]
  exact tof_box_int_differentiable hG (tb_continuous hI)

theorem zeroMode_add_real_direction (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (w : Vsp X.dim) (k : Fin (dK (IR I))) (ζ : ℂ) :
    zmC hI s 0 (w + ζ • e (IR I) k) = zmC hI s 0 w := by
  set ψ : ℂ → ℂ := fun ζ => zmC hI s 0 (w + ζ • e (IR I) k) with hψ
  have hdiff : Differentiable ℂ ψ :=
    (zeroMode_differentiable hI hs).comp ((differentiable_const _).add (differentiable_id.smul_const _))
  have hreal : ∀ ζ (t : ℝ), ψ (ζ + t) = ψ ζ := fun ζ t => by
    simp only [hψ]
    rw [add_smul, ← add_assoc, show ((t : ℂ)) • e (IR I) k = t • e (IR I) k from
      (Complex.coe_smul t _)]
    exact zeroMode_add_realSpan hI hs _ (Submodule.smul_mem _ _ (e_mem _ k))
  have hder : ∀ ζ, deriv ψ ζ = 0 := fun ζ => by
    have h1 : HasDerivAt (fun z => ψ (ζ + z)) (deriv ψ ζ) ((0 : ℝ) : ℂ) := by
      have := (hdiff (ζ + ((0 : ℝ) : ℂ))).hasDerivAt
      simpa using (this.comp_const_add ζ ((0 : ℝ) : ℂ))
    have h2 := h1.comp_ofReal
    have h3 : (fun y : ℝ => ψ (ζ + (y : ℂ))) = fun _ => ψ ζ := funext fun y => hreal ζ y
    rw [h3] at h2
    exact (h2.unique (hasDerivAt_const _ _)).symm ▸ rfl
  have := is_const_of_deriv_eq_zero hdiff hder ζ 0
  simpa [hψ] using this

theorem zeroMode_proj_two (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) : zmC hI s 0 v = zmC hI s 0 (p2 (IR I) v) := by
  have hL : ∀ (L : Finset (Fin (dK (IR I)))) (c : Fin (dK (IR I)) → ℂ) (w : Vsp X.dim),
      zmC hI s 0 (w + ∑ k ∈ L, c k • e (IR I) k) = zmC hI s 0 w := by
    intro L c w
    induction L using Finset.induction_on with
    | empty => simp
    | insert a L ha ih =>
      rw [Finset.sum_insert ha, add_comm (c a • e (IR I) a), ← add_assoc, zeroMode_add_real_direction hI hs, ih]
  have hp : p2 (IR I) v = v + ∑ k, (-(z (IR I) k v)) • e (IR I) k := by
    simp only [p2, p1, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hp, hL]

theorem proj_two_embedding (t : EuclideanSpace ℂ (Fin (gB (IR I)))) : p2 (IR I) (jj (IR I) t) = jj (IR I) t := by
  have hmem : jj (IR I) t ∈ V2 (IR I) := ((ob2 (IR I)).repr.symm t).2
  have hz : ∀ k, z (IR I) k (jj (IR I) t) = 0 := by
    intro k
    have h0 : inner ℂ (e (IR I) k) (jj (IR I) t) = 0 :=
      (Submodule.mem_orthogonal _ _).1 hmem _ (Submodule.subset_span ⟨k, rfl⟩)
    rw [PiLp.inner_apply] at h0
    simp only [z, Hf]
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  simp only [p2, p1, hz, zero_smul, Finset.sum_const_zero, sub_zero]

theorem jj_differentiable : Differentiable ℂ (jj (IR I)) := by
  exact ((V2 (IR I)).subtypeL.comp
    ((ob2 (IR I)).repr.symm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin (gB (IR I))) →L[ℂ] V2 (IR I))).differentiable

end ZM

open ZM in
theorem zeroMode_mem_sections [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ZM.zmB hI s ∈ (Col.YB hI hP 1).Sec 1 := by
  have hK := hK_of hI
  refine ⟨(zeroMode_differentiable hI hs).comp jj_differentiable, fun γ hγ t => ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_GB.1 ((YB_lat hI hP 1).1 hγ)
  simp only [zmB]
  rw [jj_add, jj_wmap' hK]
  have hp1 : p1 (IR I) x ∈ IR I := proj_one_mem_realSpan hx
  rw [← zeroMode_add_realSpan hI hs (jj (IR I) t + p2 (IR I) x) hp1,
    show jj (IR I) t + p2 (IR I) x + p1 (IR I) x = jj (IR I) t + x by rw [p2]; abel]
  rw [zeroMode_add_lattice hI hs hx, proj_two_embedding, YB_ka hI hP 1 hx, pow_one]
  have h1 : Hf t (wmap (IR I) x) = Hf (jj (IR I) t) (p2 (IR I) x) := by
    conv_lhs => rw [← wmap_jj (IR I) t]
    rw [Hf_wmap hK, proj_two_embedding]
  have h2 : Hf (wmap (IR I) x) (wmap (IR I) x) = Hf (p2 (IR I) x) (p2 (IR I) x) := Hf_wmap hK x x
  simp only [Nat.cast_one, one_mul]
  rw [h1, h2]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

def ucL (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : X.L →ₗ[ℤ] Vsp X.dim :=
  (AddMonoidHom.mk' (fun γ : X.L => uc (IR I) (γ : Vsp X.dim))
    (fun a b => by simp only [Submodule.coe_add]; exact uc_add _ _)).toIntLinearMap

theorem NIp_le_ker (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : NIp X I ≤ LinearMap.ker (ucL X I) := by
  intro x hx
  rw [LinearMap.mem_ker]
  exact uc_Ip hx

def uQ (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Qc X I →ₗ[ℤ] Vsp X.dim :=
  (NIp X I).liftQ (ucL X I) (NIp_le_ker X I)

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)}

theorem uQ_mk (γ : X.L) : uQ X I (Submodule.Quotient.mk γ) = uc (IR I) (γ : Vsp X.dim) := rfl

theorem uQ_out (c : Qc X I) : uQ X I c = uc (IR I) ((Quotient.out c : X.L) : Vsp X.dim) := by
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  calc uQ X I c = uQ X I (Submodule.Quotient.mk (Quotient.out c)) := by rw [e]
    _ = _ := uQ_mk _

theorem uQ_mem (c : Qc X I) : uQ X I c ∈ IR I := by
  rw [uQ_out]
  exact uc_mem _ _

theorem uQ_eq_zero {c : Qc X I} (h : uQ X I c = 0) : c = 0 := by
  have hγ : ((Quotient.out c : X.L) : Vsp X.dim) ∈ Ip X I := by
    rw [mem_Ip]
    refine ⟨(Quotient.out c).2, fun a ha => ?_⟩
    rw [← inner_uc (IR I) _ a (Submodule.subset_span ha), ← uQ_out, h, inner_zero_left]
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  rw [← e]
  exact (Submodule.Quotient.mk_eq_zero _).2 hγ

variable {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem uQ_sep {c : Qc X I} (h : c ≠ 0) : b0 (E := E) P.q P.R0 ≤ ‖uQ X I c‖ ^ 2 := by
  have hne : uQ X I c ≠ 0 := fun h0 => h (uQ_eq_zero h0)
  rw [uQ_out] at hne ⊢
  exact hI.sep _ (Quotient.out c).2 _ (isU_uc _) hne

theorem uQ_dist {c c' : Qc X I} (h : c ≠ c') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uQ X I c) (uQ X I c') := by
  have h1 := uQ_sep hI (sub_ne_zero.2 h)
  rw [dist_eq_norm, ← map_sub, ← Real.sqrt_sq (norm_nonneg (uQ X I (c - c')))]
  exact Real.sqrt_le_sqrt h1

theorem tailQ (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (a : ℝ) (ha : 0 < a)
    (hcond : (dK (IR I) : ℝ) + 1 ≤ a * P.q * b0 (E := E) P.q P.R0) :
    Summable (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
        Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2)) ∧
      ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2) ≤
        2 * 3 ^ (dK (IR I)) * Real.exp (-(a * P.q * b0 (E := E) P.q P.R0)) := by
  classical
  obtain ⟨ρ, -, hρ⟩ := hI.rank
  have hdK : dK (IR I) = 2 * (PT.f E * ρ) := by
    show Module.finrank ℝ (IR I) = 2 * (PT.f E * ρ)
    rw [hρ]; ring
  have hb0 : 0 < b0 (E := E) P.q P.R0 := cutoff_pos P
  have haqb : 0 < a * P.q * b0 (E := E) P.q P.R0 := by
    have : (0 : ℝ) ≤ dK (IR I) := Nat.cast_nonneg _
    linarith
  have haq : 0 < a * (P.q : ℝ) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [haqb, hb0, hneg]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a * P.q) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.2 haq
  have hs2 : s ^ 2 = a * P.q := by rw [hs_def]; exact Real.sq_sqrt haq.le
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = Real.sqrt (b0 (E := E) P.q P.R0) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ Real.sqrt_pos.2 hb0
  have hδ2 : δ ^ 2 = b0 (E := E) P.q P.R0 := by rw [hδ_def]; exact Real.sq_sqrt hb0.le
  have h4s : 0 < 4 * s := by positivity
  have hr0pos : 0 < 4 * s * δ := by positivity
  have hnorm : ∀ c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, δ ≤ ‖uQ X I c.1‖ := by
    intro c
    have hc : c.1 ≠ 0 := by simpa using c.2
    rw [hδ_def, ← Real.sqrt_sq (norm_nonneg (uQ X I c.1))]
    exact Real.sqrt_le_sqrt (uQ_sep hI hc)
  have hinj : Function.Injective
      (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} => uQ X I c.1) := by
    intro c c' hcc
    apply Subtype.ext
    have h0 : uQ X I (c.1 - c'.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hcc
    exact sub_eq_zero.1 (uQ_eq_zero h0)
  have key := hA {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} (fun c => 4 * s * ‖uQ X I c.1‖)
    (PT.f E * ρ) (4 * s * δ) hr0pos
    (by
      have e1 : (4 * s * δ) ^ 2 = 16 * (a * P.q * b0 (E := E) P.q P.R0) := by
        rw [mul_pow, mul_pow, hs2, hδ2]; ring
      have e2 : (dK (IR I) : ℝ) = 2 * ((PT.f E * ρ : ℕ) : ℝ) := by rw [hdK]; push_cast; ring
      rw [e1]; rw [e2] at hcond; linarith)
    (fun c => mul_le_mul_of_nonneg_left (hnorm c) h4s.le)
    (by
      intro R hR S hS
      have hcard : (S.image fun c => uQ X I c.1).card = S.card := Finset.card_image_of_injective _ hinj
      have hpk := pack_K hP (IR I) (S.image fun c => uQ X I c.1)
        (by
          intro u hu
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          exact uQ_mem c.1) δ (R / (4 * s)) hδ
        (by
          rw [le_div_iff₀ h4s]
          calc δ * (4 * s) = 4 * s * δ := by ring
            _ ≤ R := hR)
        (by
          intro u hu
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hu
          rw [le_div_iff₀ h4s]
          calc ‖uQ X I c.1‖ * (4 * s) = 4 * s * ‖uQ X I c.1‖ := by ring
            _ ≤ R := hS c hc)
        (by
          intro u hu v hv huv
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hv
          have hcc : c.1 ≠ c'.1 := fun e => huv (by simp only [e])
          rw [hδ_def]
          exact uQ_dist hI hcc)
      have e3 : 3 * (R / (4 * s)) / δ = 3 * R / (4 * s * δ) := by
        field_simp
      rw [e3, hdK, hcard] at hpk
      exact hpk)
  have hfun : (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
      Real.exp (-(4 * s * ‖uQ X I c.1‖) ^ 2 / 16)) =
      fun c => Real.exp (-(a * P.q) * ‖uQ X I c.1‖ ^ 2) := by
    funext c
    congr 1
    rw [mul_pow, mul_pow, hs2]; ring
  have e9 : (9 : ℝ) ^ (PT.f E * ρ) = 3 ^ (dK (IR I)) := by rw [hdK, pow_mul (3 : ℝ) 2 (PT.f E * ρ)]; norm_num
  have er : -(4 * s * δ) ^ 2 / 16 = -(a * P.q * b0 (E := E) P.q P.R0) := by
    rw [mul_pow, mul_pow, hs2, hδ2]; ring
  rw [hfun, e9, er] at key
  exact key

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end
