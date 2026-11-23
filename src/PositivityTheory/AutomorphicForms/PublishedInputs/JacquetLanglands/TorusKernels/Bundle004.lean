module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UpperTheory.Esk.InverseSeriesLemmas

theorem enorm_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (x : ℂ) : ‖r • x‖ₑ = ENNReal.ofReal r * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal hr]

theorem hasSum_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : HasSum (fun g : G => b (g⁻¹ • y)) 1 := by
  have h := (Equiv.inv G).hasSum_iff.mpr (hb.sum y)
  exact h

theorem tsum_ofReal_inv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ)
    (hb : IsCut G b) (y : Y) : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
  have hs := UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb y
  calc ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ENNReal.ofReal (∑' g : G, b (g⁻¹ • y)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) hs.summable).symm
    _ = 1 := by rw [hs.tsum_eq, ENNReal.ofReal_one]

end UpperTheory.Esk.InverseSeriesLemmas

open UpperTheory.Esk.InverseSeriesLemmas in
theorem UpperTheory.Esk.inverse_series_summable : UpperTheory.Esk.C3 := by
  unfold UpperTheory.Esk.C3
  intro G Y _ _ _ _ μ hμ b hb f hf hfi
  have hμ' : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ := hμ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → Y → ℂ, ∀ g y, Φ g y = b y • f (g • y) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : G → Y → ℂ, ∀ g y, Ψ g y = b (g⁻¹ • y) • f y := ⟨_, fun _ _ => rfl⟩
  have hΦm : ∀ g, Measurable (Φ g) := by
    intro g
    rw [show Φ g = fun y => b y • f (g • y) from funext (hΦ g)]
    exact hb.meas.smul (hf.comp (hμ' g).measurable)
  have hΨm : ∀ g, Measurable (Ψ g) := by
    intro g
    rw [show Ψ g = fun y => b (g⁻¹ • y) • f y from funext (hΨ g)]
    exact (hb.meas.comp (hμ' g⁻¹).measurable).smul hf
  have emb : ∀ g : G, MeasurableEmbedding (fun y : Y => g • y) := fun g =>
    (MeasurableEquiv.mk (MulAction.toPerm g) (hμ' g).measurable (hμ' g⁻¹).measurable).measurableEmbedding
  have hΨl : ∀ g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ := fun g =>
    lintegral_congr (fun z => by rw [hΨ, UpperTheory.Esk.InverseSeriesLemmas.enorm_smul_nonneg _ (hb.nonneg _)])
  have hΦl : ∀ g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ := by
    intro g
    rw [← (hμ' g).lintegral_comp (hΨm g).enorm]
    exact lintegral_congr (fun y => by rw [hΦ, hΨ, inv_smul_smul])
  have hfin : ∫⁻ z, ‖f z‖ₑ ∂μ < ⊤ := hfi.2
  have hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := by
    calc ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∑' g : G, ∫⁻ z, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          tsum_congr hΨl
      _ = ∫⁻ z, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
          (lintegral_tsum (fun g =>
            ((hb.meas.comp (hμ' g⁻¹).measurable).ennreal_ofReal.mul hf.enorm).aemeasurable)).symm
      _ = ∫⁻ z, ‖f z‖ₑ ∂μ := lintegral_congr (fun z => by
          rw [ENNReal.tsum_mul_right, UpperTheory.Esk.InverseSeriesLemmas.tsum_ofReal_inv b hb z, one_mul])
  have hsumΦ' : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := (tsum_congr hΦl).trans hsumΨ
  have hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ⊤ := by rw [hsumΦ']; exact hfin.ne
  have hΦi : ∀ g, ∫ y, Φ g y ∂μ = ∫ z, Ψ g z ∂μ := by
    intro g
    rw [← (hμ' g).integral_comp (emb g) (Ψ g)]
    congr 1
    funext y
    rw [hΦ, hΨ, inv_smul_smul]
  have hΨt : ∫ z, ∑' g, Ψ g z ∂μ = ∑' g, ∫ z, Ψ g z ∂μ :=
    integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (by rw [hsumΨ]; exact hfin.ne)
  have hΨp : ∀ z, ∑' g, Ψ g z = f z := by
    intro z
    simp only [hΨ]
    rw [((UpperTheory.Esk.InverseSeriesLemmas.hasSum_inv b hb z).smul_const (f z)).tsum_eq, one_smul]
  have hΦt : ∫ y, ∑' g, Φ g y ∂μ = ∑' g, ∫ y, Φ g y ∂μ :=
    integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ
  have hΦp : ∀ y, ∑' g, Φ g y = b y • ∑' g : G, f (g • y) := by
    intro y
    simp only [hΦ]
    exact tsum_const_smul'' (b y)
  have hfun : (fun y => b y • ∑' g : G, f (g • y)) = fun y => ∑' g, Φ g y :=
    funext (fun y => (hΦp y).symm)
  have heq : ∫ y, b y • ∑' g : G, f (g • y) ∂μ = ∫ y, f y ∂μ := by
    rw [hfun, hΦt, tsum_congr hΦi, ← hΨt]
    congr 1
    funext z
    exact hΨp z
  have hint : Integrable (fun y => ∑' g, Φ g y) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun g => (hΦm g).aestronglyMeasurable), ?_⟩
    have hle : ∫⁻ y, ‖∑' g, Φ g y‖ₑ ∂μ ≤ ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ :=
      lintegral_mono (fun y => enorm_tsum_le_tsum_enorm)
    have hsum_eq : ∫⁻ y, ∑' g, ‖Φ g y‖ₑ ∂μ = ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ :=
      lintegral_tsum (fun g => (hΦm g).enorm.aemeasurable)
    exact lt_of_le_of_lt (hle.trans hsum_eq.le) (lt_top_iff_ne_top.mpr hsumΦ)
  exact ⟨by rw [hfun]; exact hint, heq⟩
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HalfPlaneMeasureLemmas

open UpperTheory.Esk

def U : Set ℂ := {z | z.im ≠ 0}

theorem isOpen_U : IsOpen U := isOpen_ne_fun Complex.continuous_im continuous_const

def val (z : P) : ℂ := z.1

def mk (z : ℂ) (hz : z.im ≠ 0) : P := ⟨z, hz⟩

theorem openEmb : Topology.IsOpenEmbedding val :=
  isOpen_U.isOpenEmbedding_subtypeVal

theorem measEmb : MeasurableEmbedding val :=
  openEmb.measurableEmbedding

def rho (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / z.im ^ 2)

def F (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / den g z

def D (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ ((g.val.det : ℂ) / den g z ^ 2)).restrictScalars ℝ

theorem hasDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (F g) ((g.val.det : ℂ) / den g z ^ 2) z := by
  have h := ((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ) |>.add_const ((g 0 1 : ℝ) : ℂ)).div
    ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ) |>.add_const ((g 1 1 : ℝ) : ℂ)) (den_ne g hz)
  refine h.congr_deriv ?_
  simp only [den, id, mul_one]
  rw [det_eq]
  push_cast
  ring

theorem hasFDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : HasFDerivAt (F g) (D g z) z := by
  have := (hasDerivAt_F g hz).hasFDerivAt.restrictScalars ℝ
  simpa [D] using this

theorem det_D (g : GL (Fin 2) ℝ) (z : ℂ) :
    (D g z).det = Complex.normSq ((g.val.det : ℂ) / den g z ^ 2) := by
  simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

theorem F_eq (g : GL (Fin 2) ℝ) (z : P) : F g (val z) = val (g • z) := rfl

theorem injOn_F (g : GL (Fin 2) ℝ) : Set.InjOn (F g) U := by
  intro x hx y hy hxy
  have h : g • mk x hx = g • mk y hy := Subtype.ext hxy
  have := congrArg val (smul_left_cancel g h)
  exact this

theorem key (g : GL (Fin 2) ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫⁻ x in F g '' S, rho x = ∫⁻ x in S, rho x := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun x hx => (hasFDerivAt_F g (hSU hx)).hasFDerivWithinAt) ((injOn_F g).mono hSU)]
  refine setLIntegral_congr_fun hS (fun x hx => ?_)
  have hx' : x.im ≠ 0 := hSU hx
  have hd := den_ne g hx'
  have hn : Complex.normSq (den g x) ≠ 0 := by simpa using hd
  have hdet := g.det_ne_zero
  rw [det_D, rho, rho, F, im_div, abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul
    (Complex.normSq_nonneg _)]
  congr 1
  rw [Complex.normSq_div, Complex.normSq_ofReal, map_pow]
  field_simp

theorem vol_def : (volume : Measure P) = (Measure.comap val volume).withDensity fun z => rho (val z) := rfl

theorem vol_eq (s : Set P) (hs : MeasurableSet s) : volume s = ∫⁻ z in val '' s, rho z := by
  rw [vol_def, withDensity_apply _ hs, measEmb.restrict_comap,
    ← measEmb.lintegral_map, measEmb.map_comap,
    Measure.restrict_restrict (measEmb.measurableSet_range),
    Set.inter_eq_right.2 (Set.image_subset_range _ _)]

theorem image_pre (g : GL (Fin 2) ℝ) (s : Set P) :
    val '' ((fun z : P => g • z) ⁻¹' s) = F g⁻¹ '' (val '' s) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨val (g • p), ⟨g • p, hp, rfl⟩, ?_⟩
    rw [F_eq g⁻¹ (g • p), inv_smul_smul]
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨g⁻¹ • q, by rwa [smul_inv_smul], ?_⟩
    rw [F_eq]

theorem cont (g : GL (Fin 2) ℝ) : Continuous (fun z : P => g • z) := by
  have hv : Continuous (fun z : P => z.1) := continuous_subtype_val
  have h : Continuous (fun z : P => (g • z).1) := by
    change Continuous (fun z : P => num g z.1 / den g z.1)
    refine Continuous.div ?_ ?_ (fun z => den_ne g z.2)
    · simp only [num]; fun_prop
    · simp only [den]; fun_prop
  exact continuous_induced_rng.2 h

theorem meas_rho : Measurable (fun z : P => rho (val z)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.div ((Complex.measurable_im.comp measEmb.measurable).pow_const 2))

end UpperTheory.Esk.HalfPlaneMeasureLemmas

namespace UpperTheory.Esk

open HalfPlaneMeasureLemmas in
theorem half_plane_measure_invariant_proof : B1a := by
  have : LocallyCompactSpace P := openEmb.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts (Measure.comap val volume) := .comap' _ openEmb.continuous measEmb
  have : SigmaFinite (Measure.comap val volume) := inferInstance
  refine ⟨?_, ?_, fun g => ⟨cont g, ?_⟩⟩
  · rw [vol_def]
    exact SigmaFinite.withDensity_ofReal _
  · have : (Measure.comap val volume).IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap _ openEmb
    refine ⟨fun A hA hne => ?_⟩
    rw [vol_def, Ne, withDensity_apply_eq_zero meas_rho]
    have : {x : P | rho (val x) ≠ 0} ∩ A = A := by
      refine Set.inter_eq_right.2 (fun x _ => ?_)
      have := x.2
      simp only [Set.mem_ofPred_eq, rho, val, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [this]
    exact hA.measure_ne_zero _ hne
  · refine ⟨(cont g).measurable, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply (cont g).measurable hs, vol_eq _ ((cont g).measurable hs), vol_eq _ hs,
      image_pre, key _ (measEmb.measurableSet_image.2 hs)]
    rintro _ ⟨p, -, rfl⟩
    exact p.2

end UpperTheory.Esk
end
end
