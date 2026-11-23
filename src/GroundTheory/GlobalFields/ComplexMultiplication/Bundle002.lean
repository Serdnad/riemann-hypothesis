module

public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle001
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Complex Filter Topology Set

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {E : Type*} [NormedAddCommGroup E]

def limPunctured (f : ℂ → E) (z : ℂ) : E := limUnder (𝓝[≠] z) f

lemma limPunctured_eq_of_continuousAt {f : ℂ → E} {z : ℂ} (h : ContinuousAt f z) :
    limPunctured f z = f z :=
  (tendsto_nhdsWithin_of_tendsto_nhds h.tendsto).limUnder_eq

lemma tendsto_limPunctured [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) :
    Tendsto f (𝓝[≠] z) (𝓝 (limPunctured f z)) := by
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
  rwa [limPunctured, hc.limUnder_eq]

lemma limPunctured_eventuallyEq_of_analyticAt [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {w : ℂ} (hw : AnalyticAt ℂ f w) :
    limPunctured f =ᶠ[𝓝 w] f := by
  filter_upwards [(isOpen_analyticAt ℂ f).mem_nhds hw] with u hu
  exact limPunctured_eq_of_continuousAt hu.continuousAt

variable [NormedSpace ℂ E]

lemma analyticAt_limPunctured [CompleteSpace E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) : AnalyticAt ℂ (limPunctured f) z := by
  have hev : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w := hf.eventually_analyticAt
  have heq : limPunctured f =ᶠ[𝓝[≠] z] f :=
    hev.mono fun w hw ↦ (limPunctured_eventuallyEq_of_analyticAt hw).eq_of_nhds
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · exact hev.mono fun w hw ↦
      hw.differentiableAt.congr_of_eventuallyEq (limPunctured_eventuallyEq_of_analyticAt hw)
  · rw [← continuousWithinAt_compl_self]
    exact (tendsto_limPunctured hf ho).congr' heq.symm

variable {L : PeriodPair}

lemma IsPeriodic.limPunctured_add {f : ℂ → E} (hp : IsPeriodic L f) {z l : ℂ}
    (hl : l ∈ L.lattice) (hf : MeromorphicAt f z) (ho : 0 ≤ meromorphicOrderAt f z) :
    limPunctured f (z + l) = limPunctured f z := by
  have h1 : Tendsto (fun w ↦ w - l) (𝓝[≠] (z + l)) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun w ↦ w - l) (𝓝 (z + l)) (𝓝 (z + l - l)) :=
        (continuous_id.sub continuous_const).tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      simp only [mem_singleton_iff] at h ⊢
      rw [← h]; ring
  have h2 := (tendsto_limPunctured hf ho).comp h1
  have e : (f ∘ fun w ↦ w - l) = f := funext fun w ↦ hp.sub w hl
  rw [e] at h2
  exact h2.limUnder_eq


variable (L) in
theorem exists_const_of_meromorphicOrderAt_nonneg [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, ∀ z, AnalyticAt ℂ f z → f z = c := by
  have hd : Differentiable ℂ (limPunctured f) := fun z ↦
    (analyticAt_limPunctured (hf z) (ho z)).differentiableAt
  have hFp : IsPeriodic L (limPunctured f) := fun z l hl ↦
    hp.limPunctured_add hl (hf z) (ho z)
  refine ⟨limPunctured f 0, fun z hz ↦ ?_⟩
  rw [← limPunctured_eq_of_continuousAt hz.continuousAt]
  exact eq_of_differentiable_of_isPeriodic L hd hFp z 0


variable (L) in
theorem exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  obtain ⟨c, hc⟩ := exists_const_of_meromorphicOrderAt_nonneg L hf hp ho
  refine ⟨c, ?_⟩
  filter_upwards [(hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin] with z hz
  exact hc z hz

end Elliptic
end GroundTheory.Global
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve OnePoint

variable {F : Type*} [Field F]

structure IsShortForm (W : WeierstrassCurve F) : Prop where
  a₁_eq : W.a₁ = 0
  a₂_eq : W.a₂ = 0
  a₃_eq : W.a₃ = 0

namespace ShortWeierstrass

def g₂ (W : WeierstrassCurve F) : F := -4 * W.a₄

def g₃ (W : WeierstrassCurve F) : F := -4 * W.a₆

end ShortWeierstrass

open ShortWeierstrass

theorem IsShortForm.Δ_eq {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]
  ring

theorem IsShortForm.a₄_ne_zero_or_a₆_ne_zero {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : IsShortForm W) : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
  by_contra h
  push Not at h
  have := W.isUnit_Δ.ne_zero
  rw [hW.Δ_eq, h.1, h.2] at this
  simp at this


open Classical in
open scoped Classical in
noncomputable def weberValue (W : WeierstrassCurve F) (x : F) : F :=
  if W.a₆ = 0 then g₂ W ^ 2 / W.Δ * x ^ 2
  else if W.a₄ = 0 then g₃ W / W.Δ * x ^ 3
  else g₂ W * g₃ W / W.Δ * x

noncomputable def weberFunction (W : WeierstrassCurve F) : W.toAffine.Point → OnePoint F
  | .zero => ∞
  | .some x _ _ => OnePoint.some (weberValue W x)

@[simp]
theorem weberFunction_some (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    weberFunction W (.some x y h) = OnePoint.some (weberValue W x) := rfl

theorem weberValue_of_a₆_eq_zero {W : WeierstrassCurve F} (hb : W.a₆ = 0) (x : F) :
    weberValue W x = g₂ W ^ 2 / W.Δ * x ^ 2 := by
  simp [weberValue, hb]

theorem weberValue_of_a₄_eq_zero {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₃ W / W.Δ * x ^ 3 := by
  simp [weberValue, ha, hb]

theorem weberValue_of_ne_zero {W : WeierstrassCurve F} (ha : W.a₄ ≠ 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₂ W * g₃ W / W.Δ * x := by
  simp [weberValue, ha, hb]

section Isomorphism

variable [CharZero F]

theorem variableChange_rst_eq_zero {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  have h1 := hCW.a₁_eq
  have h2 := hCW.a₂_eq
  have h3 := hCW.a₃_eq
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, hW.a₁_eq, hW.a₂_eq,
    hW.a₃_eq] at h1 h2 h3
  have hs : C.s = 0 := by simpa [hv] using h1
  have ht : C.t = 0 := by simpa [hv] using h3
  have hr : C.r = 0 := by simpa [hv, hs] using h2
  exact ⟨hr, hs, ht⟩

theorem variableChange_a₄_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₄ = ↑C.u⁻¹ ^ 4 * W.a₄ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₄, hr, hs, ht]

theorem variableChange_a₆_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₆ = ↑C.u⁻¹ ^ 6 * W.a₆ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₆, hr, ht]

theorem weberFunction_variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F}
    [W.IsElliptic] (hC : C • W = W') (hW : IsShortForm W) (hW' : IsShortForm W')
    (P : W.toAffine.Point) :
    weberFunction W' (variableChangePoint C hC P) = weberFunction W P := by
  subst hC
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hW'
  cases P with
  | zero => rfl
  | some x y h =>
    rw [variableChangePoint_some, weberFunction_some, weberFunction_some]
    congr 1
    have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    have ha := variableChange_a₄_of_isShortForm hW hW'
    have hb := variableChange_a₆_of_isShortForm hW hW'
    have hb0 : (C • W).a₆ = 0 ↔ W.a₆ = 0 := by rw [hb]; simp
    have ha0 : (C • W).a₄ = 0 ↔ W.a₄ = 0 := by rw [ha]; simp
    by_cases h6 : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (hb0.mpr h6), weberValue_of_a₆_eq_zero h6]
      simp only [g₂, ha, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    by_cases h4 : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (ha0.mpr h4) (mt hb0.mp h6), weberValue_of_a₄_eq_zero h4 h6]
      simp only [g₃, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    · rw [weberValue_of_ne_zero (mt ha0.mp h4) (mt hb0.mp h6), weberValue_of_ne_zero h4 h6]
      simp only [g₂, g₃, ha, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp

end Isomorphism

section FieldOfDefinition

variable {L : Type*} [Field L]

def pointMapOfRingHom (φ : F →+* L) {W : WeierstrassCurve F} :
    W.toAffine.Point → (W.map φ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) ((W.toAffine.map_nonsingular φ.injective x y).mpr h)

theorem weberFunction_pointMapOfRingHom (φ : F →+* L) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    weberFunction (W.map φ) (pointMapOfRingHom φ P) = OnePoint.map φ (weberFunction W P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    have h4 : (W.map φ).a₄ = φ W.a₄ := rfl
    have h6 : (W.map φ).a₆ = φ W.a₆ := rfl
    show OnePoint.some _ = OnePoint.some _
    congr 1
    by_cases hb : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (by rw [h6, hb, map_zero]), weberValue_of_a₆_eq_zero hb]
      simp [g₂, map_Δ, map_ofNat]
    have hb' : (W.map φ).a₆ ≠ 0 := by rw [h6]; exact (map_ne_zero φ).mpr hb
    by_cases ha : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (by rw [h4, ha, map_zero]) hb', weberValue_of_a₄_eq_zero ha hb]
      simp [g₃, map_Δ, map_ofNat]
    · have ha' : (W.map φ).a₄ ≠ 0 := by rw [h4]; exact (map_ne_zero φ).mpr ha
      rw [weberValue_of_ne_zero ha' hb', weberValue_of_ne_zero ha hb]
      simp [g₂, g₃, map_Δ, map_ofNat]

end FieldOfDefinition

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsLocalRing

noncomputable section

variable {L : Type*} [Field L] [NumberField L]

theorem eventually_exists_map_eq (E : WeierstrassCurve L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_mem_localizationAt E.a₁, eventually_mem_localizationAt E.a₂,
    eventually_mem_localizationAt E.a₃, eventually_mem_localizationAt E.a₄,
    eventually_mem_localizationAt E.a₆] with v h₁ h₂ h₃ h₄ h₆
  exact ⟨⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩, rfl⟩

theorem isElliptic_of_map_eq {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L} [E.IsElliptic]
    {W : WeierstrassCurve (localizationAt L v)} (h : W.map (algebraMap (localizationAt L v) L) = E)
    (hΔ : E.Δ⁻¹ ∈ localizationAt L v) : W.IsElliptic := by
  have hW : algebraMap (localizationAt L v) L W.Δ = E.Δ := by
    rw [← WeierstrassCurve.map_Δ, h]
  rw [WeierstrassCurve.isElliptic_iff]
  refine isUnit_iff_exists_inv.mpr ⟨⟨E.Δ⁻¹, hΔ⟩, Subtype.ext ?_⟩
  change algebraMap (localizationAt L v) L W.Δ * E.Δ⁻¹ = 1
  rw [hW]
  exact mul_inv_cancel₀ E.isUnit_Δ.ne_zero

theorem eventually_exists_model (E : WeierstrassCurve L) [E.IsElliptic] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.IsElliptic ∧ W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_exists_map_eq E, eventually_mem_localizationAt E.Δ⁻¹] with v ⟨W, h⟩ hΔ
  exact ⟨W, isElliptic_of_map_eq h hΔ, h⟩

theorem algebraMap_j_of_map_eq {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L}
    [E.IsElliptic] {W : WeierstrassCurve (localizationAt L v)} [W.IsElliptic]
    (h : W.map (algebraMap (localizationAt L v) L) = E) :
    algebraMap (localizationAt L v) L W.j = E.j := by
  subst h
  exact (W.map_j _).symm

theorem eventually_residue_j_ne {E E' : WeierstrassCurve L} [E.IsElliptic] [E'.IsElliptic]
    (hj : E.j ≠ E'.j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E →
          W'.map (algebraMap (localizationAt L v) L) = E' →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
  filter_upwards [eventually_isUnit_localizationAt (sub_ne_zero.mpr hj)] with v ⟨hmem, hu⟩
    W W' _ _ h h'
  have hsub : W.j - W'.j = ⟨E.j - E'.j, hmem⟩ :=
    Subtype.ext (congrArg₂ (· - ·) (algebraMap_j_of_map_eq h) (algebraMap_j_of_map_eq h'))
  intro heq
  refine (residue_ne_zero_iff_isUnit (W.j - W'.j)).mpr (hsub ▸ hu) ?_
  rw [map_sub, heq, sub_self]

theorem j_map_residue {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.map (residue R)).j = residue R W.j :=
  W.map_j _

theorem eventually_goodReduction {ι : Type*} [Finite ι] (E : ι → WeierstrassCurve L)
    [∀ i, (E i).IsElliptic] (hE : Pairwise fun i k => (E i).j ≠ (E k).j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ (W : ι → WeierstrassCurve (localizationAt L v)) (_ : ∀ i, (W i).IsElliptic),
        (∀ i, (W i).map (algebraMap (localizationAt L v) L) = E i) ∧
        (∀ i, algebraMap (localizationAt L v) L (W i).j = (E i).j) ∧
        Pairwise fun i k => residue (localizationAt L v) (W i).j ≠
          residue (localizationAt L v) (W k).j := by
  have hd : ∀ i k, ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, i ≠ k →
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E i →
          W'.map (algebraMap (localizationAt L v) L) = E k →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
    intro i k
    by_cases hik : i = k
    · exact Filter.Eventually.of_forall fun _ h => (h hik).elim
    · exact (eventually_residue_j_ne (hE hik)).mono fun _ h _ => h
  filter_upwards [Filter.eventually_all.mpr fun i => eventually_exists_model (E i),
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hd i)] with v hm hdv
  choose W hWe hWm using hm
  exact ⟨W, hWe, hWm, fun i => algebraMap_j_of_map_eq (hWm i),
    fun i k hik => hdv i k hik (W i) (W k) (hWm i) (hWm k)⟩

end

end GroundTheory.Global
end
