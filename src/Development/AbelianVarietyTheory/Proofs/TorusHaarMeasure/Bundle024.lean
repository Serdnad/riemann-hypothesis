module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatFin

open GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem muF_lt_top_of_isCompact {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {K : Set (V (nd X))}
    (hK : IsCompact K) (hKO : K ⊆ OmF X x0) : muF X x0 K < ⊤ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image (OntoB.densF_continuousOn.mono hKO)
  unfold muF
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (densF X x0 z) ∂(volume.restrict (OmF X x0))
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(volume.restrict (OmF X x0)) :=
        setLIntegral_mono' hK.measurableSet fun z hz =>
          ENNReal.ofReal_le_ofReal (hM ⟨z, hz, rfl⟩)
    _ = ENNReal.ofReal M * (volume.restrict (OmF X x0)) K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)

theorem muF_borSat_eq (hI : MeasInvStatement (E := E)) {r : ℕ} (X : Data E r)
    {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1) {C : Set (Frame X.Ψ r)}
    (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (cpt X x0 ⁻¹' borSat X C) = muF X x1 (cpt X x1 ⁻¹' borSat X C) := by
  have hS := measurableSet_borSat X hK hC
  have h := hI r X x0 x1 h0 h1 ((borSat X C).indicator 1) (measurable_one.indicator hS) (by
    intro x _ b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS)]
      rfl
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x0).measurable hS),
    ← lintegral_indicator_one ((FundSetPf.cont_cpt X x1).measurable hS)]
  exact h

theorem muF_sat_lt_top (hI : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (hx0 : IsOrth X x0) (C : Set (Frame X.Ψ r)) (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (sat X x0 C) < ⊤ := by
  rw [sat_eq_preimage X x0 hC]
  refine hK.induction_on (p := fun s => muF X x0 (cpt X x0 ⁻¹' borSat X s) < ⊤) ?_ ?_ ?_ ?_
  · have : borSat X (∅ : Set (Frame X.Ψ r)) = ∅ := by
      ext y; simp [borSat]
    simp [this]
  · intro s t hst ht
    refine (measure_mono fun z hz => ?_).trans_lt ht
    obtain ⟨x, hx, h⟩ := hz
    exact ⟨x, hst hx, h⟩
  · intro s t hs ht
    refine (measure_mono (t := cpt X x0 ⁻¹' borSat X s ∪ cpt X x0 ⁻¹' borSat X t)
      fun z hz => ?_).trans_lt (measure_union_lt_top hs ht)
    obtain ⟨x, hx | hx, h⟩ := hz
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · intro x hx
    have hxd := hC hx
    obtain ⟨x1, hx1, b1, hb1, hxe⟩ := ortho_holds r X x hxd
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, huniq⟩ := lu_holds r X x1 hx1
    have h0 := IW.zero_mem_OmF X x1 hx1
    obtain ⟨u1, u2, -⟩ := huniq 0 h0 b1 hb1
    rw [IW.cpt_zero, ← hxe] at u1 u2
    obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((OntoB.isOpen_OmF X x1).mem_nhds h0)
    have hW : {y | y ∈ X.dom ∧ Δ y ≠ 0} ∈ 𝓝 x :=
      ((FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)).mem_nhds
        ⟨hxd, u1⟩
    have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt hW
    have hV : zOf ⁻¹' Metric.closedBall 0 ρ ∈ 𝓝 x :=
      hzc.preimage_mem_nhds (by rw [u2]; exact Metric.closedBall_mem_nhds _ hρ)
    refine ⟨{y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ,
      mem_nhdsWithin_of_mem_nhds (Filter.inter_mem hW hV), ?_⟩
    have hKc : IsCompact (cpt X x1 '' Metric.closedBall 0 ρ) :=
      (isCompact_closedBall _ _).image (FundSetPf.cont_cpt X x1)
    have hKd : cpt X x1 '' Metric.closedBall 0 ρ ⊆ X.dom := by
      rintro _ ⟨z, hz, rfl⟩
      exact hball hz
    calc muF X x0 (cpt X x0 ⁻¹' borSat X
          ({y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ))
        ≤ muF X x0 (cpt X x0 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨y, ⟨⟨hyd, hyΔ⟩, hyz⟩, b, hb, h⟩ := hz
          obtain ⟨-, hb', hy⟩ := hdec y hyd hyΔ
          refine ⟨_, ⟨zOf y, hyz, rfl⟩, rmul (bOf y) b, ExtFPf.mul_mem X hb' hb, ?_⟩
          rw [← ExtFPf.rmul_assoc, ← hy, h]
      _ = muF X x1 (cpt X x1 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) :=
          muF_borSat_eq hI X hx0 hx1 hKc hKd
      _ ≤ muF X x1 (Metric.closedBall 0 ρ) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨_, ⟨z', hz', rfl⟩, b, hb, h⟩ := hz
          rw [← ExtFPf.rmul_oneF X (cpt X x1 z)] at h
          rwa [FundSetPf.cpt_uniq X hx1 (ExtFPf.oneF_mem X) hb h]
      _ < ⊤ := muF_lt_top_of_isCompact X x1 (isCompact_closedBall _ _) hball

end GlobalTheory.SatFin
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def uStabSubgroup {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Subgroup (GL (Fin r) E) where
  carrier := {γ | IsUStab G Λ γ}
  one_mem' := by simp [IsUStab]
  mul_mem' := fun {γ δ} hγ hδ => by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.1, hδ.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hγ.2, ← hδ.2]
  inv_mem' := fun h => isUStab_inv h


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ Γ : Subgroup H, ∀ g : H, g ∈ Γ ↔ (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1)) := by
  intro r X H _
  refine ⟨((_root_.GlobalTheory.FiniteCovolume.uStabSubgroup X.Gm X.Λ).map (_root_.GlobalTheory.FiniteCovolume.embGL X.Ψ)).comap
    H.subtype, fun g => ?_⟩
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, fun τ => ?_⟩
    rw [← hg, _root_.GlobalTheory.FiniteCovolume.embGL_val]
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, funext fun τ => Units.ext ?_⟩
    rw [_root_.GlobalTheory.FiniteCovolume.embGL_val, hg]

end GlobalTheory.FiniteCovolume
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_bound_orthonormal_frame_mahler : (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x → ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  first | exact @GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | exact GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame | (intros; apply GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lintegral_fundSet_inter_le : MeasInvStatement (E := E) → ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r), IsOrth X x0 → IsOrth X x1 →
    ∀ FF, IsFundSet X x0 FF → ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (lact γ (rmul x b)) = φ x) →
    ∀ N : Set (V (nd X)), MeasurableSet N → N ⊆ OmF X x1 →
    ∫⁻ z in FF ∩ {z | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x1 y) b)},
      φ (cpt X x0 z) ∂muF X x0 ≤ ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 := by
  intro hM r X x0 x1 ho0 ho1 FF hF φ hφ hinv N hN hNO
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := fun x hx b hb => by
    have h := hinv 1 X.Γ.one_mem x hx b hb
    rwa [FundSetPf.lact_one] at h
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x1 N).indicator φ
  have hψ : Measurable ψ := hφ.indicator (measurableSet_satFrames X ho1 hN hNO)
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x1 N _ hb, hφB x hx b hb]
  have h1 : ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 = ∫⁻ y, ψ (cpt X x1 y) ∂muF X x1 := by
    rw [← lintegral_indicator hN]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho1]
  rw [h1, ← hM r X x0 x1 ho0 ho1 ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB]
  refine le_trans (setLIntegral_mono (g := fun z => ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z))) ?_ ?_)
    (lintegral_mono_set Set.inter_subset_left)
  · exact Measurable.tsum fun γ => (hψ.comp (continuous_lact X γ.1).measurable).comp hc
  · rintro z ⟨-, y, hy, γ, hγ, b, hb, h⟩
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ⁻¹, X.Γ.inv_mem hγ⟩ : X.Γ))
    have hm : rmul (cpt X x1 y) b ∈ satFrames X x1 N := ⟨y, hy, b, hb, rfl⟩
    show φ (cpt X x0 z) = ψ (lact γ⁻¹ (cpt X x0 z))
    rw [h, FundSetPf.lact_inv, hinv γ hγ _ (hNO hy) b hb]
    show _ = (satFrames X x1 N).indicator φ _
    rw [Set.indicator_of_mem hm, hφB _ (hNO hy) b hb]

end GlobalTheory.Unfold
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitary_elem_of_isUStab :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∃ g : H, ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) :=
  fun _ X _ hH γ hγ =>
    ⟨⟨embGL X.Ψ γ, (hH _).mpr (isUnitaryC_of_isUStab X hγ)⟩, fun τ => embGL_val X.Ψ γ τ⟩

end GlobalTheory.FiniteCovolume
end
