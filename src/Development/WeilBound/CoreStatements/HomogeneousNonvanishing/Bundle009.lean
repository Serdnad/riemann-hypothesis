module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle005
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflagLU
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

private theorem continuousOn_levi_of_contDiffOn' {e : ℕ} (d : (Fin e → ℂ) → ℝ) (c : Fin e → ℂ) (r : ℝ) (w : Fin e → ℂ)
    (hd2 : ContDiffOn ℝ 2 d (Metric.ball c r)) :
    ContinuousOn (fun v => ReciprocityTheory.AnForm.levi d v w) (Metric.ball c r) := by
  have hc0 := ReciprocityTheory.AnForm.continuousOn_levi Metric.isOpen_ball hd2
  refine hc0.comp (f := fun v : Fin e → ℂ => (v, w)) ?_ ?_
  · exact (continuous_id.prodMk continuous_const).continuousOn
  · intro v hv
    exact Set.mk_mem_prod hv (Set.mem_univ w)

open HolomorphicMinorCharts ReciprocityTheory.AnForm in
theorem r_pluri : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P Q : LocPot X), IsPotential A P → IsPotential A Q → IsOpen U → Dense U → SamePot A U P Q → SamePot A Set.univ P Q := by
  intro e X _ _ _ A U P Q hP hQ hUo hUd hS x _
  obtain ⟨j, hxj⟩ := A.cover x
  set ψ := A.chart j with hψ
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) :=
    ψ.isOpen_inter_preimage_symm ((P.isOpen_U x).inter (Q.isOpen_U x))
  have hxO : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x) := by
    refine ⟨ψ.map_source hxj, ?_⟩
    show ψ.symm (ψ x) ∈ P.U x ∩ Q.U x
    rw [ψ.left_inv hxj]
    exact ⟨P.mem_U x, Q.mem_U x⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO (ψ x) hxO
  set d : (Fin e → ℂ) → ℝ := fun z => P.φ x (ψ.symm z) - Q.φ x (ψ.symm z) with hdd
  have h1 := (hP.1 x j).mono (fun v (hv : v ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) => (⟨hv.1, hv.2.1⟩ : v ∈ ψ.target ∩ ψ.symm ⁻¹' P.U x))
  have h2 := (hQ.1 x j).mono (fun v (hv : v ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x)) => (⟨hv.1, hv.2.2⟩ : v ∈ ψ.target ∩ ψ.symm ⁻¹' Q.U x))
  have hd2 : ContDiffOn ℝ 2 d (Metric.ball (ψ x) r) :=
    ((h1.sub h2).mono hball).of_le (WithTop.coe_le_coe.mpr le_top)
  clear_value d
  clear h1 h2
  have hzero : ∀ z ∈ ψ.target ∩ ψ.symm ⁻¹' (P.U x ∩ Q.U x), ψ.symm z ∈ U → ∀ w, levi d z w = 0 := by
    intro z hz hzU w
    have hyPx : ψ.symm z ∈ P.U x := hz.2.1
    have hyQx : ψ.symm z ∈ Q.U x := hz.2.2
    obtain ⟨W1, hW1o, hyW1, G1, hG1, hEq1⟩ := hP.2 x (ψ.symm z) (ψ.symm z) ⟨hyPx, P.mem_U _⟩
    obtain ⟨W2, hW2o, hyW2, G2, hG2, hEq2⟩ := hQ.2 x (ψ.symm z) (ψ.symm z) ⟨hyQx, Q.mem_U _⟩
    obtain ⟨V3, hV3o, hyV3, G3, hG3, hEq3⟩ := hS (ψ.symm z) hzU
    have hNo : IsOpen (W1 ∩ W2 ∩ V3 ∩ P.U x ∩ P.U (ψ.symm z) ∩ Q.U x ∩ Q.U (ψ.symm z)) :=
      ((((((hW1o.inter hW2o).inter hV3o).inter (P.isOpen_U x)).inter (P.isOpen_U _)).inter
        (Q.isOpen_U x)).inter (Q.isOpen_U _))
    have hyN : ψ.symm z ∈ W1 ∩ W2 ∩ V3 ∩ P.U x ∩ P.U (ψ.symm z) ∩ Q.U x ∩ Q.U (ψ.symm z) :=
      ⟨⟨⟨⟨⟨⟨hyW1, hyW2⟩, hyV3⟩, hyPx⟩, P.mem_U _⟩, hyQx⟩, Q.mem_U _⟩
    have hH : AnalyticAt ℂ (fun v => G1 (ψ.symm v) - G2 (ψ.symm v) + G3 (ψ.symm v)) z :=
      ((hG1 j z ⟨hz.1, hyW1⟩).sub (hG2 j z ⟨hz.1, hyW2⟩)).add (hG3 j z ⟨hz.1, hyV3⟩)
    have hev : d =ᶠ[𝓝 z] fun v => (G1 (ψ.symm v) - G2 (ψ.symm v) + G3 (ψ.symm v)).re := by
      have hmem := (ψ.continuousAt_symm hz.1).preimage_mem_nhds (hNo.mem_nhds hyN)
      filter_upwards [hmem] with v hv
      obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := hv
      have e1 := hEq1 _ ⟨⟨a1, a4⟩, a5⟩
      have e2 := hEq2 _ ⟨⟨a2, a6⟩, a7⟩
      have e3 := hEq3 _ a3
      simp only [hdd, Complex.add_re, Complex.sub_re]
      linarith
    rw [levi_congr hev w]
    exact levi_re_analytic hH w
  have hlevi : ∀ z ∈ Metric.ball (ψ x) r, ∀ w, levi d z w = 0 := by
    intro z hz w
    by_contra hne
    have hcw := continuousOn_levi_of_contDiffOn' d (ψ x) r w hd2
    have hca : ContinuousAt (fun v => levi d v w) z := hcw.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    have hM : (fun v => levi d v w) ⁻¹' {b | b ≠ 0} ∩ Metric.ball (ψ x) r ∈ 𝓝 z :=
      Filter.inter_mem (hca.preimage_mem_nhds (isOpen_ne.mem_nhds hne)) (Metric.isOpen_ball.mem_nhds hz)
    obtain ⟨M, hMsub, hMo, hzM⟩ := mem_nhds_iff.mp hM
    have hzt : z ∈ ψ.target := (hball (hMsub hzM).2).1
    have hne2 : (ψ.source ∩ ψ ⁻¹' M).Nonempty := by
      refine ⟨ψ.symm z, ψ.map_target hzt, ?_⟩
      show ψ (ψ.symm z) ∈ M
      rw [ψ.right_inv hzt]
      exact hzM
    obtain ⟨u, ⟨hus, huM⟩, huU⟩ := hUd.inter_open_nonempty _ (ψ.isOpen_inter_preimage hMo) hne2
    have hvM := hMsub huM
    apply hvM.1
    apply hzero (ψ u) (hball hvM.2)
    rw [ψ.left_inv hus]
    exact huU
  obtain ⟨G0, hG0an, hG0eq⟩ := exists_re_of_levi_zero hr hd2 hlevi
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) r, ψ.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hxj, Metric.mem_ball_self hr⟩, fun y => G0 (ψ y), ?_, ?_⟩
  · exact holoOn_of_compat (isCompatChart_chart A j) Set.inter_subset_left (fun y hy => hG0an _ hy.2)
  · intro y hy
    have h := hG0eq (ψ y) hy.2
    simp only [hdd, ψ.left_inv hy.1] at h
    exact h

end PositivityTheory.UnitarySelfGeneration
end

section

open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {S : Type} {r : S → ℕ} {Ω : Type} [Field Ω]

abbrev Idx (r : S → ℕ) : Type := Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1}

abbrev ent {F : Type} (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) : Idx r → F := fun q => u q.1 q.2.1.1 q.2.1.2

noncomputable def gen (Ω : Type) [Field Ω] (r : S → ℕ) (σ : S) :
    Matrix (Fin (r σ)) (Fin (r σ)) (MvPolynomial (Idx r) Ω) :=
  Matrix.of fun l k => if h : k < l then MvPolynomial.X ⟨σ, ⟨(l, k), h⟩⟩ else if l = k then 1 else 0

theorem gen_map {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) :
    (gen Ω r σ).map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom = u σ := by
  ext l k
  simp only [gen, map_apply, of_apply]
  split_ifs with h1 h2
  · simp [ent]
  · subst h2; simp [(hu σ).1]
  · simp [(hu σ).2 l k (lt_of_le_of_ne (not_lt.1 h1) h2)]

theorem general_of_indep {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (hg : ∀ σ, (g σ).det ≠ 0) (σ : S) (k : Fin (r σ)) :
    (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det ≠ 0 := by
  choose w hw hw' using fun σ => exists_general (g σ) (hg σ)
  have key : ∀ (F : Type) [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F),
      (∀ σ, Uni (u σ)) → (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det =
        MvPolynomial.aeval (R := Ω) (ent u) (trunc k ((g σ).map MvPolynomial.C * gen Ω r σ)).det := by
    intro F _ _ u hu
    have := det_trunc_map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom k ((g σ).map MvPolynomial.C * gen Ω r σ)
    rw [Matrix.map_mul, gen_map u hu σ, Matrix.map_map] at this
    have e : (⇑(MvPolynomial.aeval (R := Ω) (ent u)).toRingHom ∘ ⇑MvPolynomial.C) = algebraMap Ω F := by
      funext a
      simp
    rw [e] at this
    exact this
  intro h0
  rw [key F u hu, map_eq_zero_iff _ hi] at h0
  exact hw' σ k (by rw [key _ w hw, h0, map_zero])

theorem mem_adjoin_ent {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) (l k : Fin (r σ)) : u σ l k ∈ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rcases lt_trichotomy l k with h | h | h
  · rw [(hu σ).2 l k h]; exact zero_mem _
  · rw [h, (hu σ).1]; exact one_mem _
  · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), h⟩⟩, rfl⟩

theorem adjoin_all {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) :
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω (Set.range (ent u)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact mem_adjoin_ent u hu _ _ _
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨q.1, q.2.1⟩, rfl⟩

theorem adjoin_le {F : Type} [Field F] [Algebra Ω F] (u u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hu' : ∀ σ, Uni (u' σ)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (C : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) (hC : ∀ σ, Up (C σ))
    (e : ∀ σ, u' σ = (g σ).map (algebraMap Ω F) * u σ * C σ) :
    IntermediateField.adjoin Ω (Set.range (ent u')) ≤ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have := lu_mem (IntermediateField.adjoin Ω (Set.range (ent u))).toSubfield (hC q.1) (e q.1 ▸ hu' q.1)
    (fun i j => by
      rw [Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_ent u hu _ _ _))
  rw [← e q.1] at this
  exact this _ _

theorem change [Finite S] {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u))
    (hf : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (ent u))) F)
    (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω) (hg : ∀ σ, (g σ).det ≠ 0) :
    ∃ u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F, (∀ σ, Uni (u' σ)) ∧ AlgebraicIndependent Ω (ent u') ∧
      IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) ∧
      ∀ σ i, fl (u' σ) i = fl ((g σ).map (algebraMap Ω F) * u σ) i := by
  choose C hC hU using fun σ => exists_lu _ (general_of_indep u hu hi g hg σ)
  have hC0 := fun σ => (dets_of_lu (hC σ) (hU σ)).2.1
  let u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F := fun σ => (g σ).map (algebraMap Ω F) * u σ * C σ
  have heq : IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) := by
    refine le_antisymm (adjoin_le u u' hu hU g C hC fun _ => rfl)
      (adjoin_le u' u hU hu (fun σ => (g σ)⁻¹) (fun σ => (C σ)⁻¹) (fun σ => (hC σ).inv (hC0 σ)) fun σ => ?_)
    simp only [u']
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (hC0 σ)), Matrix.mul_one,
      ← Matrix.mul_assoc, ← Matrix.map_mul, nonsing_inv_mul _ (IsUnit.mk0 _ (hg σ)),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  refine ⟨u', hU, ?_, heq, fun σ i => fl_mul _ _ (hC σ) (hC0 σ) i⟩
  have a1 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u))) F := inferInstance
  have a2 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u'))) F := by rw [heq]; exact a1
  rw [IntermediateField.isAlgebraic_adjoin_iff_top] at a1 a2
  have b1 := hi.isTranscendenceBasis_iff_isAlgebraic.2 a1
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω (ent u') b1.cardinalMk_eq_trdeg.le).1

theorem compositum (K Ω₁ Ω₂ : Type) [Field K] [Field Ω₁] [Field Ω₂] [Algebra K Ω₁] [Algebra K Ω₂]
    [FiniteDimensional K Ω₁] [FiniteDimensional K Ω₂] :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ x, i₁ (algebraMap K Ω₁ x) = i₂ (algebraMap K Ω₂ x)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank K Ω₁ = n₂ * Module.finrank K Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct K Ω₁ Ω₂)
  let Ω₃ := TensorProduct K Ω₁ Ω₂ ⧸ M
  let _ : Field Ω₃ := Ideal.Quotient.field M
  have fin : FiniteDimensional K Ω₃ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  let j₁ : Ω₁ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeLeft
  let j₂ : Ω₂ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeRight
  have e₁ := (letI : Module.Free j₁.fieldRange Ω₃ := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K j₁.fieldRange Ω₃)
  have e₂ := (letI : Module.Free j₂.fieldRange Ω₃ := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K j₂.fieldRange Ω₃)
  have q₁ : Module.finrank K Ω₁ = Module.finrank K j₁.fieldRange :=
    (AlgEquiv.ofInjectiveField j₁).toLinearEquiv.finrank_eq
  have q₂ : Module.finrank K Ω₂ = Module.finrank K j₂.fieldRange :=
    (AlgEquiv.ofInjectiveField j₂).toLinearEquiv.finrank_eq
  rw [← q₁] at e₁
  rw [← q₂] at e₂
  refine ⟨Ω₃, inferInstance, j₁.toRingHom, j₂.toRingHom, fun x => (j₁.commutes x).trans (j₂.commutes x).symm,
    Module.finrank j₁.fieldRange Ω₃, Module.finrank j₂.fieldRange Ω₃, Module.finrank_pos, ?_, rfl, rfl⟩
  rw [mul_comm, e₁, mul_comm, e₂]

theorem compositum' {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] {I : Type}
    (x₁ : I → Ω₁) (x₂ : I → Ω₂) (h₁ : AlgebraicIndependent Ω x₁) (h₂ : AlgebraicIndependent Ω x₂)
    (f₁ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁)
    (f₂ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂) :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ a, i₁ (algebraMap Ω Ω₁ a) = i₂ (algebraMap Ω Ω₂ a)) ∧ (∀ q, i₁ (x₁ q) = i₂ (x₂ q)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁ =
          n₂ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  let K₁ := IntermediateField.adjoin Ω (Set.range x₁)
  let K₂ := IntermediateField.adjoin Ω (Set.range x₂)
  let e : K₁ ≃ₐ[Ω] K₂ := h₁.aevalEquivField.symm.trans h₂.aevalEquivField
  let _ : Algebra K₁ Ω₂ := ((algebraMap K₂ Ω₂).comp e.toRingEquiv.toRingHom).toAlgebra
  have hr : Module.finrank K₁ Ω₂ = Module.finrank K₂ Ω₂ :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl _) rfl
  have : FiniteDimensional K₁ Ω₂ := Module.finite_of_finrank_pos (by rw [hr]; exact Module.finrank_pos)
  obtain ⟨Ω₃, _, i₁, i₂, h, n₁, n₂, hn, e', e₁, e₂⟩ := compositum K₁ Ω₁ Ω₂
  refine ⟨Ω₃, inferInstance, i₁, i₂, fun a => ?_, fun q => ?_, n₁, n₂, hn, hr ▸ e', e₁, e₂⟩
  · refine (h (algebraMap Ω K₁ a)).trans ?_
    congr 1
    change ((e (algebraMap Ω K₁ a) : K₂) : Ω₂) = _
    rw [e.commutes]
    rfl
  · have := h (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)))
    change i₁ (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) : Ω₁) =
      i₂ (e (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))) : Ω₂) at this
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at this
    rw [h₁.aevalEquivField_algebraMap_apply_coe, h₂.aevalEquivField_algebraMap_apply_coe] at this
    simpa using this

theorem fl_coord {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω' E'] (j : E →+ E') (hj : ∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) {n : ℕ} {c c' : Fin n → E}
    (hc' : LinearIndependent Ω' fun k => j (c' k)) {h : Matrix (Fin n) (Fin n) Ω} (hh : ∀ k, c k = ∑ l, h l k • c' l)
    {b : Fin n → E'} {m u : Matrix (Fin n) (Fin n) Ω'} (hb : ∀ k, b k = ∑ l, m l k • j (c l)) {i : ℕ}
    (hf : flagStep Ω' b i = flagStep Ω' (fun k => ∑ l, u l k • j (c' l)) i) :
    fl (h.map (algebraMap Ω Ω') * m) i = fl u i := by
  refine fl_of_indep hc' ?_
  rw [← hf]
  congr 1
  funext k
  rw [hb]
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_smul, hh, map_sum, hj,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end PositivityTheory.UnitarySelfGeneration.GF
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem r_enlarge : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ L L' : LocPot X) (s s' : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), 0 ≤ C₅ → 0 ≤ C → t₀ ≤ Real.exp (-1) → (∀ y, logNormSec L s y ≤ 0) → bdry s ⊆ bdry s' → (∀ y, y ∉ bdry s' → rW L s y ≤ rW L' s' y) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → IsSingWeight A L' s' th ph C₅ ∧ IsRegFamily A Θ L' s' th ph phT C t₀ ∧ IsRegFamilyC2 A s' ph phT := by
  intro e X _ _ _ A Θ L L' s s' th ph phT C₅ C t₀ hC5 hC ht0 hL hsub hrw hS hR hC2
  have hnb : ∀ y, y ∉ bdry s' → y ∉ bdry s := fun y hy h => hy (hsub h)
  have hpos : ∀ y, 0 < rW L s y := by
    intro y
    unfold rW
    have h1 := hL y
    have h2 := Real.exp_pos 1
    linarith
  obtain ⟨hpot, hsm, hpsh, hb⟩ := hS
  obtain ⟨h0, h1, hf⟩ := hR
  refine ⟨⟨hpot, ?_, ?_, ?_⟩, ⟨h0, h1, ?_⟩, ?_⟩
  · intro j
    exact (hsm j).mono (fun z hz => ⟨hz.1, hnb _ hz.2⟩)
  · intro x j y hy w
    exact hpsh x j y ⟨hy.1, hy.2.1, hnb _ hy.2.2⟩ w
  · intro y hy
    obtain ⟨hlo, hhi⟩ := hb y (hnb y hy)
    refine ⟨?_, hhi⟩
    have hlog : Real.log (rW L s y) ≤ Real.log (rW L' s' y) := Real.log_le_log (hpos y) (hrw y hy)
    nlinarith [mul_le_mul_of_nonneg_left hlog hC5]
  · intro t ht htt
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hf t ht htt
    have hte : t ≤ Real.exp (-1) := le_trans htt ht0
    have h1t : Real.exp 1 ≤ 1 / t := by
      rw [le_div_iff₀ ht]
      calc Real.exp 1 * t ≤ Real.exp 1 * Real.exp (-1) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
    have hL1 : 1 ≤ Real.log (1 / t) := by
      have h := Real.log_le_log (Real.exp_pos 1) h1t
      rwa [Real.log_exp] at h
    have heps : 0 ≤ epsT C t := by
      unfold epsT
      exact div_nonneg (mul_nonneg hC (Real.log_nonneg hL1)) (by linarith)
    refine ⟨a1, a2, fun y hy => a3 y (hnb y hy), a4, a5, ?_, ?_, a8⟩
    · intro y hy hle
      exact a6 y (hnb y hy) (le_trans (hrw y hy) hle)
    · intro y hy
      have h7 := a7 y (hnb y hy)
      nlinarith [mul_le_mul_of_nonneg_left (hrw y hy) heps]
  · intro j K hK hKc
    exact hC2 j K (fun z hz => ⟨(hK hz).1, hnb _ (hK hz).2⟩) hKc

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem madens_hess {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E ≃L[ℝ] E) (φ : E → ℝ) (y u v : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ c)) y u v = fderiv ℝ (fderiv ℝ φ) (c y) (c u) (c v) := by
  set e : (E →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ) := c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with he
  have h1 : fderiv ℝ (φ ∘ c) = e ∘ fderiv ℝ φ ∘ c := by
    funext z
    rw [c.comp_right_fderiv]
    ext w
    simp [he]
  rw [h1, e.comp_fderiv, c.comp_right_fderiv]
  simp [he]

theorem madens_cx (D : ℕ) (φ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    cxHessian (fun y' => φ (fun i => starRingEnd ℂ (y' i))) y =
      (cxHessian φ (fun i => starRingEnd ℂ (y i))).map (starRingEnd ℂ) := by
  let c : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := ContinuousLinearEquiv.piCongrRight (fun _ => Complex.conjCLE)
  have hc : ∀ z, c z = fun i => starRingEnd ℂ (z i) := fun z => rfl
  have hf : (fun y' : Fin D → ℂ => φ (fun i => starRingEnd ℂ (y' i))) = φ ∘ c := by
    funext z; simp [hc]
  have h1 : ∀ i : Fin D, c (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have h2 : ∀ i : Fin D, c (Complex.I • Pi.single i 1) = -(Complex.I • Pi.single i 1) := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  ext i j
  simp only [cxHessian, Matrix.map_apply, hf, madens_hess, h1, h2, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rw [hc y]
  generalize fderiv ℝ (fderiv ℝ φ) (fun i => starRingEnd ℂ (y i)) = H
  simp only [map_div₀, map_add (f := _), map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem c_madens : ∀ (D : ℕ) (φ : Fin D → (Fin D → ℂ) → ℝ) (y : Fin D → ℂ), maDensity (fun j y' => φ j (fun i => starRingEnd ℂ (y' i))) y = maDensity φ (fun i => starRingEnd ℂ (y i)) := by
  intro D φ y
  have key : ∀ A : Fin D → Matrix (Fin D) (Fin D) ℂ,
      mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
    intro A

    simp only [mixedDisc, map_mul, map_div₀, map_one, map_natCast, map_sum, map_pow, map_neg]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [Matrix.sum_apply]
  simp only [maDensity, madens_cx, key, Complex.conj_re]

end PositivityTheory.UnitarySelfGeneration
end
