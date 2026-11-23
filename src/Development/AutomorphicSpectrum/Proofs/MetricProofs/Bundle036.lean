module

import Development.WeilBound.CoreStatements.FlagImmersions.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle029
public import Development.WeilBound.CoreStatements.RationalSupMetrics.Bundle003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPair
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle031
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem mixedDisc_eq_zero_of_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (j : Fin D)
    (hA : A j = 0) : mixedDisc A = 0 := by
  apply RootFieldNumerics.mixedDisc_eq_zero <;> assumption

theorem cxHessian_zero {D : ℕ} (z : Fin D → ℂ) : cxHessian (fun _ => (0 : ℝ)) z = 0 := by
  have h : fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ))) z = 0 := by
    have h1 : fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      exact fderiv_const_apply 0
    rw [h1]
    exact fderiv_const_apply 0
  ext a b
  simp [cxHessian, h]

theorem sheetDensity_update_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Function.update φ j 0) g y w = 0 := by
  unfold sheetDensity
  split_ifs with hγ
  · have hm : mixedDisc (fun k => cxHessian
        (fun y' => Function.update φ j 0 k (hγ.choose y')) y) = 0 := by
      refine mixedDisc_eq_zero_of_eq_zero _ j ?_
      simpa using cxHessian_zero y
    simp [maDensity, hm]
  · rfl

theorem ptsIntegral_eq_zero_of_locConst :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
      (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e),
      (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  intro K _ ι _ P e φ g j hj
  have hshift : ∀ i, ∀ z ∈ mcPts P, ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, φ i u = Function.update φ j 0 i u + c := by
    intro i z hz
    by_cases hi : i = j
    · subst hi
      obtain ⟨c, hc⟩ := hj z hz
      refine ⟨c, hc.mono fun u hu => ?_⟩
      simpa using hu
    · exact ⟨0, Eventually.of_forall fun u => by simp [Function.update_of_ne hi]⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.ptsIntegral_add_locConst P hshift g]
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity_update_zero]
  · rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' :=
  @PositivityTheory.Xgp.inChart_iff_inChart_map_of_dominates
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap

theorem isFlagVBOn_pull_of_map : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (E E₁ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (ι : E →ₗ[Ω] E₁) (π : E₁ →ₗ[Ω] E) (L : Lat ξ E) (r : ℕ) (c : Fin r → E) (u : Matrix (Fin r) (Fin r) G), π ∘ₗ ι = LinearMap.id → ((L.map ι).pull ξ' f (TensorProduct.mk Ω G E₁ 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) → (L.pull ξ' f (TensorProduct.mk Ω G E 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E 1 (c l)) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_pullmap

end GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem defect_exists_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) :=
  @PositivityTheory.UnitarySelfGeneration.i_defect

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]


omit [CompactSpace X] [T2Space X] in
theorem chartPartition_norm_le_one (A : FinHolAtlas e X) (Q : ChartPartition A) (j : Fin A.n)
    (x : X) : ‖Q.χ j x‖ ≤ 1 := by
  have h : Q.χ j x ≤ ∑ k, Q.χ k x :=
    Finset.single_le_sum (f := fun k => Q.χ k x) (fun k _ => Q.nonneg k x) (Finset.mem_univ j)
  rw [Q.sum_eq_one] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (Q.nonneg j x)]
  exact h

theorem chartTerm_integrableOn (A : FinHolAtlas e X) (Q : ChartPartition A) (P : Fin e → LocPot X)
    (g : X → ℝ) (hg : MIntegrable A P g) (j : Fin A.n) :
    IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j).target := by
  have hK : IsCompact (A.chart j '' tsupport (Q.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Q.tsupport_subset j))
  have hKt : A.chart j '' tsupport (Q.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Q.tsupport_subset j hx)
  have h0 := hg j _ hKt hK
  have hcont : ContinuousOn (fun y => Q.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (Q.smooth j j).continuousOn
    simpa [Function.comp_def] using h
  have hm : AEStronglyMeasurable (fun y => Q.χ j ((A.chart j).symm y))
      (volume.restrict (A.chart j '' tsupport (Q.χ j))) :=
    (hcont.mono hKt).aestronglyMeasurable hK.measurableSet
  have h1 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * (g ((A.chart j).symm y) * locDens A P j y))
      (A.chart j '' tsupport (Q.χ j)) :=
    Integrable.bdd_mul (c := 1) h0 hm (ae_of_all _ fun y => chartPartition_norm_le_one A Q j _)
  have h2 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j '' tsupport (Q.χ j)) := by
    simpa only [mul_assoc] using h1
  refine IntegrableOn.of_forall_sdiff_eq_zero h2 (A.chart j).open_target.measurableSet ?_
  rintro y ⟨hy, hyK⟩
  have hn : (A.chart j).symm y ∉ tsupport (Q.χ j) := fun hmem =>
    hyK ⟨_, hmem, (A.chart j).right_inv hy⟩
  rw [image_eq_zero_of_notMem_tsupport hn]
  ring

theorem chartTerm_hasSum (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ))
    (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (Q : ChartPartition A)
    (hc : IsParamCover A V B Φ) (hC2 : ∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z))
    (hg : MIntegrable A P g) (j : Fin A.n) :
    (∀ n, IntegrableOn (fun z => Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧
      HasSum (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z)
        (∫ y in (A.chart j).target,
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y) := by
  obtain ⟨hpar, hB, hdisj, hnull⟩ := hc
  have hf := chartTerm_integrableOn A Q P g hg j
  have hCm : ∀ n, MeasurableSet (B n ∩ Φ n ⁻¹' (A.chart j).source) := by
    intro n
    have hO : IsOpen (V n ∩ Φ n ⁻¹' (A.chart j).source) :=
      (hpar n).2.1.isOpen_inter_preimage (hpar n).1 (A.chart j).open_source
    have hEq : B n ∩ Φ n ⁻¹' (A.chart j).source = B n ∩ (V n ∩ Φ n ⁻¹' (A.chart j).source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hB n).2 h1, h2⟩
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩
    rw [hEq]
    exact (hB n).1.inter hO.measurableSet
  have key := fun n => GlobalTheory.T.monge_ampere_chart_density_integral e X A (V n) (B n ∩ Φ n ⁻¹' (A.chart j).source) (Φ n) P
    (fun x => Q.χ j x * g x) j (hpar n) (hCm n) (fun z hz => (hB n).2 hz.1) (fun z hz => hz.2)
    (fun z hz => hC2 n z hz.1)
  have hsub : ∀ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source) ⊆
      (A.chart j).target := by
    rintro n _ ⟨z, hz, rfl⟩
    exact (A.chart j).map_source hz.2
  have hzero : ∀ n, ∀ z ∈ B n \ (B n ∩ Φ n ⁻¹' (A.chart j).source),
      Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z = 0 := by
    rintro n z ⟨hz, hz'⟩
    have hn : Φ n z ∉ tsupport (Q.χ j) := fun hmem =>
      hz' ⟨hz, Q.tsupport_subset j hmem⟩
    rw [image_eq_zero_of_notMem_tsupport hn]
    ring
  have hdis : Pairwise (Function.onFun Disjoint fun n =>
      (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have hEq : Φ n z = Φ m w := by
      refine (A.chart j).injOn hz.2 hw.2 ?_
      exact hzw.symm
    exact Set.disjoint_left.1 (hdisj hnm) ⟨z, hz.1, rfl⟩ ⟨w, hw.1, hEq.symm⟩
  have hUsub : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) ⊆
      (A.chart j).target := Set.iUnion_subset hsub
  have hsum := hasSum_integral_iUnion (fun n => (key n).1) hdis (hf.mono_set hUsub)
  have hUeq : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) =ᵐ[volume]
      (A.chart j).target := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.2 hUsub]
      exact measure_empty
    · refine measure_mono_null ?_ (hnull j)
      rintro y ⟨hy, hyU⟩
      refine ⟨hy, ?_⟩
      intro hmem
      obtain ⟨_, ⟨n, rfl⟩, z, hz, hzy⟩ := hmem
      refine hyU (Set.mem_iUnion.2 ⟨n, z, ⟨hz, ?_⟩, ?_⟩)
      · show Φ n z ∈ (A.chart j).source
        rw [hzy]
        exact (A.chart j).map_target hy
      · show A.chart j (Φ n z) = y
        rw [hzy]
        exact (A.chart j).right_inv hy
  rw [setIntegral_congr_set hUeq] at hsum
  constructor
  · intro n
    refine IntegrableOn.of_forall_sdiff_eq_zero
      ((key n).2.1.1 (hf.mono_set (hsub n))) (hB n).1 (hzero n)
  · have hEq : (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∫ y in (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source),
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
      funext n
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hB n).1 Set.inter_subset_left
        (hzero n)]
      exact ((key n).2.2).symm
    rw [hEq]
    exact hsum

theorem integrableOn_hasSum_paramCover : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ)) (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ), IsParamCover A V B Φ → (∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z)) → MIntegrable A P g → (∀ n, IntegrableOn (fun z => g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧ HasSum (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) (mInt A P g) := by
  intro e X _ _ _ A V B Φ P g hc hC2 hg
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A P g = ∑ j, ∫ y in (A.chart j).target,
      hne.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
    rw [mInt, dite_eq_left hne, integralWith]
  have hj := fun j => chartTerm_hasSum A V B Φ P g hne.some hc hC2 hg j
  have hpt : ∀ n z, g (Φ n z) * paramDens P (Φ n) z =
      ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
    intro n z
    rw [← Finset.sum_mul, ← Finset.sum_mul, hne.some.sum_eq_one, one_mul]
  have hfun : ∀ n, (fun z => g (Φ n z) * paramDens P (Φ n) z) =
      fun z => ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z :=
    fun n => funext (hpt n)
  constructor
  · intro n
    rw [hfun n]
    exact integrable_finsetSum _ fun j _ => (hj j).1 n
  · rw [hm]
    have hs := hasSum_sum (s := Finset.univ) fun j _ => (hj j).2
    have hEq : (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∑ j, ∫ z in B n, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
      funext n
      rw [hfun n]
      exact integral_finsetSum _ fun j _ => (hj j).1 n
    rw [hEq]
    exact hs

end

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.monge_ampere_difference_tendsto_zero : ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e (σ ⊕ σ)) (d : σ → S.X → ℝ), (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → ∀ (a : σ) (w : Fin e → σ ⊕ σ), Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x)) (𝓝[>] 0) (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.an_two_weights_close | exact GlobalTheory.CompanionTheory.Ar.PB.an_two_weights_close | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.an_two_weights_close <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem _root_.GlobalTheory.T.exists_form_defining_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), Birational y → IsRelevant (mCoordIdeal y) → ∀ (a : K → ℤ) (s : Ω), ∃ h : MRing ι, IsFormOff (mCoordIdeal y) h ∧ ∀ (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜), aeval z h ≠ 0 → ∃ w, HasVal y a s z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal | exact GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.exists_form_hasVal <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem shiftH_props : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) :=
  @MultiProjectiveCoordinates.shiftH_smooth_nef_gen

end GlobalTheory.CompanionTheory.Ar.Small
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem hasVal_read_of_rep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w :=
  MultiProjectiveCoordinates.valuation_unique_on_forms

end GlobalTheory.CompanionTheory.Ar.Small
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.metric_quotient_of_multihomog_pair : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → (∀ y : R.X, aeval (R.lift y y) G ≠ (0 : ℂ) → aeval (R.lift y y) Hf ≠ (0 : ℂ) → π y ∈ S.open') → ∀ x₀ : R.X, aeval (R.lift x₀ x₀) Hf ≠ (0 : ℂ) → ∃ (V : Set R.X) (N : ℕ) (C : ℝ), IsOpen V ∧ x₀ ∈ V ∧ 0 < N ∧ ∀ y ∈ V, aeval (R.lift y y) Hf ≠ (0 : ℂ) ∧ (π y ∈ S.open' → aeval (R.lift y y) G ≠ (0 : ℂ) → Real.log ‖(aeval (R.lift y y) G : ℂ) / aeval (R.lift y y) Hf‖ - Real.log (Eh.h (R.lift y y)) ≤ -(1 / (2 * (N : ℝ))) * rW S.L S.s (π y) + C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | exact GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.Decay.local_decay <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.flag_potential_levi_form_cell :
    ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ),
    let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j)
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧
      levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w =
        ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2)
          then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | exact GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Measurability

theorem countable_submodule (A : Type) [Ring A] (Λ : Type) [AddCommGroup Λ] [Module A Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] : Countable (Submodule A Λ) := by
  have hΛ : Countable Λ :=
    (Module.finBasis ℤ Λ).equivFun.toEquiv.injective.countable
  have hZ : Countable (Submodule ℤ Λ) := by
    have hs : Function.Surjective (fun s : Finset Λ => Submodule.span ℤ (s : Set Λ)) := by
      intro N
      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
      exact ⟨s, hs⟩
    exact hs.countable
  exact (Submodule.restrictScalars_injective ℤ A Λ).countable

theorem measurable_cuspW (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [MeasurableSpace X] (R : X → RiemLat E g Λ)
    (σ : Ψ → (𝓞 E →+* ℂ)) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (hform : ∀ x, (R x).form = form)
    (hnz : ∀ I, Measurable fun x => (R x).nz σ I)
    (_hbdd : ∀ x, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)}) :
    Measurable fun x => (R x).cuspW σ := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact measurable_of_empty _
  haveI := (R x₀).free
  haveI := (R x₀).fin
  haveI : Countable (Submodule (𝓞 E) Λ) := countable_submodule (𝓞 E) Λ
  let C : Submodule (𝓞 E) Λ → Prop := fun I => I ≠ ⊥ ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsSaturated I ∧
    GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub form I
  have hC : ∀ x I, (R x).IsCusp I ↔ C I := by
    intro x I
    simp only [RiemLat.IsCusp, C, hform x]
  have hset : ∀ x, {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)} =
      Set.range fun I : {I // C I} => -Real.log ((R x).nz σ I.1) := by
    intro x
    ext y
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨⟨I, (hC x I).1 hI⟩, rfl⟩
    · rintro ⟨I, rfl⟩
      exact ⟨I.1, (hC x I.1).2 I.2, rfl⟩
  have hsup : Measurable fun x => ⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1) :=
    Measurable.iSup fun I => (Real.measurable_log.comp (hnz I.1)).neg
  have heq : (fun x => (R x).cuspW σ) = fun x => max 0 (⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1)) := by
    funext x
    simp only [RiemLat.cuspW, hset x, iSup]
  rw [heq]
  exact measurable_const.max hsup

end GlobalTheory.CompanionTheory.Ar.Cusp.Measurability
end
