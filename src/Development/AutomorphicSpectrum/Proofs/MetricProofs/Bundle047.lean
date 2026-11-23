module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle001
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreMoment
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
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
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def genLin : MvPolynomial (Fin 3) (MvPolynomial (Fin 3) ℝ) := ∑ i, X i * C (X i)

def coordHom : MvPolynomial (Fin 3) ℝ →+* (S2 → ℝ) :=
  RingHom.pi fun p : S2 => MvPolynomial.eval fun i => (p : E3) i

theorem coordHom_apply (g : MvPolynomial (Fin 3) ℝ) (p : S2) :
    coordHom g p = MvPolynomial.eval (fun i => (p : E3) i) g := rfl

theorem linear_form_eq_map_eval (n : Fin 3 → ℝ) : lin3 n = MvPolynomial.map (MvPolynomial.eval n) genLin := by

  simp [lin3, genLin, map_sum, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X]

theorem dotPoly_id_eq_map : dotPoly (id : S2 → S2) = MvPolynomial.map coordHom genLin := by

  simp only [dotPoly, genLin, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext p
  rw [coordHom_apply, MvPolynomial.eval_X]
  rfl

theorem linear_expand (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (S : Finset (Fin 3 →₀ ℕ))
    (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q.support ⊆ S) :
    ℓ Q = ∑ m ∈ S, AddMonoidAlgebra.coeff Q m * ℓ (monomial m 1) := by
  calc ℓ Q = ℓ (∑ m ∈ Q.support, monomial m (AddMonoidAlgebra.coeff Q m)) := by rw [support_sum_monomial_coeff]
    _ = ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m * ℓ (monomial m 1) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show monomial m (AddMonoidAlgebra.coeff Q m) = (AddMonoidAlgebra.coeff Q m) • monomial m (1 : ℝ) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    _ = _ := Finset.sum_subset hQ fun m _ hm => by rw [notMem_support_iff.1 hm, zero_mul]

theorem stereo_one : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  intro ℓ N
  have : IsProbabilityMeasure sphereMeasure := GroundTheory.Heights₂.Heights.Inter.FibreLocal.isProbabilityMeasure_sphere
  have key : ∀ f : (Fin 3 → ℝ) → ℝ, Measurable f →
      (Integrable (fun a : ℂ => f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
        Integrable (fun m : S2 => f fun i => (m : E3) i) sphereMeasure) ∧
      ∫ a : ℂ, f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) =
        ∫ m : S2, f (fun i => (m : E3) i) ∂sphereMeasure :=
    fun f hf => (GlobalTheory.T.sphere_measure_stereographic_integral).1 f hf
  obtain ⟨G, hG⟩ : ∃ G, G = genLin ^ N := ⟨_, rfl⟩
  have hlin : ∀ a, lin3 (nS a) ^ N = MvPolynomial.map (MvPolynomial.eval (nS a)) G := fun a => by
    rw [hG, map_pow, linear_form_eq_map_eval]
  have hdot : dotPoly (id : S2 → S2) ^ N = MvPolynomial.map coordHom G := by
    rw [hG, map_pow, dotPoly_id_eq_map]
  rw [hdot]
  have hf : ∀ m, Continuous fun x : Fin 3 → ℝ => MvPolynomial.eval x (AddMonoidAlgebra.coeff G m) :=
    fun m => MvPolynomial.continuous_eval _
  have hcoord : Continuous fun p : S2 => fun i => (p : E3) i := by
    fun_prop
  have hsph : ∀ m, Integrable (fun p : S2 => MvPolynomial.eval (fun i => (p : E3) i) (AddMonoidAlgebra.coeff G m))
      sphereMeasure := fun m =>
    ((hf m).comp hcoord).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpl : ∀ m, Integrable (fun a : ℂ => MvPolynomial.eval (nS a) (AddMonoidAlgebra.coeff G m) *
      (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) := fun m =>
    (key _ (hf m).measurable).1.2 (hsph m)
  have hsupp : (momentPoly sphereMeasure (fun _ => 1) (MvPolynomial.map coordHom G)).support ⊆ G.support := by
    intro m hm
    by_contra h
    rw [mem_support_iff] at hm
    apply hm
    rw [GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly, coeff_map, notMem_support_iff.1 h]
    simp
  rw [linear_expand ℓ G.support _ hsupp, Finset.mul_sum]
  have hpt : ∀ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) = ∑ m ∈ G.support,
      (MvPolynomial.eval (nS a) (AddMonoidAlgebra.coeff G m) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) *
        (Real.pi * ℓ (monomial m 1)) := fun a => by
    rw [hlin, linear_expand ℓ G.support _ (support_map_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_map, wS]
    have hpi := Real.pi_ne_zero
    field_simp
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => (hpl m).mul_const _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, (key _ (hf m).measurable).2,
    GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly]
  simp only [coeff_map, one_mul, coordHom_apply]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.log_resolution_covers_complex_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsArithVar P (e + 1) → ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.resolution_onto_complex_points | exact GlobalTheory.CompanionTheory.Ar.Cmp.resolution_onto_complex_points | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.resolution_onto_complex_points <;> assumption)
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open Set Manifold GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

theorem exists_smooth_weight_const_near_embeddings :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F]
      [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (Λ : (F →+* ℂ) → ℝ), (∀ sg, 0 < Λ sg) →
      (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) →
      ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ,
        LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg := by
  intro K _ ι _ Ω _ F _ _ _ y Λ hpos huniq
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg =>
    {z | z ∈ mcPts (mCoordIdeal y) ∧ LiesOver y sg z}
  let C : (F →+* ℂ) → Set ((Σ k, ι k × ι k) → ℂ) := fun sg => projPt '' S sg
  have hSmul : ∀ sg z (c : K → ℂ), (∀ k, c k ≠ 0) → z ∈ S sg → (fun p => c p.1 * z p) ∈ S sg :=
    fun sg z c hc hz => ⟨mcPts_smul (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) c hc hz.1,
      liesOver_smul hz.2 c⟩
  have hC : ∀ sg, IsCompact (C sg) := by
    intro sg
    have hK : IsCompact (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
      have : S sg ∩ {z | ∀ k, blockNormSq z k = 1} =
          ({z | ∀ f ∈ mCoordIdeal y, eval z (map (Int.castRingHom ℂ) f) = 0} ∩
            {z | LiesOver y sg z}) ∩ {z | ∀ k, blockNormSq z k = 1} := by
        ext z
        simp only [S, mcPts, mem_inter_iff, mem_setOf_eq]
        constructor
        · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
          by_contra hcon
          push_neg at hcon
          have := h3 k
          simp [blockNormSq, hcon] at this
      rw [this]
      exact ((isClosed_zeros _).inter (isClosed_liesOver y sg)).inter
        isCompact_sphere.isClosed
    have heq : C sg = projPt '' (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine Subset.antisymm ?_ (image_mono inter_subset_left)
      rintro e ⟨z, hz, rfl⟩
      obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1.1
      exact ⟨_, ⟨hSmul sg z c hc hz, hc1⟩, projPt_smul c hc z⟩
    rw [heq]
    exact hK.image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hdisj : ∀ sg tg, sg ≠ tg → Disjoint (C sg) (C tg) := by
    intro sg tg hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨hzP, hzs⟩, rfl⟩ ⟨w, ⟨hwP, hwt⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (liesOver_smul hzs c) hwt)
  have hsep : ∀ sg, ∃ χ : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ᶠ e in 𝓝ˢ (⋃ tg ∈ Finset.univ.erase sg, C tg), χ e = 0) ∧
      (∀ᶠ e in 𝓝ˢ (C sg), χ e = 1) := by
    intro sg
    obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
      𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
      (isClosed_biUnion_finset fun tg _ => (hC tg).isClosed) (hC sg).isClosed
      (Set.disjoint_iUnion₂_left.2 fun tg htg => hdisj tg sg (Finset.ne_of_mem_erase htg))
    exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, h0, h1⟩
  choose χ hχs hχ0 hχ1 using hsep
  let g : ((Σ k, ι k × ι k) → ℂ) → ℝ := fun e => ∑ sg, Real.log (Λ sg) * χ sg e
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    ContDiff.sum fun sg _ => contDiff_const.mul (hχs sg)
  have hloc : ∀ sg, ∀ e ∈ C sg, ∀ᶠ e' in 𝓝 e, g e' = Real.log (Λ sg) := by
    intro sg e he
    have : ∀ tg, ∀ᶠ e' in 𝓝 e, χ tg e' = if tg = sg then 1 else 0 := by
      intro tg
      by_cases htg : tg = sg
      · subst htg
        simpa using (hχ1 tg).filter_mono (nhds_le_nhdsSet he)
      · simp only [htg, if_false]
        exact (hχ0 tg).filter_mono (nhds_le_nhdsSet
          (Set.mem_iUnion₂.2 ⟨sg, Finset.mem_erase.2 ⟨Ne.symm htg, Finset.mem_univ _⟩, he⟩))
    filter_upwards [Filter.eventually_all.2 this] with e' he'
    simp only [g, he', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let u : ((Σ k, ι k) → ℂ) → ℝ := fun z => g (projPt z)
  have hu_smul : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) →
      (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z := by
    intro c z hc
    simp only [u, projPt_smul c hc]
  refine ⟨HermLine.ofWeight (fun z => -u z) hu_smul, rfl, ?_, ?_⟩
  · have h1 := hg.comp_contDiffOn (contDiffOn_projPt (ι := ι))
    have hu := h1.neg.neg
    exact Real.contDiff_exp.comp_contDiffOn hu
  · intro z hz sg hsg
    have hzC : projPt z ∈ C sg := ⟨z, ⟨hz, hsg⟩, rfl⟩
    have hcont : ContinuousAt projPt z :=
      contDiffOn_projPt.continuousOn.continuousAt (EmbeddingWeight.isOpen_blockNonzero.mem_nhds hz.1)
    filter_upwards [Filter.Tendsto.eventually hcont (hloc sg _ hzC)] with w hw1
    change Real.exp (-(-u w)) = Λ sg
    simp only [u, hw1, neg_neg, Real.exp_log (hpos sg)]

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degree_of_isIntersectionSystem (II : IntersectionSystem) (hII : IsIntersectionSystem II) :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_iff_degree_statement.mp
    (GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_degree_form_of_existence ⟨II, hII⟩
      GroundTheory.Heights₂.Heights.Inter.Conservation.statement_holds)

theorem degree_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun ⟨II, hII⟩ => degree_of_isIntersectionSystem II hII.1

end GlobalTheory.CompanionTheory.Ar.Giv
end
