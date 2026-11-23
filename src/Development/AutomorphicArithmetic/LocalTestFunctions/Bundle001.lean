module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle001
import GroundTheory.AutomorphicForms.WhittakerGroups
import GroundTheory.GlobalFields.Bundle001
import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_testFunction_integral_local_factor :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure] (J : Subgroup (Gw n w)), CO J →
          ∀ (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ), (∀ k ∈ J, ∀ x, ψ (x * k) = ψ x) →
          ∀ (R : AdelicGLn.FiniteAdelicGL K n → ℂ), (∀ y x, R (AdelicGLn.localEmbedding w y * x) = R x) →
          ∀ e₀ : TF K n, (∀ x, e₀ x = R x * (J : Set (Gw n w)).indicator 1 (finAt w (finEmb K n x))) →
          ∃ g : TF K n, (∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x)))) ∧
            (∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m) ∧
            ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (AdelicGLn.FiniteAdelicGL K n) H),
              π.integrated m (UnitaryRep.ccToL1 m g) =
                (π.compHom (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) ∘L
                  π.integrated m (UnitaryRep.ccToL1 m e₀) := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro K _ _ n m _ w _ _ mw _ J hJ ψ hψ R hR e₀ he₀
    have hp := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
    obtain ⟨g, hg, -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.homConv _ _ (AdelicGLn.localEmbedding w) hp m mw ψ e₀
    have hJm : MeasurableSet (J : Set (Gw n w)) := hJ.2.measurableSet
    have hval : ∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x))) := by
      intro x
      set a := finAt w (finEmb K n x) with ha
      have hfa : ∀ y, finAt w (finEmb K n ((AdelicGLn.localEmbedding w y)⁻¹ * x)) = y⁻¹ * a := by
        intro y
        rw [map_mul, finAt_mul, map_inv, finAt_inv, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]
      have hRy : ∀ y, R ((AdelicGLn.localEmbedding w y)⁻¹ * x) = R x := by
        intro y
        rw [← map_inv, hR]
      have hpt : ∀ y, ψ (a * y) * e₀ ((AdelicGLn.localEmbedding w (a * y))⁻¹ * x) =
          (J : Set (Gw n w)).indicator (fun _ => R x * ψ a) y := by
        intro y
        rw [he₀, hRy, hfa]
        have e1 : (a * y)⁻¹ * a = y⁻¹ := by group
        rw [e1]
        by_cases hy : y ∈ J
        · have hy' : y⁻¹ ∈ J := J.inv_mem hy
          rw [Set.indicator_of_mem (show y⁻¹ ∈ (J : Set (Gw n w)) from hy'),
            Set.indicator_of_mem (show y ∈ (J : Set (Gw n w)) from hy), hψ y hy, Pi.one_apply]
          ring
        · have hy' : y⁻¹ ∉ J := fun h => hy (by simpa using J.inv_mem h)
          rw [Set.indicator_of_notMem (show y⁻¹ ∉ (J : Set (Gw n w)) from hy'),
            Set.indicator_of_notMem (show y ∉ (J : Set (Gw n w)) from hy)]
          ring
      rw [hg, ← integral_mul_left_eq_self _ a]
      simp only [hpt]
      rw [integral_indicator hJm, setIntegral_const]
      simp [Measure.real, mul_comm]
    have hint : ∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m := by
      have hf : IsCompact (tsupport ψ) := ψ.hasCompactSupport.isCompact
      have hS : IsCompact ((AdelicGLn.localEmbedding w) '' tsupport ψ * tsupport e₀) :=
        (hf.image hp).mul e₀.hasCompactSupport.isCompact
      have hker : Continuous fun q : AdelicGLn.FiniteAdelicGL K n × Gw n w =>
          ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) :=
        (ψ.continuous.comp continuous_snd).mul
          (e₀.continuous.comp ((hp.comp continuous_snd).inv.mul continuous_fst))
      have hI : Integrable (Function.uncurry fun (x : AdelicGLn.FiniteAdelicGL K n) (y : Gw n w) =>
          ψ y * e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x)) (m.prod mw) := by
        refine Continuous.integrable_of_hasCompactSupport hker ?_
        refine HasCompactSupport.intro (hS.prod hf) fun q hq => ?_
        change ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) = 0
        by_contra hne
        obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
        exact hq ⟨⟨_, ⟨q.2, subset_tsupport _ h1, rfl⟩, _, subset_tsupport _ h2,
          mul_inv_cancel_left _ _⟩, subset_tsupport _ h1⟩
      simp only [hg]
      rw [integral_integral_swap hI]
      simp only [integral_const_mul]
      have hinv : ∀ y : Gw n w, ∫ x, e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) ∂m = ∫ x, e₀ x ∂m :=
        fun y => integral_mul_left_eq_self (fun x => e₀ x) _
      simp only [hinv]
      rw [integral_mul_const]
    exact ⟨g, hval, hint, hop⟩
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.integrated_rightRegular_eq_localOperator :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure]
          (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ) (T : LL μ →L[ℂ] LL μ), IsOloc μ w mw ψ T →
          (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
            (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) = T := by
  intro K _ _ n μ _ w _ _ mw _ ψ T h
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [UnitaryRep.inner_integrated, h u v]
  refine integral_congr_ae ((RightCosetSpace.coeFn_compactSupportToL1 mw ψ).mono fun g hg => ?_)
  have hr : (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
      (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1) g = rhoL μ w g := by
    simp only [UnitaryRep.compHom_apply]
    rfl
  simp only [hr]
  exact congrArg (· * ⟪u, rhoL μ w g v⟫_ℂ) hg
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem map_right_eq_of_CO {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) [m.IsHaarMeasure] {J : Subgroup G} (hJ : CO J) {k : G} (hk : k ∈ J) :
    Measure.map (· * k) m = m := by
  have hcont : Measurable (· * k : G → G) := (continuous_mul_const k).measurable
  haveI : (Measure.map (· * k) m).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right m k
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * k) m) m
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  have hpre : (· * k : G → G) ⁻¹' (J : Set G) = J := by
    ext x
    exact Subgroup.mul_mem_cancel_right J hk
  have h0 : m (J : Set G) ≠ 0 := (hJ.2.measure_pos m ⟨1, J.one_mem⟩).ne'
  have hT : m (J : Set G) ≠ ⊤ := hJ.1.measure_lt_top.ne
  have e := congrArg (fun ν : Measure G => ν (J : Set G)) h
  simp only [Measure.map_apply hcont hmeas, hpre, Measure.smul_apply] at e
  have hc : Measure.haarScalarFactor (Measure.map (· * k) m) m = 1 := by
    have e' : m (J : Set G) = (Measure.haarScalarFactor (Measure.map (· * k) m) m : ENNReal) * m (J : Set G) := by
      simpa [ENNReal.smul_def] using e
    have : ((Measure.haarScalarFactor (Measure.map (· * k) m) m : NNReal) : ENNReal) = 1 :=
      ((ENNReal.mul_eq_right h0 hT).1 e'.symm)
    exact_mod_cast this
  rw [h, hc, one_smul]

theorem UpperTheory.localOperator_comp_rhoL_eq_of_right_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure] (J : Subgroup (Gw n w)), CO J →
          ∀ (φ : Gw n w → ℂ), (∀ k ∈ J, ∀ x, φ (x * k) = φ x) → ∀ T : LL μ →L[ℂ] LL μ, IsOloc μ w mw φ T →
          ∀ k ∈ J, T ∘L rhoL μ w k = T := by
  intro K _ _ n μ _ w _ _ mw _ J hJ φ hφ T hT k hk
  have hmul : ∀ (g : Gw n w) (v : LL μ), rhoL μ w (g * k) v = rhoL μ w g (rhoL μ w k v) := by
    intro g v
    simp only [rhoL, rhoF, map_mul]
    exact UnitaryRep.map_mul_apply _ _ _ v
  have hmp : MeasurePreserving (· * k : Gw n w → Gw n w) mw mw :=
    ⟨(continuous_mul_const k).measurable, map_right_eq_of_CO mw hJ hk⟩
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.comp_apply, hT u, hT u v,
    ← hmp.integral_comp (Homeomorph.mulRight k).measurableEmbedding
      (fun g => φ g * ⟪u, rhoL μ w g v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [hφ k hk, hmul]
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_open_compact_level_subgroup :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (J : ∀ i, Subgroup (Gw n (w i))), (∀ i, CO (J i)) →
          ∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) ∧
            IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  intro K _ _ n r w J hJ
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun i => ?_⟩
        rw [map_mul, finAt_mul]
        exact mul_mem (ha' i) (hb' i)
      one_mem' := by
        refine ⟨one_mem _, fun i => ?_⟩
        rw [map_one, finAt_one]
        exact one_mem _
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun i => ?_⟩
        have h1 : finAt (w i) (finEmb K n a⁻¹) * finAt (w i) (finEmb K n a) = 1 := by
          rw [← finAt_mul, ← map_mul, inv_mul_cancel, map_one, finAt_one]
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (ha' i) }
  have hmem : ∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i :=
    fun h => Iff.rfl
  have hset : (U : Set (AdelicGLn.FiniteAdelicGL K n)) =
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
        ⋂ i, (fun h => finAt (w i) (finEmb K n h)) ⁻¹' (J i : Set (Gw n (w i))) := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact hmem h
  have hopen : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [hset]
    refine (AdelicGLn.isOpen_integralFiniteGL K n).inter (isOpen_iInter_of_finite fun i => ?_)
    exact (hJ i).2.preimage ((continuous_finAt (w i)).comp continuous_finEmb)
  refine ⟨U, hmem, hopen, ?_⟩
  exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen U hopen) fun _ h => h.1
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.finprod_local_eq_indicator_mul_prod :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (f : ∀ v : Pl K, Gw n v → ℂ),
          (∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1) → ∀ x : AdelicGLn.FiniteAdelicGL K n,
          ∏ᶠ v, f v (finAt v (finEmb K n x)) =
            ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x *
              ∏ i, f (w i) (finAt (w i) (finEmb K n x)) := by
  classical
  intro K _ _ n r w hw f hf x
  have hfin : {v : Pl K | finAt v (finEmb K n x) ∉ GLnLocal.integralGL (v.adicCompletion K) n}.Finite := by
    have hB : {v : Pl K | AdelicGLn.finiteRestrictedEquiv K n x v ∉
        GLnLocal.integralGL (v.adicCompletion K) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv K n x).2
    refine hB.subset ?_
    intro v hv
    have e : finAt v (finEmb K n x) = AdelicGLn.finiteRestrictedEquiv K n x v := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).2) v = _
      rw [prodEquiv_finEmb]
    simpa [e] using hv
  set S : Finset (Pl K) := hfin.toFinset ∪ Finset.univ.image w with hS
  have hoff : ∀ v, v ∉ Set.range w → f v (finAt v (finEmb K n x)) =
      if finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n then 1 else 0 := by
    intro v hv
    rw [hf v hv]
    by_cases h : finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n
    · rw [if_pos h]; exact Set.indicator_of_mem (s := (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v))) h _
    · rw [if_neg h]; exact Set.indicator_of_notMem (s := (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v))) h _
  have hsupp : Function.mulSupport (fun v => f v (finAt v (finEmb K n x))) ⊆ (S : Set (Pl K)) := by
    intro v hv
    by_contra hvS
    have h1 : v ∉ Set.range w := by
      rintro ⟨i, rfl⟩
      exact hvS (by simp [hS])
    have h2 : finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hvS (by simp only [hS, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]; exact Or.inl h)
    exact hv ((hoff v h1).trans (if_pos h2))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  by_cases hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))
  · rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    have hsub : Finset.univ.image w ⊆ S := Finset.subset_union_right
    rw [← Finset.prod_subset hsub, Finset.prod_image (fun a _ b _ h => hw h)]
    intro v _ hv
    have h1 : v ∉ Set.range w := by
      rintro ⟨i, rfl⟩
      exact hv (by simp)
    rw [hoff v h1, if_pos (hx v h1)]
  · rw [Set.indicator_of_notMem hx, zero_mul]
    have hx' : ∃ v, v ∉ Set.range w ∧ finAt v (finEmb K n x) ∉ GLnLocal.integralGL (v.adicCompletion K) n := by
      by_contra hc
      push_neg at hc
      exact hx hc
    obtain ⟨v, h1, h2⟩ := hx'
    refine Finset.prod_eq_zero (i := v) ?_ ?_
    · simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl h2
    · rw [hoff v h1, if_neg h2]
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.indicator_level_eq_prod_local_indicator :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (J : ∀ i, Subgroup (Gw n (w i))),
          (∀ i, J i ≤ GLnLocal.integralGL ((w i).adicCompletion K) n) → ∀ U : Set (AdelicGLn.FiniteAdelicGL K n),
          (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) → ∀ x,
          U.indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) x =
            ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x *
              ∏ i, (J i : Set (Gw n (w i))).indicator 1 (finAt (w i) (finEmb K n x)) := by
  intro K _ _ n r w J hJ U hU x
  have key : ∀ (h : AdelicGLn.FiniteAdelicGL K n) (v : Pl K),
      finAt v (finEmb K n h) = AdelicGLn.finiteRestrictedEquiv K n h v := by
    intro h v
    show AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n h)).2 v = _
    rw [prodEquiv_finEmb]
  have hint : ∀ h : AdelicGLn.FiniteAdelicGL K n, h ∈ AdelicGLn.integralFiniteGL K n ↔
      ∀ v : Pl K, finAt v (finEmb K n h) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro h
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    simp only [key]
  by_cases hx : x ∈ U
  · obtain ⟨h1, h2⟩ := (hU x).1 hx
    have hy : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈
        GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)) :=
      fun v _ => (hint x).1 h1 v
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Finset.prod_eq_one]
    · simp
    · intro i _
      rw [Set.indicator_of_mem (SetLike.mem_coe.2 (h2 i))]
      rfl
  · rw [Set.indicator_of_notMem hx]
    by_cases hJx : ∀ i, finAt (w i) (finEmb K n x) ∈ J i
    · have hy : x ∉ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈
          GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)) := by
        intro hy
        refine hx ((hU x).2 ⟨(hint x).2 fun v => ?_, hJx⟩)
        by_cases hv : v ∈ Set.range w
        · obtain ⟨i, rfl⟩ := hv
          exact hJ i (hJx i)
        · exact hy v hv
      rw [Set.indicator_of_notMem hy, zero_mul]
    · push_neg at hJx
      obtain ⟨i, hi⟩ := hJx
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem (SetLike.mem_coe.not.2 hi) _), mul_zero]
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_compactOpen_biinvariant_of_test :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) (φ : Gw n w → ℂ), Test φ →
          ∃ J : Subgroup (Gw n w), CO J ∧ J ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ ∀ k ∈ J, ∀ x, φ (k * x) = φ x ∧ φ (x * k) = φ x := by
  intro K _ _ n w φ hφ
  obtain ⟨U, hU, hf⟩ := GlobalTheory.Orb.exists_biinvariant (G := Gw n w) (f := φ) ⟨hφ.1, hφ.2⟩
  refine ⟨U ⊓ GLnLocal.integralGL (w.adicCompletion K) n, ⟨?_, ?_⟩, inf_le_right,
    fun k hk x => hf k hk.1 x⟩
  · rw [Subgroup.coe_inf]
    exact (GLnLocal.isCompact_integralGL (w.adicCompletion K) n).inter_left
      (U.isClosed_of_isOpen hU)
  · rw [Subgroup.coe_inf]
    exact hU.inter (GLnLocal.isOpen_integralGL (w.adicCompletion K) n)
end
