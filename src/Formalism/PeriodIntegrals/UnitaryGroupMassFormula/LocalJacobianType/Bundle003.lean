module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.GoodTransvection
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ChiZeroRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.DiagonalPhaseFirstVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp
open scoped TensorProduct ENNReal NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def mulL {ι : Type} (z : ι → Fv F v ⊗[F] E) :
    (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (z i)).comp (LinearMap.proj i)

theorem mulL_apply {ι : Type} (z : ι → Fv F v ⊗[F] E) (c : ι → Fv F v ⊗[F] E) (i : ι) :
    mulL v z c i = z i * c i := rfl

theorem det_mulL {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → Fv F v ⊗[F] E) :
    LinearMap.det (mulL v z) = ∏ i, Algebra.norm (Fv F v) (z i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  unfold mulL
  rw [LinearMap.det_pi]
  simp only [Algebra.norm_apply]

private theorem absV_mul_lemma (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  by_cases hx : Valued.v x = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hx, zero_mul]
    simp [absV, hx, hxy]
  by_cases hy : Valued.v y = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hy, mul_zero]
    simp [absV, hy, hxy]
  have hxy : Valued.v (x * y) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hx hy
  unfold absV
  rw [dite_eq_right hx, dite_eq_right hy, dite_eq_right hxy, ← zpow_add₀ hq, ← toAdd_mul]
  congr 2
  rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
    WithZero.coe_unzero, map_mul]

private theorem absV_one_lemma_2 : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by
    rw [map_one]
    exact one_ne_zero
  unfold absV
  rw [dite_eq_right h1]
  have h2 : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h2, toAdd_one, zpow_zero]

theorem absV_prod {ι : Type} [Fintype ι] (a : ι → Fv F v) :
    absV v (∏ i, a i) = ∏ i, absV v (a i) := by
  let f : Fv F v →* ℝ :=
    { toFun := absV v, map_one' := absV_one_lemma_2 v, map_mul' := absV_mul_lemma v }
  exact map_prod f a Finset.univ

theorem box_measure_mul : BoxMul (E := E) v := by
  classical
  intro ι _ μ _ y hy
  haveI := locallyCompact_Fv v
  haveI := secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  let u : ι → (Fv F v ⊗[F] E)ˣ := fun i => (hy i).unit
  let z : ι → Fv F v ⊗[F] E := fun i => ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ)
  let h : (ι → Fv F v ⊗[F] E) ≃ₜ (ι → Fv F v ⊗[F] E) :=
    { toFun := mulL v y
      invFun := mulL v z
      left_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 * y i = 1 from (u i).inv_mul, one_mul]
      right_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show y i * ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 = 1 from (u i).mul_inv, one_mul]
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (mulL v y)
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (mulL v z) }
  let Em := h.toMeasurableEquiv
  have hNz : ∀ i, Algebra.norm (Fv F v) (z i) * Algebra.norm (Fv F v) (y i) = 1 := fun i => by
    rw [← map_mul, show z i * y i = 1 from (u i).inv_mul, map_one]
  have hdet0 : (∏ i, Algebra.norm (Fv F v) (z i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => left_ne_zero_of_mul_eq_one (hNz i)
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  set c := PI.NglqJacSplitW.modF (Fv F v) (∏ i, Algebra.norm (Fv F v) (z i)) with hc
  have hmap : μ.map Em = c • μ := by
    ext X hX
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul]
    have hpre : Em ⁻¹' X = mulL v z '' X := by
      ext x
      constructor
      · intro hx
        exact ⟨h x, hx, h.left_inv x⟩
      · rintro ⟨w, hw, rfl⟩
        show h (h.symm w) ∈ X
        rw [h.apply_symm_apply]; exact hw
    rw [hpre, hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ (mulL v z)
      (by rw [det_mulL]; exact hdet0) μ inferInstance X hX, det_mulL]
  have hS : (Set.univ.pi fun i => {c | y i * c ∈ OEv (E := E) v}) = Em ⁻¹' Obox (E := E) v ι := by
    ext x
    simp [Obox, Em, h, mulL_apply]
  rw [hS, ← MeasurableEquiv.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    hc, modF_Fv v _ hdet0, absV_prod, ENNReal.toReal_ofReal
      (Finset.prod_nonneg fun i _ => (absV_pos v (left_ne_zero_of_mul_eq_one (hNz i))).le),
    mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [eq_inv_of_mul_eq_one_left (hNz i), absV_inv]

end PI.UnitaryGroupMassFormula.LocJacTyp.BM
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

section Scale

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem haar_smul_map (μ0 : Measure V) [μ0.IsAddHaarMeasure] (c : Fv F v) (hc : c ≠ 0) :
    (Measure.map (fun x : V => c • x) μ0).IsAddHaarMeasure := by
  let h := Homeomorph.smulOfNeZero (α := V) c hc
  exact Measure.isAddHaarMeasure_map μ0 (DistribSMul.toAddMonoidHom V c)
    (continuous_const_smul c) h.surjective h.isClosedEmbedding.tendsto_cocompact

theorem scale_prod (μ0 : Measure V) [μ0.IsAddHaarMeasure] (c : Fv F v) (hc : c ≠ 0)
    (A B : Set V) (hA : MeasurableSet A) (hB : MeasurableSet B) (hA0 : μ0 A ≠ 0) (hAt : μ0 A ≠ ⊤) :
    μ0 ((fun x : V => c • x) ⁻¹' A) * μ0 ((fun x : V => c⁻¹ • x) ⁻¹' B) = μ0 A * μ0 B := by
  have := haar_smul_map v μ0 c hc
  have := haar_smul_map v μ0 c⁻¹ (inv_ne_zero hc)
  have hm : Measurable fun x : V => c • x := (continuous_const_smul c).measurable
  have hm' : Measurable fun x : V => c⁻¹ • x := (continuous_const_smul c⁻¹).measurable
  obtain ⟨s1, e1⟩ : ∃ s : NNReal, Measure.map (fun x : V => c • x) μ0 = s • μ0 :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ0⟩
  obtain ⟨s2, e2⟩ : ∃ s : NNReal, Measure.map (fun x : V => c⁻¹ • x) μ0 = s • μ0 :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ0⟩
  have hcomp : Measure.map (fun x : V => c⁻¹ • x) (Measure.map (fun x : V => c • x) μ0) = μ0 := by
    rw [Measure.map_map hm' hm]
    have : ((fun x : V => c⁻¹ • x) ∘ fun x : V => c • x) = id := by
      funext x; simp [smul_smul, inv_mul_cancel₀ hc]
    rw [this, Measure.map_id]
  have hss : ((s1 : ENNReal) * s2) * μ0 A = 1 * μ0 A := by
    have h := congrArg (fun m : Measure V => m A) hcomp
    rw [e1, Measure.map_smul s1 hm'.aemeasurable, e2, smul_smul] at h
    rw [one_mul]
    conv_rhs => rw [← h]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul]
  have hs : (s1 : ENNReal) * s2 = 1 := (ENNReal.mul_left_inj hA0 hAt).1 hss
  rw [← Measure.map_apply hm hA, ← Measure.map_apply hm' hB, e1, e2]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc (s1 : ENNReal) * μ0 A * (s2 * μ0 B) = ((s1 : ENNReal) * s2) * (μ0 A * μ0 B) := by ring
    _ = μ0 A * μ0 B := by rw [hs, one_mul]

end Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

def Mk (ι : Type) (k : ℕ) : AddSubgroup (ι → Fv F v ⊗[F] E) :=
  (ObS (E := E) v ι).comap (DistribSMul.toAddMonoidHom (ι → Fv F v ⊗[F] E) (piu v ^ k))

theorem coe_Mk (ι : Type) (k : ℕ) : (Mk (E := E) v ι k : Set (ι → Fv F v ⊗[F] E)) =
    (fun x => piu v ^ k • x) ⁻¹' Obox (E := E) v ι := by
  ext x
  rw [← coe_ObS]
  rfl

theorem ann_Mk (ι : Type) [Fintype ι] (k : ℕ) :
    ann (chi (E := E) v ψ ι) (Mk (E := E) v ι k) =
      (fun y => (piu v ^ k)⁻¹ • y) ⁻¹' Dbox (E := E) v ψ ι := by
  have hpk : piu v ^ k ≠ 0 := pow_ne_zero k (piu_ne v)
  rw [← ann_obox]
  ext y
  simp only [Set.mem_preimage, ann, Set.mem_setOf_eq, coe_Mk]
  constructor
  · intro hy x hx
    have := hy ((piu v ^ k)⁻¹ • x) (by simpa [smul_smul, mul_inv_cancel₀ hpk] using hx)
    rwa [chi_smul] at this
  · intro hy x hx
    have := hy (piu v ^ k • x) hx
    rwa [chi_smul, smul_smul, mul_inv_cancel₀ hpk, one_smul] at this

variable (hK : OpenKer v ψ) (hnt : ∃ r, psiV F ψ v r ≠ 1)
include hK hnt

theorem isCompact_dbox (ι : Type) [Fintype ι] : IsCompact (Dbox (E := E) v ψ ι) :=
  isCompact_univ_pi fun _ => conductor_isCompact v ψ hK hnt

omit hnt in
theorem isOpen_dbox (ι : Type) [Fintype ι] : IsOpen (Dbox (E := E) v ψ ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => conductor_isOpen v ψ hK

theorem exists_sd (ι : Type) [Fintype ι] :
    ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι) := by
  have hpk : ∀ k : ℕ, piu v ^ k ≠ 0 := fun k => pow_ne_zero k (piu_ne v)
  have hψc := continuous_psiV_of v ψ hK
  have hA : MeasurableSet (Obox (E := E) v ι) := (isOpen_obox v ι).measurableSet
  have hB : MeasurableSet (Dbox (E := E) v ψ ι) := (isOpen_dbox v ψ hK ι).measurableSet
  set μ0 : Measure (ι → Fv F v ⊗[F] E) := Measure.addHaar
  have hA0 : μ0 (Obox (E := E) v ι) ≠ 0 :=
    (isOpen_obox v ι).measure_ne_zero μ0 ⟨0, zero_mem_obox v ι⟩
  have hAt : μ0 (Obox (E := E) v ι) ≠ ⊤ := (isCompact_obox v ι).measure_lt_top.ne
  refine PI.OmFibreUniq.W.SdCore.selfDual_of_pairs (chi (E := E) v ψ ι) ?_ (chi_add_left v ψ ι)
    (chi_symm v ψ ι) (fun x y => norm_psiV_of v ψ hK _) (Mk (E := E) v ι) (fun k => ?_)
    (fun k => ?_) (fun k => ?_) (fun k => ?_) (fun y => ?_) (fun U hU => ?_) μ0 (fun k => ?_)
  · exact hψc.comp (continuous_finsetSum _ fun i _ => (continuous_tr v).comp
      (((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)))
  · rw [coe_Mk]
    exact (Homeomorph.smulOfNeZero (α := ι → Fv F v ⊗[F] E) _ (hpk k)).isCompact_preimage.2
      (isCompact_obox v ι)
  · rw [coe_Mk]
    exact (isOpen_obox v ι).preimage (continuous_const_smul _)
  · rw [ann_Mk]
    exact (Homeomorph.smulOfNeZero (α := ι → Fv F v ⊗[F] E) _ (inv_ne_zero (hpk k))).isCompact_preimage.2
      (isCompact_dbox v ψ hK hnt ι)
  · rw [ann_Mk]
    exact (isOpen_dbox v ψ hK ι).preimage (continuous_const_smul _)
  · have ht : Tendsto (fun k : ℕ => piu v ^ k • y) atTop (𝓝 0) := by
      simpa using (piu_tendsto v).smul_const y
    filter_upwards [ht ((isOpen_obox v ι).mem_nhds (zero_mem_obox v ι))] with k hk
    rw [← SetLike.mem_coe, coe_Mk]
    exact hk
  · filter_upwards [tube v (isCompact_dbox v ψ hK hnt ι) hU] with k hk
    rw [ann_Mk]
    intro y hy
    have := hk _ hy
    rwa [smul_smul, mul_inv_cancel₀ (hpk k), one_smul] at this
  · rw [ann_Mk, ann_Mk, coe_Mk, coe_Mk, scale_prod v μ0 _ (hpk k) _ _ hA hB hA0 hAt,
      scale_prod v μ0 _ (hpk 0) _ _ hA hB hA0 hAt]

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end
