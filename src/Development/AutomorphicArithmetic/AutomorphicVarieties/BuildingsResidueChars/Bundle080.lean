module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle079
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle006
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AutomorphicArithmetic.DivisorFrames.AlgebraicModSubmoduleQdetBlockOfGlRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MaximalCompactUniqueArchFiniteDecomposition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle001
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
public import Development.WeilBound.CuspidalAdmissibility.FixLev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.ExpEqOfHasDerivAt

@[expose] public section

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.isZFinite_of_centre_span :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : archSmooth K n), Centre (Submodule.span ℂ {φ}) → IsZFinite φ := by
  intro K _ _ n φ hφ
  obtain ⟨ι, hι, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  have key := fun τ => UpperTheory.exists_qdet_eq_pow_add_sum_coeff_mem_span (Module.End ℂ (archSmooth K n)) n (gen D (lam K n) τ)
  choose c hc hq using key
  let s : Set (Module.End ℂ (archSmooth K n)) := Set.range (fun p : ι × Fin n => c p.1 p.2)
  have hcZ : ∀ τ k, c τ k ∈ Zc K n := by
    intro τ k
    have h1 : Submodule.span ℂ (Set.range (Formalism.REAL.qdet (gen D (lam K n) τ))) ≤
        Subalgebra.toSubmodule (Zc K n) := by
      rw [Submodule.span_le]
      rintro x ⟨u, rfl⟩
      exact UpperTheory.qdet_generates_universalEnveloping_centre K n ι D τ u
    exact h1 (hc τ k)
  have hsZ : ∀ x ∈ s, x ∈ Zc K n := by
    rintro x ⟨⟨τ, k⟩, rfl⟩
    exact hcZ τ k
  have hAlg : ∀ T ∈ Zc K n, AlgMod (Submodule.span ℂ {φ}) ⊥ T := by
    intro T hT
    apply UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ (uAction '' (isExpLieAlgebra K n).centerU)
    · rintro x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩
      exact Zc_comm (uAction_mem_Zc hz) (uAction_mem_Zc hw)
    · rintro x ⟨z, hz, rfl⟩
      exact hφ z hz
    · exact hT
  have hfd := UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting _ φ s (Set.finite_range _)
    (fun a ha b hb => Zc_comm (hsZ a ha) (hsZ b hb)) (fun T hT => hAlg T (hsZ T hT))
  have hle : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤ Algebra.adjoin ℂ s := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨τ, u, rfl⟩
    show Formalism.REAL.qdet (gen D (lam K n) τ) u ∈ Algebra.adjoin ℂ s
    rw [hq τ u]
    refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun k hk => Subalgebra.smul_mem _ ?_ _)
    exact Algebra.subset_adjoin ⟨(τ, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩
  have hsub : Submodule.span ℂ ((fun z => (uAction z) φ) '' ((isExpLieAlgebra K n).centerU : Set _)) ≤
      Submodule.span ℂ ((fun T : Module.End ℂ (archSmooth K n) => T φ) '' (Algebra.adjoin ℂ s : Set _)) := by
    apply Submodule.span_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨uAction z, hle (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz), rfl⟩
  exact Submodule.finiteDimensional_of_le hsub
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.QuantumDetLeviBlocks

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Formalism.REAL.Tm]
  split_ifs <;> simp

private def pw (ι V : Type) [AddCommGroup V] [Module ℂ V] :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun f := LinearMap.compLeft f ι
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem algMod_of_ne_zero {M : Type} [AddCommGroup M] [Module ℂ M] (S N : Submodule ℂ M)
    (T : Module.End ℂ M) (P : Polynomial ℂ) (hP : P ≠ 0)
    (h : ∀ x ∈ S, Polynomial.aeval T P x ∈ N) : AlgMod S N T := by
  refine ⟨P * Polynomial.C (P.leadingCoeff)⁻¹, Polynomial.monic_mul_leadingCoeff_inv hP, fun x hx => ?_⟩
  rw [mul_comm, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
  exact N.smul_mem _ (h x hx)

end UpperTheory.V.QuantumDetLeviBlocks

open UpperTheory.V.QuantumDetLeviBlocks in
theorem UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (r s : ℕ) (X : Fin (r + s) → Fin (r + s) → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ W Z S : Submodule ℂ M, S ≤ W → (∀ p q, ∀ x ∈ W, X p q x ∈ W) → (∀ (p : Fin r) (q : Fin s), ∀ x ∈ W, X (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Z) → (∀ u, AlgMod S ⊥ (Formalism.REAL.qdet X u)) → ∀ u, AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd s p) (Fin.castAdd s q)) u) ∧ AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin s => X (Fin.natAdd r p) (Fin.natAdd r q)) u) := by
  intro M _ _ r s U hU W Z S hs hW hZ hc u
  let φ := pw S M
  let X : Fin (r + s) → Fin (r + s) → Module.End ℂ (S → M) := fun p q => φ (U p q)
  have hX : Formalism.REAL.GlRel X := by
    intro a b c d
    have := congrArg φ (hU a b c d)
    split_ifs at this ⊢ <;> simpa [X] using this
  let W' : Submodule ℂ (S → M) := Submodule.pi Set.univ fun _ => W
  let N' : Submodule ℂ (S → M) := ⊥ ⊔ Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin s), ∃ x ∈ W',
    y = X (Fin.castAdd s p) (Fin.natAdd r q) x}
  have hle : N' ≤ Submodule.pi Set.univ fun _ => Z := by
    refine sup_le bot_le (Submodule.span_le.2 ?_)
    rintro _ ⟨p, q, x, hx, rfl⟩ i hi
    exact hZ p q _ (hx i hi)
  obtain ⟨-, h1, h2⟩ := UpperTheory.algebraicModSubmodule_qdet_block_of_glRel (S → M) r s X hX W' ⊥ N'
    (fun p q x hx i hi => hW p q _ (hx i hi))
    (fun p q x hx => by rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact Submodule.zero_mem _)
    rfl (fun i => i.1) (fun i _ => hs i.2) (fun u => by
      obtain ⟨P, hP, h⟩ := hc u
      refine ⟨P, hP.ne_zero, (Submodule.mem_bot ℂ).2 ?_⟩
      funext i
      rw [← map_qdet φ U u, Polynomial.aeval_algHom_apply]
      exact (Submodule.mem_bot ℂ).1 (h i.1 i.2))
  constructor
  · obtain ⟨P, hP, h⟩ := h1 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin r => U (Fin.castAdd s p) (Fin.castAdd s q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
  · obtain ⟨P, hP, h⟩ := h2 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin s => U (Fin.natAdd r p) (Fin.natAdd r q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
end

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem map_right_inv {A H C : Type} [Group A] [Group H] [Group C] [MeasurableSpace A] [MeasurableSpace H]
    [MeasurableSpace C] (κ : Measure A) (ν : Measure H) [SFinite κ] [SFinite ν] (p : A × H → C) (hp : Measurable p)
    (hm : Measurable fun x : C × C => x.1 * x.2) (hs : Function.Surjective p) (hmul : ∀ x y, p x * p y = p (x * y))
    (hκ : ∀ a, MeasurePreserving (· * a) κ κ) (hν : ∀ d, MeasurePreserving (· * d) ν ν) (u : C) :
    MeasurePreserving (· * u) (Measure.map p (κ.prod ν)) (Measure.map p (κ.prod ν)) := by
  obtain ⟨⟨a, d⟩, rfl⟩ := hs u
  have hu : Measurable fun c : C => c * p (a, d) := hm.comp (measurable_id.prodMk measurable_const)
  refine ⟨hu, ?_⟩
  have hq := (hκ a).prod (hν d)
  rw [Measure.map_map hu hp]
  have e : (fun c : C => c * p (a, d)) ∘ p = p ∘ Prod.map (· * a) (· * d) := by
    funext x
    exact hmul x (a, d)
  rw [e, ← Measure.map_map hp hq.measurable, hq.map_eq]

theorem UpperTheory.haar_decomposition_norm_one_gl2 :
    ∀ {K : Type} [Field K] [NumberField K] (κ₂ : Measure (archCompact K 2)), IsHaarK κ₂ → ∃ (ν : Measure (AdelicGLn.integralFiniteGL K 2)) (ρ : Measure (KG K 2)), IsProbabilityMeasure ν ∧ ν.IsOpenPosMeasure ∧ IsProbabilityMeasure ρ ∧ (∀ u : KG K 2, MeasurePreserving (· * u) ρ ρ) ∧ ∀ F : G1 K 2 → ℂ, (Continuous fun k : KG K 2 => F k) → ∫ v, F (v : G1 K 2) ∂ρ = ∫ a, ∫ d, F (arc1 a * fin1 (d : FA K 2)) ∂ν ∂κ₂ := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro K _ _ κ₂ hκ
    haveI := hκ.prob
    obtain ⟨α, β, -, -, hdec, -, hA, hF⟩ := UpperTheory.maximalCompact_unique_arch_finite_decomposition (K := K) 2
    obtain ⟨-, -, hcomm, harc, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws (K := K) 2 ∅

    let ν₀ : Measure (AdelicGLn.integralFiniteGL K 2) := Measure.haarMeasure ⊤
    haveI : IsProbabilityMeasure ν₀ := ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (AdelicGLn.integralFiniteGL K 2)))⟩
    let ν : Measure (AdelicGLn.integralFiniteGL K 2) := ν₀.inv
    haveI hνp : IsProbabilityMeasure ν := by
      change IsProbabilityMeasure (Measure.map Inv.inv ν₀)
      infer_instance
    have hνo : ν.IsOpenPosMeasure := continuous_inv.isOpenPosMeasure_map inv_surjective
    have hνr : ∀ d, MeasurePreserving (· * d) ν ν := fun d => measurePreserving_mul_right ν d

    let p : archCompact K 2 × AdelicGLn.integralFiniteGL K 2 → KG K 2 := fun x =>
      ⟨arc1 x.1 * fin1 (x.2 : FA K 2), (KG K 2).mul_mem (hA x.1) (hF x.2)⟩
    have hpc : Continuous p := Continuous.subtype_mk ((harc.comp continuous_fst).mul
      (MultiplicityOne.continuous_finProj.comp (continuous_subtype_val.comp continuous_snd))) _
    have hpm : Measurable p := hpc.measurable
    have hps : Function.Surjective p := fun k => ⟨(α k, β k), Subtype.ext (hdec k).symm⟩
    have hmul : ∀ x y, p x * p y = p (x * y) := by
      intro x y
      apply Subtype.ext
      change arc1 x.1 * fin1 (x.2 : FA K 2) * (arc1 y.1 * fin1 (y.2 : FA K 2)) =
        arc1 (x.1 * y.1) * fin1 ((x.2 * y.2 : AdelicGLn.integralFiniteGL K 2) : FA K 2)
      have e1 : arc1 (x.1 * y.1) = arc1 x.1 * arc1 y.1 := by simp [arc1]
      have e2 : fin1 ((x.2 * y.2 : AdelicGLn.integralFiniteGL K 2) : FA K 2) = fin1 (x.2 : FA K 2) * fin1 (y.2 : FA K 2) := by
        simp [fin1]
      rw [e1, e2, mul_assoc, mul_assoc, ← mul_assoc (fin1 (x.2 : FA K 2)), (hcomm y.1 (x.2 : FA K 2)).symm.eq, mul_assoc]
    haveI : IsProbabilityMeasure (κ₂.prod ν) := inferInstance
    refine ⟨ν, Measure.map p (κ₂.prod ν), hνp, hνo, inferInstance,
      map_right_inv κ₂ ν p hpm (continuous_mul.measurable) hps hmul hκ.right hνr, ?_⟩
    intro F hFc
    have hc : Continuous fun x => F (p x : G1 K 2) := hFc.comp hpc
    rw [integral_map hpm.aemeasurable hFc.aestronglyMeasurable,
      integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
end

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem blocks_read {R : Type} [CommRing R] {x y : Matrix (Fin 2) (Fin 2) R}
    {X : UPos (2 + 2) 2 → R} {A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R}
    (h : Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x 0 0 y) = unipMatrix X * A) (i j : Fin 2) :
    A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = x i j ∧
      A (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = y i j := by
  have ent : ∀ a b : Fin 2 ⊕ Fin 2, (unipMatrix X * A) (finSumFinEquiv a) (finSumFinEquiv b) = Matrix.fromBlocks x 0 0 y a b := by
    intro a b
    rw [← h]
    simp
  have vl : ∀ a : Fin 2, ((finSumFinEquiv (Sum.inl a) : Fin (2 + 2)) : ℕ) < 2 := fun a => by
    rw [finSumFinEquiv_apply_left]
    exact a.2
  have vr : ∀ a : Fin 2, 2 ≤ ((finSumFinEquiv (Sum.inr a) : Fin (2 + 2)) : ℕ) := fun a => by
    rw [finSumFinEquiv_apply_right]
    exact Nat.le_add_right _ _
  have row : ∀ (a : Fin 2) (l : Fin (2 + 2)), blockEntry X (finSumFinEquiv (Sum.inr a)) l = 0 := by
    intro a l
    rw [blockEntry_apply, dite_eq_right]
    intro hh
    have := vr a
    omega
  have low : ∀ (a : Fin 2) (b : Fin (2 + 2)), (unipMatrix X * A) (finSumFinEquiv (Sum.inr a)) b = A (finSumFinEquiv (Sum.inr a)) b := by
    intro a b
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp [row]
  have c0 : ∀ a b : Fin 2, A (finSumFinEquiv (Sum.inr a)) (finSumFinEquiv (Sum.inl b)) = 0 := by
    intro a b
    rw [← low, ent]
    simp
  refine ⟨?_, ?_⟩
  · rw [show x i j = Matrix.fromBlocks x 0 0 y (Sum.inl i) (Sum.inl j) by simp, ← ent, unipMatrix, add_mul, one_mul,
      Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective l
    rcases l with l | l
    · rw [blockEntry_apply, dite_eq_right, zero_mul]
      intro hh
      have := vl l
      omega
    · rw [c0, mul_zero]
  · rw [← low, ent]
    simp

private theorem exists_depth {K : Type} [Field K] [NumberField K] (w : Pl K) {A B : Subgroup (Gw 2 w)}
    (hA : IsOpen (A : Set (Gw 2 w))) (hB : IsOpen (B : Set (Gw 2 w))) :
    ∃ m, GLnLocal.congruenceSubgroup (w.adicCompletion K) 2 m ≤ A ⊓ B := by
  have h : ((A ⊓ B : Subgroup (Gw 2 w)) : Set (Gw 2 w)) ∈ 𝓝 (1 : Gw 2 w) :=
    (hA.inter hB).mem_nhds ⟨one_mem _, one_mem _⟩
  obtain ⟨m, -, hm⟩ := (GLnLocal.hasBasis_nhds_one (w.adicCompletion K) 2).mem_iff.1 h
  exact ⟨m, hm⟩

private theorem finite_projection_integral_coe {K : Type} [Field K] [NumberField K] {n : ℕ} {u : FA K n}
    (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))

private theorem block_mem {K : Type} [Field K] [NumberField K] (S : Finset (Pl K)) {V : ∀ w : Pl K, Subgroup (Gw 2 w)}
    (m : Pl K → ℕ) (hV : ∀ w, GLnLocal.congruenceSubgroup (w.adicCompletion K) 2 (m w) ≤ V w)
    {d : FA K 2} (hd : d ∈ AdelicGLn.integralFiniteGL K 2) {u : FA K (2 + 2)} (f : Fin 2 → Fin (2 + 2)) (hf : Function.Injective f)
    (hu : u ∈ levOn S fun w : Pl K => GLnLocal.congruenceSubgroup (w.adicCompletion K) (2 + 2) (m w))
    (he : ∀ i j, (finEmb K (2 + 2) u) (f i) (f j) = (finEmb K 2 d) i j) : d ∈ levOn S V := by
  have hu' : ∀ v, finAt v (finEmb K (2 + 2) u) ∈ (if v ∈ S then GLnLocal.congruenceSubgroup (v.adicCompletion K) (2 + 2) (m v)
      else GLnLocal.integralGL (v.adicCompletion K) (2 + 2)) := hu
  have hint : ∀ v, finAt v (finEmb K 2 d) ∈ GLnLocal.integralGL (v.adicCompletion K) 2 := fun v => by
    rw [PositivityTheory.TfC.FixLev.finAt_finEmb]
    exact (AdelicGLn.mem_integralFiniteGL_iff_forall K 2).1 hd v
  change ∀ v, finAt v (finEmb K 2 d) ∈ (if v ∈ S then V v else GLnLocal.integralGL (v.adicCompletion K) 2)
  intro v
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    refine hV v ((GLnLocal.mem_congruenceSubgroup_iff _ _).2 ⟨hint v, fun i j => ?_⟩)
    have h1 := hu' v
    rw [if_pos hv] at h1
    have h2 := ((GLnLocal.mem_congruenceSubgroup_iff _ _).1 h1).2 (f i) (f j)
    have h3 : finAt v (finEmb K (2 + 2) u) (f i) (f j) = finAt v (finEmb K 2 d) i j := by
      simp only [finAt_apply, he]
    rw [h3] at h2
    have h4 : (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (v.adicCompletion K)) (f i) (f j) =
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
      simp [Matrix.one_apply, hf.eq_iff]
    rwa [h4] at h2
  · rw [if_neg hv]
    exact hint v

theorem UpperTheory.exists_level_indicator_unipotent_invariant :
    ∀ {K : Type} [Field K] [NumberField K] (S : Finset (Pl K)) (U₁ U₂ : ∀ w : Pl K, Subgroup (Gw 2 w)), Lev U₁ → Lev U₂ → ∃ (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)) (χ : AdelicGLn.integralFiniteGL K (2 + 2) → ℂ), Lev U ∧ Continuous χ ∧ (∀ h, χ h = 0 ∨ χ h = 1) ∧ χ 1 = 1 ∧ (∀ (h₀ h : AdelicGLn.integralFiniteGL K (2 + 2)) X, fin1 (h₀ : FA K (2 + 2)) = nn X → χ (h₀ * h) = χ h) ∧ (∀ h u : AdelicGLn.integralFiniteGL K (2 + 2), (u : FA K (2 + 2)) ∈ levOn S U → χ (h * u) = χ h) ∧ ∀ (d₁ d₂ : AdelicGLn.integralFiniteGL K 2) (h : AdelicGLn.integralFiniteGL K (2 + 2)), fin1 (h : FA K (2 + 2)) = lv (fin1 (d₁ : FA K 2)) (fin1 (d₂ : FA K 2)) 0 → χ h ≠ 0 → (d₁ : FA K 2) ∈ levOn S U₁ ∧ (d₂ : FA K 2) ∈ levOn S U₂ := by
  intro K _ _ S U₁ U₂ h₁ h₂
  choose m hm using fun w : Pl K => exists_depth w (h₁ w).1.2 (h₂ w).1.2
  let U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w) := fun w =>
    GLnLocal.congruenceSubgroup (w.adicCompletion K) (2 + 2) (m w)
  have hU : Lev U := fun w => ⟨⟨GLnLocal.isCompact_congruenceSubgroup _ _ _, GLnLocal.isOpen_congruenceSubgroup _ _ _⟩,
    GLnLocal.congruenceSubgroup_le _ _ _⟩
  obtain ⟨⟨-, hopen⟩, hle⟩ := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws (K := K) (2 + 2) S).1 U hU
  have fm : ∀ a b : FA K (2 + 2), fin1 (a * b) = fin1 a * fin1 b := fun a b => map_mul (MultiplicityOne.finProj K (2 + 2)) a b
  have fi : ∀ a : FA K (2 + 2), fin1 a⁻¹ = (fin1 a)⁻¹ := fun a => map_inv (MultiplicityOne.finProj K (2 + 2)) a
  let P : FA K (2 + 2) → Prop := fun h => ∃ X, ∃ u ∈ levOn S U, fin1 h = nn X * fin1 u
  have hR1 : ∀ (h u : FA K (2 + 2)), u ∈ levOn S U → P h → P (h * u) := by
    rintro h u hu ⟨X, v, hv, e⟩
    exact ⟨X, v * u, mul_mem hv hu, by rw [fm, e, fm, mul_assoc]⟩
  have hR : ∀ (h u : FA K (2 + 2)), u ∈ levOn S U → (P (h * u) ↔ P h) := fun h u hu =>
    ⟨fun hp => by simpa using hR1 _ _ (inv_mem hu) hp, hR1 h u hu⟩
  have hL1 : ∀ (h₀ h : FA K (2 + 2)) X, fin1 h₀ = nn X → P h → P (h₀ * h) := by
    rintro h₀ h X e ⟨Y, v, hv, e'⟩
    refine ⟨X + Y, v, hv, ?_⟩
    rw [fm, e, e', ← mul_assoc]
    exact congrArg (· * _) (unipOne_add 2 X Y).symm
  have hL : ∀ (h₀ h : FA K (2 + 2)) X, fin1 h₀ = nn X → (P (h₀ * h) ↔ P h) := by
    refine fun h₀ h X e => ⟨fun hp => ?_, hL1 h₀ h X e⟩
    have e' : fin1 h₀⁻¹ = nn (-X) := by
      rw [fi, e, inv_eq_iff_mul_eq_one]
      rw [← unipOne_add, add_neg_cancel, unipOne_zero]
    simpa using hL1 _ _ _ e' hp
  let χ : AdelicGLn.integralFiniteGL K (2 + 2) → ℂ := fun h => if P h then 1 else 0
  have hχR : ∀ h u : AdelicGLn.integralFiniteGL K (2 + 2), (u : FA K (2 + 2)) ∈ levOn S U → χ (h * u) = χ h := by
    intro h u hu
    simp only [χ, Subgroup.coe_mul, hR _ _ hu]
  refine ⟨U, χ, hU, ?_, fun h => ?_, ?_, ?_, hχR, ?_⟩
  · refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
    have ho : IsOpen {y : AdelicGLn.integralFiniteGL K (2 + 2) | ((x⁻¹ * y : AdelicGLn.integralFiniteGL K (2 + 2)) : FA K (2 + 2)) ∈ levOn S U} :=
      hopen.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
    filter_upwards [ho.mem_nhds (by simp)] with y hy
    have := hχR x _ hy
    rwa [mul_inv_cancel_left] at this
  · by_cases hp : P h
    · exact Or.inr (if_pos hp)
    · exact Or.inl (if_neg hp)
  · refine if_pos ⟨0, 1, one_mem _, ?_⟩
    rw [show nn (0 : UPos (2 + 2) 2 → 𝔸[K]) = 1 from unipOne_zero 2]
    simp
  · intro h₀ h X e
    simp only [χ, Subgroup.coe_mul, hL _ _ X e]
  · intro d₁ d₂ h e hne
    have hP : P h := by
      by_contra hn
      exact hne (if_neg hn)
    obtain ⟨X, u, hu, e'⟩ := hP
    have key : blk (finEmb K 2 d₁) (finEmb K 2 d₂) = unipGL X * finEmb K (2 + 2) u := by
      have a1 := congrArg Subtype.val e
      have a2 := congrArg Subtype.val e'
      rw [blkLaws.1, finite_projection_integral_coe d₁.2, finite_projection_integral_coe d₂.2] at a1
      rw [Subgroup.coe_mul, finite_projection_integral_coe (hle hu)] at a2
      have z0 : zt K 0 = 1 := by
        rw [zt, ← map_one (centralSection K 2)]
        exact congrArg _ (Subtype.ext Real.exp_zero)
      rw [neg_zero, z0, mul_one, mul_one] at a1
      exact a1.symm.trans a2
    have hb := blocks_read (x := (finEmb K 2 d₁).val) (y := (finEmb K 2 d₂).val) (X := X) (A := (finEmb K (2 + 2) u).val)
      (congrArg Units.val key)
    exact ⟨block_mem S m (fun w => (hm w).trans inf_le_left) d₁.2 (fun i => finSumFinEquiv (Sum.inl i))
        (fun _ _ h => Sum.inl_injective (finSumFinEquiv.injective h)) hu fun i j => (hb i j).1,
      block_mem S m (fun w => (hm w).trans inf_le_right) d₂.2 (fun i => finSumFinEquiv (Sum.inr i))
        (fun _ _ h => Sum.inr_injective (finSumFinEquiv.injective h)) hu fun i j => (hb i j).2⟩
end
