module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle001
import GroundTheory.AutomorphicForms.RealIwasawaIntegration
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle002
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle002
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

private theorem rop_mem (f : CC K n) (v : L2 μ) (hv : v ∈ cuspidalL2 μ) : Rop μ f v ∈ cuspidalL2 μ :=
  UnitaryRep.IsInvariant.integrated_mem _ μ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ) _ hv

private theorem pc_rop_pc (f : CC K n) : Pc μ ∘L Rop μ f ∘L Pc μ = Rop μ f ∘L Pc μ :=
  ContinuousLinearMap.ext fun v => Submodule.starProjection_eq_self_iff.2
    (rop_mem μ f _ ((cuspidalL2 μ).starProjection_apply_mem v))

private theorem adjoint_pc : ContinuousLinearMap.adjoint (Pc μ) = Pc μ :=
  (isSelfAdjoint_starProjection (cuspidalL2 μ)).adjoint_eq

private theorem adjoint_rop (f : CC K n) :
    ContinuousLinearMap.adjoint (Rop μ f) = Rop μ (CuspidalProjection.ccStar f) := by
  have := isInvInvariant_of_isMulRightInvariant μ
  exact ((rightRegularRep (Gam K n) μ).adjoint_integrated μ (UnitaryRep.ccToL1 μ f)).trans
    (congrArg _ (CuspidalProjection.ccToL1_ccStar (μ := μ) f).symm)

private theorem adjoint_rop_star (f : CC K n) :
    ContinuousLinearMap.adjoint (Rop μ (CuspidalProjection.ccStar f)) = Rop μ f := by
  rw [← adjoint_rop, ContinuousLinearMap.adjoint_adjoint]

private theorem pc_comm (f : CC K n) : Pc μ ∘L Rop μ f = Rop μ f ∘L Pc μ := by
  have h := congrArg ContinuousLinearMap.adjoint (pc_rop_pc μ (CuspidalProjection.ccStar f))
  simp only [ContinuousLinearMap.adjoint_comp, adjoint_pc, adjoint_rop_star] at h
  rw [← pc_rop_pc μ f, ← h, ContinuousLinearMap.comp_assoc]

private theorem hs_of_decay (f : CC K n) (h : PositivityTheory.Rg.Tf.Core.CuspDecay μ f) :
    IsHilbertSchmidt (Rop μ f ∘L Pc μ) := by
  obtain ⟨C, hC⟩ := h 0
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let T := Rop μ f ∘L (cuspidalL2 μ).subtypeL
  let e : RightCosetSpace (Gam K n) → StrongDual ℂ (cuspidalL2 μ) := fun q =>
    (rconvCLM (Gam K n) μ f (Quotient.out q)).comp (cuspidalL2 μ).subtypeL
  have he : ∀ q, ‖e q‖ ≤ max C 0 := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun w => ?_
    change ‖rconv (Gam K n) μ f (w : L2 μ) (Quotient.out q)‖ ≤ _
    have hb : ‖rconv (Gam K n) μ f (w : L2 μ) (Quotient.out q)‖ ≤ C * ‖(w : L2 μ)‖ := by
      simpa using hC w w.2 (Quotient.out q)
    refine hb.trans ?_
    rw [Submodule.coe_norm]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hout : ∀ (φ : L2 μ) (q : RightCosetSpace (Gam K n)),
      rconvQ (Gam K n) μ f φ q = rconv (Gam K n) μ f φ (Quotient.out q) := by
    intro φ q
    obtain ⟨a, rfl⟩ := mk_surjective (Gam K n) q
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K n)).1 (Quotient.out_eq (mk (Gam K n) a))
    rw [rconvQ_mk, ← hγ]
    exact (rconv_mul_left (Gam K n) μ f φ γ.2 a).symm
  have hae : ∀ w, T w =ᵐ[quotientMeasure (Gam K n) μ] fun q => e q w := by
    intro w
    filter_upwards [integrated_ae_eq_rconvQ (Gam K n) μ f (w : L2 μ)] with q hq
    exact hq.trans (hout _ q)
  have hT : IsHilbertSchmidt T := isHilbertSchmidt_of_ae_eq_dual T e (max C 0) he hae
  have hcomp := hT.comp_right (cuspidalL2 μ).orthogonalProjectionOnto
  convert hcomp using 1
  ext v
  rfl

end

theorem UpperTheory.ConvolutionTheory.C.decayTraceClass :
    UpperTheory.ConvolutionTheory.C.DecayTraceClass := by
  intro K _ _ n μ _ a g M ha hg _
  have hA := hs_of_decay μ a ha
  have hB : IsHilbertSchmidt (Rop μ g ∘L Pc μ) := by
    have h := (hs_of_decay μ _ hg).adjoint
    rw [ContinuousLinearMap.adjoint_comp, adjoint_pc, adjoint_rop_star, pc_comm] at h
    exact h
  have e : Pc μ ∘L (Rop μ a ∘L M ∘L Rop μ g) ∘L Pc μ =
      (Rop μ a ∘L Pc μ) ∘L (M ∘L (Rop μ g ∘L Pc μ)) :=
    ContinuousLinearMap.ext fun v =>
      DFunLike.congr_fun (pc_comm μ a) (M (Rop μ g (Pc μ v)))
  rw [e]
  exact isTraceClass_comp hA (hB.comp_left M)
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.twistUnitary :
    UpperTheory.ConvolutionTheory.C.TwistUnitary := by
  intro K _ _ n μ _ θ
  have hp' : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, θ.e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by
    rw [← θ.mem_gam, θ.e.apply_symm_apply]
  obtain ⟨h1, q1⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (Gam K n) μ θ.e θ.mem_gam θ.pres
  obtain ⟨h2, q2⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (Gam K n) μ θ.e.symm hg' hp'
  let Ul : L2 μ →ₗᵢ[ℂ] L2 μ := Lp.compMeasurePreservingₗᵢ ℂ _ q2
  let Ui : L2 μ →ₗᵢ[ℂ] L2 μ := Lp.compMeasurePreservingₗᵢ ℂ _ q1
  have hUl : ∀ ψ : L2 μ, (Ul ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (θ.e.symm (Quotient.out y))) :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ q2
  have hUi : ∀ ψ : L2 μ, (Ui ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (θ.e (Quotient.out y))) :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ q1
  have hUθ : ∀ ψ : L2 μ, θ.U ψ = Ul ψ := fun ψ =>
    Lp.ext ((θ.U_spec ψ).trans (hUl ψ).symm)
  have hTS : ∀ y : RightCosetSpace (Gam K n),
      mk (Gam K n) (θ.e.symm (Quotient.out (mk (Gam K n) (θ.e (Quotient.out y))))) = y := fun y => by
    have := h2 (θ.e (Quotient.out y))
    rw [θ.e.symm_apply_apply] at this
    exact this.trans (Quotient.out_eq y)
  have hST : ∀ y : RightCosetSpace (Gam K n),
      mk (Gam K n) (θ.e (Quotient.out (mk (Gam K n) (θ.e.symm (Quotient.out y))))) = y := fun y => by
    have := h1 (θ.e.symm (Quotient.out y))
    rw [θ.e.apply_symm_apply] at this
    exact this.trans (Quotient.out_eq y)
  have hlr : ∀ v : L2 μ, Ul (Ui v) = v := fun v => by
    refine Lp.ext ?_
    filter_upwards [hUl (Ui v), q2.quasiMeasurePreserving.ae_eq_comp (hUi v)] with y a b
    simp only [Function.comp_apply] at b
    rw [a, b, hST]
  have hrl : ∀ v : L2 μ, Ui (Ul v) = v := fun v => by
    refine Lp.ext ?_
    filter_upwards [hUi (Ul v), q1.quasiMeasurePreserving.ae_eq_comp (hUl v)] with y a b
    simp only [Function.comp_apply] at b
    rw [a, b, hTS]
  let U : L2 μ ≃ₗᵢ[ℂ] L2 μ :=
    { toLinearEquiv := LinearEquiv.ofLinearMap Ul.toLinearMap Ui.toLinearMap
        (LinearMap.ext hlr) (LinearMap.ext hrl)
      norm_map' := Ul.norm_map }
  have hUU : ∀ v, U v = Ul v := fun _ => rfl
  have hcomm : ∀ v, Ul (Pc μ v) = Pc μ (Ul v) := fun v => by
    have := DFunLike.congr_fun θ.U_comm v
    simp only [ContinuousLinearMap.comp_apply] at this
    rwa [hUθ, hUθ] at this
  have hmem : ∀ v : L2 μ, v ∈ cuspidalL2 μ ↔ Pc μ v = v := fun v =>
    (Submodule.starProjection_eq_self_iff).symm
  refine ⟨U, ?_, ?_, ?_⟩
  · ext1 v
    exact (hUθ v).symm
  · intro g v
    rw [hUU, hUU]
    refine Lp.ext ?_
    have r1 := (measurePreserving_rightMul (Γ := Gam K n) μ (θ.e g)).quasiMeasurePreserving
    filter_upwards [hUl (rightRegularRep (Gam K n) μ g v),
      q2.quasiMeasurePreserving.ae_eq_comp (coeFn_rightRegularRep (Gam K n) μ g v),
      coeFn_rightRegularRep (Gam K n) μ (θ.e g) (Ul v),
      r1.ae_eq_comp (hUl v)] with y a b c d
    simp only [Function.comp_apply] at b d
    rw [a, b, c, d]
    congr 1
    obtain ⟨x, rfl⟩ := mk_surjective (Gam K n) y
    have e1 := congrArg (rightMul (Gam K n) g) (h2 x)
    simp only [rightMul_mk] at e1
    rw [rightMul_mk, rightMul_mk, h2 (x * θ.e g), map_mul, θ.e.symm_apply_apply]
    exact e1
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      have hv' := (hmem v).1 hv
      refine (hmem _).2 ?_
      change Pc μ (Ul v) = Ul v
      rw [← hcomm, hv']
    · intro w hw
      refine ⟨Ui w, ?_, hlr w⟩
      have hw' := (hmem w).1 hw
      refine (hmem _).2 ?_
      have : Ul (Pc μ (Ui w)) = Ul (Ui w) := by rw [hcomm, hlr, hw']
      exact Ul.injective this
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

section SlopeTestRemainingChoices

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem isHS_prj (E : Submodule ℂ H) [FiniteDimensional ℂ E] : IsHilbertSchmidt (prj E) := by
  have hcl : E.topologicalClosure = E :=
    (Submodule.closed_of_finiteDimensional E).submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance
  have h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL) := by
    rw [isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top enorm_lt_top
  exact h1.comp_right E.topologicalClosure.orthogonalProjection

private theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem _ v
  rwa [hV.submodule_topologicalClosure_eq] at h

private theorem prj_eq_zero {V : Submodule ℂ H} {v : H} (hv : v ∈ Vᗮ) : prj V v = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).2 (by rwa [Submodule.orthogonal_closure])

private theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem sub_prj_mem (V : Submodule ℂ H) (v : H) : v - prj V v ∈ Vᗮ := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := V.topologicalClosure) v
  rwa [Submodule.orthogonal_closure] at h

private theorem prj_comm {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (hinv : ∀ v ∈ V, A v ∈ V) (v : H) : prj V (A v) = A (prj V v) := by
  have hu := sub_prj_mem V v
  have hadj : ContinuousLinearMap.adjoint A = A := (ContinuousLinearMap.isSelfAdjoint_iff').1 hA
  have hAu : A (v - prj V v) ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
    exact hu _ (hinv w hw)
  have h : A v = A (prj V v) + A (v - prj V v) := by
    rw [← map_add (f := _)]; congr 1; abel
  rw [h, map_add (f := _), prj_eq_zero hAu, add_zero, prj_self (hinv _ (prj_mem hV v))]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.C.eigSummands :
    UpperTheory.ConvolutionTheory.C.EigSummands := by
  intro H ι _ _ _ V W A x hc ho hW hA hinv hfd
  classical
  let E : ι → Submodule ℂ H := fun i => eigIn (V i) A x
  have hVW : ∀ i, V i ≤ W := fun i => hW ▸ (le_iSup V i).trans (Submodule.le_topologicalClosure _)
  have hEW : ∀ i, E i ≤ eigIn W A x := fun i => inf_le_inf_right _ (hVW i)
  have hEV : ∀ i, E i ≤ V i := fun i => inf_le_left
  have hEo : Pairwise fun i j => E i ⟂ E j := fun i j hij => (ho hij).mono (hEV i) (hEV j)
  have hfin : {i | E i ≠ ⊥}.Finite := by
    have hex : ∀ i : {i | E i ≠ ⊥}, ∃ v ∈ E i, v ≠ 0 := fun i => (Submodule.ne_bot_iff _).1 i.2
    choose v hvE hv0 using hex
    have hli : LinearIndependent ℂ v := linearIndependent_of_ne_zero_of_inner_eq_zero hv0 fun i j hij =>
      (hEo fun e => hij (Subtype.ext e)).inner_eq (hvE i) (hvE j)
    let v' : {i | E i ≠ ⊥} → eigIn W A x := fun i => ⟨v i, hEW i (hvE i)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp (eigIn W A x).subtype hli
    exact Set.finite_coe_iff.1 hli'.finite_of_isNoetherian
  let s := hfin.toFinset
  have hs : ∀ i, i ∈ s ↔ E i ≠ ⊥ := fun i => by simp [s]
  have hPE : ∀ i, ∀ v ∈ eigIn W A x, prj (V i) v ∈ E i := by
    intro i v hv
    refine mem_eigIn.2 ⟨prj_mem (hc i) v, ?_⟩
    rw [← prj_comm (hc i) hA (hinv i), (mem_eigIn.1 hv).2, map_smul]
  have hPP : ∀ i j, i ≠ j → ∀ v, prj (V j) (prj (V i) v) = 0 := fun i j hij v =>
    prj_eq_zero ((ho hij) (prj_mem (hc i) v))
  have hsup : eigIn W A x = ⨆ i ∈ s, E i := by
    refine le_antisymm (fun v hv => ?_) (iSup₂_le fun i _ => hEW i)
    have hu : ∑ i ∈ s, prj (V i) v ∈ ⨆ i ∈ s, E i :=
      Submodule.sum_mem _ fun i hi => (le_iSup₂_of_le i hi le_rfl : E i ≤ ⨆ i ∈ s, E i) (hPE i v hv)
    have huE : ∑ i ∈ s, prj (V i) v ∈ eigIn W A x :=
      (iSup₂_le fun i _ => hEW i : (⨆ i ∈ s, E i) ≤ eigIn W A x) hu
    have hw : v - ∑ i ∈ s, prj (V i) v ∈ W := sub_mem (mem_eigIn.1 hv).1 (mem_eigIn.1 huE).1
    have hPw : ∀ j, prj (V j) (v - ∑ i ∈ s, prj (V i) v) = 0 := by
      intro j

      rw [map_sub, map_sum]
      by_cases hj : j ∈ s
      · rw [Finset.sum_eq_single_of_mem j hj (fun i _ hij => hPP i j hij v), prj_self (prj_mem (hc j) v), sub_self]
      · have h0 : prj (V j) v = 0 := by
          have hb : E j = ⊥ := by_contra fun h => hj ((hs j).2 h)
          have h1 := hPE j v hv
          rw [hb] at h1
          exact (Submodule.mem_bot ℂ).1 h1
        rw [h0, Finset.sum_eq_zero (fun i hi => hPP i j (ne_of_mem_of_not_mem hi hj) v), sub_zero]
    have hperp : v - ∑ i ∈ s, prj (V i) v ∈ Wᗮ := by
      rw [← hW, Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro j
      have h := sub_prj_mem (V j) (v - ∑ i ∈ s, prj (V i) v)
      rwa [hPw j, sub_zero] at h
    have hz : v - ∑ i ∈ s, prj (V i) v = 0 :=
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hperp _ hw)
    rw [sub_eq_zero.1 hz]
    exact hu
  refine ⟨s, hs, hsup, fun T => ?_⟩
  have hS : (⨆ i : s, E i) = eigIn W A x := by
    rw [hsup, iSup_subtype']
  have htc : IsTraceClass (prj (⨆ i : s, E i) ∘L T ∘L prj (⨆ i : s, E i)) := by
    rw [hS]
    exact isTraceClass_comp (isHS_prj _) ((isHS_prj _).comp_left T)
  have h := UpperTheory.ConvolutionTheory.C.traceSum H s (fun i => E i) T (fun i j hij => hEo fun e => hij (Subtype.ext e)) htc
  rw [hS] at h
  rw [h.unique (hasSum_fintype _)]
  exact Finset.sum_coe_sort s fun i => trOn (E i) T
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.eigSplit :
    UpperTheory.ConvolutionTheory.C.EigSplit := by
  intro H _ _ _ W A hW hA hinv hK η hη
  have hsa : IsSelfAdjoint A := isSelfAdjoint_of_nonneg hA
  obtain ⟨hfin, hfd⟩ := UpperTheory.eigIn_finite_above_of_isCompactOperator H W A hW hsa hinv hK η hη
  obtain ⟨s, b, hb⟩ := UpperTheory.exists_hilbertBasis_prj_eigenvectors_of_isCompactOperator H W A hW hsa hinv hK
  have hS : ∀ x, x ∈ hfin.toFinset ↔ η < x ∧ eigIn W A x ≠ ⊥ := fun x => by simp
  refine ⟨hfin.toFinset, hS, fun x hx => hfd x ((hS x).1 hx).1, fun φ c T hφ hc hφc hT => ?_⟩
  rw [UpperTheory.trOn_sub_sum_eq_trace_comp_compression H W (eigIn W A) hfin.toFinset (fun x => (φ x : ℂ)) (cfc φ A) T (fun x => inf_le_left) hT]
  have hmem : ∀ v, prj W v ∈ W := fun v => by
    have h : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hW.submodule_topologicalClosure_eq] at h
  have hPP : ∀ v, prj W (prj W v) = prj W v := fun v =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ v)
  refine UpperTheory.norm_trace_comp_le_mul_traceNorm H s b _ _ c hc hT fun i => ?_
  obtain ⟨μ, hμ⟩ := hb i
  have hF := UpperTheory.cfc_apply_of_eigenvector H A hsa φ hφ μ _ hμ
  have hD : (prj W ∘L cfc φ A ∘L prj W - ∑ x ∈ hfin.toFinset, (φ x : ℂ) • prj (eigIn W A x)) (b i) =
      (if μ ∈ hfin.toFinset then 0 else (φ μ : ℂ)) • prj W (b i) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, hF, map_smul, hPP, UpperTheory.prj_eigIn_of_eigenvector_prj H W A hW hsa (b i) μ _ hμ, smul_ite, smul_zero,
      Finset.sum_ite_eq']
    split_ifs <;> simp
  rw [hD]
  by_cases h0 : prj W (b i) = 0
  · exact ⟨0, by simpa using hc, by simp [h0]⟩
  refine ⟨if μ ∈ hfin.toFinset then 0 else (φ μ : ℂ), ?_, by simp only [map_smul, ContinuousLinearMap.comp_apply, hPP]⟩
  split_ifs with hm
  · simpa using hc
  have hne : eigIn W A μ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨_, ⟨hmem _, Module.End.mem_eigenspace_iff.2 hμ⟩, h0⟩
  have hle : μ ≤ η := not_lt.1 fun h => hm ((hS μ).2 ⟨h, hne⟩)
  have hge : 0 ≤ μ := by
    have h1 := (ContinuousLinearMap.nonneg_iff_isPositive.1 hA).re_inner_nonneg_right (prj W (b i))
    rw [hμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
    have h2 : 0 < ‖prj W (b i)‖ ^ 2 := by positivity
    have h3 : 0 ≤ μ * ‖prj W (b i)‖ ^ 2 := by
      have : RCLike.re ((μ : ℂ) * ((‖prj W (b i)‖ : ℝ) : ℂ) ^ 2) = μ * ‖prj W (b i)‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; rfl
      rw [← this]; exact h1
    exact nonneg_of_mul_nonneg_left h3 h2
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hφc μ ⟨hge, hle⟩
end
