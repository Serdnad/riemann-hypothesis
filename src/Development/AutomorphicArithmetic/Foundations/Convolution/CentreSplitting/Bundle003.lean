module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle013
import Formalism.RealPlaceAnalysis.Bundle005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
public import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdUnique
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem eq_of_esymm {n : ℕ} {B B' : Multiset ℂ} (hB : B.card = n) (hB' : B'.card = n)
    (h : ∀ i : Fin n, B.esymm (i + 1) = B'.esymm (i + 1)) : B = B' := by
  have h2 : (B.map fun r => Polynomial.X - Polynomial.C r).prod = (B'.map fun r => Polynomial.X - Polynomial.C r).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hB, hB']
    refine Finset.sum_congr rfl fun j hj => ?_
    rcases j with _ | j
    · simp [Multiset.esymm]
    · rw [h ⟨j, by simpa using hj⟩]
  simpa using congrArg Polynomial.roots h2

open UpperTheory.ConvolutionTheory in
theorem UpperTheory.ConvolutionTheory.Dp.sSatUnit :
    UpperTheory.ConvolutionTheory.Dp.SSatUnit := by
  intro K _ _ n μ _ w V B hB
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hB.2.1
  refine ⟨?_, fun B₁ h₁ => eq_of_esymm h₁.1 hB.1 fun i =>
    smul_left_injective ℂ h0 ((h₁.2.2 i v hv).symm.trans (hB.2.2 i v hv))⟩
  have hne : ∀ b ∈ B, b ≠ 0 := by
    intro b hb e
    subst e
    have hn : 0 < n := hB.1 ▸ Multiset.card_pos_iff_exists_mem.2 ⟨_, hb⟩
    have h1 := hB.2.2 ⟨n - 1, by omega⟩ v hv
    have h2 : B.esymm (n - 1 + 1) = 0 := by
      rw [Nat.sub_add_cancel hn, ← hB.1, Multiset.esymm, Multiset.powersetCard_self]
      simpa using hb
    set J := GLnLocal.integralGL (w.adicCompletion K) n
    set x := Cartan.diagPow (w.adicCompletion K) n fun _ => 1 with hx
    have hxc : x ∈ Subgroup.center _ :=
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨_, by rw [Matrix.scalar_apply, hx, Cartan.coe_diagPow]⟩
    have e1 : (fun a : Fin n => if a ≤ (⟨n - 1, by omega⟩ : Fin n) then (1 : ℤ) else 0) = fun _ => 1 :=
      funext fun a => if_pos (Fin.le_def.2 (by have := a.2; simp only; omega))
    have e2 : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} = {QuotientGroup.mk x} := by
      ext c
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [Subgroup.mem_center_iff.1 hxc k]
        exact QuotientGroup.mk_mul_of_mem x hk
      · rintro rfl
        exact ⟨1, J.one_mem, by rw [one_mul]⟩
    have e3 : prj (fixL μ w J) v = v :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv.2)
    have e4 : Hop μ w J x v = rhoL μ w (QuotientGroup.mk x : _ ⧸ J).out v := by
      rw [Hop, e2, finsum_mem_singleton, ContinuousLinearMap.comp_apply, e3]
    rw [h2, zero_smul, Tsph, e1, ContinuousLinearMap.smul_apply, e4] at h1
    rcases smul_eq_zero.1 h1 with h | h
    · refine (Real.rpow_pos_of_pos ?_ _).ne' (Complex.ofReal_eq_zero.1 h)
      exact Nat.cast_pos.2 (Nat.pos_of_ne_zero fun e => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 e))
    · refine h0 (norm_eq_zero.1 ?_)
      have h3 : ∀ g, ‖rhoF μ g v‖ = ‖v‖ := fun g => by
        unfold rhoF
        exact UnitaryRep.norm_map _ _ v
      rw [← h3, ← rhoL, h, norm_zero]
  refine ⟨B.attach.map fun b => Units.mk0 b.1 (hne b.1 b.2), ?_⟩
  rw [Multiset.map_map]
  exact (Multiset.attach_map_val B).symm
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  classical
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL_of_ne h g)).symm

private theorem finProj_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (u : AdelicGLn.FiniteAdelicGL K n) :
    MultiplicityOne.finProj K n u = retractOne (finGL K n u) := by
  rw [← Fb.finEmb_eq]
  exact Subtype.ext rfl

theorem UpperTheory.ConvolutionTheory.Dp.rhoLoc :
    UpperTheory.ConvolutionTheory.Dp.RhoLoc := by
  intro K _ _ n μ _ w g v
  change rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v =
    rightRegularRep (rationalGLOne (K := K) (n := n)) μ (retractOne (finGL K n (locGL K n w g))) v
  rw [finProj_eq, localEmbedding_eq]
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.ConvolutionTheory.Dp.capHC_mem (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

theorem UpperTheory.ConvolutionTheory.Dp.capHC :
    UpperTheory.ConvolutionTheory.Dp.CapHC := by
  intro n u
  refine ⟨⟨_, capHC_mem n (u + ((n : ℂ) - 1) / 2)⟩, rfl, ?_⟩
  rw [HarishChandra.harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [HarishChandra.rhoVec, Pi.neg_apply]
  ring
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.lactSpec :
    UpperTheory.ConvolutionTheory.Dp.LactSpec := by
  intro K _ _ n u β hβ
  obtain ⟨h, hl, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  exact ⟨h, hl u⟩
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_along {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z) = UpperTheory.ConvolutionTheory.along τ z := by
  refine Cm.mixed_ext fun w => ?_
  have h : (Cm.mixEq E (GlobalTheory.CuspRep.atEmb τ z)).2 w = GlobalTheory.CuspRep.atEmb τ z w.1 := Cm.mixRing_snd _ w
  rw [h, PositivityTheory.Rg.Cz.GK.atEmb_apply]
  simp only [UpperTheory.ConvolutionTheory.along]
  by_cases e : w.1 = InfinitePlace.mk τ
  · rw [if_pos e, if_pos e, e]
  · rw [if_neg e, if_neg e]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) (z : ℂ) :
    Cm.ιC E n (GlobalTheory.CuspRep.toL (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z))) = (1 : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b z := by
  rw [Cm.ιC_apply, UpperTheory.ConvolutionTheory.elem]
  congr 2
  refine Subtype.ext ?_
  change Cm.matEq E n (Matrix.single a b (GlobalTheory.CuspRep.atEmb τ z)) = Matrix.single a b (UpperTheory.ConvolutionTheory.along τ z)
  refine Matrix.ext fun i j => ?_
  rw [Cm.matEq_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs
  · exact UpperTheory.ConvolutionTheory.Dp.jGen_along τ z
  · exact map_zero _

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_gen {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (τ : E →+* ℂ)
    (a b : Fin n) :
    (2⁻¹ : ℂ) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b 1 - (2⁻¹ * Complex.I) ⊗ₜ UpperTheory.ConvolutionTheory.elem τ a b Complex.I = Cm.genC τ a b := by
  rw [Cm.genC, AlgRepEndIrreducible.eL, UpperTheory.ConvolutionTheory.Dp.jGen_lie, UpperTheory.ConvolutionTheory.Dp.jGen_lie, TensorProduct.smul_tmul', smul_sub,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one, one_div]

private noncomputable def UpperTheory.ConvolutionTheory.Dp.jGen_lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) :
    HarishChandra.gl n →ₗ[ℂ] A where
  toFun X := ∑ c : Fin n × Fin n, X c.1 c.2 • F c.1 c.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r X := by simp [Finset.smul_sum, mul_smul]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_E {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (c : Fin n × Fin n) : UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c) = F c.1 c.2 := by
  change ∑ d : Fin n × Fin n, (HarishChandra.E c) d.1 d.2 • F d.1 d.2 = _
  rw [Finset.sum_eq_single c]
  · simp [HarishChandra.E]
  · intro d _ hd
    have : ¬ (c.1 = d.1 ∧ c.2 = d.2) := fun h => hd (Prod.ext h.1.symm h.2.symm)
    simp [HarishChandra.E, Matrix.single_apply, this]
  · simp

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) (X Y : HarishChandra.gl n) :
    UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅X, Y⁆ = ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F X, UpperTheory.ConvolutionTheory.Dp.jGen_lin F Y⁆ := by
  have hE : ∀ c d : Fin n × Fin n, UpperTheory.ConvolutionTheory.Dp.jGen_lin F ⁅HarishChandra.E c, HarishChandra.E d⁆ =
      ⁅UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E c), UpperTheory.ConvolutionTheory.Dp.jGen_lin F (HarishChandra.E d)⁆ := by
    intro c d
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, HarishChandra.E_mul_sub_mul,
      UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, UpperTheory.ConvolutionTheory.Dp.jGen_lin_E, hF, map_sub]
    congr 1 <;> split_ifs <;> simp [UpperTheory.ConvolutionTheory.Dp.jGen_lin_E]
  rw [HarishChandra.eq_sum_E X, HarishChandra.eq_sum_E Y]

  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]

private theorem UpperTheory.ConvolutionTheory.Dp.jGen_ex {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) : ∃ f : HarishChandra.U n →ₐ[ℂ] A, ∀ a b, f (HarishChandra.e (a, b)) = F a b := by
  let L : HarishChandra.gl n →ₗ⁅ℂ⁆ A :=
    { UpperTheory.ConvolutionTheory.Dp.jGen_lin F with map_lie' := fun {X Y} => UpperTheory.ConvolutionTheory.Dp.jGen_lin_lie F hF X Y }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ L, fun a b => ?_⟩
  rw [HarishChandra.e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact UpperTheory.ConvolutionTheory.Dp.jGen_lin_E F (a, b)

theorem UpperTheory.ConvolutionTheory.Dp.jGen :
    UpperTheory.ConvolutionTheory.Dp.JGen := by
  intro E _ _ _ n τ
  have key : ∀ j : HarishChandra.U n →ₐ[ℂ] UpperTheory.ConvolutionTheory.UC E n,
      UpperTheory.ConvolutionTheory.IsJ (n := n) τ j ↔ ∀ a b, j (HarishChandra.e (a, b)) = Cm.genC τ a b := fun j =>
    ⟨fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b),
      fun h a b => (h a b).trans (UpperTheory.ConvolutionTheory.Dp.jGen_gen τ a b).symm⟩
  obtain ⟨f, hf⟩ := UpperTheory.ConvolutionTheory.Dp.jGen_ex (Cm.genC (a := n) τ) (Cm.glRel_genC τ)
  exact ⟨⟨f, (key f).2 hf⟩, key⟩
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open scoped InnerProductSpace Topology

private theorem near_one_nhds {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) {v : H} (hpos : 0 < ‖v‖) :
    {g : G | ‖π g v - v‖ < ‖v‖ / 2} ∈ 𝓝 (1 : G) := by
  have hcont : Continuous fun g => π g v := π.continuous_orbit v
  have ht : Filter.Tendsto (fun g => ‖π g v - v‖) (𝓝 (1 : G)) (𝓝 ‖π 1 v - v‖) :=
    (hcont.sub continuous_const).norm.tendsto 1
  rw [UnitaryRep.map_one_apply, sub_self, norm_zero] at ht
  exact ht.eventually_lt_const (half_pos hpos)

private theorem exists_bump_nonzero {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) {v : H} (hpos : 0 < ‖v‖) (ρ : G → ℝ) (β : CompactlySupportedContinuousMap G ℂ)
    (hβa : ∀ g, β g = (ρ g : ℂ)) (hρ0 : ∀ g, 0 ≤ ρ g) (hρ1 : ∫ g, ρ g ∂ν = 1)
    (hρN : ∀ g, ρ g ≠ 0 → g ∈ {g : G | ‖π g v - v‖ < ‖v‖ / 2})
    (h2 : π.integrated ν (UnitaryRep.ccToL1 ν β) v = 0) : False := by
  have hcont : Continuous fun g => π g v := π.continuous_orbit v
  have hin : ∫ g, (ρ g : ℂ) * ⟪v, π g v⟫_ℂ ∂ν = 0 := by
    have h1 := CuspidalProjection.inner_integrated_ccToL1 ν π β v v
    rw [h2, inner_zero_right] at h1
    simp only [hβa] at h1
    exact h1.symm
  have hρi : Integrable ρ ν := by
    by_contra h
    rw [integral_undef h] at hρ1
    exact zero_ne_one hρ1
  have hint : ∀ F : G → ℂ, Continuous F → Integrable (fun g => (ρ g : ℂ) * F g) ν := fun F hF => by
    simp only [← hβa]
    exact (β.continuous.mul hF).integrable_of_hasCompactSupport (β.hasCompactSupport.mul_right)
  have hc1 : Continuous fun g => ⟪v, π g v⟫_ℂ := continuous_const.inner hcont
  have e : ∫ g, (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ ∂ν = -⟪v, v⟫_ℂ := by
    have h3 : (fun g => (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ) =
        fun g => (ρ g : ℂ) * ⟪v, π g v⟫_ℂ - (ρ g : ℂ) * ⟪v, v⟫_ℂ := by
      funext g
      rw [inner_sub_right, mul_sub]
    rw [h3, integral_sub (hint _ hc1) (hint _ continuous_const), hin, integral_mul_const,
      integral_complex_ofReal, hρ1]
    simp
  have hb : ‖∫ g, (ρ g : ℂ) * ⟪v, π g v - v⟫_ℂ ∂ν‖ ≤ ∫ g, ρ g * (‖v‖ * (‖v‖ / 2)) ∂ν := by
    refine norm_integral_le_of_norm_le (hρi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rcases eq_or_ne (ρ g) 0 with h0 | h0
    · simp [h0]
    · have hg : ‖π g v - v‖ < ‖v‖ / 2 := hρN g h0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 g)]
      refine mul_le_mul_of_nonneg_left ?_ (hρ0 g)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hg.le hpos.le)
  rw [e, integral_mul_const, hρ1, one_mul, norm_neg, inner_self_eq_norm_sq_to_K] at hb
  have h4 : ‖((‖v‖ : ℝ) : ℂ) ^ 2‖ = ‖v‖ ^ 2 := by simp
  have h5 : ‖v‖ ^ 2 ≤ ‖v‖ * (‖v‖ / 2) := by
    rw [← h4]
    simpa using hb
  nlinarith

theorem UpperTheory.ConvolutionTheory.Dp.diracSep :
    UpperTheory.ConvolutionTheory.Dp.DiracSep := by
  intro K _ _ n μ _ ν _ v hv
  by_contra hne
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hne
  obtain ⟨ρ, hρ0, hρt, hρ1, -, -, hρN, -⟩ := exists_archBump ν
    (near_one_nhds ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (archP K n) continuous_archP) hpos)
  let β : TI K n := ⟨⟨fun a => (ρ a : ℂ), hρt.continuous _⟩, hρt.2⟩
  exact exists_bump_nonzero ν _ hpos ρ β (fun _ => rfl) hρ0 hρ1 hρN (hv β hρt.1)
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem galAd_eq_adm {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃+* E)
    (s : Ad E ≃+* Ad E) (h : UpperTheory.CBC.IsGalAd σ s) : s.toRingHom = UpperTheory.V.FieldIso.adm σ :=
  (UpperTheory.ConvolutionTheory.K.adUnique E σ s.toRingHom h.1 h.2.1).trans
    (UpperTheory.ConvolutionTheory.K.adUnique E σ (UpperTheory.V.FieldIso.adm σ) (UpperTheory.V.FieldIso.continuous_adm σ)
      (UpperTheory.V.FieldIso.adm_algebraMap σ)).symm

open Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep in
private theorem cinf_real {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃+* E) (c : ℝ) :
    UpperTheory.V.FieldIso.cinf σ (fun _ => (c : ℂ)) = fun _ => (c : ℂ) := by
  funext u
  change coord _ _ = _
  unfold coord
  split_ifs <;> simp

private theorem map_splitCentre {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃+* E) (a : ℕ)
    (t : ℝ) : UpperTheory.V.FieldIso.gaMap a σ (GlobalTheory.UnitaryBC.splitCentre E a t) = GlobalTheory.UnitaryBC.splitCentre E a t := by
  unfold GlobalTheory.UnitaryBC.splitCentre
  rw [UpperTheory.V.FieldIso.gaMap_infGL]
  congr 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  change UpperTheory.V.FieldIso.cinf σ (Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j) =
    Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, ← Complex.ofReal_exp]
    exact cinf_real σ _
  · rw [Matrix.diagonal_apply_ne _ h]
    exact map_zero _

theorem UpperTheory.ConvolutionTheory.Dp.galCentral :
    UpperTheory.ConvolutionTheory.Dp.GalCentral := by
  intro E _ _ _ n σ s h
  refine ⟨fun s' h' => RingEquiv.ext fun x => ?_, fun t => ?_⟩
  · have e := (galAd_eq_adm σ s' h').trans (galAd_eq_adm σ s h).symm
    exact congrArg (fun f : Ad E →+* Ad E => f x) e
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Units.ext (Matrix.ext fun i => i.elim0)
    · have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have ht : t = ⟨Real.exp (n * Module.finrank ℚ E * (Real.log t / (n * Module.finrank ℚ E))), Real.exp_pos _⟩ := by
        refine Subtype.ext ?_
        change (t : ℝ) = Real.exp _
        rw [mul_div_cancel₀ _ (mul_ne_zero hn' hd), Real.exp_log t.2]
      rw [ht, ← UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n, galAd_eq_adm σ s h]
      exact map_splitCentre σ n _
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.twCls :
    UpperTheory.ConvolutionTheory.Dp.TwCls := by
  intro K _ _ n μ _ θ φ hφ ψ hψ
  have hmemS : ∀ g, θ.e.symm g ∈ rationalGLOne (K := K) (n := n) ↔ g ∈ rationalGLOne (K := K) (n := n) := fun g => by
    have h := θ.mem_gam (θ.e.symm g)
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h.symm
  have hpresS : MeasurePreserving θ.e.symm μ μ :=
    MeasurePreserving.symm θ.e.toHomeomorph.toMeasurableEquiv θ.pres
  obtain ⟨hmk, hT⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (rationalGLOne (K := K) (n := n)) μ θ.e.symm hmemS hpresS
  let T : RightCosetSpace (rationalGLOne (K := K) (n := n)) → RightCosetSpace (rationalGLOne (K := K) (n := n)) :=
    fun y => mk _ (θ.e.symm (Quotient.out y))
  have hTmk : ∀ x, T (mk _ x) = mk _ (θ.e.symm x) := hmk
  have hTc : Continuous T := by
    refine (isOpenQuotientMap_mk (rationalGLOne (K := K) (n := n))).isQuotientMap.continuous_iff.2 ?_
    have h : T ∘ mk _ = mk _ ∘ θ.e.symm := funext hTmk
    rw [h]
    exact (continuous_mk _).comp θ.e.symm.continuous
  let Φ := cuspQuot φ.2.1.isLeftInvariant
  let Ψ := cuspQuot ψ.2.1.isLeftInvariant
  have hΦc : Continuous Φ := continuous_cuspQuot _ φ.2.1.continuous
  have hΨc : Continuous Ψ := continuous_cuspQuot _ ψ.2.1.continuous
  have hb := (UpperTheory.ConvolutionTheory.Dp.clsBasic K n μ).2.2.2
  have hout : ∀ (χ : cuspForms K n) (y : RightCosetSpace (rationalGLOne (K := K) (n := n))),
      χ.1 ((Quotient.out y : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) =
        cuspQuot χ.2.1.isLeftInvariant y := fun χ y => by
    have h : mk (rationalGLOne (K := K) (n := n)) (Quotient.out y) = y := Quotient.out_eq y
    conv_rhs => rw [← h]
    rw [cuspQuot_mk]
  have hφa : (clsL μ φ : RightCosetSpace (rationalGLOne (K := K) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Φ :=
    (hb φ hφ).trans (Filter.Eventually.of_forall (hout φ))
  have hψa : (clsL μ ψ : RightCosetSpace (rationalGLOne (K := K) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Ψ :=
    (hb ψ hψ).trans (Filter.Eventually.of_forall (hout ψ))
  have hU : (θ.U (clsL μ ψ) : RightCosetSpace (rationalGLOne (K := K) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Ψ ∘ T :=
    (θ.U_spec _).trans (hT.quasiMeasurePreserving.ae_eq_comp hψa)
  constructor
  · intro h x
    have h1 : Ψ ∘ T =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Φ := by
      rw [h] at hU
      exact hU.symm.trans hφa
    have h2 : Ψ ∘ T = Φ := (Continuous.ae_eq_iff_eq _ (hΨc.comp hTc) hΦc).1 h1
    have h3 := congrFun h2 (mk _ (θ.e x))
    simp only [Function.comp_apply, hTmk, ContinuousMulEquiv.symm_apply_apply] at h3
    simpa only [Ψ, Φ, cuspQuot_mk] using h3
  · intro h
    have h2 : Ψ ∘ T = Φ := by
      funext y
      obtain ⟨x, rfl⟩ := mk_surjective _ y
      simp only [Function.comp_apply, hTmk, Ψ, Φ, cuspQuot_mk]
      rw [h, ContinuousMulEquiv.apply_symm_apply]
    rw [h2] at hU
    exact Lp.ext (hU.trans hφa.symm)
end
