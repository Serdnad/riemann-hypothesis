module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CentralIntegrated
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle003
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
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

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_mem_of_e {n : ℕ} (S : Subalgebra ℂ (HarishChandra.U n))
    (h : ∀ a b, HarishChandra.e (a, b) ∈ S) (x : HarishChandra.U n) : x ∈ S := by
  induction x using HarishChandra.U.induction with
  | halg r => exact S.algebraMap_mem r
  | hι X =>
    rw [HarishChandra.ι_eq_sum_e]
    exact S.sum_mem fun a _ => S.smul_mem (h a.1 a.2) _
  | hmul a b ha hb => exact S.mul_mem ha hb
  | hadd a b ha hb => exact S.add_mem ha hb

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_prod (n : ℕ) (u : ℂ) :
    (∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k) : MvPolynomial (Fin n) ℂ) =
      u ^ n • (1 : MvPolynomial (Fin n) ℂ) +
        ∑ i : Fin n, u ^ (n - (i + 1)) • MvPolynomial.esymm (Fin n) ℂ (i + 1) := by
  have h := congrArg (Polynomial.eval (MvPolynomial.C u : MvPolynomial (Fin n) ℂ))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
  rw [h, Finset.sum_range_succ', add_comm, ← Fin.sum_univ_eq_sum_range
    (fun i => MvPolynomial.esymm (Fin n) ℂ (i + 1) * MvPolynomial.C u ^ (n - (i + 1))) n]
  congr 1
  · rw [MvPolynomial.esymm_zero, MvPolynomial.smul_eq_C_mul, map_pow, Nat.sub_zero, mul_comm]
  · exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_center {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {z : Cm.UC E n} (h : ∀ τ i j, Cm.genC τ i j * z = z * Cm.genC τ i j) :
    z ∈ Subalgebra.center ℂ (Cm.UC E n) := by
  have : Algebra.adjoin ℂ {x : Cm.UC E n | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (h τ i j).symm
  exact Subalgebra.mem_center_iff.2 fun x =>
    (this (Cm.adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top) z rfl).symm

theorem UpperTheory.ConvolutionTheory.Dp.capZc :
    UpperTheory.ConvolutionTheory.Dp.CapZc := by
  intro E _ _ _ n τ
  obtain ⟨⟨j, hj⟩, hiff⟩ := UpperTheory.ConvolutionTheory.Dp.jGen E n τ
  have hg := (hiff j).1 hj
  set w : Fin n → Subalgebra.center ℂ (HarishChandra.U n) := fun i =>
    (HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ with hw
  have hzc : ∀ i : Fin n, UpperTheory.ConvolutionTheory.zc τ i = j (w i) := fun i => by
    obtain ⟨j', hj', e⟩ := Classical.epsilon_spec
      (p := fun z => ∃ j, UpperTheory.ConvolutionTheory.IsJ τ j ∧ z = j (w i : HarishChandra.U n)) ⟨_, j, hj, rfl⟩
    refine e.trans ?_
    exact capZc_mem_of_e (AlgHom.equalizer j' j) (fun a b => ((hiff j').1 hj' a b).trans (hg a b).symm) _
  have hwH : ∀ i, HarishChandra.harishChandraHom (w i) = MvPolynomial.esymm (Fin n) ℂ (i + 1) := fun i => by
    rw [← HarishChandra.harishChandraEquiv_apply, hw, AlgEquiv.apply_symm_apply]
  refine ⟨fun i => ?_, fun u => ?_⟩
  · rw [hzc]
    refine capZc_center fun σ a b => ?_
    by_cases e : σ = τ
    · subst e
      rw [← hg]
      exact (map_mul j _ _).symm.trans
        ((congrArg j (Subalgebra.mem_center_iff.1 (w i).2 _)).trans (map_mul j _ _))
    · have := capZc_mem_of_e ((Subalgebra.centralizer ℂ {Cm.genC σ a b}).comap j) (fun c d => by
        rintro _ rfl
        rw [RingHom.coe_coe, hg]
        exact Cm.commute_genC e a b c d) (w i)
      exact this _ rfl
  · obtain ⟨z, hz, hH⟩ := UpperTheory.ConvolutionTheory.Dp.capHC n u
    have e : z = u ^ n • 1 + ∑ i : Fin n, u ^ (n - (i + 1)) • w i := by
      apply HarishChandra.harishChandraHom_injective
      rw [hH, capZc_prod]

      simp only [map_add (f := _), map_smul, map_one, map_sum, hwH]
    have e2 := congrArg (j.comp (Subalgebra.center ℂ (HarishChandra.U n)).val) e

    simp only [map_add (f := _), map_smul, map_one, map_sum] at e2
    simp only [hzc]
    refine Eq.trans ?_ e2
    change _ = j (z : HarishChandra.U n)
    rw [hz, Fb.map_qdet]
    simp only [hg]
    rfl
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem aux {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (W : Submodule ℂ H) (e : G → G) (he : Function.Surjective e) (U : H →L[ℂ] H) (h1 : ∀ v, ‖U v‖ = ‖v‖)
    (h2 : Function.Surjective U) (h3 : ∀ g v, U (π g v) = π (e g) (U v)) (hc : ∀ v, U v ∈ W ↔ v ∈ W) (V : Submodule ℂ H) :
    IsSummandOf π W V ↔ IsSummandOf π W (V.map U.toLinearMap) := by
  let I : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, h1⟩
  have hinj : Function.Injective U := I.injective
  have hcm : ∀ X : Submodule ℂ H, (X.map U.toLinearMap).comap U.toLinearMap = X :=
    fun X => Submodule.comap_map_eq_of_injective hinj X
  have hmc : ∀ X : Submodule ℂ H, (X.comap U.toLinearMap).map U.toLinearMap = X :=
    fun X => Submodule.map_comap_eq_of_surjective h2 X
  have cl1 : ∀ X : Submodule ℂ H, IsClosed (X : Set H) → IsClosed (X.map U.toLinearMap : Set H) :=
    fun X hX => I.isometry.isClosedEmbedding.isClosedMap _ hX
  have cl2 : ∀ X : Submodule ℂ H, IsClosed (X : Set H) → IsClosed (X.comap U.toLinearMap : Set H) :=
    fun X hX => hX.preimage U.continuous
  have i1 : ∀ X : Submodule ℂ H, π.IsInvariant X → π.IsInvariant (X.map U.toLinearMap) := by
    rintro X hX g _ ⟨v, hv, rfl⟩
    obtain ⟨g, rfl⟩ := he g
    exact ⟨_, hX g v hv, h3 g v⟩
  have i2 : ∀ X : Submodule ℂ H, π.IsInvariant X → π.IsInvariant (X.comap U.toLinearMap) := fun X hX g v hv => by
    show U _ ∈ X
    rw [h3]
    exact hX _ _ hv
  constructor
  · intro h
    refine ⟨?_, cl1 _ h.closed, i1 _ h.inv, fun e => h.ne_bot ?_, fun X hX c i => ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact (hc v).2 (h.le hv)
    · rw [← hcm V, e, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.2 hinj
    · rcases h.irred _ ((Submodule.comap_mono hX).trans (hcm V).le) (cl2 _ c) (i2 _ i) with e | e
      · left; rw [← hmc X, e, Submodule.map_bot]
      · right; rw [← hmc X, e]
  · intro h
    have a1 := cl2 _ h.closed
    have a2 := i2 _ h.inv
    rw [hcm] at a1 a2
    refine ⟨fun v hv => (hc v).1 (h.le ⟨v, hv, rfl⟩), a1, a2, fun e => h.ne_bot ?_, fun X hX c i => ?_⟩
    · rw [e, Submodule.map_bot]
    · rcases h.irred _ (Submodule.map_mono hX) (cl1 _ c) (i1 _ i) with e | e
      · left; rw [← hcm X, e, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.2 hinj
      · right; rw [← hcm X, e, hcm]

theorem UpperTheory.ConvolutionTheory.Dp.twSummand :
    UpperTheory.ConvolutionTheory.Dp.TwSummand := by
  intro K _ _ n μ _ θ V
  obtain ⟨h1, h2, h3⟩ := twUnitary K n μ θ
  have hinj : Function.Injective θ.U := (⟨θ.U.toLinearMap, h1⟩ : LL μ →ₗᵢ[ℂ] LL μ).injective
  refine aux _ _ θ.e θ.e.surjective θ.U h1 h2 h3 (fun v => ?_) V
  have e : θ.U (PositivityTheory.Rg.Tf.Core.Pc μ v) = PositivityTheory.Rg.Tf.Core.Pc μ (θ.U v) := DFunLike.congr_fun θ.U_comm v
  have a : ∀ x, PositivityTheory.Rg.Tf.Core.Pc μ x = x ↔ x ∈ cuspidalL2 μ := fun x => Submodule.starProjection_eq_self_iff
  rw [← a, ← a, ← e, hinj.eq_iff]
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.locEmb :
    UpperTheory.ConvolutionTheory.Dp.LocEmb := by
  intro E _ _ _ n μ _ π V h
  have hcar := h.carrier_eq
  have hcen : ∀ ψ : Cm.carrier π, ψ.1 ∈ centralCuspForms E n := fun ψ => (hcar.le ψ.2).1
  have hV : ∀ ψ : Cm.carrier π, clsL μ ψ.1 ∈ V := fun ψ => (hcar.le ψ.2).2
  obtain ⟨hinj, -, heq, -⟩ := UpperTheory.ConvolutionTheory.Dp.clsBasic E n μ
  obtain ⟨-, -, -, hdense⟩ := UpperTheory.ConvolutionTheory.Dp.formsIrr E n μ V h.summand
  let J0 : Cm.carrier π →ₗ[ℂ] V := ((clsL μ).comp (Cm.carrier π).subtype).codRestrict V hV
  have hJ0 : ∀ ψ, (J0 ψ).1 = clsL μ ψ.1 := fun _ => rfl
  refine ⟨J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · have hi : Function.Injective J0 := fun a b hab => by
      have h0 : clsL μ (a.1 - b.1) = 0 := by
        rw [map_sub, ← hJ0, ← hJ0, hab, sub_self]
      exact Subtype.ext (sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hcen a) (hcen b)) h0))
    exact hi.comp (Cm.carrierEq π).symm.injective
  · intro v
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himg : (Subtype.val '' Set.range (J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap) : Set (LL μ)) =
        ((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) := by
      ext x
      constructor
      · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
        exact ⟨_, hcar ▸ ((Cm.carrierEq π).symm φ).2, rfl⟩
      · rintro ⟨ψ, hψ, rfl⟩
        have hψ' : ψ ∈ Cm.carrier π := hcar ▸ hψ
        refine ⟨_, ⟨Cm.carrierEq π ⟨ψ, hψ'⟩, rfl⟩, ?_⟩
        simp [hJ0]
    have hc : (v : LL μ) ∈ closure (((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) :=
      hdense.ge v.2
    rw [← himg] at hc
    exact hc
  · intro ψ
    simp [hJ0]
  · intro w g φ
    obtain ⟨ψ, rfl⟩ := (Cm.carrierEq π).surjective φ
    apply Subtype.ext
    set ψ' := (Cm.carrierEq π).symm (π.locRep w g (Cm.carrierEq π ψ)) with hψ'
    have hx : ∀ x, ψ'.1.1 x = ψ.1.1 (x * finGL E n (locGL E n w g)) := fun x => by
      have h1 : Cm.carrierEq π ψ' = π.locRep w g (Cm.carrierEq π ψ) := (Cm.carrierEq π).apply_symm_apply _
      exact congrArg (fun f : π.V => f.1.1 x) h1
    have h2 := heq ψ.1 (hcen ψ) ψ'.1 (finGL E n (locGL E n w g)) hx
    show clsL μ ψ'.1 = RG μ (finGL E n (locGL E n w g)) (clsL μ ((Cm.carrierEq π).symm (Cm.carrierEq π ψ)).1)
    rw [LinearEquiv.symm_apply_apply]
    exact h2
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

theorem oinf_toLp {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n) (w : CuspL2 μ) :
    Oinf μ ν β (toLp μ w) = toLp μ ((archRepT μ).integrated ν β w) := by
  refine Eq.trans ?_ (toLp_integrated_archRepT μ ν (γ := β) β.continuous β.hasCompactSupport w).symm
  rw [Oinf, UnitaryRep.integrated_ccToL1_apply]
  rfl

theorem rUC_tmul {K : Type} [Field K] [NumberField K] {n : ℕ} (c : ℂ) (p : UEnv K n) (f : (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (g : archGroup K n) : (rUC (c ⊗ₜ p) f).1 g = c * ((isExpLieAlgebra K n).rightUAction p f).1 g := by
  have h : rUC (c ⊗ₜ p) = algebraMap ℂ _ c * (isExpLieAlgebra K n).rightUAction (F := ℂ) p :=
    Algebra.TensorProduct.lift_tmul _ _ _ c p
  rw [h]
  rfl


theorem lactCen_of_gen (K : Type) [Field K] [NumberField K] (n : ℕ)
    (hG : Subgroup.closure (Set.range (isExpLieAlgebra K n).expG) = ⊤) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n) (hβ : SmoothT β) :
    ∀ p ∈ (isExpLieAlgebra K n).centerU, ∀ q ∈ (isExpLieAlgebra K n).centerU, ∀ φ ∈ centralCuspForms K n,
      Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) (clsL μ φ) =
        Oinf μ ν β (clsL μ (uActionCusp K n p φ + Complex.I • uActionCusp K n q φ)) := by
  intro p hp q hq φ hφ
  obtain ⟨h, hl⟩ := lactSpec K n ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β hβ
  have hT : (isExpLieAlgebra K n).IsTestFunction β := ⟨hβ, β.hasCompactSupport⟩
  let f : (isExpLieAlgebra K n).smoothFuns (F := ℂ) := ⟨fun g => β g⁻¹, h⟩
  have e : (fun g => f.1 g⁻¹) = β := funext fun g => by simp only [f, inv_inv]
  have hf : (isExpLieAlgebra K n).IsTestFunction fun g => f.1 g⁻¹ := e ▸ hT
  have hπ : ∀ g, ‖archRepT μ g‖ ≤ 1 := fun g => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact ((archURepT μ).norm_map g v).le
  have key : ∀ z ∈ (isExpLieAlgebra K n).centerU,
      (archRepT μ).integrated ν (fun g => ((isExpLieAlgebra K n).rightUAction z f).1 g⁻¹) (cuspVecL μ φ) =
        (archRepT μ).integrated ν β (cuspVecL μ (uActionCusp K n z φ)) := fun z hz => by
    rw [← (kernel_uAction _ ν (archRepT μ) z f hf).2, central_integrated _ ν (archRepT μ) hπ hG hz hf (isSmoothVector_cuspToL2 μ hφ),
      uAction_cuspToL2 μ hφ, e]
  have e2 : (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β : archGroup K n → ℂ) = fun g =>
      ((isExpLieAlgebra K n).rightUAction p f).1 g⁻¹ + Complex.I * ((isExpLieAlgebra K n).rightUAction q f).1 g⁻¹ := by
    funext g
    have h3 := rUC_tmul 1 p f g⁻¹
    rw [one_mul] at h3
    rw [hl g, map_add (f := _), ← h3, ← rUC_tmul Complex.I q f g⁻¹]
    rfl
  have h1 := (kernel_uAction _ ν (archRepT μ) p f hf).1
  have h2 := (kernel_uAction _ ν (archRepT μ) q f hf).1
  have h4 : ∀ (γ : TI K n) ψ, Oinf μ ν γ (clsL μ ψ) = toLp μ ((archRepT μ).integrated ν γ (cuspVecL μ ψ)) :=
    fun γ ψ => oinf_toLp μ ν γ _
  have h5 : Oinf μ ν β (clsL μ (uActionCusp K n p φ + Complex.I • uActionCusp K n q φ)) =
      Oinf μ ν β (clsL μ (uActionCusp K n p φ)) + Complex.I • Oinf μ ν β (clsL μ (uActionCusp K n q φ)) := by
    rw [(clsL μ).map_add, (clsL μ).map_smul, (Oinf μ ν β).map_add, (Oinf μ ν β).map_smul]
  rw [h5, h4, h4, h4, e2, (isExpLieAlgebra K n).integrated_add_kernel ν _ h1 (h2.const_mul _),
    IsExpLieAlgebra.integrated_const_mul_kernel, key p hp, key q hq, (toLp μ).map_add, (toLp μ).map_smul]

end UpperTheory.ConvolutionTheory.Dp
end
