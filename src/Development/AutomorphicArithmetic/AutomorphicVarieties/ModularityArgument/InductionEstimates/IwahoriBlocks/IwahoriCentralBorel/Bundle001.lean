module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle413
import Mathlib.Algebra.Module.StablyFree.Basic
import GroundTheory.AutomorphicForms.Bundle011
public import GroundTheory.AutomorphicForms.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
public import Lean.Meta.ExprDefEq
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem tens_sep {V B : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup B] [Module ℂ B]
    (z : V ⊗[ℂ] B)
    (h : ∀ φ : Module.Dual ℂ V, TensorProduct.lid ℂ B (LinearMap.rTensor B φ z) = 0) : z = 0 := by
  let b := Module.Basis.ofVectorSpace ℂ V
  let F := TensorProduct.equivFinsuppOfBasisLeft (N := B) b
  have key : ∀ (j : _) (y : V ⊗[ℂ] B),
      F y j = TensorProduct.lid ℂ B (LinearMap.rTensor B (b.coord j) y) := by
    intro j y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [F, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  apply F.injective
  rw [map_zero]
  ext j
  rw [key, h]
  simp

private theorem comm_ext {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (g : H × G) (z : V ⊗[ℂ] W) :
    TensorProduct.comm ℂ V W (extTensor X T (g.2, g.1) z) =
      extTensor T X g (TensorProduct.comm ℂ V W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private noncomputable def swapSub {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (S : Subrepresentation (extTensor X T)) : Subrepresentation (extTensor T X) where
  toSubmodule := S.toSubmodule.map (TensorProduct.comm ℂ V W).toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨extTensor X T (g.2, g.1) z, S.apply_mem_toSubmodule _ hz, comm_ext X T g z⟩

private theorem swapSub_swapSub {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (S : Subrepresentation (extTensor X T)) : swapSub T X (swapSub X T S) = S := by
  apply Subrepresentation.toSubmodule_injective
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨TensorProduct.comm ℂ V W z, ⟨z, hz, rfl⟩, by simp⟩

private noncomputable def swapIso {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W) :
    Subrepresentation (extTensor X T) ≃o Subrepresentation (extTensor T X) where
  toFun := swapSub X T
  invFun := swapSub T X
  left_inv := swapSub_swapSub X T
  right_inv := swapSub_swapSub T X
  map_rel_iff' := by
    intro S S'
    constructor
    · intro h z hz
      obtain ⟨y, hy, e⟩ := h (show TensorProduct.comm ℂ V W z ∈ (swapSub X T S).toSubmodule from
        ⟨z, hz, rfl⟩)
      have e' : y = z := (TensorProduct.comm ℂ V W).injective e
      exact e' ▸ hy
    · rintro h _ ⟨z, hz, rfl⟩
      exact ⟨z, h hz, rfl⟩

private theorem schur_ext {G Γ V B : Type} [Group G] [Group Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup B] [Module ℂ B] [Nontrivial B] (σ : Representation ℂ G V)
    (m : Representation ℂ Γ B) (hσ : Schur σ) (hm : Schur m) : Schur (extTensor σ m) := by
  intro T hT
  obtain ⟨b₀, hb₀⟩ := exists_ne (0 : B)
  obtain ⟨β, hβ⟩ : ∃ β : Module.Dual ℂ B, β b₀ = 1 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ B, φ b₀ ≠ 0 := by
      by_contra! h
      exact hb₀ ((Module.forall_dual_apply_eq_zero_iff ℂ b₀).1 h)
    exact ⟨(φ b₀)⁻¹ • φ, by simp [hφ]⟩
  let L : Module.Dual ℂ V → (V ⊗[ℂ] B →ₗ[ℂ] B) := fun φ =>
    (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B φ
  let R : V ⊗[ℂ] B →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V β
  have hLt : ∀ φ x y, L φ (x ⊗ₜ y) = φ x • y := fun φ x y => by simp [L]
  have hRt : ∀ x y, R (x ⊗ₜ y) = β y • x := fun x y => by simp [R]
  have hL : ∀ φ c z, L φ (extTensor σ m (1, c) z) = m c (L φ z) := by
    intro φ c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hLt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hR : ∀ g z, R (extTensor σ m (g, 1) z) = σ g (R z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hRt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hLR : ∀ (φ : Module.Dual ℂ V) z, φ (R z) = β (L φ z) := by
    intro φ z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hLt, hRt, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let S : V →ₗ[ℂ] V := R ∘ₗ T ∘ₗ (TensorProduct.mk ℂ V B).flip b₀
  have hS : ∀ v, S v = R (T (v ⊗ₜ b₀)) := fun v => rfl
  have hpure : ∀ v b, T (v ⊗ₜ b) = S v ⊗ₜ b := by
    intro v b
    rw [← sub_eq_zero]
    apply tens_sep
    intro φ
    obtain ⟨c, hc⟩ := hm (L φ ∘ₗ T ∘ₗ TensorProduct.mk ℂ V B v) (by
      intro c y
      have h1 : v ⊗ₜ[ℂ] m c y = extTensor σ m (1, c) (v ⊗ₜ y) := by simp
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
      rw [h1, hT, hL])
    have hc' : ∀ y, L φ (T (v ⊗ₜ y)) = c • y := hc
    have hφS : φ (S v) = c := by
      rw [hS, hLR, hc', map_smul, hβ, smul_eq_mul, mul_one]
    change L φ (T (v ⊗ₜ b) - S v ⊗ₜ b) = 0
    rw [map_sub, hc', hLt, hφS, sub_self]
  obtain ⟨c, hc⟩ := hσ S (by
    intro g v
    have h1 : σ g v ⊗ₜ[ℂ] b₀ = extTensor σ m (g, 1) (v ⊗ₜ b₀) := by simp
    rw [hS, h1, hT, hR, ← hS])
  refine ⟨c, fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [hpure, hc, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensSimple :
    ∀ {G : Type} [Group G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {B : Type} [AddCommGroup B] [Module ℂ B] (σ : Representation ℂ G V) (m : Representation ℂ Γ B), σ.IsIrreducible → Schur σ → m.IsIrreducible →
      (extTensor σ m).IsIrreducible ∧ (Schur m → Schur (extTensor σ m)) := by
  intro G _ Γ _ V _ _ B _ _ σ m hσ hs hm
  haveI : Nontrivial B := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hm
  have hsc : ∀ A : Module.End ℂ V, (∀ g, A * σ g = σ g * A) → ∃ c : ℂ, A = c • 1 := by
    intro A hA
    obtain ⟨c, hc⟩ := hs A fun g v => congrArg (fun F : Module.End ℂ V => F v) (hA g)
    exact ⟨c, LinearMap.ext fun v => by simpa using hc v⟩
  refine ⟨?_, schur_ext σ m hs⟩
  have h1 : IsSimpleOrder (Subrepresentation (extTensor m σ)) :=
    (GlobalTheory.ExtTensorSub.orderIso m σ hσ hsc).isSimpleOrder_iff.1 hm
  exact (swapIso σ m).isSimpleOrder_iff.2 h1
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.schurSm :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (w : Pl K) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Gw n w) V), GlobalTheory.PRep.IsSmooth ρ → ρ.IsIrreducible → Schur ρ := by
  intro K _ _ n w V _ _ ρ hs hi T hT
  haveI := hi
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → w.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (Gw n w) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have hsm : GroundTheory.Automorphic.IsSmooth ρ := fun v => hs v
  let φ : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := T, isIntertwining' := fun g => LinearMap.ext fun v => hT g v }
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ
  exact ⟨c, fun v => (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm⟩
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem coef_mem {A B ι : Type} (X : Submodule ℂ (A → ℂ)) (s : Finset ι) (φ : ι → A → ℂ) (ψ : ι → B → ℂ)
    (hψ : LinearIndependent ℂ ψ) (h : ∀ b, (fun a => ∑ i ∈ s, φ i a * ψ i b) ∈ X) : ∀ i ∈ s, φ i ∈ X := by
  intro i hi
  by_contra hn
  obtain ⟨f, hf, hX⟩ := Submodule.exists_le_ker_of_notMem hn
  have h0 : ∑ j ∈ s, f (φ j) • ψ j = 0 := by
    funext b
    have h1 : f (fun a => ∑ i ∈ s, φ i a * ψ i b) = 0 := hX (h b)
    have h2 : (fun a => ∑ i ∈ s, φ i a * ψ i b) = ∑ i ∈ s, ψ i b • φ i := by
      funext a
      simp [Finset.sum_apply, mul_comm]

    rw [h2, map_sum] at h1
    simpa [Finset.sum_apply, mul_comm] using h1
  exact hf (linearIndependent_iff'.1 hψ s _ h0 i hi)

private noncomputable def prodMap {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    X₁ ⊗[ℂ] X₂ →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun φ ψ x => φ.1 x.1 * ψ.1 x.2)
    (fun _ _ _ => by funext x; simp [add_mul]) (fun _ _ _ => by funext x; simp [mul_assoc])
    (fun _ _ _ => by funext x; simp [mul_add]) (fun _ _ _ => by funext x; simp [mul_left_comm]))

private theorem prodMap_tmul {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) (φ : X₁) (ψ : X₂) :
    prodMap X₁ X₂ (φ ⊗ₜ ψ) = fun x => φ.1 x.1 * ψ.1 x.2 := by
  simp only [prodMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]

private theorem prodMap_inj {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    Function.Injective (prodMap X₁ X₂) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  let β := Module.Basis.ofVectorSpace ℂ X₂
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right β t
  have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
    β.linearIndependent.map' X₂.subtype (Submodule.ker_subtype _)
  have hc := coef_mem (⊥ : Submodule ℂ (A → ℂ)) c.support (fun i => (c i).1) (fun i => (β i).1) hβ (by
    intro b
    rw [Submodule.mem_bot]
    funext a
    have := congrFun ht (a, b)

    simpa [Finsupp.sum, map_sum, prodMap_tmul, Finset.sum_apply] using this)
  refine Finset.sum_eq_zero fun i hi => ?_
  have : c i = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 (hc i hi))
  simp [this]

private theorem prodMap_range {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    LinearMap.range (prodMap X₁ X₂) = tensFn X₁ X₂ := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul φ ψ => exact Submodule.subset_span ⟨φ.1, φ.2, ψ.1, ψ.2, prodMap_tmul X₁ X₂ φ ψ⟩
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩
    exact ⟨⟨φ, hφ⟩ ⊗ₜ ⟨ψ, hψ⟩, prodMap_tmul X₁ X₂ _ _⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensLaws :
    ∀ {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)), (∃ e : X₁ ⊗[ℂ] X₂ ≃ₗ[ℂ] tensFn X₁ X₂, ∀ φ ψ x, (e (φ ⊗ₜ ψ)).1 x = φ.1 x.1 * ψ.1 x.2) ∧
      ∀ (F : A × B → ℂ) (d : ℕ) (φ : Fin d → A → ℂ) (ψ : Fin d → B → ℂ), (∀ x, F x = ∑ i, φ i x.1 * ψ i x.2) →
        (∀ b, (fun a => F (a, b)) ∈ X₁) → (∀ a, (fun b => F (a, b)) ∈ X₂) → F ∈ tensFn X₁ X₂ := by
  intro A B X₁ X₂
  refine ⟨⟨(LinearEquiv.ofInjective _ (prodMap_inj X₁ X₂)).trans (LinearEquiv.ofEq _ _ (prodMap_range X₁ X₂)), ?_⟩, ?_⟩
  · intro φ ψ x
    exact congrFun (prodMap_tmul X₁ X₂ φ ψ) x
  · intro F d φ ψ hF h₁ h₂
    let W : Submodule ℂ (B → ℂ) := X₂ ⊓ Submodule.span ℂ (Set.range ψ)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
    have hW : ∀ a, (fun b => F (a, b)) ∈ W := by
      intro a
      refine ⟨h₂ a, ?_⟩
      have : (fun b => F (a, b)) = ∑ i, φ i a • ψ i := by
        funext b
        simp [hF, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let β := Module.finBasis ℂ W
    have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
      β.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
    have hrep : ∀ a b, F (a, b) = ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b := by
      intro a b
      have := congrFun (congrArg Subtype.val (β.sum_repr ⟨_, hW a⟩)) b
      rw [Submodule.coe_sum, Finset.sum_apply] at this
      exact this.symm
    have hc := coef_mem X₁ Finset.univ (fun i a => β.repr ⟨_, hW a⟩ i) (fun i => (β i).1) hβ (by
      intro b
      have : (fun a => ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b) = fun a => F (a, b) := by
        funext a
        exact (hrep a b).symm
      rw [this]
      exact h₁ b)
    have : F = ∑ i, fun x : A × B => β.repr ⟨_, hW x.1⟩ i * (β i).1 x.2 := by
      funext x
      rw [Finset.sum_apply]
      exact hrep x.1 x.2
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨_, hc i (Finset.mem_univ i), _, (β i).2.1, rfl⟩
end

section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private lemma map_zero_eq_one_of_additive_to_group {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ Γ V)
    (Z : Submodule ℂ V) (hZ : ∀ z ∈ Z, ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z) (w : V)
    (hw : w ∈ Submodule.span ℂ {x | ∃ u : Γ, ∃ z ∈ Z, x = σ u z - z}) (hfix : ∀ u, σ u w = w) : w = 0 := by
  have key : ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ (N' : Subgroup Γ) [Fintype (Γ ⧸ N')], N' ≤ N → N'.Normal →
      ∑ c : Γ ⧸ N', σ c.out w = 0 := by
    clear hfix
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, z, hz, rfl⟩ := hx
      obtain ⟨N, hN, hNz⟩ := hZ z hz
      refine ⟨N, hN, fun N' _ hle hn => ?_⟩
      simp only [map_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      refine Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) _ _ fun c => ?_
      obtain ⟨n, hn'⟩ := QuotientGroup.mk_out_eq_mul N' (c.out * u)
      have h1 : (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) c = QuotientGroup.mk (c.out * u) := by
        simp
      rw [h1, hn', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hNz n (hle n.2)]
    | zero => exact ⟨⊤, inferInstance, fun N' _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      obtain ⟨N₂, h₂, k₂⟩ := hy
      refine ⟨N₁ ⊓ N₂, inferInstance, fun N' _ hle hn => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [k₁ N' (hle.trans inf_le_left) hn, k₂ N' (hle.trans inf_le_right) hn, add_zero]
    | smul a x _ hx =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      refine ⟨N₁, h₁, fun N' _ hle hn => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, k₁ N' hle hn, smul_zero]
  obtain ⟨N, hN, k⟩ := key
  letI : Fintype (Γ ⧸ N.normalCore) := Fintype.ofFinite _
  have h := k N.normalCore N.normalCore_le inferInstance
  simp only [hfix, Finset.sum_const, Finset.card_univ] at h
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast Fintype.card_ne_zero)

private lemma finite_translates_double_coset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : CO U) (g : G) :
    {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}.Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have := (hU.1.image hc).finite_of_discrete
  refine this.subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.heckeSimple :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Z : Submodule ℂ V) (U : Subgroup G), CO U → SimpleIn ρ Z → (∀ v ∈ Z, IsOpen {g | ρ g v = v}) →
      ∀ Q ≤ Z, (∀ v ∈ Q, ∀ u ∈ U, ρ u v = v) → (∀ g, ∀ v ∈ Q, hopR ρ U g v ∈ Q) → Q = ⊥ ∨ ∀ v ∈ Z, (∀ u ∈ U, ρ u v = v) → v ∈ Q := by
  intro G _ _ _ V _ _ ρ Z U hU hS hsm Q hQZ hQfix hQhop
  by_cases hQ : Q = ⊥
  · exact Or.inl hQ
  right
  let σ : Representation ℂ U V := ρ.comp U.subtype
  have hσ : ∀ (u : U) (x : V), σ u x = ρ u x := fun _ _ => rfl
  set W : Submodule ℂ V := Submodule.span ℂ {x | ∃ u : U, ∃ z ∈ Z, x = σ u z - z} with hW
  have hZN : ∀ z ∈ Z, ∃ N : Subgroup U, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z := by
    intro z hz
    let N : Subgroup U :=
      { carrier := {n | σ n z = z}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.1
    have ho : IsOpen (N : Set U) := (hsm z hz).preimage continuous_subtype_val
    haveI := N.quotient_finite_of_isOpen ho
    exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun n hn => hn⟩
  have htr : ∀ g, ∀ q ∈ Q, ρ g q ∈ Q ⊔ W := by
    intro g q hq
    have hfin := finite_translates_double_coset U hU g
    have h1 := hQhop g q hq
    unfold hopR at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have h2 : ∑ c ∈ hfin.toFinset, (ρ c.out q - ρ g q) ∈ W := by
      refine W.sum_mem fun c hc => ?_
      obtain ⟨u, hu, rfl⟩ := hfin.mem_toFinset.mp hc
      obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul U (u * g)
      refine Submodule.subset_span ⟨⟨u, hu⟩, ρ g q, hS.1 g q (hQZ hq), ?_⟩
      rw [hn, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hQfix q hq n n.2, hσ]
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    have h3 := (Q ⊔ W).sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
    rw [sub_sub_cancel] at h3
    have hne : ((hfin.toFinset.card : ℕ) : ℂ) ≠ 0 := by
      have : hfin.toFinset.Nonempty := ⟨QuotientGroup.mk (1 * g), hfin.mem_toFinset.mpr ⟨1, U.one_mem, rfl⟩⟩
      exact_mod_cast this.card_ne_zero
    exact ((Q ⊔ W).smul_mem_iff hne).mp h3
  set T : Submodule ℂ V := Submodule.span ℂ {x | ∃ g : G, ∃ q ∈ Q, x = ρ g q} with hT
  have hTZ : T ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact hS.1 g q (hQZ hq)
  have hTst : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    have : T.map (ρ g) ≤ T := by
      rw [hT, Submodule.map_span_le]
      rintro x ⟨g', q, hq, rfl⟩
      exact Submodule.subset_span ⟨g * g', q, hq, by rw [map_mul, Module.End.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  have hQT : Q ≤ T := fun q hq => Submodule.subset_span ⟨1, q, hq, by simp⟩
  have hTeq : T = Z := (hS.2 T hTZ hTst).resolve_left fun h => hQ (le_bot_iff.mp (h ▸ hQT))
  have hTle : T ≤ Q ⊔ W := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact htr g q hq
  intro v hv hvfix
  obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.mp (hTle (hTeq ▸ hv))
  have hw0 : w = 0 := by
    refine map_zero_eq_one_of_additive_to_group σ Z hZN w hw fun u => ?_
    have := hvfix u u.2
    rw [map_add (f := _), hQfix q hq u u.2] at this
    exact add_left_cancel this
  simpa [hw0] using hq
end
