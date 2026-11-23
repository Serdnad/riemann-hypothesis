module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportConvolutionTriple
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle018
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Tactic.Continuity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Mathlib.GroupTheory.Index
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply

@[expose] public section

section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem commutant_cyclic_eq_zero : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (v : Fin m → ℂ),
    IsUnit g.det → Function.Injective d → (∀ i, (g⁻¹ *ᵥ v) i ≠ 0) →
    ∀ A : Matrix (Fin m) (Fin m) ℂ, A * (g * diagonal d * g⁻¹) = (g * diagonal d * g⁻¹) * A →
      A *ᵥ v = 0 → A = 0 := by
  intro m g d v hg hd hv A hc hAv
  have h1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have h2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  obtain ⟨M, hM⟩ : ∃ M, M = g⁻¹ * A * g := ⟨_, rfl⟩
  have hcomm : M * diagonal d = diagonal d * M := by
    calc M * diagonal d = g⁻¹ * (A * (g * diagonal d * g⁻¹)) * g := by
          rw [hM]
          simp only [Matrix.mul_assoc]
          rw [h1, Matrix.mul_one]
      _ = g⁻¹ * ((g * diagonal d * g⁻¹) * A) * g := by rw [hc]
      _ = diagonal d * M := by
          rw [hM]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc g⁻¹ g, h1, Matrix.one_mul]
  have hdiag : ∀ i k, i ≠ k → M i k = 0 := by
    intro i k hik
    have h := congrFun (congrFun hcomm i) k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h3 : M i k * (d k - d i) = 0 := by rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exact absurd (hd (sub_eq_zero.mp h4)).symm hik
  have hMg : M * g⁻¹ = g⁻¹ * A := by
    rw [hM, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hMv : M *ᵥ (g⁻¹ *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hMg, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero]
  have hM0 : M = 0 := by
    ext i k
    by_cases hik : i = k
    · subst hik
      have h := congrFun hMv i
      have h5 : M i i * (g⁻¹ *ᵥ v) i = 0 := by
        have h6 : (M *ᵥ (g⁻¹ *ᵥ v)) i = M i i * (g⁻¹ *ᵥ v) i := by
          rw [Matrix.mulVec, dotProduct]
          exact Finset.sum_eq_single i (fun j _ hj => by rw [hdiag i j (Ne.symm hj), zero_mul])
            (fun h => absurd (Finset.mem_univ i) h)
        rw [← h6, h]; rfl
      simpa using (mul_eq_zero.mp h5).resolve_right (hv i)
    · simpa using hdiag i k hik
  calc A = g * (g⁻¹ * A * g) * g⁻¹ := by
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = 0 := by rw [← hM, hM0, Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.CompanionTheory.RgHeFrame
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem trace_diagonal_block_conjugate (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hg : IsUnit g.det)
    (hX : X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)))
    (hb : ∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g))
      = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) with hB
  have h1 : g * D * g⁻¹ = X := by
    rw [← hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.mul_one]
  have h2 : trace (D * (g⁻¹ * B * g)) = trace (X * B) := by
    rw [← h1]
    have : D * (g⁻¹ * B * g) = (D * g⁻¹ * B) * g := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h2]
  have h3 : trace (X * B) = ∑ u, ∑ w, X (e u) (e w) *
      (Matrix.fromBlocks Y 0 0 0 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [hB, Matrix.reindex_apply]
  rw [h3]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, hb]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

end GlobalTheory.CompanionTheory.RgHeFrame
end

section

open Matrix

theorem _root_.GlobalTheory.T.parabolic_stabilizer_block_unit : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J → g * C = C * h → gᴴ * C = C * hᴴ → IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧ (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | exact GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | (intros; apply GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.unitary_lift_commuting_involution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | exact GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | (intros; apply GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hecke_sum_invariant : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite → (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) → ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  first | exact @GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | exact GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed | (intros; apply GlobalTheory.CompanionTheory.Hecke.heckeSum_fixed <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_support_convolution_triple : ∀ (G₁ G₂ V : Type) [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ f₁' f₁'' : G₁ → ℂ) (f₂ f₂' f₂'' : G₂ → ℂ), (∀ f ∈ ({f₁, f₁', f₁''} : Set (G₁ → ℂ)), (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite ∧ ∀ k ∈ K₁, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ f ∈ ({f₂, f₂', f₂''} : Set (G₂ → ℂ)), (Function.support fun q : G₂ ⧸ K₂ => f q.out).Finite ∧ ∀ k ∈ K₂, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ v : V, (∀ k ∈ K₁, ρ (k, 1) v = v) → ∑ᶠ q : G₁ ⧸ K₁, f₁'' q.out • ρ (q.out, 1) v = ∑ᶠ q : G₁ ⧸ K₁, f₁ q.out • ρ (q.out, 1) (∑ᶠ q' : G₁ ⧸ K₁, f₁' q'.out • ρ (q'.out, 1) v)) → (∀ v : V, (∀ k ∈ K₂, ρ (1, k) v = v) → ∑ᶠ q : G₂ ⧸ K₂, f₂'' q.out • ρ (1, q.out) v = ∑ᶠ q : G₂ ⧸ K₂, f₂ q.out • ρ (1, q.out) (∑ᶠ q' : G₂ ⧸ K₂, f₂' q'.out • ρ (1, q'.out) v)) → ∀ v : V, (∀ k ∈ K₁.prod K₂, ρ k v = v) → ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁'' q.out.1 * f₂'' q.out.2) • ρ q.out v = ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁ q.out.1 * f₂ q.out.2) • ρ q.out (∑ᶠ q' : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁' q'.out.1 * f₂' q'.out.2) • ρ q'.out v) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul | exact GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul | (intros; apply GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul <;> assumption)
end

section


theorem _root_.GlobalTheory.T.invariant_functional_open_stabilizer : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → IsOpen {g : G | l ∘ₗ ρ g = l} := by
  first | exact @GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | exact GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | (intros; apply GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.EvalTensor

variable {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]

theorem eq_zero_of_sum_apply_eq_zero (σ : Representation ℂ G S) (π : Representation ℂ G V)
    (hirr : σ.IsIrreducible)
    (hschur : ∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id)
    {ι : Type} (b : ι → (S →ₗ[ℂ] V)) (hli : LinearIndependent ℂ b)
    (hb : ∀ i g s, b i (σ g s) = π g (b i s)) (J : Finset ι) :
    ∀ t : ι → S, ∑ j ∈ J, b j (t j) = 0 → ∀ j ∈ J, t j = 0 := by
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hirr
  induction J using Finset.induction_on with
  | empty => intro t _ j hj; simp at hj
  | insert a J ha ih =>
    intro t ht
    rw [Finset.sum_insert ha] at ht
    have hta : t a = 0 := by
      by_contra hne
      let Φ : (J → S) →ₗ[ℂ] V := ∑ j : J, (b j.1).comp (LinearMap.proj j)
      have hΦ : ∀ f : J → S, Φ f = ∑ j : J, b j.1 (f j) := fun f => by
        simp [Φ, LinearMap.sum_apply]
      have hinj : Function.Injective Φ := by
        set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        intro f hf
        rw [hΦ] at hf
        funext j
        have h0 := ih (fun i => if h : i ∈ J then f ⟨i, h⟩ else 0) (by
          rw [← Finset.sum_coe_sort J]
          simpa using hf) j.1 j.2
        simpa using h0
      have hequi : ∀ (g : G) (f : J → S), Φ (fun j => σ g (f j)) = π g (Φ f) := fun g f => by

        rw [hΦ, hΦ, map_sum]
        exact Finset.sum_congr rfl fun j _ => hb j.1 g (f j)
      let W : Subrepresentation σ :=
        { toSubmodule := (LinearMap.range Φ).comap (b a)
          apply_mem_toSubmodule := by
            rintro g v ⟨f, hf⟩
            exact ⟨fun j => σ g (f j), by rw [hequi, hf, hb]⟩ }
      have hmem : t a ∈ W := by
        refine ⟨fun j => - t j.1, ?_⟩
        rw [hΦ]
        have h1 : ∑ j : J, b j.1 (- t j.1) = - ∑ j ∈ J, b j (t j) := by
          rw [← Finset.sum_coe_sort J, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => map_neg _ _
        rw [h1]
        exact (eq_neg_of_add_eq_zero_left ht).symm ▸ rfl
      have htop : W = ⊤ := by
        rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
        · exfalso
          apply hne
          rw [h] at hmem
          exact hmem
        · exact h
      have hall : ∀ s, b a s ∈ LinearMap.range Φ := fun s => by
        have : s ∈ W := by rw [htop]; trivial
        exact this
      let e := LinearEquiv.ofInjective Φ hinj
      let B : S →ₗ[ℂ] (J → S) := e.symm.toLinearMap ∘ₗ (b a).codRestrict (LinearMap.range Φ) hall
      have hB : ∀ s, Φ (B s) = b a s := fun s => by
        have h1 : ((e (B s) : LinearMap.range Φ) : V) = Φ (B s) := LinearEquiv.ofInjective_apply _ _
        rw [← h1]
        simp [B]
      have hBc : ∀ g s, B (σ g s) = fun j => σ g (B s j) := fun g s => by
        apply hinj
        rw [hB, hequi, hB, hb]
      have hsc : ∀ j : J, ∃ c : ℂ, (LinearMap.proj j) ∘ₗ B = c • (LinearMap.id : S →ₗ[ℂ] S) := fun j =>
        hschur _ fun g s => by
          simp only [LinearMap.comp_apply, LinearMap.proj_apply]
          rw [hBc]
      choose c hc using hsc
      have hsum : b a = ∑ j : J, c j • b j.1 := by
        ext s
        rw [← hB, hΦ, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : B s j = c j • s := by
          simpa using LinearMap.congr_fun (hc j) s
        rw [h1, map_smul, LinearMap.smul_apply]
      refine hli.notMem_span_image (s := (J : Set ι)) (x := a) (by simpa using ha) ?_
      rw [hsum]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.1, j.2, rfl⟩)
    have hrest : ∑ j ∈ J, b j (t j) = 0 := by
      simpa [hta] using ht
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hta
    · exact ih t hrest j hj

theorem lift_flip_subtype_injective : ∀ {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G S) (π : Representation ℂ G V), σ.IsIrreducible → (∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id) → ∀ M : Submodule ℂ (S →ₗ[ℂ] V), (∀ f ∈ M, ∀ g s, f (σ g s) = π g (f s)) → Function.Injective (TensorProduct.lift (LinearMap.flip (M.subtype)) : S ⊗[ℂ] M →ₗ[ℂ] V) := by
  intro G S V _ _ _ _ _ σ π hirr hschur M hM
  classical
  let β := Module.Basis.ofVectorSpace ℂ M
  have hli : LinearIndependent ℂ (fun i => ((β i : M) : S →ₗ[ℂ] V)) :=
    β.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  let E := TensorProduct.equivFinsuppOfBasisRight (M := S) β
  have hxs : x = (E x).sum fun i s => s ⊗ₜ[ℂ] β i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hsum : ∑ i ∈ (E x).support, ((β i : M) : S →ₗ[ℂ] V) (E x i) = 0 := by

    rw [hxs, Finsupp.sum, map_sum] at hx
    simpa using hx
  have h0 := eq_zero_of_sum_apply_eq_zero σ π hirr hschur _ hli
    (fun i g s => hM _ (β i).2 g s) (E x).support (fun i => E x i) hsum
  have hE : E x = 0 := by
    ext i
    by_cases hi : i ∈ (E x).support
    · simpa using h0 i hi
    · simpa using hi
  exact E.map_eq_zero_iff.1 hE

end GlobalTheory.CompanionTheory.EvalTensor
end

section


theorem _root_.GlobalTheory.T.monic_factor_coefficients_integral : ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic → (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) * Q.eval (algebraMap ℂ A (u + c₂)))) → ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  first | exact @GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | exact GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product | (intros; apply GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product <;> assumption)
end

section


theorem _root_.GlobalTheory.T.multiset_antitone_enumeration : ∀ {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop), (∀ a b, P a b → f a < f b) → ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧ ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  first | exact @GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | exact GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing | (intros; apply GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing <;> assumption)
end

section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.AltSpan

theorem alternatingMap_eq_zero_of_span :
    ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M]
      {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ →
      ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 := by
  intro P _ _ M _ _ β b hb m f hf
  classical
  have key : ∀ (S : Finset (Fin m)) (v : Fin m → P), (∀ i ∉ S, v i ∈ Set.range b) → f v = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro v hv
      choose I hI using fun i => hv i (by simp)
      have hvI : v = b ∘ I := funext fun i => (hI i).symm
      rw [hvI]
      exact hf I
    · intro j S _ ih v hv
      have hlin : f.toMultilinearMap.toLinearMap v j = 0 := by
        apply LinearMap.ext_on_range hb
        intro c
        simp only [MultilinearMap.toLinearMap_apply, LinearMap.zero_apply, AlternatingMap.coe_multilinearMap]
        apply ih
        intro i hi
        by_cases hij : i = j
        · rw [hij]
          simp
        · rw [Function.update_of_ne hij]
          exact hv i (by simp [hij, hi])
      have h1 := LinearMap.congr_fun hlin (v j)
      simpa [MultilinearMap.toLinearMap_apply] using h1
  ext v
  simpa using key Finset.univ v (by simp)

end GlobalTheory.CompanionTheory.AltSpan
end

section


theorem _root_.GlobalTheory.T.prod_rel_index_ne_zero : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂), I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | exact GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero <;> assumption)
end
