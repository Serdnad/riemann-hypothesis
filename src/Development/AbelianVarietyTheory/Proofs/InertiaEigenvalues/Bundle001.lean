module

import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

namespace GlobalTheory.CardFilterLt

theorem card_filter_val_lt : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h :=
  fun hh => Fin.card_filter_val_lt.trans (min_eq_right hh)

end GlobalTheory.CardFilterLt
end

section

noncomputable section

namespace GlobalTheory.StableLatCount

def adE (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) : (A₂ →ₗ[E] A₁) →ₗ[E] (A₂ →ₗ[E] A₁) :=
  LinearMap.llcomp E A₂ A₁ A₁ (LinearMap.mulLeft E g₁) - LinearMap.lcomp E A₁ (LinearMap.mulLeft E g₂)

def homLat (E : Type) [Field E] {O A₁ A₂ : Type} [CommRing O] [Algebra O E] [CommRing A₁] [CommRing A₂]
    [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) : Submodule O (A₂ →ₗ[E] A₁) where
  carrier := {ψ | ∀ x ∈ M₂, ψ x ∈ M₁}
  add_mem' := fun ha hb x hx => by simpa using M₁.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c ψ hψ x hx => by simpa using M₁.smul_mem c (hψ x hx)

theorem adE_apply (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) (ψ : A₂ →ₗ[E] A₁) (x : A₂) : adE E g₁ g₂ ψ x = g₁ * ψ x - ψ (g₂ * x) := rfl

end GlobalTheory.StableLatCount
end
end

section

open Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem rows_algebraMap_linearIndependent {L0 L : Type} [Field L0] [Field L] [Algebra L0 L]
    {m n : ℕ} (v : Fin m → Fin n → L0) (hv : LinearIndependent L0 v) :
    LinearIndependent L (fun a b => algebraMap L0 L (v a b)) := by
  have h1 : LinearIndependent L (fun a => (1 : L) ⊗ₜ[L0] v a) :=
    Module.Flat.linearIndependent_one_tmul hv
  have h2 := h1.map' (TensorProduct.piScalarRight L0 L L (Fin n)).toLinearMap (LinearEquiv.ker _)
  have he : (fun a b => algebraMap L0 L (v a b)) =
      (TensorProduct.piScalarRight L0 L L (Fin n)).toLinearMap ∘ fun a => (1 : L) ⊗ₜ[L0] v a := by
    funext a b
    simp [TensorProduct.piScalarRight_apply, Algebra.smul_def]
  rw [he]
  exact h2

theorem ksForm_tensor_linearIndependent : ∀ (Ks L0 L WL : Type) [Field Ks] [Field L0] [Field L] [Algebra Ks L0] [Algebra L0 L] [Algebra Ks L]
    [IsScalarTower Ks L0 L] [AddCommGroup WL] [Module L WL] [Module Ks WL] [IsScalarTower Ks L WL]
    (WK : Submodule Ks WL) (n : ℕ) (bs : Fin n → WL), (∀ a, bs a ∈ WK) → Submodule.span Ks (Set.range bs) = WK →
    LinearIndependent L bs → ∀ (ι : L0 ⊗[Ks] WK →ₗ[Ks] WL), (∀ (c : L0) (f : WK), ι (c ⊗ₜ[Ks] f) = algebraMap L0 L c • (f : WL)) →
    ∀ (m : ℕ) (x : Fin m → L0 ⊗[Ks] WK), LinearIndependent L0 x → LinearIndependent L (fun a => ι (x a)) := by
  intro Ks L0 L WL _ _ _ _ _ _ _ _ _ _ _ WK n bs hmem hspan hL ι hι m x hx
  subst hspan
  have hK : LinearIndependent Ks bs := hL.restrict_scalars' Ks
  let bK := Module.Basis.span hK
  let B0 := Algebra.TensorProduct.basis L0 bK
  let M : Fin m → Fin n → L0 := fun a => B0.equivFun (x a)
  have hMli : LinearIndependent L0 M := hx.map' B0.equivFun.toLinearMap B0.equivFun.ker
  have hML := rows_algebraMap_linearIndependent (L := L) M hMli
  have hιs : ∀ (c : L0) (y : L0 ⊗[Ks] (Submodule.span Ks (Set.range bs))),
      ι (c • y) = algebraMap L0 L c • ι y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul d f => rw [TensorProduct.smul_tmul', hι, hι, smul_eq_mul, map_mul, mul_smul]
    | add y z hy hz => rw [smul_add, map_add (f := _), map_add (f := _), hy, hz, smul_add]
  have hx_eq : ∀ a, ι (x a) = ∑ b, algebraMap L0 L (M a b) • bs b := by
    intro a
    conv_lhs => rw [← B0.sum_equivFun (x a)]

    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hιs, Algebra.TensorProduct.basis_apply, hι]
    simp [bK, Module.Basis.span_apply, M]
  rw [Fintype.linearIndependent_iff] at hL hML ⊢
  intro g hg
  apply hML g
  funext b
  simp_rw [hx_eq, Finset.smul_sum, smul_smul] at hg
  rw [Finset.sum_comm] at hg
  simp_rw [← Finset.sum_smul] at hg
  have := hL _ hg b
  simpa [Finset.sum_apply] using this

end GlobalTheory
end

section

namespace GlobalTheory

theorem linRelation_descend : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (ι : Type) [Fintype ι]
    (V : Set (ι → K)) (c : ι → Ω), c ≠ 0 → (∀ v ∈ V, ∑ s, c s * algebraMap K Ω (v s) = 0) →
    ∃ d : ι → K, d ≠ 0 ∧ ∀ v ∈ V, ∑ s, d s * v s = 0 := by
  intro K Ω _ _ _ ι _ V c hc hV
  obtain ⟨s0, hs0⟩ : ∃ s, c s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  let b := Module.Basis.ofVectorSpace K Ω
  obtain ⟨j, hj⟩ : ∃ j, b.repr (c s0) j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hs0
    have h0 : b.repr (c s0) = 0 := Finsupp.ext h
    exact b.repr.map_eq_zero_iff.mp h0
  refine ⟨fun s => b.repr (c s) j, fun h => hj (congrFun h s0), fun v hv => ?_⟩
  have h2 : ∑ s, v s • c s = 0 := by
    rw [← hV v hv]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have h3 := congrArg (fun x => b.repr x j) h2

  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
  map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory
end

section

namespace GlobalTheory

open Finset

theorem ringHom_evalVectors_span_eq_top {L Ω : Type} [Field L] [Field Ω]
    (S : Set (L →+* Ω)) [Fintype S] :
    Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  have hli : LinearIndependent Ω (fun h : S => ((h : L →+* Ω) : L → Ω)) := by
    have := (linearIndependent_monoidHom L Ω).comp
      (fun h : S => ((h : L →+* Ω) : L →* Ω)) (by
        intro x y hxy
        apply Subtype.ext
        apply RingHom.ext
        intro c
        exact DFunLike.congr_fun hxy c)
    exact this
  rw [Fintype.linearIndependent_iff] at hli
  apply hf0
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  have hc : ∀ h : S, f (fun j => if h = j then (1 : Ω) else 0) = 0 := by
    apply hli
    funext c
    have hmem : (fun h : S => (h : L →+* Ω) c) ∈
        Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) :=
      Submodule.subset_span ⟨c, rfl⟩
    have h0 : f (fun h : S => (h : L →+* Ω) c) = 0 := by
      have : f (fun h : S => (h : L →+* Ω) c) ∈ Submodule.map f
          (Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c)) :=
        Submodule.mem_map_of_mem hmem
      rw [hf] at this
      exact (Submodule.mem_bot Ω).mp this
    rw [LinearMap.pi_apply_eq_sum_univ f] at h0
    simpa [Finset.sum_apply, mul_comm] using h0
  simp [hc]

theorem speiser_descent_span :
    ∀ {G L Ω M : Type} [Group G] [Field L] [Field Ω] [Algebra L Ω] [AddCommGroup M] [Module Ω M]
      [Module L M] [IsScalarTower L Ω M] (b : G → Ω → Ω) (a : G → L →+* Ω) (σ : G → M →+ M)
      (W : Submodule L M), (∀ g h c, a (g * h) c = b g (a h c)) →
      (∀ c, a 1 c = algebraMap L Ω c) → (∀ m, σ 1 m = m) →
      (∀ g h m, σ (g * h) m = σ g (σ h m)) → (∀ g (c : L) m, σ g (c • m) = a g c • σ g m) →
      (Set.range a).Finite → (∀ g, ∀ m ∈ W, σ g m ∈ W) →
      (∀ g, (∀ c, a g c = algebraMap L Ω c) → ∀ m ∈ W, σ g m = m) →
      ∀ m ∈ W, m ∈ Submodule.span Ω {m | m ∈ W ∧ ∀ g, σ g m = m} := by
  intro G L Ω M _ _ _ _ _ _ _ _ b a σ W hb ha1 _hσ1 hσmul hσsmul hfin hstab hker m hm
  classical
  let S : Set (L →+* Ω) := Set.range a
  haveI : Fintype S := hfin.fintype
  have hrep : ∀ h : S, ∃ g, a g = h := fun h => h.2
  choose gs hgs using hrep
  have hleft : ∀ g x c, a x c = b g⁻¹ (a (g * x) c) := by
    intro g x c; rw [← hb, inv_mul_cancel_left]
  let δ : S → Ω := fun h => if (h : L →+* Ω) = a 1 then 1 else 0
  have hδ : δ ∈ Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) := by
    rw [ringHom_evalVectors_span_eq_top S]; trivial
  obtain ⟨β, hβ⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hδ
  have hβh : ∀ h : S, ∑ c ∈ β.support, β c * (h : L →+* Ω) c = δ h := by
    intro h
    have := congrFun hβ h
    simpa [Finsupp.sum, Finset.sum_apply] using this
  let t : L → M := fun c => ∑ h : S, σ (gs h) (c • m)
  have htW : ∀ c, t c ∈ W := fun c => W.sum_mem fun h _ => hstab _ _ (W.smul_mem c hm)
  have hperm : ∀ g : G, ∀ y ∈ W, σ g (∑ h : S, σ (gs h) y) = ∑ h : S, σ (gs h) y := by
    intro g y hy
    let π : S → S := fun h => ⟨a (g * gs h), Set.mem_range_self _⟩
    have hπ : Function.Injective π := by
      intro h1 h2 e
      have e' : a (g * gs h1) = a (g * gs h2) := congrArg Subtype.val e
      have : a (gs h1) = a (gs h2) := by
        ext c; rw [hleft g (gs h1) c, hleft g (gs h2) c, e']
      apply Subtype.ext
      rw [← hgs h1, ← hgs h2, this]
    have hbij : Function.Bijective π := Finite.injective_iff_bijective.1 hπ
    have hsw : ∀ h, σ (g * gs h) y = σ (gs (π h)) y := by
      intro h
      have hk : a (gs (π h)) = a (g * gs h) := hgs (π h)
      have hu : ∀ c, a ((gs (π h))⁻¹ * (g * gs h)) c = algebraMap L Ω c := by
        intro c
        rw [hb, ← hk, ← hb, inv_mul_cancel, ha1]
      calc σ (g * gs h) y = σ (gs (π h) * ((gs (π h))⁻¹ * (g * gs h))) y := by
            rw [mul_inv_cancel_left]
        _ = σ (gs (π h)) (σ ((gs (π h))⁻¹ * (g * gs h)) y) := hσmul _ _ _
        _ = σ (gs (π h)) y := by rw [hker _ hu y hy]

    rw [map_sum]
    simp_rw [← hσmul, hsw]
    exact Function.Bijective.sum_comp hbij (fun h => σ (gs h) y)
  have htinv : ∀ c g, σ g (t c) = t c := fun c g => hperm g _ (W.smul_mem c hm)
  have h1S : a 1 ∈ S := Set.mem_range_self 1
  have hrec : ∑ c ∈ β.support, β c • t c = m := by
    have e1 : ∑ c ∈ β.support, β c • t c = ∑ h : S, δ h • σ (gs h) m := by
      simp only [t, Finset.smul_sum, hσsmul, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Finset.sum_smul, hgs h, hβh h]
    rw [e1, Fintype.sum_eq_single ⟨a 1, h1S⟩]
    · have hg1 : ∀ c, a (gs ⟨a 1, h1S⟩) c = algebraMap L Ω c := by
        intro c; rw [hgs]; exact ha1 c
      simp only [δ, if_pos rfl, one_smul]
      exact hker _ hg1 m hm
    · intro h hne
      have : (h : L →+* Ω) ≠ a 1 := fun e => hne (Subtype.ext e)
      simp [δ, this]
  rw [← hrec]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨htW c, htinv c⟩)

end GlobalTheory
end

section

namespace GlobalTheory.InvariantBotOrTop

open Matrix

theorem invariant_all {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) (A : Matrix (Fin r) (Fin r) k) :
    ∀ x ∈ W, A.map (algebraMap k K) *ᵥ x ∈ W := by
  have hA : A ∈ Submodule.span k (Set.range M) := by
    rw [hM]
    exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    exact hW g
  | zero =>
    intro x _
    rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
    exact W.zero_mem
  | add A B _ _ hA hB =>
    intro x hx
    rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
    exact W.add_mem (hA x hx) (hB x hx)
  | smul c A _ hA =>
    intro x hx
    rw [Matrix.map_smul _ c (fun a => by rw [smul_eq_mul, map_mul, Algebra.smul_def])]
    first
      | rw [Matrix.smul_mulVec]
      | rw [Matrix.smul_mulVec_assoc]
    exact W.smul_of_tower_mem c (hA x hx)

theorem bot_or_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)

  have he : ∀ i, (Pi.single i (1 : K) : Fin r → K) ∈ W := by
    intro i
    have h1 := invariant_all M hM W hW (Matrix.single i j 1) x hxW
    have h2 : (Matrix.single i j (1 : k)).map (algebraMap k K) *ᵥ x = x j • Pi.single i 1 := by
      ext a
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      by_cases hai : a = i
      · subst hai
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb]) (by simp)]
        simp [Matrix.single_apply]
      · rw [Finset.sum_eq_zero (fun b _ => by simp [Matrix.single_apply, hai, Ne.symm hai])]
        simp [Pi.single_apply, hai]
    rw [h2] at h1
    have h3 := W.smul_mem (x j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h3
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K) := by
    ext a
    simp [Pi.single_apply]
  rw [hy]
  exact W.sum_mem fun i _ => W.smul_mem _ (he i)

theorem main : ∀ {Γ k K : Type} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] {r : ℕ} (M : Γ → Matrix (Fin r) (Fin r) k), Submodule.span k (Set.range M) = ⊤ → ∀ (W : Submodule K (Fin r → K)), (∀ (g : Γ), ∀ x ∈ W, Matrix.mulVec (Matrix.map (M g) (⇑(Algebra.algebraMap k K) : k → K)) x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro Γ k K _ _ _ r M hM W hW
  exact bot_or_top M hM W hW

end GlobalTheory.InvariantBotOrTop
end

section

open scoped TensorProduct

namespace GlobalTheory

private theorem tower_minimal_presentation (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (A : Type)
    [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] :
    ∃ (d : ℕ) (p : (Fin d → Λ) →ₗ[Λ] A), Function.Surjective p ∧
      ∀ x, p x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  classical
  let k := IsLocalRing.ResidueField Λ
  let b := Module.finBasis k (k ⊗[Λ] A)
  have hs : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k IsLocalRing.residue_surjective
  choose v hv using fun i => hs (b i)
  have hv' : ∀ i, (1 : k) ⊗ₜ[Λ] v i = b i := hv
  have hspan : Submodule.span Λ (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv'
  refine ⟨_, Fintype.linearCombination Λ v, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  · intro x hx i
    have h1 : ∑ j, algebraMap Λ k (x j) • b j = 0 := by
      have h2 := congrArg (TensorProduct.mk Λ k A 1) hx

      rw [Fintype.linearCombination_apply, map_sum, map_zero] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hv, algebraMap_smul]
    have h3 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 i
    exact (IsLocalRing.residue_eq_zero_iff _).1 h3

theorem exists_surjective_lift_of_ker_le_maximalIdeal_smul {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
    {A B : Type} [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] [AddCommGroup B] [Module Λ B]
    (t : A →ₗ[Λ] B) (ht : Function.Surjective t)
    (hk : LinearMap.ker t ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ A))
    {a : ℕ} (p : (Fin a → Λ) →ₗ[Λ] B) (hp : Function.Surjective p) :
    ∃ q : (Fin a → Λ) →ₗ[Λ] A, Function.Surjective q ∧ t ∘ₗ q = p := by
  obtain ⟨q, hq⟩ := Module.projective_lifting_property t p ht
  refine ⟨q, ?_, hq⟩
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal Λ)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) fun y _ => ?_
  obtain ⟨x, hx⟩ := hp (t y)
  have h1 : y - q x ∈ LinearMap.ker t := by
    rw [LinearMap.mem_ker, map_sub, ← hx, ← hq, LinearMap.comp_apply, sub_self]
  have h2 : y = q x + (y - q x) := by abel
  rw [h2]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self q x) (hk h1)

theorem exists_compatible_generators_tower :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (M : ℕ → Type) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)] [∀ n, Module.Finite Λ (M n)]
  (t : ∀ n, M (n + 1) →ₗ[Λ] M n), (∀ n, Function.Surjective (t n)) →
  (∀ n, LinearMap.ker (t n) ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ (M (n + 1)))) →
  ∃ (a : ℕ) (p : ∀ n, (Fin a → Λ) →ₗ[Λ] M n), (∀ n, Function.Surjective (p n)) ∧ (∀ n, (t n) ∘ₗ (p (n + 1)) = p n) ∧
    ∀ x, p 0 x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  intro Λ _ _ M _ _ _ t ht hk
  obtain ⟨a, p0, hp0, hmin⟩ := tower_minimal_presentation Λ (M 0)
  choose q hq hq' using fun (n : ℕ) (p : (Fin a → Λ) →ₗ[Λ] M n) (hp : Function.Surjective p) =>
    exists_surjective_lift_of_ker_le_maximalIdeal_smul (t n) (ht n) (hk n) p hp
  let P : ∀ n, {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p} := fun n =>
    Nat.rec (motive := fun n => {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p})
      ⟨p0, hp0⟩ (fun n p => ⟨q n p.1 p.2, hq n p.1 p.2⟩) n
  exact ⟨a, fun n => (P n).1, fun n => (P n).2, fun n => hq' n (P n).1 (P n).2, hmin⟩

end GlobalTheory
end
