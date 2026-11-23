module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aux {G H G' H' : Type} [Monoid G] [Monoid H] [Monoid G'] [Monoid H'] (E : G →* H) (i : G' → G) (i' : H' → H)
    (j : G' → H') (hj : ∀ k k', j (k * k') = j k * j k') (hi : ∀ k, E (i k) = i' (j k)) (V : Submodule ℂ (H' → ℂ))
    (hst : ∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) :
    (∀ f ∈ V.map (LinearMap.funLeft ℂ ℂ j), ∀ k', (fun k => f (k * k')) ∈ V.map (LinearMap.funLeft ℂ ℂ j)) ∧
    ∀ (f : G → ℂ) (ψ : H → ℂ) (g₀ : H), (∀ g, (fun k => ψ (g * i' k)) ∈ V) → (∀ m, f m = ψ (g₀ * E m)) →
      ∀ g, (fun k => f (g * i k)) ∈ V.map (LinearMap.funLeft ℂ ℂ j) := by
  constructor
  · rintro _ ⟨f, hf, rfl⟩ k'
    refine ⟨_, hst f hf (j k'), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply, hj]
  · intro f ψ g₀ hψ hf g
    refine ⟨_, hψ (g₀ * E g), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, hi, mul_assoc]

private theorem aux2 (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (k : archCompact K a) :
    embArch e k.1 ∈ archCompact K n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat K a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1] at h
  exact Subgroup.mem_comap.2 h

private theorem aux3 {G X : Type} (A : Submodule ℂ (G → ℂ)) (s : Set A) (p : X → G) (W : Submodule ℂ (X → ℂ))
    (h : ∀ f ∈ s, (fun k => f.1 (p k)) ∈ W) : ∀ f ∈ Submodule.span ℂ s, (fun k => f.1 (p k)) ∈ W := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    convert W.zero_mem using 1
  | add x y _ _ hx hy =>
    convert W.add_mem hx hy using 1
  | smul c x _ hx =>
    convert W.smul_mem c hx using 1

theorem UpperTheory.finiteDimensional_slSp_reduction :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), Types S → Types (slSp e Γ S) := by
  intro K _ _ a n e Γ S hS
  obtain ⟨V, hVf, hVst, hV⟩ := hS
  let j : archCompact K a → archCompact K n := fun k => ⟨embArch e k.1, aux2 K a n e k⟩
  have hj : ∀ k k', j (k * k') = j k * j k' := fun k k' => Subtype.ext (map_mul (embArch e) k.1 k'.1)
  have hi : ∀ k : archCompact K a, emb e (infEmb K a k.1) = infEmb K n (j k).1 :=
    fun k => (UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1 k.1
  have key := aux (G := AdelicGLn.AdelicGL K a) (H := AdelicGLn.AdelicGL K n) (emb e)
    (fun k : archCompact K a => infEmb K a k.1)
    (fun k : archCompact K n => infEmb K n k.1) j hj hi V hVst
  refine ⟨V.map (LinearMap.funLeft ℂ ℂ j), ?_, key.1, ?_⟩
  · exact Module.Finite.map V _
  · intro f hf g
    unfold slSp at hf
    refine aux3 (archSmooth K a) _ (fun k : archCompact K a => g * infEmb K a k.1)
      (V.map (LinearMap.funLeft ℂ ℂ j)) ?_ f hf
    rintro f' ⟨ψ, hψ, g₀, -, hf'⟩
    exact key.2 f'.1 ψ.1 g₀ (hV ψ hψ) hf' g
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.slSp_preserves_growth_and_level :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), (Growth S → Growth (slSp e Γ S)) ∧ (Level S → Level (slSp e Γ S)) := by
  intro K _ _ a n e Γ S
  constructor
  · intro hG φ hφ
    induction hφ using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hf
      obtain ⟨C, N, hC⟩ := hG ψ hψ
      have hC0 : 0 ≤ C := by
        have h1 := (norm_nonneg _).trans (hC 1)
        have hp : 0 < height (1 : AdelicGLn.AdelicGL K n) ^ N := pow_pos (height_pos _) N
        exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) hp
      have hc : 0 ≤ heightConst K n * height g :=
        mul_nonneg (zero_le_one.trans (one_le_heightConst (K := K) (n := n))) (height_pos g).le
      refine ⟨C * (heightConst K n * height g) ^ N, N, fun m => ?_⟩
      have hh : height (g * emb e m) ≤ heightConst K n * height g * height m :=
        (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le K a n e m) hc)
      calc ‖(f : AdelicGLn.AdelicGL K a → ℂ) m‖ = ‖(ψ : AdelicGLn.AdelicGL K n → ℂ) (g * emb e m)‖ := by rw [hfm]
        _ ≤ C * height (g * emb e m) ^ N := hC _
        _ ≤ C * (heightConst K n * height g * height m) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le hh N) hC0
        _ = C * (heightConst K n * height g) ^ N * height m ^ N := by rw [mul_pow]; ring
    | zero => simpa using (hasModerateGrowth_zero (K := K) (n := a))
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul c x _ hx => simpa using hx.smul c
  · rintro ⟨L, hL, hinv⟩
    let f : AdelicGLn.FiniteAdelicGL K a →* AdelicGLn.FiniteAdelicGL K n := emb e
    refine ⟨L.comap f, hL.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).2.2, fun φ hφ => ?_⟩
    induction hφ using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hh
      intro u hu m
      rw [hfm, hfm, map_mul, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).1 u, ← mul_assoc]
      exact hinv ψ hψ (f u) hu _
    | zero => intro u _ m; simp
    | add x y _ _ hx hy => intro u hu m; simp [hx u hu m, hy u hu m]
    | smul c x _ hx => intro u hu m; simp [hx u hu m]
end
