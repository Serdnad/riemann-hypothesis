module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GradientAtPoint

variable {σ : Type*} (w : σ → ℂ)

def grad : MvPolynomial σ ℂ →ₗ[ℂ] (σ → ℂ) :=
  LinearMap.pi fun i => (aeval w).toLinearMap ∘ₗ (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap

theorem grad_apply (p : MvPolynomial σ ℂ) (i : σ) : grad w p i = eval w (pderiv i p) := by
  simp [grad]

theorem grad_mul (a b : MvPolynomial σ ℂ) :
    grad w (a * b) = eval w a • grad w b + eval w b • grad w a := by
  ext i
  simp only [grad_apply, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, Pi.add_apply, Pi.smul_apply]

theorem grad_X_sub_C [DecidableEq σ] (j : σ) : grad w (X j - C (w j)) = Pi.single j 1 := by
  ext i
  rw [grad_apply, map_sub, pderiv_C, sub_zero, pderiv_X]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem grad_mul_of_eval_eq_zero (r p : MvPolynomial σ ℂ) (hp : eval w p = 0) :
    grad w (r * p) = eval w r • grad w p := by
  rw [grad_mul, hp, zero_smul, add_zero]

def linPart [Fintype σ] (c : σ → ℂ) : MvPolynomial σ ℂ :=
  ∑ i, C (c i) * (X i - C (w i))

theorem sub_C_eval_mem_span (p : MvPolynomial σ ℂ) :
    p - C (eval w p) ∈ Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), show p + q - (C (eval w p) + C (eval w q)) = (p - C (eval w p)) + (q - C (eval w q)) by
      ring]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, eval_X, map_mul,
      show p * X i - C (eval w p) * C (w i) = (p - C (eval w p)) * X i + C (eval w p) * (X i - C (w i)) by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem ker_eval_eq_span :
    RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) =
      Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  apply le_antisymm
  · intro p hp
    have h := sub_C_eval_mem_span w p
    rwa [RingHom.mem_ker.1 hp, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]

theorem grad_eq_zero_of_mem_sq {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2) : grad w p = 0 := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [grad_mul, RingHom.mem_ker.1 ha, RingHom.mem_ker.1 hb, zero_smul, zero_smul, add_zero]
  · rw [map_add (f := _), hx, hy, add_zero]

theorem sub_linPart_mem_sq [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) :
    p - linPart w (grad w p) ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  classical
  rw [ker_eval_eq_span] at hp
  obtain ⟨a, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hp
  have hg : grad w (∑ i, a i * (X i - C (w i))) = fun i => eval w (a i) := by

    rw [map_sum]
    simp_rw [grad_mul, grad_X_sub_C, map_sub, eval_X, eval_C, sub_self, zero_smul, add_zero]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hg, linPart, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_mul, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]

theorem mem_sq_of_grad_eq_zero [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) (hg : grad w p = 0) :
    p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  have h := sub_linPart_mem_sq w hp
  rwa [hg, linPart, Finset.sum_eq_zero (fun i _ => by simp), sub_zero] at h

end GradientAtPoint

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimitiveFormRemainder.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (N : ℕ) (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (n : σ → ℕ)
    (c : (i : σ) → Fin (n i) → (Fin d → ℂ) → ℂ) (f : (σ → ℂ) → ℂ),
    AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) → (∀ i j, AnalyticAt ℂ (c i j) (A w)) →
    (∀ i (T : ℂ), T ^ n i + ∑ j, c i j (A w) * T ^ (j : ℕ) = (T - w i) ^ n i) →
    AnalyticAt ℂ f w →
    ∃ (M : ℕ) (R : Polynomial ((Fin d → ℂ) → ℂ)), (∀ k, AnalyticAt ℂ (R.coeff k) (A w)) ∧
      ∀ᶠ z in 𝓝 w, (∀ i, z i ^ n i + ∑ j, c i j (A z) * z i ^ (j : ℕ) = 0) →
        (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
        δ (A z) ^ M * f z = R.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsAnalyticNear {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  ∃ (N : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
    (∀ i, AnalyticOnNhd ℂ (f i) N) ∧ X ∩ N = {z | z ∈ N ∧ ∀ i, f i z = 0}

def GermIrreducibleAt {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  w ∈ X ∧ ∀ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∨ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsGenericCountCover {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (N : ℕ) : Prop :=
  (∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) ∧
  ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
    (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
    ∀ y ∈ U, g y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N ∧
      ∀ x ∈ Y, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧ Y ∩ V = h '' O

noncomputable def fibreDiscr {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (l : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (y : Fin d → ℂ) : ℂ :=
  if h : {x | x ∈ Y ∧ A x = y}.encard = N then
    ∏ p ∈ (Set.finite_of_encard_eq_coe h).toFinset.offDiag, (l p.1 - l p.2)
  else 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsLocalParametrisation {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ) : Prop :=
  IsOpen B ∧ w ∈ X ∩ B ∧ IsOpen D ∧ IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
    (∀ x ∈ X ∩ B, A x = A w → x = w) ∧
    AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
    (∀ y ∈ D, δ y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = N) ∧
    (∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O) ∧
    X ∩ B ⊆ closure {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsRegularPointOf {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (x : σ → ℂ) : Prop :=
  x ∈ Y ∧ ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
    (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O

def regLocus {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) : Set (σ → ℂ) :=
  {x | IsRegularPointOf Y x}

theorem regLocus_subset {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) : regLocus Y ⊆ Y :=
  fun _ hx => hx.1

theorem isRegularPointOf_regLocus {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {x : σ → ℂ}
    (hx : x ∈ regLocus Y) : IsRegularPointOf (regLocus Y) x := by
  have hx' : IsRegularPointOf Y x := hx
  obtain ⟨hxY, d, A, O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hx'
  refine ⟨hx, d, A, O, V, g, hO, hV, hxV, hg, hAg, ?_⟩
  rw [← hYV]
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨regLocus_subset Y hz, hzV⟩
  · rintro ⟨hzY, hzV⟩
    exact ⟨⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩, hzV⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsFiniteModuloOver {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) {k : ℕ}
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) : Prop :=
  ∃ (n : ℕ) (e : Fin n → (σ → ℂ) → ℂ), (∀ m, AnalyticAt ℂ (e m) x) ∧
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (b : Fin n → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ m, AnalyticAt ℂ (b m) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z = ∑ m, b m (L z) * e m z + ∑ i, h i z * f i z

def FiniteModuloIntegral.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] (x : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ)
    (L : (σ → ℂ) →L[ℂ] (τ → ℂ)),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ j, AnalyticAt ℂ (a j) (L x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z ^ N + ∑ j, a j (L z) * g z ^ (j : ℕ) = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsolatedFibreLocalUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B, (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ B ∩ W, A x = A w → x = w) →
    ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), M ∈ 𝓝 w ∧ AnalyticAt ℂ g (A w) ∧
      (¬ ∀ᶠ y in 𝓝 (A w), g y = 0) ∧
      ∀ x ∈ X ∩ B ∩ M, g (A x) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionBranchLocus.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → IsPreconnected D → D.Nonempty → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∃ δ : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
      ∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → IsPreconnected D → D.Nonempty → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
      AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = N) ∧
      (∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O) ∧
      X ∩ B ⊆ closure {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionLocalCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ) (n : ℕ),
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
      (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
      (∀ y ∈ U, {x | x ∈ X ∩ B ∧ A x = y}.encard ≤ n) ∧
      ∀ y ∈ U, g y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = n ∧
        ∀ x ∈ X ∩ B, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionLocalUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
      (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
      ∀ y ∈ U, g y ≠ 0 →
        ∀ x ∈ X ∩ B, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
