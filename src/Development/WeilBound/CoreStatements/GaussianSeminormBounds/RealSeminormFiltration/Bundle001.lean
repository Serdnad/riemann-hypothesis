module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

section

noncomputable section

open Complex Matrix Filter Topology

namespace PositivityTheory.RL.Up

theorem exp_mul_inj {z z' : ℂ} (h : ∀ t : ℝ, cexp (z * t) = cexp (z' * t)) : z = z' := by
  have d : ∀ z : ℂ, HasDerivAt (fun t : ℝ => cexp (z * t)) z 0 := fun z => by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul z).cexp
  have := d z
  simp only [h] at this
  exact this.unique (d z')

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

def expU (Z : 𝔸) : 𝔸ˣ :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  ⟨NormedSpace.exp Z, NormedSpace.exp (-Z),
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_right, add_neg_cancel, NormedSpace.exp_zero],
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]⟩

theorem expU_add (Z : 𝔸) (s t : ℝ) : expU ((s + t) • Z) = expU (s • Z) * expU (t • Z) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  refine Units.ext ?_
  show NormedSpace.exp _ = NormedSpace.exp _ * NormedSpace.exp _
  rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl Z).smul_left s).smul_right t)]

theorem expU_zero : expU (0 : 𝔸) = 1 := Units.ext NormedSpace.exp_zero

theorem continuous_expU (Z : 𝔸) : Continuous fun t : ℝ => expU (t • Z) :=
  Units.isOpenEmbedding_val.isInducing.continuous_iff.2
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z t).continuousAt)

end Banach

theorem eq_trace {β : Type} [Fintype β] [DecidableEq β] (ξ : Matrix β β ℂ →ₗ[ℂ] ℂ)
    (h : ∀ A B, ξ (A * B - B * A) = 0) : ∃ c : ℂ, ∀ A, ξ A = c * A.trace := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b⟩⟩
  · exact ⟨0, fun A => by rw [Subsingleton.elim A 0, map_zero, zero_mul]⟩
  refine ⟨ξ (single b b 1), fun A => ?_⟩
  have h1 : ∀ i j, i ≠ j → ξ (single i j 1) = 0 := fun i j hij => by
    have := h (single i i 1) (single i j 1)
    rwa [single_mul_single_same, single_mul_single_of_ne (h := hij.symm), one_mul, sub_zero] at this
  have h2 : ∀ i, ξ (single i i 1) = ξ (single b b 1) := fun i => by
    have := h (single i b 1) (single b i 1)
    rwa [single_mul_single_same, single_mul_single_same, one_mul, map_sub, sub_eq_zero] at this
  conv_lhs => rw [matrix_eq_sum_single A]

  simp only [map_sum]
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j, ξ (single i j (A i j)) = A i j * ξ (single i j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [e, h1 i j hj.symm, mul_zero]) (by simp), e, h2, mul_comm]
  rfl

theorem real_form_trace {β : Type} [Fintype β] [DecidableEq β] (τ : Matrix β β ℂ →ₗ[ℝ] Matrix β β ℂ)
    (hI : ∀ A, τ (I • A) = -(I • τ A)) (hτ : ∀ A, τ (τ A) = A) (ζ : Matrix β β ℂ →ₗ[ℝ] ℂ)
    (hb : ∀ X Y, τ X = X → τ Y = Y → τ (X * Y - Y * X) = X * Y - Y * X ∧ ζ (X * Y - Y * X) = 0) :
    ∃ c : ℂ, ∀ Z, τ Z = Z → ζ Z = c * Z.trace := by
  let P : Matrix β β ℂ → Matrix β β ℂ := fun A => (1 / 2 : ℝ) • (A + τ A)
  have hP : ∀ A, τ (P A) = P A := fun A => by simp only [P, map_smul, map_add (f := _), hτ, add_comm]
  let ξ0 : Matrix β β ℂ → ℂ := fun A => ζ (P A) - I * ζ (P (I • A))
  have add : ∀ A B, ξ0 (A + B) = ξ0 A + ξ0 B := fun A B => by
    simp only [ξ0, P, smul_add, map_add (f := _), map_smul]
    ring
  have rs : ∀ (r : ℝ) A, ξ0 (r • A) = r * ξ0 A := fun r A => by
    simp only [ξ0, P, smul_comm I r, smul_add, map_add (f := _), map_smul, real_smul]
    ring
  have is : ∀ A, ξ0 (I • A) = I * ξ0 A := fun A => by
    simp only [ξ0, P, smul_smul, I_mul_I, neg_smul, one_smul, smul_add, map_add (f := _), map_smul, map_neg, real_smul, smul_neg]
    linear_combination ((((1 / 2 : ℝ) : ℂ) * ζ (I • A) + ((1 / 2 : ℝ) : ℂ) * ζ (τ (I • A)))) * I_mul_I
  let ξ : Matrix β β ℂ →ₗ[ℂ] ℂ :=
    { toFun := ξ0
      map_add' := add
      map_smul' := fun c A => by
        have e : c • A = c.re • A + I • (c.im • A) := by
          ext i j
          simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, real_smul]
          linear_combination (-A i j) * re_add_im c
        rw [e, add, is, rs, rs, RingHom.id_apply, smul_eq_mul]
        linear_combination (ξ0 A) * re_add_im c }
  have fix : ∀ Z, τ Z = Z → ξ Z = ζ Z := fun Z hZ => by
    have e1 : P Z = Z := by
      simp only [P, hZ]
      module
    have e2 : P (I • Z) = 0 := by simp only [P, hI, hZ, add_neg_cancel, smul_zero]
    show ζ (P Z) - I * ζ (P (I • Z)) = _
    rw [e1, e2, map_zero, mul_zero, sub_zero]
  have dec : ∀ A, A = P A - I • P (I • A) := fun A => by
    simp only [P, hI]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul, real_smul]
    push_cast
    linear_combination ((A i j - τ A i j) / 2) * I_mul_I
  have br : ∀ X Y, τ X = X → τ Y = Y → ξ (X * Y - Y * X) = 0 := fun X Y hX hY => by
    rw [fix _ (hb X Y hX hY).1, (hb X Y hX hY).2]
  obtain ⟨c, hc⟩ := eq_trace ξ fun A B => by
    have h1 : ∀ X, τ X = X → ξ (X * B - B * X) = 0 := fun X hX => by
      have e : X * B - B * X = (X * P B - P B * X) - I • (X * P (I • B) - P (I • B) * X) := by
        conv_lhs => rw [dec B]
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        abel
      rw [e, map_sub, map_smul, br _ _ hX (hP _), br _ _ hX (hP _), smul_zero, sub_zero]
    have e : A * B - B * A = (P A * B - B * P A) - I • (P (I • A) * B - B * P (I • A)) := by
      conv_lhs => rw [dec A]
      simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, map_sub, map_smul, h1 _ (hP _), h1 _ (hP _), smul_zero, sub_zero]
  exact ⟨c, fun Z hZ => by rw [← fix Z hZ, hc]⟩

end PositivityTheory.RL.Up

end
end

section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

section SlopeTestRemainingChoices

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] in
theorem updInv (s : J) : Function.Involutive
    (fun x : (J → I) × I => (Function.update x.1 s x.2, x.1 s)) := by
  rintro ⟨w, i⟩
  simp [Function.update_idem, Function.update_self, Function.update_eq_self]

theorem sum_upd {β : Type} [AddCommMonoid β] (s : J) (g : (J → I) → I → β) :
    ∑ w, ∑ j, g w j = ∑ w, ∑ j, g (Function.update w s j) (w s) := by
  calc ∑ w, ∑ j, g w j = ∑ x : (J → I) × I, g x.1 x.2 := (Fintype.sum_prod_type' g).symm
    _ = ∑ x : (J → I) × I, g (Function.update x.1 s x.2) (x.1 s) :=
        (Equiv.sum_comp (Function.Involutive.toPerm _ (PositivityTheory.KReal.updInv s))
          (fun x => g x.1 x.2)).symm
    _ = ∑ w, ∑ j, g (Function.update w s j) (w s) :=
        Fintype.sum_prod_type' (fun w j => g (Function.update w s j) (w s))

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def positionA (m : Matrix I I ℂ) (Θ : (J → I) → V) : (J → I) → V :=
  fun w => ∑ s, ∑ j, m (w s) j • Θ (Function.update w s j)

def formT (Θ Θ' : (J → I) → V) : ℂ := ∑ w, ⟪Θ w, Θ' w⟫_ℂ

theorem formT_positionA (m : Matrix I I ℂ) (Θ Θ' : (J → I) → V) :
    formT (positionA mᴴ Θ) Θ' = formT Θ (positionA m Θ') := by
  unfold PositivityTheory.KReal.formT PositivityTheory.KReal.positionA
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.conjTranspose_apply,
    starRingEnd_apply, star_star]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  conv_rhs => rw [PositivityTheory.KReal.sum_upd s]
  simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

theorem formT_self_nonneg (a : (J → I) → V) : 0 ≤ (formT a a).re := by
  unfold PositivityTheory.KReal.formT
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun w _ => by
    have h := inner_self_nonneg (𝕜 := ℂ) (x := a w)
    rwa [RCLike.re_to_complex] at h

end SlopeTestRemainingChoices

theorem cas_tensor {K I J : Type} [Fintype K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J]
    (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (c0 : ℝ) (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (W : (J → I) → Module.End ℂ M)
    (hW : ∀ k w, e k * W w = W w * e k + ∑ i, ∑ j, c k j (w i) • W (Function.update w i j))
    (φ : M →ₗ[ℂ] ℂ) (Ψ : (J → I) → V) (hΨ : ∀ w v, ⟪Ψ w, v⟫_ℂ = φ (W w (ι v)))
    (hφ : ∀ w v, φ ((∑ k, e k * e (σ k)) (W w (ι v)) - (c0 : ℂ) • W w (ι v)) = 0)
    (hpos : ∀ (s : J) (w : J → I),
      0 ≤ (∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re = 0 →
        (fun i => Ψ (Function.update w s i)) = 0)) : Ψ = 0 := by
  have hc : ∀ k u x, e k (W u x) = W u (e k x) + ∑ i, ∑ j, c k j (u i) • W (Function.update u i j) x := by
    intro k u x
    have h := LinearMap.congr_fun (hW k u) x
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have hk : ∀ k u x, e k (e (σ k) (W u x)) = W u (e k (e (σ k) x)) +
      (∑ i, ∑ j, c k j (u i) • W (Function.update u i j) (e (σ k) x) +
        ∑ i, ∑ j, c (σ k) j (u i) • (W (Function.update u i j) (e k x) +
          ∑ i', ∑ j', c k j' (Function.update u i j i') •
            W (Function.update (Function.update u i j) i' j') x)) := by
    intro k u x

    simp only [hc, map_add (f := _), map_sum, map_smul, add_assoc]
  have hΨ' : ∀ u v, φ (W u (ι v)) = ⟪Ψ u, v⟫_ℂ := fun u v => (hΨ u v).symm
  have hΨe : ∀ k u v, φ (W u (e k (ι v))) = ⟪Ψ u, ρ k v⟫_ℂ := by
    intro k u v
    rw [← hι, hΨ]
  have hcas : ∀ v, ∑ k, e k (e (σ k) (ι v)) = (c0 : ℂ) • ι v := by
    intro v
    have h := congrArg ι (LinearMap.congr_fun hc0 v)

    simpa only [LinearMap.sum_apply, Module.End.mul_apply, map_sum, hι, LinearMap.smul_apply,
    Module.End.one_apply, map_smul] using h
  have hA : ∀ u v, ∑ k, φ (W u (e k (e (σ k) (ι v)))) = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by
    intro u v
    calc ∑ k, φ (W u (e k (e (σ k) (ι v)))) = φ (W u (∑ k, e k (e (σ k) (ι v)))) := by

          simp only [map_sum]
      _ = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by rw [hcas, map_smul, map_smul, hΨ', smul_eq_mul]
  have hF : ∀ w, ∑ k, (⟪PositivityTheory.KReal.positionA (c (σ k)) Ψ w, ρ (σ k) (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) Ψ w, ρ k (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ) w, Ψ w⟫_ℂ) = 0 := by
    intro w
    have h := hφ w (Ψ w)
    have h' := hA w (Ψ w)

    simp only [map_sub, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hk, map_add (f := _), map_smul,
    smul_eq_mul, hΨ', hΨe, h3, Matrix.conjTranspose_apply, starRingEnd_apply, star_star,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib] at h
    simp only [PositivityTheory.KReal.positionA, sum_inner, inner_smul_left, h3, Matrix.conjTranspose_apply,
      starRingEnd_apply, star_star, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    linear_combination h - h'
  have hsum : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun w _ => hF w)
    rw [Finset.sum_comm] at h
    simpa only [PositivityTheory.KReal.formT, Finset.sum_add_distrib] using h
  have hT1 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) =
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) :=
    Fintype.sum_equiv (Function.Involutive.toPerm σ hσ) _ _ (fun _ => rfl)
  have hck : ∀ k, c k = (c (σ k))ᴴ := fun k => by rw [← h3 (σ k), hσ k]
  have hT3 : 0 ≤ (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k)
      (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [hck k, PositivityTheory.KReal.formT_positionA]
    exact PositivityTheory.KReal.formT_self_nonneg _
  have hre2 : (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re ≤ 0 := by
    have h := congrArg Complex.re hsum
    rw [hT1, Complex.add_re, Complex.add_re, Complex.zero_re] at h
    linarith
  obtain ⟨q, hq⟩ : ∃ q : J → (J → I) → ℂ, ∀ s w, q s w = ∑ k, ∑ i, ∑ j,
      ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : J → (J → I) → ℂ, ∀ s w, H s w = ∑ k, ∑ j,
      ⟪Ψ w, c k (w s) j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  have hpos' : ∀ s w, 0 ≤ (q s w).re ∧ ((q s w).re = 0 → (fun i => Ψ (Function.update w s i)) = 0) := by
    intro s w
    rw [hq]
    exact hpos s w
  have hqH : ∀ s w, q s w = ∑ i, H s (Function.update w s i) := by
    intro s w
    simp only [hq, hH, Function.update_self, Function.update_idem]
    exact Finset.sum_comm
  have hsumH : ∀ s, ∑ w, q s w = (Fintype.card I : ℂ) * ∑ w, H s w := by
    intro s
    have h := PositivityTheory.KReal.sum_upd s (fun w i => H s (Function.update w s i))
    simp only [Function.update_idem, Function.update_eq_self] at h
    simp only [hqH, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hHc : ∀ s w, H s w = starRingEnd ℂ (∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
      ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by
    intro s w
    rw [hH]

    simp only [map_sum, map_mul, Complex.conj_conj, inner_conj_symm, inner_smul_right, ← hadj]
  have hT2 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) =
      ∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) * ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ := by
    simp only [PositivityTheory.KReal.formT, PositivityTheory.KReal.positionA, sum_inner, inner_smul_left]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
  have hHT : (∑ s, ∑ w, H s w).re =
      (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re := by
    rw [hT2, Finset.sum_comm]
    have e1 : ∑ w, ∑ s, H s w = starRingEnd ℂ (∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
        ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by

      simp only [hHc, map_sum]
    rw [e1, Complex.conj_re]
  have hQle : ∑ s, ∑ w, (q s w).re ≤ 0 := by
    have e2 : ∑ s, ∑ w, (q s w).re = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
      calc ∑ s, ∑ w, (q s w).re = ∑ s, ((Fintype.card I : ℂ) * ∑ w, H s w).re := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Complex.re_sum, hsumH]
        _ = ((Fintype.card I : ℂ) * ∑ s, ∑ w, H s w).re := by
            rw [Finset.mul_sum, Complex.re_sum]
        _ = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
            rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e2, hHT]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hre2
  have hQ0 : ∀ s w, (q s w).re = 0 := by
    intro s w
    have h1 : (q s w).re ≤ ∑ w', (q s w').re :=
      Finset.single_le_sum (f := fun w' => (q s w').re) (fun w' _ => (hpos' s w').1) (Finset.mem_univ w)
    have h2 : ∑ w', (q s w').re ≤ ∑ s', ∑ w', (q s' w').re :=
      Finset.single_le_sum (f := fun s' => ∑ w', (q s' w').re)
        (fun s' _ => Finset.sum_nonneg fun w' _ => (hpos' s' w').1) (Finset.mem_univ s)
    linarith [(hpos' s w).1]
  funext w
  have h := congrFun ((hpos' (Classical.arbitrary J) w).2 (hQ0 _ w)) (w (Classical.arbitrary J))
  simpa using h

end PositivityTheory.KReal

end
end
