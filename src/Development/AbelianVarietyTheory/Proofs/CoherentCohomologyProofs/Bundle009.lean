module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.QuotSMulTop
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.WeightAddLeOfMemSupportDividedContraction
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isBaseChange_gradedPiece : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup N] [Module R₀ N] [Module R N] [IsScalarTower R₀ R N] (𝒩₀ : ℤ → Submodule R₀ N₀) [Decomposition 𝒩₀] (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] (ψ : N₀ →ₗ[R₀] N) (n : ℤ) (θ : 𝒩₀ n →ₗ[R₀] 𝒩 n), IsBaseChange R ψ → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → (∀ y, (θ y : N) = ψ y) → IsBaseChange R θ := by
  intro R₀ R _ _ _ N₀ N _ _ _ _ _ _ 𝒩₀ _ 𝒩 _ ψ n θ h hdeg hθ
  let p₀ : N₀ →ₗ[R₀] 𝒩₀ n :=
    DirectSum.component R₀ ℤ (fun i => 𝒩₀ i) n ∘ₗ (decomposeLinearEquiv 𝒩₀).toLinearMap
  let p : N →ₗ[R] 𝒩 n :=
    DirectSum.component R ℤ (fun i => 𝒩 i) n ∘ₗ (decomposeLinearEquiv 𝒩).toLinearMap
  have hp₀ : ∀ y, p₀ y = decompose 𝒩₀ y n := fun _ => rfl
  have hp : ∀ y, p y = decompose 𝒩 y n := fun _ => rfl
  have hp₀i : ∀ y : 𝒩₀ n, p₀ (y : N₀) = y := fun y => by
    apply Subtype.ext
    rw [hp₀]
    exact decompose_of_mem_same 𝒩₀ y.2
  have hpi : ∀ y : 𝒩 n, p (y : N) = y := fun y => by
    apply Subtype.ext
    rw [hp]
    exact decompose_of_mem_same 𝒩 y.2
  have hcomm : ∀ y, θ (p₀ y) = p (ψ y) := by
    intro y
    induction y using Decomposition.inductionOn 𝒩₀ with
    | zero => simp
    | @homogeneous j y =>
      by_cases hj : j = n
      · subst hj
        rw [hp₀i, ← hθ, hpi]
      · have h1 : p₀ (y : N₀) = 0 := by
          apply Subtype.ext
          rw [hp₀]
          exact decompose_of_mem_ne 𝒩₀ y.2 hj
        have h2 : p (ψ y) = 0 := by
          apply Subtype.ext
          rw [hp]
          exact decompose_of_mem_ne 𝒩 (hdeg j y y.2) hj
        rw [h1, h2, map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let L : R ⊗[R₀] 𝒩₀ n →ₗ[R] 𝒩 n := LinearMap.liftBaseChange R θ
  have hL1 : ∀ x, L (p₀.baseChange R x) = p (h.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hcomm]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hL2 : ∀ x, (L x : N) = h.equiv ((𝒩₀ n).subtype.baseChange R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hθ]
    | add a b ha hb => simp only [map_add (f := _), Submodule.coe_add, ha, hb]
  have hret : ∀ x, p₀.baseChange R ((𝒩₀ n).subtype.baseChange R x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [hp₀i]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hbij : Function.Bijective L := by
    constructor
    · intro a b hab
      have h1 : h.equiv ((𝒩₀ n).subtype.baseChange R a)
          = h.equiv ((𝒩₀ n).subtype.baseChange R b) := by
        rw [← hL2, ← hL2, hab]
      rw [← hret a, h.equiv.injective h1, hret]
    · intro z
      refine ⟨p₀.baseChange R (h.equiv.symm z), ?_⟩
      rw [hL1, LinearEquiv.apply_symm_apply, hpi]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x => ?_
  simp [L]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem projMatrix_abstract {S : Type} [CommRing S] {P₀ P₁ P₂ F₀ F₁ G₁ G₂ : Type}
    [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
    [AddCommGroup F₀] [Module S F₀] [AddCommGroup F₁] [Module S F₁]
    [AddCommGroup G₁] [Module S G₁] [AddCommGroup G₂] [Module S G₂]
    (d₀ : P₀ →ₗ[S] P₁) (d₁ : P₁ →ₗ[S] P₂) (p₀ : F₀ →ₗ[S] P₀) (s₀ : P₀ →ₗ[S] F₀)
    (p₁ : F₁ →ₗ[S] P₁) (s₁ : P₁ →ₗ[S] F₁) (D₀ : F₀ →ₗ[S] G₁) (D₁ : G₁ →ₗ[S] G₂)
    (q₁ : G₁ →ₗ[S] F₁) (q₀ : G₁ →ₗ[S] F₀) (i₁ : F₁ →ₗ[S] G₁) (i₀ : F₀ →ₗ[S] G₁)
    (r₂ : G₂ →ₗ[S] P₂) (r₁ : G₂ →ₗ[S] F₁) (r₀ : G₂ →ₗ[S] P₀)
    (h₀ : p₀ ∘ₗ s₀ = LinearMap.id) (h₁ : p₁ ∘ₗ s₁ = LinearMap.id)
    (hq₁ : q₁ ∘ₗ D₀ = s₁ ∘ₗ d₀ ∘ₗ p₀) (hq₀ : q₀ ∘ₗ D₀ = LinearMap.id - s₀ ∘ₗ p₀)
    (hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id)
    (hr₂ : r₂ ∘ₗ D₁ = d₁ ∘ₗ p₁ ∘ₗ q₁) (hr₁ : r₁ ∘ₗ D₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁)
    (hr₀ : r₀ ∘ₗ D₁ = p₀ ∘ₗ q₀) :
    Set.BijOn p₀ {v | D₀ v = 0} (LinearMap.ker d₀) ∧
      (Function.Exact d₀ d₁ → ∀ w, D₁ w = 0 → ∃ v, D₀ v = w) := by
  have h₀ : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁ : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have hq₁ : ∀ x, q₁ (D₀ x) = s₁ (d₀ (p₀ x)) := fun x => LinearMap.congr_fun hq₁ x
  have hq₀ : ∀ x, q₀ (D₀ x) = x - s₀ (p₀ x) := fun x => LinearMap.congr_fun hq₀ x
  have hi : ∀ x, i₁ (q₁ x) + i₀ (q₀ x) = x := fun x => LinearMap.congr_fun hi x
  have hr₂ : ∀ x, r₂ (D₁ x) = d₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₂ x
  have hr₁ : ∀ x, r₁ (D₁ x) = q₁ x - s₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₁ x
  have hr₀ : ∀ x, r₀ (D₁ x) = p₀ (q₀ x) := fun x => LinearMap.congr_fun hr₀ x
  have key : ∀ v, D₀ v = 0 → s₀ (p₀ v) = v := fun v hv => by
    have := hq₀ v
    rw [hv, map_zero] at this
    exact (sub_eq_zero.mp this.symm).symm
  refine ⟨⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun x hx => ⟨s₀ x, ?_, h₀ x⟩⟩, ?_⟩
  · have hv : D₀ v = 0 := hv
    have := congrArg p₁ (hq₁ v)
    rw [hv, map_zero, map_zero, h₁] at this
    exact this.symm
  · rw [← key v hv, ← key v' hv', h]
  · have hx : d₀ x = 0 := hx
    show D₀ (s₀ x) = 0
    rw [← hi (D₀ (s₀ x)), hq₁, hq₀, h₀, hx]
    simp
  · intro hex w hw
    have e₂ := hr₂ w
    have e₁ := hr₁ w
    have e₀ := hr₀ w
    rw [hw, map_zero] at e₂ e₁ e₀
    obtain ⟨x, hx⟩ := (hex _).mp e₂.symm
    refine ⟨s₀ x + q₀ w, ?_⟩
    have hp : p₀ (s₀ x + q₀ w) = x := by rw [map_add (f := _), h₀, ← e₀, add_zero]
    rw [← hi (D₀ _), hq₁, hq₀, hp, hx, ← sub_eq_zero.mp e₁.symm, add_sub_cancel_left, hi]

theorem projMatrix_mulVec {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) (x : R' ⊗[R] (Fin a → R)) :
    ((LinearMap.toMatrix' f).map (algebraMap R R')).mulVec
        (TensorProduct.piScalarRight R R' R' (Fin a) x) =
      TensorProduct.piScalarRight R R' R' (Fin b) (f.baseChange R' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Matrix.mulVec_add, hx, hy]
  | tmul r y =>
    ext i
    have hy : f y = (LinearMap.toMatrix' f).mulVec y := by
      rw [LinearMap.toMatrix'_mulVec]
    rw [LinearMap.baseChange_tmul, hy]

    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, Algebra.smul_def, map_mul,
    map_sum, Finset.sum_mul, mul_assoc]

theorem projMatrix_sum {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a : ℕ} {P : Type} [AddCommGroup P] [Module R P] (p : (Fin a → R) →ₗ[R] P)
    (x : R' ⊗[R] (Fin a → R)) :
    ∑ k, TensorProduct.piScalarRight R R' R' (Fin a) x k ⊗ₜ[R] p (Pi.single k 1) =
      p.baseChange R' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul r y =>
    have hy : p y = ∑ k, y k • p (Pi.single k 1) := by

      simp only [← map_smul, ← map_sum]
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [LinearMap.baseChange_tmul, hy]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      TensorProduct.tmul_sum, TensorProduct.smul_tmul]

theorem exists_matrices_of_projective_complex :
    ∀ (R : Type) [CommRing R] (P₀ P₁ P₂ : Type) [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (d₀ : P₀ →ₗ[R] P₁) (d₁ : P₁ →ₗ[R] P₂), d₁ ∘ₗ d₀ = 0 → ∃ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R) (u : Fin a → P₀), D₁ * D₀ = 0 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], Set.BijOn (fun v : Fin a → R' => ∑ k, v k ⊗ₜ[R] u k) {v | (D₀.map (algebraMap R R')).mulVec v = 0} (LinearMap.ker (d₀.baseChange R')) ∧ (Function.Exact (d₀.baseChange R') (d₁.baseChange R') → ∀ w : Fin b → R', (D₁.map (algebraMap R R')).mulVec w = 0 → ∃ v, (D₀.map (algebraMap R R')).mulVec v = w) := by
  intro R _ P₀ P₁ P₂ _ _ _ _ _ _ _ _ _ _ _ _ d₀ d₁ hd
  obtain ⟨n₀, p₀, s₀, -, -, h₀⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₀
  obtain ⟨n₁, p₁, s₁, -, -, h₁⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₁
  obtain ⟨n₂, p₂, s₂, -, -, h₂⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₂
  have hE : ∀ n m : ℕ, Nonempty ((Fin (n + m) → R) ≃ₗ[R] (Fin n → R) × (Fin m → R)) :=
    fun n m => ⟨(LinearEquiv.funCongrLeft R R finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ R R)⟩
  obtain ⟨E⟩ := hE n₁ n₀
  obtain ⟨E'⟩ := hE n₂ (n₁ + n₀)
  have h₀' : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁' : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have h₂' : ∀ x, p₂ (s₂ x) = x := fun x => LinearMap.congr_fun h₂ x
  have hd' : ∀ x, d₁ (d₀ x) = 0 := fun x => LinearMap.congr_fun hd x
  let q₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₁ → R) := LinearMap.fst R _ _ ∘ₗ E.toLinearMap
  let q₀ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₀ → R) := LinearMap.snd R _ _ ∘ₗ E.toLinearMap
  let i₁ : (Fin n₁ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inl R _ _
  let i₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inr R _ _
  let f₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) :=
    E.symm.toLinearMap ∘ₗ LinearMap.prod (s₁ ∘ₗ d₀ ∘ₗ p₀) (LinearMap.id - s₀ ∘ₗ p₀)
  let f₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin (n₂ + (n₁ + n₀)) → R) :=
    E'.symm.toLinearMap ∘ₗ LinearMap.prod (s₂ ∘ₗ d₁ ∘ₗ p₁ ∘ₗ q₁)
      (E.symm.toLinearMap ∘ₗ LinearMap.prod (q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁) (s₀ ∘ₗ p₀ ∘ₗ q₀))
  let r₂ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₂ := p₂ ∘ₗ LinearMap.fst R _ _ ∘ₗ E'.toLinearMap
  let r₁ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] (Fin n₁ → R) :=
    q₁ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  let r₀ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₀ :=
    p₀ ∘ₗ q₀ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  have hq₁ : q₁ ∘ₗ f₀ = s₁ ∘ₗ d₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₁, f₀]
  have hq₀ : q₀ ∘ₗ f₀ = LinearMap.id - s₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₀, f₀]
  have hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id := LinearMap.ext fun x => by
    simp [q₀, q₁, i₀, i₁, ← map_add (f := _)]
  have hr₂ : r₂ ∘ₗ f₁ = d₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₂, f₁, h₂']
  have hr₁ : r₁ ∘ₗ f₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₁, f₁, q₁]
  have hr₀ : r₀ ∘ₗ f₁ = p₀ ∘ₗ q₀ := LinearMap.ext fun x => by simp [r₀, f₁, q₀, h₀']
  have hf : f₁ ∘ₗ f₀ = 0 := LinearMap.ext fun x => by
    have e₁ : q₁ (f₀ x) = s₁ (d₀ (p₀ x)) := LinearMap.congr_fun hq₁ x
    have e₀ : q₀ (f₀ x) = x - s₀ (p₀ x) := LinearMap.congr_fun hq₀ x
    simp [f₁, e₁, e₀, h₀', h₁', hd']
  refine ⟨n₀, n₁ + n₀, n₂ + (n₁ + n₀), LinearMap.toMatrix' f₀, LinearMap.toMatrix' f₁,
    fun k => p₀ (Pi.single k 1), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hf, map_zero]
  intro R' _ _
  obtain ⟨hB, hX⟩ := projMatrix_abstract (d₀.baseChange R') (d₁.baseChange R')
    (p₀.baseChange R') (s₀.baseChange R') (p₁.baseChange R') (s₁.baseChange R')
    (f₀.baseChange R') (f₁.baseChange R') (q₁.baseChange R') (q₀.baseChange R')
    (i₁.baseChange R') (i₀.baseChange R') (r₂.baseChange R') (r₁.baseChange R')
    (r₀.baseChange R')
    (by rw [← LinearMap.baseChange_comp, h₀, LinearMap.baseChange_id])
    (by rw [← LinearMap.baseChange_comp, h₁, LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hq₁])
    (by simp only [← LinearMap.baseChange_comp, hq₀, LinearMap.baseChange_sub,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, ← LinearMap.baseChange_add, hi,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hr₂])
    (by simp only [← LinearMap.baseChange_comp, hr₁, LinearMap.baseChange_sub])
    (by simp only [← LinearMap.baseChange_comp, hr₀])
  constructor
  · let e := TensorProduct.piScalarRight R R' R' (Fin n₀)
    have hmem : ∀ x, (((LinearMap.toMatrix' f₀).map (algebraMap R R')).mulVec (e x) = 0) ↔
        f₀.baseChange R' x = 0 := fun x => by
      rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff]
    refine ⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun y hy => ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective v
      have := hB.mapsTo ((hmem x).mp hv)
      rwa [← projMatrix_sum] at this
    · obtain ⟨x, rfl⟩ := e.surjective v
      obtain ⟨x', rfl⟩ := e.surjective v'
      congr 1
      refine hB.injOn ((hmem x).mp hv) ((hmem x').mp hv') ?_
      rw [← projMatrix_sum, ← projMatrix_sum]
      exact h
    · obtain ⟨x, hx, rfl⟩ := hB.surjOn hy
      exact ⟨e x, (hmem x).mpr hx, projMatrix_sum R' p₀ x⟩
  · intro hex w hw
    obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight R R' R' (Fin (n₁ + n₀))).surjective w
    rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff] at hw
    obtain ⟨v, rfl⟩ := hX hex x hw
    exact ⟨_, projMatrix_mulVec R' f₀ v⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

open scoped Pointwise

namespace GlobalTheory

theorem flat_quotSMulTop_coker_of_matrix_witnesses :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (r a b : ℕ) (g : Fin r → S) (u : S) (Φ : Matrix (Fin a) (Fin b) S), Module.Flat R (S ⧸ Ideal.span (Set.range g)) → (∃ c : Fin r → S, u = ∑ k, c k * g k) → (∀ k, ∃ (C : Matrix (Fin b) (Fin a) S) (C' : Matrix (Fin a) (Fin a) S), g k • (1 : Matrix (Fin a) (Fin a) S) = Φ * C + u • C') → (∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S), Φ * Ψ * Φ = Φ + ∑ k, g k • E k) → Module.Flat R (QuotSMulTop u ((Fin a → S) ⧸ LinearMap.range Φ.mulVecLin)) := by
  intro R S _ _ _ r a b g u Φ hflat hu hker hreg
  obtain ⟨c, hc⟩ := hu
  obtain ⟨Ψ, E, hΨ⟩ := hreg
  let I : Ideal S := Ideal.span (Set.range g)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have huI : u ∈ I := by
    rw [hc]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hgI k)
  have hmv : ∀ {m : ℕ} (A : Matrix (Fin a) (Fin m) S), (∀ j i, A j i ∈ I) →
      ∀ y j, (Matrix.mulVec A y) j ∈ I := by
    intro m A hA y j
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hA j i)
  let K := LinearMap.range Φ.mulVecLin
  let M := (Fin a → S) ⧸ K
  let T : Submodule S M := u • (⊤ : Submodule S M)
  let pr : (Fin a → S) →ₗ[S] QuotSMulTop u M := T.mkQ ∘ₗ K.mkQ
  have hK : ∀ y, pr (Matrix.mulVec Φ y) = 0 := by
    intro y
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    have hy : K.mkQ (Matrix.mulVec Φ y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 ⟨y, rfl⟩
    rw [hy, Submodule.Quotient.mk_zero]
  have hU : ∀ z, pr (u • z) = 0 := by
    intro z
    simp only [pr, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [map_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hG : ∀ k x, g k • pr x = 0 := by
    intro k x
    obtain ⟨C, C', h⟩ := hker k
    have hx : g k • x = Matrix.mulVec Φ (Matrix.mulVec C x) + u • Matrix.mulVec C' x := by
      have := congrArg (fun A => Matrix.mulVec A x) h
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec] at this
      exact this
    rw [← map_smul, hx, map_add (f := _), hK, hU, add_zero]
  have hI : ∀ s ∈ I, ∀ x, s • pr x = 0 := by
    intro s hs x
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hs
    simp only [Finset.sum_smul, smul_eq_mul, mul_smul, hG, smul_zero, Finset.sum_const_zero]
  let q : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) :=
    LinearMap.pi fun j => (Submodule.mkQ I) ∘ₗ LinearMap.proj j
  have hq : ∀ v, (∀ j, v j ∈ I) → q v = 0 := by
    intro v hv
    funext j
    exact (Submodule.Quotient.mk_eq_zero I).2 (hv j)
  have hqI : ∀ s ∈ I, ∀ w : Fin a → S ⧸ I, s • w = 0 := by
    intro s hs w
    funext j
    obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective I (w j)
    rw [Pi.smul_apply, ← ht, ← Submodule.Quotient.mk_smul, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hs
  have hE : ∀ j i, (∑ k, g k • E k) j i ∈ I := by
    intro j i
    rw [Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hgI k)
  let f0 : (Fin a → S) →ₗ[S] (Fin a → S ⧸ I) := q ∘ₗ (LinearMap.id - (Φ * Ψ).mulVecLin)
  have h1 : K ≤ LinearMap.ker f0 := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [f0, LinearMap.comp_apply]
    apply hq
    intro j
    have hy : Φ.mulVecLin y - (Φ * Ψ).mulVecLin (Φ.mulVecLin y) = -(Matrix.mulVec (∑ k, g k • E k) y) := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hΨ, Matrix.add_mulVec]
      abel
    rw [LinearMap.sub_apply, LinearMap.id_apply, hy, Pi.neg_apply]
    exact Submodule.neg_mem _ (hmv _ hE y j)
  let f1 : M →ₗ[S] (Fin a → S ⧸ I) := K.liftQ f0 h1
  have h2 : T ≤ LinearMap.ker f1 := by
    intro m hm
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    rw [LinearMap.mem_ker, map_smul]
    exact hqI u huI _
  let i : QuotSMulTop u M →ₗ[S] (Fin a → S ⧸ I) := T.liftQ f1 h2
  let p : (Fin a → S ⧸ I) →ₗ[S] QuotSMulTop u M :=
    ∑ j, (Submodule.liftQ I (LinearMap.toSpanSingleton S _ (pr (Pi.single j 1)))
      (fun s hs => by
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
        exact hI s hs _)) ∘ₗ LinearMap.proj j
  have hpq : ∀ v, p (q v) = pr v := by
    intro v
    simp only [p, q, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply]

    conv_rhs => rw [← Finset.univ_sum_single v, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    refine congrArg pr ?_
    funext k
    by_cases h : k = j <;> simp [h]
  have hpi : p ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun n => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective T n
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K m
    show p (q (x - (Φ * Ψ).mulVecLin x)) = pr x
    rw [hpq, map_sub, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hK, sub_zero]
  have := hflat
  have : Module.Flat R (Fin a → S ⧸ I) :=
    Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin a => S ⧸ I)).symm
  exact Module.Flat.of_retract (i.restrictScalars R) (p.restrictScalars R)
    (LinearMap.ext fun n => LinearMap.congr_fun hpi n)

end GlobalTheory
end
