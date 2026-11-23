module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.ThetaProd

theorem hasLevel_mul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (S : ℕ)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : HasLevel (S * R) φ := by
  refine ⟨fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h.1 x hx k i).nsmul S
    simpa [mul_assoc] using this
  · have := h.2 x ((S : ℚ) • y) fun k i => by simpa using (hy k i).nsmul S
    rw [← this, smul_smul, Nat.cast_mul, mul_comm]

theorem isSB_prod {κ ι₁ ι₂ : Type} [Fintype κ] [Fintype ι₁] [Fintype ι₂]
    {φ₁ : Matrix κ ι₁ ℚ → ℂ} {φ₂ : Matrix κ ι₂ ℚ → ℂ} (h₁ : IsSB φ₁) (h₂ : IsSB φ₂) :
    IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) := by
  obtain ⟨R₁, hR₁, h₁⟩ := h₁
  obtain ⟨R₂, hR₂, h₂⟩ := h₂
  have g₁ := hasLevel_mul R₂ h₁
  have g₂ := hasLevel_mul R₁ h₂
  rw [mul_comm] at g₁
  refine ⟨R₁ * R₂, by positivity, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have a₁ := g₁.1 _ (left_ne_zero_of_mul hx)
    have a₂ := g₂.1 _ ((map_ne_zero conj).1 (right_ne_zero_of_mul hx))
    rcases i with i | i
    · exact a₁ k i
    · have := (a₂ k i).neg
      simpa [toCols₂] using this
  · have a₁ := g₁.2 x.toCols₁ y.toCols₁ fun k i => hy k (Sum.inl i)
    have a₂ := g₂.2 (-x.toCols₂) (-y.toCols₂) fun k i => (hy k (Sum.inr i)).neg
    have e₁ : (x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₁ =
      x.toCols₁ + ((R₁ * R₂ : ℕ) : ℚ) • y.toCols₁ := rfl
    have e₂ : -(x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₂ =
      -x.toCols₂ + ((R₁ * R₂ : ℕ) : ℚ) • (-y.toCols₂) := by
      rw [smul_neg, ← neg_add]; rfl
    simp only [e₁, e₂, a₁, a₂]

theorem fromBlocks_mem_siegel {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {τ₁ : Matrix ι₁ ι₁ ℂ} {τ₂ : Matrix ι₂ ι₂ ℂ} (h₁ : τ₁ ∈ Siegel ι₁) (h₂ : τ₂ ∈ Siegel ι₂) :
    Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) := by
  refine ⟨Matrix.IsSymm.fromBlocks h₁.1 (by simp) (h₂.1.map _).neg, ?_⟩
  have e : (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map Complex.im =
      Matrix.fromBlocks (τ₁.map Complex.im) 0 0 (τ₂.map Complex.im) := by
    ext (i | i) (j | j) <;> simp
  rw [e]
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨Matrix.IsHermitian.fromBlocks h₁.2.isHermitian (by simp) h₂.2.isHermitian, fun x hx => ?_⟩
  obtain ⟨u, v, rfl⟩ : ∃ u v, x = Sum.elim u v :=
    ⟨x ∘ Sum.inl, x ∘ Sum.inr, (Sum.elim_comp_inl_inr x).symm⟩
  rw [star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  have a := h₁.2.posSemidef.dotProduct_mulVec_nonneg u
  have b := h₂.2.posSemidef.dotProduct_mulVec_nonneg v
  rw [star_trivial] at a b
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      rintro rfl
      apply hx
      rw [hu]
      ext (i | i) <;> rfl
    have := h₂.2.dotProduct_mulVec_pos hv
    rw [star_trivial] at this
    linarith
  · have := h₁.2.dotProduct_mulVec_pos hu
    rw [star_trivial] at this
    linarith

def colsEquiv (κ ι₁ ι₂ : Type) : Matrix κ (ι₁ ⊕ ι₂) ℚ ≃ Matrix κ ι₁ ℚ × Matrix κ ι₂ ℚ where
  toFun m := (m.toCols₁, -m.toCols₂)
  invFun p := fromCols p.1 (-p.2)
  left_inv m := by simp
  right_inv p := by simp

theorem row_exponent {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (τ₁ : Matrix ι₁ ι₁ ℂ) (τ₂ : Matrix ι₂ ι₂ ℂ) (ζ₁ : ι₁ → ℂ) (ζ₂ : ι₂ → ℂ) (v : ι₁ ⊕ ι₂ → ℚ) :
    qv v ⬝ᵥ Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) *ᵥ qv v +
        2 * (qv v ⬝ᵥ Sum.elim ζ₁ (star ζ₂)) =
      (qv (fun i => v (Sum.inl i)) ⬝ᵥ τ₁ *ᵥ qv (fun i => v (Sum.inl i)) +
        2 * (qv (fun i => v (Sum.inl i)) ⬝ᵥ ζ₁)) -
      conj (qv (fun i => -v (Sum.inr i)) ⬝ᵥ τ₂ *ᵥ qv (fun i => -v (Sum.inr i)) +
        2 * (qv (fun i => -v (Sum.inr i)) ⬝ᵥ ζ₂)) := by
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp [dotProduct, mulVec, qv, Fintype.sum_sum_type, h2]
  ring

theorem thS_mul_conj_thS : ∀ (κ ι₁ ι₂ : Type) [Fintype κ] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (φ₁ : Matrix κ ι₁ ℚ → ℂ) (φ₂ : Matrix κ ι₂ ℚ → ℂ), IsSB φ₁ → IsSB φ₂ → IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) ∧ ∀ τ₁ ∈ Siegel ι₁, ∀ τ₂ ∈ Siegel ι₂, Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) ∧ ∀ (ζ₁ : κ → ι₁ → ℂ) (ζ₂ : κ → ι₂ → ℂ), thS φ₁ τ₁ ζ₁ * conj (thS φ₂ τ₂ ζ₂) = thS (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))) (fun k => Sum.elim (ζ₁ k) (star (ζ₂ k))) := by
  intro κ ι₁ ι₂ _ _ _ _ _ φ₁ φ₂ h₁ h₂
  refine ⟨isSB_prod h₁ h₂, fun τ₁ t₁ τ₂ t₂ => ⟨fromBlocks_mem_siegel t₁ t₂, fun ζ₁ ζ₂ => ?_⟩⟩
  have s₁ := SiegelSum.summable_norm_thetaTerm κ ι₁ φ₁ h₁ τ₁ t₁ ζ₁
  have s₂ := SiegelSum.summable_norm_thetaTerm κ ι₂ φ₂ h₂ τ₂ t₂ ζ₂
  unfold thS
  rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm s₁
    (by simpa only [Complex.norm_conj] using s₂), ← (colsEquiv κ ι₁ ι₂).tsum_eq]
  refine tsum_congr fun m => ?_

  simp only [row_exponent, Finset.sum_sub_distrib, mul_sub, ← map_sum]
  rw [map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
    sub_eq_add_neg, Complex.exp_add, mul_mul_mul_comm, mul_neg, neg_mul]
  rfl

end GlobalTheory.SW.ThetaProd
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.GaussSum

theorem twist {N W : Type} [AddCommGroup N] [Fintype N] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (Q : N → W) (B : N →+ N →+ W) (hQ : ∀ x y, Q (x + y) = Q x + Q y + B x y) (ψ : N →+ W)
    (hT : ∑ x, e (Q x) = ∑ x, e (ψ x - Q x)) :
    ∑ x, e (Q x) = 0 ∨ ∃ a, ∑ x, e (Q x) = e (Q a) * conj (∑ x, e (Q x)) := by
  by_cases hz : ∑ x, e (Q x) = 0
  · exact Or.inl hz
  right
  have hsq : (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) := by
    calc (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ x, e (ψ x - Q x) * ∑ y, e (Q y) := by
          rw [← Finset.sum_mul, ← hT]
      _ = ∑ x, ∑ z, e (Q z) * e (ψ x + B x z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Equiv.sum_comp (Equiv.addLeft x), Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [← he, ← he, Equiv.coe_addLeft, hQ]
          congr 1
          abel
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
  have hne : ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) ≠ 0 := hsq ▸ mul_ne_zero hz hz
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ha' := right_ne_zero_of_mul ha
  have h1 : ∀ y, e (ψ y + B y a) = 1 := by
    intro y
    have : ∑ x, e (ψ x + B x a) = e (ψ y + B y a) * ∑ x, e (ψ x + B x a) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addLeft y)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← he, Equiv.coe_addLeft]
      congr 1
      simp only [map_add (f := _), AddMonoidHom.add_apply]
      abel
    exact (mul_eq_right₀ ha').1 this.symm
  refine ⟨a, ?_⟩
  conv_lhs => rw [hT]

  rw [map_sum, ← Equiv.sum_comp (Equiv.addRight a) (fun x => conj (e (Q x))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hc, ← he, Equiv.coe_addRight, hQ, ← mul_one (e (Q a + _)), ← h1 x, ← he]
  congr 1
  abel

def quat {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) : Fin 4 → M :=
  ![a • x 0 + (-b) • x 1 + (-c) • x 2 + (-d) • x 3,
    b • x 0 + a • x 1 + (-d) • x 2 + c • x 3,
    c • x 0 + d • x 1 + a • x 2 + (-b) • x 3,
    d • x 0 + (-c) • x 1 + b • x 2 + a • x 3]

theorem quat_add {M : Type} [AddCommGroup M] (a b c d : ℤ) (x y : Fin 4 → M) :
    quat a b c d (x + y) = quat a b c d x + quat a b c d y := by
  funext i
  fin_cases i <;> simp [quat] <;> module

theorem quat_conj {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) (i : Fin 4) :
    quat a (-b) (-c) (-d) (quat a b c d x) i = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • x i := by
  fin_cases i <;> simp [quat] <;> module

theorem quat_form {M W : Type} [AddCommGroup M] [AddCommGroup W] (β : M →+ M →+ W) (a b c d : ℤ)
    (x y : Fin 4 → M) :
    ∑ i, β (quat a b c d x i) (quat a b c d y i) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • ∑ i, β (x i) (y i) := by
  simp only [Fin.sum_univ_four, quat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply]
  module

theorem pow_four {M W : Type} [AddCommGroup M] [Fintype M] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (q : M → W) (β : M →+ M →+ W) (hq : ∀ x y, q (x + y) = q x + q y + β x y) :
    (∑ x, e (q x)) ^ 4 = 0 ∨ ∃ a : Fin 4 → M,
      (∑ x, e (q x)) ^ 4 = (∏ i, e (q (a i))) * conj ((∑ x, e (q x)) ^ 4) := by
  classical
  set n := Fintype.card M with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hnx : ∀ x : M, (n : ℤ) • x = 0 := fun x => by
    rw [natCast_zsmul]; exact card_nsmul_eq_zero
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n - 1)
  have hm : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (n : ℤ) - 1 := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) habcd
    push_cast [Nat.cast_sub hn1] at h
    exact h
  have hinj : Function.Injective (quat (M := M) (a : ℤ) b c d) := by
    intro x y hxy
    funext i
    have hx := quat_conj (a : ℤ) b c d x i
    have hy := quat_conj (a : ℤ) b c d y i
    rw [hm, sub_smul, hnx, one_smul, zero_sub] at hx hy
    rw [← neg_inj, ← hx, ← hy, hxy]
  have hbij := hinj.bijective_of_finite
  have hprod : ∀ y : Fin 4 → W, e (∑ i, y i) = ∏ i, e (y i) := by
    intro y; simp only [Fin.sum_univ_four, Fin.prod_univ_four, he]
  have hS4 : (∑ x, e (q x)) ^ 4 = ∑ x : Fin 4 → M, e (∑ i, q (x i)) := by
    rw [Finset.sum_pow', Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun x _ => (hprod (fun i => q (x i))).symm)
  let B : (Fin 4 → M) →+ (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => ∑ i, β (x i) (y i))
      (fun y z => by simp [Finset.sum_add_distrib]))
    (fun x y => by ext z; simp [Finset.sum_add_distrib])
  have hB : ∀ x y, B x y = ∑ i, β (x i) (y i) := fun _ _ => rfl
  have hQ : ∀ x y : Fin 4 → M, ∑ i, q ((x + y) i) = ∑ i, q (x i) + ∑ i, q (y i) + B x y := by
    intro x y
    simp only [hB, Pi.add_apply, hq, Finset.sum_add_distrib]
  have hnB : ∀ x y, (n : ℤ) • B x y = 0 := by
    intro x y
    rw [← map_zsmul]
    have : (n : ℤ) • y = 0 := funext fun i => hnx (y i)
    rw [this, map_zero]
  let ψ : (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => ∑ i, q (quat (a : ℤ) b c d x i) + ∑ i, q (x i)) (by
      intro x y
      rw [quat_add, hQ, hQ, hB (quat _ _ _ _ _), quat_form, hm, ← hB, sub_smul, hnB, one_smul]
      abel)
  have := twist e he hc h0 (fun x : Fin 4 → M => ∑ i, q (x i)) B hQ ψ (by
    rw [← hbij.sum_comp (fun x => e (∑ i, q (x i)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp [ψ])
  rw [← hS4] at this
  simpa only [hprod] using this

theorem isMu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [mul_pow, pow_mul, h, mul_comm m, pow_mul, h']; simp

theorem isMu_norm {a : ℂ} (ha : IsMu a) : ‖a‖ = 1 := by
  obtain ⟨m, hm, h⟩ := ha
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this

theorem ph_sum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  intro M _ _ f ⟨h1, h3⟩
  have hmu : ∀ x, IsMu (f x) := fun x => h1 x trivial
  let u : M → Circle := fun x => ⟨f x, mem_sphere_zero_iff_norm.2 (isMu_norm (hmu x))⟩
  let p : M → Additive Circle := fun x => Additive.ofMul (u x)
  have hp : ∀ x y z, p (x + y + z) + p x + p y + p z = p (x + y) + p (y + z) + p (x + z) + p 0 := by
    intro x y z
    have : u (x + y + z) * u x * u y * u z = u (x + y) * u (y + z) * u (x + z) * u 0 :=
      Circle.ext (by simp only [Circle.coe_mul]; exact h3 x trivial y trivial z trivial)
    exact congrArg Additive.ofMul this
  let β : M →+ M →+ Additive Circle := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => p (x + y) - p x - p y + p 0)
      (fun y z => by
        have := hp x y z
        rw [← add_assoc]
        rw [← sub_eq_zero] at this ⊢; rw [← this]; abel))
    (fun x y => by
      ext1 z
      have := hp x y z
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← sub_eq_zero] at this ⊢; rw [← this]; abel)
  let e : Additive Circle → ℂ := fun t => ((Additive.toMul t : Circle) : ℂ)
  have he : ∀ s t, e (s + t) = e s * e t := fun s t => by simp [e]
  have hc : ∀ t, e (-t) = conj (e t) := fun t => by
    simp only [e, toMul_neg]; exact Circle.coe_inv_eq_conj _
  have hf : ∀ x, f x = f 0 * e (p x - p 0) := by
    intro x
    have : e (p 0 + (p x - p 0)) = e (p x) := by congr 1; abel
    rw [he] at this
    exact this.symm
  have hmu' : ∀ x, IsMu (e (p x - p 0)) := by
    intro x
    rw [sub_eq_add_neg, he, hc]
    refine isMu_mul (hmu x) ?_
    obtain ⟨m, hm, h⟩ := hmu 0
    exact ⟨m, hm, by rw [← map_pow]; change conj (f 0 ^ m) = 1; rw [h, map_one]⟩
  have hsum : ∑ x, f x = f 0 * ∑ x, e (p x - p 0) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => hf x
  rw [hsum]
  rcases pow_four e he hc (by simp [e]) (fun x => p x - p 0) β (fun x y => by
    simp only [β, AddMonoidHom.mk'_apply]; abel) with h | ⟨a, h⟩
  · rw [pow_eq_zero_iff (by norm_num)] at h
    rw [h, mul_zero]; exact ph_zero
  · set S := ∑ x, e (p x - p 0)
    have hz : IsMu (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) := by
      refine isMu_mul ?_ ?_
      · obtain ⟨m, hm, h⟩ := hmu 0
        exact ⟨m, hm, by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]⟩
      · rw [Fin.prod_univ_four]
        exact isMu_mul (isMu_mul (isMu_mul (hmu' _) (hmu' _)) (hmu' _)) (hmu' _)
    obtain ⟨m, hm, hz⟩ := hz
    refine ⟨8 * m, by omega, ?_⟩
    have h8 : (f 0 * S) ^ 8 = (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) * ((‖f 0 * S‖ : ℝ) : ℂ) ^ 8 := by
      have hn : ((‖S‖ : ℝ) : ℂ) ^ 8 = S ^ 4 * conj (S ^ 4) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]; push_cast; ring
      rw [norm_mul, isMu_norm (hmu 0), one_mul, hn]
      linear_combination f 0 ^ 8 * S ^ 4 * h
    rw [pow_mul, h8, mul_pow, hz, one_mul, pow_mul]

end GlobalTheory.Phase.GaussSum
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem rep_eq_of_neg_rep_add_rep_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -_root_.GlobalTheory.SW.FourierJ.rep R n + _root_.GlobalTheory.SW.FourierJ.rep R n' =
      R • _root_.GlobalTheory.SW.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem exists_rep_add_natCast_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : _root_.GlobalTheory.SW.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = _root_.GlobalTheory.SW.FourierJ.rep R n + R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    Summable (fun x => φ x * F x) → ∑' x, φ x * F x =
      ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) *
        ∑' m : κ → ι → ℤ, F (_root_.GlobalTheory.SW.FourierJ.rep R n +
          (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m) := by
  intro κ ι _ _ _ _ R φ F hR hφ hsum
  have hRq : (R : ℚ) ≠ 0 := by positivity
  have hsmul : ∀ m : κ → ι → ℤ, (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m = R • _root_.GlobalTheory.SW.FourierJ.zm m :=
    fun m => Nat.cast_smul_eq_nsmul ℚ R _
  let e : (κ → ι → Fin (R * R)) × (κ → ι → ℤ) → Matrix κ ι ℚ := fun p =>
    _root_.GlobalTheory.SW.FourierJ.rep R p.1 + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm p.2
  have he : Function.Injective e := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ h
    simp only [e] at h
    have hn : n = n' := by
      apply rep_eq_of_neg_rep_add_rep_eq_smul_zm hR (m - m')
      ext k i
      have hk := congrFun (congrFun h k) i
      simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul, smul_eq_mul,
        Pi.sub_apply] at hk ⊢
      push_cast
      linear_combination -hk
    subst hn
    have hm : m = m' := by
      funext k i
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.add_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply,
        smul_eq_mul, add_right_inj] at hk
      exact_mod_cast mul_left_cancel₀ hRq hk
    rw [hm]
  have hsupp : Function.support (fun x => φ x * F x) ⊆ Set.range e := by
    intro x hx
    have hφx : φ x ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hx)
    obtain ⟨n, m, hnm⟩ := exists_rep_add_natCast_smul_zm_of_intM_smul hR x (hφ.1 x hφx)
    exact ⟨(n, m), by simp only [e, hsmul]; exact hnm.symm⟩
  rw [← he.tsum_eq hsupp]
  have hs2 : Summable fun p => φ (e p) * F (e p) := hsum.comp_injective he
  rw [hs2.tsum_prod' (fun n => hs2.comp_injective (by intro m m' h; simpa using h)),
    tsum_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [e]
  rw [hφ.2 _ _ ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)]

end GlobalTheory.SW.FourierJ
end
