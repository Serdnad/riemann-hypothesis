module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanPlane

open Matrix

theorem star_mulVec_map {m k : Type} [Fintype k] (B : Matrix m k ℂ) (v : k → ℂ) :
    star (B *ᵥ v) = B.map star *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, star_sum]

theorem form_mulVec {m k l : Type} [Fintype m] [Fintype k] [Fintype l] (A : Matrix m k ℂ) (B : Matrix m l ℂ)
    (M : Matrix m m ℂ) (u : k → ℂ) (v : l → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (B *ᵥ v) = u ⬝ᵥ (Aᵀ * M * B.map star) *ᵥ star v := by
  rw [star_mulVec_map, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ u),
    dotProduct_mulVec, dotProduct_comm]

theorem herm_swap {m : Type} [Fintype m] (M : Matrix m m ℂ) (hM : Mᴴ = M) (x y : m → ℂ) :
    y ⬝ᵥ M *ᵥ star x = star (x ⬝ᵥ M *ᵥ star y) := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by rw [← conjTranspose_apply, hM]
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_form {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, x ⬝ᵥ A *ᵥ star y = x ⬝ᵥ B *ᵥ star y) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

end GlobalTheory.CartanPlane

namespace GlobalTheory.CartanPlane
open Matrix

theorem extend_swap : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  intro n n₁ M X Yv ι P θ₁ hn hM hXX hYY hXY hιX hιY hPι hθ₁
  subst hn
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hYX : Yv ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap M hM, hXY]; simp
  have hιuX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιX, zero_dotProduct]
  have hιuY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Yv = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιY, zero_dotProduct]
  have hXιu : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuX, star_zero]
  have hYιu : ∀ u, Yv ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuY, star_zero]
  have hιι : ∀ u u', (ι *ᵥ u) ⬝ᵥ M *ᵥ star (ι *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => form_mulVec ι ι M u u'
  have hexp : ∀ u (a b : ℂ) u' (a' b' : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star (ι *ᵥ u' + a' • X + b' • Yv) =
      u ⬝ᵥ M₁ *ᵥ star u' + a * star b' + b * star a' := by
    intro u a b u' a' b'
    simp only [add_dotProduct, star_add, mulVec_add, dotProduct_add, smul_dotProduct, star_smul, mulVec_smul,
      dotProduct_smul, hιι, hιuX, hιuY, hXιu, hYιu, hXX, hYY, hXY, hYX, smul_eq_mul]
    ring
  have hcY : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star Yv = a := by
    intro u a b; have := hexp u a b 0 0 1; simpa using this
  have hcX : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star X = b := by
    intro u a b; have := hexp u a b 0 1 0; simpa using this

  have hdec : ∀ z : Fin (n₁ + 2) → ℂ, ∃ (u : Fin n₁ → ℂ) (a b : ℂ), z = ι *ᵥ u + a • X + b • Yv := by
    let Φ : ((Fin n₁ → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin (n₁ + 2) → ℂ) :=
      (Matrix.toLin' ι).comp (LinearMap.fst ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight X).comp (LinearMap.snd ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight Yv).comp (LinearMap.snd ℂ _ _)
    have hΦ : ∀ p, Φ p = ι *ᵥ p.1 + p.2 0 • X + p.2 1 • Yv := fun p => by simp [Φ]
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨u, w⟩ h0
      rw [hΦ] at h0
      have ha := hcY u (w 0) (w 1)
      have hb := hcX u (w 0) (w 1)
      simp only at h0 ha hb
      rw [h0, zero_dotProduct] at ha hb
      have hu : ι *ᵥ u = 0 := by rw [← ha, ← hb] at h0; simpa using h0
      have : u = 0 := by rw [← one_mulVec u, ← hPι, ← mulVec_mulVec, hu, mulVec_zero]
      refine Prod.ext this ?_
      ext i; fin_cases i <;> simp [← ha, ← hb]
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod])).mp hinj
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨p.1, p.2 0, p.2 1, by rw [← hp, hΦ]⟩

  set vX := M *ᵥ star X with hvX
  set vY := M *ᵥ star Yv with hvY
  set C₁ : Matrix (Fin n₁) (Fin (n₁ + 2)) ℂ := P - vecMulVec (P *ᵥ X) vY - vecMulVec (P *ᵥ Yv) vX with hC₁
  set θ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := ι * θ₁ * C₁ + vecMulVec Yv vY + vecMulVec X vX with hθdef
  have hθ : ∀ u (a b : ℂ), θ *ᵥ (ι *ᵥ u + a • X + b • Yv) = ι *ᵥ (θ₁ *ᵥ u) + b • X + a • Yv := by
    intro u a b
    have ha : vY ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = a := by rw [dotProduct_comm]; exact hcY u a b
    have hb : vX ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = b := by rw [dotProduct_comm]; exact hcX u a b
    have hC : C₁ *ᵥ (ι *ᵥ u + a • X + b • Yv) = u := by
      rw [hC₁, sub_mulVec, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, mulVec_add, mulVec_add,
        mulVec_smul, mulVec_smul, mulVec_mulVec, hPι, one_mulVec]
      simp only [op_smul_eq_smul]
      abel
    rw [hθdef, add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, ← mulVec_mulVec, ← mulVec_mulVec, hC]
    simp only [op_smul_eq_smul]
    abel
  have hext : ∀ A B : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ,
      (∀ u (a b : ℂ), A *ᵥ (ι *ᵥ u + a • X + b • Yv) = B *ᵥ (ι *ᵥ u + a • X + b • Yv)) → A = B := by
    intro A B h
    apply ext_of_mulVec_single
    intro i
    obtain ⟨u, a, b, hz⟩ := hdec (Pi.single i 1)
    rw [hz, h]
  have hθ₁θ₁ : ∀ u, θ₁ *ᵥ (θ₁ *ᵥ u) = u := fun u => by rw [mulVec_mulVec, hθ₁.1, one_mulVec]
  have hiso₁ : ∀ u u', (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star (θ₁ *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => by
    rw [form_mulVec, hθ₁.2.1]
  have hre : ∀ c : ℂ, (c * star c).re = Complex.normSq c := fun c => by
    simp [Complex.mul_re, Complex.normSq_apply]
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply hext
    intro u a b
    rw [← mulVec_mulVec, hθ, hθ, hθ₁θ₁, one_mulVec]
  · apply ext_form
    intro x y
    rw [← form_mulVec]
    obtain ⟨u, a, b, rfl⟩ := hdec x
    obtain ⟨u', a', b', rfl⟩ := hdec y
    rw [hθ, hθ, hexp, hexp, hiso₁]
    ring
  · intro x hx
    obtain ⟨u, a, b, rfl⟩ := hdec x
    rw [hθ, hexp, Complex.add_re, Complex.add_re, hre, hre]
    by_cases hu : u = 0
    · subst hu
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        simp [h.1, h.2]
      simp only [mulVec_zero, zero_dotProduct, Complex.zero_re, zero_add]
      rcases hab with h | h
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg b; linarith
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg a; linarith
    · have := hθ₁.2.2 u hu
      have := Complex.normSq_nonneg b; have := Complex.normSq_nonneg a; linarith
  · apply ext_of_mulVec_single
    intro j
    have := hθ (Pi.single j 1) 0 0
    simp only [zero_smul, add_zero] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, this]
  · have := hθ 0 1 0
    simpa using this

end GlobalTheory.CartanPlane
end

section

noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

section Real

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

def schrF (P : V → V → ℝ) (w : V × V) (f : V → ℂ) : V → ℂ :=
  fun y => Complex.exp (-(2 * Real.pi * Complex.I) * ((P y w.2 + P w.1 w.2 / 2 : ℝ) : ℂ)) * f (y + w.1)

def omega (P : V → V → ℝ) (w w' : V × V) : ℝ := P w.1 w'.2 - P w'.1 w.2

structure IsPairing (P : V → V → ℝ) : Prop where
  addL : ∀ x x' y, P (x + x') y = P x y + P x' y
  addR : ∀ x y y', P x (y + y') = P x y + P x y'
  smulL : ∀ (c : ℝ) x y, P (c • x) y = c * P x y
  smulR : ∀ (c : ℝ) x y, P x (c • y) = c * P x y
  nondegL : ∀ x, (∀ y, P x y = 0) → x = 0
  nondegR : ∀ y, (∀ x, P x y = 0) → y = 0

structure Setup (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V)) : Prop where
  pair : IsPairing P
  pair₁ : IsPairing P₁
  add : ∀ w w', j (w + w') = j w + j w'
  smul : ∀ (c : ℝ) w, j (c • w) = c • j w
  symp : ∀ w w', omega P (j w) (j w') = omega P₁ w w'
  iso : ∀ l ∈ L, ∀ l' ∈ L, omega P l l' = 0
  orth : ∀ l ∈ L, ∀ w, omega P l (j w) = 0
  max : ∀ v, (∀ l ∈ L, omega P v l = 0) → (∀ w, omega P v (j w) = 0) → v ∈ L

def stdP (P₁ : V₁ → V₁ → ℝ) (k : ℕ) (x y : V₁ × (Fin k → ℝ)) : ℝ := P₁ x.1 y.1 + ∑ i, x.2 i * y.2 i

def jStd (k : ℕ) (w : V₁ × V₁) : (V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ)) := ((w.1, 0), (w.2, 0))


variable (V₁) in
def LStd (k : ℕ) : Set ((V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ))) :=
  {l | ∃ b : Fin k → ℝ, l = ((0, 0), (0, b))}

theorem isPairing_stdP {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : IsPairing (stdP P₁ k) := by
  exact {
    addL x x' y := by
      simp only [stdP, Prod.fst_add, Prod.snd_add, h.addL, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
    addR x y y' := by
      simp only [stdP, Prod.fst_add, Prod.snd_add, h.addR, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
    smulL c x y := by
      simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulL, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      ring
    smulR c x y := by
      simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulR, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
        ← Finset.mul_sum]
      ring
    nondegL x hx := by
      have h1 : x.1 = 0 := h.nondegL _ fun y => by simpa [stdP] using hx (y, 0)
      have h2 : ∑ i, x.2 i * x.2 i = 0 := by
        have := hx (0, x.2)
        simp only [stdP] at this
        rwa [show P₁ x.1 0 = 0 by simpa using h.smulR 0 x.1 0, zero_add] at this
      have h3 : x.2 = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (x.2 i))).1 h2 i (Finset.mem_univ _)
        simpa using this
      exact Prod.ext h1 h3
    nondegR y hy := by
      have h1 : y.1 = 0 := h.nondegR _ fun x => by simpa [stdP] using hy (x, 0)
      have h2 : ∑ i, y.2 i * y.2 i = 0 := by
        have := hy (0, y.2)
        simp only [stdP] at this
        rwa [show P₁ 0 y.1 = 0 by simpa using h.smulL 0 0 y.1, zero_add] at this
      have h3 : y.2 = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y.2 i))).1 h2 i (Finset.mem_univ _)
        simpa using this
      exact Prod.ext h1 h3
  }

theorem IsPairing.zero_left {P : V → V → ℝ} (h : IsPairing P) (y : V) : P 0 y = 0 := by
  simpa using h.smulL 0 0 y

theorem IsPairing.zero_right {P : V → V → ℝ} (h : IsPairing P) (x : V) : P x 0 = 0 := by
  simpa using h.smulR 0 x 0

theorem setup_std {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : Setup (stdP P₁ k) P₁ (jStd k) (LStd V₁ k) := by
  exact {
    pair := isPairing_stdP h k
    pair₁ := h
    add w w' := by simp [jStd]
    smul c w := by simp [jStd]
    symp w w' := by simp [omega, stdP, jStd]
    iso := by
      rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
      simp [omega, stdP, h.zero_left]
    orth := by
      rintro _ ⟨b, rfl⟩ w
      simp [omega, stdP, jStd, h.zero_left, h.zero_right]
    max := by
      rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hL hj
      have e2 : a₂ = 0 := by
        have := hL ((0, 0), (0, a₂)) ⟨a₂, rfl⟩
        simp only [omega, stdP, h.zero_right, h.zero_left, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
          zero_add, sub_zero] at this
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (a₂ i))).1 this i (Finset.mem_univ _)
        simpa using this
      have e1 : a₁ = 0 := h.nondegL _ fun y => by
        have := hj (0, y)
        simpa [omega, stdP, jStd, h.zero_left] using this
      have e3 : b₁ = 0 := h.nondegR _ fun x => by
        have := hj (x, 0)
        simpa [omega, stdP, jStd, h.zero_right] using this
      exact ⟨b₂, by simp [e1, e2, e3]⟩
  }

theorem isPairing_mul : IsPairing (fun x y : ℝ => x * y) := by
  exact {
    addL x x' y := add_mul x x' y
    addR x y y' := mul_add x y y'
    smulL c x y := by simp [mul_assoc]
    smulR c x y := by simp only [smul_eq_mul]; ring
    nondegL x hx := by simpa using hx 1
    nondegR y hy := by simpa using hy 1
  }

end Real

section Adelic

open scoped Matrix
open NumberField GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def trP (κ : Type) [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i)

def locV {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

end Adelic

end GlobalTheory.ArchUniq
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}

def actLin (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) : Matrix α β E ≃ₗ[R] Matrix α β E where
  toFun x := GlobalTheory.WeilM.actAB c p x
  invFun x := (((p.1⁻¹ : GlobalTheory.WeilM.UG c JA) : GL α E) : Matrix α α E) * x *
    (((p.2⁻¹ : GlobalTheory.WeilM.UG c JB) : GL β E) : Matrix β β E)ᵀ
  map_add' x y := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_smul, Matrix.smul_mul]
  left_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  right_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.mul_one]

end Gen

variable (F : Type) [Field F] [NumberField F]

def finE {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F := fun i => (0, y i)

def finE2 {κ : Type} (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (finE F m.1, finE F m.2)

def infE {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), 0)

def mixedSpaceVecPairAsAdeles {κ : Type} (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (infE F v.1, infE F v.2)

def slice {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), y i)

def schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * f (z + v.1)

variable {F}

theorem dot_infE {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F) (z : κ → mixedEmbedding.mixedSpace F) :
    x ⬝ᵥ infE F z = infE F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ⬝ᵥ infE F z := by
  simp only [dotProduct, infE]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Prod.ext ?_ ?_
  · show (x i).1 * _ = _ * _
    rw [RingEquiv.symm_apply_apply]
  · show (x i).2 * 0 = (0 : FiniteAdeleRing (𝓞 F) F) * 0
    rw [mul_zero, mul_zero]

theorem pureA_schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (schrInf F ψ v f) g = GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) (GlobalTheory.WeilM.pureA F f g) := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  rw [dot_infE x v.2, mul_assoc]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + v.1 =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + infE F v.1) i).1 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + v.1 i =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v.1 i))
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
  have h2 : (fun i => (x i).2) = fun i => ((x + infE F v.1) i).2 := by
    funext i
    show (x i).2 = (x i).2 + 0
    rw [add_zero]
  rw [h1, h2]

theorem slice_schr (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    slice F (GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) Φ) y = schrInf F ψ v (slice F Φ y) := by
  funext z
  simp only [slice, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  congr 2
  · congr 1
    refine (dot_infE _ v.2).trans ?_
    congr 2
    funext i
    exact RingEquiv.apply_symm_apply _ _
  · funext i
    refine Prod.ext ?_ ?_
    · exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · exact add_zero _

theorem pureA_add {κ : Type} (f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (f + f') g = GlobalTheory.WeilM.pureA F f g + GlobalTheory.WeilM.pureA F f' g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.add_apply, add_mul]

theorem pureA_smul {κ : Type} (a : ℂ) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (a • f) g = a • GlobalTheory.WeilM.pureA F f g := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem exists_schwartz_slice {κ : Type} [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z, s z = slice F Φ y z := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g y • f, fun z => ?_⟩
    simp only [SchwartzMap.smul_apply, smul_eq_mul, slice, GlobalTheory.WeilM.pureA, RingEquiv.apply_symm_apply]
    exact mul_comm _ _
  | zero => exact ⟨0, fun z => rfl⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hx'
    exact ⟨s + s', fun z => by rw [SchwartzMap.add_apply, hs, hs']; rfl⟩
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨a • s, fun z => by rw [SchwartzMap.smul_apply, hs]; rfl⟩

end GlobalTheory.WeilAdm

end
end
