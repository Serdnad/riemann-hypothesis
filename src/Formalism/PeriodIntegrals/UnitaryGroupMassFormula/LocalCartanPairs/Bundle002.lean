module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.Bundle001
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

section

noncomputable section

namespace PI.SqPair.LCP

open Polynomial IsLocalRing

theorem pair_dichotomy : Dichotomy := by
  intro R _ _ R₀ hfix _ _ _ _ hunr ϖ hϖ
  obtain ⟨θ, hθ⟩ := hunr
  have hst : ∀ r : R₀, star (r : R) = r := fun r => (hfix _).mp r.2
  have unit_of : ∀ {M : Type} [CommMonoid M] (a b : M), a * b = 1 → IsUnit a :=
    fun a b h => ⟨⟨a, b, h, (mul_comm b a).trans h⟩, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ Di : R, (θ - star θ) * Di = 1 := hθ.exists_right_inv
  have hDis : star Di = -Di := by
    have h2 := congrArg star hDi
    simp only [star_mul', star_sub, star_star, star_one] at h2
    linear_combination (-star Di) * hDi + (-Di) * h2
  have coord : ∀ x : R, ∃ a b : R₀, x = a + b * θ := by
    intro x
    have hb : (x - star x) * Di ∈ R₀ := by
      rw [hfix]
      simp only [star_mul', star_sub, star_star, hDis]
      ring
    have ha : x - (x - star x) * Di * θ ∈ R₀ := by
      rw [hfix]
      simp only [star_mul', star_sub, star_star, hDis]
      linear_combination (x - star x) * hDi
    exact ⟨⟨_, ha⟩, ⟨_, hb⟩, by simp⟩
  have hT : θ + star θ ∈ R₀ := by rw [hfix, star_add, star_star, add_comm]
  have hN : θ * star θ ∈ R₀ := by rw [hfix, star_mul', star_star, mul_comm]
  obtain ⟨T, hTc⟩ : ∃ T : R₀, (T : R) = θ + star θ := ⟨⟨_, hT⟩, rfl⟩
  obtain ⟨Nn, hNc⟩ : ∃ Nn : R₀, (Nn : R) = θ * star θ := ⟨⟨_, hN⟩, rfl⟩
  obtain ⟨E, hEc⟩ : ∃ E : R₀, (E : R) = Di ^ 2 :=
    ⟨⟨Di ^ 2, by rw [hfix, star_pow, hDis, neg_sq]⟩, rfl⟩
  have h4 : ((4 : R₀) : R) = 4 := map_ofNat R₀.subtype 4
  have hd : IsUnit (T ^ 2 - 4 * Nn) :=
    unit_of _ E (Subtype.ext (by
      push_cast [hTc, hNc, hEc, h4]
      linear_combination (θ * Di - star θ * Di + 1) * hDi))
  by_cases hs : ∃ c : R₀, ¬ IsUnit (c ^ 2 + T * c + Nn)
  · left
    obtain ⟨c, hc⟩ := hs
    have hu : IsUnit (2 * c + T) := by
      by_contra hn
      have h1 : (2 * c + T) ^ 2 ∈ maximalIdeal R₀ :=
        Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).mpr hn) 2 two_pos
      have h2 : 4 * (c ^ 2 + T * c + Nn) ∈ maximalIdeal R₀ :=
        Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr hc)
      have h3 := Ideal.sub_mem _ h1 h2
      rw [show (2 * c + T) ^ 2 - 4 * (c ^ 2 + T * c + Nn) = T ^ 2 - 4 * Nn by ring] at h3
      exact (mem_maximalIdeal _).mp h3 hd
    obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 + C T * X + C Nn) (by monicity!) c
      (by simpa [mem_maximalIdeal, mem_nonunits_iff] using hc)
      (by rw [show (derivative (X ^ 2 + C T * X + C Nn)).eval c = 2 * c + T by
        simp only [derivative_add, derivative_X_pow, derivative_C_mul_X, derivative_C, eval_add,
          eval_mul, eval_C, eval_pow, eval_X, add_zero] <;> norm_num]; exact hu)
    have hr' : r ^ 2 + T * r + Nn = 0 := by simpa using hr
    have hrR : (r : R) ^ 2 + (θ + star θ) * r + θ * star θ = 0 := by
      have h4 := congrArg (fun z : R₀ => (z : R)) hr'
      push_cast [hTc, hNc] at h4
      exact h4
    refine ⟨(r + θ) * Di, ?_, ?_⟩
    · linear_combination Di ^ 2 * hrR + (r + θ) * Di * hDi
    · simp only [star_mul', star_add, hst, hDis]
      linear_combination hDi
  · right
    push_neg at hs
    have hcoe : ∀ z : R₀, IsUnit z → IsUnit (z : R) := fun z hz => hz.map R₀.subtype
    have key : ∀ a b : R₀, IsUnit a ∨ IsUnit b → IsUnit ((a : R) + b * θ) := by
      intro a b hab
      have hNab : IsUnit (a ^ 2 + T * a * b + Nn * b ^ 2) := by
        rcases em (IsUnit b) with hb | hb
        · obtain ⟨bu, rfl⟩ := hb
          have hbb : (bu : R₀) * ↑bu⁻¹ = 1 := bu.mul_inv
          have e : a ^ 2 + T * a * bu + Nn * (bu : R₀) ^ 2 =
              (bu : R₀) ^ 2 * ((a * ↑bu⁻¹) ^ 2 + T * (a * ↑bu⁻¹) + Nn) := by
            linear_combination (-(a ^ 2) * ((bu : R₀) * ↑bu⁻¹ + 1) - T * a * bu) * hbb
          rw [e]
          exact (bu.isUnit.pow 2).mul (hs _)
        · have ha := hab.resolve_right hb
          by_contra hn
          have h1 : a ^ 2 + T * a * b + Nn * b ^ 2 ∈ maximalIdeal R₀ := (mem_maximalIdeal _).mpr hn
          have h2 : b * (T * a + Nn * b) ∈ maximalIdeal R₀ :=
            Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hb)
          have h3 := Ideal.sub_mem _ h1 h2
          rw [show a ^ 2 + T * a * b + Nn * b ^ 2 - b * (T * a + Nn * b) = a ^ 2 by ring] at h3
          exact (mem_maximalIdeal _).mp h3 (ha.pow 2)
      have e : ((a : R) + b * θ) * (a + b * star θ) = ((a ^ 2 + T * a * b + Nn * b ^ 2 : R₀) : R) := by
        push_cast
        rw [hTc, hNc]
        ring
      exact isUnit_of_mul_isUnit_left (x := (a : R) + b * θ) (y := (a : R) + b * star θ)
        (by rw [e]; exact hcoe _ hNab)
    have hne : (ϖ : R) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have hnu : ¬ IsUnit (ϖ : R) := by
      intro h
      obtain ⟨w, hw⟩ := h.exists_right_inv
      have hw' : (ϖ : R) * star w = 1 := by
        have h5 := congrArg star hw
        rwa [star_mul', hst, star_one] at h5
      have hws : star w = w := by linear_combination w * hw' - star w * hw
      exact hϖ.not_isUnit (unit_of ϖ ⟨w, (hfix w).mpr hws⟩ (Subtype.ext hw))
    have hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u := by
      intro x hx
      obtain ⟨a, b, rfl⟩ := coord x
      by_cases ha : a = 0
      · subst ha
        have hb : b ≠ 0 := by
          rintro rfl
          simp at hx
        obtain ⟨j, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
        refine ⟨j, ((v : R₀) : R) * θ, ?_, ?_⟩
        · simpa using key 0 v (Or.inr v.isUnit)
        · push_cast
          ring
      by_cases hb : b = 0
      · subst hb
        obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
        refine ⟨i, ((u : R₀) : R), hcoe _ u.isUnit, ?_⟩
        push_cast
        ring
      obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      obtain ⟨j, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
      rcases le_total i j with hij | hij
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
        refine ⟨i, ((u : R₀) : R) + ((v * ϖ ^ k : R₀) : R) * θ, key _ _ (Or.inl u.isUnit), ?_⟩
        push_cast
        ring
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
        refine ⟨j, ((u * ϖ ^ k : R₀) : R) + ((v : R₀) : R) * θ, key _ _ (Or.inr v.isUnit), ?_⟩
        push_cast
        ring
    have hdom : IsDomain R := by
      haveI : Nontrivial R := nontrivial_of_ne _ _ hne
      haveI : NoZeroDivisors R := by
        refine ⟨fun {x y} hxy => ?_⟩
        by_contra hc
        push_neg at hc
        obtain ⟨m, u, hu, rfl⟩ := hval x hc.1
        obtain ⟨n, v, hv, rfl⟩ := hval y hc.2
        have h1 : (ϖ : R) ^ (m + n) * (u * v) = 0 := by
          rw [← hxy]
          ring
        have h2 := (hu.mul hv).mul_left_eq_zero.mp h1
        exact pow_ne_zero (m + n) hϖ.ne_zero (Subtype.ext (by push_cast; exact h2))
      exact NoZeroDivisors.to_isDomain R
    exact ⟨hfix, ⟨θ, hθ⟩, ϖ.2, hne, hnu, hdom, hval⟩

end PI.SqPair.LCP
end
end

section

noncomputable section
open Matrix

namespace PI.SqPair.LocCartanPairW

variable {R : Type*} [CommRing R] (σ : R ≃+* R)

theorem cmp_map_mulVec {ι : Type*} [Fintype ι] (h : Matrix ι ι R) (v : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) = h.map σ *ᵥ (fun i => σ (v i)) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem cmp_gram_pull {ι : Type*} [Fintype ι] (A h : Matrix ι ι R) (v w : ι → R) :
    (fun i => σ ((h *ᵥ v) i)) ⬝ᵥ (A *ᵥ (h *ᵥ w)) =
      (fun i => σ (v i)) ⬝ᵥ (((h.map σ)ᵀ * A * h) *ᵥ w) := by
  rw [cmp_map_mulVec σ h v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec _ (h.map σ)ᵀ, Matrix.vecMul_transpose]

theorem cmp_gram_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι R) (a b : R) (v w : ι → R) :
    (fun i => σ ((a • v) i)) ⬝ᵥ (A *ᵥ (b • w)) = σ a * b * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
  have h1 : (fun i => σ ((a • v) i)) = σ a • fun i => σ (v i) := by
    funext i; simp [map_mul]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (fun i => σ a * σ (v i)) ⬝ᵥ (A *ᵥ w) = σ a * ((fun i => σ (v i)) ⬝ᵥ (A *ᵥ w)) := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  have h3 : (σ a • fun i => σ (v i)) = fun i => σ a * σ (v i) := by
    funext i; simp
  rw [h3, h2]; ring

private lemma smulMulVec_lemma {ι : Type*} [Fintype ι] (a : R) (M : Matrix ι ι R) (v : ι → R) :
    (a • M) *ᵥ v = a • (M *ᵥ v) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem cmp_gram_pre [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R)
    (hs : s ≠ 0) (hh : (h.map σ)ᵀ * A * h = s • A') (v w x y : ι → R) (c d t : R)
    (hv : h *ᵥ v = c • x) (hw : h *ᵥ w = d • y)
    (hxy : (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) = s * t) :
    (fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w) = t := by
  have key : s • ((fun i => σ (v i)) ⬝ᵥ (A' *ᵥ w)) =
      (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) * (σ c * d) := by
    rw [← dotProduct_smul, ← smulMulVec_lemma, ← hh, ← cmp_gram_pull σ A h v w, hv, hw,
      cmp_gram_smul σ A c d x y]
    ring
  rw [hxy, smul_eq_mul] at key
  exact mul_left_cancel₀ hs key

theorem cmp_hyp [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R) (hs : s ≠ 0)
    (hh : (h.map σ)ᵀ * A * h = s • A') (c₁ c₂ : R) (hc : σ c₁ * c₂ = s)
    (x₁ y₁ v₁ w₁ : ι → R) (hv : h *ᵥ v₁ = c₁ • x₁) (hw : h *ᵥ w₁ = c₂ • y₁)
    (hxx : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ x₁) = 0) (hyy : (fun i => σ (y₁ i)) ⬝ᵥ (A *ᵥ y₁) = 0)
    (hxy : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ y₁) = 1) :
    (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ v₁) = 0 ∧ (fun i => σ (w₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 0 ∧
      (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 1 := by
  refine ⟨cmp_gram_pre σ A A' h s hs hh v₁ v₁ x₁ x₁ c₁ c₁ 0 hv hv (by rw [hxx]; ring),
    cmp_gram_pre σ A A' h s hs hh w₁ w₁ y₁ y₁ c₂ c₂ 0 hw hw (by rw [hyy]; ring),
    cmp_gram_pre σ A A' h s hs hh v₁ w₁ x₁ y₁ c₁ c₂ 1 hv hw (by rw [hxy, hc]; ring)⟩

private lemma mapMul_lemma_2 {α β γ : Type*} [Fintype β] (X : Matrix α β R) (Y : Matrix β γ R) :
    (X * Y).map σ = X.map σ * Y.map σ := by
  ext i j

  simp [Matrix.mul_apply, map_sum, map_mul]

theorem cmp_split [IsDomain R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (c₁ c₂ : R) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (x y v₁ w₁ : ι → R)
    (hv : h *ᵥ v₁ = c₁ • x) (hw : h *ᵥ w₁ = c₂ • y)
    (u u' : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ A₁' : Matrix κ κ R)
    (huv : u * v = 1) (hvu : v * u = 1)
    (hu0 : ∀ i, u i (.inl 0) = x i) (hu1 : ∀ i, u i (.inl 1) = y i)
    (hu0' : ∀ i, u' i (.inl 0) = v₁ i) (hu1' : ∀ i, u' i (.inl 1) = w₁ i)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks !![0, 1; 1, 0] 0 0 A₁') :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal ![c₁, c₂]) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = v * h * u' := ⟨_, rfl⟩
  have hcol : ∀ b : Fin 2, ∀ i, (h * u') i (.inl b) = ![c₁, c₂] b * u i (.inl b) := by
    rw [Fin.forall_fin_two]
    constructor
    · intro i
      have e := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu0', hu0, e]
    · intro i
      have e := congrFun hw i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu1', hu1, e]
  have hM1 : ∀ a (b : Fin 2), M a (.inl b) =
      ![c₁, c₂] b * (1 : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) a (.inl b) := by
    intro a b
    rw [hMdef, Matrix.mul_assoc, Matrix.mul_apply, ← hvu, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcol b i]
    ring
  have hUM : u * M = h * u' := by
    rw [hMdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]
  have hGram : (M.map σ)ᵀ * fromBlocks !![0, 1; 1, 0] 0 0 A₁ * M =
      s • fromBlocks !![0, 1; 1, 0] 0 0 A₁' := by
    rw [← hG, ← hG']
    calc (M.map σ)ᵀ * ((u.map σ)ᵀ * A * u) * M = ((u * M).map σ)ᵀ * A * (u * M) := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = ((h * u').map σ)ᵀ * A * (h * u') := by rw [hUM]
      _ = (u'.map σ)ᵀ * ((h.map σ)ᵀ * A * h) * u' := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = s • ((u'.map σ)ᵀ * A' * u') := by
          rw [hh, Matrix.mul_smul, Matrix.smul_mul]
  have hMb : M = fromBlocks (diagonal ![c₁, c₂]) M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rw [hM1 (.inl a) b]
      by_cases hab : a = b
      · subst hab
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      · simp [Matrix.one_apply, Matrix.diagonal_apply, hab]
    · simp [Matrix.toBlocks₁₂]
    · rw [hM1 (.inr a) b]
      simp [Matrix.one_apply]
    · simp [Matrix.toBlocks₂₂]
  rw [hMb] at hGram
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul, Matrix.map_zero, map_zero, Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, smul_zero] at hGram
  obtain ⟨-, hQ, -, hS⟩ := Matrix.fromBlocks_inj.mp hGram
  have hc₁' : σ c₁ ≠ 0 := by simpa using hc₁
  have hc₂' : σ c₂ ≠ 0 := by simpa using hc₂
  have hB : M.toBlocks₁₂ = 0 := by
    ext a l
    have e0 := congrFun (congrFun hQ 0) l
    have e1 := congrFun (congrFun hQ 1) l
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hc₁', hc₂'] at e0 e1
    fin_cases a
    · simpa using e1
    · simpa using e0
  refine ⟨M.toBlocks₂₂, ?_, ?_⟩
  · rw [← hMdef]
    nth_rewrite 1 [hMb]
    rw [hB]
  · rw [hB] at hS
    simpa using hS

end PI.SqPair.LocCartanPairW

namespace PI.SqPair.LCP

open PI.SqPair.LocCartanPairW

theorem inert_isLocalRing {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R} {ϖ : R}
    (hI : Inert R₀ ϖ) : IsLocalRing R := by
  haveI := hI.dom
  have key : ∀ x : R, ¬ IsUnit x → ϖ ∣ x := by
    intro x hx
    by_cases h0 : x = 0
    · exact ⟨0, by rw [h0, mul_zero]⟩
    · obtain ⟨m, u, hu, rfl⟩ := hI.val x h0
      cases m with
      | zero => exact absurd (by simpa using hu) hx
      | succ k => exact ⟨ϖ ^ k * u, by ring⟩
  have back : ∀ x : R, ϖ ∣ x → ¬ IsUnit x := by
    rintro x ⟨c, rfl⟩ hu
    exact hI.pi_nonunit (isUnit_of_mul_isUnit_left hu)
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  exact back _ (dvd_add (key a ha) (key b hb))

theorem split_of (hS : SplitOff) : Split := by
  intro R _ _ R₀ ϖ hI κ _ _ A A' h k a hP hak x y v w hxx hyy hxy hv hw
  have := hI.dom
  have : IsLocalRing R := inert_isLocalRing hI
  obtain ⟨⟨hAh, -⟩, ⟨hAh', -⟩, hh⟩ := hP
  have hϖ : star ϖ = ϖ := (hI.fix ϖ).mp hI.pi_mem
  have hcard : Fintype.card κ + 2 = Fintype.card (Fin 2 ⊕ κ) := by
    simp [Fintype.card_sum, add_comm]
  obtain ⟨u, ui, A₁, huv, hvu, hu0, hu1, hG⟩ := hS R (Fin 2 ⊕ κ) κ hcard A hAh x y hxx hyy hxy
  have hs : ϖ ^ (2 * k) ≠ 0 := pow_ne_zero _ hI.pi_ne
  have hc : (starRingAut : R ≃+* R) (ϖ ^ (k - a)) * ϖ ^ (k + a) = ϖ ^ (2 * k) := by
    rw [map_pow, starRingAut_apply, hϖ, ← pow_add]
    congr 1
    omega
  obtain ⟨h1, h2, h3⟩ := cmp_hyp (starRingAut : R ≃+* R) A A' h _ hs hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    hc x y v w hv hw hxx hyy hxy
  obtain ⟨u', ui', A₁', huv', -, hu0', hu1', hG'⟩ :=
    hS R (Fin 2 ⊕ κ) κ hcard A' hAh' v w h1 h2 h3
  obtain ⟨h₂, hM, -⟩ := cmp_split (starRingAut : R ≃+* R) A A' h _ hh (ϖ ^ (k - a)) (ϖ ^ (k + a))
    (pow_ne_zero _ hI.pi_ne) (pow_ne_zero _ hI.pi_ne) x y v w hv hw u u' ui A₁ A₁' huv hvu hu0 hu1
    hu0' hu1' hG hG'
  refine ⟨u, u', A₁, A₁', h₂, ![ϖ ^ (k - a), ϖ ^ (k + a)], isUnit_det_of_right_inverse huv,
    isUnit_det_of_right_inverse huv', hG, hG', ?_⟩
  rw [← hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]

end PI.SqPair.LCP
end
end

section

noncomputable section
open Matrix

namespace PI.SqPair.LCP

section Lin
variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι]

lemma sg_hf_add_left (A : Matrix ι ι R) (x x' y : ι → R) :
    hf A (x + x') y = hf A x y + hf A x' y := by
  simp only [hf, star_add, add_dotProduct]

lemma sg_hf_add_right (A : Matrix ι ι R) (x y y' : ι → R) :
    hf A x (y + y') = hf A x y + hf A x y' := by
  simp only [hf, mulVec_add, dotProduct_add]

lemma sg_hf_smul_left (A : Matrix ι ι R) (c : R) (x y : ι → R) :
    hf A (c • x) y = star c * hf A x y := by
  simp only [hf, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma sg_hf_smul_right (A : Matrix ι ι R) (c : R) (x y : ι → R) :
    hf A x (c • y) = c * hf A x y := by
  simp only [hf, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma sg_hf_star {A : Matrix ι ι R} (hA : Aᴴ = A) (x y : ι → R) :
    star (hf A x y) = hf A y x := by
  conv_rhs => rw [← hA]
  simp only [hf, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, conjTranspose_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Lin

theorem step_of (h5 : Select) (h8 : Plane) (h6 : Split) : Step := by
  intro R _ _ R₀ _ ϖ hin κ _ _ A A' h k hP hnb
  haveI := hin.dom
  obtain ⟨a, x, y, ha0, hak, hxy, ⟨c, hc⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := h5 R R₀ ϖ hin (Fin 2 ⊕ κ) A A' h k hP hnb
  have hA : Aᴴ = A := hP.1.1
  have hsϖ : star ϖ = ϖ := (hin.fix ϖ).1 hin.pi_mem
  have hyx : hf A y x = 1 := by rw [← sg_hf_star hA x y, hxy, star_one]
  have hpow0 : ϖ ^ (2 * a) ≠ 0 := pow_ne_zero _ hin.pi_ne
  have hcR : c ∈ R₀ := by
    rw [hin.fix]
    have h1 := sg_hf_star hA x x
    rw [hc, star_mul, star_pow, hsϖ] at h1
    exact mul_left_cancel₀ hpow0 (by rw [mul_comm, h1])
  have hβR : hf A y y ∈ R₀ := (hin.fix _).2 (sg_hf_star hA y y)
  have hϖm : (⟨ϖ, hin.pi_mem⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hin.pi_nonunit (hu.map R₀.subtype)
  have hmα : ϖ ^ (2 * a) * c ∈ R₀ := R₀.mul_mem (R₀.pow_mem hin.pi_mem _) hcR
  have hαm : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    have e : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) = ⟨ϖ, hin.pi_mem⟩ ^ (2 * a) * ⟨c, hcR⟩ := Subtype.ext (by simp)
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))
  obtain ⟨W, hWdet, hW, s', hs'⟩ := h8 R R₀ ϖ hin ⟨ϖ ^ (2 * a) * c, hmα⟩ ⟨hf A y y, hβR⟩ hαm
  have e00 := congrFun (congrFun hW 0) 0
  have e11 := congrFun (congrFun hW 1) 1
  have e01 := congrFun (congrFun hW 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hyp, conjTranspose_apply] at e00 e11 e01 hs'
  have hk : ϖ ^ (k + a) = ϖ ^ (2 * a) * ϖ ^ (k - a) := by rw [← pow_add]; congr 1; omega

  refine h6 R R₀ ϖ hin κ A A' h k a hP hak (W 0 0 • x + W 1 0 • y) (W 0 1 • x + W 1 1 • y) (W 0 0 • v + (s' * c) • w) ((W 0 1 * ϖ ^ (2 * a)) • v + W 1 1 • w) ?_ ?_ ?_ ?_ ?_
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e00
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e11
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e01
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk, hs']
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk]
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring

end PI.SqPair.LCP
end
end
