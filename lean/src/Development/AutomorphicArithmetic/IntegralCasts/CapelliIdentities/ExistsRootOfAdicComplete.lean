import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HenselSimpleRoot

open Polynomial

namespace UpperTheory.Reformulated.B.AdicCompleteRootExistence

private lemma exists_root_of_adicComplete {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.eval a = 0 ∧ a - a₀ ∈ I :=
  GlobalTheory.exists_simple_root_of_isAdicComplete I f a₀ h₁ h₂

private lemma root_of_local {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {ϖ : R}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (f : R[X]) (a : R) (k : ℕ) (ε : Rˣ)
    (h1 : f.derivative.eval a = ϖ ^ k * ε) (h2 : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b : R, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a := by
  obtain ⟨c, hc⟩ := h2
  obtain ⟨q, hq⟩ := Polynomial.binomExpansion (f.map C) (C a) (C (ϖ ^ (k + 1)) * X)
  have hcomp : eval (C a + C (ϖ ^ (k + 1)) * X) (f.map C) =
      f.comp (C a + C (ϖ ^ (k + 1)) * X) := by
    rw [eval_map]; rfl
  rw [hcomp, eval_map_apply, derivative_map, eval_map_apply, h1, hc] at hq
  let g : R[X] := C c + C (ε : R) * X + C ϖ * q * X ^ 2
  have hgy : ∀ y, g.eval y = c + ε * y + ϖ * (q.eval y * y ^ 2) := by
    intro y; simp only [g, eval_add, eval_mul, eval_C, eval_X, eval_pow]; ring
  have hg'y : ∀ y, g.derivative.eval y =
      ε + ϖ * (q.derivative.eval y * y ^ 2 + q.eval y * (2 * y)) := by
    intro y
    simp only [g, derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
      eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero, eval_one, map_natCast, eval_natCast]
    norm_num
    ring
  set y₀ : R := -((ε⁻¹ : Rˣ) : R) * c with hy₀
  have hεy : (ε : R) * y₀ = -c := by
    rw [hy₀, ← mul_assoc, mul_neg, Units.mul_inv]; ring
  have hroot₀ : g.eval y₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [hgy, add_assoc, ← add_assoc c, hεy, add_neg_cancel, zero_add]
    exact Ideal.mul_mem_right _ _ hϖ
  have hunit : IsUnit (g.derivative.eval y₀) := by
    rw [hg'y]
    by_contra hn
    have hm := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hε : (ε : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right
        (q.derivative.eval y₀ * y₀ ^ 2 + q.eval y₀ * (2 * y₀)) _ hϖ)
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).1 hε ε.isUnit
  obtain ⟨y, hy, -⟩ := exists_root_of_adicComplete (IsLocalRing.maximalIdeal R) g y₀ hroot₀
    (hunit.map _)
  refine ⟨a + ϖ ^ (k + 1) * y, ?_, ⟨y, by ring⟩⟩
  have hev := congrArg (eval y) hq
  simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow] at hev
  rw [hev]
  have : ϖ ^ (2 * k + 1) * g.eval y = 0 := by rw [hy, mul_zero]
  rw [hgy] at this
  linear_combination this

end UpperTheory.Reformulated.B.AdicCompleteRootExistence

theorem UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K]
      {ϖ : ↥(ValuativeRel.valuation K).integer},
      Irreducible ϖ →
        ∀ (f : Polynomial ↥(ValuativeRel.valuation K).integer) (a : ↥(ValuativeRel.valuation K).integer) (k : ℕ)
          (ε : (↥(ValuativeRel.valuation K).integer)ˣ),
          Polynomial.eval a
                ((Polynomial.derivative :
                    Polynomial ↥(ValuativeRel.valuation K).integer → Polynomial ↥(ValuativeRel.valuation K).integer)
                  f) =
              ϖ ^ k * (↑ε : ↥(ValuativeRel.valuation K).integer) →
            ϖ ^ ((2 : ℕ) * k + (1 : ℕ)) ∣ Polynomial.eval a f →
              ∃ (b : ↥(ValuativeRel.valuation K).integer),
                Polynomial.eval b f = (0 : ↥(ValuativeRel.valuation K).integer) ∧ ϖ ^ (k + (1 : ℕ)) ∣ b - a := by
  intro K _ _ _ _ ϖ hϖ f a k ε h1 h2
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact UpperTheory.Reformulated.B.AdicCompleteRootExistence.root_of_local
    ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) f a k ε h1 h2
