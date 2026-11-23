module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.LKDef

section Transport

variable {Γ H V V' : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

private theorem symm_semi {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e) :
    IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [hs]
  simp

private theorem symm_int {ξ : Representation ℂ Γ V} {ξ' : Representation ℂ Γ V'} {e : V ≃+ V'}
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : ∀ g x, e.symm (ξ' g x) = ξ g (e.symm x) := by
  intro g x
  apply e.injective
  rw [hi]
  simp

private theorem forms_left {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (γ : Γ) (g : H) : φ.1 (ι γ * g) = ξ γ (φ.1 g) := φ.2.1 γ g

private theorem forms_right {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    (φ : HeckeTraceForms.forms ι K ξ) (k : H) (hk : k ∈ K) (g : H) : φ.1 (g * k) = φ.1 g := φ.2.2 k hk g

private def fmap (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x))
    (φ : HeckeTraceForms.forms ι K ξ) : HeckeTraceForms.forms ι K ξ' :=
  ⟨fun g => e (φ.1 g), fun γ g => by
      show e (φ.1 (ι γ * g)) = ξ' γ (e (φ.1 g))
      rw [forms_left φ, hi],
    fun k hk g => by
      show e (φ.1 (g * k)) = e (φ.1 g)
      rw [forms_right φ k hk]⟩

private def fequiv (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} (e : V ≃+ V') (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) :
    HeckeTraceForms.forms ι K ξ ≃+ HeckeTraceForms.forms ι K ξ' where
  toFun := fmap ι K e hi
  invFun := fmap ι K e.symm (symm_int hi)
  left_inv φ := by
    apply Subtype.ext; funext g
    exact e.symm_apply_apply _
  right_inv φ := by
    apply Subtype.ext; funext g
    exact e.apply_symm_apply _
  map_add' a b := by
    apply Subtype.ext; funext g
    exact map_add e _ _

private theorem fequiv_semi (ι : Γ →* H) (K : Subgroup H) {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) : IsSemi σ (fequiv ι K e hi) := by
  intro c φ
  apply Subtype.ext; funext g
  exact hs c (φ.1 g)

private theorem transport {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V}
    {ξ' : Representation ℂ Γ V'} {σ : ℂ ≃+* ℂ} {e : V ≃+ V'} (hs : IsSemi σ e)
    (hi : ∀ g x, e (ξ g x) = ξ' g (e x)) {F : H → ℂ}
    {T : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (hT : HeckeTraceForms.IsHecke ι K ξ F T) :
    ∃ T' : HeckeTraceForms.forms ι K ξ' →ₗ[ℂ] HeckeTraceForms.forms ι K ξ',
      HeckeTraceForms.IsHecke ι K ξ' (fun h => σ (F h)) T' ∧
        ∀ x, fequiv ι K e hi (T x) = T' (fequiv ι K e hi x) := by
  have hsym := symm_semi (fequiv_semi ι K hs hi)
  refine ⟨{ toFun := fun ψ => fequiv ι K e hi (T ((fequiv ι K e hi).symm ψ))
            map_add' := fun a b => by simp
            map_smul' := fun c ψ => by
              rw [hsym c ψ, map_smul, fequiv_semi ι K hs hi]
              simp }, ?_, ?_⟩
  · intro ψ g
    change e ((T ((fequiv ι K e hi).symm ψ)).1 g) = _
    rw [hT, AddEquiv.map_finsum]
    refine finsum_congr fun q => ?_
    rw [hs]
    congr 1
    exact e.apply_symm_apply _
  · intro x
    change fequiv ι K e hi (T x) = fequiv ι K e hi (T ((fequiv ι K e hi).symm (fequiv ι K e hi x)))
    rw [AddEquiv.symm_apply_apply]

private theorem hecke_unique {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {F : H → ℂ}
    {T T' : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] HeckeTraceForms.forms ι K ξ} (h : HeckeTraceForms.IsHecke ι K ξ F T)
    (h' : HeckeTraceForms.IsHecke ι K ξ F T') : T = T' := by
  apply LinearMap.ext; intro φ
  apply Subtype.ext; funext g
  rw [h φ g, h' φ g]

end Transport

theorem heckeTraceSemi_of :
    TraceSemi → HeckeTraceSemi := by
  intro hTr σ Γ H V V' _ _ _ _ _ _ ξ ξ' e hs hi ι K F
  by_cases h : ∃ T, HeckeTraceForms.IsHecke ι K ξ F T
  · obtain ⟨T', hT', hint⟩ := transport (ι := ι) (K := K) hs hi h.choose_spec
    have h' : ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := ⟨T', hT'⟩
    have hc : h'.choose = T' := hecke_unique h'.choose_spec hT'
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dite_eq_left h, dite_eq_left h', hc]
    exact hTr σ _ _ (fequiv ι K e hi) (fequiv_semi ι K hs hi) _ _ hint
  · have h' : ¬ ∃ T, HeckeTraceForms.IsHecke ι K ξ' (fun x => σ (F x)) T := by
      rintro ⟨T', hT'⟩
      obtain ⟨T, hT, -⟩ := transport (ι := ι) (K := K) (symm_semi hs) (symm_int hi) hT'
      refine h ⟨T, ?_⟩
      simpa only [RingEquiv.symm_apply_apply] using hT
    rw [HeckeTraceForms.heckeTrace, HeckeTraceForms.heckeTrace, dite_eq_right h, dite_eq_right h', map_zero]

end UpperTheory.Gal.LocalSmoothExtension
end

section

set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

theorem coeffOcc_of : CoeffOcc := by
  intro d n t c h hinj hc hEq i
  set P : ℂ[X] := ∑ a ∈ Finset.range (d + 1), C ((-1) ^ a * t a) * X ^ a with hPdef
  set Q : ℂ[X] := ∑ j, C c * X ^ (h j) with hQdef
  have hPQ : P = Q := by
    apply Polynomial.funext
    intro y
    simp only [hPdef, hQdef, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← Finset.mul_sum, ← hEq y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [neg_pow]
    ring
  have hQ : Q.coeff (h i) = c := by
    simp only [hQdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (fun e => hji (hinj e).symm), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hP : P.coeff (h i) = if h i ∈ Finset.range (d + 1) then (-1) ^ (h i) * t (h i) else 0 := by
    simp only [hPdef, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  intro ht
  rw [hPQ, hQ] at hP
  split_ifs at hP with hlt
  · rw [ht, mul_zero] at hP
    exact hc hP
  · exact hc hP

end UpperTheory.Gal.LocalSmoothExtension
end

section

set_option autoImplicit false

namespace UpperTheory.Gal.LocalSmoothExtension

theorem hExpInj_of : HExpInj := by
  intro F _ _ n t₀ ε lam h hanti hh i k hik
  rcases hh with ⟨m, -, hh⟩ | ⟨m, -, hh⟩
  · rw [hh i, hh k] at hik
    have hi := i.isLt
    have hk := k.isLt
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti t₀ hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti t₀ hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega
  · rw [hh i, hh k] at hik
    have si : ∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) i =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have sk : ∑ j ∈ Finset.univ.erase k, lam (NumberField.ComplexEmbedding.conjugate t₀) j +
        lam (NumberField.ComplexEmbedding.conjugate t₀) k =
        ∑ j, lam (NumberField.ComplexEmbedding.conjugate t₀) j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ k)
    rcases lt_trichotomy i k with hlt | heq | hgt
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hlt.le
      have hlt' : (i : ℕ) < k := hlt
      exfalso
      omega
    · exact heq
    · have hle := hanti (NumberField.ComplexEmbedding.conjugate t₀) hgt.le
      have hgt' : (k : ℕ) < i := hgt
      exfalso
      omega

end UpperTheory.Gal.LocalSmoothExtension
end

section

set_option autoImplicit false

noncomputable section

open Matrix Polynomial
open UpperTheory.Gal.W2 (lefTerm)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem lefSum_of : LefSum := by
  intro d A y
  set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp
  have hdeg : p.natDegree < d + 1 := by
    have h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) =
        (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C := by
      rw [Matrix.map_one C (map_zero _) (map_one _), add_comm]
    have hle := natDegree_det_X_add_C_le A 1
    rw [← h1, Fintype.card_fin] at hle
    exact Nat.lt_succ_of_le hle
  have hev : p.eval (-y) = (1 - y • A).det := by
    rw [hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp <;> ring
  unfold lefTerm
  rw [← hev, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UpperTheory.Gal.LocalSmoothExtension
end
end
