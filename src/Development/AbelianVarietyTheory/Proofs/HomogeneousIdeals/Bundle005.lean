module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle001
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Polynomial.CauchyBound
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
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma

noncomputable section

namespace GlobalTheory

local notation "𝕢" => Periodic.qParam

def modularJ (τ : ℍ) : ℂ := E₄ τ ^ 3 / discriminant τ

lemma modularJ_def (τ : ℍ) : modularJ τ = E₄ τ ^ 3 / discriminant τ := rfl

lemma modularJ_smul (γ : SL(2, ℤ)) (τ : ℍ) : modularJ (γ • τ) = modularJ τ := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h1 := SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have h2 := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  have h3 := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have h4 := discriminant_ne_zero τ
  change E₄ ((γ : GL (Fin 2) ℝ) • τ) ^ 3 / CuspForm.discriminant ((γ : GL (Fin 2) ℝ) • τ) =
    E₄ τ ^ 3 / CuspForm.discriminant τ
  rw [h1, h2]
  change _ / (_ * discriminant τ) = _ / discriminant τ
  field_simp

lemma mdifferentiable_modularJ : MDiff modularJ :=
  (E₄.holo'.pow 3).div CuspForm.discriminant.holo' discriminant_ne_zero

lemma periodic_comp_ofComplex_of_vadd {f : ℍ → ℂ} {h : ℝ} (hf : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) :
    Periodic (f ∘ ofComplex) (h : ℂ) := by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert! hf ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have : im (w + h) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

lemma qParam_one_vadd (τ : ℍ) : 𝕢 1 ((1 : ℝ) +ᵥ τ : ℍ) = 𝕢 1 τ := by
  simp [Periodic.qParam, mul_add, Complex.exp_add]

lemma hasQExpansion_qParam_pow_mul {f : ℍ → ℂ} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hhol : MDiff f) {m : ℕ} (hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ m * f τ) :
    HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * f τ) (qExpansion 1 fun τ ↦ 𝕢 1 τ ^ m * f τ) := by
  refine .of_periodic one_pos (periodic_comp_ofComplex_of_vadd fun τ ↦ ?_) ?_ hbdd
  · rw [qParam_one_vadd, ← modular_T_smul, hinv]
  · exact (((HasQExpansion.qParam 1).mdifferentiable one_pos).pow m).mul hhol

lemma twelve_dvd_sigma (n : ℕ) : (12 : ℤ) ∣ 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) := by
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  have : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp
  push_cast
  exact this d

lemma qExpansion_E₄ : qExpansion 1 E₄ =
    PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * PowerSeries.mk fun n ↦ (σ 3 n : ℤ)) := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
  rw [coeff_map, show (240 : ℤ⟦X⟧) = C 240 from rfl, map_add (f := _), coeff_C_mul, coeff_one]
  split_ifs with hm
  · simp [hm]
  · simp; norm_num

lemma qExpansion_E₆ : qExpansion 1 E₆ =
    PowerSeries.map (Int.castRingHom ℂ) (1 - 504 * PowerSeries.mk fun n ↦ (σ 5 n : ℤ)) := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]
  rw [coeff_map, show (504 : ℤ⟦X⟧) = C 504 from rfl, map_sub, coeff_C_mul, coeff_one]
  split_ifs with hm
  · simp [hm]
  · simp; norm_num

lemma exists_hasQExpansion_discriminant : ∃ U : ℤ⟦X⟧, coeff 0 U = 1 ∧
    HasQExpansion 1 discriminant (X * PowerSeries.map (Int.castRingHom ℂ) U) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (σ 3 n : ℤ) with hA
  set B : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (σ 5 n : ℤ) with hB
  obtain ⟨S, hS⟩ : ∃ S : ℤ⟦X⟧, 5 * A + 7 * B = 12 * S := by
    choose c hc using twelve_dvd_sigma
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [show (5 : ℤ⟦X⟧) = C 5 from rfl, show (7 : ℤ⟦X⟧) = C 7 from rfl,
      show (12 : ℤ⟦X⟧) = C 12 from rfl, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul]
    simpa [hA, hB] using hc n
  set D : ℤ⟦X⟧ := S + 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2 with hD
  have hD' : (1 + 240 * A) ^ 3 - (1 - 504 * B) ^ 2 = 1728 * D := by
    rw [hD]; linear_combination 144 * hS
  have h1 := (HasQExpansion.const 1 (1728⁻¹ : ℂ)).mul
    (((hasQExpansion_modularForm E₄).pow 3).sub ((hasQExpansion_modularForm E₆).pow 2))
  rw [qExpansion_E₄, qExpansion_E₆, ← map_pow, ← map_pow, ← map_sub, hD', map_mul, ← mul_assoc,
    show (C (1728⁻¹ : ℂ) * PowerSeries.map (Int.castRingHom ℂ) 1728 : ℂ⟦X⟧) = 1 by
      rw [show (1728 : ℤ⟦X⟧) = C 1728 from rfl, map_C, ← map_mul]; simp, one_mul] at h1
  have h2 : HasQExpansion 1 discriminant (PowerSeries.map (Int.castRingHom ℂ) D) :=
    h1.congr fun τ ↦ by rw [discriminant_eq_E₄_cube_sub_E₆_sq]; ring
  have h3 : HasQExpansion 1 discriminant (qExpansion 1 discriminant) := fun τ ↦
    ModularForm.hasSum_qExpansion CuspForm.discriminant one_pos one_mem_strictPeriods_SL τ
  have h4 := h2.unique one_pos h3
  have h5 : coeff 0 D = 0 := by
    have := CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
    rw [CuspForm.coe_discriminant, ← h4, coeff_map] at this
    simpa using this
  have h6 : coeff 1 D = 1 := by
    have := discriminant_qExpansion_coeff_one
    rw [← h4, coeff_map] at this
    simpa using this
  obtain ⟨U, hU⟩ : X ∣ D := X_dvd_iff.mpr (by simpa using h5)
  refine ⟨U, by rw [← h6, hU, coeff_succ_X_mul], ?_⟩
  rwa [hU, map_mul, map_X] at h2

theorem exists_hasQExpansion_modularJ : ∃ J : ℤ⟦X⟧, coeff 0 J = 1 ∧
    HasQExpansion 1 (fun τ ↦ 𝕢 1 τ * modularJ τ) (PowerSeries.map (Int.castRingHom ℂ) J) := by
  obtain ⟨U, hU0, hU⟩ := exists_hasQExpansion_discriminant
  have hq (τ : ℍ) : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
  have hu : HasQExpansion 1 (fun τ ↦ discriminant τ / 𝕢 1 τ)
      (PowerSeries.map (Int.castRingHom ℂ) U) :=
    .of_qParam_mul (hU.congr fun τ ↦ by field_simp [hq τ])
  have hE := (hasQExpansion_modularForm E₄).pow 3
  have heq (τ : ℍ) : 𝕢 1 τ ^ 1 * modularJ τ = E₄ τ ^ 3 / (discriminant τ / 𝕢 1 τ) := by
    rw [modularJ_def]; field_simp
  have hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * modularJ τ := by
    simp_rw [heq]
    exact ((hE.tendsto one_pos).div (hu.tendsto one_pos) (by simp [hU0])).isBigO_one ℝ
  have h1 := hasQExpansion_qParam_pow_mul modularJ_smul mdifferentiable_modularJ hbdd
  set φ := qExpansion 1 fun τ : ℍ ↦ 𝕢 1 τ ^ 1 * modularJ τ
  have h2 := (h1.mul hu).unique one_pos (hE.congr fun τ ↦ by
    rw [modularJ_def]; field_simp [hq τ, discriminant_ne_zero τ])
  rw [qExpansion_E₄, ← map_pow] at h2
  set E : ℤ⟦X⟧ := (1 + 240 * PowerSeries.mk fun n ↦ (σ 3 n : ℤ)) ^ 3 with hE'
  have hUV : U * U.invOfUnit 1 = 1 := mul_invOfUnit U 1 (by simpa using hU0)
  refine ⟨E * U.invOfUnit 1, by simp [hE'], ?_⟩
  rw [map_mul, ← h2, mul_assoc, ← map_mul, hUV, map_one, mul_one]
  simpa using h1

theorem exists_polynomial_modularJ_of_hasQExpansion (A : AddSubgroup ℂ) {m : ℕ} {f : ℍ → ℂ}
    {φ : ℂ⟦X⟧} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hf : HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * f τ) φ) (hA : ∀ k, coeff k φ ∈ A) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ P.coeff m = coeff 0 φ ∧ (∀ i, P.coeff i ∈ A) ∧
      ∀ τ, f τ = P.eval (modularJ τ) := by
  induction m generalizing f φ with
  | zero =>
    simp only [pow_zero, one_mul] at hf
    have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
      ext τ; simpa [SL_slash_apply] using hinv γ τ
    let F : ModularForm 𝒮ℒ 0 :=
      { toFun := f
        slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
        holo' := hf.mdifferentiable one_pos
        bdd_at_cusps' := fun {c} hc ↦ by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [hs γ]
          exact hf.isBoundedAtImInfty one_pos }
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
    have hc' : f = fun _ ↦ c := hc
    have h0 : φ = C c := hf.unique one_pos (hc' ▸ HasQExpansion.const 1 c)
    have h1 : c ∈ A := by simpa [h0] using hA 0
    refine ⟨Polynomial.C c, by simp, by simp [h0], fun i ↦ ?_, fun τ ↦ by simp [hc']⟩
    rw [Polynomial.coeff_C]
    split_ifs
    exacts [h1, A.zero_mem]
  | succ m ih =>
    obtain ⟨J, hJ0, hJ⟩ := exists_hasQExpansion_modularJ
    set c := coeff 0 φ with hc
    have h1 := hf.sub ((HasQExpansion.const 1 c).mul (hJ.pow (m + 1)))
    set ψ := φ - C c * PowerSeries.map (Int.castRingHom ℂ) J ^ (m + 1) with hψ
    have hψA (k : ℕ) : coeff k ψ ∈ A := by
      rw [hψ, map_sub, coeff_C_mul, ← map_pow, coeff_map]
      refine A.sub_mem (hA k) ?_
      simpa [mul_comm, hc] using A.zsmul_mem (hA 0) (coeff k (J ^ (m + 1)))
    obtain ⟨χ, hχ⟩ : X ∣ ψ := X_dvd_iff.mpr (by
      have : constantCoeff (PowerSeries.map (Int.castRingHom ℂ) J) = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hJ0, map_one]
      simp [hψ, hc, this])
    have h2 : HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * (f τ - c * modularJ τ ^ (m + 1))) χ :=
      .of_qParam_mul (hχ ▸ h1.congr fun τ ↦ by ring)
    obtain ⟨P, hP1, -, hP3, hP4⟩ := ih (fun γ τ ↦ by rw [hinv, modularJ_smul]) h2
      (fun k ↦ by simpa [hχ, coeff_succ_X_mul] using hψA (k + 1))
    refine ⟨P + Polynomial.monomial (m + 1) c, ?_, ?_, fun i ↦ ?_, fun τ ↦ ?_⟩
    · exact Polynomial.natDegree_add_le_of_degree_le (by omega)
        (Polynomial.natDegree_monomial_le _)
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hP1)]
    · rw [Polynomial.coeff_add, Polynomial.coeff_monomial_apply]
      refine A.add_mem (hP3 i) ?_
      split_ifs
      exacts [hA 0, A.zero_mem]
    · simp [← hP4]

end GlobalTheory
end
end

section

namespace GlobalTheory.AffinePoints

open Topology Filter Set Polynomial

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

theorem exists_comap_eq_of_isIntegral {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (p : A →ₐ[K] K) (hp : ∀ a, φ a = 0 → p a = 0) : ∃ q : B →ₐ[K] K, comap φ q = p := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  have hsurj : Function.Surjective p := fun c => ⟨algebraMap K A c, by simp⟩
  haveI : (RingHom.ker p).IsMaximal := RingHom.ker_isMaximal_of_surjective p hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) (RingHom.ker p) hp
  have hcomp : ∀ a, Ideal.Quotient.mk Q (φ a) = algebraMap K (B ⧸ Q) (p a) := by
    intro a
    have : a - algebraMap K A (p a) ∈ Q.comap (algebraMap A B) := by
      rw [← Ideal.under_def, hQp]
      simp [RingHom.mem_ker]
    have h2 : φ (a - algebraMap K A (p a)) ∈ Q := this
    rw [map_sub, AlgHom.commutes] at h2
    exact Ideal.Quotient.eq.2 h2
  haveI : Algebra.IsIntegral K (B ⧸ Q) := ⟨fun x => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨h, hm, hb⟩ := hφ b
    refine ⟨h.map p.toRingHom, hm.map _, ?_⟩
    have : (algebraMap K (B ⧸ Q)).comp p.toRingHom = (Ideal.Quotient.mk Q).comp φ.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [eval₂_map, this, ← hom_eval₂, hb, map_zero]⟩
  let e : K ≃ₐ[K] (B ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ Q))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K Q), ?_⟩
  ext a
  change e.symm (Ideal.Quotient.mk Q (φ a)) = p a
  rw [hcomp, AlgEquiv.commutes]; rfl

theorem finite_fiber_comap {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [Field K] [Algebra R K] (φ : A →ₐ[R] B) (hφ : φ.Finite) (p : A →ₐ[R] K) :
    ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}).Finite := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A K := p.toRingHom.toAlgebra
  haveI : Module.Finite A B := hφ
  let F : ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}) → (B →ₐ[A] K) := fun q =>
    { q.1.toRingHom with commutes' := fun a => DFunLike.congr_fun q.2 a }
  refine Set.finite_coe_iff.1 (Finite.of_injective F fun q q' h => ?_)
  ext b
  exact DFunLike.congr_fun h b

theorem norm_le_of_isRoot_monic {h : ℂ[X]} (hm : h.Monic) {t : ℂ} (ht : h.IsRoot t) :
    ‖t‖ ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖ + 1 := by
  have h1 := ht.norm_lt_cauchyBound hm.ne_zero
  have h2 : h.cauchyBound ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖₊ + 1 := by
    simp only [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, add_le_add_iff_right]
    exact Finset.sup_le fun i hi =>
      Finset.single_le_sum (f := fun i => ‖h.coeff i‖₊) (fun _ _ => zero_le) hi
  have h3 := h1.le.trans h2
  simpa [NNReal.coe_sum] using NNReal.coe_le_coe.2 h3

theorem isProperMap_comap (φ : A →ₐ[ℂ] B) (hφ : φ.toRingHom.IsIntegral) :
    IsProperMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by
  refine isProperMap_iff_ultrafilter_of_t2.2 ⟨continuous_comap φ, fun 𝒰 p hp => ?_⟩
  have hlim : ∀ b : B, ∃ t : ℂ, Tendsto (fun q : B →ₐ[ℂ] ℂ => q b) 𝒰 (𝓝 t) := by
    intro b
    obtain ⟨h, hm, hb⟩ := hφ b
    let M : (A →ₐ[ℂ] ℂ) → ℝ := fun r => ∑ i ∈ Finset.range h.natDegree, ‖r (h.coeff i)‖ + 1
    have hM : Continuous M :=
      (continuous_finsetSum _ fun i _ => (continuous_eval _).norm).add continuous_const
    have hbd : ∀ q : B →ₐ[ℂ] ℂ, ‖q b‖ ≤ M (comap φ q) := by
      intro q
      have hr : (h.map (comap φ q).toRingHom).IsRoot (q b) := by
        have : (comap φ q).toRingHom = q.toRingHom.comp φ.toRingHom := rfl
        rw [IsRoot, eval_map, this]
        change eval₂ _ (q.toRingHom b) h = 0
        rw [← hom_eval₂, hb, map_zero]
      have := norm_le_of_isRoot_monic (hm.map _) hr
      simpa [hm.natDegree_map, M] using this
    have hev : ∀ᶠ q in (𝒰 : Filter (B →ₐ[ℂ] ℂ)), q b ∈ Metric.closedBall (0 : ℂ) (M p + 1) := by
      filter_upwards [((hM.tendsto p).comp hp).eventually (gt_mem_nhds (lt_add_one (M p)))]
        with q hq
      exact mem_closedBall_zero_iff.2 ((hbd q).trans hq.le)
    obtain ⟨t, -, ht⟩ := (isCompact_closedBall (0 : ℂ) (M p + 1)).ultrafilter_le_nhds
      (𝒰.map fun q : B →ₐ[ℂ] ℂ => q b) (le_principal_iff.2 hev)
    exact ⟨t, ht⟩
  choose u hu using hlim
  have hu' : Tendsto (fun q : B →ₐ[ℂ] ℂ => (q : B → ℂ)) 𝒰 (𝓝 u) := tendsto_pi_nhds.2 hu
  obtain ⟨q, hq⟩ := (isClosedEmbedding_coe (R := ℂ) (A := B) (C := ℂ)).isClosed_range.mem_of_tendsto
    hu' (Eventually.of_forall fun q => ⟨q, rfl⟩)
  refine ⟨q, ?_⟩
  rw [← tendsto_id', tendsto_nhds_iff]
  intro b
  rw [show q b = u b from congrFun hq b]
  exact hu b

theorem exists_isRoot_norm_lt {h : ℂ[X]} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t, h.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt ..)

theorem exists_apply_eq_zero_and_eq_one {K : Type*} [Field K] [Algebra K A] (p : A →ₐ[K] K)
    {S : Set (A →ₐ[K] K)} (hS : S.Finite) (hp : p ∉ S) :
    ∃ a : A, p a = 0 ∧ ∀ q ∈ S, q a = 1 := by
  classical
  have : ∀ q ∈ S, ∃ e : A, p e = 1 ∧ q e = 0 := by
    intro q hq
    obtain ⟨b, hb⟩ : ∃ b, p b ≠ q b := by
      by_contra h
      push Not at h
      exact hp (by rwa [AlgHom.ext h])
    refine ⟨(p b - q b)⁻¹ • (b - algebraMap K A (q b)), ?_, by simp⟩
    simp [inv_mul_cancel₀ (sub_ne_zero.2 hb)]
  choose! e he using this
  refine ⟨1 - ∏ q ∈ hS.toFinset, e q, ?_, fun q hq => ?_⟩
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_one fun q hq => (he q (by simpa using hq)).1,
      sub_self]
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_zero (i := q) (by simpa using hq) (he q hq).2,
      sub_zero]

theorem isOpenMap_comap [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] (φ : A →ₐ[ℂ] B)
    (hφ : φ.Finite) (hinj : Function.Injective φ) :
    IsOpenMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by
  have hint : φ.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hφ
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, hpU, rfl⟩
  obtain ⟨a, hpa, ha⟩ := exists_apply_eq_zero_and_eq_one p
    ((finite_fiber_comap φ hφ (comap φ p)).diff (t := U)) (fun h => h.2 hpU)
  have hai : IsIntegral A a := hint a
  have hm := minpoly.monic hai
  have hK : IsClosed (comap φ '' (Uᶜ ∩ {q : B →ₐ[ℂ] ℂ | ‖q a‖ ≤ 1 / 2})) :=
    (isProperMap_comap φ hint).isClosedMap _ (hU.isClosed_compl.inter
      (isClosed_le (continuous_eval a).norm continuous_const))
  have hW : IsOpen {r : A →ₐ[ℂ] ℂ |
      ‖r ((minpoly A a).coeff 0)‖ < (1 / 2) ^ (minpoly A a).natDegree} :=
    isOpen_lt (continuous_eval _).norm continuous_const
  refine mem_of_superset ((hK.isOpen_compl.inter hW).mem_nhds ⟨?_, ?_⟩) ?_
  · rintro ⟨q, ⟨hqU, hqa⟩, hq⟩
    rw [mem_setOf_eq, ha q ⟨hq, hqU⟩] at hqa
    norm_num at hqa
  · have h1 : p (φ ((minpoly A a).coeff 0)) = 0 := by
      have h2 : p.toRingHom (eval₂ φ.toRingHom a (minpoly A a)) = 0 := by
        rw [show eval₂ φ.toRingHom a (minpoly A a) = 0 from minpoly.aeval A a, map_zero]
      rw [hom_eval₂, show p.toRingHom a = 0 from hpa, eval₂_at_zero] at h2
      exact h2
    rw [mem_setOf_eq, comap_apply, h1, norm_zero]
    positivity
  · rintro r ⟨hrK, hrW⟩
    obtain ⟨t, ht, htn⟩ := exists_isRoot_norm_lt (h := (minpoly A a).map r.toRingHom) (hm.map _)
      (ε := 1 / 2) (by norm_num) (by simpa [hm.natDegree_map] using hrW)
    let χ : A[X] →ₐ[ℂ] B := (aeval a).restrictScalars ℂ
    have hχ : χ.toRingHom.IsIntegral := by
      refine RingHom.IsIntegral.tower_top (C : A →+* A[X]) χ.toRingHom ?_
      convert hint
      ext x
      simp [χ, RingHom.algebraMap_toAlgebra]
    obtain ⟨q, hq⟩ := exists_comap_eq_of_isIntegral χ hχ (aevalTower r t) fun f hf => by
      obtain ⟨k, rfl⟩ := minpoly.isIntegrallyClosed_dvd hai (p := f) hf
      have : aevalTower r t (minpoly A a) = 0 := by
        rw [IsRoot, eval_map] at ht
        exact ht
      rw [map_mul, this, zero_mul]
    have hqr : comap φ q = r := by
      ext x
      simpa [χ, RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hq (C x)
    have hqa : q a = t := by simpa [χ] using DFunLike.congr_fun hq X
    refine ⟨q, ?_, hqr⟩
    by_contra hqU
    exact hrK ⟨q, ⟨hqU, by rw [mem_setOf_eq, hqa]; exact htn.le⟩, hqr⟩

end GlobalTheory.AffinePoints
end

section

open TensorProduct CategoryTheory AlgebraicGeometry

universe u

namespace GlobalTheory.GaloisDescent

section Instances

variable (K L G V : Type*) [CommSemiring K] [Semiring L] [Algebra K L] [Monoid G]
  [MulSemiringAction G L]

end Instances

section Group

variable {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]

end Group

section AlgEquiv

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable [Algebra K ℂ]

theorem complex_stable_iff_exists_baseChange {V : Type*} [AddCommGroup V]
    [Module K V] (W : Submodule ℂ (ℂ ⊗[K] V)) :
    (∀ σ : ℂ ≃ₐ[K] ℂ, ∀ w ∈ W, σ.toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange ℂ = W :=
  stable_iff_exists_baseChange (fun σ : ℂ ≃ₐ[K] ℂ => σ.toAlgHom)
    complex_mem_range_of_forall_algEquiv W

end AlgEquiv

end GlobalTheory.GaloisDescent
end
