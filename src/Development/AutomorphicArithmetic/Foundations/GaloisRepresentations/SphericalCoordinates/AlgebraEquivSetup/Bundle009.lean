module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015

@[expose] public section

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPerfCof :
    PerfCof := by
  intro E _ _ _ A
  classical
  have hδ : A.δ ≠ 0 := by
    intro h
    have h2 := A.δ_sign A.τ₀ rfl
    rw [h, map_zero, Complex.zero_im] at h2
    exact lt_irrefl _ h2
  let Ψ : E →ₗ[ℚ] Module.Dual ℚ E :=
    ((LinearMap.mul ℚ E).compr₂ (Algebra.trace ℚ E)) ∘ₗ LinearMap.mulLeft ℚ A.δ
  have hΨ : ∀ x z, Ψ x z = Algebra.trace ℚ E (A.δ * x * z) := fun x z => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 := LinearMap.congr_fun hx (A.δ * x)⁻¹
    rw [hΨ, mul_inv_cancel₀ (mul_ne_zero hδ hx0), LinearMap.zero_apply,
      show (1 : E) = algebraMap ℚ E 1 from (map_one _).symm, Algebra.trace_algebraMap] at h1
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    simp at h1
    omega
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj
  let bQ := NumberField.integralBasis E
  let b := NumberField.RingOfIntegers.basis E
  choose ξ hξ using fun i => hsurj (bQ.coord i)
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image ξ)
  have hint : ∀ i, ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = y • ξ i := fun i =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hyint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  choose w hw using hint
  let η : _ → 𝓞 E := fun i => (y : 𝓞 E) * w i
  have hηc : ∀ i, algebraMap (𝓞 E) E (η i) = (y : E) * ((y : E) * ξ i) := by
    intro i
    change algebraMap (𝓞 E) E ((y : 𝓞 E) * w i) = _
    rw [map_mul, map_intCast, hw i, zsmul_eq_mul]
  have hDz : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
  have hDpos : 0 < y.natAbs * y.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0)
  have key : ∀ i z, A.trd (η i * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * b.coord i z := by
    intro i
    have hlin : A.trd ∘ₗ LinearMap.mulLeft ℤ (η i) = ((y.natAbs * y.natAbs : ℕ) : ℤ) • b.coord i := by
      refine b.ext fun j => ?_
      apply Int.cast_injective (α := ℚ)
      have hb : bQ j = algebraMap (𝓞 E) E (b j) := NumberField.integralBasis_apply E j
      have hc : (((η i * b j : 𝓞 E)) : E) = (y : E) * ((y : E) * ξ i) * bQ j := by
        change algebraMap (𝓞 E) E (η i * b j) = _
        rw [map_mul, hηc, hb]
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, A.trd_spec, hc, LinearMap.smul_apply,
        smul_eq_mul, hDz,
        show A.δ * ((y : E) * ((y : E) * ξ i) * bQ j) = ((y * y : ℤ) : ℚ) • (A.δ * ξ i * bQ j) by
          rw [Algebra.smul_def, map_intCast]
          push_cast
          ring,
        map_smul, smul_eq_mul, ← hΨ, hξ]
      rw [Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Module.Basis.repr_self]
      rcases eq_or_ne j i with h | h
      · subst h
        simp
      · simp [Finsupp.single_apply, h]
    intro z
    exact LinearMap.congr_fun hlin z
  have hdual : ∀ f : 𝓞 E →ₗ[ℤ] ℤ, ∃ x : 𝓞 E, ∀ z,
      A.trd (x * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * f z := by
    intro f
    refine ⟨∑ i, f (b i) • η i, fun z => ?_⟩
    conv_rhs => rw [← b.sum_dual_apply_smul_coord f]

    rw [Finset.sum_mul, map_sum, LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, key, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hc0 : A.c ≠ 0 := by
    intro h
    exact A.c_ne (by rw [h]; rfl)
  have hN0 : 0 < Ideal.absNorm (Ideal.span {A.c}) := by
    refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {A.c}))
  refine ⟨y.natAbs * y.natAbs * Ideal.absNorm (Ideal.span {A.c}), Nat.mul_pos hDpos hN0,
    fun q hq => ⟨_, hq, fun f => ?_, ⟨c' * ((y.natAbs * y.natAbs : ℕ) : 𝓞 E), ?_⟩⟩⟩
  · obtain ⟨x, hx⟩ := hdual ((Ideal.absNorm (Ideal.span {A.c}) : ℤ) • f)
    refine ⟨x, fun z => ?_⟩
    rw [hx, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  · rw [← mul_assoc, ← hc']
    push_cast
    ring
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma beta_baseChange {E : Type} [Field E] [NumberField E] {n : ℕ}
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) (b : 𝓞 E)
    (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    β ((DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ z) = (b : E) • β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  | tmul q v =>
    have h1 : ∀ w : Fin n → 𝓞 E, q ⊗ₜ[ℤ] w = q • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
      intro w
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ (q ⊗ₜ[ℤ] v)
        = q ⊗ₜ[ℤ] (b • v) := by
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [h2, h1 (b • v), h1 v, map_smul, map_smul]
    funext i
    simp only [Pi.smul_apply, hβ]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingOfIntegers.coe_eq_algebraMap, Rat.smul_def, mul_left_comm, Algebra.smul_def]

theorem UpperTheory.Gal.W2.Seed.pRepLaws :
    RepLaws := by
  rintro E _ _ _ A n rep ⟨β, hβ, hr⟩
  have hβ1 : ∀ v : Fin n → 𝓞 E, β (1 ⊗ₜ v) = fun i => (v i : E) := fun v => funext (hβ v)
  have hsc : ∀ c : 𝓞 E, rep (algebraMap E (Matrix (Fin n) (Fin n) E) c)
      = (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) c).baseChange ℚ := by
    intro c
    refine LinearMap.ext fun z => β.injective ?_
    rw [hr, beta_baseChange β hβ c z, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  refine ⟨?_, ?_, hsc, ?_⟩
  · intro x y hxy
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := β.surjective w
    simp only [Matrix.toLin'_apply]
    rw [← hr, ← hr, hxy]
  · intro M
    constructor
    · rintro ⟨x, rfl⟩ b
      rw [← hsc, ← map_mul, ← map_mul, Algebra.commutes]
    · intro hM
      let F0 : (Fin n → E) →ₗ[ℚ] (Fin n → E) := β.toLinearMap ∘ₗ M ∘ₗ β.symm.toLinearMap
      have hF0 : ∀ (b : 𝓞 E) w, F0 ((b : E) • w) = (b : E) • F0 w := by
        intro b w
        obtain ⟨z, rfl⟩ := β.surjective w
        have h := congrArg (fun N => β (N z)) (hM b)
        simp only [Module.End.mul_apply] at h
        rw [beta_baseChange β hβ] at h
        simp only [F0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rw [← beta_baseChange β hβ, LinearEquiv.symm_apply_apply, h]
      have hF : ∀ (e : E) w, F0 (e • w) = e • F0 w := by
        intro e w
        obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
        have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
        apply smul_right_injective (Fin n → E) hd0
        change algebraMap (𝓞 E) E d • F0 _ = algebraMap (𝓞 E) E d • _
        rw [smul_smul, mul_div_cancel₀ _ hd0]
        have h2 := hF0 d ((algebraMap (𝓞 E) E b / algebraMap (𝓞 E) E d) • w)
        have h3 := hF0 b w
        change F0 (algebraMap (𝓞 E) E d • _) = algebraMap (𝓞 E) E d • _ at h2
        change F0 (algebraMap (𝓞 E) E b • _) = algebraMap (𝓞 E) E b • _ at h3
        rw [← h2, smul_smul, mul_div_cancel₀ _ hd0, h3]
      let F : (Fin n → E) →ₗ[E] (Fin n → E) :=
        { toFun := F0, map_add' := F0.map_add, map_smul' := hF }
      refine ⟨Matrix.toLin'.symm F, ?_⟩
      refine LinearMap.ext fun z => β.injective ?_
      rw [hr]
      have hx : (Matrix.toLin'.symm F) *ᵥ β z = F (β z) := by
        rw [← Matrix.toLin'_apply, LinearEquiv.apply_symm_apply]
      rw [hx]
      simp [F, F0]
  · intro x v
    apply β.injective
    rw [hr, hβ1, hβ1]
    funext i
    exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) x v i).symm
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepAdj :
    RepAdj := by
  intro E _ _ _ A n rep hrep x a b
  obtain ⟨β, h1, h2⟩ := hrep
  have key : ∀ z w, LinearMap.BilinForm.baseChange ℚ (A.EF n) z w =
      Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * β z i * IsCMField.complexConj E (β w i)) := by
    have hσq : ∀ (q : ℚ) (b : E), IsCMField.complexConj E (q • b) = q • IsCMField.complexConj E b := by
      intro q b
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      simp
    have hEF : ∀ v u : Fin n → 𝓞 E, ((A.EF n v u : ℤ) : ℚ) =
        Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * v i * IsCMField.complexConj E (u i)) := by
      intro v u
      simp only [Arith.EF, LinearMap.mk₂_apply, A.trd_spec]
      push_cast
      simp only [A.bar_eq]
    intro z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb, add_mul, Finset.sum_add_distrib, mul_add]
    | tmul q v =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb, mul_add, Finset.sum_add_distrib]
      | tmul r u =>
        rw [LinearMap.BilinForm.baseChange_tmul]
        have e1 : q ⊗ₜ[ℤ] v = q • ((1:ℚ) ⊗ₜ[ℤ] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have e2 : r ⊗ₜ[ℤ] u = r • ((1:ℚ) ⊗ₜ[ℤ] u) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e1, e2, map_smul, map_smul]
        simp only [Pi.smul_apply, h1, hσq]
        have hS : ∑ x, (A.hd n x : E) * q • (v x : E) * r • IsCMField.complexConj E (u x : E) =
            (q * r) • ∑ x, (A.hd n x : E) * v x * IsCMField.complexConj E (u x : E) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Algebra.smul_def, map_mul]
          ring
        rw [hS, mul_smul_comm, map_smul, ← hEF, zsmul_eq_mul, smul_eq_mul]
        ring
  have hreal : ∀ i, IsCMField.complexConj E (A.hd n i : E) = A.hd n i := by
    intro i
    have hc : IsCMField.complexConj E (A.c : E) = A.c := by
      rw [← A.bar_eq, A.c_real]
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  have hc0 : (A.c : E) ≠ 0 := by
    intro h
    have := A.c_neg
    rw [h, map_zero] at this
    simp at this
  have hne : ∀ i, (A.hd n i : E) ≠ 0 := by
    intro i
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc0]
  rw [key, key, h2, h2]
  congr 2
  generalize β a = p
  generalize β b = s
  have hD : ∀ d : Fin n → E, (∀ m, d m ≠ 0) → (diagonal d)⁻¹ = diagonal (fun m => (d m)⁻¹) := by
    intro d hd
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext m
    exact inv_mul_cancel₀ (hd m)
  have hx : ∀ j, (MulOpposite.unop ((hermStar (A.H n) (by
      simp only [Arith.H, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i)) x) *ᵥ s) j =
      (A.hd n j : E)⁻¹ * ∑ k, IsCMField.complexConj E (x k j) * A.hd n k * s k := by
    intro j
    simp only [hermStar, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, Arith.H]
    rw [Matrix.diagonal_map (map_zero _)]
    simp only [Function.comp_def, RingHom.coe_coe, hreal]
    rw [hD _ hne, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    rw [show ∀ d : Fin n → E, diagonal d *ᵥ s = fun m => d m * s m from fun d => funext (Matrix.mulVec_diagonal d s)]
    simp only [Matrix.mulVec, dotProduct, transpose_apply, map_apply, RingHom.coe_coe]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hx]

  simp only [map_mul, map_inv₀, map_sum, hreal, IsCMField.complexConj_apply_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have := hne j
  field_simp
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormCoord :
    TraceType → FormCoord := by
  intro hT E _ _ _ A n Θ hΘ x y
  classical
  have hconj : ∀ (τ : E →+* ℂ) (b : 𝓞 E),
      τ ((A.bar b : 𝓞 E) : E) = (starRingEnd ℂ) (τ (b : E)) := fun τ b => by
    rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
  have hkey : ∀ a b : Fin n → 𝓞 E, ((A.EF n a b : ℤ) : ℝ) =
      ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
        (starRingEnd ℂ) (k.1.1 (b k.2 : E))).re := by
    intro a b
    have h1 : ((A.EF n a b : ℤ) : ℝ) =
        ((Algebra.trace ℚ E (A.δ * ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E)) : ℚ) : ℝ) := by
      rw [← A.trd_spec, A.EF_apply]; norm_cast
    rw [h1, (hT E A).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E) =
        ∑ i, ((A.hd n i : 𝓞 E) : E) * (a i : E) * ((A.bar (b i) : 𝓞 E) : E) := by

      simpa using map_sum (algebraMap (𝓞 E) E) (fun i => A.hd n i * a i * A.bar (b i)) Finset.univ

    rw [h2, map_mul, map_sum, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, hconj, mul_assoc]
  have hx : ∀ (r : ℝ) (a : Fin n → 𝓞 E) (k : Phi A × Fin n),
      Θ (r ⊗ₜ[ℤ] a) k = (r : ℂ) * k.1.1 (a k.2 : E) := by
    rintro r a ⟨τ, i⟩
    have h : r ⊗ₜ[ℤ] a = r • ((1 : ℝ) ⊗ₜ[ℤ] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, Pi.smul_apply, hΘ, Complex.real_smul]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add (f := _), LinearMap.add_apply, h₁, h₂, Pi.add_apply, mul_add, add_mul, Complex.add_re,
      Finset.sum_add_distrib]
  | tmul r a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), h₁, h₂, Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
    | tmul s b =>
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, hkey, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx, hx, map_mul, Complex.conj_ofReal]
      have h : k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * ((r : ℂ) * k.1.1 (a k.2 : E)) *
          ((s : ℂ) * (starRingEnd ℂ) (k.1.1 (b k.2 : E))) =
          ((r * s : ℝ) : ℂ) * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
            (starRingEnd ℂ) (k.1.1 (b k.2 : E))) := by
        push_cast; ring
      rw [h, Complex.re_ofReal_mul]; ring
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma traceCM_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private lemma conj_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    IsCMField.complexConj E (IsCMField.complexConj E z) = z :=
  IsCMField.complexConj_apply_apply E z

private lemma inCodiff_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) {y : E} (hy : InCodiff y) :
    InCodiff (IsCMField.complexConj E y) := by
  intro x
  obtain ⟨m, hm⟩ := hy (bar.symm x)
  refine ⟨m, ?_⟩
  have h : IsCMField.complexConj E y * (x : E) =
      IsCMField.complexConj E (y * ((bar.symm x : 𝓞 E) : E)) := by
    rw [map_mul, ← hbar, RingEquiv.apply_symm_apply]
  rw [h, traceCM_conj, hm]

private lemma inCodiff_mul {E : Type} [Field E] [NumberField E] {y : E} (hy : InCodiff y) (a : 𝓞 E) :
    InCodiff (y * (a : E)) := by
  intro x
  obtain ⟨m, hm⟩ := hy (a * x)
  refine ⟨m, ?_⟩
  rw [mul_assoc, ← hm]
  push_cast
  rfl

private lemma inCodiff_add {E : Type} [Field E] [NumberField E] {y z : E} (hy : InCodiff y) (hz : InCodiff z) :
    InCodiff (y + z) := by
  intro x
  obtain ⟨m, hm⟩ := hy x
  obtain ⟨n, hn⟩ := hz x
  refine ⟨m + n, ?_⟩
  rw [add_mul, map_add (f := _), hm, hn]
  push_cast
  rfl

theorem UpperTheory.Gal.W2.Seed.pRealGen :
    CodiffGen → CodiffUnit → RealGen := by
  intro hgen hunit E _ _ _ bar hbar M hM ε hε
  obtain ⟨y, hy⟩ := hgen E M hM
  by_cases hy0 : y = 0
  · subst hy0
    exact ⟨0, map_zero _, hy⟩
  obtain ⟨hyc, e, he, hegen⟩ := hy
  have hcy : InCodiff (IsCMField.complexConj E y) := inCodiff_conj bar hbar hyc
  obtain ⟨x0, hx0⟩ := hegen _ hcy
  have hx0' : (e : E) * y = IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by
    have h := congrArg (IsCMField.complexConj E) hx0
    rw [map_mul, map_mul, conj_conj', map_natCast] at h
    rw [hbar, h]
  have hnorm : x0 * bar x0 = (e : 𝓞 E) ^ 2 := by
    apply RingOfIntegers.ext
    have h1 : y * ((e : E) ^ 2) = y * ((x0 : E) * ((bar x0 : 𝓞 E) : E)) := by
      calc y * ((e : E) ^ 2) = (e : E) * ((e : E) * y) := by ring
        _ = (e : E) * IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by rw [hx0']; ring
        _ = y * (x0 : E) * ((bar x0 : 𝓞 E) : E) := by rw [hx0]
        _ = _ := by ring
    have h2 := mul_left_cancel₀ hy0 h1
    push_cast
    exact h2.symm
  set t : E := y * (ε : E) + IsCMField.complexConj E (y * (ε : E)) with ht
  refine ⟨t, ?_, ?_⟩
  · rw [ht, map_add (f := _), conj_conj', add_comm]
  · apply hunit E M hM y t ⟨hyc, e, he, hegen⟩
      (inCodiff_add (inCodiff_mul hyc ε) (inCodiff_conj bar hbar (inCodiff_mul hyc ε)))
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr he
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have h3 : ((a * e + b * M : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
      rw [← h3]
      push_cast
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hx0P : x0 ∉ P := by
      intro h
      apply heP
      have h4 : (e : 𝓞 E) ^ 2 ∈ P := hnorm ▸ P.mul_mem_right _ h
      exact hP.isPrime.mem_of_pow_mem 2 h4
    obtain ⟨h1, h2⟩ := hε P hP hMP
    refine ⟨e, e * ε + x0 * bar ε, heP, ?_, ?_⟩
    · intro hu
      rcases hP.isPrime.mem_or_mem h2 with hεP | hεP
      · apply hx0P
        have h5 : x0 = (e * ε + x0 * bar ε) - (e - x0) * ε - x0 * (ε + bar ε - 1) := by ring
        rw [h5]
        exact P.sub_mem (P.sub_mem hu (P.mul_mem_left _ hεP)) (P.mul_mem_left _ h1)
      · apply heP
        have h5 : (e : 𝓞 E) = (e * ε + x0 * bar ε) - e * (ε + bar ε - 1) + (e - x0) * bar ε := by ring
        rw [h5]
        exact P.add_mem (P.sub_mem hu (P.mul_mem_left _ h1)) (P.mul_mem_left _ hεP)
    · rw [ht, map_mul, ← hbar]
      push_cast
      linear_combination ((bar ε : 𝓞 E) : E) * hx0
end
