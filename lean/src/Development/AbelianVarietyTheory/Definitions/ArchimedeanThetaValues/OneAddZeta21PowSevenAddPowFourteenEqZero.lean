import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

noncomputable section

namespace GlobalTheory.HostModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section General

theorem sq_sub_smul_derivation_eq_zero {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module A M] [Module B M] (D : Derivation A B M) (σ : B →+* B) (hσ : ∀ b, σ (σ b) = b)
    (hfix : ∀ b, σ b = b → b ∈ Set.range (algebraMap A B)) (w b : B) : (w - σ w) ^ 2 • D b = 0 := by
  have h0 : ∀ x, σ x = x → D x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := hfix x hx
    exact D.map_algebraMap a
  have h1 : ∀ x, D (σ x) = -D x := fun x => by
    have h := h0 (x + σ x) (by rw [map_add, hσ, add_comm])
    rw [map_add] at h
    exact eq_neg_of_add_eq_zero_right h
  have h2 : ∀ x, (x - σ x) • D x = 0 := fun x => by
    have h := h0 (σ x * x) (by rw [map_mul, hσ, mul_comm])
    rw [D.leibniz, h1, smul_neg, ← sub_eq_add_neg, ← sub_smul] at h
    rw [← neg_sub, neg_smul, h, neg_zero]
  have h3 : (w - σ w) • D b + (b - σ b) • D w = 0 := by
    have h := h2 (w + b)
    have e : w + b - σ (w + b) = (w - σ w) + (b - σ b) := by rw [map_add]; ring
    rw [e, map_add, add_smul, smul_add, smul_add, h2, h2, zero_add, add_zero] at h
    exact h
  have h4 := congrArg (fun m => (w - σ w) • m) h3
  simp only [smul_add, smul_zero] at h4
  rw [smul_comm (w - σ w) (b - σ b), h2, smul_zero, add_zero, ← mul_smul, ← sq] at h4
  exact h4

theorem formallyUnramified_of_isCoprime {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B →+* B)
    (hσ : ∀ b, σ (σ b) = b) (hfix : ∀ b, σ b = b → b ∈ Set.range (algebraMap A B)) (w₁ w₂ : B)
    (h : IsCoprime (w₁ - σ w₁) (w₂ - σ w₂)) : Algebra.FormallyUnramified A B := by
  have hD : ∀ b, KaehlerDifferential.D A B b = 0 := fun b => by
    obtain ⟨u, v, huv⟩ : IsCoprime ((w₁ - σ w₁) ^ 2) ((w₂ - σ w₂) ^ 2) := h.pow
    rw [← one_smul B (KaehlerDifferential.D A B b), ← huv, add_smul, mul_smul, mul_smul,
      sq_sub_smul_derivation_eq_zero _ σ hσ hfix, sq_sub_smul_derivation_eq_zero _ σ hσ hfix, smul_zero, smul_zero,
      add_zero]
  have hbot : (⊤ : Submodule B (Ω[B⁄A])) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨b, rfl⟩
    exact hD b
  refine ⟨⟨fun x y => ?_⟩⟩
  have hz : ∀ z : Ω[B⁄A], z = 0 := fun z => by
    rw [← Submodule.mem_bot B, ← hbot]
    trivial
  rw [hz x, hz y]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem unramified_of_isCoprime (w₁ w₂ : 𝓞 E)
    (h : IsCoprime (w₁ - IsCMField.ringOfIntegersComplexConj E w₁) (w₂ - IsCMField.ringOfIntegersComplexConj E w₂)) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  { formallyUnramified := formallyUnramified_of_isCoprime (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)
      (fun b => RingOfIntegers.ext (IsCMField.complexConj_apply_apply E (b : E)))
      (fun b hb => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E b).1 hb) w₁ w₂ h
    finiteType := inferInstance }

theorem complexConj_eq_neg_of_sq_eq_neg {x : E} {n : ℕ} (hx : x ^ 2 = -(n : E)) : IsCMField.complexConj E x = -x := by
  let φ : E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  have h : φ x ^ 2 = -(n : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h0 : (φ x).re = 0 := by
    by_contra hne
    have hi : (φ x).im = 0 := by
      have : (φ x).re * (φ x).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [hi] at hre
    have := mul_self_pos.2 hne
    linarith
  apply Complex.ext <;> simp [h0]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.HostModel.coe_sq_eq_neg {x : 𝓞 E} {n : ℕ} (hx : x ^ 2 = -(n : 𝓞 E)) : (x : E) ^ 2 = -(n : E) := by
  have h := congrArg (fun y : 𝓞 E => (y : E)) hx
  simpa using h

theorem sub_complexConj_eq_of_two_mul {w x : 𝓞 E} {n : ℕ} (hx : x ^ 2 = -(n : 𝓞 E)) (hw : 2 * w = 1 + x) :
    w - IsCMField.ringOfIntegersComplexConj E w = x := by
  have hx' : IsCMField.ringOfIntegersComplexConj E x = -x := by
    apply RingOfIntegers.ext
    have h : (x : E) ^ 2 = -(n : E) := coe_sq_eq_neg hx
    exact complexConj_eq_neg_of_sq_eq_neg h
  have h := congrArg (IsCMField.ringOfIntegersComplexConj E) hw
  rw [map_mul, map_add, map_one, hx', map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
  linear_combination hw - h

theorem unramified_of_sqrt {x₁ x₂ w₁ w₂ : 𝓞 E} {m n : ℕ} (hmn : m.Coprime n) (h₁ : x₁ ^ 2 = -(m : 𝓞 E))
    (h₂ : x₂ ^ 2 = -(n : 𝓞 E)) (hw₁ : 2 * w₁ = 1 + x₁) (hw₂ : 2 * w₂ = 1 + x₂) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
  apply unramified_of_isCoprime w₁ w₂
  rw [sub_complexConj_eq_of_two_mul h₁ hw₁, sub_complexConj_eq_of_two_mul h₂ hw₂,
    ← IsCoprime.pow_iff (m := 2) (n := 2) two_pos two_pos, h₁, h₂, IsCoprime.neg_neg_iff]
  exact hmn.cast

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.HostModel.exists_embedding_rt_eq (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have h : (φ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, coe_sq_eq_neg H.rt_sq, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨φ, h⟩
  · refine ⟨φ.comp (IsCMField.complexConj E).toRingHom, ?_⟩
    change φ (IsCMField.complexConj E (H.rt : E)) = H.rt0
    rw [complexConj_eq_neg_of_sq_eq_neg (coe_sq_eq_neg H.rt_sq), map_neg, h, neg_neg]

end General

abbrev E21 : Type := CyclotomicField 21 ℚ

instance isCyclotomicExtension_cyclotomicField21 : IsCyclotomicExtension {21} ℚ E21 := CyclotomicField.isCyclotomicExtension 21 ℚ

instance isCMField_cyclotomicField21 : IsCMField E21 := IsCyclotomicExtension.Rat.isCMField E21 (S := {21}) ⟨21, rfl, by norm_num⟩

def primitiveRootCyclotomicField21 : 𝓞 E21 := (IsCyclotomicExtension.zeta_spec 21 ℚ E21).toInteger

theorem isPrimitiveRoot_primitiveRootCyclotomicField21 : IsPrimitiveRoot primitiveRootCyclotomicField21 21 :=
  (IsCyclotomicExtension.zeta_spec 21 ℚ E21).toInteger_isPrimitiveRoot

theorem sum_zeta21_pow_multiples_of_three_eq_zero : 1 + primitiveRootCyclotomicField21 ^ 3 + primitiveRootCyclotomicField21 ^ 6 + primitiveRootCyclotomicField21 ^ 9 + primitiveRootCyclotomicField21 ^ 12 + primitiveRootCyclotomicField21 ^ 15 + primitiveRootCyclotomicField21 ^ 18 = 0 := by
  have h : IsPrimitiveRoot (primitiveRootCyclotomicField21 ^ 3) 7 := isPrimitiveRoot_primitiveRootCyclotomicField21.pow (by norm_num) (by norm_num)
  have h2 := h.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  linear_combination h2

def halfSqrtNegSeven : 𝓞 E21 := 1 + primitiveRootCyclotomicField21 ^ 3 + primitiveRootCyclotomicField21 ^ 6 + primitiveRootCyclotomicField21 ^ 12

def sqrtNegSeven : 𝓞 E21 := 2 * halfSqrtNegSeven - 1

def sqrtNegThree : 𝓞 E21 := 1 + 2 * primitiveRootCyclotomicField21 ^ 7

theorem halfSqrtNegSeven_quadratic : halfSqrtNegSeven ^ 2 - halfSqrtNegSeven + 2 = 0 := by
  have h := isPrimitiveRoot_primitiveRootCyclotomicField21.pow_eq_one
  unfold halfSqrtNegSeven
  linear_combination 2 * sum_zeta21_pow_multiples_of_three_eq_zero + primitiveRootCyclotomicField21 ^ 3 * h

theorem sqrtNegSeven_sq : sqrtNegSeven ^ 2 = -((7 : ℕ) : 𝓞 E21) := by
  unfold sqrtNegSeven
  push_cast
  linear_combination 4 * halfSqrtNegSeven_quadratic

theorem unramified_E21_over_maximalRealSubfield :
    Algebra.Unramified (𝓞 (maximalRealSubfield E21)) (𝓞 E21) := by
  let ω := primitiveRootCyclotomicField21 ^ 7
  have hω : IsPrimitiveRoot ω 3 := isPrimitiveRoot_primitiveRootCyclotomicField21.pow (by norm_num) (by norm_num)
  have hsum := hω.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  apply unramified_of_sqrt (m := 7) (n := 3) (x₂ := sqrtNegThree)
    (w₁ := halfSqrtNegSeven) (w₂ := 1 + ω) (by decide) sqrtNegSeven_sq
  · change (1 + 2 * ω) ^ 2 = -(3 : 𝓞 E21)
    linear_combination 4 * hsum
  · unfold sqrtNegSeven
    ring
  · change 2 * (1 + ω) = 1 + (1 + 2 * ω)
    ring

def host : Host E21 where
  d := 7
  d_mod := by norm_num
  d_prime := by norm_num
  rt := sqrtNegSeven
  rt_sq := sqrtNegSeven_sq
  w0 := halfSqrtNegSeven
  two_weight_eq_one_add_root := by unfold sqrtNegSeven; ring
  bar := (IsCMField.ringOfIntegersComplexConj E21).toRingEquiv
  bar_eq _ := rfl
  unram := unramified_E21_over_maximalRealSubfield
  rt0 := Complex.I * (Real.sqrt 7 : ℝ)
  sqrt_neg_disc_sq := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring

@[simp] theorem host_d : host.d = 7 := rfl

@[simp] theorem host_rt : host.rt = sqrtNegSeven := rfl

@[simp] theorem host_w0_eq_halfSqrtNegSeven : host.w0 = halfSqrtNegSeven := rfl

@[simp] theorem host_rt0_eq_I_mul_sqrt_seven : host.rt0 = Complex.I * (Real.sqrt 7 : ℝ) := rfl

instance nonempty_host : Nonempty (Host E21) := ⟨host⟩

theorem finrank_rat_E21_eq_twelve : Module.finrank ℚ E21 = 12 := by
  rw [IsCyclotomicExtension.finrank E21 (Polynomial.cyclotomic.irreducible_rat (n := 21) (by norm_num))]
  decide

example : host.bar host.rt = -host.rt :=
  RingOfIntegers.ext (complexConj_eq_neg_of_sq_eq_neg (n := 7)
    (coe_sq_eq_neg sqrtNegSeven_sq))

example : host.w0 * host.bar host.w0 = 2 := by
  have h := sub_complexConj_eq_of_two_mul host.rt_sq host.two_weight_eq_one_add_root
  change halfSqrtNegSeven - host.bar host.w0 = 2 * halfSqrtNegSeven - 1 at h
  change halfSqrtNegSeven * host.bar host.w0 = 2
  linear_combination -halfSqrtNegSeven * h - halfSqrtNegSeven_quadratic

example : ∃ τ : E21 →+* ℂ, τ (sqrtNegSeven : E21) = Complex.I * (Real.sqrt 7 : ℝ) := exists_embedding_rt_eq host

end GlobalTheory.HostModel
