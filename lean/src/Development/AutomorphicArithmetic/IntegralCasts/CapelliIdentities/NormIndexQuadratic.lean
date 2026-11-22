import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Pl :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Kv :
    {F : Type} → [inst : Field F] → [NumberField F] → UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F → Type :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.cv :
    {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) → F →+* UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦ Algebra.algebraMap F (UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v)

open NumberField IsDedekindDomain Module

namespace UpperTheory.Reformulated.B.NormIndexQuadratic

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private instance liesOver (P : HeightOneSpectrum (𝓞 E)) : P.asIdeal.LiesOver (P.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem ucont (P : HeightOneSpectrum (𝓞 E)) :
    UniformContinuous (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E))) :=
  HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E (P.under (𝓞 F)) P

private noncomputable def compMap (P : HeightOneSpectrum (𝓞 E)) : (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E :=
  (HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E)))
      (ucont P).continuous).comp (HeightOneSpectrum.adicCompletion.equiv F (P.under (𝓞 F))).toRingHom)

private theorem compMap_coe (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    compMap P (x : (P.under (𝓞 F)).adicCompletion F) = ((algebraMap F E x : E) : P.adicCompletion E) := by
  apply HeightOneSpectrum.adicCompletion.ext
  have e : (compMap P (x : (P.under (𝓞 F)).adicCompletion F)).toCompletion =
      UniformSpace.Completion.mapRingHom (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E)))
        (ucont P).continuous ((x : F) : ((P.under (𝓞 F)).valuation F).Completion) := rfl
  rw [e, UniformSpace.Completion.mapRingHom_coe]
  rw [HeightOneSpectrum.adicCompletion.coe_toCompletion]
  congr 1

end

private lemma exists_quad {K : Type} [Field K] [NumberField K] {θ : K} (h : ¬ IsSquare θ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (r : L) (σ : L ≃ₐ[K] L),
      r ^ 2 = algebraMap K L θ ∧ σ r = -r ∧
      (∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * r) ∧ finrank K L = 2 := by
  have : Fact (∀ r : K, r ^ 2 ≠ θ + 0 * r) := ⟨fun r hr => h ⟨r, by rw [← sq, hr]; simp⟩⟩
  have : NumberField (QuadraticAlgebra K θ 0) := NumberField.of_module_finite K _
  refine ⟨QuadraticAlgebra K θ 0, inferInstance, this, inferInstance, QuadraticAlgebra.omega,
    { (starRingAut : RingAut (QuadraticAlgebra K θ 0)) with commutes' := ?_ }, ?_, ?_, ?_,
    QuadraticAlgebra.finrank_eq_two _ _⟩
  · intro r; ext <;> simp
  · ext <;> simp [sq]
  · show star _ = _
    ext <;> simp
  · intro x
    exact ⟨x.re, x.im, by ext <;> simp⟩

theorem glob_neg_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {Δ d : F},
      Δ ≠ (0 : F) →
        (∀ (v : Pl F),
            ∃ (a : Kv v) (b : Kv v),
              (-1 : Kv v) =
                a ^ (2 : ℕ) - (cv v : F → Kv v) Δ * b ^ (2 : ℕ)) →
          ∀ (σ₀ : F →+* ℝ),
            (∀ (σ : F →+* ℝ), (σ : F → ℝ) d < (0 : ℝ)) →
              ∃ (p₀ : F) (p₁ : F) (q₀ : F) (q₁ : F),
                p₀ ^ (2 : ℕ) + d * p₁ ^ (2 : ℕ) - Δ * (q₀ ^ (2 : ℕ) + d * q₁ ^ (2 : ℕ)) = (-1 : F) ∧ p₀ * p₁ = Δ * q₀ * q₁ := by
  intro F _ _ Δ d hΔ h σ₀ hd
  have hsq : ¬ IsSquare d := by
    rintro ⟨t, rfl⟩
    exact absurd (hd σ₀) (not_lt.2 (by rw [map_mul]; exact mul_self_nonneg _))
  obtain ⟨E, _, _, _, r, σ, h1, h2, h3, -⟩ := exists_quad hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    refine hsq ⟨0, (algebraMap F E).injective ?_⟩
    rw [← h1]; simp
  have hreal (τ : E →+* ℝ) : ∃ a b : ℝ,
      τ (-1) = a ^ 2 - τ (algebraMap F E Δ) * b ^ 2 := by
    have hneg := hd (τ.comp (algebraMap F E))
    rw [RingHom.comp_apply, ← h1, map_pow] at hneg
    exact False.elim ((not_lt_of_ge (sq_nonneg _)) hneg)
  have hfin (w : Pl E) : ∃ a b : Kv w,
      cv w (-1) = a ^ 2 - cv w (algebraMap F E Δ) * b ^ 2 := by
    obtain ⟨a, b, hab⟩ := h (w.under (𝓞 F))
    refine ⟨compMap w a, compMap w b, ?_⟩
    have hmap : compMap w (cv (w.under (𝓞 F)) Δ) = cv w (algebraMap F E Δ) :=
      compMap_coe w Δ
    simpa only [map_neg, map_one, map_sub, map_pow, map_mul, hmap] using congrArg (compMap w) hab
  obtain ⟨p, q, hpq⟩ := GlobalTheory.QNorm.hasseNormSt E (algebraMap F E Δ) (-1)
    (by simpa using hΔ) (by simp) hreal hfin
  obtain ⟨p₀, p₁, rfl⟩ := h3 p
  obtain ⟨q₀, q₁, rfl⟩ := h3 q
  have h7 := congrArg σ hpq
  simp only [map_neg, map_one, map_sub, map_mul, map_add, map_pow, h2, σ.commutes] at h7
  refine ⟨p₀, p₁, q₀, q₁, (algebraMap F E).injective ?_, (algebraMap F E).injective ?_⟩
  · simp only [map_neg, map_one, map_sub, map_mul, map_add, map_pow, ← h1]
    linear_combination (-1 / 2) * hpq + (-1 / 2) * h7
  · simp only [map_mul]
    refine mul_right_cancel₀ hr0 ?_
    linear_combination (-1 / 4) * hpq + (1 / 4) * h7

end UpperTheory.Reformulated.B.NormIndexQuadratic
