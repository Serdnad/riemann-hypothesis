import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulMemSpanOfFiniteQuotStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating

/-! # Saturation of graded presentations -/

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem exists_pow_smul_eq_add_sub_one_smul {S M : Type} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) : ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

private lemma comap_ker_inf_smul_whole_eq_smul_whole_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) :
    Submodule.comap (LinearMap.ker φ).subtype (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F)) =
      u • (⊤ : Submodule S (LinearMap.ker φ)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨-, hx⟩
    obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have hvK : v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply hreg
      rw [← map_smul, hv]
      exact LinearMap.mem_ker.mp x.2
    have hx' : x = u • (⟨v, hvK⟩ : LinearMap.ker φ) := Subtype.ext hv.symm
    rw [hx']
    exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro hx
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨(u • b).2, ?_⟩
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem_pointwise_smul (b : F) u ⊤ Submodule.mem_top

private lemma ker_sup_smul_whole_eq_ker_mkQ_comp {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    LinearMap.ker φ ⊔ u • (⊤ : Submodule S F) =
      LinearMap.ker ((u • (⊤ : Submodule S G)).mkQ ∘ₗ φ) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [LinearMap.comp_apply, hy, map_zero]
    · intro y hy
      obtain ⟨v, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ u ⊤ Submodule.mem_top
  · intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    obtain ⟨k, v, hk, rfl⟩ := hker y w hw.symm
    exact Submodule.add_mem_sup (LinearMap.mem_ker.mpr hk)
      (Submodule.smul_mem_pointwise_smul v u ⊤ Submodule.mem_top)

theorem finite_quotSMulTop_ker_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) [Module.Finite S F]
    [Module.FinitePresentation S (QuotSMulTop u G)]
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), φ y = z + u • w)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker φ)) := by
  let ψ : F →ₗ[S] QuotSMulTop u G := (u • (⊤ : Submodule S G)).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (u • (⊤ : Submodule S G)) z
    obtain ⟨y, w, hy⟩ := hsurj z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hy, add_sub_cancel_left]
    exact Submodule.smul_mem_pointwise_smul w u ⊤ Submodule.mem_top
  have hfg : (LinearMap.ker ψ).FG := Module.FinitePresentation.fg_ker ψ hψ
  have hfin : Module.Finite S ↥(LinearMap.ker φ ⊔ u • (⊤ : Submodule S F)) := by
    rw [ker_sup_smul_whole_eq_ker_mkQ_comp u φ hker]
    exact Module.Finite.iff_fg.mpr hfg
  have h2 : Module.Finite S (LinearMap.ker φ ⧸ Submodule.comap (LinearMap.ker φ).subtype
      (LinearMap.ker φ ⊓ u • (⊤ : Submodule S F))) :=
    Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient (LinearMap.ker φ)
      (u • (⊤ : Submodule S F))).symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ (u • (⊤ : Submodule S (LinearMap.ker φ)))
    (comap_ker_inf_smul_whole_eq_smul_whole_of_regular u φ hreg))

theorem finite_quotSMulTop_ker_of_graded :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (F : Type) [AddCommGroup F] [Module R F] [Module (MvPolynomial ι R) F] [IsScalarTower R (MvPolynomial ι R) F] (ℱ : ℤ → Submodule R F) [PolyGradedSMul ι ℱ] [Decomposition ℱ] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢] (φ : F →ₗ[MvPolynomial ι R] G) (i : ι), IsGradedMap ℱ 𝒢 φ → Module.Finite (MvPolynomial ι R) F → (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ) → Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G) → Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) (LinearMap.ker φ)) := by
  intro ι _ _ R _ F _ _ _ _ ℱ _ _ G _ _ _ _ 𝒢 _ _ φ i hφ hF hpow hfp
  obtain ⟨hregG, hkillG, -⟩ := X_sub_one_smul_graded ι R G 𝒢 i
  obtain ⟨-, -, hhomF⟩ := X_sub_one_smul_graded ι R F ℱ i
  refine finite_quotSMulTop_ker_of_regular (X i - 1 : MvPolynomial ι R) φ hregG ?_ ?_
  · intro z
    obtain ⟨k, hk⟩ := hpow z
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
    obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z
    exact ⟨y, w, hy.trans hw⟩
  · intro y w hyw
    obtain ⟨n₀, hn⟩ := hhomF y
    obtain ⟨y', hy', v₀, hyv⟩ := hn n₀ le_rfl
    have hφy' : φ y' ∈ 𝒢 n₀ := hφ hy'
    have h1 : φ y = φ y' + (X i - 1 : MvPolynomial ι R) • φ v₀ := by
      rw [hyv, map_add, map_smul]
    have h2 : φ y' = (X i - 1 : MvPolynomial ι R) • (w - φ v₀) := by
      rw [smul_sub, ← hyw, h1]
      abel
    obtain ⟨k, hk⟩ := hkillG n₀ (φ y') (w - φ v₀) hφy' h2
    obtain ⟨w₁, hw₁⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k y'
    refine ⟨(X i : MvPolynomial ι R) ^ k • y', v₀ - w₁, ?_, ?_⟩
    · rw [map_smul, hk]
    · rw [hyv, hw₁, smul_sub]
      abel

end GlobalTheory

end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_graded_presentation_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢], (∀ i : ι, Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)) → ∃ (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G), (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) ∧ IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 ψ ∧ ∀ i : ι, (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧ (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ hG
  obtain ⟨a, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 fun i =>
    GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R G 𝒢 i (haveI := hG i; inferInstance)
  set φ := Fintype.linearCombination (MvPolynomial ι R) g with hφdef
  have hφ : IsGradedMap (grFree ι R d) 𝒢 φ := isGradedMap_linearCombination 𝒢 hg
  have hsat' : ∀ (i : ι) (z : G), ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ := by
    intro i z
    rw [hφdef, Fintype.range_linearCombination]
    exact hsat i z
  let _ : Decomposition (grSub (grFree ι R d) (LinearMap.ker φ)) :=
    grSubDecomposition _ hφ.isHomogeneous_ker
  obtain ⟨b, e, κ, hκ, hksat⟩ := exists_homogeneous_family_saturating ι R (LinearMap.ker φ)
    (grSub (grFree ι R d) (LinearMap.ker φ)) fun i =>
      GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop ι R _ (grSub (grFree ι R d) (LinearMap.ker φ)) i
        (GlobalTheory.finite_quotSMulTop_ker_of_graded ι R _ (grFree ι R d) G 𝒢 φ i hφ inferInstance (hsat' i) (hG i))
  let Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R) := Matrix.of fun l j => (κ j).1 l
  have hrange : LinearMap.range Φ.mulVecLin =
      (Submodule.span (MvPolynomial ι R) (Set.range κ)).map (LinearMap.ker φ).subtype := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : LinearMap.range Φ.mulVecLin ≤ LinearMap.ker φ := by
    rw [hrange]
    exact Submodule.map_subtype_le _ _
  refine ⟨a, b, d, e, Φ, Submodule.liftQ _ φ hle, fun l j => ?_, hφ.liftQ _ hle,
    fun i => ⟨fun y hy => ?_, fun z => ?_⟩⟩
  · have := mem_grPi.1 (mem_grSub.1 (hκ j)) l
    rw [sub_eq_add_neg]
    exact this
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨k, hk⟩ := hksat i ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨_, hk, rfl⟩
  · rw [Submodule.range_liftQ]
    exact hsat' i z

end GlobalTheory
