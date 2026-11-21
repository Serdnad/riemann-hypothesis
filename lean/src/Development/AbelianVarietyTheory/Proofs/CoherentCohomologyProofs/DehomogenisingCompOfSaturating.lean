import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyBaseChangeGrCubeIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNoetherianSubringHomogeneousMatrixFlatChar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteGrCechHomology
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingEqZeroIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGradedPresentationSaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteQuotSMulTopXSubOneOfChart

/-! # Dehomogenization of a saturated presentation -/

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_isBaseChange_coker {R₀ R A₀ A M₁ M₂ N₁ N₂ : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [Ring A₀] [Ring A] [Algebra R₀ A₀] [Algebra R A] [SMul R₀ A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R₀ M₁] [Module R₀ M₂] [Module A₀ M₁] [Module A₀ M₂]
    [IsScalarTower R₀ A₀ M₁] [IsScalarTower R₀ A₀ M₂]
    [Module R₀ N₁] [Module R₀ N₂] [Module R N₁] [Module R N₂] [Module A N₁] [Module A N₂]
    [IsScalarTower R₀ R N₁] [IsScalarTower R₀ R N₂] [IsScalarTower R A N₁] [IsScalarTower R A N₂]
    [IsScalarTower R₀ A N₂]
    (f₀ : M₁ →ₗ[A₀] M₂) (f : N₁ →ₗ[A] N₂) (h₁ : M₁ →ₗ[R₀] N₁) (h₂ : M₂ →ₗ[R₀] N₂)
    (b₁ : IsBaseChange R h₁) (b₂ : IsBaseChange R h₂) (hcomm : ∀ x, h₂ (f₀ x) = f (h₁ x)) :
    ∃ ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f),
      IsBaseChange R ψ ∧ ∀ y, ψ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (h₂ y) := by
  let q₀ : M₂ →ₗ[R₀] (M₂ ⧸ LinearMap.range f₀) := (LinearMap.range f₀).mkQ.restrictScalars R₀
  let q : N₂ →ₗ[R] (N₂ ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.restrictScalars R
  have hq₀ : Function.Surjective q₀ := (LinearMap.range f₀).mkQ_surjective
  have hq : Function.Surjective q := (LinearMap.range f).mkQ_surjective
  have hex₀ : Function.Exact (f₀.restrictScalars R₀) q₀ := LinearMap.exact_map_mkQ_range f₀
  have hex : Function.Exact (f.restrictScalars R) q := LinearMap.exact_map_mkQ_range f
  have hker : LinearMap.ker q₀ ≤ LinearMap.ker ((q.restrictScalars R₀).comp h₂) := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hex₀ y).1 hy
    exact (hex _).2 ⟨h₁ x, (hcomm x).symm⟩
  let ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f) :=
    ((LinearMap.ker q₀).liftQ _ hker).comp (q₀.quotKerEquivOfSurjective hq₀).symm.toLinearMap
  have hψ : ∀ y, ψ (q₀ y) = q (h₂ y) := by
    intro y
    have : (q₀.quotKerEquivOfSurjective hq₀).symm (q₀ y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  exact ⟨ψ, IsBaseChange.of_right_exact R (f := f₀.restrictScalars R₀) (g := q₀)
    (f' := f.restrictScalars R) (g' := q) h₁ h₂ ψ (LinearMap.ext hcomm) (LinearMap.ext hψ)
    b₁ b₂ hex₀ hq₀ hex hq, hψ⟩

theorem isBaseChange_coker_matrix_mvPolynomial :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (a b : ℕ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀))
      (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      Φ₀.map (MvPolynomial.map (algebraMap R₀ R)) = Φ →
      ∃ ψ : ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin) →ₗ[R₀]
          ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin),
        IsBaseChange R ψ ∧ ∀ y : Fin a → MvPolynomial ι R₀,
          ψ (Submodule.Quotient.mk y) =
            Submodule.Quotient.mk fun l => MvPolynomial.map (algebraMap R₀ R) (y l) := by
  intro ι R₀ R _ _ _ a b Φ₀ Φ hΦ
  have hm : IsBaseChange R (mapAlgHom (σ := ι) (Algebra.ofId R₀ R)).toLinearMap :=
    IsBaseChange.of_equiv (algebraTensorAlgEquiv R₀ R).toLinearEquiv fun p => by
      simp [mapAlgHom_apply]
  refine exists_isBaseChange_coker Φ₀.mulVecLin Φ.mulVecLin _ _
    (IsBaseChange.finitePow (Fin b) hm) (IsBaseChange.finitePow (Fin a) hm) fun x => ?_
  funext l
  rw [← hΦ]
  exact RingHom.map_mulVec (MvPolynomial.map (algebraMap R₀ R)) Φ₀ x l

end GlobalTheory

end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isGradedMap_mulVecLin {ι : Type} {R : Type*} [CommRing R] {κ μ : Type*} [Fintype μ]
    {d : κ → ℤ} {e : μ → ℤ} {Φ : Matrix κ μ (MvPolynomial ι R)}
    (h : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) :
    IsGradedMap (grFree ι R e) (grFree ι R d) Φ.mulVecLin := by
  intro n v hv
  refine mem_grPi.2 fun l => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, grShift_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have := grSMul_mem (polyGrading ι R) (h l j) (mem_grPi.1 hv j)
  rwa [smul_eq_mul, show n + -e j + (e j - d l) = n + -d l by ring] at this

theorem isHomogeneous_range_mulVecLin :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ)
      (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) →
        (LinearMap.range Φ.mulVecLin).IsHomogeneous (grFree ι R d) :=
  fun _ _ _ _ _ _ _ _ _ _ h => (isGradedMap_mulVecLin h).isHomogeneous_range

end GlobalTheory

end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise

namespace GlobalTheory

theorem nonempty_homLoc_singleton_equiv_quotSMulTop : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Nonempty (homLoc ℳ {i} 0 ≃ₗ[R] QuotSMulTop (X i - 1 : MvPolynomial ι R) M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  obtain ⟨-, h2, h3⟩ := GlobalTheory.X_sub_one_smul_graded ι R M ℳ i
  let K : Submodule (MvPolynomial ι R) M := (X i - 1 : MvPolynomial ι R) • ⊤
  have hK : ∀ y : M, y ∈ K ↔ ∃ w : M, y = (X i - 1 : MvPolynomial ι R) • w := fun y => by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨w, _, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, trivial, h.symm⟩⟩
  let φ : ∀ k : ℕ, ℳ (0 + k * (({i} : Finset ι).card : ℤ)) →ₗ[R]
      QuotSMulTop (X i - 1 : MvPolynomial ι R) M :=
    fun k => (K.mkQ.restrictScalars R) ∘ₗ (ℳ _).subtype
  have hφv : ∀ k m, φ k m = Submodule.Quotient.mk (m : M) := fun _ _ => rfl
  have hφ : ∀ (k : ℕ) (m : ℳ (0 + k * (({i} : Finset ι).card : ℤ)))
      (m' : ℳ (0 + (k + 1 : ℕ) * (({i} : Finset ι).card : ℤ))),
      (m' : M) = xProd R {i} • (m : M) → φ (k + 1) m' = φ k m := by
    intro k m m' h
    rw [hφv, hφv, Submodule.Quotient.eq]
    refine (hK _).2 ⟨m, ?_⟩
    rw [h, sub_smul, one_smul, xProd, Finset.prod_singleton]
  refine ⟨LinearEquiv.ofBijective (homLocLift φ hφ) ⟨?_, ?_⟩⟩
  · rw [homLocLift_injective_iff]
    intro k m hm
    rw [hφv, Submodule.Quotient.mk_eq_zero] at hm
    obtain ⟨w, hw⟩ := (hK _).1 hm
    obtain ⟨l, hl⟩ := h2 _ _ w m.2 hw
    exact ⟨l, by rwa [xProd, Finset.prod_singleton]⟩
  · rw [homLocLift_surjective_iff]
    intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    obtain ⟨n₀, hn⟩ := h3 y
    obtain ⟨y', hy', w, hw⟩ := hn (0 + (n₀.toNat : ℕ) * (({i} : Finset ι).card : ℤ))
      (by simp)
    refine ⟨n₀.toNat, ⟨y', hy'⟩, ?_⟩
    rw [hφv, eq_comm, Submodule.Quotient.eq]
    exact (hK _).2 ⟨w, by rw [hw, add_sub_cancel_left]⟩

end GlobalTheory

end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

private theorem flat_loc_over_algebra {A S M N : Type} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M] [AddCommGroup N] [Module A N]
    [Module S N] [IsScalarTower A S N] (T : Submonoid S) (f : M →ₗ[S] N) [IsLocalizedModule T f]
    (h : Module.Flat A M) : Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  have := IsLocalizedModule.map_injective T (AlgebraTensorModule.rTensor A Q f)
    (AlgebraTensorModule.rTensor A P f) (AlgebraTensorModule.lTensor S M Q.subtype) (h Q)
  rw [IsLocalizedModule.map_lTensor] at this
  exact this

private theorem flat_iff_forall_piece {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ] :
    Module.Flat R M ↔ ∀ n, Module.Flat R (ℳ n) :=
  (Module.Flat.equiv_iff (decomposeLinearEquiv ℳ)).trans Module.Flat.directSum_iff

theorem flat_homLoc_of_flat_homLoc_singleton :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
      [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
      (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) (s : Finset ι)
      (n : ℤ), i ∈ s → Module.Flat R (homLoc ℳ {i} 0) → Module.Flat R (homLoc ℳ s n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i s n hi h0
  have step (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) ↔ Module.Flat R (homLoc ℳ {i} (t + 1)) :=
    Module.Flat.equiv_iff (LinearEquiv.ofBijective _
      (homLocSMul_X_bijective ℳ (Finset.mem_singleton_self i) t))
  have hall (t : ℤ) : Module.Flat R (homLoc ℳ {i} t) := by
    induction t using Int.induction_on with
    | zero => exact h0
    | succ k ih => exact (step _).1 ih
    | pred k ih => exact (step _).2 (by rwa [sub_add_cancel])
  have h1 := (flat_iff_forall_piece (homLoc ℳ {i})).2 hall
  have hsub : ({i} : Finset ι) ⊆ s := Finset.singleton_subset_iff.2 hi
  have hc : xProd R s = xProd R (s \ {i}) * xProd R {i} := (Finset.prod_sdiff hsub).symm
  have h2 : IsLocalizedModule.Away (xProd R (s \ {i}) * xProd R {i})
      (locRes X M hsub ∘ₗ LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) := by
    rw [locRes_comp_mkLinearMap, ← hc]
    exact localizedModuleIsLocalizedModule _
  have h3 : IsLocalizedModule.Away (xProd R (s \ {i})) (locRes X M hsub) :=
    isLocalizedModule_away_of_comp (b := xProd R {i})
      (LocalizedModule.mkLinearMap (.powers (xProd R {i})) M) _
  have h4 := flat_loc_over_algebra (A := R) (.powers (xProd R (s \ {i}))) (locRes X M hsub) h1
  exact (flat_iff_forall_piece (homLoc ℳ s)).1 h4 n

end GlobalTheory

end

open CategoryTheory CategoryTheory.Limits DirectSum TensorProduct

noncomputable section

namespace GlobalTheory

theorem dehomogenising_comp_of_saturating {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type}
    [CommRing R] {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    [Decomposition 𝒩] {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    (𝒢 : ℤ → Submodule R G) {ψ : N →ₗ[MvPolynomial ι R] G} (hψ : IsGradedMap 𝒩 𝒢 ψ) (i : ι)
    (h₁ : ∀ y, ψ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    (h₂ : ∀ z : G, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ)
    {B : Type} [CommRing B] (π : MvPolynomial ι R →+* B) {P : Type} [AddCommGroup P] [Module B P]
    (ε : G →ₛₗ[π] P) (hπ : π (MvPolynomial.X i) = 1) (hε : Function.Surjective ε)
    (hk : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    Function.Surjective (ε.comp ψ) ∧
      ∀ y, ε.comp ψ y = 0 ↔ ∃ w : N, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w := by
  refine ⟨fun p => ?_, dehomogenising_eq_zero_iff ι R N 𝒩 i B π P (ε.comp ψ) hπ ?_⟩
  · obtain ⟨z, rfl⟩ := hε p
    obtain ⟨k, y, hy⟩ := h₂ z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, hy, LinearMap.map_smulₛₗ, map_pow, hπ, one_pow, one_smul]
  · intro n y hy h
    obtain ⟨k, hk⟩ := hk n _ (hψ hy) h
    obtain ⟨j, hj⟩ := h₁ _ ((map_smul ψ _ y).trans hk)
    exact ⟨j + k, by rw [pow_add, mul_smul, hj]⟩

theorem exists_noetherian_model_grCube (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢]
    (H : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
      (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
      Algebra.Smooth R B ∧ Module.FinitePresentation B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
        ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
          ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    ∃ (R₀ : Subring R) (_ : IsNoetherianRing R₀) (C₀ : Cube.{0} ι R₀)
      (θ : Cube.baseChange R C₀ ⟶ grCube ι 𝒢 0),
      (∀ I : Finset ι, I.Nonempty → Module.Flat R₀ (C₀.obj I)) ∧
        (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) ∧
        ∀ I : Finset ι, I.Nonempty → Function.Bijective (θ.app I).hom := by
  obtain ⟨a, b, d, e, Φ, ψ, hΦ, hψ, hsat⟩ :=
    exists_graded_presentation_saturating ι R G 𝒢 fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, hfp, -, h⟩ := H i
      exact (finite_quotSMulTop_X_sub_one_of_chart ι R G 𝒢 i B iB iA π P iP iM ε h).2
        inferInstance hfp
  let := grQuotDecomposition (grFree ι R d) (isHomogeneous_range_mulVecLin ι R a b d e Φ hΦ)
  obtain ⟨R₀, Φ₀, hN, hmap, hΦ₀, hflat⟩ :=
    exists_noetherian_subring_homogeneous_matrix_flat_charts ι R a b d e Φ hΦ fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, -, hp, hπs, hπ, hε, hk⟩ := H i
      obtain ⟨k₁, k₂⟩ := dehomogenising_comp_of_saturating
        (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 hψ i (hsat i).1 (hsat i).2
        (π : MvPolynomial ι R →+* B) ε hπ hε hk
      refine ⟨B, iB, iA, π, P, iP, iM, (ε.comp ψ).comp (LinearMap.range Φ.mulVecLin).mkQ, hs, hp,
        hπs, hπ, k₁.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
      rw [LinearMap.comp_apply, k₂]
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨w', rfl⟩ := Submodule.mkQ_surjective _ w
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hw
        obtain ⟨v, hv⟩ := hw
        exact ⟨v, w', by rw [← Matrix.mulVecLin_apply, hv, sub_add_cancel]⟩
      · rintro ⟨v, w', rfl⟩
        refine ⟨Submodule.mkQ _ w', ?_⟩
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact ⟨v, by rw [Matrix.mulVecLin_apply, add_sub_cancel_right]⟩
  let := grQuotDecomposition (grFree ι R₀ d)
    (isHomogeneous_range_mulVecLin ι R₀ a b d e Φ₀ hΦ₀)
  obtain ⟨ψ₀, hbc, hψ₀⟩ := isBaseChange_coker_matrix_mvPolynomial ι R₀ R a b Φ₀ Φ hmap
  obtain ⟨iso⟩ := nonempty_baseChange_grCube_iso ι R₀ R _
    (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) _
    (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) ψ₀ 0 hbc
    (fun i y => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, hψ₀, hψ₀, ← Submodule.Quotient.mk_smul]
      congr 1
      ext1 l
      simp)
    (by
      rintro j _ ⟨y, hy, rfl⟩
      refine mem_grQuot.2 ⟨_, mem_grPi.2 fun l => ?_, (hψ₀ y).symm⟩
      have := mem_polyGrading_iff.1 (mem_grPi.1 hy l)
      refine mem_polyGrading_iff.2 fun c hc => this c fun h0 => hc ?_
      rw [MvPolynomial.coeff_map, h0, map_zero])
  refine ⟨R₀, hN, grCube ι (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) 0,
    iso.hom ≫ grCubeMap hψ 0, ?_, ?_, ?_⟩
  · rintro I ⟨i, hi⟩
    obtain ⟨f⟩ := nonempty_homLoc_singleton_equiv_quotSMulTop ι R₀ _
      (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) i
    have := hflat i
    exact flat_homLoc_of_flat_homLoc_singleton ι R₀ _ _ i I 0 hi (Module.Flat.of_linearEquiv f)
  · exact finite_grCech_homology ι R₀ _ _ inferInstance 0
  · rintro I ⟨i, hi⟩
    rw [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact (homLocMap_bijective_of_X hψ hi (hsat i).1 (hsat i).2 0).comp
      (ConcreteCategory.bijective_of_isIso (iso.hom.app I))

end GlobalTheory
