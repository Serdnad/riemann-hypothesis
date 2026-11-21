import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PowSmulMemOfHomogeneous

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

open GradedHilbert Pointwise

/-- Homogeneous lifts of generators modulo `Xᵢ - 1` generate after inverting `Xᵢ`. -/
theorem exists_X_pow_smul_mem_span_of_finite_quot :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
      (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M]
      (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι),
      Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M) →
      ∃ T : Finset M, ∀ y : M, ∃ k : ℕ,
        (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i hfin
  classical
  set I : Submodule (MvPolynomial ι R) M :=
    (X i - 1 : MvPolynomial ι R) • (⊤ : Submodule (MvPolynomial ι R) M)
  obtain ⟨G, hG⟩ := hfin.fg_top
  have hlift : ∀ q : QuotSMulTop (X i - 1 : MvPolynomial ι R) M,
      ∃ m : M, ∃ d : ℤ, m ∈ ℳ d ∧ Submodule.Quotient.mk m = q := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨n₀, hn₀⟩ := _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul ℳ i m
    obtain ⟨m', hm', w, hw⟩ := hn₀ n₀ le_rfl
    refine ⟨m', n₀, hm', ?_⟩
    rw [Submodule.Quotient.eq, hw, sub_add_cancel_left]
    exact I.neg_mem (Submodule.smul_mem_pointwise_smul w _ ⊤ Submodule.mem_top)
  choose f d hfd hfq using hlift
  let T : Finset M := G.image f
  set S := Submodule.span (MvPolynomial ι R) (T : Set M) with hS
  have hS_gr : S.IsHomogeneous ℳ := by
    rw [hS]
    apply isHomogeneous_span_gr ℳ
    intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    exact ⟨d q, hfd q⟩
  letI : Decomposition (grQuot ℳ S) := grQuotDecomposition ℳ hS_gr
  -- The chosen lifts generate modulo Xᵢ − 1, so Xᵢ − 1 acts surjectively on M ⧸ S.
  have hsurj : Function.Surjective (fun z : M ⧸ S => (X i - 1 : MvPolynomial ι R) • z) := by
    intro z
    obtain ⟨y, rfl⟩ := S.mkQ_surjective z
    have hsub : (G : Set (QuotSMulTop (X i - 1 : MvPolynomial ι R) M)) ⊆ I.mkQ '' (T : Set M) :=
      fun q hq => ⟨f q, Finset.mem_coe.2 (Finset.mem_image_of_mem f hq), hfq q⟩
    have hy : I.mkQ y ∈ S.map I.mkQ := by
      rw [hS, Submodule.map_span]
      exact Submodule.span_mono hsub (hG ▸ Submodule.mem_top)
    obtain ⟨s, hs, hsy⟩ := Submodule.mem_map.1 hy
    have hy_sub_s : y - s ∈ I := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← hsy, sub_self]
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy_sub_s
    have hs_zero : S.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero S).2 hs
    refine ⟨S.mkQ w, ?_⟩
    change (X i - 1 : MvPolynomial ι R) • S.mkQ w = S.mkQ y
    rw [← map_smul, hw, map_sub, hs_zero, sub_zero]
  have hlocal : ∀ n z, z ∈ grQuot ℳ S n →
      ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ (⊥ : Submodule (MvPolynomial ι R) (M ⧸ S)) := by
    intro n z hz
    obtain ⟨w, hw⟩ := hsurj z
    obtain ⟨k, hk⟩ := exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul (grQuot ℳ S) i hz hw.symm
    exact ⟨k, (Submodule.mem_bot _).2 hk⟩
  refine ⟨T, fun y => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_of_homogeneous (grQuot ℳ S) ⊥ (X i) hlocal (S.mkQ y)
  refine ⟨k, (Submodule.Quotient.mk_eq_zero S).1 ?_⟩
  rw [← Submodule.mkQ_apply, map_smul]
  exact (Submodule.mem_bot _).1 hk

end GlobalTheory
