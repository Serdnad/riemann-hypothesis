import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.XSmulMemWeightedHomogeneousSubmodule
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteHomologyCubeComplexGradedModuleStatement

/-! # Finiteness of graded Čech homology -/

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_cycles_of_finite_homology {R : Type} [Ring R] {α : Type} {c : ComplexShape α}
    (K : HomologicalComplex (ModuleCat.{0} R) c) (i j : α) (hij : c.prev j = i)
    [Module.Finite R (K.X i)] [Module.Finite R (K.homology j)] :
    Module.Finite R (K.cycles j) := by
  have hex : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  exact Module.Finite.of_exact hex
    ((ModuleCat.epi_iff_surjective (K.homologyπ j)).1 inferInstance)

theorem finite_cechHomology_of_finite_cubeHomology (ι : Type) [LinearOrder ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (A : Cube.{0} ι R) (h₀ : Module.Finite R (A.obj ∅))
    (h : ∀ p, Module.Finite R ((cubeComplex A).homology p)) (p : ℕ) :
    Module.Finite R ((cechComplex A).homology p) := by
  cases p with
  | zero =>
    have h1 := h 1
    have h2 : Module.Finite R ((cubeComplex A).X 0) :=
      Module.Finite.equiv (Cube.termZeroEquiv A).symm
    have h3 := finite_cycles_of_finite_homology (cubeComplex A) 0 1 (by simp)
    exact Module.Finite.equiv
      (cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm).toLinearEquiv
  | succ p =>
    have h1 := h (p + 2)
    exact Module.Finite.equiv (cechHomologySuccIso A p).symm.toLinearEquiv

end GlobalTheory

end

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_piece_of_polyGradedSMul : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n, Module.Finite R (ℳ n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ _ n
  refine GradedHilbert.finite_piece (ι := ι) ℳ (fun i k m hm => ?_) n
  have := grSMul_mem ℳ (X_mem_polyGrading i) hm
  first
    | exact this
    | exact add_comm k 1 ▸ this
    | simpa [add_comm] using this

end GlobalTheory

end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_grCech_homology : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n p, Module.Finite R ((cechComplex (grCube ι ℳ n)).homology p) := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ hM n p
  have h₀ : Module.Finite R (ℳ n) := finite_piece_of_polyGradedSMul ι R M ℳ hM n
  have h₁ : Module.Finite R ((grCube ι ℳ n).obj ∅) :=
    Module.Finite.equiv (homLocEmptyEquiv ι ℳ n)
  exact finite_cechHomology_of_finite_cubeHomology ι R (grCube ι ℳ n) h₁
    (GlobalTheory.T.finite_homology_cubeComplex_gradedModule ι R M ℳ hM n) p

end GlobalTheory
