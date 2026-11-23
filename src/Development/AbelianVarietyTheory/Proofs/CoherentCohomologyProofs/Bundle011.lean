module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsGradedMapLinearCombination
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
theorem _root_.GlobalTheory.exists_homogeneous_family_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ], (∀ i : ι, ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M)) → ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) ∧ ∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ hT
  choose T hT using hT
  choose S hS using fun m : M => _root_.GlobalTheory.exists_sum_grProj ℳ m
  classical
  let G : Finset (ℤ × M) := (Finset.univ.biUnion T).biUnion fun t =>
    (S t).image fun j => (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t)
  refine ⟨G.card, fun l => (G.equivFin.symm l).1.1, fun l => (G.equivFin.symm l).1.2,
    fun l => ?_, fun i y => ?_⟩
  · have hmem := (G.equivFin.symm l).2
    obtain ⟨t, -, hj⟩ := Finset.mem_biUnion.1 hmem
    obtain ⟨j, -, hjeq⟩ := Finset.mem_image.1 hj
    show (G.equivFin.symm l : ℤ × M).2 ∈ ℳ (G.equivFin.symm l : ℤ × M).1
    rw [← hjeq]
    exact _root_.GlobalTheory.GradedHilbert.proj_mem ℳ j t
  · obtain ⟨k, hk⟩ := hT i y
    refine ⟨k, Submodule.span_le.2 ?_ hk⟩
    intro t ht
    rw [← hS t]
    refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
    have hG : (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t) ∈ G :=
      Finset.mem_biUnion.2 ⟨t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩,
        Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
    exact ⟨G.equivFin ⟨_, hG⟩, by simp⟩

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

open CategoryTheory CategoryTheory.Limits TensorProduct Function

namespace GlobalTheory

theorem exists_smul_mem_range_of_exact_fibre {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [Module.Finite R B] [Module.Projective R B] [Module.Finite R C] [Module.Projective R C]
    (K : Type*) [Field K] [Algebra R K] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor K) (g.lTensor K)) (b : B) (hb : g b = 0) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧ r • b ∈ LinearMap.range f := by
  let P : Ideal R := RingHom.ker (algebraMap R K)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  let O := Localization.AtPrime P
  have h1 := (exact_lTensor_iff_residueField P K rfl f g).1 h
  have h2 : Exact (AlgebraTensorModule.lTensor O P.ResidueField f)
      (AlgebraTensorModule.lTensor O P.ResidueField g) ↔
      Exact ((f.baseChange O).lTensor P.ResidueField) ((g.baseChange O).lTensor P.ResidueField) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField C)
      (by ext; simp) (by ext; simp)
  have h3 := h2.1 h1
  have hfg' : g.baseChange O ∘ₗ f.baseChange O = 0 := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero]
  obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField hfg'
    (fun m _ => forall_exact_residueField_of_isLocalRing h3 m)
  have h4 := exact_of_homotopy hfg' hst
  obtain ⟨x, hx⟩ := (h4 ((1 : O) ⊗ₜ[R] b)).1 (by simp [hb])
  obtain ⟨⟨a, u⟩, ha⟩ := IsLocalizedModule.surj P.primeCompl (TensorProduct.mk R O A 1) x
  have h5 : TensorProduct.mk R O B 1 ((u : R) • b) = TensorProduct.mk R O B 1 (f a) := by
    have := congrArg (f.lTensor O) ha
    rw [Submonoid.smul_def, map_smul] at this
    have hx' : f.lTensor O x = (1 : O) ⊗ₜ[R] b := hx
    rw [hx'] at this
    simpa using this
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) h5
  refine ⟨(v * u : P.primeCompl), (v * u).2, (v : R) • a, ?_⟩
  rw [map_smul, Submonoid.coe_mul, mul_smul]
  exact hv.symm


set_option backward.isDefEq.respectTransparency false in
theorem exists_smul_homology_eq_zero_of_acyclic_fibre (R : Type) [CommRing R] [IsNoetherianRing R]
    (K : Type) [Field K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hac : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic)
    (p : ℕ) : ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0 := by
  letI : Algebra R K := χ.toAlgebra
  obtain ⟨L, φ, -, h2, -, h4, h5, -, h7⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} C n hn hflat hfin
  have h8 : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) := h7 K
  have h9 : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj L).ExactAt p :=
    (exactAt_iff_of_quasiIsoAt
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) p).2 (hac p)
  have h10 : Exact ((L.sc p).f.hom.lTensor K) ((L.sc p).g.hom.lTensor K) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h9
  have hpt : ∀ z : L.homology p, ∃ r : R, χ r ≠ 0 ∧ r • z = 0 := by
    intro z
    let e := (L.sc p).moduleCatHomologyIso.toLinearEquiv
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (e z)
    haveI : Module.Finite R (L.sc p).X₂ := h2 _
    haveI : Module.Finite R (L.sc p).X₃ := h2 _
    haveI : Module.Projective R (L.sc p).X₂ := h4 _
    haveI : Module.Projective R (L.sc p).X₃ := h4 _
    obtain ⟨r, hr, a, ha⟩ := exists_smul_mem_range_of_exact_fibre K
      (congrArg ModuleCat.Hom.hom (L.sc p).zero) h10 b.1 b.2
    refine ⟨r, hr, e.injective ?_⟩
    rw [map_smul, map_zero, ← hb]
    exact (Submodule.Quotient.mk_eq_zero _).2 (show r • b ∈ _ from ⟨a, Subtype.ext ha⟩)
  let e := (isoOfQuasiIsoAt φ p).toLinearEquiv
  let P : PrimeSpectrum R := ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩
  have hP : P ∉ Module.support R (C.homology p) := by
    rw [Module.notMem_support_iff']
    intro z
    obtain ⟨r, hr, hz⟩ := hpt (e.symm z)
    refine ⟨r, hr, ?_⟩
    rw [← e.apply_symm_apply z, ← map_smul, hz, map_zero]
  haveI := hfin p
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hP
  obtain ⟨r, hr, hr'⟩ := hP
  exact ⟨r, hr', Module.mem_annihilator.1 hr⟩

end GlobalTheory
end
