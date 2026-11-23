module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle030
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle065
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle069
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuum
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle070
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

section

open TensorProduct

namespace GlobalTheory

theorem exists_basicOpen_subset_of_isConstructible_of_bot_mem {B : Type*} [CommRing B] [IsDomain B]
    {s : Set (PrimeSpectrum B)} (hs : Topology.IsConstructible s)
    (h0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ s) :
    ∃ q : B, q ≠ 0 ∧ ∀ p : PrimeSpectrum B, q ∉ p.asIdeal → p ∈ s := by
  revert h0
  induction s, hs using Topology.IsConstructible.induction_of_isTopologicalBasis
      _ (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)) with
  | isCompact_basis i => exact PrimeSpectrum.isCompact_basicOpen _
  | sdiff i t ht =>
    intro h0
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      not_exists, not_not] at h0

    refine ⟨i, fun hi => h0.1 (by simp [hi]), fun p hp => ?_⟩
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      not_exists, not_not]
    refine ⟨hp, fun j hj => ?_⟩
    have hj0 : j = 0 := by simpa using h0.2 j hj
    simp [hj0]
  | union s hs t ht Hs Ht =>
    rintro (h0 | h0)
    · obtain ⟨q, hq, hsub⟩ := Hs h0
      exact ⟨q, hq, fun p hp => Or.inl (hsub p hp)⟩
    · obtain ⟨q, hq, hsub⟩ := Ht h0
      exact ⟨q, hq, fun p hp => Or.inr (hsub p hp)⟩

theorem exists_ringHom_extend_of_ker_mem_range_comap {B A L : Type*} [CommRing B] [CommRing A]
    [Algebra B A] [Algebra.FiniteType B A] [Field L] [IsAlgClosed L] (φ : B →+* L)
    (h : (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A))) :
    ∃ ψ : A →+* L, ψ.comp (algebraMap B A) = φ := by
  obtain ⟨P, hP⟩ := h
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hPp : RingHom.ker φ = P.asIdeal.comap (algebraMap B A) := by
    have := congrArg PrimeSpectrum.asIdeal hP
    simpa using this.symm

  let σ : (RingHom.ker φ).ResidueField →+* L :=
    Ideal.ResidueField.lift (RingHom.ker φ) φ le_rfl (fun x hx => by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact isUnit_iff_ne_zero.mpr fun h0 => hx (RingHom.mem_ker.mpr h0))

  let g : (RingHom.ker φ).ResidueField →ₐ[B] P.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ (RingHom.ker φ) P.asIdeal (Algebra.ofId B A) hPp
  let F : (RingHom.ker φ).ResidueField ⊗[B] A →ₐ[B] P.asIdeal.ResidueField :=
    Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom B A _) (fun _ _ => Commute.all _ _)
  have : Nontrivial ((RingHom.ker φ).ResidueField ⊗[B] A) := F.toRingHom.domain_nontrivial
  obtain ⟨χ, hχ⟩ := exists_ringHom_extend_of_finiteType (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A) L σ
  refine ⟨χ.comp (Algebra.TensorProduct.includeRight (R := B)
    (A := (RingHom.ker φ).ResidueField) (B := A)).toRingHom, RingHom.ext fun b => ?_⟩
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply B (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A), hχ]
  exact Ideal.ResidueField.lift_algebraMap _ _ _ _ _

theorem exists_ne_zero_forall_complexPoint_extend :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A]
    [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by
  intro B A _ _ _ _ _ _ _ hinj
  have hfp : (algebraMap B A).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp ‹_›)

  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨q, hq, hsub⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem
    (PrimeSpectrum.isConstructible_range_comap hfp) hgen
  exact ⟨q, hq, fun φ hφ =>
    exists_ringHom_extend_of_ker_mem_range_comap φ (hsub _ fun hk => hφ (RingHom.mem_ker.mp hk))⟩

end GlobalTheory
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_mem_span_eval_of_finiteDimensional {Y : Type} (E : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ E] (φ : Module.Dual ℂ E) :
    φ ∈ Submodule.span ℂ
      (Set.range fun y : Y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) :=
  _root_.UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional E φ

end GlobalTheory
end

section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hermitian_flag_unipotent_matrix_exists_sparse : ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * X = 0 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      u * X₁ = X₁ → u * Xb = Xb + X₁ * A →
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ (w : Fin (l + d) → ℂ) (a : Fin l → ℂ), Matrix.mulVec u v - v = Matrix.mulVec X₂ w + Matrix.mulVec X₁ a) →
      ∃ N : Matrix (Fin r) (Fin r) ℂ, u * X = X + X * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → ℂ, (∀ i : Fin r, i.val < l + d → Matrix.mulVec (X.conjTranspose * J) v i = 0) →
          ∃ w : Fin r → ℂ, (∀ i, w i ≠ 0 → i.val < l + d) ∧ Matrix.mulVec u v - v = Matrix.mulVec X w) := by
  first | exact @GlobalTheory.isotropic_unipotent_column_relations | exact GlobalTheory.isotropic_unipotent_column_relations | (intros; apply GlobalTheory.isotropic_unipotent_column_relations <;> assumption)
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory


open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
theorem _root_.GlobalTheory.hermitian_congr_involution (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0) :
    ∃ R s : Matrix ι ι ℂ, R.det ≠ 0 ∧ sᴴ = s ∧ s * s = 1 ∧ Rᴴ * s * R = H := by
  have hA : H.IsHermitian := hH
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set d := hA.eigenvalues with hdd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hdd, hi]; simp)
  set s : Matrix ι ι ℂ := diagonal fun i => if 0 < d i then 1 else -1 with hs
  set D : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt |d i| : ℝ) : ℂ) with hD
  have key : D * s * D = diagonal (RCLike.ofReal ∘ d) := by
    rw [hD, hs, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    have hsq : ((Real.sqrt |d i| : ℝ) : ℂ) * ((Real.sqrt |d i| : ℝ) : ℂ) = ((|d i| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Function.comp_apply]
    split_ifs with h
    · rw [mul_one, hsq, abs_of_pos h]; rfl
    · rw [mul_neg_one, neg_mul, hsq, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hd0 i))]
      push_cast; ring_nf; rfl
  have hDH : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]; congr 1; funext i; simp
  have hsH : sᴴ = s := by
    rw [hs, diagonal_conjTranspose]; congr 1; funext i; by_cases h : 0 < d i <;> simp [h]
  have hss : s * s = 1 := by
    rw [hs, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hR : (D * star U)ᴴ * s * (D * star U) = H := by
    rw [conjTranspose_mul, hDH, star_eq_conjTranspose, conjTranspose_conjTranspose]
    conv_rhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← key]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose]
    rfl
  refine ⟨D * star U, s, ?_, hsH, hss, hR⟩
  intro h0
  apply hd
  rw [← hR, det_mul, det_mul, h0, mul_zero]

end GlobalTheory
end

section

open MeasureTheory Matrix


theorem _root_.GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  first | exact @GlobalTheory.ghom_factors_through_det | exact GlobalTheory.ghom_factors_through_det | (intros; apply GlobalTheory.ghom_factors_through_det <;> assumption)
end

section

open scoped ComplexOrder

theorem _root_.GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary : ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  first | exact @GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | exact GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | (intros; apply GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  first | exact @GlobalTheory.herm_gamma | exact GlobalTheory.herm_gamma | (intros; apply GlobalTheory.herm_gamma <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hermitian_spectral_projections_anticommute : ∀ (n : Type) [Fintype n] [DecidableEq n] (Y J : Matrix n n ℂ), Y.IsHermitian → J * Y = -(Y * J) → ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧ (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧ N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧ J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  first | exact @GlobalTheory.hermitian_spectral_parts_anticommute | exact GlobalTheory.hermitian_spectral_parts_anticommute | (intros; apply GlobalTheory.hermitian_spectral_parts_anticommute <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.mem_span_heisenberg_translates_of_vacuum : ∀ (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M), (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ v, ρ 0 v = v) → (∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v) → (∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1) → (∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x) → (∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u) → e ≠ 0 → (∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) → (∀ u ∈ Λ, ρ (2 • u) e = e) → (∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e) → ∀ v : M, (∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) → v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  first | exact @GlobalTheory.HeisVacuum.mem_span_translates_vacuum | exact GlobalTheory.HeisVacuum.mem_span_translates_vacuum | (intros; apply GlobalTheory.HeisVacuum.mem_span_translates_vacuum <;> assumption)
end

section

open Matrix
open scoped Classical


theorem _root_.GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) → (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈ Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  first | exact @GlobalTheory.unitary_tensor_places_positions | exact GlobalTheory.unitary_tensor_places_positions | (intros; apply GlobalTheory.unitary_tensor_places_positions <;> assumption)
end

section

open Classical MvPolynomial

theorem _root_.GlobalTheory.T.unitaryGroup_family_zariski_dense : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ), (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ, MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | exact GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | (intros; apply GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense <;> assumption)
end

section


theorem _root_.GlobalTheory.T.fixed_vectors_irreducible_subrep_decomposition : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Set G) (F : Submodule ℂ V), (∀ v, v ∈ F ↔ ∀ k ∈ K, ρ k v = v) → ∀ 𝒜 : Set (Submodule ℂ V), (∀ P ∈ 𝒜, P ≠ ⊥ ∧ (∀ g, ∀ v ∈ P, ρ g v ∈ P) ∧ ∀ W : Submodule ℂ V, W ≤ P → (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = P) → FiniteDimensional ℂ ((⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V)) → ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ V), (∀ i, π i ∈ 𝒜 ∧ π i ⊓ F ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ F) ∧ (⨆ i, π i ⊓ F) = (⨆ P ∈ 𝒜, P ⊓ F) ∧ ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → ∃ i, ∃ T : V →ₗ[ℂ] V, (∀ v ∈ P, T v ∈ π i) ∧ (∀ v ∈ P, T v = 0 → v = 0) ∧ ∀ g, ∀ v ∈ P, T (ρ g v) = ρ g (T v) := by
  first | exact @GlobalTheory.AbsDec.fixed_decomposition | exact GlobalTheory.AbsDec.fixed_decomposition | (intros; apply GlobalTheory.AbsDec.fixed_decomposition <;> assumption)
end
