module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Mathlib.RingTheory.IsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle218
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle219
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

open IsLocalRing

theorem locallyConstant_eq_of_specializes {Y Λ : Type*} [TopologicalSpace Y]
    (φ : LocallyConstant Y Λ) {y y' : Y} (h : y ⤳ y') : φ y = φ y' :=
  h.mem_open (φ.isLocallyConstant.isOpen_fiber (φ y')) rfl

theorem mem_iff_of_specializes_of_isClopen {Y : Type*} [TopologicalSpace Y] {V : Set Y}
    (hV : IsClopen V) {y y' : Y} (h : y ⤳ y') : y ∈ V ↔ y' ∈ V :=
  ⟨fun hy ↦ h.mem_closed hV.1 hy, fun hy ↦ h.mem_open hV.2 hy⟩

theorem bijective_locallyConstant_comap_of_specializes_of_isClopen {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (Λ : Type*) (f : C(X, Y))
    (h1 : ∀ y : Y, ∃ x : X, y ⤳ f x)
    (h2 : ∀ U : Set X, IsClopen U → ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = U) :
    Function.Bijective (fun φ : LocallyConstant Y Λ ↦ φ.comap f) := by
  choose g hg using h1
  refine ⟨fun φ ψ hφψ ↦ ?_, fun ψ ↦ ?_⟩
  · ext y
    have h : (φ.comap f) (g y) = (ψ.comap f) (g y) := by
      rw [show φ.comap f = ψ.comap f from hφψ]
    rw [locallyConstant_eq_of_specializes φ (hg y), locallyConstant_eq_of_specializes ψ (hg y)]
    simpa using h
  · have key : ∀ l : Λ, ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = {x | ψ x = l} ∧
        (fun y ↦ ψ (g y)) ⁻¹' {l} = V := by
      intro l
      obtain ⟨V, hV, hVU⟩ := h2 _ (ψ.isLocallyConstant.isClopen_fiber l)
      refine ⟨V, hV, hVU, ?_⟩
      ext y
      show ψ (g y) = l ↔ y ∈ V
      rw [mem_iff_of_specializes_of_isClopen hV (hg y)]
      change ψ (g y) = l ↔ g y ∈ f ⁻¹' V
      rw [hVU]
      rfl
    refine ⟨⟨fun y ↦ ψ (g y), IsLocallyConstant.iff_isOpen_fiber.2 fun l ↦ ?_⟩, ?_⟩
    · obtain ⟨V, hV, -, hV'⟩ := key l
      rw [hV']
      exact hV.2
    · ext x
      obtain ⟨V, -, hVU, hV'⟩ := key (ψ x)
      have hx : x ∈ f ⁻¹' V := by rw [hVU]; rfl
      rw [← hV'] at hx
      exact hx

theorem map_maximalIdeal_le_of_isIntegral (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (M : Ideal B) [M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A B) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  have : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem exists_isIdempotentElem_lift_quotient_of_isIntegral (A B : Type) [CommRing A]
    [HenselianLocalRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    {c : B ⧸ (maximalIdeal A).map (algebraMap A B)} (hc : IsIdempotentElem c) :
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc.eq, sub_self]
  have hb' : b * b - b ∈ Submodule.span B (algebraMap A B '' (maximalIdeal A : Set A)) := hb
  obtain ⟨n, r, s, hs⟩ := Submodule.mem_span_set'.1 hb'
  choose a ha hsa using fun i ↦ (s i).2
  set B₀ := Algebra.adjoin A (insert b (Set.range r)) with hB₀
  haveI : Module.Finite A B₀ := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_range r).insert b) fun x _ ↦ Algebra.IsIntegral.isIntegral x
  let b₀ : B₀ := ⟨b, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let r₀ : Fin n → B₀ := fun i ↦ ⟨r i, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩
  have hsum : b₀ * b₀ - b₀ = ∑ i, r₀ i * algebraMap A B₀ (a i) := by
    apply Subtype.ext
    show b * b - b = B₀.val (∑ i, r₀ i * algebraMap A B₀ (a i))

    rw [map_sum, ← hs]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, AlgHom.commutes, hsa i, smul_eq_mul]
    rfl
  have hb₀ : b₀ * b₀ - b₀ ∈ (maximalIdeal A).map (algebraMap A B₀) := by
    rw [hsum]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  obtain ⟨e₀, ⟨he₀, he₀b⟩, -⟩ := existsUnique_idempotent_lift_quotient A (S := B₀)
    (c := Ideal.Quotient.mk _ b₀) (by
      show Ideal.Quotient.mk _ b₀ * Ideal.Quotient.mk _ b₀ = Ideal.Quotient.mk _ b₀
      rw [← map_mul, Ideal.Quotient.eq]
      exact hb₀)
  refine ⟨(e₀ : B), he₀.map B₀.val, ?_⟩
  have h := Ideal.mem_map_of_mem (B₀.val : B₀ →+* B) (Ideal.Quotient.eq.1 he₀b)
  rw [Ideal.map_map, AlgHom.comp_algebraMap] at h
  rw [Ideal.Quotient.eq]
  simpa using h

theorem bijective_locallyConstant_comap_algebraicClosure_tensor : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  intro Λ A _ _ _ _ B _ _ _
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  let ιk : B →ₐ[A] k ⊗[A] B := Algebra.TensorProduct.includeRight
  let μ : k ⊗[A] B →+* Ω ⊗[A] B :=
    (Algebra.TensorProduct.map (Algebra.ofId k Ω) (AlgHom.id A B)).toRingHom
  have hμ : IsHomeomorph (PrimeSpectrum.comap μ) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable (R := A) (K := k)
      (S := B) Ω
  have hIk : ∀ x ∈ I, ιk x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker ιk := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show ιk (algebraMap A B a) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
        show algebraMap A k a = 0 from (IsLocalRing.residue_eq_zero_iff a).2 ha, zero_tmul]
    exact hle hx
  let e' : B ⧸ I →+* k ⊗[A] B := Ideal.Quotient.lift I ιk.toRingHom hIk
  have he'mk : ∀ b : B, e' (Ideal.Quotient.mk I b) = ιk b := fun b ↦ rfl
  let σ : k →ₐ[A] B ⧸ I := Ideal.Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A (B ⧸ I))
    fun a ha ↦ by
      rw [Algebra.ofId_apply]
      show Ideal.Quotient.mk I (algebraMap A B a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  let τ : k ⊗[A] B →ₐ[A] B ⧸ I :=
    Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ A I) fun _ _ ↦ Commute.all _ _
  have hτ : ∀ q, τ (e' q) = q := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [he'mk]
    show τ ((1 : k) ⊗ₜ[A] b) = _
    simp [τ]
  have he' : Function.Bijective e' := by
    refine ⟨Function.LeftInverse.injective hτ, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := includeRight_residueField_surjective A B y
    exact ⟨Ideal.Quotient.mk I b, rfl⟩
  let ρ : B ⧸ I →+* Ω ⊗[A] B := μ.comp e'
  have hρ : IsHomeomorph (PrimeSpectrum.comap ρ) := by
    rw [PrimeSpectrum.comap_comp]
    exact (PrimeSpectrum.isHomeomorph_comap_of_bijective he').comp hμ
  have hfac : ∀ x : PrimeSpectrum (Ω ⊗[A] B),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x =
        PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap ρ x) := by
    intro x
    have : (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom =
        ρ.comp (Ideal.Quotient.mk I) := by
      ext b
      show (1 : Ω) ⊗ₜ[A] b = μ ((1 : k) ⊗ₜ[A] b)
      simp [μ]
    rw [this]
    rfl
  apply bijective_locallyConstant_comap_of_specializes_of_isClopen
  · intro y
    obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    have hIM : I ≤ M := map_maximalIdeal_le_of_isIntegral A B M
    haveI := hM.isPrime
    let P : PrimeSpectrum (B ⧸ I) := ⟨M.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
    have hPM : (PrimeSpectrum.comap (Ideal.Quotient.mk I) P).asIdeal = M := by
      show (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hIM]
    obtain ⟨x, hx⟩ := hρ.surjective P
    refine ⟨x, ?_⟩
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
    show y.asIdeal ≤ (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x).asIdeal
    rw [hfac, hx, hPM]
    exact hyM
  · intro U hU
    have hU' : IsClopen (PrimeSpectrum.comap ρ '' U) :=
      ⟨hρ.isClosedMap U hU.1, hρ.isOpenMap U hU.2⟩
    set c := PrimeSpectrum.isIdempotentElemEquivClopens.symm ⟨_, hU'⟩ with hc
    obtain ⟨e, he, hec⟩ := exists_isIdempotentElem_lift_quotient_of_isIntegral A B c.2
    have hU'c : (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I e) : Set (PrimeSpectrum (B ⧸ I))) =
        PrimeSpectrum.comap ρ '' U := by
      rw [hec]
      exact congrArg SetLike.coe (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _)
    refine ⟨PrimeSpectrum.basicOpen e, ?_, ?_⟩
    · have := (PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩).isClopen
      rwa [PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply] at this
    · ext x
      change PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x ∈
        PrimeSpectrum.basicOpen e ↔ x ∈ U
      rw [hfac, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
        ← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, hU'c, hρ.injective.mem_set_image]

end GlobalTheory
end
end

section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  first | (exact @GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (exact GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (intros; apply GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul  <;> assumption)
end

section

open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_baseChange : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L]
    [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f →
    ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) →
      finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧
        (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  intro K L V W ι _ _ _ _ _ _ _ _ _ _ _ f hf a a' ha
  refine ⟨GlobalTheory.finrank_iInf_ker_of_isBaseChange K L V W ι f a a' hf ha, ?_⟩
  rw [GlobalTheory.GaloisDescent.span_image_iInf hf]
  exact iInf_congr fun i =>
    (GlobalTheory.GaloisDescent.span_image_ker hf hf (a i) (a' i) (fun v => ha i v)).symm

end GlobalTheory.BadCount
end

section

open IsLocalRing

namespace GlobalTheory

theorem c_one_of_finite_extension : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → (∀ (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) := by
  intro K L _ _ _ _ hK n d f hf hd hdn
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.T.exists_isHomogeneous_eval_eq_norm K L n d f hf
  have hm0 : 0 < Module.finrank K L := Module.finrank_pos
  let e : Fin n × Fin (Module.finrank K L) ≃ Fin (n * Module.finrank K L) := finProdFinEquiv
  have hG : (MvPolynomial.rename e F).IsHomogeneous (d * Module.finrank K L) := hFh.rename_isHomogeneous
  obtain ⟨z, hz0, hz⟩ := hK (n * Module.finrank K L) (d * Module.finrank K L) (MvPolynomial.rename e F) hG
    (Nat.mul_pos hd hm0) (Nat.mul_lt_mul_of_pos_right hdn hm0)
  set y : Fin n × Fin (Module.finrank K L) → K := z ∘ e with hy
  rw [MvPolynomial.eval_rename] at hz
  have hy0 : y ≠ 0 := by
    intro h
    apply hz0
    funext k
    have := congrFun h (e.symm k)
    simpa [hy] using this
  refine ⟨fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j, ?_, ?_⟩
  · intro hx
    apply hy0
    funext ⟨i, j⟩
    have hi := congrFun hx i
    simp only [Pi.zero_apply] at hi
    have hli := (Module.finBasis K L).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun j => y (i, j)) (by simpa [Algebra.smul_def] using hi) j
    simpa using this
  · have := hFe y
    rw [hz] at this
    exact (Algebra.norm_eq_zero_iff (R := K)).mp this.symm

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory

theorem weighted_det_divergence_mem_ideal : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R) (δ0 : Derivation K R R) (I : Ideal R) (M : Matrix ι ι R) (a b : ι → R) (w t ρ : R), (∀ i j, δ0 (M i j) = δ i (a j)) → (∀ h i j, δ h (M i j) = δ i (M h j)) → δ0 w = 0 → (∀ i, δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j ∈ I) → ρ = ∑ j, b j * a j → δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * ∑ j, M.adjugate j i * a j) + t * δ i ρ * (w * ∑ j, M.adjugate j i * a j)) ∈ I := by
  intro K R _ _ _ ι _ _ δ δ0 I M a b w t ρ h0 hM hw hI hρ
  set c : ι → R := fun i => ∑ j, M.adjugate j i * a j with hc
  have hdet : δ0 M.det = ∑ i, δ i (c i) := by
    rw [GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry δ0 M]
    have hp := GlobalTheory.T.piola_identity_adjugate_divergence_free δ M hM
    have h1 : ∀ i, δ i (c i) = ∑ j, M.adjugate j i * δ0 (M i j) + ∑ j, a j * δ i (M.adjugate j i) := by
      intro i

      simp only [hc, map_sum, Derivation.leibniz, smul_eq_mul, h0, Finset.sum_add_distrib]
    have h2 : ∑ i, ∑ j, a j * δ i (M.adjugate j i) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum, hp j, mul_zero]
    simp only [h1, Finset.sum_add_distrib, h2, add_zero]
  have hadj : ∀ k, ∑ i, c i * M i k = M.det * a k := by
    intro k
    have h3 : ∀ j, ∑ i, M.adjugate j i * M i k = if j = k then M.det else 0 := by
      intro j
      have := congrFun (congrFun (Matrix.adjugate_mul M) j) k
      rw [Matrix.mul_apply] at this
      rw [this, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    calc ∑ i, c i * M i k = ∑ j, a j * ∑ i, M.adjugate j i * M i k := by
          simp only [hc, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = M.det * a k := by
          simp only [h3, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  have hrho : ∑ i, c i * (w * ∑ j, M i j * b j) = ρ * (w * M.det) := by
    calc ∑ i, c i * (w * ∑ j, M i j * b j) = ∑ j, w * b j * ∑ i, c i * M i j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ρ * (w * M.det) := by
          rw [hρ, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by rw [hadj]; ring
  have key : δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i))
      = - ∑ i, c i * (δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j) := by
    rw [Derivation.leibniz, hw, smul_zero, add_zero, smul_eq_mul, hdet, ← hrho, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  change δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i)) ∈ I
  rw [key]
  exact I.neg_mem (I.sum_mem fun i _ => I.mul_mem_left _ (hI i))

end GlobalTheory
end

section

open scoped Matrix

namespace GlobalTheory

theorem exists_skewHermitian_mul_add_det_ne_zero_of_pair :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n C D hCD hrk
  obtain ⟨U, P, e, hU, hP, he, hE⟩ := GlobalTheory.T.exists_rank_normal_form_matrix_field k n C
  have hmul : ∀ A B : Matrix (Fin n) (Fin n) k,
      ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
    intro A B
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hinv : ∀ A : Matrix (Fin n) (Fin n) k, (((A.map σ)ᵀ).map σ)ᵀ = A := by
    intro A
    ext i j
    simp [hσ]
  have hone : (((1 : Matrix (Fin n) (Fin n) k).map σ)ᵀ) = 1 := by
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have h3 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUu
  set E : Matrix (Fin n) (Fin n) k := Matrix.diagonal e with hEdef
  have hEE : E * E = E := by
    rw [hEdef, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  have hEs : (E.map σ)ᵀ = E := by
    rw [hEdef, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  set Q : Matrix (Fin n) (Fin n) k := (P⁻¹.map σ)ᵀ with hQ
  set Ps : Matrix (Fin n) (Fin n) k := (P.map σ)ᵀ with hPs
  have hPQ : Ps * Q = 1 := by rw [hPs, hQ, ← hmul, h2, hone]
  have hQP : Q * Ps = 1 := by rw [hPs, hQ, ← hmul, h1, hone]
  have hQs : (Q.map σ)ᵀ = P⁻¹ := hinv _
  have hE' : E = Ps * ((C.map σ)ᵀ * (U.map σ)ᵀ) := by
    rw [← hEs, ← hE, hmul, hmul]
  have hA : E * ((U * D * Q).map σ)ᵀ = U * (C * (D.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hmul, hmul, hQs, ← hE]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, h1, Matrix.one_mul]
  have hB : U * D * Q * E = U * (D * (C.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hE']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQP, Matrix.one_mul]
  have hsum : E * ((U * D * Q).map σ)ᵀ + U * D * Q * E = 0 := by
    rw [hA, hB, ← Matrix.add_mul, ← Matrix.mul_add, hCD, Matrix.mul_zero, Matrix.zero_mul]
  have hrk' : ∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* (U * D * Q) = 0 → a = 0 := by
    intro a ha hb
    have e1 : U * C = E * P⁻¹ := by
      rw [← hE, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : U * D = (U * D * Q) * Ps := by
      rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have h0 : a ᵥ* U = 0 := by
      apply hrk
      · rw [Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      · rw [Matrix.vecMul_vecMul, e2, ← Matrix.vecMul_vecMul, hb, Matrix.zero_vecMul]
    have : a ᵥ* (U * U⁻¹) = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
    rwa [h3, Matrix.vecMul_one] at this
  obtain ⟨V', hV', hdet⟩ := GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent k σ hσ ε hε hσε n E (U * D * Q) hEE hEs hsum hrk'
  refine ⟨P * V' * Ps, ?_, ?_⟩
  · have hPss : (Ps.map σ)ᵀ = P := hinv _
    rw [hmul, hmul, hV', hPss, ← hPs]
    simp [Matrix.mul_assoc]
  · intro h
    apply hdet
    have : E * V' + U * D * Q = U * (C * (P * V' * Ps) + D) * Q := by
      rw [← hE, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one]
    rw [this, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]

end GlobalTheory
end

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1 → ∀ (Q : K[X]) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q)) → LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧ Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) = LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧ (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first | exact @GlobalTheory.unitary_conj_ker_basis_gram | exact GlobalTheory.unitary_conj_ker_basis_gram | (intros; apply GlobalTheory.unitary_conj_ker_basis_gram <;> assumption)
end
