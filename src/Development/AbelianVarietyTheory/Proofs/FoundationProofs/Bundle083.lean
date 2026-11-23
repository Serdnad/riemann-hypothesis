module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle045
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
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
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q → ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  first | exact @GlobalTheory.algEquiv_primitiveRoot_pow | exact GlobalTheory.algEquiv_primitiveRoot_pow | (intros; apply GlobalTheory.algEquiv_primitiveRoot_pow <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.exists_kummer_generator_of_locallyConstant_hom : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (E : IntermediateField K Ω) (χ : (Ω ≃ₐ[K] Ω) → ZMod N),
  IsLocallyConstant χ → (∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, χ (g * h) = χ g + χ h) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ E ∧ ∀ g ∈ E.fixingSubgroup, g θ = ζ ^ (χ g).val * θ := by
  first | exact @GlobalTheory.kummer_generator_of_char | exact GlobalTheory.kummer_generator_of_char | (intros; apply GlobalTheory.kummer_generator_of_char <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
  ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
    ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  first | exact @GlobalTheory.norm_isHomogeneous_poly_coords | exact GlobalTheory.norm_isHomogeneous_poly_coords | (intros; apply GlobalTheory.norm_isHomogeneous_poly_coords <;> assumption)
end

section

noncomputable section

namespace GlobalTheory

open IsLocalRing TensorProduct

universe u


open IsLocalRing TensorProduct in
open WithConv in
theorem _root_.GlobalTheory.bialgHom_map_antipode {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B] (g : A →ₐc[R] B) (a : A) :
    g (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (g a) := by
  have h1 := LinearMap.algHom_comp_convMul_distrib (g : A →ₐ[R] B)
    (toConv (HopfAlgebra.antipode R)) (toConv LinearMap.id)
  have h2 := LinearMap.convMul_comp_coalgHom_distrib (toConv LinearMap.id)
    (toConv (HopfAlgebra.antipode R)) (g : A →ₗc[R] B)
  have e1 : (g : A →ₐ[R] B).toLinearMap ∘ₗ ofConv (1 : WithConv (A →ₗ[R] A)) =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp only [LinearMap.convOne_def]
    exact (g : A →ₐ[R] B).commutes _
  have e2 : ofConv (1 : WithConv (B →ₗ[R] B)) ∘ₗ (g : A →ₗc[R] B).toLinearMap =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp [LinearMap.convOne_def]
  rw [LinearMap.antipode_mul_id, e1] at h1
  rw [LinearMap.id_mul_antipode, e2] at h2
  have h := left_inv_eq_right_inv (ofConv_injective h1).symm (ofConv_injective h2).symm
  simpa using congrArg (fun f : WithConv (A →ₗ[R] B) ↦ (ofConv f) a) h


open IsLocalRing TensorProduct in
theorem _root_.GlobalTheory.henselianLocalRing_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R :=
  _root_.GlobalTheory.henselianLocalRing_of_henselianRing R


open IsLocalRing TensorProduct in
theorem _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable (R : Type u) (L : Type*) [CommRing R]
    [HenselianLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [Module.Finite (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  obtain ⟨A, _, _, hfin, het, hloc, he⟩ := _root_.GlobalTheory.exists_etale_lift_of_isSeparable R L
  exact ⟨A, inferInstance, inferInstance, hfin, het, _root_.GlobalTheory.henselianLocalRing_of_finite R A, he⟩


open IsLocalRing TensorProduct in
open CategoryTheory in
theorem _root_.GlobalTheory.finite_algebras_over_henselian (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      (∃ (ι : Type u) (_ : Finite ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
        (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
        ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i)) ∧
      ∀ c : S ⧸ (maximalIdeal R).map (algebraMap R S), IsIdempotentElem c →
        ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c) ∧
    (CommAlgCat.FiniteEtale.baseChange.{u} R (ResidueField R)).IsEquivalence ∧
    ∀ (L : Type u) [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
      [Algebra.IsSeparable (ResidueField R) L],
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
        HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  refine ⟨fun S _ _ _ ↦ ⟨_root_.GlobalTheory.exists_algEquiv_pi_henselianLocalRing R S,
    fun c hc ↦ _root_.GlobalTheory.existsUnique_idempotent_lift_quotient R hc⟩, ?_,
    fun L _ _ _ _ ↦ _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable R L⟩
  refine
    { faithful := ⟨fun {X Y} f g h ↦ ?_⟩
      full := ⟨fun {X Y} φ ↦ ?_⟩
      essSurj := ⟨fun Y ↦ ?_⟩ }
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    exact ObjectProperty.hom_ext _ (CommAlgCat.hom_ext
      ((_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).1
        (congrArg (fun φ ↦ φ.hom.hom) h)))
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    obtain ⟨f, hf⟩ := (_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).2 φ.hom.hom
    exact ⟨ObjectProperty.homMk (CommAlgCat.ofHom f),
      ObjectProperty.hom_ext _ (CommAlgCat.hom_ext hf)⟩
  · have : Algebra.Etale (ResidueField R) Y.obj := Y.property.2
    obtain ⟨A, _, _, hfin, het, ⟨e⟩⟩ := _root_.GlobalTheory.exists_etale_lift_of_etale.{u, u} R Y.obj
    exact ⟨⟨CommAlgCat.of R A, ⟨hfin, het⟩⟩, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

end GlobalTheory
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem powerSeries_to_hahnSeries_rat :
    ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  intro Ω _ N hN
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  let f : ℕ →+ ℚ := (AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Nat.castAddMonoidHom ℚ)
  have hf : ∀ k : ℕ, f k = (k : ℚ) / N := fun k => by
    simp [f, div_eq_mul_inv]
  have hfle : ∀ g g' : ℕ, f g ≤ f g' ↔ g ≤ g' := fun g g' => by
    rw [hf, hf, div_le_div_iff_of_pos_right hN', Nat.cast_le]
  have hfi : Function.Injective f := fun g g' h =>
    le_antisymm ((hfle g g').1 h.le) ((hfle g' g).1 h.ge)
  refine ⟨(HahnSeries.embDomainRingHom f hfi hfle).comp
    (HahnSeries.toPowerSeries (R := Ω)).symm.toRingHom, ?_, ?_⟩
  · intro p k
    rw [← hf]
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    rw [HahnSeries.embDomain_mk_coeff]
    rfl
  · intro p r hr
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨k, -, hk⟩
    exact hr k (by rw [← hf]; exact hk.symm)

end GlobalTheory
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span : ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω) (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 → (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  first | exact @GlobalTheory.valuation_eq_one_of_pow_eq_span | exact GlobalTheory.valuation_eq_one_of_pow_eq_span | (intros; apply GlobalTheory.valuation_eq_one_of_pow_eq_span <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.gaussExtension_coeff_mem_nonunits_alt : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L), (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) → (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1) → ∀ (Ψ : Polynomial (Polynomial V)) (ω : L), Ψ.Monic → (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0) → ∀ R : Polynomial (Polynomial F), R.natDegree < Ψ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
  first | exact @GlobalTheory.gaussExtension_coeff_mem_nonunits | exact GlobalTheory.gaussExtension_coeff_mem_nonunits | (intros; apply GlobalTheory.gaussExtension_coeff_mem_nonunits <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.valuationSubring_le_of_residue_independent : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic → (∀ i j, (Φ.coeff i).coeff j ∈ V) → Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω) → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → (∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W₁.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits) → W₁ ≤ W₂ := by
  first | exact @GlobalTheory.BertiniNoether.le_of_residue_independent | exact GlobalTheory.BertiniNoether.le_of_residue_independent | (intros; apply GlobalTheory.BertiniNoether.le_of_residue_independent <;> assumption)
end
