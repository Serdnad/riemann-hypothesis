module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
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

open TensorProduct Module Function Filter Topology

namespace GlobalTheory

open Semicont

section FiniteModule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_away_equiv_of_eventually_finrank_fiber_eq [IsReduced R] [Module.Finite R M]
    (p : PrimeSpectrum R)
    (h : ∀ᶠ q : PrimeSpectrum R in 𝓝 p,
      finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) =
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    ∃ f ∉ p.asIdeal, Nonempty
      ((Fin (finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) →
        Localization.Away f) ≃ₗ[Localization.Away f] LocalizedModule.Away f M) := by
  obtain ⟨φ, hφ⟩ := exists_baseChange_surjective (R := R) (M := M) p.asIdeal.ResidueField
  have h1 := h.and ((isOpen_setOf_baseChange_surjective φ).mem_nhds hφ)
  obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 h1
  have hker : ∀ x, φ x = 0 → f • x = 0 := by
    intro x hx
    ext j
    refine IsReduced.eq_zero _ (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
    by_cases hfJ : f ∈ J
    · exact J.mul_mem_right _ hfJ
    obtain ⟨h2, h3⟩ := hf (show (⟨J, hJ⟩ : PrimeSpectrum R) ∈ _ from hfJ)
    have hinj : Injective (φ.baseChange J.ResidueField) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((finrank_baseChange_fin _ _).trans h2.symm)).2 h3
    have h4 : (1 : J.ResidueField) ⊗ₜ[R] x = 0 := hinj (by simp [hx])
    have h5 :=
      congrFun (congrArg (TensorProduct.piScalarRight R J.ResidueField J.ResidueField _) h4) j
    refine J.mul_mem_left _ ?_
    rw [← Ideal.algebraMap_residueField_eq_zero]
    simpa [Algebra.smul_def] using h5
  let A := Localization.Away f
  have hsurj : Surjective (φ.baseChange A) := by
    rw [baseChange_surjective_iff]
    have : Subsingleton (LocalizedModule.Away f (M ⧸ LinearMap.range φ)) := by
      rw [LocalizedModule.subsingleton_iff_disjoint, Set.disjoint_left]
      intro q hq
      have h3 : Surjective (φ.baseChange q.asIdeal.ResidueField) := (hf hq).2
      rwa [baseChange_surjective_iff, ← not_nontrivial_iff_subsingleton,
        ← Module.mem_support_iff_nontrivial_residueField_tensorProduct] at h3
    exact (LocalizedModule.equivTensorProduct (Submonoid.powers f) _).symm.toEquiv.subsingleton
  have hinj : Injective (φ.baseChange A) := by
    have : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
    rw [← LinearMap.ker_eq_bot, ← baseChange_ker, Submodule.baseChange_eq_span, eq_bot_iff,
      Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hu : IsUnit (algebraMap R A f) := IsLocalization.Away.algebraMap_isUnit f
    refine (hu.smul_eq_zero).1 ?_
    rw [algebraMap_smul, ← map_smul, hker x hx, map_zero]
  exact ⟨f, hpf, ⟨(TensorProduct.piScalarRight R A A _).symm ≪≫ₗ
    LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩ ≪≫ₗ
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm⟩⟩

theorem finitePresentation_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.FinitePresentation R M := by
  refine Module.FinitePresentation.of_localizationSpan
    {f | Module.FinitePresentation (Localization.Away f) (LocalizedModule.Away f M)} ?_
    fun g => g.2
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_away_equiv_of_eventually_finrank_fiber_eq (M := M)
    ⟨m, hm.isPrime⟩ (h.eventually_eq _)
  exact hf (hle (Ideal.subset_span (Module.FinitePresentation.of_equiv e)))

theorem projective_of_finite_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Projective R M :=
  have := finitePresentation_of_isLocallyConstant_finrank_fiber h
  projective_of_isLocallyConstant_finrank_fiber h

theorem finrank_tensorProduct_eq_finrank_fiber (k : Type*) [Field k] [Algebra R k]
    (p : PrimeSpectrum R) (hp : p.asIdeal = RingHom.ker (algebraMap R k)) :
    finrank k (k ⊗[R] M) = finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  letI : Algebra p.asIdeal.ResidueField k :=
    (Ideal.ResidueField.lift p.asIdeal (algebraMap R k) hp.le (fun x hx => by
      refine IsUnit.mk0 _ fun h0 => hx ?_
      rw [hp]
      exact h0)).toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField k :=
    IsScalarTower.of_algebraMap_eq fun x => (Ideal.ResidueField.lift_algebraMap ..).symm
  rw [← (AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField k k M).finrank_eq,
    Module.finrank_baseChange]

end FiniteModule

section Map

variable {R : Type*} [CommRing R] {E F : Type*} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

theorem finrank_baseChange_coker_add_finrank_range [Module.Finite R F]
    (k : Type*) [Field k] [Algebra R k] (φ : E →ₗ[R] F) :
    finrank k (k ⊗[R] (F ⧸ LinearMap.range φ)) + finrank k (LinearMap.range (φ.baseChange k)) =
      finrank k (k ⊗[R] F) := by
  rw [(baseChangeQuotEquiv k _).finrank_eq, baseChange_range]
  exact Submodule.finrank_quotient_add_finrank _

theorem projective_coker_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    Module.Projective R (F ⧸ LinearMap.range φ) := by
  refine projective_of_finite_of_isLocallyConstant_finrank_fiber
    ((IsLocallyConstant.iff_eventually_eq _).2 fun p => ?_)
  filter_upwards [h.eventually_eq p, (Semicont.isLocallyConstant_finrank_fiber F).eventually_eq p]
    with q h1 h2
  have h3 := finrank_baseChange_coker_add_finrank_range p.asIdeal.ResidueField φ
  have h4 := finrank_baseChange_coker_add_finrank_range q.asIdeal.ResidueField φ
  omega

theorem exists_comp_comp_eq_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    ∃ s : F →ₗ[R] E, φ ∘ₗ s ∘ₗ φ = φ :=
  have := projective_coker_of_isLocallyConstant_finrank_range φ h
  exists_comp_comp_eq_of_projective φ

theorem exists_retraction_ker_of_generalizedInverse (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) :
    ∃ r : E →ₗ[R] LinearMap.ker φ, r ∘ₗ (LinearMap.ker φ).subtype = LinearMap.id := by
  have hs' : ∀ x, φ (s (φ x)) = φ x := LinearMap.congr_fun hs
  refine ⟨(LinearMap.id - s ∘ₗ φ).codRestrict _ fun x => by simp [hs'], ?_⟩
  ext x
  simp

theorem lTensor_subtype_injective_of_retraction (P : Submodule R E) (r : E →ₗ[R] P)
    (hr : r ∘ₗ P.subtype = LinearMap.id) (N : Type*) [AddCommGroup N] [Module R N] :
    Injective (P.subtype.lTensor N) :=
  LeftInverse.injective (g := r.lTensor N) fun x => by
    rw [← LinearMap.lTensor_comp_apply, hr, LinearMap.lTensor_id, LinearMap.id_apply]

theorem baseChange_ker_of_comp_comp_eq (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) (S : Type*) [CommRing S] [Algebra R S] :
    (LinearMap.ker φ).baseChange S = LinearMap.ker (φ.baseChange S) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]
  · intro hz
    obtain ⟨y, hy⟩ := (tensorKer_bijective_of_comp_comp_eq S S φ s hs).2 ⟨z, hz⟩
    exact ⟨y, (LinearMap.tensorKer_coe S S φ y).symm.trans (congrArg Subtype.val hy)⟩

universe u v

end Map

universe u v w

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNTwist

noncomputable def twistMap {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : HahnSeries ℚ Ω' where
  coeff r := χ r * s (h.coeff r)
  isPWO_support' := h.isPWO_support.mono (by
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro h0
    exact hr (by rw [h0, map_zero, mul_zero]))

lemma twistMap_coeff {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) (r : ℚ) : (twistMap s χ h).coeff r = χ r * s (h.coeff r) := rfl

lemma twistMap_support {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : (twistMap s χ h).support ⊆ h.support := by
  intro r hr
  simp only [HahnSeries.mem_support, twistMap_coeff, ne_eq] at hr ⊢
  intro h0
  exact hr (by rw [h0, map_zero, mul_zero])

noncomputable def twistHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h0 : χ 0 = 1) (hadd : ∀ r r', χ (r + r') = χ r * χ r') :
    HahnSeries ℚ Ω →+* HahnSeries ℚ Ω' where
  toFun := twistMap s χ
  map_one' := by
    ext r
    rw [twistMap_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs with hr
    · subst hr; simp [h0]
    · simp
  map_zero' := by
    ext r
    simp [twistMap_coeff]
  map_add' x y := by
    ext r
    simp [twistMap_coeff, mul_add]
  map_mul' x y := by
    ext a
    show (twistMap s χ (x * y)).coeff a = (twistMap s χ x * twistMap s χ y).coeff a

    rw [twistMap_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    have hsub : Finset.antidiagonal (twistMap s χ x).isPWO_support (twistMap s χ y).isPWO_support a ⊆
        Finset.antidiagonal x.isPWO_support y.isPWO_support a :=
      fun ij hij => (Finset.antidiagonal_mono_right (twistMap_support s χ y))
        ((Finset.antidiagonal_mono_left (twistMap_support s χ x)) hij)
    rw [Finset.sum_subset hsub (fun ij hbig hij => ?_)]
    · refine Finset.sum_congr rfl (fun ij hij => ?_)
      have hsum : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hij).2.2
      rw [twistMap_coeff, twistMap_coeff, map_mul, ← hsum, hadd]
      ring
    · have hs : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hbig).2.2
      by_cases h1 : (twistMap s χ x).coeff ij.1 = 0
      · rw [h1, zero_mul]
      · by_cases h2 : (twistMap s χ y).coeff ij.2 = 0
        · rw [h2, mul_zero]
        · exact absurd (Finset.mem_antidiagonal.mpr ⟨h1, h2, hs⟩) hij

end GlobalTheory.FNTwist

theorem GlobalTheory.FNTwist.exists_scale_twist_ringHom : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (s : Ω →+* Ω') (l : ℚ) (χ : ℚ → Ω'), 0 < l → χ 0 = 1 → (∀ r r', χ (r + r') = χ r * χ r') → ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω', ∀ h r, (Φ h).coeff (r * l) = χ r * s (h.coeff r) := by
  intro Ω Ω' _ _ s l χ hl h0 hadd
  have hinj : Function.Injective (AddMonoidHom.mulRight l) := by
    intro a b hab
    simpa [AddMonoidHom.coe_mulRight, hl.ne'] using hab
  have hmono : ∀ g g' : ℚ, AddMonoidHom.mulRight l g ≤ AddMonoidHom.mulRight l g' ↔ g ≤ g' := by
    intro g g'
    simp only [AddMonoidHom.coe_mulRight]
    exact mul_le_mul_iff_of_pos_right hl
  refine ⟨(HahnSeries.embDomainRingHom (AddMonoidHom.mulRight l) hinj hmono).comp
    (GlobalTheory.FNTwist.twistHom s χ h0 hadd), fun h r => ?_⟩
  rw [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
  have := HahnSeries.embDomain_coeff (f := ⟨⟨AddMonoidHom.mulRight l, hinj⟩, hmono _ _⟩)
    (x := GlobalTheory.FNTwist.twistHom s χ h0 hadd h) (a := r)
  rw [show χ r * s (h.coeff r) = (GlobalTheory.FNTwist.twistHom s χ h0 hadd h).coeff r from rfl]
  simpa using this
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HahnSub

theorem coeff_mul_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h h' : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hh' : ∀ r, h'.coeff r ∈ A) (r : ℚ) : (h * h').coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact A.sum_mem fun ij _ => A.mul_mem (hh ij.1) (hh' ij.2)

theorem coeff_inv_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hl : h.leadingCoeff⁻¹ ∈ A) (r : ℚ) : (h⁻¹).coeff r ∈ A := by
  by_cases h0 : h = 0
  · subst h0
    simp

  let g : HahnSeries ℚ A :=
    { coeff := fun s => ⟨h.coeff s, hh s⟩
      isPWO_support' := h.isPWO_support.mono fun s hs e => hs (Subtype.ext e) }
  have hg : ∀ s, (g.coeff s : Ω) = h.coeff s := fun s => rfl
  have hg0 : g ≠ 0 := by
    intro e
    apply h0
    ext s
    rw [← hg, e]
    rfl
  have hord : g.order = h.order := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 h0
      rw [HahnSeries.leadingCoeff_eq, ← hg, e]
      rfl
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [← hg]
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 hg0
      rw [HahnSeries.leadingCoeff_eq]
      exact Subtype.ext e
  have hlead : (g.leadingCoeff : Ω) = h.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hg, hord]
  have hunit : IsUnit g.leadingCoeff := by
    refine IsUnit.of_mul_eq_one (⟨h.leadingCoeff⁻¹, hl⟩ : A) ?_
    apply Subtype.ext
    show (g.leadingCoeff : Ω) * h.leadingCoeff⁻¹ = 1
    rw [hlead]
    exact mul_inv_cancel₀ (HahnSeries.leadingCoeff_ne_zero.2 h0)
  obtain ⟨v, hv⟩ := (HahnSeries.isUnit_iff.2 hunit).exists_right_inv
  let f : A →ₙ+* Ω := A.subtype.toNonUnitalRingHom
  have hgf : g.map f = h := by
    ext s
    rfl
  have hone : (1 : HahnSeries ℚ A).map f = 1 := by
    ext s
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> rfl
  have key : h * v.map f = 1 := by
    rw [← hgf, ← HahnSeries.map_mul, hv, hone]
  rw [inv_eq_of_mul_eq_one_right key, HahnSeries.map_coeff]
  exact (v.coeff r).2

theorem coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  intro Ω _ A
  exact ⟨fun h h' hh hh' r => coeff_mul_mem A h h' hh hh' r,
    fun h hh hl r => coeff_inv_mem A h hh hl r⟩

end GlobalTheory.HahnSub
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_mul_eq_zero_dom : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  intro f g hf hg hfg
  have hF := (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hG := (UpperHalfPlane.mdifferentiable_iff.mp hg).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hne : ({z : ℂ | 0 < z.im}).Nonempty := ⟨Complex.I, by simp⟩
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hF hG (fun z _ => by simp [Function.comp_apply, hfg]) hU with h | h
  · left
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this
  · right
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem upperHalfPlane_eq_zero_of_vanish_high :
    ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  intro f C hf hC
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have han := hd.analyticOnNhd hopen
  have hpc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((|C| + 1 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀im : z₀.im = |C| + 1 := by simp [hz₀]
  have hmem : z₀ ∈ {z : ℂ | 0 < z.im} := by
    show 0 < z₀.im
    rw [hz₀im]; positivity
  have hev : (f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds z₀] 0 := by
    have hopen2 : IsOpen {z : ℂ | max C 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hin : z₀ ∈ {z : ℂ | max C 0 < z.im} := by
      show max C 0 < z₀.im
      rw [hz₀im]
      have := le_abs_self C
      have := abs_nonneg C
      exact max_lt (by linarith) (by linarith)
    filter_upwards [hopen2.mem_nhds hin] with z hz
    have hz' : max C 0 < z.im := hz
    have h0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz'
    have h1 : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz'
    simp only [Function.comp_apply, Pi.zero_apply, UpperHalfPlane.ofComplex_apply_of_im_pos h0]
    exact hC _ h1
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hmem hev
  funext τ
  have := heq (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im} from τ.im_pos)
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasSum_powerSeries_inv_of_convergent : ∀ (a : ℕ → ℂ) (ρ : ℝ), 0 < ρ → a 0 ≠ 0 → (∀ x : ℂ, ‖x‖ < ρ → Summable fun n => a n * x ^ n) → ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ x : ℂ, ‖x‖ < ρ' → (∑' n, a n * x ^ n) ≠ 0 ∧ HasSum (fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n) (∑' n, a n * x ^ n)⁻¹ := by
  first | exact @GlobalTheory.PowerSeriesInv.hasSum_inv | exact GlobalTheory.PowerSeriesInv.hasSum_inv | (intros; apply GlobalTheory.PowerSeriesInv.hasSum_inv <;> assumption)
end
