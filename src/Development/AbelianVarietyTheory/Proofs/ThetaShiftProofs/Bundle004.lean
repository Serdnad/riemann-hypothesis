module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FixedPoint

universe u v w

section Algebra

variable {K₀ : Type u} {K₁ : Type v} {L : Type w} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]

theorem mem_range_of_algebraMap_fixed [PerfectField K₀] [IsAlgClosed L] (a : K₁)
    (ha : ∀ s : L ≃ₐ[K₀] L, s (algebraMap K₁ L a) = algebraMap K₁ L a) :
    a ∈ Set.range (algebraMap K₀ K₁) := by
  obtain ⟨k, hk⟩ := GaloisDescent.mem_range_algebraMap_of_forall_algEquiv _ ha
  refine ⟨k, (algebraMap K₁ L).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hk]

theorem exists_ringHom_of_forall_mem_range {A : Type*} [CommRing A] (φ : A →+* K₁)
    (h : ∀ a, φ a ∈ Set.range (algebraMap K₀ K₁)) :
    ∃ ψ : A →+* K₀, (algebraMap K₀ K₁).comp ψ = φ := by
  choose f hf using h
  have hi := (algebraMap K₀ K₁).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, RingHom.ext hf⟩ <;>
    simp [hf]

theorem exists_ringHom_of_fixed [PerfectField K₀] [IsAlgClosed L] {A : Type*} [CommRing A]
    (φ : A →+* K₁)
    (h : ∀ (s : L ≃ₐ[K₀] L) (a : A), s (algebraMap K₁ L (φ a)) = algebraMap K₁ L (φ a)) :
    ∃ ψ : A →+* K₀, (algebraMap K₀ K₁).comp ψ = φ :=
  exists_ringHom_of_forall_mem_range φ fun a => mem_range_of_algebraMap_fixed _ fun s => h s a

end Algebra

section Scheme

local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))

variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]

theorem epi_specAlg : Epi specAlg(K₀, K₁) :=
  have : Surjective specAlg(K₀, K₁) := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective _

theorem point_ext {Z : Scheme.{u}} {y y' : Spec (.of K₀) ⟶ Z}
    (h : specAlg(K₀, K₁) ≫ y = specAlg(K₀, K₁) ≫ y') : y = y' :=
  have := epi_specAlg (K₀ := K₀) (K₁ := K₁)
  (cancel_epi _).mp h

theorem existsUnique_factor [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x) :
    ∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ Z).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx ⊢
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_fixed (K₀ := K₀) (L := L) φ.hom fun s a => by
    have h := hx s
    simp only [← Category.assoc] at h
    rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
    exact congr(($h).hom a)
  have hy : specAlg(K₀, K₁) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Z.fromSpecResidueField z =
      Spec.map φ ≫ Z.fromSpecResidueField z := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ]
    rfl
  exact ⟨_, hy, fun y' hy' => point_ext (hy'.trans hy.symm)⟩

theorem existsUnique_factor_of_isAlgClosed [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of L) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L, Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ x = x) :
    ∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, L) ≫ y = x :=
  existsUnique_factor (L := L) x fun s => by simpa using hx s

theorem top_le_preimage_comp_iff {Z : Scheme.{u}} (y : Spec (.of K₀) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ (specAlg(K₀, K₁) ≫ y) ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ U := by
  refine ⟨fun h p _ => ?_, fun h p _ => h (Set.mem_univ (specAlg(K₀, K₁) p))⟩
  have h' := h (Set.mem_univ (IsLocalRing.closedPoint K₁))
  rw [Subsingleton.elim p (specAlg(K₀, K₁) (IsLocalRing.closedPoint K₁))]
  exact h'

theorem value_comp {A B : CommRingCat.{u}} (g : A ⟶ B) {Z : Scheme.{u}} (y : Spec A ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map g ≫ y) ⁻¹ᵁ U) (f : Γ(Z, U)) :
    (Scheme.ΓSpecIso B).hom ((Spec.map g ≫ y).appLE U ⊤ h' f) =
      g ((Scheme.ΓSpecIso A).hom (y.appLE U ⊤ h f)) := by
  have : (Spec.map g ≫ y).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso B).hom =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso A).hom ≫ g := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc]
    congr 1
  exact congr(($this).hom f)

theorem value_mem_range [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)) :
    ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈ Set.range (algebraMap K₀ K₁) := by
  obtain ⟨y, rfl⟩ := (existsUnique_factor x hx).exists
  exact ⟨_, (value_comp _ y U ((top_le_preimage_comp_iff y U).1 h) h f).symm⟩

theorem defined_over_of_fixed [CharZero K₀] [IsAlgClosed L] :
    (∀ a : L, (∀ s : L ≃ₐ[K₀] L, s a = a) → a ∈ Set.range (algebraMap K₀ L)) ∧
    ∀ (Z : Scheme.{u}) (x : Spec (.of K₁) ⟶ Z),
      (∀ s : L ≃ₐ[K₀] L,
        Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x) →
      (∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x) ∧
      ∀ (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)),
        ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈
          Set.range (algebraMap K₀ K₁) :=
  ⟨GaloisDescent.mem_range_algebraMap_of_forall_algEquiv,
    fun _ x hx => ⟨existsUnique_factor x hx, value_mem_range x hx⟩⟩

end Scheme

end GlobalTheory.FixedPoint
end

section

namespace GlobalTheory

theorem log_translate_sub_const_of_quasiPeriodic {g : ℕ} {θ ρ q : (Fin g → ℂ) → ℂ}
    {la : Fin g → ℂ} {A B : (Fin g → ℂ) →ₗ[ℂ] ℂ} {a b : ℂ} (hθ : Differentiable ℂ θ) (hθ0 : θ ≠ 0)
    (hρ : Differentiable ℂ ρ) (hq : Continuous q) (hqρ : ∀ z, Complex.exp (q z) = ρ z)
    (ha : a ≠ 0) (h1 : ∀ z, θ (z + la) = a * Complex.exp (A z) * θ z)
    (h2 : ∀ z, θ (z + la) * ρ (z + la) = b * Complex.exp (B z) * (θ z * ρ z)) (z w) :
    q (z + la) - q z - (B z - A z) = q (w + la) - q w - (B w - A w) := by
  have hA : Differentiable ℂ A := (LinearMap.toContinuousLinearMap A).differentiable
  have hB : Differentiable ℂ B := (LinearMap.toContinuousLinearMap B).differentiable
  have hρ' : Differentiable ℂ fun z => ρ (z + la) := hρ.comp (differentiable_id.add_const la)
  have hF : Differentiable ℂ fun z =>
      a * Complex.exp (A z) * ρ (z + la) - b * Complex.exp (B z) * ρ z :=
    ((hA.cexp.const_mul a).mul hρ').sub ((hB.cexp.const_mul b).mul hρ)
  have key : ∀ z, a * Complex.exp (A z) * ρ (z + la) - b * Complex.exp (B z) * ρ z = 0 := by
    rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero θ _ hθ hF (fun z => by
      have := h2 z
      rw [h1 z] at this
      linear_combination this) with h | h
    · exact absurd (funext h) hθ0
    · exact h
  have hexp : ∀ z, Complex.exp (q (z + la) - q z - (B z - A z)) = b / a := by
    intro z
    have hk := key z
    rw [← hqρ, ← hqρ] at hk
    have e1 := Complex.exp_ne_zero (q z)
    have e2 := Complex.exp_ne_zero (A z)
    have e3 := Complex.exp_ne_zero (B z)
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub]
    field_simp
    linear_combination hk
  have hc : Continuous fun z => q (z + la) - q z - (B z - A z) :=
    ((hq.comp (continuous_id.add continuous_const)).sub hq).sub
      (hB.continuous.sub hA.continuous)
  exact Complex.isCoveringMap_exp.const_of_comp hc
    (fun u v => Subtype.ext ((hexp u).trans (hexp v).symm)) z w

theorem factor_commutator_eq_of_nonvanishing :
    ∀ (g : ℕ) (θ ρ : (Fin g → ℂ) → ℂ) (la mu : Fin g → ℂ) (A₁ A₂ B₁ B₂ : (Fin g → ℂ) →ₗ[ℂ] ℂ)
      (a₁ a₂ b₁ b₂ : ℂ), Differentiable ℂ θ → θ ≠ 0 → Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) →
      a₁ ≠ 0 → a₂ ≠ 0 → (∀ z, θ (z + la) = a₁ * Complex.exp (A₁ z) * θ z) →
      (∀ z, θ (z + mu) = a₂ * Complex.exp (A₂ z) * θ z) →
      (∀ z, θ (z + la) * ρ (z + la) = b₁ * Complex.exp (B₁ z) * (θ z * ρ z)) →
      (∀ z, θ (z + mu) * ρ (z + mu) = b₂ * Complex.exp (B₂ z) * (θ z * ρ z)) →
      B₁ mu - A₁ mu = B₂ la - A₂ la := by
  intro g θ ρ la mu A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hθ hθ0 hρ hρ0 ha₁ ha₂ h1 h2 h3 h4
  obtain ⟨q, hq, hqρ⟩ := exists_continuous_cexp_eq hρ.continuous hρ0
  have e1 := log_translate_sub_const_of_quasiPeriodic hθ hθ0 hρ hq hqρ ha₁ h1 h3 mu 0
  have e2 := log_translate_sub_const_of_quasiPeriodic hθ hθ0 hρ hq hqρ ha₂ h2 h4 la 0
  simp only [zero_add, map_zero, sub_zero] at e1 e2
  rw [add_comm mu la] at e1
  linear_combination e2 - e1

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem sum_re_cmType_eq_half_trace (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (ν₀ : E) :
    ∑ τ : X.Ψ, (τ.1 ν₀).re = ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => ComplexEmbedding.involutive_conjugate E τ
  have h1 : ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) = ∑ τ : E →+* ℂ, (τ ν₀).re := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := ν₀)
    rw [← (RingHom.equivRatAlgHom (R := E) (S := ℂ)).sum_comp] at h
    have h' := congrArg Complex.re h
    rw [Complex.re_sum] at h'
    simpa using h'
  have h2 : ∑ τ : {τ : E →+* ℂ // τ ∉ X.Ψ}, (τ.1 ν₀).re = ∑ τ : X.Ψ, (τ.1 ν₀).re := by
    let e : {τ : E →+* ℂ // τ ∉ X.Ψ} ≃ X.Ψ :=
      { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
          rw [X.cmType, hcc]; exact τ.2⟩
        invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, (X.cmType _).1 τ.2⟩
        left_inv := fun τ => Subtype.ext (hcc _)
        right_inv := fun τ => Subtype.ext (hcc _) }
    refine Fintype.sum_equiv e _ _ fun τ => ?_
    change _ = (ComplexEmbedding.conjugate τ.1 ν₀).re
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  have h3 := Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ ∈ X.Ψ)
    (fun τ => (τ ν₀).re)
  have h4 : ∑ τ : X.Ψ, (τ.1 ν₀).re + ∑ τ : {τ : E →+* ℂ // τ ∉ X.Ψ}, (τ.1 ν₀).re
      = ∑ τ : E →+* ℂ, (τ ν₀).re := by
    convert h3
  rw [h1, ← h4, h2]
  ring

end GlobalTheory
end

section

namespace GlobalTheory.TraceRealPartConjugateSum

open NumberField

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ => rfl

theorem sum_re_add_conj {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : E) :
    ∑ τ : ↥(ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X),
      Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) =
      (↑((Algebra.trace ℚ E : E → ℚ) x) : ℝ) := by
  classical
  set Ψ := ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X with hΨ
  have hconj : ∀ τ : E →+* ℂ,
      τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = τ x + (ComplexEmbedding.conjugate τ) x := by
    intro τ
    rw [map_add (f := _), ComplexEmbedding.conjugate_coe_eq, ReciprocityTheory.ChartRestriction.G.FD.cc,
      IsCMField.complexEmbedding_complexConj]
  have himg : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, ComplexEmbedding.involutive_conjugate E τ⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E τ]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have hsum : ∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = ∑ τ : E →+* ℂ, τ x := by
    rw [← Finset.sum_add_sum_compl Ψ (fun τ : E →+* ℂ => τ x), himg,
      Finset.sum_image (fun a _ b _ h => (ComplexEmbedding.involutive_conjugate E).injective h),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => hconj τ
  calc ∑ τ : ↥Ψ, Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))
      = Complex.re (∑ τ : ↥Ψ, (↑τ : E →+* ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := (Complex.re_sum _ _).symm
    _ = Complex.re (∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := by
      rw [Finset.sum_coe_sort Ψ (fun τ : E →+* ℂ => τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))]
    _ = _ := by
      rw [hsum, ← trace_eq_sum_ringHom x]
      simp

end GlobalTheory.TraceRealPartConjugateSum
end

section

namespace GlobalTheory.SubmoduleScalarClosure

open NumberField

theorem int_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (m : ℤ) :
    (m : E) • x ∈ L := by
  have h := L.smul_mem (m : 𝓞 E) hx
  rwa [← algebraMap_smul E (m : 𝓞 E) x, map_intCast] at h

theorem integer_ring_smul_mem_submodule {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (𝓞 E) (Fin r → E)) {x : Fin r → E} (hx : x ∈ L) (a : 𝓞 E) :
    (a : E) • x ∈ L := by
  have h := L.smul_mem a hx
  rwa [← algebraMap_smul E a x] at h

theorem main {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ (n : ℤ), n ≠ (0 : ℤ) ∧ (↑n : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by

  let S : Submodule E (Fin r → E) :=
    { carrier := {w | ∃ n : ℤ, n ≠ 0 ∧ (n : E) • w ∈ X.Λ}
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨k, hk, hb⟩
        refine ⟨n * k, mul_ne_zero hn hk, ?_⟩
        have h := X.Λ.add_mem (int_smul_mem_submodule X.Λ ha k) (int_smul_mem_submodule X.Λ hb n)
        convert h using 1
        rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (k : E) (n : E)]
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c w ⟨n, hn, hw⟩

        have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
        obtain ⟨d, hd, hint⟩ := hc.exists_integral_multiple
        refine ⟨d * n, mul_ne_zero hd hn, ?_⟩
        have h := integer_ring_smul_mem_submodule X.Λ hw ⟨d • c, hint⟩
        convert h using 1
        show _ = (d • c) • ((n : E) • w)
        rw [smul_smul, smul_smul, zsmul_eq_mul]
        congr 1
        push_cast
        ring }
  have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ S :=
    Submodule.span_le.mpr fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  rw [X.Λ_span] at hle
  obtain ⟨n, hn, h⟩ := hle (Submodule.mem_top : v ∈ ⊤)
  exact ⟨n, hn, h⟩

end GlobalTheory.SubmoduleScalarClosure
end
