module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.ratZariskiClosurePoints_isGroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ∀ (R : Type) [CommRing R] [Algebra ℚ R], (1 : Matrix ι ι R) ∈ pts Γ R ∧ (∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, x * y ∈ pts Γ R) ∧ (∀ x ∈ pts Γ R, x.adjugate ∈ pts Γ R) ∧ ∀ x ∈ pts Γ R, x.det = 1 := by
  first | exact @GlobalTheory.ClassFin.pts_group | exact GlobalTheory.ClassFin.pts_group | (intros; apply GlobalTheory.ClassFin.pts_group <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqs_subgroupOf_self {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs U).subgroupOf U = sqs (⊤ : Subgroup U) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩
  · rintro ⟨y, -, h⟩
    exact ⟨y.1, y.2, congrArg Subtype.val h⟩

theorem card_sq_eq_one_sUnits (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card {a : sUnits F S // a ^ 2 = 1} = 2 := by
  have hm : (-1 : Fˣ) ∈ sUnits F S := by
    rw [mem_sUnits]; intro v _; simp
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨⟨-1, hm⟩, Subtype.ext (by simp)⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun a : {a : sUnits F S // a ^ 2 = 1} => ((a.1.1 : Fˣ) : F)) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h1
    norm_num at h1
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (a : F) ^ 2 = 1 := by
      have := congrArg (fun a : sUnits F S => ((a.1 : Fˣ) : F)) h
      simpa using this
    rcases sq_eq_one_iff.mp h1 with h2 | h2
    · left
      exact Subtype.ext (Subtype.ext (Units.ext h2))
    · right
      exact Subtype.ext (Subtype.ext (Units.ext h2))

theorem relIndex_sqs_sUnits : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  haveI := GlobalTheory.T.sUnitsNumberField_fg F S
  rw [Subgroup.relIndex, sqs_subgroupOf_self, GlobalTheory.T.index_sqs_of_fg, card_sq_eq_one_sUnits,
    ← GlobalTheory.T.finrank_sUnitsNumberField_add_one F S, pow_succ]

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem ltr_mul_left {ι : Type} [Fintype ι] [DecidableEq ι] (g h : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    ltr (g * h) f = ltr h (ltr g f) := by
  have : ltr (g * h) = (ltr h).comp (ltr g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩

    simp only [ltr, MvPolynomial.aeval_X, AlgHom.comp_apply, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [this]; rfl

theorem ltr_one_left {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPolynomial (ι × ι) ℂ) :
    ltr (1 : Matrix ι ι ℂ) f = f := by
  have : ltr (1 : Matrix ι ι ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [ltr, MvPolynomial.aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Matrix.one_apply_ne hb.symm]
    · simp
  rw [this]; rfl

noncomputable def ltrRep {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] (ρ : G →* Matrix ι ι ℂ) :
    Representation ℂ G (MvPolynomial (ι × ι) ℂ) where
  toFun g := (ltr (ρ g⁻¹)).toLinearMap
  map_one' := by
    refine LinearMap.ext fun f => ?_
    simp [ltr_one_left]
  map_mul' g h := by
    refine LinearMap.ext fun f => ?_
    simp [ltr_mul_left]

noncomputable def dualPowRep {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] (ρ : G →* Matrix ι ι ℂ) (n : ℕ) :
    Representation ℂ G ((Fin n → ι) → ℂ) where
  toFun g := Matrix.toLin' (tpow n (ρ g⁻¹))ᵀ
  map_one' := by
    rw [inv_one, map_one, ((GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).1 n).1, transpose_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [_root_.mul_inv_rev, map_mul, ((GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).1 n).2.1, transpose_mul, Matrix.toLin'_mul]; rfl

theorem ltr_completely_reducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ U : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U, ltr g f ∈ U) → ∃ U' : Submodule ℂ (MvPolynomial (ι × ι) ℂ), (∀ g ∈ Γ, ∀ f ∈ U', ltr g f ∈ U') ∧ IsCompl U U' := by
  intro ι _ _ Γ hΓ hss U hU
  obtain ⟨G, _, ρ, hρ⟩ := GlobalTheory.T.exists_group_hom_range_eq_of_isPre ι Γ hΓ
  have hs : ∀ n, (dualPowRep ρ n).IsSemisimpleRepresentation := by
    intro n
    rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation (Fin n → ι) G _ (dualPowRep ρ n) (Pi.basisFun ℂ _)]
    have h := GlobalTheory.T.completelyReducible_kroneckerPower_transpose ι Γ hΓ hss n
    convert h using 1
    subst hρ
    ext M
    simp only [Set.mem_range, Set.mem_image, LinearMap.toMatrix_eq_toMatrix']
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨ρ g⁻¹, ⟨_, rfl⟩, (LinearMap.toMatrix'_toLin' _).symm⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g⁻¹, ?_⟩
      change LinearMap.toMatrix' (Matrix.toLin' (tpow n (ρ g⁻¹⁻¹))ᵀ) = _
      rw [inv_inv, LinearMap.toMatrix'_toLin']
  choose p _ hp2 hp3 using (GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties ι).2.2.2
  have hsemi : (ltrRep ρ).IsSemisimpleRepresentation := by
    refine GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant G _ (ltrRep ρ) (Σ n : ℕ, (Fin n → ι)) (fun j => (Fin j.1 → ι) → ℂ)
      (fun j => dualPowRep ρ j.1) (fun j => p j.1 j.2) (fun j => hs j.1) ?_ ?_
    · rintro ⟨n, b⟩ g v
      change p n b (Matrix.toLin' (tpow n (ρ g⁻¹))ᵀ v) = ltr (ρ g⁻¹) (p n b v)
      rw [hp2, Matrix.toLin'_apply, Matrix.mulVec_transpose]
    · rw [eq_top_iff]
      intro f _
      rw [← MvPolynomial.sum_homogeneousComponent f]
      refine Submodule.sum_mem _ fun n _ => ?_
      obtain ⟨l, hl⟩ := hp3 n _ (MvPolynomial.homogeneousComponent_isHomogeneous n f)
      rw [hl]
      refine Submodule.sum_mem _ fun b _ => ?_
      exact Submodule.mem_iSup_of_mem (⟨n, b⟩ : Σ n : ℕ, (Fin n → ι)) ⟨l b, rfl⟩
  let S : Subrepresentation (ltrRep ρ) :=
    ⟨U, fun g v hv => hU _ (hρ ▸ ⟨g⁻¹, rfl⟩) v hv⟩
  obtain ⟨S', hS'⟩ := hsemi.exists_isCompl S
  refine ⟨S'.toSubmodule, ?_, ?_⟩
  · rintro g hg f hf
    rw [← hρ] at hg
    obtain ⟨g, rfl⟩ := hg
    have := S'.apply_mem_toSubmodule g⁻¹ hf
    change ltr (ρ g⁻¹⁻¹) f ∈ _ at this
    rwa [inv_inv] at this
  · constructor
    · rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hS'.1)
    · rw [codisjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hS'.2)

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_rational_matrix_approx_adele_linear_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (φ : Matrix (Fin n) (Fin n) (RA F E) →+ Matrix (Fin n) (Fin n) (RA F E)), (∀ (a : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), φ ((a ⊗ₜ[F] (1 : E) : RA F E) • M) = (a ⊗ₜ[F] (1 : E) : RA F E) • φ M) → ∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), φ (M - fm F M₀) *ᵥ z = D • w := by
  first | exact @GlobalTheory.UnRep.exists_rational_approx_after_adele_linear | exact GlobalTheory.UnRep.exists_rational_approx_after_adele_linear | (intros; apply GlobalTheory.UnRep.exists_rational_approx_after_adele_linear <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_adelic_unitary_translate_standardLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M : ℕ) (Λ : GenLat E n), 0 < M → Λ.Unimod → Λ.TrivAt M → ∃ g : GL (Fin n) (RA (maximalRealSubfield E) E), IsUnA (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) g.1 ∧ (Λ.La : Set (Fin n → E)) = latOf (maximalRealSubfield E) g.1 (stdLat E n : Set (Fin n → E)) ∧ ∀ D : ℕ, 0 < D → CongAtA (maximalRealSubfield E) (stdLat E n) M D g.1 := by
  first | exact @GlobalTheory.AdelTranslate.exists_adelic_translate | exact GlobalTheory.AdelTranslate.exists_adelic_translate | (intros; apply GlobalTheory.AdelTranslate.exists_adelic_translate <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem cmAdele_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AF F)ˣ, Φ (idF F E a : (AE F E)ˣ) = x := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hex := GlobalTheory.T.exists_cm_adele_tensor_equiv_mixed_finite F E σ h1 h2 h3 h4
  obtain ⟨Φ, a1, a2, a3, a4, a5⟩ := hex
  refine ⟨Φ, a1, a2, ?_, a4, a5⟩
  rintro v ε ⟨α, rfl, hv, hv'⟩
  exact a3 v (pairA F 0 α) rfl hv hv'

end GlobalTheory
end

end

section

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.cmExtension_adeles_standardModel_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AF F)ˣ, Φ (idF F E a : (AE F E)ˣ) = x := by
  first | exact @GlobalTheory.cmAdele_dictionary | exact GlobalTheory.cmAdele_dictionary | (intros; apply GlobalTheory.cmAdele_dictionary <;> assumption)

end
end
