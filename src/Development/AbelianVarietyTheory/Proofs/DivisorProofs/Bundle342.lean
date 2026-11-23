module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle264
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004

@[expose] public section

section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

namespace GlobalTheory.CurvForm

theorem form_mulVec_left {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K (M *ᵥ v) w = form (Mᵀ * K) v w := by
  simp only [form]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_mulVec_right {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K v (M *ᵥ w) = form (K * Mᴴᵀ) v w := by
  simp only [form]
  rw [star_mulVec, ← mulVec_transpose, mulVec_mulVec]

theorem form_curv_self_eq : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ),
    MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) →
    (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) →
    ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v =
      form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by
  intro n g H z h2 hu hs hh hdd ξ v
  have hP : (mdel H z ξ)ᵀ = mdel H z ξ := by
    rw [← mdel_transpose, mdel_congr (hs.mono fun x hx => hx.eq)]
  have hQ : mdbar H z ξ = (mdel H z ξ)ᴴ := (conjTranspose_mdel hh ξ).symm
  have hHt : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hHi : (H z)⁻¹ᵀ = (H z)⁻¹ := by rw [transpose_nonsing_inv, hHt]
  rw [curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero, sub_zero, hHt, hP, hQ]
  set P := mdel H z ξ with hPdef
  have hPc : Pᴴᵀ = Pᴴ := by
    ext i j
    have := congrFun (congrFun hP i) j
    simp only [transpose_apply, conjTranspose_apply] at this ⊢
    rw [this]
  simp only [form_mulVec_left, form_mulVec_right]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_mul, hHi, hP, transpose_transpose, hPc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

end GlobalTheory.CurvForm
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B], IsField B → SH B := by
  first | (exact @GlobalTheory.field_finiteType_algClosed_SH) | (exact GlobalTheory.field_finiteType_algClosed_SH) | (intros; apply GlobalTheory.field_finiteType_algClosed_SH  <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed : ∀ (D : Type) [CommRing D] [IsDomain D], AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  first | (exact @GlobalTheory.AICIff.aic_iff) | (exact GlobalTheory.AICIff.aic_iff) | (intros; apply GlobalTheory.AICIff.aic_iff  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure : ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  first | (exact @GlobalTheory.aic_integralClosure_algebraicClosure) | (exact GlobalTheory.aic_integralClosure_algebraicClosure) | (intros; apply GlobalTheory.aic_integralClosure_algebraicClosure  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_representable_cech_level_of_stable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  first | (exact @GlobalTheory.EtC.cech_level_representable) | (exact GlobalTheory.EtC.cech_level_representable) | (intros; apply GlobalTheory.EtC.cech_level_representable  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cocycleCompHomComplex_assoc_on_cohomology_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  first | (exact @GlobalTheory.cocycle_comp_assoc_classes) | (exact GlobalTheory.cocycle_comp_assoc_classes) | (intros; apply GlobalTheory.cocycle_comp_assoc_classes  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleChains_disc_biprod_desc_isIso : ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f₁ : P₁ ⟶ Q) (f₂ : P₂ ⟶ Q), IsIso (biprod.desc ((free R).map f₁) ((free R).map f₂)) → IsIso (biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))) := by
  first | exact @GlobalTheory.EtC.chains_disc_biprod_isIso | exact GlobalTheory.EtC.chains_disc_biprod_isIso | (intros; apply GlobalTheory.EtC.chains_disc_biprod_isIso <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  first | (exact @GlobalTheory.exists_retraction_of_AIC) | (exact GlobalTheory.exists_retraction_of_AIC) | (intros; apply GlobalTheory.exists_retraction_of_AIC  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isLocallySurjective_etale_baseChange : (∀ (Y X : Scheme.{0}) (f : Y ⟶ X), Etale f → Surjective f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f)) ∧ (∀ (P Q : PSh) (f : P ⟶ Q) (s : Q ⟶ P), s ≫ f = 𝟙 Q → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) ∧ ∀ (P Q P' Q' : PSh) (a : P' ⟶ P) (f' : P' ⟶ Q') (f : P ⟶ Q) (b : Q' ⟶ Q), IsPullback a f' f b → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' := by
  first | (exact @GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (exact GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (intros; apply GlobalTheory.EtC.locallySurjective_etale_section_baseChange  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mono_free_etale_mayerVietoris_left_map : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), Mono (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) := by
  first | (exact @GlobalTheory.EtC.MVLeft.left_mono) | (exact GlobalTheory.EtC.MVLeft.left_mono) | (intros; apply GlobalTheory.EtC.MVLeft.left_mono  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafComplex_mappingCone_acyclic_of_quasiIso : ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic := by
  first | exact @GlobalTheory.EtC.mappingCone_acyclic | exact GlobalTheory.EtC.mappingCone_acyclic | (intros; apply GlobalTheory.EtC.mappingCone_acyclic <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n, CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  first | (exact @GlobalTheory.EtC.discRep) | (exact GlobalTheory.EtC.discRep) | (intros; apply GlobalTheory.EtC.discRep  <;> assumption)
end
