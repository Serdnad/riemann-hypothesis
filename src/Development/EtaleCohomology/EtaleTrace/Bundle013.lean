module

public import Development.EtaleCohomology.EtaleTrace.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def ChartGenMem : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ((⟨genericPoint X, hη⟩ : U) ∈ chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) w f ≠ 0)

def ChartGenVal : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : (⟨genericPoint X, hη⟩ : U) ∈ chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f),
      U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ h ((chartMor i U hx φ).app _
          (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))) *
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from
          eval₂ (kHom p) w f) ^ m =
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from eval₂ (kHom p) w g)

theorem ChartGenOn_of (h1 : ChartGenMem) (h2 : ChartGenVal) : ChartGenOn := by
  intro k _ X _ p N w i hi U hx φ hφ hη n hn f hf
  exact ⟨h1 k p N w i hi U hx φ hφ hη n hn f hf, fun m g hg h => h2 k p N w i hi U hx φ hφ hη n hn f hf m g hg h⟩

theorem ChartGenMem_pf : ChartGenMem := by
  intro k _ X _ p N w i hi U hx φ hφ hη n hn f hf
  have e1 : chartMor i U hx φ = U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι _ (MvPolynomial.X i) hx zero_lt_one := by
    rw [chartMor, Scheme.Opens.toSpecΓ, Category.assoc, ← Spec.map_comp_assoc]; rfl
  have e2 : chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f =
      U.ι ⁻¹ᵁ X.basicOpen (φ (HomogeneousLocalization.Away.isLocalizationElem hx hf)) := by
    rw [e1, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
      Proj.awayι_preimage_basicOpen _ hx zero_lt_one hf hn, SpecMap_preimage_basicOpen,
      Scheme.Opens.toSpecΓ_preimage_basicOpen]
    rfl
  rw [e2]
  change genericPoint X ∈ X.basicOpen _ ↔ _
  rw [Scheme.mem_basicOpen _ _ _ hη]
  have h' : (@algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField CommRing.toCommSemiring _ (stalkFunctionFieldAlgebra X (genericPoint X)))
      (X.presheaf.germ U _ hη (φ (HomogeneousLocalization.Away.isLocalizationElem hx hf))) =
        eval₂ (kHom p) w f / w i ^ n := by
    have h := hφ (genericPoint X) hη n (f ^ 1) (by simpa using hf)
    exact h.trans (by rw [pow_one])
  rw [isUnit_iff_ne_zero, ← (@algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField CommRing.toCommSemiring _ (stalkFunctionFieldAlgebra X (genericPoint X))).injective.ne_iff,
    map_zero, h']
  simp [hi]

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem sect_eq_of_alg (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (y : X) (hy : y ∈ U), algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy t)) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro y hy
  have : Nonempty U := ⟨⟨y, hy⟩⟩
  have hst : s = t := by
    apply Scheme.germToFunctionField_injective X U
    have := h y hy
    rwa [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [hst]

theorem fromZero_eq_mk {k : Type} [Field k] {N : ℕ} (i : Fin (N + 1))
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1) (c : k)
    (hg : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k (0 • 1)) :
    HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) k) (Submonoid.powers (MvPolynomial.X i))
      (algebraMap k (homogeneousSubmodule (Fin (N + 1)) k 0) c) = HomogeneousLocalization.Away.mk _ hx 0 (C c) hg := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.fromZeroRingHom]
  rfl

theorem chart_key {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)) (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U))
  (hφ : ∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) :
  (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin (N + 1)) k 0)) ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) k)
        (Submonoid.powers (MvPolynomial.X i)))) ≫ CommRingCat.ofHom ((U.topIso.inv.hom).comp φ) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.ι ≫ p).appTop := by
  ext c
  have hg : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k (0 • 1) :=
    (mem_homogeneousSubmodule _ _).2 (by simpa using isHomogeneous_C (Fin (N + 1)) c)
  have hsec : φ (HomogeneousLocalization.Away.mk _ hx 0 (C c) hg) =
      X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    apply sect_eq_of_alg X
    intro y hy
    rw [hφ, TopCat.Presheaf.germ_res_apply]
    have : Nonempty (⊤ : X.Opens) := ⟨⟨y, trivial⟩⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    simp [kHom]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [fromZero_eq_mk i hx c hg, hsec]
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, CommRingCat.hom_comp,
    RingHom.comp_apply]
  erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem ChartOverK_of : ChartOverK := by
  intro k _ X _ p N w i hi U hx φ hφ
  have hR : U.ι ≫ p = U.toScheme.toSpecΓ ≫ Spec.map ((U.ι ≫ p).appTop) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have key := chart_key p N w i U hx φ hφ
  rw [hR]
  unfold chartMor PNto
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← key]
  simp only [Spec.map_comp, Category.assoc]
  rfl

end LateralTheory.EtaleTrace.Cov
end
end
