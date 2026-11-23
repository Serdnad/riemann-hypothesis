module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle028
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Properties
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

section

open Filter Topology

theorem _root_.GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  first | exact @GlobalTheory.riemann_sum_of_one_sided_increments | exact GlobalTheory.riemann_sum_of_one_sided_increments | (intros; apply GlobalTheory.riemann_sum_of_one_sided_increments <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance' : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R), (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R), (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ), (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det → ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) → ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) := by
  first | exact @GlobalTheory.exists_conj_skew_det_unit_of_avoidance | exact GlobalTheory.exists_conj_skew_det_unit_of_avoidance | (intros; apply GlobalTheory.exists_conj_skew_det_unit_of_avoidance <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_corner_unit_of_right_inverse' : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e → (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 → ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) := by
  first | exact @GlobalTheory.exists_corner_unit_of_right_inverse | exact GlobalTheory.exists_corner_unit_of_right_inverse | (intros; apply GlobalTheory.exists_corner_unit_of_right_inverse <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localization_away_range_le_of_dvd_of_comp : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range := by
  first | exact @GlobalTheory.away_range_le_of_dvd' | exact GlobalTheory.away_range_le_of_dvd' | (intros; apply GlobalTheory.away_range_le_of_dvd' <;> assumption)
end

section

open AlgebraicGeometry

theorem _root_.GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen : ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U → ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧ ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)), ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  first | exact @GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | exact GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | (intros; apply GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.exists_separating_basicOpen_functions' : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  first | exact @GlobalTheory.exists_separating_basicOpen_functions | exact GlobalTheory.exists_separating_basicOpen_functions | (intros; apply GlobalTheory.exists_separating_basicOpen_functions <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem fibre_finite_isClosed_of_affine_finite {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V))
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    (f.base ⁻¹' {x}).Finite ∧ ∀ y : Y, f.base y = x → IsClosed ({y} : Set Y) := by
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hU
  haveI hg : IsFinite (f ∣_ V) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h1 : (f.app (V.ι ''ᵁ ⊤)).hom.Finite := by
      rw [Scheme.Opens.ι_image_top]; exact hfin
    have h2 : ∀ {A B : CommRingCat.{0}} (e : A ⟶ B) [IsIso e], e.hom.Finite := fun e _ =>
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).2
    rw [morphismRestrict_appTop]
    exact (h2 _).comp h1
  have hmemU : ∀ y : Y, f.base y = x → y ∈ f ⁻¹ᵁ V := fun y hy => by
    show f.base y ∈ V
    rw [hy]; exact hxV
  have hres : ∀ (y : Y) (hy : f.base y = x),
      (f ∣_ V) (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) = (⟨x, hxV⟩ : V.toScheme) := by
    intro y hy
    exact Subtype.ext ((morphismRestrict_base_coe f V _).trans hy)
  refine ⟨?_, ?_⟩
  · refine (((f ∣_ V).finite_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).image
      (f ⁻¹ᵁ V).ι.base).subset ?_
    intro y hy
    exact ⟨⟨y, hmemU y hy⟩, hres y hy, rfl⟩
  · intro y hy
    rw [← closure_subset_iff_isClosed]
    intro z hz
    rw [← specializes_iff_mem_closure] at hz
    have hfz : f.base z = x := by
      have h1 : f.base y ⤳ f.base z := hz.map f.base.hom.continuous
      rw [hy, specializes_iff_mem_closure, hx.closure_eq] at h1
      exact h1
    have hspec : (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) ⤳ ⟨z, hmemU z hfz⟩ :=
      (f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.1 hz
    have hdisc := ((f ∣_ V).isDiscrete_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).to_subtype
    have hs2 : (⟨_, hres y hy⟩ : ((f ∣_ V) ⁻¹' {(⟨x, hxV⟩ : V.toScheme)} : Set _)) ⤳
        ⟨_, hres z hfz⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
    have := congrArg (fun p => (p.1 : (f ⁻¹ᵁ V).toScheme).1) hs2.eq
    exact (Set.mem_singleton_iff.2 this.symm)

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem exists_basicOpen_free_avoiding_finite : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (n : ℕ) (V : X.Opens), IsAffineOpen V → IsAffineOpen (f ⁻¹ᵁ V) → (letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n) → ∀ (x : X), x ∈ V → ∀ (T : Set X), T.Finite → (∀ y ∈ T, IsClosed ({y} : Set X)) → x ∉ T → ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧ (∀ y ∈ T, y ∉ W) ∧ IsAffineOpen W ∧ IsAffineOpen (f ⁻¹ᵁ W) ∧ (letI := (f.app W).hom.toAlgebra; Module.Free Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.Finite Γ(X, W) Γ(Y, f ⁻¹ᵁ W) ∧ Module.finrank Γ(X, W) Γ(Y, f ⁻¹ᵁ W) = n) := by
  intro X Y f n V hV hV' hfree x hx T hT hcl hxT
  have hTc : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    exact hT.isClosed_biUnion hcl
  let O : X.Opens := V ⊓ ⟨Tᶜ, hTc.isOpen_compl⟩
  obtain ⟨a, haO, hxa⟩ := hV.exists_basicOpen_le (V := O) ⟨x, hx, hxT⟩ hx
  refine ⟨X.basicOpen a, hxa, X.basicOpen_le a, fun y hy hya => (haO hya).2 hy, hV.basicOpen a,
    ?_, ?_⟩
  · rw [Scheme.preimage_basicOpen]; exact hV'.basicOpen _
  letI : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  obtain ⟨hF, hFin, hr⟩ := hfree
  letI : Algebra Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    (f.app (X.basicOpen a)).hom.toAlgebra
  let iX : X.basicOpen a ⟶ V := homOfLE (X.basicOpen_le a)
  let iY : f ⁻¹ᵁ X.basicOpen a ⟶ f ⁻¹ᵁ V := homOfLE (fun y hy => X.basicOpen_le a hy)
  letI : Algebra Γ(X, V) Γ(X, X.basicOpen a) := (X.presheaf.map iX.op).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) := (Y.presheaf.map iY.op).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    ((algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V))).toAlgebra
  haveI : IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : (algebraMap Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
      (algebraMap Γ(X, V) Γ(X, X.basicOpen a)) =
      (algebraMap Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).comp
        (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V)) :=
    congrArg CommRingCat.Hom.hom (f.naturality iX.op)
  haveI : IsScalarTower Γ(X, V) Γ(X, X.basicOpen a) Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    IsScalarTower.of_algebraMap_eq' hcomm.symm
  haveI : IsLocalization.Away a Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
  haveI : IsLocalization.Away (algebraMap Γ(X, V) Γ(Y, f ⁻¹ᵁ V) a)
      Γ(Y, f ⁻¹ᵁ X.basicOpen a) :=
    hV'.isLocalization_of_eq_basicOpen _ iY (Scheme.preimage_basicOpen f a)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ V) (Submonoid.powers a))
      Γ(Y, f ⁻¹ᵁ X.basicOpen a) := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  haveI : IsLocalizedModule (Submonoid.powers a)
      (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr this
  have hbc : IsBaseChange Γ(X, X.basicOpen a)
      (IsScalarTower.toAlgHom Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ(Y, f ⁻¹ᵁ X.basicOpen a)).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Γ(X, X.basicOpen a) _).mp
      inferInstance
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  haveI : Nonempty (X.basicOpen a) := ⟨⟨x, hxa⟩⟩
  haveI : Nontrivial Γ(X, V) := Scheme.component_nontrivial X V
  haveI : Nontrivial Γ(X, X.basicOpen a) := Scheme.component_nontrivial X _
  let b := Module.Free.chooseBasis Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let b' := hbc.basis b
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  rw [Module.finrank_eq_card_basis b', ← hr, Module.finrank_eq_card_basis b]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false

namespace GlobalTheory.AffBaseChange

theorem isPushout_appLE_of_isPullback_of_isAffine :
    ∀ (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S),
      IsPullback f g p q → IsAffine S → IsAffine S' → ∀ (W : X.Opens), IsAffineOpen W →
      IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.app W)
        (g.appLE ⊤ (f ⁻¹ᵁ W) (fun _ _ => trivial)) := by
  intro X X' S S' f g p q h hS hS' W hW
  haveI : IsAffineHom q := inferInstance
  have P := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE h.flip this (isAffineOpen_top S) hW
    (fun _ _ => trivial) (fun _ _ => trivial)
  exact P.flip

end GlobalTheory.AffBaseChange
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor : ∀ {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ] (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O), O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ → j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op = κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  first | exact @GlobalTheory.SectionsPinch.app_eq_of_factor | exact GlobalTheory.SectionsPinch.app_eq_of_factor | (intros; apply GlobalTheory.SectionsPinch.app_eq_of_factor; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  first | exact @GlobalTheory.fibre_dense_affine_chart_primes | exact GlobalTheory.fibre_dense_affine_chart_primes | (intros; apply GlobalTheory.fibre_dense_affine_chart_primes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.exists_ringHom_spec_factor_fromSpec_of_closedPoint_mem : ∀ (X : Scheme.{0}) (V : X.Opens) (hV : IsAffineOpen V) (A : Type) [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ X), f (IsLocalRing.closedPoint A) ∈ V →
    ∃ g : Γ(X, V) →+* A, f = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec := by
  first | exact @GlobalTheory.spec_local_hom_factors_affineOpen | exact GlobalTheory.spec_local_hom_factors_affineOpen | (intros; apply GlobalTheory.spec_local_hom_factors_affineOpen <;> assumption)
end
