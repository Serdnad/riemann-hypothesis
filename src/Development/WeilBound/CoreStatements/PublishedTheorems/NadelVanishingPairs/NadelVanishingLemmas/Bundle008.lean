module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundle
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle929
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_finset_sec_descends | exact _root_.GlobalTheory.LogPair.exists_finset_sec_descends | (intros; apply _root_.GlobalTheory.LogPair.exists_finset_sec_descends <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_open_immersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → RelSnc (e ≫ f) d (fun i => (L i).pull e) (fun i => Cartier.secPull (σ i) e) := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_pull_of_isOpenImmersion | exact _root_.GlobalTheory.LogPair.relSnc_pull_of_isOpenImmersion | (intros; apply _root_.GlobalTheory.LogPair.relSnc_pull_of_isOpenImmersion <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LogPair.ChartPt

theorem cstOn_res {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) :
    cstOn f V = (resG X h).comp (cstOn f U) := by
  unfold cstOn resG
  rw [← CommRingCat.hom_comp, Category.assoc]
  congr 2
  exact (Scheme.Hom.appLE_map f _ _).symm

theorem smooth_cstOn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) [Smooth f] {U : X.Opens}
    (hU : IsAffineOpen U) : (cstOn f U).Smooth := by
  have hs := HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  unfold cstOn
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv _).2 hs

theorem isEtCoord_basicOpen {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U : X.Opens}
    (hU : IsAffineOpen U) {d : ℕ} (t : Fin d → Γ(X, U)) (h : Γ(X, U))
    (H : letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra;
      (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h))
        (fun a => algebraMap Γ(X, U) (Localization.Away h) (t a))).Etale) :
    IsEtCoord f (X.basicOpen h) (fun a => resG X (X.basicOpen_le h) (t a)) := by
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen h) := (resG X (X.basicOpen_le h)).toAlgebra
  have hl : IsLocalization.Away h Γ(X, X.basicOpen h) := hU.isLocalization_basicOpen h
  let φ := IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h) Γ(X, X.basicOpen h)
  have H' := RingHom.Etale.respectsIso.1 _ φ.toRingEquiv H
  unfold IsEtCoord
  convert H' using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun a => ?_)
  · rw [cstOn_res f (X.basicOpen_le h)]
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [IsScalarTower.algebraMap_apply R Γ(X, U) (Localization.Away h), AlgEquiv.commutes]
    rfl
  · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [AlgEquiv.commutes]
    rfl

end GlobalTheory.LogPair.ChartPt

noncomputable section
namespace GlobalTheory.LogPair.ChartPt

theorem resG_comp {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem exists_chart : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (U : X.Opens) (c : ∀ i, (L i).ι) (hc : ∀ i, U ≤ (L i).U (c i)) (x : X) (K : Type) [Field K] [Algebra Γ(X, U) K], IsAffineOpen U → x ∈ U → (∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ x ∈ X.basicOpen a) → (letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra; Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d ∧ LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} => (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i) ((σ i).f (c i))))) → ∃ C : SncChart f d L σ, x ∈ C.U := by
  intro R _ X f _ d s L σ U c hc x K _ _ hU hxU hK H
  classical
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  obtain ⟨hd, hli⟩ := H
  have : Algebra.Smooth R Γ(X, U) := smooth_cstOn f hU
  obtain ⟨t, e', het, htli⟩ := GlobalTheory.T.extend_linear_independent_differentials R Γ(X, U) K d
    {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0}
    (fun i => resG X (hc i.1) ((σ i.1).f (c i.1))) hd hli
  obtain ⟨h, hh, het2⟩ := GlobalTheory.T.etale_coordinates_kaehler_basis R Γ(X, U) K d t hd htli
  have hV := isEtCoord_basicOpen f hU t h het2
  let sf : Fin s → Γ(X, U) := fun i => resG X (hc i) ((σ i).f (c i))
  let q : Fin s → Γ(X, U) := fun j => if algebraMap Γ(X, U) K (sf j) = 0 then 1 else sf j
  let g : Γ(X, U) := h * ∏ j, q j
  have hgW : X.basicOpen g ≤ X.basicOpen h := by
    simp only [g, Scheme.basicOpen_mul]; exact inf_le_left
  have hgs : ∀ i, algebraMap Γ(X, U) K (sf i) ≠ 0 → X.basicOpen g ≤ X.basicOpen (sf i) := by
    intro i hi
    obtain ⟨k, hk⟩ : sf i ∣ g := by
      have hq : q i = sf i := if_neg hi
      exact dvd_mul_of_dvd_right (hq ▸ Finset.dvd_prod_of_mem q (Finset.mem_univ i)) h
    rw [hk, Scheme.basicOpen_mul]; exact inf_le_left
  have hxg : x ∈ X.basicOpen g := by
    rw [← hK]
    simp only [g, map_mul, map_prod]
    refine mul_ne_zero hh (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    simp only [q]; split_ifs with hj
    · simp
    · exact hj
  have hgU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hEt := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R X f (X.basicOpen h) (X.basicOpen g) hgW d _ (hU.basicOpen h) (hU.basicOpen g) hV
  have hunit : ∀ i, algebraMap Γ(X, U) K (sf i) ≠ 0 → IsUnit (resG X hgU (sf i)) := by
    intro i hi
    have h1 : IsUnit (resG X (X.basicOpen_le (sf i)) (sf i)) := X.toRingedSpace.isUnit_res_basicOpen (sf i)
    have h2 := h1.map (resG X (hgs i hi))
    rwa [resG_comp] at h2
  refine ⟨{
      U := X.basicOpen g
      affine := hU.basicOpen g
      t := fun a => resG X hgU (t a)
      etale := ?_
      c := c
      le := fun i => hgU.trans (hc i)
      e := fun i => if hi : algebraMap Γ(X, U) K (sf i) = 0 then some (e' ⟨i, hi⟩) else none
      inj := ?_
      u := fun i => if hi : algebraMap Γ(X, U) K (sf i) = 0 then 1 else (hunit i hi).unit
      eq := ?_ }, hxg⟩
  · convert hEt using 2 with a
    rw [resG_comp]
  · intro i j a hi hj
    split_ifs at hi hj with h1 h2
    have := e'.injective ((Option.some_injective _ hi).trans (Option.some_injective _ hj).symm)
    exact congrArg Subtype.val this
  · intro i
    by_cases hi : algebraMap Γ(X, U) K (sf i) = 0
    · rw [dite_eq_left hi, dite_eq_left hi]
      simp only [Units.val_one, one_mul, Option.elim_some]
      rw [het ⟨i, hi⟩, resG_comp]
    · rw [dite_eq_right hi, dite_eq_right hi]
      simp only [IsUnit.unit_spec, Option.elim_none, mul_one]
      rw [resG_comp]

end GlobalTheory.LogPair.ChartPt
end
end
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

private theorem dDR_iota_dlog_eq_zero (K : Type) [Field K] (u : Kˣ) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ι K (dlog u)) = 0 := by
  have h1 : (ExteriorAlgebra.ι K (dlog u) : CechDR.DR ℤ K) =
      ((u : K)⁻¹) • CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) := by
    show ExteriorAlgebra.ι K (((u⁻¹ : Kˣ) : K) • KaehlerDifferential.D ℤ K (u : K)) = _
    rw [map_smul, Units.val_inv_eq_inv_val]
  rw [h1, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero, Derivation.leibniz_inv, map_smul,
    smul_mul_assoc]
  have h2 : (CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) : CechDR.DR ℤ K) *
      CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) = 0 := ExteriorAlgebra.ι_sq_zero _
  rw [h2, smul_zero]

private theorem dDR_prod_dlog_eq_zero_and_euler_contraction (K : Type) [Field K] {n : ℕ} (x : Fin n → Kˣ) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hθ : IsEulerContraction x i θ) (l : List (Fin n)) :
    CechDR.dDR ℤ K (l.map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod = 0 ∧
    CechDR.dDR ℤ K (θ (l.map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod) = 0 := by
  have d1 : CechDR.dDR ℤ K (1 : CechDR.DR ℤ K) = 0 := by
    have h := CechDR.dDR_algebraMap (R := ℤ) (B := K) 1
    rw [map_one, Derivation.map_one_eq_zero, map_zero] at h
    exact h
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    refine ⟨d1, ?_⟩
    rw [hθ.1, map_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · rw [CechDR.dDR_mul, ih.1, dDR_iota_dlog_eq_zero, mul_zero, zero_mul, add_zero]
    · rw [hθ.2.1, hθ.2.2 a]
      split_ifs
      · rw [one_mul, map_sub, CechDR.dDR_mul, ih.1, ih.2, dDR_iota_dlog_eq_zero, mul_zero, zero_mul,
          add_zero, sub_self]
      · rw [zero_mul, zero_sub, map_neg, CechDR.dDR_mul, ih.2, dDR_iota_dlog_eq_zero, mul_zero, zero_mul,
          add_zero, neg_zero]

theorem euler_cartan_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K), IsEulerContraction x i θ → ∀ (c : K) (e : Fin n → K) (I : Finset (Fin n)),
    dK c = ∑ j, e j • dlog (x j) →
    extD K (θ (c • logWedge x I)) + θ (extD K (c • logWedge x I)) = e i • logWedge x I := by
  intro K _ n x i θ hθ c e I hc
  obtain ⟨hd, hdθ⟩ := dDR_prod_dlog_eq_zero_and_euler_contraction K x i θ hθ (I.sort (· ≤ ·))
  have hω : logWedge x I =
      ((I.sort (· ≤ ·)).map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod := rfl
  rw [hω]
  generalize ((I.sort (· ≤ ·)).map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod = ω at hd hdθ ⊢
  have hθc : θ (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c)) = e i • 1 := by
    have h : KaehlerDifferential.D ℤ K c = ∑ j, e j • dlog (x j) := hc

    rw [h, map_sum, map_sum]
    simp only [map_smul, hθ.2.2, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [extD_apply]
  rw [map_smul θ, CechDR.dDR_smul, CechDR.dDR_smul, hd, hdθ]
  simp only [smul_zero, add_zero]
  show _ + θ (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c) * ω) = _
  rw [hθ.2.1, hθc, smul_one_mul]
  show ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c) * θ ω + (e i • ω - _) = _
  abel

end GlobalTheory
end
