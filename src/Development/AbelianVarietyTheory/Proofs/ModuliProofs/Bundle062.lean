module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_local_derivation_lift_smooth_over_field : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by
  first | exact @GlobalTheory.KS.exists_locDerK_of_smooth | exact GlobalTheory.KS.exists_locDerK_of_smooth | (intros; apply GlobalTheory.KS.exists_locDerK_of_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem holUnif_linear_eq_self_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z = z := by
  have hmem : ∀ z, F z - z ∈ u.Λ := fun z => by
    rw [← u.ker]
    have h := u.ex_add (F z - z) z
    rw [sub_add_cancel, hF] at h
    exact mul_eq_right.1 h.symm
  have := u.discrete
  have hc : Continuous (fun z => (⟨F z - z, hmem z⟩ : u.Λ)) :=
    (F.continuous_of_finiteDimensional.sub continuous_id).subtype_mk _
  have h := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa [sub_eq_zero] using h

theorem holUnif_linear_lift_mem {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
    (u : HolUnif A L g) (u' : HolUnif A' L' g') (f : A ⟶ A') [IsMonHom f]
    (F : (Fin g → ℂ) → (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) (z : Fin g → ℂ) (hz : z ∈ u.Λ) :
    F z ∈ u'.Λ := by
  rw [← u'.ker, hF, (u.ker z).2 hz]
  exact MonObj.one_comp f

theorem exists_addEquiv_of_linearEquiv_range {La : Type} [AddCommGroup La] {g : ℕ} (Q Q' : La →+ (Fin g → ℂ))
    (hQ : Function.Injective Q) (hQ' : Function.Injective Q') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (h₁ : ∀ x, h (Q' x) ∈ Q.range) (h₂ : ∀ x, h.symm (Q x) ∈ Q'.range) :
    ∃ gam : La ≃+ La, ∀ x, h (Q' x) = Q (gam x) := by
  choose a ha using h₁
  choose c hc using h₂
  refine ⟨{ toFun := a, invFun := c, left_inv := fun x => hQ' ?_, right_inv := fun x => hQ ?_,
            map_add' := fun x y => hQ ?_ }, fun x => (ha x).symm⟩
  · rw [hc, ha, h.symm_apply_apply]
  · rw [ha, hc, h.apply_symm_apply]
  · rw [map_add (f := _), ha, ha, ha, map_add (f := _), map_add (f := _)]

theorem exists_lattice_aut_of_tMap_id :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t t' : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q Q' : La →+ (Fin g → ℂ)) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ), Function.Injective Q → Function.Injective Q' → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t'.A t'.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t'.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t'.act j₀) → TMap t' t (𝟙 _) → ∃ (gam : La ≃+ La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), ∀ x, h (Q' x) = Q (gam x) := by
  intro o _ g k J b em w w' t t' La _ EF lam ac Q Q' Hm Hm' hQ hQ' ⟨u, _, _, hΛ, _⟩ ⟨u', _, _, hΛ', _⟩ ⟨φ, hφ, _⟩
  have hid : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_of_iso (Iso.refl t.A))
  have he' : IsMonHom e.inv := inferInstance
  obtain ⟨F, hF⟩ : ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u'.ex z ≫ e.hom :=
    exists_linear_lift_of_isMonHom_polAV t'.pol t.pol t'.L t.L u' u e.hom he
  obtain ⟨G, hG⟩ : ∃ G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u'.ex (G z) = u.ex z ≫ e.inv :=
    exists_linear_lift_of_isMonHom_polAV t.pol t'.pol t.L t'.L u u' e.inv he'
  have hFG : ∀ z, F (G z) = z := holUnif_linear_eq_self_of_ex_eq u (F ∘ₗ G) fun z => by
    rw [LinearMap.comp_apply, hF, hG, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hGF : ∀ z, G (F z) = z := holUnif_linear_eq_self_of_ex_eq u' (G ∘ₗ F) fun z => by
    rw [LinearMap.comp_apply, hG, hF, Category.assoc, e.hom_inv_id, Category.comp_id]
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear F G (LinearMap.ext hFG) (LinearMap.ext hGF)
  obtain ⟨gam, hgam⟩ := exists_addEquiv_of_linearEquiv_range Q Q' hQ hQ' h
    (fun x => (hΛ _).1 (holUnif_linear_lift_mem u' u e.hom F hF _ ((hΛ' _).2 ⟨x, rfl⟩)))
    (fun x => (hΛ' _).1 (holUnif_linear_lift_mem u u' e.inv G hG _ ((hΛ _).2 ⟨x, rfl⟩)))
  exact ⟨gam, h, hgam⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS

theorem top_le_preimage_of_dualFst_comp {X : Scheme.{0}} (g : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ g) ⁻¹ᵁ U) : ⊤ ≤ g ⁻¹ᵁ U := by
  intro x _
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := fun c =>
    ⟨TrivSqZeroExt.inl c, by simp⟩

  have hker : ∀ p : PrimeSpectrum (DualNumber ℂ),
      (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom : Set (DualNumber ℂ)) ⊆ p.asIdeal := by
    intro p a ha
    have ha0 : a.fst = 0 := ha
    have hsq : a ^ 2 = 0 := by
      ext <;> simp [pow_two, ha0]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [hsq]; exact p.asIdeal.zero_mem)
  have hx : x ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ hsurj]
    exact hker x
  obtain ⟨q, rfl⟩ := hx
  exact h (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)

private theorem valAt'_app' {X Z : Scheme.{0}} (y : Sp ℂ ⟶ X) (τ : X ⟶ Z) (O : Z.Opens) (f : Γ(Z, O)) :
    valAt' y (τ ⁻¹ᵁ O) ((τ.app O).hom f) = valAt' (y ≫ τ) O f := by
  unfold valAt'
  by_cases h : ⊤ ≤ y ⁻¹ᵁ τ ⁻¹ᵁ O
  · have h' : ⊤ ≤ (y ≫ τ) ⁻¹ᵁ O := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ (y ≫ τ) ⁻¹ᵁ O := h
    rw [dite_eq_right h, dite_eq_right h']

private theorem comp_mul_monObj {X Y M : Over (Sp ℂ)} [MonObj M] (f : X ⟶ Y) (g h : Y ⟶ M) :
    f ≫ (g * h) = (f ≫ g) * (f ≫ h) :=
  MonObj.comp_mul f g h

private theorem toUnit_left_eq_hom {T : Over (Sp ℂ)} (t : T ⟶ 𝟙_ (Over (Sp ℂ))) : t.left = T.hom := by
  have := Over.w t
  exact (Category.comp_id _).symm.trans this

def dualZero : 𝟙_ (Over (Sp ℂ)) ⟶ epsR ℂ :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem exists_locDer_of_isDiff {g : ℕ} (A : Over (Sp ℂ)) [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
    (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) (hv : IsTangent v) (hd : u.IsDiff w v) :
    ∃ d, LocDer A.hom A.hom (𝟙 _) (fun _ => 0) ⊤ d ∧ ∀ O f z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O →
      valAt' (u.ex z).left ((𝟙 A.left) ⁻¹ᵁ O) (d O f) = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  classical
  unfold HolUnif.IsDiff at hd
  unfold IsTangent at hv
  have hse : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    exact Over.w dualZero

  let ρ := pullback.fst A.hom (spMap (algebraMap ℂ (DualNumber ℂ)))
  let π := pullback.snd A.hom (spMap (algebraMap ℂ (DualNumber ℂ)))
  let B : Over (Sp ℂ) := Over.mk (π ≫ spMap (algebraMap ℂ (DualNumber ℂ)))
  let ρ' : B ⟶ A := Over.homMk ρ pullback.condition
  let v' : B ⟶ A := Over.homMk (π ≫ v.left) (by
    rw [Category.assoc, Over.w v]
    rfl)

  let Φ := (ρ' * v').left
  let j : A.left ⟶ pullback A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
    pullback.lift (𝟙 _) (A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (by
      rw [Category.assoc, hse, Category.comp_id, Category.id_comp])
  let j' : A ⟶ B := Over.homMk j (by
    change j ≫ π ≫ _ = _
    rw [pullback.lift_snd_assoc, Category.assoc, hse, Category.comp_id])
  have hj1 : j' ≫ ρ' = 𝟙 A := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hj2 : j' ≫ v' = 1 := by
    apply Over.OverMorphism.ext
    change j ≫ π ≫ v.left = (toUnit A ≫ η).left
    rw [pullback.lift_snd_assoc, Category.assoc, hv, Over.comp_left, toUnit_left_eq_hom]
  have hjΦ : j ≫ Φ = 𝟙 A.left := by
    have h1 : j' ≫ (ρ' * v') = 𝟙 A := by rw [comp_mul_monObj, hj1, hj2, _root_.mul_one]
    exact congrArg (fun t => t.left) h1
  have hΦp : Φ ≫ A.hom = π ≫ spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w (ρ' * v')
  obtain ⟨d, hd1, hd2⟩ := GlobalTheory.T.exists_localDerivation_of_dualNumber_thickening A.left _ A.hom π ρ j (IsPullback.of_hasPullback _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) ℂ (algebraMap ℂ (DualNumber ℂ)) A.left A.hom
    (𝟙 A.left) Φ hjΦ hΦp
  refine ⟨d, ?_, ?_⟩
  · have hD : (fun r : ℂ => (algebraMap ℂ (DualNumber ℂ) r).snd) = fun _ => 0 :=
      funext fun r => rfl
    rw [hD] at hd1
    exact hd1
  · intro O f z hz

    let τ : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A
    have hτ : ∀ z', u.ex z' ≫ τ = u.ex (z + z') := by
      intro z'
      rw [u.ex_add, comp_mul_monObj, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp,
        Category.comp_id]
    have hy : (u.ex z).left ≫ A.hom = 𝟙 _ := Over.w (u.ex z)
    let yt : Sp (DualNumber ℂ) ⟶ pullback A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
      pullback.lift (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (u.ex z).left) (𝟙 _) (by
        rw [Category.assoc, hy]
        exact (Category.comp_id _).trans (Category.id_comp _).symm)
    let yt' : epsR ℂ ⟶ B := Over.homMk yt (by
      change yt ≫ π ≫ _ = _
      rw [pullback.lift_snd_assoc, Category.id_comp]
      rfl)
    have hv1 : yt' ≫ ρ' = toUnit _ ≫ u.ex z := by
      apply Over.OverMorphism.ext
      change yt ≫ ρ = _
      rw [pullback.lift_fst, Over.comp_left, toUnit_left_eq_hom]
      rfl
    have hv2 : yt' ≫ v' = v := by
      apply Over.OverMorphism.ext
      change yt ≫ π ≫ v.left = v.left
      rw [pullback.lift_snd_assoc, Category.id_comp]
    have hVz : yt ≫ Φ = v.left ≫ τ.left := by
      have h1 : yt' ≫ (ρ' * v') = v ≫ τ := by
        rw [comp_mul_monObj, hv1, hv2, comp_mul_monObj, ← Category.assoc, comp_toUnit, Category.comp_id]
      exact congrArg (fun t => t.left) h1

    have hfib : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left ≫ τ.left = (u.ex z).left := by
      have h1 : dualZero ≫ v = 1 := by
        apply Over.OverMorphism.ext
        change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left =
          (toUnit (𝟙_ (Over (Sp ℂ))) ≫ η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left
        rw [hv, toUnit_unit, Category.id_comp]
      have h2 : dualZero ≫ v ≫ τ = u.ex z := by
        rw [← Category.assoc, h1, comp_mul_monObj, ← Category.assoc, comp_toUnit, toUnit_unit,
          Category.id_comp, Category.comp_id, _root_.mul_one]
      exact congrArg (fun t => t.left) h2
    have h0 : ⊤ ≤ (yt ≫ Φ) ⁻¹ᵁ O := by
      rw [hVz]
      apply top_le_preimage_of_dualFst_comp
      rw [hfib]
      exact hz
    rw [← hd2 (u.ex z).left yt (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) O h0 f]
    have hmain : ∀ (G : Sp (DualNumber ℂ) ⟶ A.left) (hG : G = v.left ≫ τ.left) (hG0 : ⊤ ≤ G ⁻¹ᵁ O),
        TrivSqZeroExt.snd (show DualNumber ℂ from
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((G.appLE O ⊤ hG0).hom f)) =
          fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
      rintro G rfl hG0
      have key := hd (τ.left ⁻¹ᵁ O) hG0 ((τ.left.app O).hom f)
      have hfun : (fun z' => valAt' (u.ex z').left (τ.left ⁻¹ᵁ O) ((τ.left.app O).hom f)) =
          fun z' => valAt' (u.ex (z + z')).left O f := by
        funext z'
        rw [valAt'_app', ← Over.comp_left, hτ]
      have hshift : fderiv ℂ (fun z' => valAt' (u.ex (z + z')).left O f) 0 =
          fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z := by
        simpa using fderiv_comp_add_left (𝕜 := ℂ) (f := fun y : Fin g → ℂ => valAt' (u.ex y).left O f)
          (x := (0 : Fin g → ℂ)) z
      rw [hfun, hshift] at key
      rw [← key]
      rw [Scheme.Hom.comp_appLE]
      rfl
    exact hmain _ hVz h0

theorem invariant_field_algebraic : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ w : (Fin P₀.g → ℂ), ∃ d, LocDer P₀.A.hom P₀.A.hom (𝟙 _) (fun _ => 0) ⊤ d ∧ ∀ O f z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left ((𝟙 P₀.A.left) ⁻¹ᵁ O) (d O f) = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  intro P₀ u Hm χ hU w
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := hU.tan₂ w
  exact exists_locDer_of_isDiff P₀.A u w v hv hd

end GlobalTheory.KS

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertFamily

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

private theorem valAt'_add' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f + f') = valAt' y W f + valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W W' : X.Opens} (hle : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : valAt' y W' (resG X hle f) = valAt' y W f := by
  have hW : ⊤ ≤ y ⁻¹ᵁ W := fun x hx => hle (h hx)
  unfold valAt' valAt
  rw [dite_eq_left h, dite_eq_left hW]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem valAt'_constFn_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : y ≫ p = 𝟙 _) (a : ℂ) :
    valAt' y ⊤ (constFn p ⊤ a) = a := by
  have hq : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((q.appLE ⊤ ⊤ e).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a := by
    rintro q e rfl
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (((Sp ℂ).presheaf.map (𝟙 (Opposite.op (⊤ : (Sp ℂ).Opens)))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a
    simp
  have e0 : ⊤ ≤ y ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold valAt' valAt constFn
  rw [dite_eq_left e0]
  refine Eq.trans ?_ (hq (y ≫ p) (fun _ _ => trivial) hp)
  congr 1
  rw [← CommRingCat.comp_apply]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE y p ⊤ ⊤ ⊤ _ e0)

theorem ex_over (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 _ := by
  exact (Over.w (u.ex z)).trans (by simp)

theorem differentiableAt_val (z : Fin g → ℂ) (O : A.left.Opens) (f : Γ(A.left, O)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O) :
    DifferentiableAt ℂ (fun z' => valAt' (u.ex z').left O f) z := by
  obtain ⟨hO, hD⟩ := u.hol O f
  exact hD.differentiableAt (hO.mem_nhds h)

theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer (u.ex z).left (fun O f => fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w) := by
  constructor
  · intro O h f f'
    have e : (fun z' => valAt' (u.ex z').left O (f + f')) =
        (fun z' => valAt' (u.ex z').left O f) + fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_add' _ _ _ _
    rw [e, fderiv_add (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    rfl
  · intro O h f f'
    have e : (fun z' => valAt' (u.ex z').left O (f * f')) =
        (fun z' => valAt' (u.ex z').left O f) * fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_mul_of_top_le_preimage_open _ _ _ _
    rw [e, fderiv_mul (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  · intro O O' hle h f
    have hev : (fun z' => valAt' (u.ex z').left O' (resG A.left hle f)) =ᶠ[nhds z]
        fun z' => valAt' (u.ex z').left O f := by
      filter_upwards [(u.hol O' (resG A.left hle f)).1.mem_nhds h] with z' hz'
      exact valAt'_resG _ hle hz' f
    rw [hev.fderiv_eq]

theorem fderiv_constFn (z w : Fin g → ℂ) (a : ℂ) :
    fderiv ℂ (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) z w = 0 := by
  have e : (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) = fun _ => a := by
    funext z'
    exact valAt'_constFn_top _ _ (ex_over u z') a
  rw [e]
  simp

theorem fn_eq {X : Scheme.{0}} (m : A.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    fn u m W f = fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  funext z'
  unfold fn valAt' valAt
  by_cases h : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W
  · rw [dite_eq_left h, dite_eq_left (show ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]
    congr 1
  · rw [dite_eq_right h, dite_eq_right (show ¬ ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]

theorem existsUnique_vector : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  intro P₀ u Hm χ hG R _ x₀ X p m _ hpb z δ hδ hc
  obtain ⟨hex, huniq⟩ := GlobalTheory.T.germDerivation_of_fibre_of_kills_base P₀.A R x₀ X p m hpb (u.ex z).left (ex_over u z)
  obtain ⟨δ₀, hδ₀, hc₀, hδδ₀⟩ := hex δ hδ hc
  obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.germDerivation_uniformised_abelianVariety_unique_vector P₀ u Hm χ hG z δ₀ hδ₀ hc₀
  refine ⟨w, fun W f hz => ?_, fun w' hw' => hwu w' fun O f hO => ?_⟩
  · rw [hδδ₀ W f hz, hw (m ⁻¹ᵁ W) ((m.app W).hom f) hz, fn_eq]
  · have hD := ptDer_fderiv u z w'
    have hpt : PtDer (u.ex z).left
        (fun O f => δ₀ O f - fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w') := by
      refine ⟨fun V hV f f' => ?_, fun V hV f f' => ?_, fun V V' hle hV f => ?_⟩
      · have h1 := hδ₀.add V hV f f'
        have h2 := hD.add V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.mul V hV f f'
        have h2 := hD.mul V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.res V V' hle hV f
        have h2 := hD.res V V' hle hV f
        linear_combination h1 - h2
    have key := huniq _ hpt (fun a => by
        have h1 := hc₀ a
        have h2 := fderiv_constFn u z w' a
        linear_combination h1 - h2)
      (fun V f hV => by
        have h1 := hδδ₀ V f hV
        have h2 := hw' V f hV
        rw [fn_eq] at h2
        linear_combination h2 - h1) O f hO
    exact sub_eq_zero.mp key

end GlobalTheory.KS.VertFamily
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem smoothOfRelativeDimension_of_isPullback_isDominant :
    ∀ (X U Y Y' : Scheme.{0}) (j : U ⟶ X) (p : Y ⟶ X) (p' : Y' ⟶ U) (φ : Y' ⟶ Y) (g : ℕ),
      IsPullback φ p' p j → IsDominant j → Smooth p → SmoothOfRelativeDimension g p' →
        SmoothOfRelativeDimension g p := by
  intro X U Y Y' j p p' φ g hpb hj hp hg
  have := hp
  have key : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p) := by
    intro y
    obtain ⟨n, W, hyW, hn⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim p y
    have hopen : IsOpen (p '' (W : Set Y)) := p.isOpenMap _ W.isOpen
    obtain ⟨u, w, hwW, hwu⟩ := hj.denseRange.exists_mem_open hopen ⟨p y, y, hyW, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hwu
    have h1 : φ (hpb.isoPullback.inv z) = w := by
      rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz1]
    have hng := ReciprocityTheory.ChartRestriction.G.H1.dim_base hpb hn hg (hpb.isoPullback.inv z) (h1 ▸ hwW)
    subst hng
    exact ⟨W, hyW, hn⟩
  choose W hyW hW using key
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} g)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) W ?_ hW
  rw [eq_top_iff]
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.existsUnique_descent_automorphism_invariant_morphism : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [IsAlgClosed C] [Algebra K C] (S : Scheme.{0}) (b : Sp K ⟶ S) (X Y : Over S), IsSeparated Y.hom → ∀ κ : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk b, κ.left = spMap (algebraMap K C) → ∀ f : Over.mk (spMap (algebraMap K C) ≫ b) ⊗ X ⟶ Y, (∀ (σ : C ≃ₐ[K] C) (s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b)), s.left = spMap (σ : C →+* C) → s ▷ X ≫ f = f) → ∃! g : Over.mk b ⊗ X ⟶ Y, κ ▷ X ≫ g = f := by
  first | exact @GlobalTheory.InvariantMorDescent.existsUnique_desc | exact GlobalTheory.InvariantMorDescent.existsUnique_desc | (intros; apply GlobalTheory.InvariantMorDescent.existsUnique_desc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_linear_lift_of_isMonHom_uniformisation : ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (f : P.A ⟶ P'.A), IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  first | exact @GlobalTheory.exists_linear_lift_of_isMonHom_polAV | exact GlobalTheory.exists_linear_lift_of_isMonHom_polAV | (intros; apply GlobalTheory.exists_linear_lift_of_isMonHom_polAV <;> assumption)
end
