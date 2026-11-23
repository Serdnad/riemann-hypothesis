module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SimilitudeDefiniteFormIsAlgebraicOnVector
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_minimal_support {F J : Type} [Field F] (A : Finset J) (M : (J → F) → Prop)
    (L : (J → F) → F) (hM : ∀ v w (a : F), M v → M w → M (fun i => v i - a * w i))
    (hL : ∀ v w (a : F), L (fun i => v i - a * w i) = L v - a * L w)
    (v : J → F) (hv : M v) (hLv : L v ≠ 0) :
    ∃ v', M v' ∧ L v' ≠ 0 ∧ ∀ w, M w → (∀ i ∈ A, v' i = 0 → w i = 0) →
      ∀ i₀ ∈ A, v' i₀ ≠ 0 → w i₀ = 0 → ∀ i ∈ A, w i = 0 := by
  classical
  let s : (J → F) → Finset J := fun u => A.filter (fun i => u i ≠ 0)
  have hex : ∃ n, ∃ u, M u ∧ L u ≠ 0 ∧ (s u).card = n := ⟨_, v, hv, hLv, rfl⟩
  obtain ⟨v', hMv', hLv', hcard⟩ := Nat.find_spec hex
  refine ⟨v', hMv', hLv', ?_⟩
  have hmin : ∀ u, M u → L u ≠ 0 → s u ⊆ s v' → s u ≠ s v' → False := by
    intro u hMu hLu hsub hne
    have hlt : (s u).card < (s v').card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    rw [hcard] at hlt
    exact Nat.find_min hex hlt ⟨u, hMu, hLu, rfl⟩
  intro w hMw hsupp i₀ hi₀ hv'i₀ hwi₀ j hj
  by_contra hwj
  have hv'j : v' j ≠ 0 := fun h => hwj (hsupp j hj h)
  by_cases hLw : L w = 0
  · have hMu : M (fun i => v' i - v' j / w j * w i) := hM v' w _ hMv' hMw
    have hLu : L (fun i => v' i - v' j / w j * w i) ≠ 0 := by
      rw [hL v' w, hLw, mul_zero, sub_zero]
      exact hLv'
    apply hmin _ hMu hLu
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, fun h => hi.2 ?_⟩
      rw [h, hsupp i hi.1 h, mul_zero, sub_zero]
    · intro heq
      have hjs : j ∈ s v' := by simp [s, hj, hv'j]
      rw [← heq] at hjs
      simp only [s, Finset.mem_filter] at hjs
      exact hjs.2 (by rw [div_mul_cancel₀ _ hwj, sub_self])
  · apply hmin w hMw hLw
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, fun h => hi.2 (hsupp i hi.1 h)⟩
    · intro heq
      have hi₀s : i₀ ∈ s v' := by simp [s, hi₀, hv'i₀]
      rw [← heq] at hi₀s
      simp [s, hwi₀] at hi₀s

theorem exists_weighted_relation :
    ∀ (F T X : Type) [Field F] [Group T] (c : T → X → F) (σ : T → F →+* F) (φ : T → F) (S : Finset X) (p q : X → F), (∀ t t' χ, c (t * t') χ = c t χ * c t' χ) → (∀ χ, c 1 χ = 1) → (∀ t t' χ, σ t (c t' χ) = c t' χ) → (∀ t t', σ t (φ t') = φ (t' * t)) → (∀ t, φ t * ∑ χ ∈ S, c t χ * p χ = ∑ χ ∈ S, c t χ * q χ) → ∑ χ ∈ S, p χ ≠ 0 → ∃ (χ₀ : X) (p' q' : X → F), ∑ χ ∈ S, p' χ ≠ 0 ∧ φ 1 * ∑ χ ∈ S, p' χ = ∑ χ ∈ S, q' χ ∧ ∀ t, ∀ χ ∈ S, σ t (p' χ) * c t χ₀ = c t χ * p' χ ∧ σ t (q' χ) * c t χ₀ = c t χ * q' χ := by
  intro F T X _ _ c σ φ S p q hmul hone hσc hσφ hrel hsum
  classical
  have hcinv : ∀ t χ, c t χ * c t⁻¹ χ = 1 := by
    intro t χ
    rw [← hmul, mul_inv_cancel, hone]
  obtain ⟨v', hMv', hLv', hmin⟩ := exists_minimal_support (S.disjSum S)
    (fun v : X ⊕ X → F => ∀ t, φ t * ∑ χ ∈ S, c t χ * v (Sum.inl χ) = ∑ χ ∈ S, c t χ * v (Sum.inr χ))
    (fun v => ∑ χ ∈ S, v (Sum.inl χ))
    (by
      intro v w a hv hw t
      have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t χ * (g χ - a * h χ)
          = ∑ χ ∈ S, c t χ * g χ - a * ∑ χ ∈ S, c t χ * h χ := by
        intro g h
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun χ _ => by ring
      rw [e1 (fun χ => v (Sum.inl χ)) (fun χ => w (Sum.inl χ)),
        e1 (fun χ => v (Sum.inr χ)) (fun χ => w (Sum.inr χ))]
      linear_combination hv t - a * hw t)
    (by
      intro v w a
      rw [Finset.sum_sub_distrib, Finset.mul_sum])
    (Sum.elim p q) (fun t => hrel t) hsum
  obtain ⟨χ₀, hχ₀S, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLv'
  set r := v' (Sum.inl χ₀) with hrdef
  have htw : ∀ t, ∀ t', φ t' * ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inl χ)))
      = ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inr χ))) := by
    intro t t'
    have h := congrArg (σ t) (hMv' (t' * t⁻¹))

    simp only [map_mul, map_sum, hσc, hσφ, inv_mul_cancel_right, hmul] at h
    have e : ∀ g : X → F, ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * g χ) = ∑ χ ∈ S, c t' χ * c t⁻¹ χ * g χ :=
      fun g => Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm
    rw [e (fun χ => σ t (v' (Sum.inl χ))), e (fun χ => σ t (v' (Sum.inr χ)))]
    exact h
  have hfin : ∀ t, ∀ i ∈ S.disjSum S,
      σ t (r⁻¹ * v' i) * c t χ₀ = c t (Sum.elim id id i) * (r⁻¹ * v' i) := by
    intro t i hi
    have hsr : σ t r ≠ 0 := (map_ne_zero (σ t)).mpr hr
    have hz := hmin (fun j => c t⁻¹ (Sum.elim id id j) * σ t (v' j) - c t⁻¹ χ₀ * σ t r / r * v' j)
      (fun t' => by
        have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t' χ * (g χ - c t⁻¹ χ₀ * σ t r / r * h χ)
            = ∑ χ ∈ S, c t' χ * g χ - c t⁻¹ χ₀ * σ t r / r * ∑ χ ∈ S, c t' χ * h χ := by
          intro g h
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun χ _ => by ring
        simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
        rw [e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inl χ))) (fun χ => v' (Sum.inl χ)),
          e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inr χ))) (fun χ => v' (Sum.inr χ))]
        linear_combination htw t t' - c t⁻¹ χ₀ * σ t r / r * hMv' t')
      (by
        intro j _ hj
        simp [hj])
      (Sum.inl χ₀) (Finset.inl_mem_disjSum.mpr hχ₀S) hr
      (by
        show c t⁻¹ χ₀ * σ t r - c t⁻¹ χ₀ * σ t r / r * r = 0
        rw [div_mul_cancel₀ _ hr, sub_self])
      i hi
    have e' : r * (c t⁻¹ (Sum.elim id id i) * σ t (v' i)) = c t⁻¹ χ₀ * σ t r * v' i := by
      have hz' : c t⁻¹ (Sum.elim id id i) * σ t (v' i) = c t⁻¹ χ₀ * σ t r / r * v' i :=
        sub_eq_zero.mp hz
      rw [hz']
      field_simp
    have hc := hcinv t (Sum.elim id id i)
    have hc0 := hcinv t χ₀
    have h1 : σ t r * (σ t r)⁻¹ = 1 := mul_inv_cancel₀ hsr
    have h2 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    rw [map_mul, map_inv₀]
    linear_combination ((σ t r)⁻¹ * r⁻¹ * c t (Sum.elim id id i) * c t χ₀) * e'
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀ * c t (Sum.elim id id i) * c t⁻¹ (Sum.elim id id i)) * h2
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀) * hc
      + (r⁻¹ * c t (Sum.elim id id i) * v' i * c t χ₀ * c t⁻¹ χ₀) * h1
      + (r⁻¹ * c t (Sum.elim id id i) * v' i) * hc0
  refine ⟨χ₀, fun χ => r⁻¹ * v' (Sum.inl χ), fun χ => r⁻¹ * v' (Sum.inr χ), ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum]
    exact mul_ne_zero (inv_ne_zero hr) hLv'
  · have h1 := hMv' 1
    simp only [hone, _root_.one_mul] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← h1]
    ring
  · intro t χ hχ
    exact ⟨by simpa only [Sum.elim_inl, id_eq] using hfin t (Sum.inl χ) (Finset.inl_mem_disjSum.mpr hχ),
      by simpa only [Sum.elim_inr, id_eq] using hfin t (Sum.inr χ) (Finset.inr_mem_disjSum.mpr hχ)⟩

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.similitude_definite_form_isAlgebraic_on_vector : ∀ (Λ : Type) [AddCommGroup Λ] (Q : Λ → ℤ) (φ : Module.End ℤ Λ) (e : Λ) (q l r : ℕ), 2 ≤ l → (∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) → (∀ x, 0 ≤ Q x) → (∀ x, Q x = 0 → x = 0) → (∀ x, Q (φ x) = q * Q x) → (∀ n : ℕ, ∃ (χ : Polynomial ℤ) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ Polynomial.aeval φ χ e = l ^ n • y) → ∃ P : Polynomial ℤ, P ≠ 0 ∧ Polynomial.aeval φ P e = 0 ∧ ∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q := by
  first | exact @GlobalTheory.SimAlg.similitude_algebraic | exact GlobalTheory.SimAlg.similitude_algebraic | (intros; apply GlobalTheory.SimAlg.similitude_algebraic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem splitTorus_hom_eq_one_of_no_cocharacter :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) →
      ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  intro S B _ X _ _ _ h u hu
  classical
  let b := Module.Free.chooseBasis ℤ X
  let l : _ → (X →+ ULift.{0} ℤ) := fun i =>
    (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  let c : _ → (ULift.{0} ℤ →+ X) := fun i =>
    (zmultiplesHom X (b i)).comp (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom
  have h1 : ∀ i, SplitTorus.torusMap S ((c i).comp (l i)) ≫ u = 1 := fun i => by
    have e : SplitTorus.torusMap S (l i) ≫ u = 1 := h _ (inferInstanceAs
      (IsMonHom (SplitTorus.torusMap S (l i) ≫ u)))
    rw [SplitTorus.torusMap_comp, Category.assoc, e, MonObj.comp_one]
  have h2 : ∀ s : Finset (Module.Free.ChooseBasisIndex ℤ X),
      SplitTorus.torusMap S (∑ i ∈ s, (c i).comp (l i)) ≫ u = 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, SplitTorus.torusMap_zero, MonObj.one_comp]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, SplitTorus.torusMap_add, MonObj.mul_comp, h1, ih, _root_.mul_one]
  have h3 : (∑ i, (c i).comp (l i)) = AddMonoidHom.id X := by
    ext x
    rw [AddMonoidHom.finsetSum_apply]
    simpa [c, l] using b.sum_repr x
  have := h2 Finset.univ
  rwa [h3, SplitTorus.torusMap_id, Category.id_comp] at this

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_integral_ext_isAlgClosed_residueField' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  first | exact @GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField | exact GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField | (intros; apply GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem free_localizedModule_mul {C : Type} [CommRing C] (M : Type) [AddCommGroup M] [Module C M]
    (r g : C) (h : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) M)) :
    Module.Free (Localization.Away (r * g)) (LocalizedModule (Submonoid.powers (r * g)) M) := by
  let _ : Algebra (Localization.Away r) (Localization.Away (r * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away r) r g).toAlgebra
  have _ : IsScalarTower C (Localization.Away r) (Localization.Away (r * g)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away r) r g c).symm
  let _ : Module (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    Module.compHom _ (algebraMap (Localization.Away r) (Localization.Away (r * g)))
  have _ : IsScalarTower (Localization.Away r) (Localization.Away (r * g))
      (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun a b x => by
      show (a • b) • x = algebraMap _ (Localization.Away (r * g)) a • b • x
      rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower C (Localization.Away r) (LocalizedModule (Submonoid.powers (r * g)) M) :=
    ⟨fun c a x => by
      show algebraMap _ (Localization.Away (r * g)) (c • a) • x =
        c • algebraMap _ (Localization.Away (r * g)) a • x
      rw [Algebra.smul_def, map_mul, mul_smul,
        ← IsScalarTower.algebraMap_apply C (Localization.Away r) (Localization.Away (r * g)),
        algebraMap_smul]⟩
  have hr := LocalizedModule.isBaseChange (Submonoid.powers r) M
  have hrg := LocalizedModule.isBaseChange (Submonoid.powers (r * g)) M
  rw [← hr.lift_comp (LocalizedModule.mkLinearMap (Submonoid.powers (r * g)) M)] at hrg
  exact Module.Free.of_equiv (hr.of_comp hrg).equiv

theorem exists_smooth_free_away : ∀ (k C : Type) [Field k] [PerfectField k] [CommRing C] [Nontrivial C] [IsReduced C] [Algebra k C] [Algebra.FiniteType k C] (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M], ∃ f : C, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  intro k C _ _ _ _ _ _ _ M _ _ _
  have _ : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have _ : Algebra.FinitePresentation k C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have _ : Module.FinitePresentation C M := Module.finitePresentation_of_finite C M
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  have := hm.isPrime
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C)) (J := m) bot_le
  have _ : p.IsPrime := hp.1.1
  have _ : Ring.KrullDimLE 0 (Localization.AtPrime p) := Ring.KrullDimLE.of_isLocalization p hp _
  let _ : Field (Localization.AtPrime p) := (Ring.KrullDimLE.isField_of_isReduced).toField
  have _ : Algebra.IsSmoothAt k p := Algebra.FormallySmooth.of_perfectField
  have _ : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Free.of_divisionRing _ _
  obtain ⟨f₁, hf₁p, hf₁⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k p
  obtain ⟨r, hrp, hr, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  refine ⟨r * f₁, ?_, ?_, free_localizedModule_mul M r f₁ hr⟩
  · intro h0
    have : r * f₁ ∈ p := by rw [h0]; exact p.zero_mem
    exact (Ideal.IsPrime.mem_or_mem ‹_› this).elim hrp hf₁p
  · rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth] at hf₁ ⊢
    exact fun x hx => hf₁ (PrimeSpectrum.basicOpen_mul_le_right r f₁ hx)

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.CycAway
open NumberField

theorem isLocalization_of_le_closure {Ω : Type} [Field Ω] {n : ℕ} (h0 : (n : Ω) ≠ 0) (A : Type) [CommRing A]
    (T : Subring Ω) [Algebra A T] (hinj : Function.Injective (algebraMap A T)) (hinv : (n : Ω)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹})) :
    IsLocalization (Submonoid.powers (n : A)) T := by
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹}),
      ∃ m : ℕ, ∃ a, z * (n : Ω) ^ m = (algebraMap A T a : Ω) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | rfl
      · exact ⟨0, a, by simp⟩
      · exact ⟨1, 1, by simp [h0]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * n ^ k + b * n ^ m, ?_⟩
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, a, ha⟩ := hx
      refine ⟨m, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    simp only [map_pow, map_natCast]
    refine IsUnit.pow _ (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    simp [h0]
  · intro z
    obtain ⟨m, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨_, m, rfl⟩), Subtype.ext ?_⟩
    simp only [map_pow, map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem dedekind_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n a : ℕ} (hn : n.Prime)
    [IsCyclotomicExtension {n ^ a} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ a)) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) ∧ Algebra.FiniteType ℤ (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI := Fact.mk hn
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne_zero
  refine ⟨IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _, ?_⟩
  have h1 : Algebra.FiniteType ℤ (𝓞 K) := inferInstance
  have h2 : Algebra.FiniteType (𝓞 K) T :=
    have := IsLocalization.Away.finitePresentation (S := T) (n : 𝓞 K)
    inferInstance
  exact h1.trans h2

theorem exists_base : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n a : ℕ), n.Prime → ∃ (o : Subring Ω) (ze : oˣ), IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧ IsUnit (n : o) ∧ IsPrimitiveRoot (Units.map o.subtype.toMonoidHom ze) (n ^ a) ∧ o = Subring.closure {((ze : o) : Ω), (n : Ω)⁻¹} := by
  intro Ω _ _ _ n a hn
  haveI := Fact.mk hn
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  let K := CyclotomicField (n ^ a) ℚ
  haveI : IsCyclotomicExtension {n ^ a} ℚ K := CyclotomicField.isCyclotomicExtension (n ^ a) ℚ
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  let φ : K →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := K) (M := Ω)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec (n ^ a) ℚ K
  set ζ := IsCyclotomicExtension.zeta (n ^ a) ℚ K
  obtain ⟨hD, hF⟩ := dedekind_closure hn φ hζ
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  have hz : IsPrimitiveRoot (φ ζ) (n ^ a) := hζ.map_of_injective φ.injective
  let z : T := ⟨φ ζ, Subring.subset_closure (Or.inl rfl)⟩
  have hz' : IsPrimitiveRoot z (n ^ a) := IsPrimitiveRoot.of_map_of_injective (f := T.subtype) hz T.subtype_injective
  have hu : IsUnit z := hz'.isUnit (NeZero.ne _)
  refine ⟨T, hu.unit, hD, hF, ?_, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ⟨_, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext ?_)
    simp [h0]
  · rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz
  · rfl

end GlobalTheory.CycAway
end
