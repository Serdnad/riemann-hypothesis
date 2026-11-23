module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle137
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle005
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.IntegralConjFinExt

open Matrix

theorem norm_sum_le_one (l : ℕ) [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl l)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans
      (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem norm_one_apply_le (l : ℕ) [Fact l.Prime] (a : ℕ) (i j : Fin a) :
    ‖(1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

def intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) (PadicAlgCl l)) : Subgroup Γ where
  carrier := {g | ∀ i j, ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 ∧
    ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1}
  one_mem' := fun i j => by
    simp only [inv_one, map_one, Units.val_one]
    exact ⟨norm_one_apply_le l a i j, norm_one_apply_le l a i j⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [_root_.mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hg i k).1 (norm_nonneg _) (hh k j).1,
      norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hh i k).2 (norm_nonneg _) (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem isOpen_intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) (PadicAlgCl l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))) :
    IsOpen (intSubgroup l ρ : Set Γ) := by
  let V : Set Γ := ⋂ i, ⋂ j,
    ({g | ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1} ∩
     {g | ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1})
  have hVo : IsOpen V :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_lt (((hρ.matrix_elem i j).sub continuous_const).norm) continuous_const).inter
        (isOpen_lt ((((hρ.matrix_elem i j).comp continuous_inv).sub continuous_const).norm) continuous_const)
  have hV1 : (1 : Γ) ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, inv_one, map_one, Units.val_one,
      sub_self, norm_zero, zero_lt_one, and_self, implies_true]
  have hle : ∀ x y : PadicAlgCl l, ‖x - y‖ < 1 → ‖y‖ ≤ 1 → ‖x‖ ≤ 1 := fun x y hxy hy => by
    have := PadicAlgCl.isNonarchimedean l (x - y) y
    rw [sub_add_cancel] at this
    exact this.trans (max_le hxy.le hy)
  have hVU : V ⊆ (intSubgroup l ρ : Set Γ) := fun g hg i j => by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    exact ⟨hle _ _ (hg i j).1 (norm_one_apply_le l a i j), hle _ _ (hg i j).2 (norm_one_apply_le l a i j)⟩
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVo.mem_nhds hV1) hVU)



theorem exists_finExt_conj_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  intro l _ Γ _ _ _ _ _ a ρ hρ
  letI : DecidableEq Γ := Classical.decEq Γ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l Γ a ρ hρ ⟨⊥, inferInstance⟩
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let U := intSubgroup l ρ
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen _ (isOpen_intSubgroup l ρ hρ)
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  let T : Finset Γ := Finset.univ.image (fun q : Γ ⧸ U => q.out)
  have hTU : ∀ x : Γ, ∃ t ∈ T, t⁻¹ * x ∈ U := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U x
    refine ⟨(x : Γ ⧸ U).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hh, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact U.inv_mem h.2
  obtain ⟨r, hr⟩ := GlobalTheory.StableLattice.lift_of_integral (O := L.1) (K := PadicAlgCl l)
    Subtype.val_injective ρ (fun g i j => ⟨⟨_, hL g i j⟩, rfl⟩)
  have hre : ∀ g i j, (((r g : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j : PadicAlgCl l) =
      ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j := by
    intro g i j
    rw [← hr g, Matrix.GeneralLinearGroup.map_apply]
    rfl
  let e : L.1 ≃ₐ[Loc.OL L] FractionRing (Loc.OL L) :=
    IsLocalization.algEquiv (nonZeroDivisors (Loc.OL L)) L.1 (FractionRing (Loc.OL L))
  let σ : Γ →* GL (Fin a) (FractionRing (Loc.OL L)) :=
    (Matrix.GeneralLinearGroup.map e.toRingEquiv.toRingHom).comp r
  have hσ : ∀ x : Γ, ∃ t ∈ T, ∀ i j, (σ (t⁻¹ * x)).val i j ∈
        (algebraMap (Loc.OL L) (FractionRing (Loc.OL L))).range := by
    intro x
    obtain ⟨t, ht, hu⟩ := hTU x
    refine ⟨t, ht, fun i j => ?_⟩
    have hmem : ((r (t⁻¹ * x) : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j ∈ Loc.OL L := by
      rw [Formalism.BasicNotions.Examples₂.LB.mem_OL, hre]
      exact (hu i j).1
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [σ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply]
    rw [← e.commutes]
    rfl
  obtain ⟨P', hP'⟩ := GlobalTheory.StableLattice.exists_conj_integral σ T hσ
  let φ : FractionRing (Loc.OL L) →+* PadicAlgCl l :=
    (algebraMap L.1 (PadicAlgCl l)).comp e.symm.toRingEquiv.toRingHom
  have hφσ : ∀ g, Matrix.GeneralLinearGroup.map φ (σ g) = ρ g := by
    intro g
    rw [← hr g]
    ext i j
    simp only [σ, φ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.comp_apply]
    congr 1
    exact e.symm_apply_apply _
  refine ⟨L, Matrix.GeneralLinearGroup.map φ P', fun g i k => ?_⟩
  have h1 : (Matrix.GeneralLinearGroup.map φ P')⁻¹ * ρ g * Matrix.GeneralLinearGroup.map φ P' =
      Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') := by
    rw [MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ), MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ),
      MonoidHom.map_inv (Matrix.GeneralLinearGroup.map φ), hφσ]
  suffices key : ((Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') : GL (Fin a) (PadicAlgCl l)) :
      Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 by
    rw [← h1] at key
    exact key
  obtain ⟨z, hz⟩ := hP' g i k
  rw [Matrix.GeneralLinearGroup.map_apply, ← hz]
  have h2 : φ (algebraMap (Loc.OL L) (FractionRing (Loc.OL L)) z) = (((z : L.1)) : PadicAlgCl l) := by
    simp only [φ, RingHom.comp_apply]
    rw [← e.commutes z]
    show algebraMap L.1 (PadicAlgCl l) (e.symm (e _)) = _
    rw [e.symm_apply_apply]
    rfl
  rw [h2, GlobalTheory.IntOfFinExt.mem_intOf_iff]
  exact ⟨(z : L.1).2, (Formalism.BasicNotions.Examples₂.LB.mem_OL L _).1 z.2⟩

end GlobalTheory.IntegralConjFinExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.NonlocalTrait

theorem exists_common_ext {F L₁ L₂ : Type} [Field F] [Field L₁] [Field L₂] (a : F →+* L₁) (b : F →+* L₂) :
    ∃ (L : Type) (_ : Field L) (i : L₁ →+* L) (j : L₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct F L₁ L₂)
  letI := Ideal.Quotient.field m
  refine ⟨TensorProduct F L₁ L₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := F) (A := L₁) (B := L₂)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  congr 1
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

theorem torusExtension_iterate {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G))) :
    Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G))) := by
  obtain ⟨T⟩ := h
  exact ⟨torusExtOfIso (pullCompIso b a G) T⟩

theorem torusExtension_compose {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  exact ⟨torusExtOfIso (pullCompIso b a G).symm T⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.NonlocalTrait


open GlobalTheory.NonlocalTrait in
theorem GlobalTheory.exists_trait_nonlocal_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), ¬ IsLocalHom g →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ψ : R →+* V)
      (Ω : Type) (_ : Field Ω) (α : FractionRing V →+* Ω) (β : W →+* Ω),
      IsLocalHom ψ ∧ (∀ x ∈ maximalIdeal W, β x = 0) ∧
      (α.comp (algebraMap V (FractionRing V))).comp ψ = β.comp g ∧
      Nonempty (TorusExtension ((Over.pullback (spMap ((algebraMap V (FractionRing V)).comp ψ))).obj G)) := by
  intro R _ _ _ _ G _ hG W _ _ g hg
  set p : Ideal R := Ideal.comap g (maximalIdeal W) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  obtain ⟨r₀, hr₀u, hr₀⟩ : ∃ r, IsUnit (g r) ∧ ¬ IsUnit r := by
    by_contra h
    push_neg at h
    exact hg ⟨fun r hr => h r hr⟩
  have hr₀p : r₀ ∉ p := fun h => ((mem_maximalIdeal _).1 (Ideal.mem_comap.1 h)) hr₀u
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  haveI : IsLocalRing (R ⧸ p) := .of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hunit : ∀ r : R, IsUnit (Ideal.Quotient.mk p r) → IsUnit r := by
    intro r hr
    obtain ⟨b, hb⟩ := hr.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_contra hru
    have h1 : r * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hru
    have h2 : r * y - 1 ∈ maximalIdeal R :=
      hpm (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_sub, map_mul, hb, map_one, sub_self]))
    have h3 := (maximalIdeal R).sub_mem h1 h2
    rw [sub_sub_cancel] at h3
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hA : ¬ IsField (R ⧸ p) := by
    intro hF
    have h0 : Ideal.Quotient.mk p r₀ ≠ 0 := fun h => hr₀p (Ideal.Quotient.eq_zero_iff_mem.1 h)
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
    exact hr₀ (hunit r₀ (Units.mkOfMulEqOne _ b hb).isUnit)
  let k₀ := FractionRing (R ⧸ p)
  let φ₀ : R →+* k₀ := (algebraMap (R ⧸ p) k₀).comp (Ideal.Quotient.mk p)
  let σ : k₀ →+* AlgebraicClosure k₀ := algebraMap k₀ (AlgebraicClosure k₀)
  let G₀ := (Over.pullback (spMap φ₀)).obj G
  have hG₀ : IsSemiAbelian G₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm
      infer_instance
    · have := hG.smooth
      change Smooth (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · have := hG.separated
      change IsSeparated (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · have := hG.quasiCompact
      change QuasiCompact (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · have := hG.geomConnected
      change GeometricallyConnected (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ spMap φ₀)
      exact ⟨torusExtOfIso (pullCompIso q (spMap φ₀) G) E⟩
  haveI := hG₀.smooth
  haveI := hG₀.quasiCompact
  haveI := hG₀.separated
  have T₀ : Nonempty (TorusExtension ((Over.pullback (spMap σ)).obj G₀)) :=
    torusExtension_iterate _ _ G (by rw [← spMap_comp']; exact hG.fibres _ _)
  obtain ⟨T⟩ := T₀
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ G₀ T
  haveI : Finite s := hs.to_subtype
  let k' := IntermediateField.adjoin k₀ s
  haveI : FiniteDimensional k₀ k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  letI : Algebra (R ⧸ p) k' := ((algebraMap k₀ k').comp (algebraMap (R ⧸ p) k₀)).toAlgebra
  haveI : IsScalarTower (R ⧸ p) k₀ k' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨V, hV, hdom⟩ := (discreteValuationRing_dominating_noetherian_local (R := R ⧸ p) (K := k₀) k').1 hA
  rw [LocalSubring.le_def] at hdom
  obtain ⟨hsub, hloc⟩ := hdom
  have hmem : ∀ a : R ⧸ p, algebraMap (R ⧸ p) k' a ∈ V := fun a => hsub ⟨a, rfl⟩
  have hinjA : Function.Injective (algebraMap (R ⧸ p) k') :=
    (algebraMap k₀ k').injective.comp (IsFractionRing.injective (R ⧸ p) k₀)
  let ψA : (R ⧸ p) →+* V := (algebraMap (R ⧸ p) k').codRestrict V hmem
  let ψ : R →+* V := ψA.comp (Ideal.Quotient.mk p)
  have hψ : IsLocalHom ψ := by
    refine ⟨fun r hr => hunit r ?_⟩
    set a := Ideal.Quotient.mk p r
    have h1 : IsUnit (Subring.inclusion hsub ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩) := hr
    obtain ⟨⟨u, v, huv, _⟩, hu⟩ := hloc.map_nonunit _ h1
    have hu' : u = ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩ := hu
    subst hu'
    obtain ⟨b, hb⟩ := v.2
    refine (Units.mkOfMulEqOne a b (hinjA ?_)).isUnit
    have := congrArg Subtype.val huv
    rw [map_mul, map_one, hb]
    exact this
  let κ := ResidueField W
  let gA : (R ⧸ p) →+* κ := Ideal.Quotient.lift p ((residue W).comp g) (fun a ha => by
    show residue W (g a) = 0
    exact (residue_eq_zero_iff _).2 (Ideal.mem_comap.1 ha))
  have hgA : Function.Injective gA := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : residue W (g r) = 0 := ha
    have : g r ∈ maximalIdeal W := (residue_eq_zero_iff _).1 ha'
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.2 this)
  let g₀ : k₀ →+* κ := IsFractionRing.lift hgA
  let e : k' ≃ₐ[V] FractionRing V := IsLocalization.algEquiv (nonZeroDivisors V) k' (FractionRing V)
  let α₀ : k₀ →+* FractionRing V := e.toRingEquiv.toRingHom.comp (algebraMap k₀ k')
  let β₀ : FractionRing V →+* AlgebraicClosure k₀ := (algebraMap k' (AlgebraicClosure k₀)).comp e.symm.toRingEquiv.toRingHom
  have hβα : β₀.comp α₀ = σ := by
    ext x
    simp [α₀, β₀, σ]
  have hsr : s ⊆ Set.range β₀ := fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin k₀ s hx⟩, by simp [β₀]⟩
  have T₂ := torusExtension_compose _ _ G (H (FractionRing V) α₀ β₀ hβα hsr)
  have key : α₀.comp φ₀ = (algebraMap V (FractionRing V)).comp ψ := by
    ext r
    show e (algebraMap k₀ k' (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) =
      algebraMap V (FractionRing V) (ψA (Ideal.Quotient.mk p r))
    rw [← e.commutes]
    rfl
  obtain ⟨L, _, i, j, hij⟩ := exists_common_ext α₀ g₀
  refine ⟨V, inferInstance, inferInstance, hV, ψ, L, inferInstance, i, j.comp (residue W), hψ, ?_, ?_, ?_⟩
  · intro x hx
    simp [(residue_eq_zero_iff x).2 hx]
  · rw [RingHom.comp_assoc, ← key]
    ext r
    have h1 := congrArg (fun f => f (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) hij
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 ⊢
    show i (α₀ (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) = _
    rw [h1]
    simp [g₀, gA, φ₀, IsFractionRing.lift_algebraMap]
  · rw [← key, spMap_comp']
    exact T₂
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.InertiaTwoPlaces

open Polynomial

theorem fix_of_fix_integral {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (h : ∀ b : Ω, IsIntegral ℤ b → σ b = b) : σ = 1 := by
  ext x
  obtain ⟨s, t, hs, ht, hs1, e⟩ := ReciprocityTheory.Gal.exists_den E (⊤ : ValuationSubring Ω) (x := x)
    ((ValuationSubring.valuation_le_one_iff _ _).mpr trivial)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have h2 : σ s * σ x = σ t := by rw [← map_mul, e]
  rw [h s hs, h t ht, ← e] at h2
  exact mul_left_cancel₀ hs0 h2

theorem eq_of_mem_Ine_of_mem_Ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A,
    σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  intro E Ω _ _ _ _ _ A A' P hA hA' σ hσ hσ' hne
  by_contra hAA
  apply hne
  apply fix_of_fix_integral
  intro b hb
  by_contra hD
  have hD0 : σ b - b ≠ 0 := sub_ne_zero.mpr hD
  set f0 := minpoly ℤ b with hf0
  have hf0m : f0.Monic := minpoly.monic hb
  have hf0b : Polynomial.aeval b f0 = 0 := minpoly.aeval ℤ b
  set d := f0.natDegree with hd
  have hnat : ∀ n : ℕ, A'.valuation (n : Ω) ≤ 1 := fun n => ReciprocityTheory.Gal.valuation_natCast_le_one A' n
  obtain ⟨m, hdm, hmu⟩ : ∃ m : ℕ, d ≤ m ∧ A'.valuation (m : Ω) = 1 := by
    by_cases h1 : A'.valuation (d : Ω) = 1
    · exact ⟨d, le_rfl, h1⟩
    refine ⟨d + 1, Nat.le_succ d, ?_⟩
    by_contra h2
    have l1 : A'.valuation (d : Ω) < 1 := lt_of_le_of_ne (hnat d) h1
    have l2 : A'.valuation ((d + 1 : ℕ) : Ω) < 1 := lt_of_le_of_ne (hnat _) h2
    have : A'.valuation (((d + 1 : ℕ) : Ω) - (d : Ω)) < 1 := by
      rw [sub_eq_add_neg]
      exact Valuation.map_add_lt _ l2 (by rw [Valuation.map_neg]; exact l1)
    push_cast at this
    simp at this
  set f1 : Polynomial ℤ := Polynomial.X ^ (m - d) * f0 with hf1
  have hf1m : f1.Monic := (Polynomial.monic_X_pow _).mul hf0m
  have hf1d : f1.natDegree = m := by
    rw [hf1, (Polynomial.monic_X_pow _).natDegree_mul hf0m, Polynomial.natDegree_X_pow, ← hd]
    omega
  have hf1b : Polynomial.aeval b f1 = 0 := by simp [hf1, hf0b]
  have hσA : σ ∈ Dec (F := E) A := Ine_le_Dec A hσ
  have hbD : IsIntegral ℤ (σ b - b) :=
    (hb.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)).sub hb
  have hc : IsIntegral ℤ ((σ b - b) ^ m) := hbD.pow m
  have hc0 : (σ b - b) ^ m ≠ 0 := pow_ne_zero _ hD0
  obtain ⟨e0, he0i, he0A, he0A'⟩ := GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other E Ω A A' P hA hA' (Ne.symm hAA) _ hc hc0
  obtain ⟨e, hei, hef, heA, heA'⟩ := GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element E Ω A A' σ hσ' e0 _ he0i he0A he0A'
  obtain ⟨ys, hcard, hys, hprod⟩ := GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial E Ω A' σ hσ' b e m f1 hei hef heA' hmu hf1m hf1d hf1b
  have hbm : A.valuation (b ^ m - 1) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A ((hb.pow m).sub isIntegral_one))
  have h1 : A.valuation (e * (b ^ m - 1)) < A.valuation (σ b - b) ^ m := by
    rw [Valuation.map_mul, ← Valuation.map_pow]
    calc A.valuation e * A.valuation (b ^ m - 1) ≤ A.valuation e * 1 := mul_le_mul_of_nonneg_left hbm zero_le'
      _ = A.valuation e := mul_one _
      _ < _ := heA
  have h2 : A.valuation (σ b - b) ^ m ≤ A.valuation ((ys.map (fun y => b - y)).prod) := by
    rw [map_multiset_prod, Multiset.map_map, ← hcard]
    rw [← Multiset.card_map (fun y => A.valuation (b - y)) ys]
    apply Multiset.pow_card_le_prod
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyf := (hys y hy).2
    have e1 : σ b - b = σ (b - y) - (b - y) := by rw [map_sub, hyf]; ring
    rw [e1, sub_eq_add_neg]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [Valuation.map_neg, GlobalTheory.T.iwasawaDecomposition_fact E Ω A σ hσA, max_self]
  rw [← hprod] at h2
  exact absurd h2 (not_le.mpr h1)

end GlobalTheory.InertiaTwoPlaces
end
end
