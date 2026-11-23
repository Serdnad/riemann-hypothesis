module

import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusImageFactorQuotientGoodOpen
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfiniteTorsionOrCocharacterOfArcAtInfinity
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle079
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle088
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.SecRatio

private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

private theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (e : U ≤ V) (a : R) : resG X e (constFn p V a) = constFn p U a := by
  unfold constFn
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  erw [Scheme.Hom.appLE_map]

variable {X : Scheme.{0}} {H : LB X}

theorem compat_res (s : H.Sec) (i j : H.ι) {V : X.Opens} (hi : V ≤ H.U i) (hj : V ≤ H.U j) :
    resG X hi (s.f i) = resG X (le_inf hi hj) (H.g i j : Γ(X, H.U i ⊓ H.U j)) * resG X hj (s.f j) := by
  have := congrArg (resG X (le_inf hi hj)) (s.compat i j)
  rw [map_mul] at this
  erw [rr, rr] at this
  exact this

theorem isUnit_res (t : H.Sec) (l : H.ι) {V : X.Opens} (hV : V ≤ Out.nonzeroLocus t)
    (hl : V ≤ H.U l) : IsUnit (resG X hl (t.f l)) := by
  apply GlobalTheory.ProjSpace.isUnit_resG_sec <;> assumption

theorem existsUnique_isRatio (hH : H.IsLB) (s t : H.Sec) (W : X.Opens)
    (hW : W ≤ Out.nonzeroLocus t) : ∃! r : Γ(X, W), IsRatio s t W r := by
  have hu : ∀ l, IsUnit (resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l)) :=
    fun l => isUnit_res t l (inf_le_left.trans hW) _
  have hq : ∀ l, ∃ q : Γ(X, W ⊓ H.U l), resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) =
      q * resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l) := fun l =>
    ⟨resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) * ↑(hu l).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : W ≤ ⨆ l, W ⊓ H.U l := by
    rw [← inf_iSup_eq, hH.cover, inf_top_eq]
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun l => W ⊓ H.U l) q := by
    intro i j
    change resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i) (q i) =
      resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j) (q j)
    have hi : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U i := inf_le_left.trans inf_le_right
    have hj : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U j := inf_le_right.trans inf_le_right
    have e1 := congrArg (resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have u := isUnit_res t i ((inf_le_left.trans inf_le_left).trans hW) hi
    apply u.mul_right_cancel
    rw [← e1, compat_res s i j hi hj, compat_res t i j hi hj, e2]
    ring
  obtain ⟨r, hr, hr'⟩ := X.sheaf.existsUnique_gluing' (fun l => W ⊓ H.U l) W
    (fun l => homOfLE inf_le_left) hcov q hcomp
  refine ⟨r, fun l => ?_, fun r' h' => hr' r' fun l => ?_⟩
  · have : resG X (inf_le_left : W ⊓ H.U l ≤ W) r = q l := hr l
    rw [this]; exact hq l
  · change resG X (inf_le_left : W ⊓ H.U l ≤ W) r' = q l
    apply (hu l).mul_right_cancel
    rw [← hq l]; exact (h' l).symm

theorem existsUnique_isLin {k : Type} [CommRing k] (p : X ⟶ Sp k) {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → k) : ∃! φ : H.Sec, IsLin p s a φ := by
  refine ⟨⟨fun l => ∑ j, constFn p (H.U l) (a j) * (s j).f l, fun i j => ?_⟩, fun l => rfl, ?_⟩
  · change resG X inf_le_left _ = _ * resG X inf_le_right _

    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_mul, res_const, res_const]
    have : resG X inf_le_left _ = _ * resG X inf_le_right _ := (s n).compat i j
    rw [this]; ring
  · rintro ⟨f, hf⟩ h
    have : f = _ := funext h
    subst this
    rfl

theorem ratio_and_lin : (∀ (X : Scheme.{0}) (H : LB X), H.IsLB → (∀ (s t : H.Sec) (W : X.Opens), W ≤ Out.nonzeroLocus t → ∃! r : Γ(X, W), IsRatio s t W r) ∧ ∀ (k : Type) [CommRing k] (p : X ⟶ Sp k) (J : Type) [Fintype J] (s : J → H.Sec) (a : J → k), ∃! φ : H.Sec, IsLin p s a φ) :=
  fun _ _ hH => ⟨existsUnique_isRatio hH, fun _ _ p _ _ s a => existsUnique_isLin p s a⟩

end GlobalTheory.SecRatio
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem spMap_factor_jK {V Ω : Type} [CommRing V] [IsDomain V] [Field Ω] (φ : V →+* Ω)
    (hi : Function.Injective φ) : ∃ r, spMap φ = r ≫ Out.jK V := by
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing V) hi), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsFractionRing.lift_algebraMap hi x).symm

theorem range_comp_ι_subset {X Y : Scheme.{0}} (U : Y.Opens) (f : X ⟶ U.toScheme) :
    Set.range (f ≫ U.ι) ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact (f x).2

theorem field_point_factor_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V) :
    (∃ r, q = r ≫ spMap (IsLocalRing.residue V)) ∨ ∃ r, q = r ≫ Out.jK V := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  by_cases h : RingHom.ker φ.hom = ⊥
  · exact Or.inr (spMap_factor_jK φ.hom ((RingHom.injective_iff_ker_eq_bot _).2 h))
  · have hp : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime _
    have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal V :=
      IsLocalRing.eq_maximalIdeal (hp.isMaximal h)
    refine Or.inl ⟨spMap (Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) φ.hom
      fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem isSemiAbelian_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (H : Over (Sp V)) [GrpObj H] [hc : IsCommMonObj H] (hs : Smooth H.hom) (hsep : IsSeparated H.hom)
    (hq : QuasiCompact H.hom)
    (h₁ : IsSemiAbelian ((Over.pullback (spMap (IsLocalRing.residue V))).obj H))
    (h₂ : IsSemiAbelian ((Over.pullback (Out.jK V)).obj H)) : IsSemiAbelian H := by
  have key : ∀ (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V), ∃ (T : Scheme.{0}) (r : Sp Ω ⟶ T) (f : T ⟶ Sp V),
      q = r ≫ f ∧ IsSemiAbelian ((Over.pullback f).obj H) := by
    intro Ω _ q
    rcases field_point_factor_dvr V Ω q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨_, r, _, hr, h₁⟩
    · exact ⟨_, r, _, hr, h₂⟩
  refine ⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩
  · obtain ⟨T, r, f, rfl, h⟩ := key K q
    have hg : GeometricallyConnected (pullback.snd H.hom f) := h.geomConnected
    rw [← (pullbackLeftPullbackSndIso H.hom f r).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K r
  · obtain ⟨T, r, f, rfl, h⟩ := key Ω q
    obtain ⟨E⟩ := h.fibres Ω r
    have : IsMonHom (pullCompIso r f H).symm.hom := inferInstanceAs (IsMonHom (pullCompIso r f H).inv)
    exact ⟨torusExtOfIso (pullCompIso r f H).symm E⟩

namespace Core

variable (C : Core)

theorem isPullback_a : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
  have h : IsPullback C.a (𝟙 _) C.G.ι (C.a ≫ C.G.ι) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using h.paste_vert C.cart

theorem isOpenImmersion_a : IsOpenImmersion C.a :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.isPullback_a.flip inferInstance

theorem range_a : Set.range C.a = C.GG.hom ⁻¹' C.U := by
  have h := C.isPullback_a
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    h.isoPullback.hom.surjective.range_comp, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

theorem isNoetherian_Z : IsNoetherian C.Z := by
  have := C.lft
  have := C.qc
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : CompactSpace C.Z := QuasiCompact.compactSpace_of_compactSpace C.π
  exact {}

theorem isNoetherian_P : IsNoetherian C.P.left := by
  have := C.isNoetherian_Z
  have := C.proper
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian C.P.hom
  have : CompactSpace C.P.left := QuasiCompact.compactSpace_of_compactSpace C.P.hom
  exact {}

theorem surjective_GG : Surjective C.GG.hom :=
  ⟨fun z => ⟨C.e z, by
    change (C.e ≫ C.G.ι ≫ C.P.hom) z = z
    rw [C.e_sec]; rfl⟩⟩

theorem nonempty_A : Nonempty C.A.left := by
  obtain ⟨z, hz⟩ := C.ne
  have := C.ab.geomConnected
  exact ⟨(C.A.hom.surjective ⟨z, hz⟩).choose⟩

theorem isIntegral_G : IsIntegral C.G.toScheme := by
  have : Nonempty C.G.toScheme := C.nonempty_A.map C.a
  exact isIntegral_of_isOpenImmersion C.G.ι

theorem flat_P : Flat (C.P.hom ≫ C.π) := by
  have := C.isNoetherian_P
  have := C.isOpenImmersion_a
  have := C.nonempty_A
  have := C.flat
  have := C.ab.smooth
  have : TopologicalSpace.NoetherianSpace C.A.left :=
    (C.a ≫ C.G.ι).isOpenEmbedding.isInducing.noetherianSpace
  have : IsDominant (C.a ≫ C.G.ι) :=
    ⟨(C.a ≫ C.G.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsSchemeTheoreticallyDominant (C.a ≫ C.G.ι) := .of_isDominant _
  have : Flat ((C.a ≫ C.G.ι) ≫ C.P.hom ≫ C.π) := by
    rw [← Category.assoc, C.cart.w]
    infer_instance
  exact flat_of_isSchemeTheoreticallyDominant
    (fun _ _ inst h => (@Module.Flat.flat_iff_torsion_eq_bot_of_isBezout ℤ _ _ _ inst.toModule _ _).mpr h)
    (C.a ≫ C.G.ι) _

variable {C} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)


include τ in
theorem Test.cl : C.Cl y := by
  have hi : Function.Injective ((OO p).subtype.comp τ.j) := (OO p).subtype_injective.comp τ.j_inj
  obtain ⟨r, hr⟩ := spMap_factor_jK _ hi
  have e : gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := (Spec.map_comp _ _).symm.trans hr
  have e' : gPt p ≫ y = (r ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold Cl
  rw [e']
  exact range_comp_ι_subset _ _

theorem Test.charZero : CharZero τ.V :=
  RingHom.charZero ((OO p).subtype.comp τ.j)

theorem Test.isSemiAbelian : IsSemiAbelian τ.H := by
  obtain ⟨S, hS⟩ := τ.split
  have := τ.smooth
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact isSemiAbelian_of_fibres_dvr τ.V τ.H (SmoothOfRelativeDimension.smooth C.g _) τ.sep τ.qc
    (isSemiAbelian_of_isGt _ S _ hS)
    (isSemiAbelian_of_isAbelianScheme _ (PolPull.isAbelianScheme_of_isGrpPullback C.ab τ.φ_cart))

end Core

theorem core_basic : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  intro C
  have := C.proper
  have := C.isNoetherian_P
  have := C.flat_P
  have := C.surjective_GG
  have : TopologicalSpace.NoetherianSpace C.G.toScheme := C.G.ι.isOpenEmbedding.isInducing.noetherianSpace
  refine ⟨inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom)), C.isIntegral_G, ?_, C.flat_P, C.isOpenImmersion_a,
    C.isPullback_a, C.range_a, C.isNoetherian_Z, C.isNoetherian_P, inferInstance,
    fun p _ y τ => ⟨τ.cl, τ.charZero, τ.isSemiAbelian⟩⟩
  change Flat ((C.G.ι ≫ C.P.hom) ≫ C.π)
  rw [Category.assoc]
  infer_instance

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.fibreLaw_of_testCartesian : ∀ C : Core, C.TestCart → C.FibLaw := by
  first | exact @GlobalTheory.ZJ.Core.fibLaw_of_testCart | exact GlobalTheory.ZJ.Core.fibLaw_of_testCart | (intros; apply GlobalTheory.ZJ.Core.fibLaw_of_testCart <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module.Free ℤ X') (_ : Module.Finite ℤ X') (i' : splitTorus (Sp k) X' ⟶ G) (ρ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X'), IsMonHom i' ∧ IsMonHom ρ ∧ Surjective ρ.left ∧ ρ ≫ i' = i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i' V) := by
  first | exact @GlobalTheory.TorusImage.exists_factor_goodOpen | exact GlobalTheory.TorusImage.exists_factor_goodOpen | (intros; apply GlobalTheory.TorusImage.exists_factor_goodOpen <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.infinite_torsion_or_cocharacter_of_arc_at_infinity : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ a : Sp (FractionRing (PowerSeries k)) ⟶ G.left, a ≫ G.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → (¬ ∃ b : Sp (PowerSeries k) ⟶ G.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → Infinite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ p = 1} ∨ ∃ f : Gm (Sp k) ⟶ G, IsMonHom f ∧ f ≠ 1 := by
  first | exact @GlobalTheory.SS.infinite_torsion_or_cocharacter | exact GlobalTheory.SS.infinite_torsion_or_cocharacter | (intros; apply GlobalTheory.SS.infinite_torsion_or_cocharacter <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem RatModel.exists_ringHom_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) {U : Set M.Z} (hy : Set.range y ⊆ U) :
    ∃ ψ : M.ringOn U →+* K, ∀ a, ψ a = M.val y a :=
  ⟨(RatModel.valHom y _ (RatModel.range_eq_singleton y (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (RatModel.ringOn_le_O (hy ⟨_, rfl⟩))).toRingHom, fun _ => rfl⟩

theorem minors_regular_and_unit_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (R' : Subalgebra o Ω) (hR : S.R ≤ R') (n a : ℕ) (GG : Fin n → S.J → R'), S.Over₀ M U₀ → R' ≤ M.ringOn U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) → ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (∀ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k / S.th x₀ ^ (a * Fintype.card S.J) ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ≠ 0 ∧ S.th x₀ ^ (a * Fintype.card S.J) / (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ∈ M.O z) := by
  intro o Ω _ _ _ _ S M U₀ R' hR n a GG hO hR' hLL hT hsup hTT hcl hGG
  obtain ⟨hLL, -⟩ := hLL
  obtain ⟨-, -, -, hcp⟩ := hTT
  set D : (S.J → Fin n) → Ω := fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) with hD
  set m := a * Fintype.card S.J with hm

  have hDR : ∀ k, D k = ((Matrix.det (Matrix.of fun i j => GG (k i) j) : R') : Ω) := fun k =>
    ((R'.val.toRingHom.map_det (Matrix.of fun i j => GG (k i) j))).symm
  have hclosed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z,
      (∀ k, D k / S.th x₀ ^ m ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, D k ≠ 0 ∧ S.th x₀ ^ m / D k ∈ M.O z) := by
    intro z hz x₀ hx₀
    have h0 : S.th x₀ ≠ 0 := hx₀.1
    have hth : S.th x₀ ∈ M.ringOn U₀ := hO.le (S.th_mem x₀)
    have hinv : (S.th x₀)⁻¹ ∈ M.ringOn U₀ := hO.th_unit x₀ h0
    have hDm : ∀ k, D k ∈ M.ringOn U₀ := fun k => hDR k ▸ hR' (Subtype.prop _)
    have hφ : ∀ k, D k / S.th x₀ ^ m ∈ M.ringOn U₀ := fun k => by
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_mem (hDm k) (pow_mem hinv m)
    have htest : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y →
        (∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ ≤ 1) ∧
        ((∃ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ = 1) ↔ S.TT M z = ⊥) := by
      intro p _ y hy
      obtain ⟨ψ, hψ⟩ := M.exists_ringHom_val (gPt p ≫ y) hy.2
      obtain ⟨y₀, hAt, hb, ⟨τ⟩⟩ := hT z p y hy
      let y' : R' →+* PadicAlgCl p := ψ.comp (Subalgebra.inclusion hR').toRingHom
      have e : y₀ = y'.comp (Subalgebra.inclusion hR).toRingHom :=
        RingHom.ext fun b => (hAt b).trans (hψ ⟨b, hO.le b.2⟩).symm
      subst e
      obtain ⟨hs, hH⟩ := hsup z p y _ τ hy hAt
      have hδ := (hs x₀).1 hx₀
      have hpos := τ.δ_pos
      obtain ⟨h1, h2⟩ := GlobalTheory.T.maximal_minors_dual_thetaTest_lattice_bound o Ω S p _ τ hb hcl n (τ.δ ^ a) (fun k j => y' (GG k j)) (pow_pos hpos a)
        (hGG p y' τ hb)
      rw [← pow_mul, ← hm] at h1 h2
      have hpm : 0 < τ.δ ^ m := pow_pos hpos m
      have hval : ∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ * τ.δ ^ m =
          ‖Matrix.det (Matrix.of fun i j => y' (GG (k i) j))‖ := by
        intro k
        have e1 : (⟨_, hφ k⟩ : M.ringOn U₀) * ⟨_, hth⟩ ^ m =
            Subalgebra.inclusion hR' (Matrix.det (Matrix.of fun i j => GG (k i) j)) :=
          Subtype.ext ((div_mul_cancel₀ _ (pow_ne_zero m h0)).trans (hDR k))
        have e2 := congrArg (fun t => ‖ψ t‖) e1
        simp only [map_mul, map_pow, norm_mul, norm_pow] at e2
        rw [hψ, hψ] at e2
        rw [← hδ]
        refine e2.trans ?_
        exact congrArg norm (y'.map_det (Matrix.of fun i j => GG (k i) j))
      refine ⟨fun k => ?_, ?_⟩
      · have := h1 k
        rw [← hval] at this
        exact le_of_mul_le_mul_right (by simpa using this) hpm
      · rw [ThetaSys.TT, hH, ← h2]
        refine exists_congr fun k => ?_
        rw [← hval]
        exact ⟨fun h => by rw [h, _root_.one_mul], fun h => mul_right_cancel₀ hpm.ne' (h.trans (_root_.one_mul _).symm)⟩
    obtain ⟨⟨p, _, y, hy⟩, hreg⟩ := hLL U₀ le_rfl hO.ne z hz
    have hmem : ∀ k, D k / S.th x₀ ^ m ∈ M.O z := fun k =>
      hreg _ (hφ k) fun p _ y hy => (htest p y hy).1 k
    refine ⟨hmem, ?_⟩
    rw [← (htest p y hy).2]
    refine exists_congr fun k => ?_
    rw [RatModel.norm_val_eq_one_iff hy.1 (hmem k), RatModel.isUnit_O_iff]
    simp only [inv_div, ne_eq, div_eq_zero_iff, pow_ne_zero m h0, or_false]
  intro z x₀ hx₀
  have hTTeq : ∀ x : M.Z, S.supI M x = S.supI M z → S.TT M x = S.TT M z := fun x h => by
    rw [ThetaSys.TT, ThetaSys.TT, ThetaSys.HH, ThetaSys.HH, h]
  obtain ⟨x, -, hx, hzx, hs⟩ := hcp z ⊤ trivial
  obtain ⟨h1, h2⟩ := hclosed x hx x₀ (hs ▸ hx₀)
  refine ⟨fun k => RatModel.O_le_of_specializes hzx (h1 k), fun h => ?_, fun ⟨k, hk, hk'⟩ => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := h2.1 ((hTTeq x hs).trans h)
    exact ⟨k, hk, RatModel.O_le_of_specializes hzx hk'⟩
  · obtain ⟨x', hW, hx', -, hs'⟩ := hcp z ⟨_, M.isOpen_setOf_mem_O (S.th x₀ ^ m / D k)⟩ hk'
    exact (hTTeq x' hs').symm.trans ((hclosed x' hx' x₀ (hs' ▸ hx₀)).2.2 ⟨k, hk, hW⟩)

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_dense_closedPoints_chartSplitting : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t), t (⊥ : PrimeSpectrum R) = z ∧ ∃ (Ch : Charts ((Over.pullback t).obj C.GG).left) (d : ℕ) (c : Fin d → Ch.Cl) (Sg : Set (Sp R)), Dense Sg ∧ Ch.SplitOn c Sg ∧ ∀ x ∈ Sg, IsClosed ({t x} : Set C.Z) := by
  first | exact @GlobalTheory.ZJ.DenseSplit.exists_dense_splitOn | exact GlobalTheory.ZJ.DenseSplit.exists_dense_splitOn | (intros; apply GlobalTheory.ZJ.DenseSplit.exists_dense_splitOn <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_of_baseProduct_section : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  first | exact @GlobalTheory.UnitTheta.exists_sec_of_baseOver | exact GlobalTheory.UnitTheta.exists_sec_of_baseOver | (intros; apply GlobalTheory.UnitTheta.exists_sec_of_baseOver <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.valuations_torusExtension_points : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J) ∧ (∀ g : GtPtF u.D.toPre (PadicAlgCl p), ∃ ν : u.D.toPre.X →+ ℝ, u.GtN g ν) ∧ (∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', u.GtN g ν → u.GtN g ν' → ν = ν') ∧ (∀ (g g' g'' : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', GtPtF.IsAdd g g' g'' → u.GtN g ν → u.GtN g' ν' → u.GtN g'' (ν + ν')) ∧ ∀ (y : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)), GtPtF.IsIota y g → u.GtN g (QuadraticMap.polar l.q y) := by
  first | exact @GlobalTheory.ZH.TorusVal.main | exact GlobalTheory.ZH.TorusVal.main | (intros; apply GlobalTheory.ZH.TorusVal.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_secOn_power_of_local_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  first | exact @GlobalTheory.ZH.exists_secOn_genVal_of_bases | exact GlobalTheory.ZH.exists_secOn_genVal_of_bases | (intros; apply GlobalTheory.ZH.exists_secOn_genVal_of_bases <;> assumption)
end
