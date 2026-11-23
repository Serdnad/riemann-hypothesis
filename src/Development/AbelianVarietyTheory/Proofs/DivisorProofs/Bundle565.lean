module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle513
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective : ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε], (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m') := by
  first | (exact @GlobalTheory.EtC.extHom_of_quasiIso) | (exact GlobalTheory.EtC.extHom_of_quasiIso) | (intros; apply GlobalTheory.EtC.extHom_of_quasiIso  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R, ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  first | (exact @GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (exact GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (intros; apply GlobalTheory.EtC.cone_kinj_and_bijective_iff  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeClass

variable {R : Type} [CommRing R]

theorem mk_ofHom_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) :
    CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) = cpull f M 0 (CohomologyClass.mk (Cocycle.ofHom g)) := by
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem mk_injective_sgl (X : Shv R) (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (CohomologyClass.mk : Cocycle (sgl X) I 0 → CohomologyClass (sgl X) I 0) := by
  intro a b h
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff (m := -1) (hm := by norm_num)] at h
  obtain ⟨β, hβ⟩ := h
  have hβ0 : β = 0 := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    by_cases hp : p = 0
    · subst hp
      exact (CochainComplex.isZero_of_isStrictlyGE I 0 q (by omega)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  rw [hβ0, δ_zero] at hβ
  exact sub_eq_zero.1 (Cocycle.ext hβ.symm)

theorem cpull_single_injective {X Y : Shv R} (g : X ⟶ Y) [Epi g] (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map g) I 0) := by
  intro x y h
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  have h' := mk_injective_sgl X I h
  have hg : Epi (((CochainComplex.singleFunctor (Shv R) 0).map g).f 0) := by
    change Epi (((HomologicalComplex.single _ _ 0).map g).f 0)
    rw [HomologicalComplex.single_map_f_self]
    infer_instance
  congr 1
  refine Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    have e := congrArg (fun z : Cocycle (sgl X) I 0 => z.1.v 0 0 (add_zero 0)) h'
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.comp_v _ _ (zero_add 0) 0 0 0 (add_zero 0) (add_zero 0),
      Cochain.ofHom_v] at e
    exact (cancel_epi _).1 e
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

theorem mk_ofHom_eq_of_homotopy {K L : Cx R} (f g : K ⟶ L) (h : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  have e := congrArg (fun φ => φ (CohomologyClass.mk (Cocycle.ofHom (𝟙 L)))) ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.2.2.2 f g ⟨h⟩ L 0).1
  simpa only [← mk_ofHom_comp, Category.comp_id] using e

end GlobalTheory.EtC.ConeClass

namespace GlobalTheory.EtC.ConeClass

theorem cone_class_eq : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∀ (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) →
    CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)) ≫ resAug S.X₃)) =
      CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
  intro R _ S hS hc e hh
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI : QuasiIso (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) :=
    mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₃).IsKInjective := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsKInjective)
  haveI : (res R S.X₃).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsStrictlyGE 0)
  haveI : Epi S.g := hS.epi_g
  have hbij := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0
  obtain ⟨c, hc'⟩ := hbij.2 (CohomologyClass.mk (Cocycle.ofHom
    (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)))
  refine (mk_ofHom_comp _ _).trans (Eq.trans ?_ hc')
  refine congrArg _ ?_
  have hinr : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
      mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc = resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) := by
    simp [mappingCone.map]
  have hres : resAug S.X₂ ≫ resMap R S.g = (CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃ :=
    InjectiveResolution.Hom.ι'_comp_hom'
      ⟨InjectiveResolution.desc S.g (injectiveResolution _) (injectiveResolution _),
        InjectiveResolution.desc_commutes_zero _ _ _⟩
  apply cpull_single_injective S.g (res R S.X₃)
  have hA : cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
      (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃))) =
      CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) := by
    calc cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
            (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃)))
        = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃)) :=
          (mk_ofHom_comp _ _).symm
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ resMap R S.g)) := by rw [hres]
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :=
          (mk_ofHom_eq_of_homotopy _ _ (hh.compLeft (resAug S.X₂))).symm
  have hB1 : CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) =
      cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) := by
    rw [hc', mk_ofHom_comp]
  have hB2 : cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) =
      cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0 c := by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1, mappingCone.inr_descShortComplex]
    rfl
  have hC : (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :
        CohomologyClass (sgl S.X₂) (res R S.X₃) 0) =
      CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
    rw [reassoc_of% hinr]
  exact hA.trans (hC.trans (hB1.trans hB2))

end GlobalTheory.EtC.ConeClass
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverForms

open KaehlerDifferential

theorem exists_pow_smul_eq_zero {R C B : Type} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (g : C →ₐ[R] B) (f : C)
    (hloc : @IsLocalization.Away C _ f B _ g.toRingHom.toAlgebra)
    (L : Ω[C⁄R] →ₗ[R] Ω[B⁄R]) (hD : ∀ c, L (D R C c) = D R B (g c))
    (hs : ∀ (c : C) (α : Ω[C⁄R]), L (c • α) = g c • L α)
    (α : Ω[C⁄R]) (h : L α = 0) : ∃ m : ℕ, f ^ m • α = 0 := by
  letI : Algebra C B := g.toRingHom.toAlgebra
  haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have hL : ∀ β, L β = KaehlerDifferential.map R R C B β := by
    intro β
    have hβ : β ∈ Submodule.span C (Set.range (D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hβ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hD, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [hs, hx, (KaehlerDifferential.map R R C B).map_smul]
      exact algebraMap_smul B c _
  haveI := KaehlerDifferential.isLocalizedModule_map R C B (Submonoid.powers f)
  have h' : KaehlerDifferential.map R R C B α = KaehlerDifferential.map R R C B 0 := by
    rw [← hL, h, map_zero]
  obtain ⟨⟨c, hc⟩, hc0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
  obtain ⟨m, rfl⟩ := hc
  refine ⟨m, ?_⟩
  simpa [Submonoid.smul_def] using hc0

theorem eq_zero_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  intro R _ X s hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.card, fun k => Opposite.op (t.equivFin.symm k).1, fun w hw => ?_⟩
  have hcov : ∀ x : X, ∃ U ∈ t, x ∈ (U.1 : Set X) := fun x => by
    simpa using ht (Set.mem_univ x)
  have hV0 : ∀ U ∈ t, w.1 (Opposite.op U) = 0 := fun U hU => by
    have : evForm s (Opposite.op (t.equivFin.symm (t.equivFin ⟨U, hU⟩)).1) w = 0 := hw _
    have e : t.equivFin.symm (t.equivFin ⟨U, hU⟩) = ⟨U, hU⟩ := Equiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  apply Subtype.ext
  funext W
  obtain ⟨W₀⟩ := W
  have hW : IsAffineOpen W₀.1 := W₀.2
  let S : Set Γ(X, W₀.1) := {f | ∃ U ∈ t, X.basicOpen f ≤ U.1}
  have hS : Ideal.span S = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) ?_
    intro x hx
    obtain ⟨U, hU, hxU⟩ := hcov x
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, U, hU, hf⟩, hxf⟩
  let α : Ω[Sec s W₀.1⁄R] := w.1 (Opposite.op W₀)
  let I : Ideal (Sec s W₀.1) := LinearMap.ker (LinearMap.toSpanSingleton (Sec s W₀.1) _ α)
  have hrad : ∀ f ∈ S, f ∈ I.radical := by
    rintro f ⟨U, hU, hf⟩
    let D' : X.affineOpens := ⟨X.basicOpen f, hW.basicOpen f⟩
    let φ : (Opposite.op W₀ : AffOp X) ⟶ Opposite.op D' := (homOfLE (X.basicOpen_le f)).op
    let ψ : (Opposite.op U : AffOp X) ⟶ Opposite.op D' := (homOfLE hf).op
    have h0 : p1 (OAff s) φ α = 0 := by
      have e1 := w.2 φ
      have e2 := w.2 ψ
      rw [hV0 U hU, map_zero] at e2
      exact e1.symm.trans e2
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero (mp (OAff s) φ) f
      (hW.isLocalization_basicOpen f) (p1 (OAff s) φ) (p1_D (OAff s) φ) (oneFormsMapOfFunctorMorphism_smul (OAff s) φ) α h0
    exact ⟨m, by simpa [I] using hm⟩
  have hI : I = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff]
    have h2 := Ideal.span_le.2 hrad
    exact (show (⊤ : Ideal (Sec s W₀.1)) ≤ Ideal.span S from hS.ge).trans h2
  have h1 : (1 : Sec s W₀.1) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end GlobalTheory.CoverForms
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem mul_eq_zero_of_mem_map_sq {R : Type} [CommRing R] {I : Ideal R} (hI : I ^ 2 = 0) {B' : Type} [CommRing B']
    [Algebra R B'] {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B', Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

theorem isTheta_mul_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {B B₀ B' : Type}
    [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {p : B →+* B₀}
    {a b : B →ₐ[R] B'} {θ : Ω[B₀⁄R₀] →+ B'} (h : IsTheta I p a b θ) (x : B) {t : B'}
    (ht : t ∈ I.map (algebraMap R B')) : a x * t = b x * t := by
  have hd : (a x - b x) * t = 0 := by
    rw [← h.der x]; exact mul_eq_zero_of_mem_map_sq hI (h.mem _) ht
  rw [sub_mul, sub_eq_zero] at hd
  exact hd

theorem isTheta_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' : Type) [CommRing B'] [Algebra R B'] (a b c : B →ₐ[R] B') (θ θ' : Ω[B₀⁄R₀] →+ B'), IsTheta I p a b θ → (IsTheta I p b a (-θ) ∧ (IsTheta I p b c θ' → IsTheta I p a c (θ + θ')) ∧ (IsTheta I p a b θ' → θ = θ') ∧ (θ = 0 → a = b)) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' _ _ a b c θ θ' h
  refine ⟨⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ?_,
    fun h0 ↦ ?_⟩
  · rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, h.smul, mul_neg, isTheta_mul_eq hI h x (h.mem w)]
  · rw [AddMonoidHom.neg_apply, h.der, neg_sub]
  · exact (Ideal.neg_mem_iff _).2 (h.mem w)
  · rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, h.smul, h'.smul, mul_add,
      isTheta_mul_eq hI h x (h'.mem w)]
  · rw [AddMonoidHom.add_apply, h.der, h'.der]; ring
  · exact Ideal.add_mem _ (h.mem w) (h'.mem w)
  · ext w
    have hw : w ∈ Submodule.span B₀ (Set.range (KaehlerDifferential.D R₀ B₀)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, rfl⟩ := hy
      obtain ⟨x, rfl⟩ := hp y
      rw [h.der, h'.der]
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    | smul r u _ hu =>
      obtain ⟨x, rfl⟩ := hp r
      rw [h.smul, h'.smul, hu]
  · ext x
    have := h.der x
    rw [h0, AddMonoidHom.zero_apply] at this
    exact (sub_eq_zero.1 this.symm)

end GlobalTheory.Obs
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.isTheta_comp : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (E E' : Type) [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E'] (a b : B →ₐ[R] E) (θ : Ω[B₀⁄R₀] →+ E), IsTheta I p a b θ → (∀ g : E →ₐ[R] E', IsTheta I p (g.comp a) (g.comp b) ((g : E →+* E').toAddMonoidHom.comp θ)) ∧ ∀ (h : B' →ₐ[R] B) (h₀ : B₀' →ₐ[R₀] B₀), (∀ x, p (h x) = h₀ (p' x)) → IsTheta I p' (a.comp h) (b.comp h) (θ.comp (SemiHom.of_algHom h₀).m1.toAddMonoidHom) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' E E' _ _ _ _ a b θ hθ
  refine ⟨fun g ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h h₀ hh ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩⟩
  · change g (θ (p x • w)) = g (a x) * g (θ w)
    rw [hθ.smul, map_mul]
  · change g (θ (KaehlerDifferential.D R₀ B₀ (p x))) = g (a x) - g (b x)
    rw [hθ.der, map_sub]
  · have h1 := Ideal.mem_map_of_mem (g : E →+* E') (hθ.mem w)
    rw [Ideal.map_map, g.comp_algebraMap] at h1
    simpa using h1
  · change θ ((SemiHom.of_algHom h₀).m1 (p' x • w)) = a (h x) * θ ((SemiHom.of_algHom h₀).m1 w)
    rw [SemiHom.oneFormMap_smul_semilinear]
    change θ (h₀ (p' x) • _) = _
    rw [← hh, hθ.smul]
  · change θ ((SemiHom.of_algHom h₀).m1 (KaehlerDifferential.D R₀ B₀' (p' x))) = a (h x) - b (h x)
    rw [SemiHom.m1_D]
    change θ (KaehlerDifferential.D R₀ B₀ (h₀ (p' x))) = _
    rw [← hh, hθ.der]
  · exact hθ.mem _
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.haar_integral_over_coset_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (K : Subgroup (GL (Fin a) k)),
    IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) → ∀ F : GL (Fin a) k → ℂ,
    (∀ g x, x ∈ K → F (g * x) = F g) → ∀ R : Finset (GL (Fin a) k),
    (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') → (∀ g, F g ≠ 0 → ∃ r ∈ R, r⁻¹ * g ∈ K) →
    ∫ g, F g ∂(haarVol (KO k (Fin a))) = ((haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) : ℂ) * ∑ r ∈ R, F r := by
  first | exact @GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | exact GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets | (intros; apply GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets <;> assumption)
end

section

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.semilinearHom_connected_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | exact GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | (intros; apply GlobalTheory.PDivGroup.semiHom_app_eq_conn_part <;> assumption)
end

section

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.semilinearHom_etale_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | exact GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LocalDualNil

theorem exists_pow_mem_map {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]
    [Module.Finite O R] [IsLocalRing R] (ε : R →ₐ[O] O) (m : Ideal O) (hm : m.IsMaximal) :
    ∃ r : ℕ, ∀ φ : R, ε φ ∈ m → ∀ s, r ≤ s → φ ^ s ∈ m.map (algebraMap O R) := by
  set J : Ideal R := m.map (algebraMap O R) with hJ
  by_cases htop : J = ⊤
  · exact ⟨0, fun φ _ s _ => htop ▸ Submodule.mem_top⟩
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 htop
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ m) (R ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ J)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hr
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨r, fun φ hφ s hs => ?_⟩
  have h1 : ¬ IsUnit φ := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hφ (h.map ε))
  have h2 : Ideal.Quotient.mk J φ ∈ IsLocalRing.maximalIdeal (R ⧸ J) :=
    fun h => h1 (isUnit_of_map_unit _ _ h)
  have h3 := Ideal.pow_mem_pow h2 r
  rw [hr, Submodule.zero_eq_bot, Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h3
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [pow_add]
  exact J.mul_mem_right _ h3

theorem exists_pow_apply_mem : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (m : Ideal O), m.IsMaximal → IsLocalRing (G.dual.A n) → ∃ r : ℕ, ∀ φ : G.dual.A n,
      φ 1 ∈ m → ∀ s, r ≤ s → ∀ a : G.A n, (φ ^ s) a ∈ m := by
  intro p O _ G n m hm hloc
  obtain ⟨r, hr⟩ := exists_pow_mem_map (Bialgebra.counitAlgHom O (G.dual.A n)) m hm
  refine ⟨r, fun φ hφ s hs a => ?_⟩
  have h := hr φ hφ s hs
  generalize φ ^ s = ψ at h
  have h' : ψ ∈ m • (⊤ : Submodule O (G.dual.A n)) := by
    rw [Ideal.smul_top_eq_map]
    exact h
  refine Submodule.smul_induction_on (p := fun ψ : G.dual.A n => ψ a ∈ m) h' ?_ ?_
  · intro c hc χ _
    exact m.mul_mem_right (χ a) hc
  · intro x y hx hy
    exact m.add_mem hx hy

end GlobalTheory.LocalDualNil
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) = p ^ (n * G.height) := by
  first | exact @GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | exact GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | (intros; apply GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem <;> assumption)
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.eventually_zmodTorsorGaloisProductMap_bijective_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (actA : Multiplicative (ZMod q) →* (A ≃ₐ[F.obj j] A)),
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj j] A) q (GlobalTheory.TorsorColim.bcAct c.pt actA)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj k) (F.obj k ⊗[F.obj j] A) q
        (GlobalTheory.TorsorColim.bcAct (F.obj k) actA)) := by
  first | (exact @GlobalTheory.TorsorColim.eventually_prodMapOf_bijective) | (exact GlobalTheory.TorsorColim.eventually_prodMapOf_bijective) | (intros; apply GlobalTheory.TorsorColim.eventually_prodMapOf_bijective  <;> assumption)
end
