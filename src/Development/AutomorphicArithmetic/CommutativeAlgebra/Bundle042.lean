module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle508
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle019
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitEqMultiplicativeGroupSection
public import Development.AutomorphicArithmetic.CommutativeAlgebra.KummerClassAddOfUnitSecAdd
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle034

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.KumRoot

private lemma map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (ModuleCat.Hom.hom (φ.hom.app (op V))) ((ModuleCat.Hom.hom (F.obj.map g.op)) x) =
    (ModuleCat.Hom.hom (G.obj.map g.op)) ((ModuleCat.Hom.hom (φ.hom.app (op U))) x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private lemma res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  show (ModuleCat.Hom.hom (F.obj.map k.op)) ((ModuleCat.Hom.hom (F.obj.map g.op)) x) =
    (ModuleCat.Hom.hom (F.obj.map (k ≫ g).op)) x
  rw [← ModuleCat.comp_apply, ← F.obj.map_comp]
  rfl

private lemma sec_map_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := by
  exact map_add _ a b

private lemma sec_map_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := by
  exact map_sub _ a b

private lemma sec_res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := by
  exact map_add _ a b

private lemma sec_res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (a : Sec F U) :
    Sec.res g (n • a) = n • Sec.res g a := by
  exact map_nsmul _ n a

private lemma map_smul_int {V : Scheme.{0}} (b : Sec Gm V) (n : ℤ) : Sec.map (n • 𝟙 Gm) b = n • b := by
  rfl

private lemma unitSec_pow {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) (n : ℕ) : unitSec (v ^ n) = n • unitSec v := by
  induction n with
  | zero => simp [UpperTheory.PicD.unitSec_one]
  | succ n ih => rw [pow_succ, UpperTheory.PicD.unitSec_mul, ih, succ_nsmul]

private lemma units_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom w) =
      Units.map (k ≫ g).appTop.hom.toMonoidHom w := by
  ext
  simp [Scheme.Hom.appTop, Scheme.Hom.app]
  rfl

private lemma ker_res {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (z : Sec ((res R F).X 0) U)
    (hz : Sec.map ((res R F).d 0 1) z = 0) : ∃ s : Sec F U, Sec.map (resι R F) s = z := by
  obtain ⟨α, hα0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R U (res R F) (-1) 0 1 (by norm_num) (by norm_num)).1 z hz
  obtain ⟨s, hs⟩ := (GlobalTheory.T.degreeZeroSectionClass_properties R F U).2.1.2 (CohomologyClass.mk α)
  refine ⟨s, ?_⟩
  have h1 := ((GlobalTheory.T.degreeZeroSectionClass_properties R F U).1 s α).2 hs.symm
  rw [← h1, hα0]
  show (ModuleCat.Hom.hom (((res R F).X 0).obj.map (𝟙 U).op)) z = z
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma resι_inj {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Sec.map (resι R F) a = Sec.map (resι R F) b) : a = b := by
  obtain ⟨α, hα⟩ := CohomologyClass.mk_surjective (secClass F a)
  have h1 := ((GlobalTheory.T.degreeZeroSectionClass_properties R F U).1 a α).2 hα
  have h2 := ((GlobalTheory.T.degreeZeroSectionClass_properties R F U).1 b α).1 (h1.trans h)
  exact (GlobalTheory.T.degreeZeroSectionClass_properties R F U).2.1.1 (hα.symm.trans h2)

variable (q : ℕ) [NeZero q]

private noncomputable def kp {V : Scheme.{0}} (s : Sec (tw q 1) V) : Sec Gm V :=
  Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from s)

private lemma kp_add {V : Scheme.{0}} (s t : Sec (tw q 1) V) : kp q (s + t) = kp q s + kp q t := by
  unfold kp
  exact sec_map_add _ _ _

private lemma kp_res {W V : Scheme.{0}} (k : W ⟶ V) (s : Sec (tw q 1) V) :
    Sec.res k (kp q s) = kp q (Sec.res k s) := by
  unfold kp
  exact (map_res _ _ _).symm

private lemma kp_nsmul {V : Scheme.{0}} (s : Sec (tw q 1) V) : q • kp q s = 0 := by
  unfold kp
  have h0 := (UpperTheory.Deg2.kap_spec q).2.1
  have h1 : Sec.map ((q : ℤ) • 𝟙 Gm) (Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from s)) =
      Sec.map (UpperTheory.Deg2.kap q ≫ ((q : ℤ) • 𝟙 Gm)) (show Sec (UpperTheory.Deg2.T q) V from s) := rfl
  rw [← natCast_zsmul, ← map_smul_int, h1, h0]
  rfl

private lemma unique_datum {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (v v' : (Γ(V, ⊤))ˣ)
    (s s' : Sec (tw q 1) V) (hv : v ^ q = v' ^ q)
    (h : kumT q V v + Sec.map (resι _ (tw q 1)) s = kumT q V v' + Sec.map (resι _ (tw q 1)) s') :
    unitSec v + kp q s = unitSec v' + kp q s' := by
  have hx : Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec (v⁻¹ * v')) = 0 := by
    rw [map_smul_int, natCast_zsmul, ← unitSec_pow, mul_pow, ← hv, inv_pow, inv_mul_cancel,
      UpperTheory.PicD.unitSec_one]
  obtain ⟨a, ha⟩ := (UpperTheory.Deg2.kap_spec q).2.2.2.1 V hq (unitSec (v⁻¹ * v')) hx
  have e1 : unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) a := by
    rw [ha, ← UpperTheory.PicD.unitSec_mul, mul_inv_cancel_left]
  have e2 := UpperTheory.kummer_class_add_of_unitSec_add q V hq v v' a e1
  rw [e2, add_assoc] at h
  have h3 : Sec.map (resι _ (tw q 1)) s = Sec.map (resι _ (tw q 1)) ((show Sec (tw q 1) V from a) + s') := by
    rw [sec_map_add]
    exact add_left_cancel h
  have hs := resι_inj _ _ _ _ h3
  rw [hs, kp_add, e1, add_assoc]
  rfl

end UpperTheory.KumRoot

open UpperTheory.KumRoot in
theorem UpperTheory.exists_root_of_kummer_class_eq_zero :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (w : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q w = 0 → ∃ v : (Γ(X, ⊤))ˣ, v ^ q = w := by
  intro q _ X w hq hw
  obtain ⟨γ, hγ, -, hγ2⟩ := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).1 X w hq
  rw [hw] at hγ
  obtain ⟨y, hy⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).2 γ).2.1 hγ
  have hqV : ∀ {V : Scheme.{0}} (g : V ⟶ X), IsUnit (q : Γ(V, ⊤)) := by
    intro V g
    have := hq.map g.appTop.hom
    simpa using this
  let D : (V : Scheme.{0}) → (V ⟶ X) → Sec Gm V → Prop := fun V g b =>
    ∃ (v : (Γ(V, ⊤))ˣ) (s : Sec (tw q 1) V),
      v ^ q = Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop g)) w ∧
      Sec.res g y = kumT q V v + Sec.map (resι _ (tw q 1)) s ∧ b = unitSec v + kp q s
  have hA : ∀ {V : Scheme.{0}} (g : V ⟶ X) (v : (Γ(V, ⊤))ˣ),
      v ^ q = Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop g)) w → ∃ b, D V g b := by
    intro V g v hv
    have e := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := sch.obj X) (I := res (ZMod q) (tw q 1)) (n := 1)).2.1
      (γ : Cochain _ _ 1) 0 1 (by norm_num) V X g (𝟙 X)
    have hd : Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (Sec.res g y - kumT q V v) = 0 := by
      rw [sec_map_sub, map_res, hy, sub_eq_zero]
      refine e.trans ?_
      exact hγ2 V g v hv
    obtain ⟨s, hs⟩ := ker_res _ V _ hd
    exact ⟨_, v, s, hv, by rw [hs]; abel, rfl⟩
  have hB : ∀ {V : Scheme.{0}} (g : V ⟶ X) (b b' : Sec Gm V), D V g b → D V g b' → b = b' := by
    intro V g b b' ⟨v, s, hv, hs, hb⟩ ⟨v', s', hv', hs', hb'⟩
    rw [hb, hb']
    exact unique_datum q (hqV g) v v' s s' (hv.trans hv'.symm) (hs.symm.trans hs')
  have hC : ∀ {V W : Scheme.{0}} (g : V ⟶ X) (k : W ⟶ V) (b : Sec Gm V), D V g b → D W (k ≫ g) (Sec.res k b) := by
    intro V W g k b ⟨v, s, hv, hs, hb⟩
    refine ⟨Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop k)) v, Sec.res k s, ?_, ?_, ?_⟩
    · rw [← map_pow, hv]
      exact units_comp k g w
    · rw [← res_comp, hs, sec_res_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V k v (hqV g), map_res]
      rfl
    · rw [hb, sec_res_add, UpperTheory.PicD.unitSec_res, kp_res]
      rfl
  have hloc : Loc X fun V g => ∃ b, D V g b :=
    GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 X _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q X).2.2.2 hq w) (fun V g ⟨v, hv⟩ => hA g v hv)
  obtain ⟨S, hS, hSP⟩ := hloc
  obtain ⟨b0, hb0⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ Gm X).2 S hS (fun V g hg => Classical.choose (hSP V g hg))
    (fun V W g k hg => hB (k ≫ g) _ _ (hC g k _ (Classical.choose_spec (hSP V g hg)))
      (Classical.choose_spec (hSP W (k ≫ g) (S.downward_closed hg k))))
  obtain ⟨u, hu⟩ := UpperTheory.exists_unit_eq_multiplicativeGroup_section X b0
  refine ⟨u, UpperTheory.eq_of_unitGlobalSection_eq X _ _ ?_⟩
  rw [unitSec_pow, hu]
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ Gm X).1
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, s, hv, -, hb⟩ := Classical.choose_spec (hSP V g hg)
  rw [sec_res_nsmul, hb0 V g hg, hb, nsmul_add, kp_nsmul, add_zero, ← unitSec_pow, hv,
    UpperTheory.PicD.unitSec_res]
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.exists_isPullback_iff_preimage {V₀ X' U₀ X : Scheme.{0}} (v : V₀ ⟶ X') (m : X' ⟶ X) (u : U₀ ⟶ X)
    [IsOpenImmersion v] [IsOpenImmersion u] :
    (∃ w, IsPullback v w m u) ↔ m ⁻¹ᵁ u.opensRange = v.opensRange := by
  constructor
  · rintro ⟨w, hw⟩
    ext x
    change x ∈ m ⁻¹' Set.range u ↔ x ∈ Set.range v
    rw [← Scheme.Pullback.range_fst]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨hw.isoPullback.inv b, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_inv_fst]
    · rintro ⟨a, rfl⟩
      refine ⟨hw.isoPullback.hom a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hw.isoPullback_hom_fst]
  · intro h
    have hr : Set.range v = Set.range (pullback.fst m u) := by
      rw [Scheme.Pullback.range_fst]
      have := congrArg (fun O : X'.Opens => (O : Set X')) h
      exact this.symm
    let e := IsOpenImmersion.isoOfRangeEq v (pullback.fst m u) hr
    refine ⟨e.hom ≫ pullback.snd m u, IsPullback.of_iso_pullback ⟨?_⟩ e ?_ rfl⟩
    · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr, Category.assoc,
        pullback.condition, Category.assoc]
    · exact IsOpenImmersion.isoOfRangeEq_hom_fac v (pullback.fst m u) hr

private lemma UpperTheory.pullback_map_symmetry_whisker {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y) :
    pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp) ≫
        (pullbackSymmetry G.hom Y.hom).hom =
      (pullbackSymmetry G.hom T.hom).hom ≫ (y ▷ G).left := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
    pullbackSymmetry_hom_comp_snd]
  · erw [pullback.lift_snd]
    simp
  · erw [pullback.lift_fst]
    simp

private lemma UpperTheory.isPullback_transport_symmetry {S : Scheme.{0}} {T Y G : Over S} (y : T ⟶ Y)
    (V : (T ⊗ G).left.Opens) {U₀ : Scheme.{0}} (u : U₀ ⟶ pullback G.hom Y.hom) (w : (V : Scheme.{0}) ⟶ U₀) :
    IsPullback (V.ι ≫ (pullbackSymmetry G.hom T.hom).inv) w
        (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y.left (𝟙 S) (by simp) (by simp)) u ↔
      IsPullback V.ι w (y ▷ G).left (u ≫ (pullbackSymmetry G.hom Y.hom).hom) := by
  have hsq := UpperTheory.pullback_map_symmetry_whisker (G := G) y
  constructor
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom) (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom) ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact hsq
    · simp
  · intro h
    refine h.of_iso (Iso.refl _) (pullbackSymmetry G.hom T.hom).symm (Iso.refl _)
      (pullbackSymmetry G.hom Y.hom).symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp

theorem UpperTheory.exists_clopRepOfRank_of_locallyNoetherian :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S), IsFinite G.hom → Etale G.hom → ∀ r : ℕ, ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.RepOfRank r G Y U := by
  intro S _ G hfin het r
  obtain ⟨H, h, U₀, u, hprop, hcl, hfin', hflat', hrk, huniv⟩ :=
    GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper S G.left G.hom hfin inferInstance inferInstance r
  haveI := hprop
  haveI := hcl
  haveI := hfin'
  haveI := hflat'
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : Etale (pullback.snd G.hom h) := inferInstance
  haveI : IsOpenImmersion u :=
    UpperTheory.isOpenImmersion_of_closedImmersion_flat_etale u (pullback.snd G.hom h) inferInstance hcl hflat' inferInstance
  let Y : Over S := Over.mk h
  let ι₀ : U₀ ⟶ (Y ⊗ G).left := u ≫ (pullbackSymmetry G.hom Y.hom).hom
  haveI : IsOpenImmersion ι₀ := by dsimp [ι₀]; infer_instance
  haveI : IsClosedImmersion ι₀ := by dsimp [ι₀]; infer_instance
  refine ⟨Y, ι₀.opensRange, ?_, ?_, ?_⟩
  · exact ι₀.isClosedEmbedding.isClosed_range
  · intro y
    have hp : UpperTheory.RepresentationRank.proj ι₀.opensRange = ι₀.isoOpensRange.inv ≫ (u ≫ pullback.snd G.hom h) := by
      rw [Iso.eq_inv_comp]
      change ι₀.isoOpensRange.hom ≫ (ι₀.opensRange.ι ≫ pullback.fst Y.hom G.hom) = _
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
      simp [ι₀, Y]
    rw [hp, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrk y
  · intro T V hV hVr
    obtain ⟨hVF, hVE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hV
    haveI := hVF
    haveI := hVE
    let v : (V : Scheme.{0}) ⟶ pullback G.hom T.hom := V.ι ≫ (pullbackSymmetry G.hom T.hom).inv
    haveI : IsClosedImmersion V.ι :=
      IsClosedImmersion.of_isPreimmersion V.ι (by rw [Scheme.Opens.range_ι]; exact hV)
    haveI : IsClosedImmersion v := by dsimp [v]; infer_instance
    have hvp : v ≫ pullback.snd G.hom T.hom = UpperTheory.RepresentationRank.proj V := by
      simp [v, UpperTheory.RepresentationRank.proj]
    haveI : IsFinite (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; exact hVF
    haveI : Flat (v ≫ pullback.snd G.hom T.hom) := by rw [hvp]; infer_instance
    obtain ⟨f, ⟨hf, w, hw⟩, huniq⟩ := huniv T.left T.hom V v inferInstance inferInstance
      inferInstance (fun t => by rw [hvp]; exact hVr t)
    have key : ∀ y' : T ⟶ Y, ((y' ▷ G).left ⁻¹ᵁ ι₀.opensRange = V ↔
        ∃ w, IsPullback v w
          (pullback.map G.hom T.hom G.hom Y.hom (𝟙 _) y'.left (𝟙 S) (by simp) (by simp)) u) := by
      intro y'
      have h1 := UpperTheory.exists_isPullback_iff_preimage V.ι (y' ▷ G).left ι₀
      rw [Scheme.Opens.opensRange_ι] at h1
      rw [← h1]
      exact exists_congr fun w => (UpperTheory.isPullback_transport_symmetry y' V u w).symm
    refine ⟨Over.homMk f hf, (key _).mpr ⟨w, hw⟩, ?_⟩
    intro y' hy'
    obtain ⟨w', hw'⟩ := (key y').mp hy'
    exact Over.OverMorphism.ext (huniq y'.left ⟨Over.w y', w', hw'⟩)
end
