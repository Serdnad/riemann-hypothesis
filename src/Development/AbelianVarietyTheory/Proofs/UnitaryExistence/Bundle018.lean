module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaFunctionIsogenyRestriction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.PointInterp

variable {k : Type} [Field k] {X Y : Scheme.{0}}

def valueAt (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (p.appLE U ⊤ h).hom

theorem top_le_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (z : Spec (CommRingCat.of k)) :
    ⊤ ≤ p ⁻¹ᵁ U ↔ p z ∈ U :=
  ⟨fun h => h (show z ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial), fun h y _ => by
    obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum k) _ _
    exact h⟩

theorem valueAt_rs (p : Spec (CommRingCat.of k) ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) : valueAt p V h (rs X hle a) = valueAt p U h' a :=
  congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (BoxSection.appLE_res p hle h h' a)

theorem valueAt_cst (f : X ⟶ Spec (CommRingCat.of k)) (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : k) : valueAt p U h (cst f U c) = c := by
  refine (valueAt_rs p le_top h le_top _).trans ?_
  have e : p.appLE ⊤ ⊤ le_top = p.appTop := Scheme.Hom.appLE_eq_app p
  have e' : f.appTop ≫ p.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f.appTop ≫ p.appLE ⊤ ⊤ le_top) ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
  rw [e, e', Category.id_comp, Iso.inv_hom_id]
  rfl

theorem valueAt_ne_zero_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    valueAt p U h a ≠ 0 ↔ ⊤ ≤ p ⁻¹ᵁ X.basicOpen a := by
  have hb := Scheme.basicOpen_appLE p ⊤ U h a
  rw [top_inf_eq] at hb
  rw [← hb, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (valueAt p U h a) = (p.appLE U ⊤ h).hom a :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply _
    rw [this] at hu'
    exact (Scheme.basicOpen_of_isUnit _ hu').ge
  · intro hu
    refine IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ?_
    exact (Spec (CommRingCat.of k)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      (Scheme.mem_basicOpen _ _ y hy).1 (hu hy)

theorem eq_of_valueAt_eq (p q : Spec (CommRingCat.of k) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) (h : valueAt p U hp = valueAt q U hq) : p = q := by
  have e : p.appLE U ⊤ hp = q.appLE U ⊤ hq := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom]
    exact CommRingCat.hom_ext h
  have hV := isAffineOpen_top (Spec (CommRingCat.of k))
  have : IsIso hV.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi hV.fromSpec, ← hU.SpecMap_appLE_fromSpec p hV hp, ← hU.SpecMap_appLE_fromSpec q hV hq, e]

def subMulSec (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (s t : LB.Sec H) (c : k) : LB.Sec H where
  f j := s.f j - cst f _ c * t.f j
  compat i j := by
    rw [map_sub, map_sub, map_mul, map_mul, s.compat i j, t.compat i j]
    have e₁ := rs_cst f (inf_le_left : H.U i ⊓ H.U j ≤ H.U i) c
    have e₂ := rs_cst f (inf_le_right : H.U i ⊓ H.U j ≤ H.U j) c
    rw [e₁, e₂]
    ring

theorem top_le_nonzeroLocus_iff {H : LB X} (s : LB.Sec H) (p : Spec (CommRingCat.of k) ⟶ X) (l : H.ι)
    (hl : ⊤ ≤ p ⁻¹ᵁ H.U l) : ⊤ ≤ p ⁻¹ᵁ nonzeroLocus s ↔ valueAt p _ hl (s.f l) ≠ 0 := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  rw [valueAt_ne_zero_iff, top_le_iff _ _ z, top_le_iff _ _ z]
  exact mem_nonzeroLocus_iff_mem_basicOpen_chart s l ((top_le_iff _ _ z).1 hl)

theorem exists_separating (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (hH : H.IsLB) {n : ℕ}
    {s : Fin (n + 1) → LB.Sec H} (hs : VeryAmpleBy f H s) (p q : Spec (CommRingCat.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _) (hne : p ≠ q) :
    ∃ σ : LB.Sec H, ⊤ ≤ p ⁻¹ᵁ nonzeroLocus σ ∧ ¬ ⊤ ≤ q ⁻¹ᵁ nonzeroLocus σ := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show p z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
  have hpa := (top_le_iff p _ z).2 ha
  by_cases hqa : ⊤ ≤ q ⁻¹ᵁ nonzeroLocus (s a)
  swap
  · exact ⟨s a, hpa, hqa⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs.2 a
  obtain ⟨b, hb⟩ : ∃ b, valueAt p _ hpa (r b) ≠ valueAt q _ hqa (r b) := by
    by_contra hc
    push_neg at hc
    refine hne (eq_of_valueAt_eq p q haff hpa hqa (RingHom.ext fun x => ?_))
    obtain ⟨F, rfl⟩ := hsurj x
    induction F using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂Hom_C, valueAt_cst f p hp, valueAt_cst f q hq]
    | add F G hF hG => rw [map_add (f := _), map_add (f := _), map_add (f := _), hF, hG]
    | mul_X F j hF => rw [map_mul, MvPolynomial.eval₂Hom_X', map_mul, map_mul, hF, hc]
  have key : ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hxa : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (s a)) (c : k),
      ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (subMulSec f (s b) (s a) c) ↔ valueAt x _ hxa (r b) ≠ c := by
    intro x hx hxa c
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show x z ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    have hxl := (top_le_iff x _ z).2 hl
    have hm : ⊤ ≤ x ⁻¹ᵁ (nonzeroLocus (s a) ⊓ H.U l) := le_inf hxa hxl
    have e := congrArg (valueAt x _ hm) (hr b l)
    rw [map_mul, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxa] at e
    have h0 := (top_le_nonzeroLocus_iff (s a) x l hxl).1 hxa
    rw [top_le_nonzeroLocus_iff _ x l hxl]
    change valueAt x _ hxl ((s b).f l - cst f _ c * (s a).f l) ≠ 0 ↔ _
    rw [map_sub, map_mul, valueAt_cst f x hx, e, ← sub_mul, mul_ne_zero_iff, sub_ne_zero]
    exact and_iff_left h0
  exact ⟨subMulSec f (s b) (s a) (valueAt q _ hqa (r b)), (key p hp hpa _).2 hb,
    fun h => (key q hq hqa _).1 h rfl⟩

end GlobalTheory.PointInterp
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
namespace GlobalTheory.AbLaw.BaseChange

theorem cst_comp_specMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f' : X ⟶ Spec (CommRingCat.of R')) (W : X.Opens) (r : R) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) W r = cst f' W (g r) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).hom r)
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom] at h ⊢
  rw [h]

theorem ap_top_eq_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {W : X.Opens} (h : W ≤ f ⁻¹ᵁ ⊤) (d : Γ(Spec (CommRingCat.of R), ⊤)) :
    ∃ r, ap f h d = cst f W r := by
  obtain ⟨r, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of R))) (W := ⊤) rfl).2 d
  exact ⟨r, by rw [ap_cst, Category.comp_id]⟩

end GlobalTheory.AbLaw.BaseChange


open GlobalTheory.AbLaw.BaseChange in
theorem GlobalTheory.AbLaw.isProjBy_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsProjBy f → IsProjBy f' := by
  intro R R' _ _ g X X' f p q sq hf
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  have hloc : ∀ a, nonzeroLocus (boxSec p q (s a) (oneSec _)) = p ⁻¹ᵁ nonzeroLocus (s a) ⊓ q ⁻¹ᵁ ⊤ := fun a => by
    rw [nonzeroLocus_boxSec, nonzeroLocus_oneSec]
  have hbox : (box p q H (Inh.trivLB _)).IsLB := by
    have hK : (Inh.trivLB (Spec (CommRingCat.of R'))).IsLB := by
      refine ⟨?_, ?_, ?_⟩
      · simp [Inh.trivLB]
      · intro i
        exact (res _).map_one
      · intro i j k
        exact (congrArg₂ (· * ·) (res _).map_one (res _).map_one).trans
          ((_root_.one_mul _).trans (res _).map_one.symm)
    refine ⟨?_, ?_, ?_⟩
    · refine top_le_iff.1 fun y _ => ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, (Inh.trivLB _).U i by rw [hK.cover]; trivial)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
    · intro a
      refine Units.ext ((rs_mul p q _ _ _ _ _).trans ?_)
      rw [ap_g_self p hH, ap_g_self q hK, _root_.mul_one, Units.val_one]
    · intro a b c
      refine Units.ext ((congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).trans
        (Eq.trans ?_ (rs_mul p q _ _ _ _ _).symm))
      exact (mul_mul_mul_comm _ _ _ _).trans
        (congrArg₂ (· * ·) (ap_cocycle p hH _ _ _ _ _ _).symm (ap_cocycle q hK _ _ _ _ _ _).symm)
  refine ⟨box p q H (Inh.trivLB _), hbox, m,
    fun a => boxSec p q (s a) (oneSec _), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [hloc]
    exact ⟨hi, trivial⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' a
  have aff₂ : IsAffineOpen (⊤ : (Spec (CommRingCat.of R')).Opens) := isAffineOpen_top _
  have loc := hloc a
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  refine ⟨?_, fun b => ap p l₁ (r₁ b), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_ap p _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg (· * _) (ap_ratio p (hr₁ b k.1) _ _)).trans (_root_.mul_assoc _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C (g c), by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w, GlobalTheory.AbLaw.BaseChange.cst_comp_specMap]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X i, ?_⟩
        simp only [MvPolynomial.eval₂Hom_X']
    · change ap q l₂ _ ∈ _
      obtain ⟨r, hr⟩ := GlobalTheory.AbLaw.BaseChange.ap_top_eq_cst q l₂ d
      exact ⟨MvPolynomial.C r, by rw [MvPolynomial.eval₂Hom_C, hr]⟩
end
end

section

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.AdelicUnitaryTop

section Restricted

theorem secondCountable_restrictedProduct {ι : Type} [Countable ι] (R : ι → Type)
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) : SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hS : ∀ T : Finset ι, cofinite ≤ 𝓟 ((T : Set ι)ᶜ) := fun T =>
    le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  have hsc : ∀ T : Finset ι, SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((T : Set ι)ᶜ)]) :=
    fun T => RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he := fun T : Finset ι => RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  haveI : ∀ T : Finset ι, SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) := fun T =>
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa using h)

end Restricted

section Adeles

variable (F : Type) [Field F] [NumberField F]

theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.glint_finite_residueField v

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  Valued.integer.properSpace_iff_compactSpace_integer.1 (properSpace_adicCompletion F v)

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
      fun a b h => HeightOneSpectrum.ext h

theorem locallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI := properSpace_adicCompletion F
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (.of_forall fun v => isCompact_iff_compactSpace.2 (compactSpace_adicCompletionIntegers F v))

theorem secondCountable_finiteAdele : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI := properSpace_adicCompletion F
  haveI := countable_heightOneSpectrum F
  exact secondCountable_restrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun _ ↦ Valued.isOpen_valuationSubring _

theorem t2Space_finiteAdeleRing_of_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

theorem t2Space_infiniteAdeleRing_of_numberField_field : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  haveI := locallyCompact_finiteAdele F
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  haveI := secondCountable_finiteAdele F
  haveI := secondCountable_infiniteAdele F
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem t2Space_adeleRing_numberField : T2Space (AdeleRing (𝓞 F) F) :=
  haveI := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Adeles

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem nonempty_homeomorph :
    Nonempty (R ⊗[F] E ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem lcsc_HA [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) :=
  by apply _root_.UpperTheory.Reformulated.B.Yzd4.lcsc_HA <;> assumption

end Tensor

theorem lcsc_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  intro F E _ _ _ _ _ σ M J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  exact lcsc_HA (AF F) σ M J

end GlobalTheory.AdelicUnitaryTop
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.integralClosure_finite_local_complete_mixedChar : ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime → (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S → Module.Finite S (integralClosure S (FractionRing S)) ∧ ∃ _ : IsLocalRing (integralClosure S (FractionRing S)), IsNoetherianRing (integralClosure S (FractionRing S)) ∧ IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S))) (integralClosure S (FractionRing S)) := by
  first | exact @GlobalTheory.normalisation_finite_local_complete_of_mixedChar | exact GlobalTheory.normalisation_finite_local_complete_of_mixedChar | (intros; apply GlobalTheory.normalisation_finite_local_complete_of_mixedChar <;> assumption)
end

section

open Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.theta_function_isogeny_restriction : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ (M : ℕ) (Λ₁ : AddSubgroup (Fin g → ℂ)), Λ₁ ≤ Λ → (∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = M * k) ↔ v ∈ Λ₁) → ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin g) ℂ), P ≠ 0 → P.totalDegree + 2 ≤ M → ∃ y : Fin n → Fin g → ℂ, (∀ b, (M : ℂ) • y b ∈ Λ₁) ∧ ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun q => (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ)) (fun z : Fin n → Fin g → ℂ => ∏ b, Complex.exp (-(Real.pi * (star (y b) ⬝ᵥ Hm.mulVec (z b)))) * θ (z b + y b)) 0 ≠ 0 := by
  first | exact @GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero | exact GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero | (intros; apply GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero <;> assumption)
end
