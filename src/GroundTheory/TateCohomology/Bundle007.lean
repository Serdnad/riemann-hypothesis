module

public import GroundTheory.TateCohomology.Bundle004
public import GroundTheory.TateCohomology.Bundle003
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
import GroundTheory.TateCohomology.InducedNorm
public import GroundTheory.TateCohomology.PGroupCohTrivial
public import GroundTheory.TateCohomology.PGroupFree
public import GroundTheory.TateCohomology.Bundle001
public import GroundTheory.TateCohomology.Bundle006
public import GroundTheory.TateCohomology.TateConnecting
public import Mathlib.Tactic.Continuity
import GroundTheory.TateCohomology.CupProduct
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
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupHomology

universe u

section H1

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]

theorem isZero_groupHomology_one_iff (A : Rep.{u} k G) :
    IsZero (groupHomology A 1) ↔ ∀ y : G →₀ A, d₁₀ A y = 0 → ∃ c : G × G →₀ A, d₂₁ A c = y := by
  constructor
  · intro h y hy
    have h0 : H1π A ⟨y, LinearMap.mem_ker.mpr hy⟩ = 0 :=
      @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h) _ _
    exact LinearMap.mem_range.mp ((H1π_eq_zero_iff _).mp h0)
  · intro h
    have : Subsingleton (groupHomology A 1) := by
      suffices hz : ∀ z : groupHomology A 1, z = 0 from ⟨fun x y => by rw [hz x, hz y]⟩
      intro z
      induction z using H1_induction_on with
      | h z =>
        apply (H1π_eq_zero_iff z).mpr
        exact LinearMap.mem_range.mpr (h z.1 (LinearMap.mem_ker.mp z.2))
    exact ModuleCat.isZero_of_subsingleton _

variable {A : Rep.{u} k G} {B : Rep.{u} k' G}

theorem d₁₀_mapRange_addEquiv (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (y : G →₀ A) : d₁₀ B (Finsupp.mapRange e (map_zero e) y) = e (d₁₀ A y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [Finsupp.mapRange_add (map_add e), map_add (f := _), h₁, h₂]
  | single g a => rw [Finsupp.mapRange_single, d₁₀_single, d₁₀_single, map_sub, he]

theorem d₂₁_mapRange_addEquiv (e : A.V ≃+ B.V) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a))
    (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange e (map_zero e) c) = Finsupp.mapRange e (map_zero e) (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [Finsupp.mapRange_add (map_add e), map_add (f := _), h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange_single, d₂₁_single, d₂₁_single, Finsupp.mapRange_add (map_add e),
      Finsupp.mapRange_sub (map_sub e), Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single, he]

theorem isZero_groupHomology_one_of_addEquiv (e : A.V ≃+ B.V)
    (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a)) (h : IsZero (groupHomology A 1)) :
    IsZero (groupHomology B 1) := by
  rw [isZero_groupHomology_one_iff] at h ⊢
  intro y hy
  have hyy : Finsupp.mapRange e (map_zero e) (Finsupp.mapRange e.symm (map_zero e.symm) y) = y := by
    ext g; simp
  have hy' : d₁₀ A (Finsupp.mapRange e.symm (map_zero e.symm) y) = 0 := by
    apply e.injective
    rw [← d₁₀_mapRange_addEquiv e he, hyy, hy, map_zero]
  obtain ⟨c, hc⟩ := h _ hy'
  exact ⟨Finsupp.mapRange e (map_zero e) c, by rw [d₂₁_mapRange_addEquiv e he, hc, hyy]⟩

end H1

section Torsion

variable {k G : Type u} [CommRing k] [Group G]

theorem nsmul_id_hom_apply (M : Rep.{u} k G) (n : ℕ) (x : M) : (n • 𝟙 M).hom x = n • x := by
  rw [Rep.nsmul_hom]; rfl

theorem nsmul_eq_zero_of_surjective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) {n : ℕ} (hA : ∀ x : A, n • x = 0) (y : B) : n • y = 0 := by
  obtain ⟨x, rfl⟩ := hf y
  change n • f.hom.toLinearMap x = 0
  rw [← map_nsmul, hA, map_zero]

theorem nsmul_eq_zero_of_injective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) {n : ℕ} (hB : ∀ y : B, n • y = 0) (x : A) : n • x = 0 := by
  apply hf
  change f.hom.toLinearMap (n • x) = f.hom.toLinearMap 0
  rw [map_nsmul, map_zero]
  exact hB _

theorem nsmul_eq_zero_coind (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0)
    (x : coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M)) : n • x = 0 :=
  Subtype.ext (funext fun g => hM (x.1 g))

theorem nsmul_eq_zero_coindShift (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : coindShift M, n • y = 0 :=
  nsmul_eq_zero_of_surjective (coindSES.obj M).g
    ((Rep.epi_iff_surjective _).1 (coindSES_shortExact M).epi_g) (nsmul_eq_zero_coind M hM)

theorem nsmul_eq_zero_indShift [Fintype G] (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : indShift M, n • y = 0 := by
  classical
  let e := indCoindIso (G := G) (res (⊥ : Subgroup G).subtype M)
  have he : Function.Injective e.hom.hom := (Rep.mono_iff_injective e.hom).1 inferInstance
  have h₂ := nsmul_eq_zero_of_injective e.hom he (nsmul_eq_zero_coind M hM)
  exact nsmul_eq_zero_of_injective (indSES.obj M).f
    ((Rep.mono_iff_injective _).1 (indSES_shortExact M).mono_f) h₂

end Torsion

section ZMod

variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]

noncomputable def zmodRep (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) : Rep (ZMod p) G :=
  letI : Module (ZMod p) M := AddCommGroup.zmodModule hM
  Rep.of (X := M)
    { toFun := fun g => AddMonoidHom.toZModLinearMap p (M.ρ g).toAddMonoidHom
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }

variable [Fintype G]

theorem tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0)
    (h : IsZero (tateCohomology M (-2))) : TateAcyclic M ∧ CohTrivial M := by
  have h1 : IsZero (groupHomology M 1) := h.of_iso (tateNegTwoIsoH1 M).symm
  have h1' : IsZero (groupHomology (zmodRep p M hM) 1) :=
    isZero_groupHomology_one_of_addEquiv (AddEquiv.refl M.V) (fun _ _ => rfl) h1
  obtain ⟨ι, ⟨e⟩⟩ := exists_iso_free_of_isZero_groupHomology_one hG _ h1'
  have := free_asModule_of_iso_free e
  obtain ⟨φ, hφ⟩ := exists_sum_eq_of_basis (zmodRep p M hM) (Module.Free.chooseBasis _ _)
  refine ⟨tateAcyclic_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ,
    cohTrivial_of_sum_eq M
      (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M.V M.V _ _ M.hV2 M.hV2 ⟨φ, map_add φ⟩ ?_) hφ⟩
  all_goals
    intro n x
    have hmod : M.hV2 = AddCommGroup.toIntModule M.V := Subsingleton.elim _ _
    rw [hmod]
    exact map_zsmul φ n x

theorem tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) (q : ℤ)
    (hq : IsZero (tateCohomology M q)) : TateAcyclic M ∧ CohTrivial M :=
  tateAcyclic_cohTrivial_of_isZero_of_shift (fun M => ∀ x : M, p • x = 0)
    (fun M hM => nsmul_eq_zero_coindShift M hM) (fun M hM => nsmul_eq_zero_indShift M hM)
    (fun M hM h => tateAcyclic_cohTrivial_of_isZero_neg_two_of_nsmul_eq_zero hG M hM h) q M hM hq

end ZMod

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Additive

variable [Fintype G]

instance tateCohomologyFunctor_additive (n : ℤ) :
    (tateCohomologyFunctor (R := k) (G := G) n).Additive := by
  unfold tateCohomologyFunctor
  infer_instance

end Additive

section Rep

variable (S : Subgroup G) [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex


omit [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)] in
theorem indResAdjunction_counit_app_hom_mk (A : Rep.{u} k G) (g : G) (a : A) :
    ((indResAdjunction k S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (res S.subtype A).ρ g a) = A.ρ g⁻¹ a := by
  change ((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = _
  simp

theorem unit_comp_indCoindIso_inv_comp_counit (A : Rep.{u} k G) :
    (resCoindAdjunction.{u, u} k S.subtype).unit.app A ≫ (indCoindIso (res S.subtype A)).inv ≫
      (indResAdjunction.{u} k S.subtype).counit.app A = S.index • 𝟙 A := by
  ext a
  change ((indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (((resCoindAdjunction.{u, u} k S.subtype).unit.app A).hom a)) =
    S.index • a

  rw [coindToInd_apply, map_sum]
  refine (Finset.sum_congr rfl (g := fun _ => a) fun x _ => ?_).trans ?_
  · induction x using Quotient.inductionOn with
    | h g =>
      rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
      change A.ρ g⁻¹ (A.ρ g a) = a
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · rw [Finset.sum_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]
    rfl

end Rep

section Tate

variable [Fintype G] (S : Subgroup G) [Fintype S]


open scoped Classical in
theorem tateIndIso_inv_eq (B : Rep.{u} k S) (n : ℤ) :
    (tateIndIso S B n).inv =
      (tateCoindIso S B n).inv ≫ (tateCohomologyFunctor n).map (indCoindIso.{u, u, u} B).inv :=
  rfl

theorem tateRes_app_comp_tateCores_app (A : Rep.{u} k G) (n : ℤ) :
    (tateRes S n).app A ≫ (tateCores S n).app A = S.index • 𝟙 (tateCohomology A n) := by
  rw [tateRes_app, tateCores_app, tateIndIso_inv_eq, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
    unit_comp_indCoindIso_inv_comp_counit, Functor.map_nsmul]
  exact congrArg (S.index • ·) ((tateCohomologyFunctor n).map_id A)

end Tate

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Naturality





theorem tateIsoH_map_apply {X Y : Rep.{u} k G} (φ : X ⟶ Y) (n : ℕ) [NeZero n]
    (x : tateCohomology X n) :
    (tateIsoH Y n n rfl).hom.hom (((tateCohomologyFunctor n).map φ).hom x) =
      groupCohomology.map (MonoidHom.id G) φ n ((tateIsoH X n n rfl).hom.hom x) :=
  congr(($((TateCohomology.isoGroupCohomology n).hom.naturality φ)).hom x)

end Naturality

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}
  (hX : X.ShortExact)

theorem tateIsoH_δ_zero_apply (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) (c : (tateComplex X.X₃).cycles 0)
    (hc : ((tateComplex X.X₃).iCycles 0).hom c = (cochainsIso₀ X.X₃).inv.hom z) :
    (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom
      ((TateCohomology.δ hX 0).hom (((tateComplex X.X₃).homologyπ 0).hom c)) =
      H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  have hxc : x ∈ cocycles₁ X.X₁ := mem_cocycles₁_of_comp_eq_d₀₁ hX hx
  let x₁ : (tateComplex X.X₁).X (0 + 1) := (cochainsIso₁ X.X₁).inv.hom x
  let x₂ : (tateComplex X.X₂).X 0 := (cochainsIso₀ X.X₂).inv.hom y
  have hd : ((tateComplex X.X₁).d (0 + 1) (0 + 1 + 1)).hom x₁ = 0 := by
    have e := congr(($(eq_d₁₂_comp_inv X.X₁)).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    have h0 : d₁₂ X.X₁ x = 0 := LinearMap.mem_ker.1 hxc
    rw [h0, map_zero] at e
    exact e
  have hx₂ : ((tateComplex.map X.g).f 0).hom x₂ = ((tateComplex X.X₃).iCycles 0).hom c := by
    rw [hc]
    funext v
    exact hy
  have hx₁ : ((tateComplex.map X.f).f (0 + 1)).hom x₁ = ((tateComplex X.X₂).d 0 (0 + 1)).hom x₂ := by
    have e := congr(($(eq_d₀₁_comp_inv X.X₂)).hom y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    refine Eq.trans ?_ e.symm
    funext v
    exact congrFun hx (v 0)
  have h1 := tδ_apply hX 0 (((tateComplex X.X₃).iCycles 0).hom c)
    (tate_d_iCycles_int _ 0 c) x₂ hx₂ x₁ hx₁ hd
  rw [tateCyclesMk_iCycles] at h1
  have h2 := tateIsoH_homologyπ X.X₁ 1 (tateCyclesMk X.X₁ (0 + 1) x₁ hd)
  refine (congrArg (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom h1).trans (h2.trans ?_)
  have h3 := cocyclesMk₁_eq X.X₁ ⟨x, hxc⟩
  refine Eq.trans ?_ (congrArg (π X.X₁ 1).hom h3)
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans ((iCycles_tateCyclesMk _ _ _ _).trans (iCocycles_mk _ _).symm)

end GroundTheory.GroupCoh
end
