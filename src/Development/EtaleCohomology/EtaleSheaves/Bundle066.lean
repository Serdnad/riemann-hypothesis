module

public import Development.EtaleCohomology.EtaleSheaves.Bundle030
public import Development.EtaleCohomology.EtaleSheaves.Bundle056
import Aesop.Frontend.Tactic
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
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
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.EtaleCohomology.EtaleSheaves.Bundle046
import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.BaseChange
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadProperPf

def LeafSpreadSeparated : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsSeparated c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → IsSeparated q'

end LateralTheory.E.LeafSpreadProperPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order

namespace LateralTheory.E.LeafStalkSmoothClosedPf

theorem coheight_le_topDim {X : Scheme.{0}} (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let := specializationOrder X
  have h := coheight_le_krullDim
    (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)
  rwa [coheight_orderIso] at h

theorem stalk_not_isField {X : Scheme.{0}} [IsIntegral X] (y : X) (hy : y ≠ genericPoint X) :
    ¬ IsField (X.presheaf.stalk y) := by
  intro hF
  let := hF.toField
  have h0 : ringKrullDim (X.presheaf.stalk y) = 0 := ringKrullDim_eq_zero_of_field _
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have hc : coheight y = 0 := by exact_mod_cast h0
  rw [coheight_eq_zero] at hc
  have h1 : y ≤ genericPoint X := genericPoint_specializes y
  have h2 : genericPoint X ≤ y := hc h1
  exact hy (Specializes.antisymm (h2 : y ⤳ genericPoint X) (h1 : genericPoint X ⤳ y)).eq

theorem stalk_dvr {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (y : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk y)) (hd : topologicalKrullDim X = 1)
    (hy : y ≠ genericPoint X) : IsDiscreteValuationRing (X.presheaf.stalk y) := by
  have hc : coheight y ≤ 1 := by
    have := (coheight_le_topDim y).trans hd.le
    exact_mod_cast this
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hc
  have : Ring.DimensionLEOne (X.presheaf.stalk y) :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain (X.presheaf.stalk y) := {}
  exact ((IsDiscreteValuationRing.TFAE _ (stalk_not_isField y hy)).out 3 1).mp this

set_option backward.isDefEq.respectTransparency false in
theorem LeafStalkSmoothClosed_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed := by
  intro Ω _ _ C c _ hc hn hd y hy
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have := hn y
  have : IsDiscreteValuationRing (C.presheaf.stalk y) := stalk_dvr y (hn y) hd hy
  have hE := LocallyOfFiniteType.stalkMap c y
  algebraize [(c.stalkMap y).hom]
  let p : Spec (CommRingCat.of Ω) := c y
  let K' := (Spec.structureSheaf Ω).presheaf.stalk p
  let e : Ω ≃ₐ[Ω] K' := IsLocalization.atUnits _ p.asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic Ω K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField Ω)).toField
  let : Field ((Sp Ω).presheaf.stalk (c y)) := this
  have : PerfectField ((Sp Ω).presheaf.stalk (c y)) :=
    Algebra.IsAlgebraic.perfectField (K := Ω) (L := (Spec.structureSheaf Ω).presheaf.stalk p)
  exact GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _

end LateralTheory.E.LeafStalkSmoothClosedPf
end
end

section

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.RelEqvInjPf

set_option linter.unusedSectionVars false
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

abbrev pl {K L : CochainComplex C ℤ} (f : K ⟶ L) (M : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass L M n →+ CohomologyClass K M n := cpre (Cocycle.ofHom f) M n n (zero_add n)

lemma inr_map {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) : mappingCone.inr φ' ≫ mappingCone.map φ' φ α β comm = β ≫ mappingCone.inr φ := by
  simp [mappingCone.map]

lemma map_fst {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) :
    (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp (mappingCone.fst φ).1 (zero_add 1) =
      (mappingCone.fst φ').1.comp (Cochain.ofHom α) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_zero 1) (by omega)]
    simp [mappingCone.map]
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain]
    simp

lemma laurent_adjoin_eq_of_image_eq {A' A I : CochainComplex C ℤ} (α : A' ⟶ A) {j k : ℤ} (hjk : j + 1 = k)
    (hα : Function.Injective (pl α I k)) (z : Cocycle A I k) (ξ : Cochain A' I j)
    (h : δ j k ξ = (Cochain.ofHom α).comp z.1 (zero_add k)) : ∃ t : Cochain A I j, δ j k t = z.1 := by
  have h0 : pl α I k (CohomologyClass.mk z) = 0 := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom α) z (zero_add k)) = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨j, hjk, ξ, h⟩
  have h1 : CohomologyClass.mk z = 0 := hα (h0.trans (map_zero _).symm)
  rw [CohomologyClass.mk_eq_zero_iff] at h1
  obtain ⟨j', hj', t, ht⟩ := h1
  obtain rfl : j' = j := by omega
  exact ⟨t, ht⟩

lemma exists_finset_adjoin_laurent_preimage {B' B I : CochainComplex C ℤ} (β : B' ⟶ B) {j k : ℤ} (hjk : j + 1 = k)
    (hβ : Function.Surjective (pl β I k)) (z : Cocycle B' I k) :
    ∃ (w : Cocycle B I k) (r : Cochain B' I j), δ j k r = z.1 - (Cochain.ofHom β).comp w.1 (zero_add k) := by
  obtain ⟨W, hW⟩ := hβ (CohomologyClass.mk z)
  obtain ⟨w, rfl⟩ := W.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom β) w (zero_add k)) = _ at hW
  have h2 := hW.symm
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at h2
  obtain ⟨j', hj', r, hr⟩ := h2
  obtain rfl : j' = j := by omega
  exact ⟨w, r, by rw [hr]; rfl⟩

theorem main {A B A' B' I : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) (l m n : ℤ) (hl : l + 1 = m) (hm : m + 1 = n)
    (hαi : Function.Injective (pl α I m)) (hβi : Function.Injective (pl β I n))
    (hβs : Function.Surjective (pl β I m)) :
    Function.Injective (pl (mappingCone.map φ' φ α β comm) I n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp _ c _) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m', hm', ξ0, hξ0⟩ := hy
  have em : m' = m := by omega
  subst m'
  change δ m n ξ0 = (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp c.1 (zero_add n) at hξ0
  set a := (mappingCone.inl φ).comp c.1 (show -1 + n = m by omega) with ha
  set b := (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add n) with hb
  have hdec : c.1 = mappingCone.descCochain φ a b hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm]; simp [ha, hb]
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hδa : δ m n a = n.negOnePow • (Cochain.ofHom φ).comp b (zero_add n) := by
    have h := congrArg (fun z => (mappingCone.inl φ).comp z (show -1 + (n + 1) = n by omega)) hc
    simp only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] at h
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg, sub_eq_zero] at h
    exact h
  have hδb : δ n (n + 1) b = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add (n + 1))) hc
    simpa using h

  have h1 : δ m n ((Cochain.ofHom (mappingCone.inr φ')).comp ξ0 (zero_add m)) =
      (Cochain.ofHom β).comp (Cocycle.mk b (n + 1) rfl hδb).1 (zero_add n) := by
    rw [δ_ofHom_comp, hξ0, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    rfl
  obtain ⟨η, hη⟩ := laurent_adjoin_eq_of_image_eq β hm hβi _ _ h1
  change δ m n η = b at hη

  set s := n.negOnePow with hs
  set γ := a - s • (Cochain.ofHom φ).comp η (zero_add m) with hγ
  have hδγ : δ m n γ = 0 := by
    rw [hγ, δ_sub, δ_units_smul, δ_ofHom_comp, hη, hδa, sub_self]
  set D0 := mappingCone.descCochain φ (0 : Cochain A I l) η hl with hD0
  have hcγ : c.1 = δ m n D0 + (mappingCone.fst φ).1.comp γ (by omega) := by
    rw [hdec, hD0, mappingCone.δ_descCochain _ _ _ _ _ hm, hη, hγ]
    simp only [mappingCone.descCochain, δ_zero, zero_add, Cochain.comp_sub]
    abel

  set ξ := ξ0 - (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp D0 (zero_add m) with hξ
  have h3 : δ m n ξ = (mappingCone.fst φ').1.comp ((Cochain.ofHom α).comp γ (zero_add m)) (by omega) := by
    rw [hξ, δ_sub, δ_ofHom_comp, hξ0, hcγ, Cochain.comp_add, add_sub_cancel_left,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, map_fst, Cochain.comp_assoc_of_second_is_zero_cochain]
  set p := (mappingCone.inl φ').comp ξ (show -1 + m = l by omega) with hp
  set q := (Cochain.ofHom (mappingCone.inr φ')).comp ξ (zero_add m) with hq
  have hdecξ : ξ = mappingCone.descCochain φ' p q hl := by
    rw [mappingCone.ext_cochain_from_iff _ l m hl]; simp [hp, hq]
  rw [hdecξ, mappingCone.δ_descCochain _ _ _ _ _ hm] at h3
  have h3a : δ l m p + s • (Cochain.ofHom φ').comp q (zero_add m) = (Cochain.ofHom α).comp γ (zero_add m) := by
    have h := congrArg (fun z => (mappingCone.inl φ').comp z (show -1 + n = m by omega)) h3
    simpa only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] using h
  have h3b : δ m n q = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ')).comp z (zero_add n)) h3
    simpa using h

  obtain ⟨w, r, hr⟩ := exists_finset_adjoin_laurent_preimage β hl hβs (Cocycle.mk q n hm h3b)
  change δ l m r = q - (Cochain.ofHom β).comp w.1 (zero_add m) at hr
  have hw : δ m n w.1 = 0 := Cocycle.δ_eq_zero w n
  have h4 : δ l m (p + s • (Cochain.ofHom φ').comp r (zero_add l)) =
      (Cochain.ofHom α).comp (Cocycle.mk (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) n hm
        (by rw [δ_sub, δ_units_smul, δ_ofHom_comp, hδγ, hw]; simp)).1 (zero_add m) := by
    change _ = (Cochain.ofHom α).comp (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) (zero_add m)
    rw [δ_add, δ_units_smul, δ_ofHom_comp, hr, Cochain.comp_sub, Cochain.comp_sub, ← h3a,
      Cochain.comp_units_smul]
    simp only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
    rw [comm, smul_sub]
    abel
  obtain ⟨t, ht⟩ := laurent_adjoin_eq_of_image_eq α hl hαi _ _ h4
  change δ l m t = γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m) at ht

  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, D0 + mappingCone.descCochain φ t w.1 hl, ?_⟩
  rw [δ_add, mappingCone.δ_descCochain φ t w.1 hl n hm, ht, hw, hcγ]
  simp
  rw [← hs, sub_add_cancel]

theorem RelEqvInj_of : LateralTheory.E.RelDescPf.RelEqvInj := by
  intro R _ F U E U' E' f f' u e comm hu he n
  exact main ((chains R).map f) ((chains R).map f') ((chains R).map u) ((chains R).map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (n - 1 - 1) (n - 1) n (by omega) (by omega)
    (hu (n - 1)).1 (he n).1 (he (n - 1)).2

end LateralTheory.E.RelEqvInjPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelInjectivity

def gN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') : cech (Spec.map u) ⟶ cech (Spec.map e) :=
  Arrow.mapCechNerve (f := Arrow.mk (yoneda.map (Spec.map u))) (g := Arrow.mk (yoneda.map (Spec.map e)))
    ⟨yoneda.map (Spec.map φ''), yoneda.map (Spec.map φ'), by
      simp only [Arrow.mk_hom, Functor.id_map, Functor.id_obj, Arrow.mk_left, Arrow.mk_right,
        ← Functor.map_comp, ← Spec.map_comp, h]⟩

def iN {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app _ := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro x y θ
    apply WidePullback.hom_ext
    · intro j
      erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, WidePullback.lift_π]
      exact Category.id_comp _
    · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, WidePullback.lift_base]
      exact Category.id_comp _

theorem iN_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : iN f ≫ cechAug f = sch.map f := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem iN_app_zero_iso {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((iN f).app (op ⦋0⦌)) := by
  refine ⟨⟨WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0, ?_, ?_⟩⟩
  · erw [WidePullback.lift_π]
  · apply WidePullback.hom_ext
    · intro j
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      erw [Category.assoc, WidePullback.lift_π, Category.id_comp]
      exact Category.comp_id _
    · erw [Category.assoc, WidePullback.lift_base, Category.id_comp]
      exact WidePullback.π_arrow _ _

theorem gN_aug {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    gN φ' e u φ'' h ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem gN_iN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    sch.map (Spec.map φ'') ≫ iN (Spec.map e) = iN (Spec.map u) ≫ gN φ' e u φ'' h := by
  have hw : yoneda.map (Spec.map φ'') ≫ yoneda.map (Spec.map e) = yoneda.map (Spec.map u) ≫ yoneda.map (Spec.map φ') := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h]
  refine NatTrans.ext (funext fun x => ?_)
  apply WidePullback.hom_ext
  · intro j
    erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, ← Category.assoc,
      WidePullback.lift_π, Category.id_comp]
    exact Category.comp_id _
  · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, ← Category.assoc,
      WidePullback.lift_base]
    exact hw

def Filt : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  (∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n → Function.Injective (pull R (disc.map (g.app (op ⦋p⦌))) F m) ∧
    Function.Surjective (pull R (disc.map (g.app (op ⦋p⦌))) F (m - 1))) →
  Function.Injective (rpull R g (disc.map h) b a comm F n)

def LvlRel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo : IsPushout φ' e u φ'',
  ∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n →
    Function.Injective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) m) ∧
    Function.Surjective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) (m - 1))

theorem LevelInj_of (hF : Filt) (hL : LvlRel) : LateralTheory.E.RelDescPf.LevelInj := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  refine ⟨gN φ' e u φ'' hpo'.w, gN_aug _ _ _ _ _, iN (Spec.map e), iN (Spec.map u), gN_iN _ _ _ _ _,
    iN_aug _, iN_aug _, ?_⟩
  exact hF hH (ZMod q) (tw q i) n (gN φ' e u φ'' hpo'.w) (yoneda.map (Spec.map φ'')) (iN (Spec.map e))
    (iN (Spec.map u)) (gN_iN _ _ _ _ _) (iN_app_zero_iso _) (iN_app_zero_iso _)
    (hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo')

end LateralTheory.E.FiltrationLevelInjectivity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafObjFPPf

def Desc (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
    FP q ∧ IsPullback v f q (toR R)

def LeafObjAff : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), IsAffine X → FP f → Desc k f

def LeafObjGlue : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
    Desc k (U.ι ≫ f) → Desc k (V.ι ≫ f) → Desc k ((U ⊓ V).ι ≫ f) → Desc k f

def LeafQCQSInduct : Prop := ∀ (S : Scheme.{0}) [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop),
    (∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f) →
    (∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f) →
    ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → P f

theorem objectDescent_of_affineDescent (hA : LeafObjAff) (hG : LeafObjGlue) (hI : LeafQCQSInduct) : LeafObjFP := by
  intro k _ Ω _ _ X f hf
  exact hI (Sp Ω) (fun g => Desc k g) (fun g hX hg => hA k Ω g hX hg)
    (fun g hg U V hUV h1 h2 h3 => hG k Ω g hg U V hUV h1 h2 h3) f hf

end LateralTheory.E.LeafObjFPPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafPairFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  simp only [toR, incl, ← Spec.map_comp]
  congr 1

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem raise {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D) (hq : FP q)
    (hs : IsPullback v c q (toR R)) :
    ∃ (E : Scheme.{0}) (q' : E ⟶ Sp R') (w : C ⟶ E), FP q' ∧ IsPullback w c q' (toR R') := by
  refine ⟨pullback q (incl h), pullback.snd _ _, pullback.lift v (c ≫ toR R') ?_, fp_snd _ _ hq, ?_⟩
  · rw [Category.assoc, toR_incl, hs.w]
  · refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, toR_incl]
    exact hs

def LeafMapFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (q1 : D1 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP q1 → IsPullback v0 c0 q (toR R) →
    IsPullback v1 (γ1 ≫ c0) q1 (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

theorem pairDescent_of_objects_morphisms (hO : LeafObjFP) (hM : LeafMapFP) : LeafPairFP := by
  intro k _ Ω _ _ R hR C0 C1 c0 γ1 h1 D0 q v0 hq hsq
  obtain ⟨R1, hR1, D1, q1, v1, hq1, hs1⟩ := hO k Ω (γ1 ≫ c0) h1
  obtain ⟨E0, q0', w0, hq0', hs0'⟩ := raise (le_sup_left : R ≤ R ⊔ R1) c0 q v0 hq hsq
  obtain ⟨E1, q1', w1, hq1', hs1'⟩ := raise (le_sup_right : R1 ≤ R ⊔ R1) (γ1 ≫ c0) q1 v1 hq1 hs1
  exact hM k Ω (R ⊔ R1) (hR.sup hR1) c0 γ1 q0' q1' w0 w1 hq0' hq1' hs0' hs1'

end LateralTheory.E.LeafPairFPPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.ReducedOfSmooth

theorem LeafReducedSmooth_of : LateralTheory.E.QuasiFiniteDescent.LeafReducedSmooth := by
  intro k _ Ω _ _ R _ D q hq
  have : Smooth q := hq.smooth
  have : _root_.IsReduced R := isReduced_of_injective R.val Subtype.val_injective
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of R)) := inferInstance
  exact GlobalTheory.isReduced_of_smooth_of_isReduced q

end LateralTheory.E.ReducedOfSmooth
end
end
