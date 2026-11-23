module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Aesop.BuiltinRules
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section NiCoh

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem ni_nat {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') {T T' : C} (φ : T ⟶ T') (x : F.obj T) :
    (β.app T').hom ((F.map φ).hom x) = (F'.map φ).hom ((β.app T).hom x) := by
  rw [← ModuleCat.comp_apply, β.naturality, ModuleCat.comp_apply]

theorem ni_pull_cls {F F' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (n : ℕ) (a : Cn F n) (ha : d F n a = 0) :
    ∃ hb, (Mor.ofNatTrans β).pull n ((cx F).cls a ha) = (cx F').cls (fun s => (β.app _).hom (a s)) hb := by
  have hb : d F' n (fun s => (β.app _).hom (a s)) = 0 :=
    ((Mor.ofNatTrans β).d_pullC n a).trans (by rw [ha, map_zero])
  exact ⟨hb, CrystallineSemistableComparison.P.mapH_cls (Mor.ofNatTrans β).hom n a ha hb⟩

theorem ni_pull_add {F F' : C ⥤ ModuleCat.{w} R} (β β' : F ⟶ F') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β + β')).pull n x = (Mor.ofNatTrans β).pull n x + (Mor.ofNatTrans β').pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β + β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n a ha
  rw [e1, e2, e3, ← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.1 _ _ h2 h3 (by rw [map_add (f := _), h2, h3, add_zero])]
  congr 1

theorem ni_pull_zero {F F' : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (0 : F ⟶ F')).pull n x = 0 := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (0 : F ⟶ F') n a ha
  rw [e1, (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1]
  have : (fun s => ((0 : F ⟶ F').app _).hom (a s)) = (0 : Cn F' n) := by
    funext s
    simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, Pi.zero_apply]
  rw [this]
  exact Submodule.zero_mem _

theorem ni_pull_sum {ι : Type} {F F' : C ⥤ ModuleCat.{w} R} (β : ι → (F ⟶ F')) (S : Finset ι) (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (∑ k ∈ S, β k)).pull n x = ∑ k ∈ S, (Mor.ofNatTrans (β k)).pull n x := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ni_pull_zero]
  | insert k S hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ni_pull_add, ih]

theorem ni_pull_comp {F F' F'' : C ⥤ ModuleCat.{w} R} (β : F ⟶ F') (β' : F' ⟶ F'') (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (β ≫ β')).pull n x = (Mor.ofNatTrans β').pull n ((Mor.ofNatTrans β).pull n x) := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (β ≫ β') n a ha
  obtain ⟨h2, e2⟩ := ni_pull_cls β n a ha
  obtain ⟨h3, e3⟩ := ni_pull_cls β' n _ h2
  rw [e1, e2, e3]
  rfl

theorem ni_pull_id {F : C ⥤ ModuleCat.{w} R} (n : ℕ) (x : H F n) :
    (Mor.ofNatTrans (𝟙 F)).pull n x = x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
  obtain ⟨h1, e1⟩ := ni_pull_cls (𝟙 F) n a ha
  rw [e1]
  rfl

def fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) : SubF F where
  S T := LinearMap.ker ((e.app T).hom - LinearMap.id)
  map_mem := fun {_ _} φ {_} hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [ni_nat, hx]

theorem mem_fixF {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (T : C) (x : F.obj T) :
    x ∈ (fixF e).S T ↔ (e.app T).hom x = x := by
  change x ∈ LinearMap.ker ((e.app T).hom - LinearMap.id) ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

def fixP {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : F ⟶ (fixF e).fn where
  app T := ModuleCat.ofHom (LinearMap.codRestrict _ (e.app T).hom fun x => by
    rw [mem_fixF, ← ModuleCat.comp_apply, ← NatTrans.comp_app, he])
  naturality T T' φ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (ni_nat e φ x))

def fixI {F : C ⥤ ModuleCat.{w} R} (S : SubF F) : S.fn ⟶ F where
  app T := ModuleCat.ofHom (S.S T).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem fixP_fixI {F : C ⥤ ModuleCat.{w} R} (e : F ⟶ F) (he : e ≫ e = e) : fixP e he ≫ fixI (fixF e) = e :=
  NatTrans.ext (funext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

def gNat {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) : G ⟶ G where
  app _ := G.map (X := SingleObj.star _) (Y := SingleObj.star _) g
  naturality X Y a := by
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    exact mul_comm (g : Gam d) (a : Gam d)

theorem gNat_pull {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (n : ℕ) (x : H G n) :
    (Mor.ofNatTrans (gNat G g)).pull n x = x := by
  have := CrystallineSemistableComparison.P.prism (Mor.ofNatTrans (gNat G g)) (Mor.id G)
    { app := fun _ => (g : SingleObj.star (Gam d) ⟶ SingleObj.star (Gam d)), naturality := fun _ _ a => mul_comm (g : Gam d) (a : Gam d) }
    (fun T x => rfl) n x
  rw [this]
  exact ((CrystallineSemistableComparison.P.pull_comp (Mor.id G) (Mor.id G) n x).2)

theorem killed_of {d : ℕ} (G : SingleObj (Gam d) ⥤ ModuleCat.{w} R) (g : Gam d) (s : R)
    (hu : ∀ T, UpTo s ((gNat G g - 𝟙 G).app T).hom) (n : ℕ) (z : H G n) : s ^ 2 • z = 0 := by
  obtain ⟨x, hx⟩ := (CrystallineSemistableComparison.P.coef_upTo _ s hu n).2 z
  rw [← hx]
  have e1 := ni_pull_add (gNat G g - 𝟙 G) (𝟙 G) n x
  rw [sub_add_cancel, gNat_pull, ni_pull_id] at e1
  calc _ = ((Mor.ofNatTrans (gNat G g - 𝟙 G)).pull n x + x) - x := (add_sub_cancel_right _ _).symm
    _ = x - x := by rw [← e1]
    _ = 0 := sub_self x

theorem ni_killed {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N) (h : NI s α) (k : Fin d)
    (n : ℕ) (z : H (fixF (h.π k)).fn n) : s ^ 2 • z = 0 := by
  refine killed_of _ (gen k) s (fun T => ?_) n z
  change UpTo s ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom
  have hδ : ∀ y : (fixF (h.π k)).fn.obj (SingleObj.star _), ((gNat (fixF (h.π k)).fn (gen k) - 𝟙 _).app (SingleObj.star _)).hom y =
      ((fixF (h.π k)).fn.map (X := SingleObj.star _) (Y := SingleObj.star _) (gen k)).hom y - y := fun y => rfl
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · rw [hδ, sub_eq_zero] at hy
    have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    exact Subtype.ext (h.inj k y.1 h1 (congrArg Subtype.val hy))
  · have h1 : ((h.π k).app _).hom y.1 = y.1 := (mem_fixF (h.π k) _ y.1).1 y.2
    obtain ⟨x, hx, hx2⟩ := h.surj k y.1 h1
    exact ⟨⟨x, (mem_fixF (h.π k) _ x).2 hx⟩, by rw [hδ]; exact Subtype.ext hx2⟩

end NiCoh

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ni_coh : ∀ {R : Type} [CommRing R] {d : ℕ} (s : R) {M N : SingleObj (Gam d) ⥤ ModuleCat.{w} R} (α : M ⟶ N), NI s α → ∀ n, IsoLe (s ^ 2) n (Mor.ofNatTrans α) := by
  intro R _ d s M N α h n j _
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have e := ni_pull_comp α h.ρ j x
    rw [h.αρ, ni_pull_id, hx, map_zero] at e
    rw [e, smul_zero]
  · refine ⟨(Mor.ofNatTrans h.ρ).pull j (s ^ 2 • y), ?_⟩
    rw [← ni_pull_comp]
    have e := ni_pull_add (h.ρ ≫ α) (∑ k, h.π k) j (s ^ 2 • y)
    rw [h.sum, ni_pull_id, ni_pull_sum] at e
    have hk : ∀ k, (Mor.ofNatTrans (h.π k)).pull j (s ^ 2 • y) = 0 := by
      intro k
      rw [← fixP_fixI (h.π k) (h.idem k), ni_pull_comp, map_smul, ni_killed s α h k, map_zero]
    rw [Finset.sum_eq_zero (fun k _ => hk k), add_zero] at e
    exact e.symm
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

lemma rc_pull_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w} R}
    {F'' : C'' ⥤ ModuleCat.{w} R} (m : Mor F F' (RingHom.id R)) (m' : Mor F' F'' (RingHom.id R)) (n : ℕ) :
    (m.comp m' : Mor F F'' (RingHom.id R)).pull n = (m'.pull n).comp (m.pull n) :=
  LinearMap.ext fun x => (CrystallineSemistableComparison.P.pull_comp m m' n x).1

lemma rc_restrict_comp {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (n : ℕ) :
    (Mor.restrict F (G' ⋙ G)).pull n = ((Mor.restrict (G ⋙ F) G').pull n).comp ((Mor.restrict F G).pull n) :=
  rc_pull_comp (Mor.restrict F G) (Mor.restrict (G ⋙ F) G') n

lemma rc_iso_upTo {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F₁ : C ⥤ ModuleCat.{w} R}
    (e : F ≅ F₁) (n : ℕ) : UpTo (1 : R) ((Mor.ofNatTrans e.hom).pull n) := by
  have h := CrystallineSemistableComparison.P.coef_upTo e.hom (1 : R) (fun T => by
    refine ((CrystallineSemistableComparison.P.upTo_alg (e.hom.app T).hom LinearMap.id 1 1).2.2.2.2).2 ?_
    exact (e.app T).toLinearEquiv.bijective) n
  rwa [one_pow] at h

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.ri_calc : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C''] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (s s' : R) (n : ℕ), (RI s n F G → RI s' n (G ⋙ F) G' → RI (s * s') n F (G' ⋙ G)) ∧ (RI s n F G → RI s' n F (G' ⋙ G) → RI (s * s') n (G ⋙ F) G') ∧ (RI s n (G ⋙ F) G' → RI s' n F (G' ⋙ G) → RI (s * s') n F G) ∧ (RI s n F G → RI (s * s') n F G) ∧ (∀ G₁ : C' ⥤ C, (G ≅ G₁) → RI s n F G → RI s n F G₁) ∧ (G.IsEquivalence → RI 1 n F G) ∧ (∀ F₁ : C ⥤ ModuleCat.{w} R, (F ≅ F₁) → RI s n F G → RI s n F₁ G) := by
  intro R _ C _ C' _ C'' _ F G G' s s' n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 j hj
    rw [RI, IsoLe] at *
    rw [rc_restrict_comp]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').1 (h1 j hj) (h2 j hj)
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.1 (h1 j hj) this
  · intro h1 h2 j hj
    have := h2 j hj
    rw [rc_restrict_comp] at this
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s s').2.2.1 (h1 j hj) this
  · intro h1 j hj
    exact (CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id s s').2.2.2.1 (h1 j hj)
  · intro G₁ e h1 j hj
    have hp : (Mor.restrict F G₁).pull j =
        ((Mor.ofNatTrans (Functor.whiskerRight e.hom F)).pull j).comp ((Mor.restrict F G).pull j) := by
      rw [← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F G₁)
        ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerRight e.hom F))) e.inv ?_ j x
      intro T x
      change (F.map (e.hom.app T)).hom ((F.map (e.inv.app T)).hom x) = x
      rw [← ModuleCat.comp_apply, ← F.map_comp, e.inv_hom_id_app, F.map_id]
      rfl
    rw [hp, ← mul_one s]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ s 1).1 (h1 j hj) (rc_iso_upTo (Functor.isoWhiskerRight e F) j)
  · intro hG j hj
    exact ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F G).pull j) LinearMap.id 1 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj F G G.asEquivalence.inverse G.asEquivalence.toAdjunction j)
  · intro F₁ e h1 j hj
    have hp : (Mor.restrict F₁ G).pull j =
        ((Mor.ofNatTrans (Functor.whiskerLeft G e.hom)).pull j).comp
          (((Mor.restrict F G).pull j).comp ((Mor.ofNatTrans e.inv).pull j)) := by
      rw [← rc_pull_comp, ← rc_pull_comp]
      refine LinearMap.ext fun x => CrystallineSemistableComparison.P.prism (Mor.restrict F₁ G)
        ((Mor.ofNatTrans e.inv).comp ((Mor.restrict F G).comp (Mor.ofNatTrans (Functor.whiskerLeft G e.hom))))
        (𝟙 G) ?_ j x
      intro T x
      change (e.hom.app (G.obj T)).hom ((e.inv.app (G.obj T)).hom ((F₁.map (𝟙 (G.obj T))).hom x)) = x
      rw [F₁.map_id, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e.inv_hom_id_app]
      rfl
    rw [hp, ← one_mul s, ← mul_one (1 * s)]
    exact (CrystallineSemistableComparison.P.upTo_alg _ _ (1 * s) 1).1
      ((CrystallineSemistableComparison.P.upTo_alg _ _ 1 s).1 (rc_iso_upTo e.symm j) (h1 j hj))
      (rc_iso_upTo (Functor.isoWhiskerLeft G e) j)
end
