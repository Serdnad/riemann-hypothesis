module

public import Development.EtaleCohomology.EtaleSheaves.Bundle017
public import Development.EtaleCohomology.EtaleSheaves.Bundle005
import Development.EtaleCohomology.EtaleSheaves.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle011
public import Development.EtaleCohomology.WeilConjectures.Bundle004
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Development.EtaleCohomology.EtaleSheaves.Bundle018
public import Development.EtaleCohomology.EtaleSheaves.Bundle021
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCoprodPf

section General
variable {C : Type*} [Category C] [Preadditive C]

theorem sum_comp_split {K L : CochainComplex C ℤ} {n : ℤ} {ι : Type} {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (α : Cochain K L n) (s : Finset ι) :
    ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α (zero_add n)) (zero_add n) =
      (Cochain.ofHom (∑ j ∈ s, p j ≫ i j)).comp α (zero_add n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Cochain.ofHom_add, Cochain.add_comp,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem cls_inj {K L : CochainComplex C ℤ} {ι : Type} [Fintype ι] {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (hsum : ∑ j, p j ≫ i j = 𝟙 K) (n : ℤ)
    (x : CohomologyClass K L n) (hx : ∀ j, cpre (Cocycle.ofHom (i j)) L n n (zero_add n) x = 0) : x = 0 := by
  classical
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h : ∀ j, ∃ β : Cochain (Kj j) L (n - 1),
      δ (n - 1) n β = (Cochain.ofHom (i j)).comp α.1 (zero_add n) := by
    intro j
    have := hx j
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at this
    obtain ⟨m, hm, β, hβ⟩ := this
    obtain rfl : m = n - 1 := by omega
    exact ⟨β, by rw [hβ]; rfl⟩
  choose β hβ using h
  have hδ : ∀ s : Finset ι, δ (n - 1) n (∑ j ∈ s, (Cochain.ofHom (p j)).comp (β j) (zero_add _)) =
      ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α.1 (zero_add n)) (zero_add n) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, δ_add, ih, δ_ofHom_comp, hβ]
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, ∑ j, (Cochain.ofHom (p j)).comp (β j) (zero_add _), ?_⟩
  rw [hδ, sum_comp_split, hsum, Cochain.id_comp]

end General

section Sheaves
variable (R : Type) [CommRing R]

abbrev W : Spc ⥤ SimplicialObject (Shv R) := (SimplicialObject.whiskering _ _).obj (free R)

abbrev G : SimplicialObject (Shv R) ⥤ Cx R :=
  AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ ComplexShape.embeddingDownNat.extendFunctor (Shv R)

variable {m : ℕ} (Z : Fin m → Scheme.{0})

def gen (j : Fin m) : Sec ((free R).obj (yoneda.obj (Z j))) (∐ Z) :=
  ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose

theorem gen_res (j t : Fin m) : Sec.res (Sigma.ι Z t) (gen R Z j) =
    Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))) t :=
  congrFun ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose_spec t

def pr (j : Fin m) : (free R).obj (yoneda.obj (∐ Z)) ⟶ (free R).obj (yoneda.obj (Z j)) :=
  LateralTheory.E.L_sch_clsPfYon.yon R _ _ (gen R Z j)

theorem sec_comp {F F' F'' : Shv R} (φ : F ⟶ F') (ψ : F' ⟶ F'') {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sum_pr : ∑ j, pr R Z j ≫ (free R).map (yoneda.map (Sigma.ι Z j)) = 𝟙 _ := by
  classical
  apply LateralTheory.E.L_sch_clsPfYon.yon_ext
  apply (LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (∐ Z))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).1
  funext t
  change Sec.res (Sigma.ι Z t) _ = Sec.res (Sigma.ι Z t) _
  rw [LateralTheory.E.LeafKumSpecPf.sec_res_map, LateralTheory.E.LeafKumSpecPf.sec_res_map]
  erw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
  have hy : (ConcreteCategory.hom ((yoneda.obj (∐ Z)).map (Sigma.ι Z t).op)) (𝟙 (∐ Z)) = Sigma.ι Z t := by
    rfl
  rw [hy, LateralTheory.EtaleFoundations.EvDeltaPf.sec_sum, Finset.sum_eq_single t]
  · rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_same,
      LateralTheory.EtaleFoundations.EvDeltaPf.freeGen_map]
    rfl
  · intro b _ hb
    rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_of_ne (Ne.symm hb)]
    exact map_zero _
  · simp

def prS (j : Fin m) : (W R).obj (sch.obj (∐ Z)) ⟶ (W R).obj (sch.obj (Z j)) where
  app _ := pr R Z j
  naturality a b θ := by
    change (free R).map (𝟙 _) ≫ pr R Z j = pr R Z j ≫ (free R).map (𝟙 _)
    simp

theorem sum_prS : ∑ j, prS R Z j ≫ (W R).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
  refine NatTrans.ext (funext fun a => ?_)
  rw [NatTrans.app_sum]
  exact sum_pr R Z

end Sheaves

theorem LeafCoprod_of : LateralTheory.E.E4.LeafCoprod := by
  intro _ q n i m Z hZ
  have : ∀ j, Finite (Ht q (sch.obj (Z j)) n i) := hZ
  refine Finite.of_injective (AddMonoidHom.pi fun j => pull (ZMod q) (sch.map (Sigma.ι Z j)) (tw q i) n) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hsum : ∑ j, (G (ZMod q)).map (prS (ZMod q) Z j) ≫ (chains (ZMod q)).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
    have h1 : (G (ZMod q)).map (∑ j, prS (ZMod q) Z j ≫ (W (ZMod q)).map (sch.map (Sigma.ι Z j))) = 𝟙 _ := by
      rw [sum_prS, CategoryTheory.Functor.map_id]

    rw [Functor.map_sum] at h1
    simp only [Functor.map_comp] at h1
    exact h1
  exact cls_inj (fun j => (chains (ZMod q)).map (sch.map (Sigma.ι Z j))) (fun j => (G (ZMod q)).map (prS (ZMod q) Z j))
    hsum n x (fun j => congrFun hx j)

end LateralTheory.E.LeafCoprodPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafFiltPf

abbrev Sg {R : Type} [CommRing R] (X : Shv R) : Cx R := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj X

variable {R : Type} [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ)

theorem coe_sub' {K L : Cx R} {m : ℤ} (a b : Cocycle K L m) :
    ((a - b : Cocycle K L m) : Cochain K L m) = (a : Cochain K L m) - (b : Cochain K L m) := rfl

theorem coe_zero' {K L : Cx R} {m : ℤ} : ((0 : Cocycle K L m) : Cochain K L m) = 0 := rfl

theorem res_zero (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) := by
  have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by omega)

def V (s : ℤ) (z : Cocycle K (res R F) n) : Prop := ∀ p q (h : p + n = q), s < p → z.1.v p q h = 0

def S (s : ℤ) : Set (HK R K F n) := {x | ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z}

theorem memS {s : ℤ} {x : HK R K F n} (h : x ∈ S K F n s) :
    ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z := h

theorem cocyc (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    z.1.v s d hd ≫ (res R F).d d (d + 1) = 0 := by
  have h0 := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) s (d + 1) (by omega)
  rw [δ_v n (n + 1) rfl _ s (d + 1) _ d (s + 1) (by omega) rfl, hz (s + 1) (d + 1) (by omega) (by omega)] at h0
  simpa using h0

def clsC (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    Cocycle (Sg (K.X s)) (res R F) d :=
  Cocycle.fromSingleMk (z.1.v s d hd) (zero_add d) (d + 1) rfl (cocyc K F n s d hd z hz)

theorem clsC_v (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    (clsC K F n s d hd z hz).1.v 0 d (zero_add d) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd :=
  Cochain.fromSingleMk_v _ _

theorem CB (X : Shv R) (d : ℤ) (c : Cocycle (Sg X) (res R F) d) (hc : CohomologyClass.mk c = 0) (e : ℤ)
    (he : e + 1 = d) : ∃ β : Cochain (Sg X) (res R F) e,
      β.v 0 e (zero_add e) ≫ (res R F).d e d = c.1.v 0 d (zero_add d) := by
  obtain ⟨m, hm, β, hβ⟩ := (CohomologyClass.mk_eq_zero_iff c).1 hc
  obtain rfl : e = m := by omega
  refine ⟨β, ?_⟩
  have := Cochain.congr_v hβ 0 d (zero_add d)
  rw [δ_v e d hm β 0 d _ e 1 (by omega) rfl] at this
  have hz1 : IsZero ((Sg X).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
  rw [hz1.eq_of_tgt ((Sg X).d 0 1) 0] at this
  simpa using this

theorem KL (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) (e : ℤ) (he : e + 1 = d)
    (β : Cochain (Sg (K.X s)) (res R F) e)
    (hβ : β.v 0 e (zero_add e) ≫ (res R F).d e d =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd) :
    ∃ w : Cocycle K (res R F) n, CohomologyClass.mk w = CohomologyClass.mk z ∧ V K F n (s - 1) w := by
  let g : K.X s ⟶ (res R F).X e :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).inv ≫ β.v 0 e (zero_add e)
  let hh : Cochain K (res R F) (n - 1) := Cochain.single g (n - 1)
  let D : Cocycle K (res R F) n := Cocycle.mk (δ (n - 1) n hh) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - D, ?_, ?_⟩
  · have hD : CohomologyClass.mk D = 0 := (CohomologyClass.mk_eq_zero_iff D).2 ⟨n - 1, by omega, hh, rfl⟩
    rw [CohomologyClass.mk_sub, hD, sub_zero]
  · intro p q hpq hp
    have hDv : D.1.v p q hpq = (δ (n - 1) n hh).v p q hpq := rfl
    simp only [coe_sub', Cochain.sub_v, hDv]
    rw [δ_v (n - 1) n (by omega) hh p q hpq (q - 1) (p + 1) rfl rfl]
    rcases lt_or_eq_of_le (show s ≤ p by omega) with h | h
    · rw [hz p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = d := by omega
      obtain rfl : e = q - 1 := by omega
      rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp only [g, Category.assoc, hβ, Iso.inv_hom_id_assoc, comp_zero, smul_zero, add_zero, sub_self]

theorem step (s d : ℤ) (hd : s + n = d) [Finite (HK R (Sg (K.X s)) F d)] (hS : (S K F n (s - 1)).Finite) :
    (S K F n s).Finite := by
  classical
  let φ : HK R K F n → HK R (Sg (K.X s)) F d := fun x =>
    if h : x ∈ S K F n s then CohomologyClass.mk (clsC K F n s d hd (memS K F n h).choose (memS K F n h).choose_spec.2) else 0
  have key : ∀ x ∈ S K F n s, ∀ x' ∈ S K F n s, φ x = φ x' → x - x' ∈ S K F n (s - 1) := by
    intro x hx x' hx' he
    simp only [φ, dif_pos hx, dif_pos hx'] at he
    have hz := (memS K F n hx).choose_spec
    have hz' := (memS K F n hx').choose_spec
    have h0 : CohomologyClass.mk (clsC K F n s d hd (memS K F n hx).choose hz.2 -
        clsC K F n s d hd (memS K F n hx').choose hz'.2) = 0 := by
      rw [CohomologyClass.mk_sub, he, sub_self]
    obtain ⟨β, hβ⟩ := CB F (K.X s) d _ h0 (d - 1) (by omega)
    have hV : V K F n s ((memS K F n hx).choose - (memS K F n hx').choose) := by
      intro p q h hp
      simp [Cochain.sub_v, hz.2 p q h hp, hz'.2 p q h hp]
    obtain ⟨w, hw, hwV⟩ := KL K F n s d hd _ hV (d - 1) (by omega) β (by
      rw [hβ]
      simp only [coe_sub', Cochain.sub_v, clsC_v, Preadditive.comp_sub])
    exact ⟨w, by rw [hw, CohomologyClass.mk_sub, hz.1, hz'.1], hwV⟩
  let g : HK R (Sg (K.X s)) F d → HK R K F n := fun t =>
    if h : ∃ x ∈ S K F n s, φ x = t then h.choose else 0
  refine ((Set.finite_univ.prod hS).image (fun p => g p.1 + p.2)).subset ?_
  intro x hx
  have h : ∃ y ∈ S K F n s, φ y = φ x := ⟨x, hx, rfl⟩
  refine ⟨(φ x, x - g (φ x)), ⟨trivial, ?_⟩, ?_⟩
  · have hg : g (φ x) = h.choose := by simp only [g, dif_pos h]
    rw [hg]
    exact key x hx _ h.choose_spec.1 h.choose_spec.2.symm
  · simp

theorem base (s : ℤ) (hs : s + n < 0) : S K F n s ⊆ {0} := by
  rintro x ⟨z, rfl, hz⟩
  have : z = 0 := by
    refine Cocycle.ext (Cochain.ext _ _ (fun p q hpq => ?_))
    rw [coe_zero', Cochain.zero_v]
    rcases lt_or_ge s p with h | h
    · exact hz p q hpq h
    · exact (res_zero F q (by omega)).eq_of_tgt (z.1.v p q hpq) 0
  simp [this]

theorem LeafFilt_of : LateralTheory.E.LeafSSCut.LeafFilt := by
  intro _ R _ K _ F n hfin
  have ind : ∀ k : ℕ, ∀ r : ℕ, 1 ≤ r → n < r + k → (S K F n (-(r : ℤ))).Finite := by
    intro k
    induction k with
    | zero => intro r _ hr; exact (Set.finite_singleton 0).subset (base K F n _ (by push_cast at hr; omega))
    | succ k ih =>
      intro r hr1 hr
      by_cases hk : n < r + k
      · exact ih r hr1 hk
      · have : Finite (HK R (Sg (K.X (-(r : ℤ)))) F (n - r)) := hfin r (by omega) (by push_cast at hr; omega)
        have h2 := ih (r + 1) (by omega) (by push_cast at hr ⊢; omega)
        have e : (-((r + 1 : ℕ) : ℤ)) = -(r : ℤ) - 1 := by push_cast; ring
        rw [e] at h2
        exact step K F n (-(r : ℤ)) (n - r) (by omega) h2
  have hS := ind n.toNat 1 le_rfl (by omega)
  have e : (-((1 : ℕ) : ℤ)) = (0 : ℤ) - 1 := by norm_num
  rw [e] at hS
  have hsub : ((HK.pull R (LateralTheory.E.LeafSSCut.incl0 K) F n).ker : Set (HK R K F n)) ⊆ S K F n (0 - 1) := by
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    have hz : V K F n 0 z := fun p q hpq hp =>
      (CochainComplex.isZero_of_isStrictlyLE K 0 p hp).eq_of_src _ _
    have hc : CohomologyClass.mk (zcomp (Cocycle.ofHom (LateralTheory.E.LeafSSCut.incl0 K)) z (zero_add n)) = 0 := hx
    obtain ⟨β, hβ⟩ := CB F (K.X 0) n _ hc (n - 1) (by omega)
    obtain ⟨w, hw, hwV⟩ := KL K F n 0 n (zero_add n) z hz (n - 1) (by omega) β (by
      rw [hβ]
      change ((Cochain.ofHom (LateralTheory.E.LeafSSCut.incl0 K)).comp z.1 (zero_add n)).v 0 n (zero_add n) = _
      rw [Cochain.comp_v _ _ (zero_add n) 0 0 n (by omega) (by omega), Cochain.ofHom_v]
      simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f])
    exact ⟨w, hw, hwV⟩
  exact (hS.subset hsub).to_subtype

end LateralTheory.E.LeafFiltPf
end
end

section

namespace LateralTheory.E.E4

theorem mem_range_of_isIntegral {k B : Type} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] {x : B} (hx : IsIntegral k x) : x ∈ Set.range (algebraMap k B) := by
  have h : (minpoly k x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx)
  have hm : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic hx
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul, map_add (f := _),
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hm
  exact ⟨-(minpoly k x).coeff 0, by rw [map_neg]; exact hm.symm⟩

theorem fg_subgroup_mult (n : ℕ) (H : Subgroup (Multiplicative (Fin n → ℤ))) : Group.FG H := by
  have : IsNoetherian ℤ (Additive (Multiplicative (Fin n → ℤ))) :=
    isNoetherian_of_linearEquiv (AddEquiv.additiveMultiplicative (Fin n → ℤ)).symm.toIntLinearEquiv
  rw [Group.fg_iff_subgroup_fg, Subgroup.fg_iff_add_fg]
  have := IsNoetherian.noetherian (R := ℤ) H.toAddSubgroup.toIntSubmodule
  exact (Submodule.fg_iff_addSubgroup_fg _).1 this

def LeafUnitsOrd : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B],
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsFG_of (h : LeafUnitsOrd) : LeafUnitsFG := by
  intro k B _ _ _ _ _ _
  obtain ⟨n, φ, hφ⟩ := h k B
  have hker : φ.ker ≤ (Units.map (algebraMap k B).toMonoidHom).range := by
    intro u hu
    obtain ⟨a, ha⟩ := mem_range_of_isIntegral (hφ u hu)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact u.ne_zero ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩
  have : Group.FG φ.range := fg_subgroup_mult n _
  have : Group.FG (Bˣ ⧸ φ.ker) :=
    Group.fg_of_surjective (f := ((QuotientGroup.quotientKerEquivRange φ).symm : φ.range →* Bˣ ⧸ φ.ker))
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map φ.ker (Units.map (algebraMap k B).toMonoidHom).range (MonoidHom.id _) hker) ?_
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk u, rfl⟩

def LeafUnitsOrdCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem isIntegral_of_isField {k B : Type} [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (hB : IsField B) (x : B) : IsIntegral k x := by
  let _ := hB.toField
  have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  exact Algebra.IsIntegral.isIntegral x

theorem LeafUnitsOrd_of (h : LeafUnitsOrdCurve) : LeafUnitsOrd := by
  intro k B _ _ _ _ _ _
  by_cases hB : IsField B
  · exact ⟨0, 1, fun u _ => isIntegral_of_isField hB _⟩
  · exact h k B hB

theorem LeafUnitsFG_of_curve (h : LeafUnitsOrdCurve) : LeafUnitsFG := LeafUnitsFG_of (LeafUnitsOrd_of h)

def LeafNoetherCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ g : Polynomial k →ₐ[k] B, Function.Injective g ∧ g.Finite

def LeafOrdAtInfinity : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsOrdCurve_of (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsOrdCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨g, hg, hf⟩ := hN k B hB
  exact hV k B g hg hf

theorem LeafUnitsFG_of_leaves (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_curve (LeafUnitsOrdCurve_of hN hV)

end LateralTheory.E.E4
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostRelCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

def LeafTrunc : Prop := ∀ (A : Type 2) [Category.{1} A] [Abelian A] [HasDerivedCategory.{2} A]
  (K0 K1 K2 L : DerivedCategory A) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2),
  (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) →
  (DerivedCategory.homologyFunctor A 2).map f = 0 → (DerivedCategory.homologyFunctor A 1).map g = 0 →
  (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) →
  (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) →
  IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) →
  ∃ h : K0 ⟶ L, h ≫ ℓ = f ≫ g

def LeafRep : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∃ (A : Type 2) (_ : Category.{1} A) (_ : Abelian A) (_ : HasDerivedCategory.{2} A) (O K0 K1 K2 L : DerivedCategory A)
    (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj L)),
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) ∧
    (DerivedCategory.homologyFunctor A 2).map f = 0 ∧ (DerivedCategory.homologyFunctor A 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map ℓ)

theorem goal_of (hT : LeafTrunc) (hR : LeafRep) : LeafGhostRel := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n y
  obtain ⟨A, _, _, _, O, K0, K1, K2, L, f, g, ℓ, e0, e2, eL, hK0, hf, hg, hK2, hL, hℓ, hinj, hsurj, n0, nL⟩ :=
    hR hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨h, hh⟩ := hT A K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  obtain ⟨c, hc⟩ := hsurj n (e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map h)
  refine ⟨c, hinj n ?_⟩
  rw [n0, nL, hc, Category.assoc, ← Functor.map_comp, hh]

end LateralTheory.E.LeafGhostRelCut

end
end

section

open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IECobPf

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem IECob_of : LateralTheory.E.ULAStalkPf.IECob := by
  intro A B C D f g u v sq hf
  have := et_cobase
  have hI : IE.IsStableUnderCobaseChange := by
    unfold IE; infer_instance
  exact hI.of_isPushout sq.flip hf

end LateralTheory.E.IECobPf
end
