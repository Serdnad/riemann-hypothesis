module

public import Development.EtaleCohomology.EtaleSheaves.Bundle006
public import Development.EtaleCohomology.EtaleSheaves.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.EtaleSheaves.Bundle008
public import Development.EtaleCohomology.TateTwists.Bundle004
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassRootLocalization

open LateralTheory.E.CupProductRingLaws LateralTheory.E.ChernCocycleExistenceAndUniqueness

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  have hF := ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => hab V g hg)

variable {R : Type} [CommRing R] in
theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res g (freeGen R P U x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (show uliftFunctor.{1, 0}.obj (P.obj (op U)) from ULift.up x))
  refine Eq.trans ?_ key
  unfold freeGen
  congr 1
  simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]
  erw [ModuleCat.free_map_apply]
  rfl

variable {R : Type} [CommRing R] in
theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : ev α p s h V (x.res g) = Sec.res g (ev α p s h U x) := by
  unfold ev Sx.res
  rw [freeGen_res]
  exact NatTrans.naturality_apply (((chainsXIso R E p).inv ≫ α.v _ _ h).hom) g.op _

def LeafRootLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem evUnique_of (hr : LeafRootLoc) : EtaleKummerChernCocycleEvaluationsUnique := by
  intro q _ E L hq γ γ' h h'
  constructor
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U x) fun V g hv => ?_
    obtain ⟨v, hv⟩ := hv
    rw [← ev_res, ← ev_res, h.2.1 V _ v hv, h'.2.1 V _ v hv]
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 0 1 (by omega)))
      (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 1 1 (by omega)))) fun V g hv => ?_
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hv
    rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
    rw [← ev_res, ← ev_res, h.2.2 V _ v w hv hw, h'.2.2 V _ v w hv hw]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hr : LeafRootLoc) : EtaleFirstChernClassRepresentedByChernCocycle :=
  LateralTheory.E.ChernCocycleExistenceAndUniqueness.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique hE (evUnique_of hr)

end LateralTheory.E.ChernClassRootLocalization
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairHtpyPf

def LeafTwTensExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTensFactor : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
  ∀ ν : Pair I J K, ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T),
  τ.IsTensor → IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResHtpy : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∀ u u' : T ⟶ res _ (tw q k), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem secMap_id_f {R : Type} [CommRing R] (I : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (I.X s) U) :
    Sec.map ((𝟙 I : I ⟶ I).f s) x = x := by
  rw [HomologicalComplex.id_f]; rfl

theorem secMap_addx {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem secMap_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem hom_reindex {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (Hh : ∀ i j, T.X i ⟶ K.X j)
    (U : Scheme.{0}) (s t v n : ℤ) (hv : v + 1 = n) (hs : s + t = n) (hs' : s + t = v + 1)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (Hh (v + 1) v) (τ.mul U s t (v + 1) hs' a b) = Sec.map (Hh n v) (τ.mul U s t n hs a b) := by
  subst hv; rfl

theorem pairHtpy_of_homotopy {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (μ μ' : Pair I J K) (u u' : T ⟶ K)
    (hu : τ.Compat μ (𝟙 I) (𝟙 J) u) (hu' : τ.Compat μ' (𝟙 I) (𝟙 J) u') (H : Homotopy u u') :
    LateralTheory.E.LeafTwPairUniquePf.PairHtpy μ μ' := by
  refine ⟨fun U s t w hw => (τ.mul U s t (w + 1) hw).compr₂ (((H.hom (w + 1) w).hom.app (op U)).hom), ?_, ?_⟩
  · intro V U g s t w hw a b
    simp only [LinearMap.compr₂_apply]
    rw [← τ.nat g s t (w + 1) hw a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (τ.mul _ s t (w + 1) hw a b)) ((H.hom (w + 1) w).hom.naturality g.op)).symm
  · intro U s t w hw a b
    simp only [LinearMap.compr₂_apply]
    have e1 := hu U s t w hw a b
    have e2 := hu' U s t w hw a b
    rw [secMap_id_f, secMap_id_f] at e1 e2
    rw [← e1, ← e2]
    have hc := H.comm w
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel w (w + 1) by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (w - 1) w by simp)] at hc
    rw [hc, secMap_add, secMap_add, secMap_comp, secMap_comp]
    have e3 := hom_reindex τ H.hom U s t (w - 1) w (by omega) hw (by omega) a b
    have e3' : (ModuleCat.Hom.hom ((H.hom (w - 1 + 1) (w - 1)).hom.app (op U))) (τ.mul U s t (w - 1 + 1) (by omega) a b) =
        Sec.map (H.hom w (w - 1)) (τ.mul U s t w hw a b) := e3
    rw [e3']
    rw [τ.leibniz, secMap_addx, secMap_usmul]
    dsimp only [Sec.map]
    abel

end LateralTheory.E.LeafTwPairHtpyPf

open LateralTheory.E.LeafTwPairHtpyPf in
theorem LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of (hE : LeafTwTensExists) (hF : LeafTensFactor) (hR : LeafTwTensRes)
    (hH : LeafTwResHtpy) : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := by
  intro q _ i j μ μ' hμ hμ'
  obtain ⟨T, τ, hτ⟩ := hE q i j
  obtain ⟨u, hu⟩ := hF (ZMod q) τ hτ μ
  obtain ⟨u', hu'⟩ := hF (ZMod q) τ hτ μ'
  obtain ⟨H⟩ := hH q (i + j) _ (hR q i j τ hτ) u u' (fun U ζ => by
    have a1 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    have a2 := hu' U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [secMap_id_f, secMap_id_f] at a1 a2
    rw [a1, a2, hμ U ζ, hμ' U ζ])
  exact pairHtpy_of_homotopy τ μ μ' u u' hu hu' H
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTwTensExPf

open Classical in
section
variable {R : Type} [CommRing R] (I J : Cx R)

theorem tres_tmul {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res]

def TP (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have := tres_tmul I J (𝟙 U.unop) w p a b
        simp only [DirectSum.lof_eq_of] at this
        simp [this, Sec.res]
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have h1 := tres_tmul I J (g.unop ≫ f.unop) w p a b
        have h2 := tres_tmul I J f.unop w p a b
        have h3 := tres_tmul I J g.unop w p (Sec.res f.unop a) (Sec.res f.unop b)
        simp only [DirectSum.lof_eq_of] at h1 h2 h3
        simp [h1, h2, Sec.res]
        exact h3.symm
end
end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

abbrev lo {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p

def dT (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    lo I J (U := U) (w := w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
    ((p.1.1.negOnePow : ℤˣ) : ℤ) • (lo I J (U := U) (w := w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

theorem dT_tmul (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      lo I J ⟨(s + 1, t), by simp only; omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
      ((s.negOnePow : ℤˣ) : ℤ) • lo I J ⟨(s, t + 1), by simp only; omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b) := by
  simp [dT, lo, DirectSum.toModule_lof]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

theorem dd0 {K : Cx R} {U : Scheme.{0}} (s : ℤ) (a : Sec (K.X s) U) :
    Sec.map (K.d (s + 1) (s + 1 + 1)) (Sec.map (K.d s (s + 1)) a) = 0 := by
  rw [LateralTheory.E.LeafTwPairExistsPf.map_map, HomologicalComplex.d_comp_d]
  simp [Sec.map]

theorem dT_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  erw [tres_tmul, dT_tmul, dT_tmul, map_add, map_zsmul, tres_tmul, tres_tmul,
    LateralTheory.E.LeafTwPairExistsPf.res_map, LateralTheory.E.LeafTwPairExistsPf.res_map]

theorem dT_dT (U : Scheme.{0}) (w : ℤ) : dT I J U (w + 1) ∘ₗ dT I J U w = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_tmul, map_add (f := _), map_zsmul]
  rw [dT_tmul (s := s + 1) (t := t) (w := w + 1)]
  rw [dT_tmul (s := s) (t := t + 1) (w := w + 1)]
  rw [dd0 (K := I), dd0 (K := J)]
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, smul_zero, add_zero,
    Int.negOnePow_succ, Units.val_neg, neg_smul, neg_add_cancel]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def dTP (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (dT_nat I J g.unop w)

def PC : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (TP I J) (dTP I J) (fun w => by
    ext U : 2
    exact ModuleCat.hom_ext (dT_dT I J U.unop w))

def TC : Cx R := ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).obj (PC I J)

abbrev un (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((TC I J).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).app (op U)).hom

theorem un_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (un I J U w x) = un I J V w (Tens.res g w x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).naturality g.op)) x).symm

theorem un_d (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((TC I J).d w (w + 1)) (un I J U w x) = un I J U (w + 1) (dT I J U w x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (congrArg (fun f => f.app (op U)) (toSheafify_naturality Scheme.etaleTopology.{0} (dTP I J w)))) x
  simp only [TC, PC, Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d] at this ⊢
  exact this.symm

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def tau : Pair I J (TC I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (un I J U w ∘ₗ lo I J ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_nat]
    congr 1
    exact tres_tmul I J g w ⟨(s, t), h⟩ a b
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_d, dT_tmul, map_add (f := _), map_zsmul, Units.smul_def]

theorem tau_lift (U : Scheme.{0}) (w : ℤ) : (tau I J).lift U w = un I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp [Pair.lift, tau]

theorem tau_isTensor : (tau I J).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (U := op U) y, fun V g ⟨t, ht⟩ => ⟨t, ?_⟩⟩
    rw [tau_lift]
    exact ht
  · rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (X := op U) x 0 (by rw [map_zero]; exact hx), fun V g hg => ?_⟩
    have : Tens.res g w x = Tens.res g w 0 := hg
    rwa [map_zero] at this

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf

theorem LeafTwTensEx_of : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensEx := by
  intro q _ i j
  exact ⟨_, tau _ _, tau_isTensor _ _⟩

end LateralTheory.E.LeafTwTensExPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneExistsPf

open LateralTheory.E.CupProductRingLaws

def LeafUnitSec : Prop := ∀ (q : ℕ) [NeZero q], ∃ one : ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Sec (tw q 0) U,
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : IsUnit (q : Γ(U, ⊤))) (hV : IsUnit (q : Γ(V, ⊤))),
    Sec.res g (one U hU) = one V hV) ∧
  ∀ (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (ζ : Prim q Γ(U, ⊤)), one U hU = twGen 0 ζ

def LeafCocycleOfSec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U),
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) →
  ∃ α : Cocycle ((chains R).obj E) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α.1 0 0 (by simp) U x = Sec.map (resι R F) (s U ⟨x⟩)

theorem LeafOneExists_of (hU : LeafUnitSec) (hC : LeafCocycleOfSec) : LateralTheory.E.LeafOneSpecPf.LeafOneExists := by
  intro q _ E hE
  obtain ⟨one, hnat, hone⟩ := hU q
  obtain ⟨α, hα⟩ := hC (ZMod q) (tw q 0) E (fun U h => one U (hE U h))
    (fun V U g hU' hV' => hnat V U g _ _)
  refine ⟨α, fun U x ζ => ?_⟩
  rw [hα U x, hone U _ ζ]
  rfl

end LateralTheory.E.LeafOneExistsPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwTensResPf

def LeafTensTwres : Prop := LateralTheory.EtaleFoundations.EtaleTensorPairTwistResolutionMul

def LeafResFlat : Prop := ∀ (q : ℕ) [NeZero q] (j t : ℤ), FlatS ((res (ZMod q) (tw q j)).X t)

instance resGE (q : ℕ) (i : ℤ) : (res (ZMod q) (tw q i)).IsStrictlyGE 0 := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem res_isTwRes (q : ℕ) [NeZero q] (i : ℤ) :
    IsTwRes q i (res (ZMod q) (tw q i)) (fun _ ζ => resGen i ζ) := by
  refine ⟨resGE q i, resAug (tw q i), ?_, fun U ζ => ?_⟩
  · unfold resAug
    exact (inferInstance : QuasiIso (injectiveResolution (tw q i)).ι')
  · simp only [resGen, resι, sglι, Sec.map]
    rfl

theorem leafTwTensRes_of (h1 : LeafTensTwres) (h2 : LeafResFlat) : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensRes := by
  intro q _ i j T τ hτ
  exact h1 q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) (res_isTwRes q i) (res_isTwRes q j) (h2 q j) τ hτ

end LateralTheory.E.LeafTwTensResPf
end
end
