module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle008
public import Development.EtaleCohomology.CohomologicalPurity.Bundle011
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.CohomologicalPurity.Bundle012
public import Development.EtaleCohomology.CohomologicalPurity.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def OffContN (r : ℕ) : Prop := ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (x : Fin r → A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span (Set.range x)) D s t n i

def OffContBasic : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (f : A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  HtOffCont q φ (Ideal.span {f}) D s t n i

def OffContStep : Prop := A1 → A4 → B1 → LeafBd → LeafExc → OffContBasic → ∀ r : ℕ, OffContN r → OffContN (r + 1)

theorem offContN_zero (hb : OffContBasic) (a1 : A1) (a4 : A4) (b1 : B1) : OffContN 0 := by
  intro q A B _ _ φ x hq J _ _ D s t hc he n i
  have hx : Ideal.span (Set.range x) = Ideal.span {(0 : A)} := by
    rw [Set.range_eq_empty, Ideal.span_empty, Ideal.span_singleton_eq_bot.mpr rfl]
  rw [hx]
  exact hb a1 a4 b1 q φ 0 hq J D s t hc he n i

theorem offContN_all (hb : OffContBasic) (hs : OffContStep) (a1 : A1) (a4 : A4) (b1 : B1) (bd : LeafBd)
    (ex : LeafExc) : ∀ r, OffContN r := by
  intro r
  induction r with
  | zero => exact offContN_zero hb a1 a4 b1
  | succ r ih => exact hs a1 a4 b1 bd ex hb r ih

theorem leafOffCont_of (hb : OffContBasic) (hs : OffContStep) : LeafOffCont := by
  intro a1 a4 b1 bd ex q A B _ _ φ I hI hq J _ _ D s t hc he n i
  obtain ⟨S, hS⟩ := hI
  have h := offContN_all hb hs a1 a4 b1 bd ex S.card q φ (fun k => (S.equivFin.symm k : A)) hq J D s t hc he n i
  have hr : Set.range (fun k => (S.equivFin.symm k : A)) = (S : Set A) := by
    ext a; constructor
    · rintro ⟨k, rfl⟩; exact (S.equivFin.symm k).2
    · intro ha; exact ⟨S.equivFin ⟨a, ha⟩, by simp⟩
  rw [hr, hS] at h
  exact h

theorem off_span_singleton (A : Type) [CommRing A] (f : A) :
    ((off A (Ideal.span {f}) : Set (Spec (CommRingCat.of A))) =
      ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A))) := by
  change (PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]

theorem range_fin_succ {A : Type} {r : ℕ} (x : Fin (r + 1) → A) :
    Set.range x = Set.range (fun k : Fin r => x k.castSucc) ∪ {x (Fin.last r)} := by
  rw [Set.union_singleton]
  ext a; constructor
  · rintro ⟨k, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · exact Set.mem_insert_of_mem _ ⟨k', rfl⟩
    · exact Set.mem_insert _ _
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def pcok (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A) (b : B' ⟶ B)
    (w : i' ≫ b = a ≫ i) : cokernel ((freeP R).map i') ⟶ cokernel ((freeP R).map i) :=
  cokernel.map _ _ ((freeP R).map a) ((freeP R).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, w])

theorem isIso_cokernel_map_of_etale_local_iso (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (hW : Scheme.etaleTopology.W (pcok R i' i a b w)) :
    IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
      (by rw [← Functor.map_comp, ← Functor.map_comp, w])) := by
  rw [GrothendieckTopology.W_iff] at hW
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w' : (freeP R).map i' ≫ (freeP R).map b = (freeP R).map a ≫ (freeP R).map i := by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  have key : cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, ← w', G.map_comp]) ≫
        cokernelComparison ((freeP R).map i) G =
      cokernelComparison ((freeP R).map i') G ≫ G.map (pcok R i' i a b w) :=
    cokernel_map_comp_cokernelComparison _ G _ _ _ (by first | exact w' | exact w'.symm)
  have h2 : IsIso (cokernelComparison ((freeP R).map i') G ≫ G.map (pcok R i' i a b w)) := by
    have : IsIso (G.map (pcok R i' i a b w)) := hW
    infer_instance
  have h3 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, ← w', G.map_comp])) := by
    have h4 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, ← w', G.map_comp]) ≫ cokernelComparison _ G) := by
      rw [key]; exact h2
    exact IsIso.of_isIso_comp_right _ (cokernelComparison ((freeP R).map i) G)
  exact h3

def LeafFreeCokSurj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  Presheaf.IsLocallySurjective Scheme.etaleTopology (pcok R i' i a b w)

def LeafFreeCokInj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  Presheaf.IsLocallyInjective Scheme.etaleTopology (pcok R i' i a b w)

theorem LeafFreeCok_of (hS : LeafFreeCokSurj) (hI : LeafFreeCokInj) : LeafFreeCok := by
  intro R _ A' B' A B i' i a b w h1 h2 h3
  apply isIso_cokernel_map_of_etale_local_iso
  have := hS R i' i a b w h2
  have := hI R i' i a b w h1 h3
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

def WVec (d : ℕ) (U : Scheme.{0}) : Type := {v : Vec (d + 1) 0 U // IsUnit (v.1 0)}

instance (d : ℕ) (U : Scheme.{0}) : SmallCategory (WVec d U) where
  Hom v w := v.1 ⟶ w.1
  id v := 𝟙 v.1
  comp f g := f ≫ g
  id_comp f := Category.id_comp (obj := Vec (d + 1) 0 U) f
  comp_id f := Category.comp_id (obj := Vec (d + 1) 0 U) f
  assoc f g h := Category.assoc (obj := Vec (d + 1) 0 U) f g h

def WVec.map (d : ℕ) {V U : Scheme.{0}} (f : V ⟶ U) : WVec d U ⥤ WVec d V where
  obj v := ⟨(Vec.map (d + 1) 0 f).obj v.1, v.2.map f.appTop.hom⟩
  map u := (Vec.map (d + 1) 0 f).map u
  map_id v := (Vec.map (d + 1) 0 f).map_id v.1
  map_comp p q := (Vec.map (d + 1) 0 f).map_comp p q

def wCat (d : ℕ) : Scheme.{0}ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (WVec d U.unop)
  map f := (WVec.map d f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def Wsp (d : ℕ) : Spc := (wCat d ⋙ nerveFunctor).flip

def WVec.incl (d : ℕ) (U : Scheme.{0}) : WVec d U ⥤ Vec (d + 1) 0 U where
  obj v := v.1
  map u := u

def Wincl (d : ℕ) : Wsp d ⟶ Pj (d + 1) 0 :=
  nerveMap { app := fun U => (WVec.incl d U.unop).toCatHom, naturality := fun _ _ _ => rfl }

def Wpt {d : ℕ} {X : Scheme.{0}} (v : WVec d X) : sch.obj X ⟶ Wsp d where
  app n :=
    { app := fun U => TypeCat.ofHom fun (f : U.unop ⟶ X) =>
        (Functor.const (Fin (n.unop.len + 1))).obj ((WVec.map d f).obj v)
      naturality := fun U U' g => by
        ext f
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact ((WVec.map d g.unop).map_id ((WVec.map d f).obj v)).symm }
  naturality n m f := rfl

theorem wpt_incl {d : ℕ} {X : Scheme.{0}} (v : WVec d X) : Wpt v ≫ Wincl d = Pj.pt v.1 := rfl

def wvec1 {d : ℕ} {A : Type} [CommRing A] (x : Fin d → A) : WVec d (Spec (CommRingCat.of A)) :=
  ⟨vec1 x, by
    show IsUnit ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) 0))
    rw [Fin.cons_zero, map_one]; exact isUnit_one⟩

abbrev W (d : ℕ) (R : Type) [CommRing R] : Spc := Wsp d ⨯ sp R

def wb (d : ℕ) (R : Type) [CommRing R] : W d R ⟶ PR (d + 1) 0 R := prod.map (Wincl d) (𝟙 _)

def wa (d : ℕ) (R : Type) [CommRing R] : sp (MvPolynomial (Fin d) R) ⟶ W d R :=
  prod.lift (Wpt (wvec1 MvPolynomial.X)) (spMap MvPolynomial.C)

theorem wa_wb (d : ℕ) (R : Type) [CommRing R] : wa d R ≫ wb d R =
    (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
      sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) := by
  simp only [wa, wb, prod.lift_map, Category.comp_id, wpt_incl]
  rfl

theorem opn_mono {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  have h : ∀ n, Mono ((sch.map U.ι).app n) := by
    intro n
    have : ∀ V, Mono (((sch.map U.ι).app n).app V) := by
      intro V
      rw [mono_iff_injective]
      intro f g h
      change f ≫ U.ι = g ≫ U.ι at h
      exact (cancel_mono U.ι).1 h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

def LeafWCov : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  Cover2 (ZMod q) (wb d R) (pr d R).hom

def LeafWEqvR : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∀ i, Eqv _ (wa d R) (tw q i)

def LeafWEqvL : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
  (I : Ideal (MvPolynomial (Fin d) R)), Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) →
  ∀ g : (opn (off (MvPolynomial (Fin d) R) I)).left ⟶ pullback (wb d R) (pr d R).hom,
  g ≫ pullback.fst _ _ = (opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R → ∀ i, Eqv _ g (tw q i)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

namespace LateralTheory.CohomologicalPurity.Thom.ExcP

open Chart in
theorem LeafChartFact_of (hG : LeafGeo) (hC : LeafWCov) (hR : LeafWEqvR) (hL : LeafWEqvL) :
    LeafChartFact := by
  intro hH q _ d R _ I hI hq Φ hΦ
  have := hG.1 d R
  have hab : wa d R ≫ wb d R = Φ.right := by rw [hΦ, wa_wb]
  have hw : ((opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R) ≫ wb d R = Φ.left ≫ (pr d R).hom := by
    erw [Category.assoc, hab]; exact (Arrow.w Φ).symm
  let P : Arrow Spc := Arrow.mk (pullback.fst (wb d R) (pr d R).hom)
  let β : P ⟶ pr d R := Arrow.homMk (pullback.snd _ _) (wb d R) pullback.condition.symm
  let α : opn (off (MvPolynomial (Fin d) R) I) ⟶ P :=
    Arrow.homMk (pullback.lift _ _ hw) (wa d R) (pullback.lift_fst _ _ _)
  refine ⟨P, α, β, ?_, opn_mono _, (IsPullback.of_hasPullback (wb d R) (pr d R).hom).mono_fst_of_mono this,
    hL hH q d R I hI hq _ (pullback.lift_fst _ _ _), hR hH q d R hq, IsPullback.of_hasPullback _ _, hC hH q d R hq⟩
  exact hom_ext (hG.1 d R) (by rw [Arrow.comp_right]; exact hab)

end LateralTheory.CohomologicalPurity.Thom.ExcP
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem Vec.hom_subsingleton (N k : ℕ) (U : Scheme.{0}) (v w : Vec N k U) : Subsingleton (v ⟶ w) := by
  constructor
  intro a b
  apply Subtype.ext; apply Units.ext
  rw [← sub_eq_zero]
  set s : Γ(U, ⊤) := (a.1 : Γ(U, ⊤)) - b.1 with hs_def
  have hs : ∀ i, s * w.1 i = 0 := fun i => by rw [hs_def, sub_mul, ← a.2 i, ← b.2 i, sub_self]
  have hcov : (⊤ : U.Opens) ≤ iSup fun i => U.basicOpen (w.1 i) := by
    intro p _
    obtain ⟨i, -, hp⟩ := w.2 p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hp⟩
  refine U.sheaf.eq_of_locally_eq' (fun i => U.basicOpen (w.1 i)) ⊤ (fun i => homOfLE le_top) hcov s 0 fun i => ?_
  have hu : IsUnit (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op (w.1 i)) :=
    U.toRingedSpace.isUnit_res_basicOpen (w.1 i)
  have h0 := congrArg (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op) (hs i)
  rw [map_mul, map_zero] at h0
  change U.presheaf.map _ s = U.presheaf.map _ 0
  rw [map_zero]
  exact (hu.mul_left_eq_zero).1 h0

theorem off_le_C (A : Type) [CommRing A] (I : Ideal A) : off (Polynomial A) (I.map Polynomial.C) ≤
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I := by
  intro p hp
  simp only [off, Scheme.Hom.mem_preimage] at hp ⊢
  intro hI
  apply hp
  have hI' : ∀ x ∈ I, Polynomial.C x ∈ p.asIdeal := fun x hx => hI hx
  show ((Ideal.map Polynomial.C I : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal
  exact Ideal.map_le_iff_le_comap.2 (fun x hx => hI' x hx)

def LeafTailNerve : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R')
    (e₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)))
    (e₂ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0))),
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n ≫ e₂.hom =
      e₁.hom ≫ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R' ⟶ PR d 0 R').app (op (SimplexCategory.mk 0))

def LeafTailRep0 : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : (PR (d + 1) 1 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : (PR d 0 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off A I).toScheme),
      (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app (op (SimplexCategory.mk 0)) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep_of (hN : LeafTailNerve) (h0 : LeafTailRep0) : LeafTailRep := by
  intro d R _ n
  obtain ⟨R', _, ψ, e₁, e₂, w₁⟩ := hN d R n
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w₂⟩ := h0 d R'
  refine ⟨A, inferInstance, I, φ.comp ψ, hI, h, disc.mapIso (e₁ ≪≫ f₁), disc.mapIso (e₂ ≪≫ f₂), ?_⟩
  change disc.map _ ≫ disc.map (e₂.hom ≫ f₂.hom) = disc.map (e₁.hom ≫ f₁.hom) ≫ disc.map (yoneda.map _)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, w₁, Category.assoc, w₂, Category.assoc]

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem hk_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cone_map_congr {R : Type} [CommRing R] {K₁ L₁ K₂ L₂ : Cx R} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (h : f₁ ≫ b = a ≫ f₂) (h' : f₁ ≫ b' = a' ≫ f₂) (ha : a = a') (hb : b = b') :
    mappingCone.map f₁ f₂ a b h = mappingCone.map f₁ f₂ a' b' h' := by
  subst ha; subst hb; rfl

theorem dbl_sq (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map P.hom ≫ (chains R).map (dbl.inl P) = (chains R).map P.hom ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (pushout.condition (f := P.hom) (g := P.hom))

def dblCone (R : Type) [CommRing R] (P : Arrow Spc) :
    mappingCone ((chains R).map P.hom) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map P.hom) ((chains R).map (dbl.inl P)) (dbl_sq R P)

theorem dblMap_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map (dbl.inr P') ≫ (chains R).map (dbl.map φ) = (chains R).map φ.right ≫ (chains R).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]

def dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone ((chains R).map (dbl.inr P')) ⟶ mappingCone ((chains R).map (dbl.inr P)) :=
  mappingCone.map _ _ ((chains R).map φ.right) ((chains R).map (dbl.map φ)) (dblMap_sq R φ)

theorem dblCone_nat (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    coneMap R φ ≫ dblCone R P = dblCone R P' ≫ dblConeMap R φ := by
  unfold coneMap dblCone dblConeMap
  rw [← mappingCone.map_comp, ← mappingCone.map_comp]
  apply cone_map_congr
  · rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ)
  · rw [← Functor.map_comp, ← Functor.map_comp, inl_map]

theorem inr_dblConeMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    mappingCone.inr _ ≫ dblConeMap R φ = (chains R).map (dbl.map φ) ≫ mappingCone.inr _ := by
  simp [dblConeMap, mappingCone.map]

def LeafDblConeQI : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → QuasiIso (dblCone R P)

def LeafConeSplit : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (g : K ⟶ L) (r : L ⟶ K), g ≫ r = 𝟙 K →
  ∀ (F : Shv R) (n : ℤ), Function.Injective (HK.pull R (mappingCone.inr g) F n) ∧
    ∀ y : HK R L F n, HK.pull R g F n y = 0 ↔ ∃ x, HK.pull R (mappingCone.inr g) F n x = y

theorem inr_fold_chains (R : Type) [CommRing R] (P : Arrow Spc) :
    (chains R).map (dbl.inr P) ≫ (chains R).map (dbl.fold P) = 𝟙 _ := by
  rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]

def psi (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) :
    HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n).codRestrict _ fun x =>
    ((hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n).2 _).2 ⟨x, rfl⟩

theorem psi_bij (q : ℕ) (P : Arrow Spc) (n i : ℤ) (hS : LeafConeSplit) : Function.Bijective (psi q P n i hS) := by
  have h := hS (ZMod q) _ _ (inr_fold_chains (ZMod q) P) (tw q i) n
  refine ⟨fun a b hab => h.1 (congrArg Subtype.val hab), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (h.2 y.1).1 y.2
  exact ⟨x, Subtype.ext hx⟩

theorem leafHsRel_of (hD : LeafDblConeQI) (hS : LeafConeSplit) : LeafHsRel := by
  intro h1 q i
  let θ : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
      (HK (ZMod q) (mappingCone ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hrel (ZMod q) P.hom (tw q i) n) :=
    fun P n h => by
      haveI := hD (ZMod q) P h
      exact AddEquiv.ofBijective (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n) (h1 (ZMod q) _ (tw q i) n)
  refine ⟨fun P n h => (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm.trans (θ P n h), ?_⟩
  intro P' P φ h' h n x
  have key : (AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x) =
      HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n
        ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x) := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    set y := (AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x with hy
    have hx : x = psi q P n i hS y := by
      rw [hy]; exact ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).apply_symm_apply x).symm
    rw [hx]
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
        (HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n y) =
      HK.pull (ZMod q) (mappingCone.inr _) (tw q i) n (HK.pull (ZMod q) (dblConeMap (ZMod q) φ) (tw q i) n y)
    rw [← hk_pull_comp, ← hk_pull_comp, inr_dblConeMap]
  change HK.pull (ZMod q) (dblCone (ZMod q) P') (tw q i) n
      ((AddEquiv.ofBijective (psi q P' n i hS) (psi_bij q P' n i hS)).symm (Hs.pull q φ n i x)) =
    HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (HK.pull (ZMod q) (dblCone (ZMod q) P) (tw q i) n
      ((AddEquiv.ofBijective (psi q P n i hS) (psi_bij q P n i hS)).symm x))
  rw [key, ← hk_pull_comp, ← hk_pull_comp, dblCone_nat]

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem LeafBZ_of : LeafBZ := by
  intro R _ K X U n W a ⟨b, hb0, hba⟩
  subst hba
  refine ⟨?_, ?_⟩
  · show ((K.X n).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    have e := congrArg (fun φ => φ.hom b) ((K.d (n - 1) n).hom.naturality (W.ι ⁻¹ᵁ U).ι.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [← e]
    have hb0' : ((K.X (n - 1)).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom b = 0 := hb0
    rw [hb0', map_zero]
  · show ((K.d n (n + 1)).hom.app (op W.toScheme)).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    change ((K.d (n - 1) n ≫ K.d n (n + 1)).hom.app (op W.toScheme)).hom b = 0
    rw [K.d_comp_d]
    rfl

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end
