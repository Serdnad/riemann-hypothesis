module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle006
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom
namespace ActPf

variable {d : ℕ} {A : Type} [CommRing A]

def φ {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A)) : A →+* Γ(U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appTop).hom

theorem φ_comp {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    φ (f ≫ s) = f.appTop.hom.comp (φ s) := rfl

def actV (M : Matrix (Fin d) (Fin d) A) {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) : Fin (d + 1) → Γ(U, ⊤) :=
  Fin.cons (v 0) ((M.map (φ s)).mulVec (Fin.tail v))

theorem actV_mem (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) (v : Fin (d + 1) → Γ(U, ⊤)) (p : U)
    (h : ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (v i)) :
    ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (actV M s v i) := by
  obtain ⟨i, hi, hp⟩ := h
  by_contra hc
  push Not at hc
  have hM' : IsUnit (M.map (φ s)).det := by
    have h := hM.map (φ s); rw [RingHom.map_det] at h; exact h
  have hz : ∀ j : Fin d, (U.Γevaluation p).hom ((M.map (φ s)).mulVec (Fin.tail v) j) = 0 := by
    intro j
    have := hc j.succ (by simp; omega)
    simp only [actV, Fin.cons_succ] at this
    exact (Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).2 this
  have ht : ∀ j : Fin d, (U.Γevaluation p).hom (Fin.tail v j) = 0 := by
    intro j
    have hinv : (M.map (φ s))⁻¹.mulVec ((M.map (φ s)).mulVec (Fin.tail v)) = Fin.tail v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM', Matrix.one_mulVec]
    rw [← hinv, RingHom.map_mulVec]
    have : ((U.Γevaluation p).hom ∘ (M.map (φ s)).mulVec (Fin.tail v)) = 0 := funext hz
    rw [this, Matrix.mulVec_zero]; rfl
  cases i using Fin.cases with
  | zero =>
    have := hc 0 (by simp at hi; omega)
    simp only [actV, Fin.cons_zero] at this
    exact this hp
  | succ j =>
    exact ((Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).1 (ht j)) hp

def actF (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) : Vec (d + 1) k U ⥤ Vec (d + 1) k U where
  obj v := ⟨actV M s v.1, fun p => actV_mem M hM hk s v.1 p (v.2 p)⟩
  map {v w} u := ⟨u.1, fun i => by
    cases i using Fin.cases with
    | zero => simp only [actV, Fin.cons_zero]; exact u.2 0
    | succ j =>
      simp only [actV, Fin.cons_succ]
      have : Fin.tail v.1 = (u.1 : Γ(U, ⊤)) • Fin.tail w.1 := funext fun l => by
        simp only [Fin.tail, Pi.smul_apply, smul_eq_mul]; exact u.2 l.succ
      rw [this, Matrix.mulVec_smul]; rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem comp_val {N k : ℕ} {U : Scheme.{0}} {X Y Z : Vec N k U} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (a ≫ b).1 = b.1 * a.1 := rfl

theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {X Y : Vec N k U} (h : X = Y) : (eqToHom h).1 = 1 := by
  subst h; rfl

theorem actV_map (M : Matrix (Fin d) (Fin d) A) {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) :
    (fun i => f.appTop.hom (actV M s v i)) = actV M (f ≫ s) (fun i => f.appTop.hom (v i)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [actV]
  | succ j =>
    simp only [actV, Fin.cons_succ]
    rw [RingHom.map_mulVec, φ_comp, Matrix.map_map]
    rfl

theorem actF_map (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {V U : Scheme.{0}}
    (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    actF M hM hk s ⋙ Vec.map (d + 1) k f = Vec.map (d + 1) k f ⋙ actF M hM hk (f ≫ s) := by
  refine CategoryTheory.Functor.ext (fun v => Subtype.ext (actV_map M f s v.1)) (fun v w u => ?_)
  apply Subtype.ext
  simp only [comp_val, eqToHom_val, one_mul]
  erw [eqToHom_val, mul_one]
  rfl

def actSp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) : E ⟶ Pj (d + 1) k where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        ((show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙
          actF M hM hk (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x) :
          Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
      naturality := fun U U' f => by
        ext x
        have h1 := ConcreteCategory.congr_hom ((a.app n).naturality f) x
        have h2 := ConcreteCategory.congr_hom ((b.app n).naturality f) x
        refine (congrArg₂ (fun (F : Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U'.unop)
          (s : U'.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (n.unop.len + 1) ⥤ _)) h1 h2).trans ?_
        exact congrArg (fun G => (show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙ G)
          (actF_map M hM hk f.unop (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x)).symm }
  naturality n m f := by
    ext U x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (a.naturality f) U) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (b.naturality f) U) x
    exact (congrArg₂ (fun (F : Fin (m.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
          (s : U.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (m.unop.len + 1) ⥤ _)) h1 h2).trans rfl

theorem actSp_comp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E' E : Spc}
    (g : E' ⟶ E) (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    g ≫ actSp M hM hk a b = actSp M hM hk (g ≫ a) (g ≫ b) := by
  ext n U x; rfl

theorem actSp_incl (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {E : Spc}
    (a : E ⟶ Pj (d + 1) 1) (b : E ⟶ sp A) :
    actSp M hM le_rfl a b ≫ Pj.incl (d + 1) = actSp M hM (Nat.zero_le 1) (a ≫ Pj.incl (d + 1)) b := by
  ext n U x; rfl

theorem actSp_line (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    actSp M hM hk a b ≫ Pj.line (d + 1) k = a ≫ Pj.line (d + 1) k := by
  ext n U x; rfl

theorem actSp_pt (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) (x : Fin d → A) :
    actSp M hM (Nat.zero_le 1) (Pj.pt (vec1 x)) (𝟙 (sp A)) = Pj.pt (vec1 (M.mulVec x)) := by
  ext n U f
  refine CategoryTheory.Functor.ext (fun _ => Subtype.ext ?_) (fun _ _ _ => ?_)
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      show ((M.map (φ _)).mulVec _) j = φ _ ((M.mulVec x) j)
      rw [RingHom.map_mulVec]
      rfl
  · apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val]
    simp only [one_mul, mul_one]
    erw [eqToHom_val]
    rfl

end ActPf

open ActPf in
theorem LeafAct_of : LeafAct := by
  intro d A _ M hM
  let gR : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A :=
    prod.lift (actSp M hM (Nat.zero_le 1) prod.fst prod.snd) prod.snd
  let gL : PR (d + 1) 1 A ⟶ PR (d + 1) 1 A := prod.lift (actSp M hM le_rfl prod.fst prod.snd) prod.snd
  have hw : gL ≫ (pr d A).hom = (pr d A).hom ≫ gR := by
    apply prod.hom_ext
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_fst, prod.lift_fst, gL, gR]
      rw [prod.lift_fst_assoc, actSp_incl, actSp_comp, prod.map_fst, prod.map_snd, Category.comp_id]
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd, gL, gR]
  refine ⟨Arrow.homMk gL gR hw, ?_, ?_, ?_⟩
  · change gR ≫ prod.fst ≫ Pj.line (d + 1) 0 = _
    rw [prod.lift_fst_assoc, actSp_line]
  · change gR ≫ prod.snd = _
    exact prod.lift_snd _ _
  · intro x
    change chart x ≫ gR = _
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, actSp_comp, chart, prod.lift_fst, prod.lift_snd, actSp_pt, chart, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, chart, chart, prod.lift_snd, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd
namespace ImgPf

variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}
  (T0 : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s))

def T' (E : Spc) (p s : ℤ) : (((chains S).obj E).X p ⟶ I.X s) →+ (((chains R).obj E).X p ⟶ J.X s) :=
  if h : -(((-p).toNat : ℕ) : ℤ) = p then
    { toFun := fun φ => (((chains R).obj E).XIsoOfEq h).inv ≫ (chainsXIso R E _).hom ≫
        T0 _ s ((chainsXIso S E _).inv ≫ (((chains S).obj E).XIsoOfEq h).hom ≫ φ)
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add] }
  else 0

theorem T'_eq (E : Spc) (k : ℕ) (s : ℤ) (φ : ((chains S).obj E).X (-(k : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s φ = (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
  have key : ∀ (k' : ℕ) (h' : -(k' : ℤ) = -(k : ℤ)), (((chains R).obj E).XIsoOfEq h').inv ≫ (chainsXIso R E k').hom ≫
      T0 _ s ((chainsXIso S E k').inv ≫ (((chains S).obj E).XIsoOfEq h').hom ≫ φ) =
      (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
    intro k' h'
    obtain rfl : k' = k := by omega
    simp [HomologicalComplex.XIsoOfEq_rfl]
  unfold T'
  rw [dite_eq_left (by simp)]
  exact key _ _

theorem T'_pos (E : Spc) (p s : ℤ) (hp : 0 < p) : T' T0 E p s = 0 := by
  unfold T'
  rw [dite_eq_right (by omega)]

theorem T'_comp_d (E : Spc) (p s t : ℤ) (φ : ((chains S).obj E).X p ⟶ I.X s)
    (hd : ∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T0 P t (φ ≫ I.d s t) = T0 P s φ ≫ J.d s t) :
    T' T0 E p t (φ ≫ I.d s t) = T' T0 E p s φ ≫ J.d s t := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [T'_eq, T'_eq, ← Category.assoc, hd, Category.assoc]
  · rw [T'_pos T0 E p t hp, T'_pos T0 E p s hp]
    simp

theorem T'_free (E E' : Spc) (k k' : ℕ) (s : ℤ) {ι : Type} [Fintype ι] (c : ι → ℤ)
    (u : ι → (E.obj (op (SimplexCategory.mk k)) ⟶ E'.obj (op (SimplexCategory.mk k'))))
    (gS : ((chains S).obj E).X (-(k : ℤ)) ⟶ ((chains S).obj E').X (-(k' : ℤ)))
    (gR : ((chains R).obj E).X (-(k : ℤ)) ⟶ ((chains R).obj E').X (-(k' : ℤ)))
    (hS : gS = (chainsXIso S E k).hom ≫ (∑ i, c i • (free S).map (u i)) ≫ (chainsXIso S E' k').inv)
    (hR : gR = (chainsXIso R E k).hom ≫ (∑ i, c i • (free R).map (u i)) ≫ (chainsXIso R E' k').inv)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ)
    (φ : ((chains S).obj E').X (-(k' : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s (gS ≫ φ) = gR ≫ T' T0 E' (-(k' : ℤ)) s φ := by
  rw [T'_eq, T'_eq, hS, hR]

  simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul, hn]

theorem T'_d (E : Spc) (p p' s : ℤ) (h : p + 1 = p') (φ : ((chains S).obj E).X p' ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).obj E).d p p' ≫ φ) = ((chains R).obj E).d p p' ≫ T' T0 E p' s φ := by
  rcases lt_or_ge p 0 with hp | hp
  · obtain ⟨k, rfl, rfl⟩ : ∃ k : ℕ, p = -((k + 1 : ℕ) : ℤ) ∧ p' = -(k : ℤ) := ⟨(-p - 1).toNat, by omega, by omega⟩
    refine T'_free T0 E E k.succ k s (fun i : Fin (k + 2) => ((-1 : ℤ) ^ (i : ℕ))) (fun i => E.δ i) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extend_d_eq ((chainsN S).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
    · refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
  · have hz : ((chains S).obj E).d p p' = 0 := by
      apply (HomologicalComplex.isZero_extend_X _ _ p' ?_).eq_of_tgt
      intro i hi
      change -(i : ℤ) = p' at hi
      omega
    rw [hz, T'_pos T0 E p' s (by omega)]
    simp

theorem T'_map (E E' : Spc) (f : E ⟶ E') (p s : ℤ) (φ : ((chains S).obj E').X p ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).map f).f p ≫ φ) = ((chains R).map f).f p ≫ T' T0 E' p s φ := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    refine T'_free T0 E E' k k s (fun _ : Unit => 1) (fun _ => f.app _) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extendMap_f ((chainsN S).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
    · refine (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
  · rw [T'_pos T0 E p s hp, T'_pos T0 E' p s hp]
    simp

def TC (E : Spc) (n : ℤ) : Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n where
  toFun α := Cochain.mk fun p q h => T' T0 E p q (α.v p q h)
  map_zero' := Cochain.ext _ _ fun p q h => by simp
  map_add' α β := Cochain.ext _ _ fun p q h => by simp [Cochain.add_v]

theorem TC_v (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p q : ℤ) (h : p + n = q) :
    (TC T0 E n α).v p q h = T' T0 E p q (α.v p q h) :=
  Cochain.mk_v (fun p q h => T' T0 E p q (α.v p q h)) p q h

end ImgPf

open ImgPf in
theorem LeafImg_of (hI : LeafImgHom) : LeafImg := by
  intro S R _ _ I J ρ
  obtain ⟨T0, hgen, hd, hn⟩ := hI S R I J ρ
  refine ⟨fun E n => TC T0 E n, ?_, ?_, ?_⟩
  · intro E n α p s h U x
    unfold ev
    rw [TC_v, T'_eq, Iso.inv_hom_id_assoc]
    exact hgen _ _ _ U x
  · intro E n m α
    by_cases hnm : n + 1 = m
    · refine Cochain.ext _ _ fun p q hpq => ?_
      rw [TC_v, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
        map_add, Units.smul_def, Units.smul_def, map_zsmul, T'_comp_d T0 E _ _ _ _ hd, TC_v, TC_v,
        T'_d T0 E p (p + 1) q rfl _ hn]
    · rw [δ_shape n m hnm, δ_shape n m hnm, map_zero]
  · intro E E' f n α
    refine Cochain.ext _ _ fun p q hpq => ?_
    simp only [pb, TC_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    exact T'_map T0 E E' f p q _ hn

end LateralTheory.CohomologicalPurity.Bd
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

namespace GenPf

variable (R : Type) [CommRing R]

abbrev mk {P : PSh} {U : Scheme.{0}} (x : P.obj (op U)) : ((freeP R).obj P).obj (op U) :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj (op U))) (ULift.up x)

theorem freePresheaf_obj_map_mk (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (mk R x) = mk R (P.map g.op x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

theorem freePresheaf_map_app_mk {P P' : PSh} (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (mk R x) = mk R (f.app (op U) x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

theorem part1 (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom k (mk R x))
    ((toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_obj_map_mk] at h
  exact h.symm

theorem part2 (P P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom (NatTrans.app k (op U)) (mk R x))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_map_app_mk] at h
  exact h.symm

def adjE (P : PSh) (G : Shv R) : ((free R).obj P ⟶ G) ≃ ((freeP R).obj P ⟶ G.obj) :=
  (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv ((freeP R).obj P) G

theorem adjE_apply (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) :
    adjE R P G φ = toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P) ≫ φ.hom :=
  Adjunction.homEquiv_unit _ _ _ _

theorem adjE_gen (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    ((adjE R P G φ).app (op U)).hom (mk R x) = Sec.map φ (freeGen R P U x) := by
  rw [adjE_apply]; rfl

theorem part3 (P : PSh) (G : Shv R) (φ ψ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) :
    φ = ψ := by
  apply (adjE R P G).injective
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨U⟩ := U
  apply ModuleCat.free_hom_ext
  rintro ⟨y⟩
  exact (adjE_gen R P G φ U y).trans ((h U y).trans (adjE_gen R P G ψ U y).symm)

def descP (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun y => t U.unop (ULift.down y))
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    obtain ⟨U⟩ := U
    obtain ⟨V⟩ := V
    rintro ⟨y⟩
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    erw [freePresheaf_obj_map_mk R P g.unop y, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (ht g.unop y).symm

theorem freePresheafDesc_app_mk (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((descP R P G t ht).app (op U)).hom (mk R x) = t U x := by
  simp only [descP]
  exact ModuleCat.freeDesc_apply _ _

theorem part4 (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x := by
  refine ⟨(adjE R P G).symm (descP R P G t ht), fun U x => ?_⟩
  rw [← adjE_gen, Equiv.apply_symm_apply, freePresheafDesc_app_mk]

end GenPf

theorem LeafGen_of : LeafGen := by
  intro R _ P
  exact ⟨fun g x => GenPf.part1 R P g x, fun P' f U x => GenPf.part2 R P P' f U x,
    fun G φ ψ h => GenPf.part3 R P G φ ψ h, fun G t ht => GenPf.part4 R P G t ht⟩

end LateralTheory.CohomologicalPurity.Bd
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

theorem pb_v {R : Type} [CommRing R] {A B I : Cx R} (f : A ⟶ B) {n : ℤ} (c : Cochain B I n) (p q : ℤ) (hpq : p + n = q) :
    (pb f c).v p q hpq = f.f p ≫ c.v p q hpq := by
  simp [pb, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

theorem LeafGood_of : LeafGood := by
  intro R _ A B D i l r I hm hp hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro p
    simpa using (hp p).w
  · intro n a
    refine ⟨Cochain.mk (fun p q hpq => Injective.factorThru (a.v p q hpq) (i.f p)), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [pb_v]
    simp [Cochain.mk_v]
  · intro n c c' h
    refine ⟨Cochain.mk (fun p q hpq => (hp p).desc (c.v p q hpq) (c'.v p q hpq) (by
      have := congrArg (fun x => x.v p q hpq) h
      simpa only [pb_v] using this)), ?_, ?_⟩
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
  · intro n b b' h1 h2
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    apply (hp p).hom_ext
    · have := congrArg (fun x => x.v p q hpq) h1
      simpa only [pb_v] using this
    · have := congrArg (fun x => x.v p q hpq) h2
      simpa only [pb_v] using this

end LateralTheory.CohomologicalPurity.Bd
end
end
