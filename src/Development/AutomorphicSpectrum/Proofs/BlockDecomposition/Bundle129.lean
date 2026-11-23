module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CovDescent

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)

theorem cosieve_capU (hU : ∀ α, Cosieve (U α)) (S : Finset ι) : Cosieve (capU U S) := fun _ _ φ h =>
  ⟨h.1.imp fun a ha => hU a φ ha, fun α hα => hU α φ (h.2 α hα)⟩

variable {U} in
theorem capU_mono {S T : Finset ι} (h : S ⊆ T) {X : C} (hX : capU U T X) : capU U S X :=
  ⟨hX.1, fun α hα => hX.2 α (h hα)⟩

variable {U} in
theorem capU_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capU U (ent i) T) :
    capU U (ent (Fin.cons (α := fun _ => ι) a i)) T := by
  refine ⟨⟨a, ha⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi.2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

def liftC (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : ComposableArrows (capU U S).FullSubcategory n :=
  (capU U S).lift s fun k => cosieve_capU U hU S (s.map (homOfLE (Fin.zero_le k))) h

abbrev Tm (n : ℕ) : PM.{max u v w} R ι := (covSy F U hQ).term n

def evL (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : (Tm F U hQ n).M S →ₗ[R] F.obj (s.obj (Fin.last n)) :=
  (LinearMap.proj (R := R) (φ := fun t : ComposableArrows (capU U S).FullSubcategory n =>
    ((capU U S).ι ⋙ F).obj (t.obj (Fin.last n))) (liftC U hU S s h)) ∘ₗ
    (relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n).subtype

variable {F U hQ}

theorem evL_congr (hU : ∀ α, Cosieve (U α)) {n p : ℕ} (f : ∀ i : Fin p → ι, (Tm F U hQ n).M (ent i))
    {i i' : Fin p → ι} (e : i = i') (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0))
    (h' : capU U (ent i') (s.obj 0)) : evL F U hQ hU _ s h (f i) = evL F U hQ hU _ s h' (f i') := by
  subst e; rfl

theorem evL_d (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X p)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0)) :
    evL F U hQ hU _ s h ((Tm F U hQ n).cech.d p y i) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        evL F U hQ hU _ s (capU_mono (ent_comp i k.succAbove) h) (y (i ∘ k.succAbove)) := by
  have e := congrArg ((evL F U hQ hU _ s h) ∘ₗ
    (LinearMap.proj (R := R) (φ := fun i : Fin (p + 2) → ι => (Tm F U hQ n).M (ent i)) i))
    (Cos.d_apply (Tm F U hQ n).cech p y)

  rw [map_sum] at e
  simp only [map_zsmul] at e
  exact e

theorem capU_const {b : ι} {T : C} (hb : U b T) : capU U (ent fun _ : Fin 1 => b) T := by
  refine ⟨⟨b, hb⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  exact hb

theorem cons_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Function.comp]

theorem cons_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ j.succ.succAbove =
      Fin.cons (α := fun _ => ι) a (i ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp]
  · simp [Function.comp]

theorem M_ext (hU : ∀ α, Cosieve (U α)) {n : ℕ} {S : Finset ι} {x y : (Tm F U hQ n).M S}
    (h : ∀ t : ComposableArrows (capU U S).FullSubcategory n,
      evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property x =
        evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property y) : x = y :=
  Subtype.ext (funext h)

def mkM {n : ℕ} (S : Finset ι) (f : CH.Cn ((capU U S).ι ⋙ F) n)
    (hf : ∀ t : ComposableArrows (capU U S).FullSubcategory n, Q (t.obj 0).obj → f t = 0) :
    (Tm F U hQ n).M S :=
  (⟨f, hf⟩ : relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n)

theorem evL_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (x : (Tm F U hQ n).M S)
    (s : ComposableArrows C n) (h : capU U S (s.obj 0)) (hs : Q (s.obj 0)) :
    evL F U hQ hU S s h x = 0 :=
  x.2 (liftC U hU S s h) hs

theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X (p + 1))
    (hy : (Tm F U hQ n).cech.d (p + 1) y = 0) (i : Fin (p + 2) → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d (p + 1) y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_succ] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 : ∀ j : Fin (p + 2),
      evL F U hQ hU _ s (capU_mono (ent_comp _ j.succ.succAbove) h')
        (y ((Fin.cons (α := fun _ => ι) b i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) =
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) :=
    fun j => evL_congr hU y (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (y : (Tm F U hQ n).cech.X 0)
    (hy : (Tm F U hQ n).cech.d 0 y = 0) (i : Fin 1 → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = evL F U hQ hU _ s (capU_const hb) (y fun _ => b) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d 0 y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_two] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 := evL_congr hU y (i := (Fin.cons (α := fun _ => ι) b i : Fin 2 → ι) ∘ (1 : Fin 2).succAbove)
    (i' := fun _ => b) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (capU_mono (ent_comp _ _) h') (capU_const hb)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

def hh (hU : ∀ α, Cosieve (U α)) (a : ∀ T, (∃ b, U b T) → ι) (ha : ∀ T h, U (a T h) T) {p n : ℕ}
    (y : (Tm F U hQ n).cech.X (p + 1)) : (Tm F U hQ n).cech.X p := fun i =>
  mkM (ent i) (fun t => evL F U hQ hU _ (t ⋙ (capU U (ent i)).ι)
      (capU_cons (ha _ (t.obj 0).property.1) (t.obj 0).property)
      (y (Fin.cons (α := fun _ => ι) (a _ (t.obj 0).property.1) i)))
    fun t ht => evL_zero hU _ _ _ _ ht

theorem desc (hU : ∀ α, Cosieve (U α)) (n : ℕ) : (Tm F U hQ n).Ex := by
  have hc : ∀ T : C, ∀ h : ∃ b, U b T, ∃ b, U b T := fun _ h => h
  choose a ha using hc
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU _ i _ _).trans ?_
    refine Eq.trans ?_ (map_zero (evL F U hQ hU _ _ _)).symm
    rw [Fin.sum_univ_two]
    change (-1 : ℤ) ^ 0 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x +
      (-1 : ℤ) ^ 1 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x = 0
    simp
  · rw [one_smul]
    refine M_ext hU fun t => ?_
    have hb := ha _ (t.obj 0).property.1
    have h1 := congrArg (evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const hb))
      (congrFun hx fun _ => a _ (t.obj 0).property.1)
    exact (h1.trans (map_zero _)).trans (map_zero _).symm
  · refine ⟨mkM ∅ (fun t => evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const (ha _ (t.obj 0).property.1))
      (y fun _ => a _ (t.obj 0).property.1)) fun t ht => evL_zero hU _ _ _ _ ht, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    exact (cocycle_zero hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
  · refine ⟨hh hU a ha y, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU (hh hU a ha y) i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
    rfl

theorem covDesc : CovDesc := fun _ _ _ _ _ _ _ _ _ _ hU n => desc hU n

end GlobalTheory.CompanionTheory.CovDescent
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w

namespace GlobalTheory.CompanionTheory.OneResProof

variable {R : Type} [CommRing R]

section Abstract

variable (D : DCx.{w} R)

def IsB (p : ℕ) : ∀ q, D.X p q → Prop
  | 0, y => y = 0
  | q + 1, y => ∃ u, D.dv p q u = y

def EZ (q : ℕ) : Prop := ∀ p (y : D.X (p + 1) q), D.dv (p + 1) q y = 0 → D.dh (p + 1) q y = 0 →
  ∃ x, D.dv p q x = 0 ∧ D.dh p q x = y

variable {D}

theorem eb (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u)
    {q : ℕ} (hZ : EZ D q) (p : ℕ) (u : D.X (p + 1) q) (hy : D.dh (p + 1) (q + 1) (D.dv (p + 1) q u) = 0) :
    ∃ t, D.dh p (q + 1) (D.dv p q t) = D.dv (p + 1) q u := by
  have h1 : D.dv (p + 2) q (D.dh (p + 1) q u) = 0 := by rw [← D.hv, hy]
  obtain ⟨w, hw, hw'⟩ := hZ (p + 1) (D.dh (p + 1) q u) h1 (D.hh _ _ _)
  obtain ⟨t, ht⟩ := hrow q p (u - w) (by rw [map_sub, hw', sub_self])
  exact ⟨t, by rw [D.hv, ht, map_sub, hw, sub_zero]⟩

theorem ez (hrow : ∀ q p (u : D.X (p + 1) q), D.dh (p + 1) q u = 0 → ∃ t, D.dh p q t = u) (a : ℕ)
    (hcol : ∀ p q, q ≠ a → ∀ y : D.X p q, D.dv p q y = 0 → IsB D p q y)
    (hA : ∀ p (y : D.X (p + 1) a), D.dv (p + 1) a y = 0 → D.dh (p + 1) a y = 0 →
      ∃ x, D.dv p a x = 0 ∧ IsB D (p + 1) a (y - D.dh p a x)) (q : ℕ) : EZ D q := by
  induction q with
  | zero =>
    intro p y hv hh
    by_cases h : 0 = a
    · subst h
      obtain ⟨x, hx, hb⟩ := hA p y hv hh
      exact ⟨x, hx, (sub_eq_zero.1 hb).symm⟩
    · exact ⟨0, map_zero _, by rw [map_zero]; exact (hcol _ 0 h y hv : y = 0).symm⟩
  | succ q ih =>
    intro p y hv hh
    by_cases h : q + 1 = a
    · subst h
      obtain ⟨x, hx, u, hu⟩ := hA p y hv hh
      obtain ⟨t, ht⟩ := eb hrow ih p u (by rw [hu, map_sub, hh, D.hh, sub_zero])
      exact ⟨x + D.dv p q t, by rw [map_add (f := _), hx, D.vv, add_zero], by rw [map_add (f := _), ht, hu]; abel⟩
    · obtain ⟨u, rfl⟩ : ∃ u, D.dv (p + 1) q u = y := hcol _ _ h y hv
      obtain ⟨t, ht⟩ := eb hrow ih p u hh
      exact ⟨D.dv p q t, D.vv _ _ _, ht⟩

end Abstract

variable {ι : Type} [DecidableEq ι]

theorem cech_nat {P Q : PM.{w} R ι} (φ : ∀ S, P.M S →ₗ[R] Q.M S)
    (nat : ∀ {S T : Finset ι} (h : S ⊆ T) x, φ T (P.res h x) = Q.res h (φ S x)) (p : ℕ) (x : P.cech.X p)
    (t : Fin (p + 2) → ι) : φ _ (P.cech.d p x t) = Q.cech.d p (fun i => φ _ (x i)) t := by
  rw [Cos.d_apply, Cos.d_apply]

  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact nat _ _

abbrev dcx (A : Sy.{w} R ι) : DCx.{w} R where
  X p q := (A.term q).cech.X p
  dh p q := (A.term q).cech.d p
  dv p q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  hh p q := (A.term q).cech.dd p
  vv p q x := funext fun i => (A.K (ent i)).dd q (x i)
  hv p q x := funext fun t => (cech_nat (P := A.term q) (Q := A.term (q + 1)) (fun S => (A.K S).d q)
    (fun h x => (A.res h).comm _ x) p x t).symm

abbrev zpm (A : Sy.{w} R ι) (a : ℕ) : PM.{w} R ι where
  M S := (A.K S).Z a
  res h := (A.res h).mapZ a
  res_id S h x := Subtype.ext (A.res_id S h a x.1)
  res_comp h h' x := Subtype.ext (A.res_comp h h' a x.1)

theorem isB_of (A : Sy.{w} R ι) (p q : ℕ) (y : (dcx A).X p q) (h : ∀ i, y i ∈ (A.K (ent i)).B q) : IsB (dcx A) p q y := by
  cases q with
  | zero => exact funext fun i => h i
  | succ q =>
    choose u hu using h
    exact ⟨u, funext hu⟩

theorem ent_nonempty {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty :=
  ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem hcol (A : Sy.{w} R ι) (a : ℕ) (hO : A.One a) (p q : ℕ) (hq : q ≠ a) (y : (dcx A).X p q)
    (hy : (dcx A).dv p q y = 0) : IsB (dcx A) p q y := by
  refine isB_of A p q y fun i => ?_
  have hs := hO (ent i) (ent_nonempty i) q hq
  have hi : (A.K (ent i)).d q (y i) = 0 := congrFun hy i
  have h0 : (Submodule.Quotient.mk ⟨y i, hi⟩ : (A.K (ent i)).H q) = 0 := Subsingleton.elim _ _
  have h2 : (⟨y i, hi⟩ : (A.K (ent i)).Z q) ∈ ((A.K (ent i)).B q).submoduleOf ((A.K (ent i)).Z q) :=
    (Submodule.Quotient.mk_eq_zero _).1 h0
  exact h2

theorem hrow (A : Sy.{w} R ι) (hD : A.Desc) (q p : ℕ) (u : (dcx A).X (p + 1) q) (hu : (dcx A).dh (p + 1) q u = 0) :
    ∃ t, (dcx A).dh p q t = u := by
  obtain ⟨t, ht⟩ := (hD q).2.2.2 p u hu
  exact ⟨t, ht.trans (one_smul _ _)⟩

theorem hA (A : Sy.{w} R ι) (a : ℕ)
    (hres : (A.coh a).cech.cx.ResUpTo 1 (LinearMap.ker ((A.coh a).cech.d 0)).subtype) (p : ℕ) (y : (dcx A).X (p + 1) a)
    (hv : (dcx A).dv (p + 1) a y = 0) (hh : (dcx A).dh (p + 1) a y = 0) :
    ∃ x, (dcx A).dv p a x = 0 ∧ IsB (dcx A) (p + 1) a (y - (dcx A).dh p a x) := by
  have natI : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      ((zpm A a).cech.d p z t).1 = (dcx A).dh p a (fun i => (z i).1) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.term a) (fun S => ((A.K S).Z a).subtype) (fun h x => rfl) p z t
  have natQ : ∀ (p : ℕ) (z : (zpm A a).cech.X p) (t : Fin (p + 2) → ι),
      Submodule.Quotient.mk ((zpm A a).cech.d p z t) =
        (A.coh a).cech.d p (fun i => Submodule.Quotient.mk (z i)) t := fun p z t =>
    cech_nat (P := zpm A a) (Q := A.coh a) (fun S => Submodule.mkQ _) (fun h x => rfl) p z t
  let y' : (zpm A a).cech.X (p + 1) := fun i => ⟨y i, congrFun hv i⟩
  have h0 : (zpm A a).cech.d (p + 1) y' = 0 := funext fun t => Subtype.ext ((natI (p + 1) y' t).trans (congrFun hh t))
  obtain ⟨c, hc⟩ := hres.2.2.2 p (fun i => Submodule.Quotient.mk (y' i)) (funext fun t => by
    have := natQ (p + 1) y' t
    rw [h0] at this
    exact this.symm)
  have hlift : ∀ i, ∃ z : (A.K (ent i)).Z a, Submodule.Quotient.mk z = c i := fun i =>
    Submodule.Quotient.mk_surjective _ (c i)
  choose z hz using hlift
  refine ⟨fun i => (z i).1, funext fun i => (z i).2, isB_of A _ _ _ fun t => ?_⟩
  have h1 : (Submodule.Quotient.mk (y' t - (zpm A a).cech.d p z t) : (A.K (ent t)).H a) = 0 := by
    rw [Submodule.Quotient.mk_sub, natQ, sub_eq_zero]
    have e : (fun i => Submodule.Quotient.mk (z i)) = c := funext hz
    rw [e]
    exact (congrFun (hc.trans (one_smul R _)) t).symm
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h1
  have e : (y - (dcx A).dh p a fun i => (z i).1) t = (y' t - (zpm A a).cech.d p z t).1 := by
    rw [Submodule.coe_sub, natI]
    rfl
  rw [e]
  exact h2

theorem high (A : Sy.{w} R ι) (a : ℕ) (hD : A.Desc) (hO : A.One a) (hZ : ∀ q, EZ (dcx A) q) (q : ℕ) (hq : q + 1 ≠ a) :
    Subsingleton ((A.K ∅).H (q + 1)) := by
  have hall : ∀ h : (A.K ∅).H (q + 1), h = 0 := by
    intro h
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [Submodule.Quotient.mk_eq_zero]
    change x ∈ (A.K ∅).B (q + 1)
    have hx' : (A.K ∅).d (q + 1) x = 0 := hx
    have hev : (dcx A).dv 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := funext fun i => by
      change (A.K (ent i)).d (q + 1) ((A.res _).f (q + 1) x) = 0
      rw [(A.res _).comm, hx', map_zero]
    obtain ⟨u, hu⟩ : ∃ u, (dcx A).dv 0 q u = (A.term (q + 1)).aug x := hcol A a hO 0 (q + 1) hq _ hev
    have hdh : (dcx A).dh 0 (q + 1) ((A.term (q + 1)).aug x) = 0 := (hD (q + 1)).1 x
    obtain ⟨v, hv, hv'⟩ := hZ q 0 ((dcx A).dh 0 q u) (by rw [← (dcx A).hv, hu, hdh]) ((dcx A).hh _ _ _)
    obtain ⟨s, hs⟩ := (hD q).2.2.1 (u - v) (by
      have : (dcx A).dh 0 q (u - v) = 0 := by rw [map_sub, hv', sub_self]
      exact this)
    rw [one_smul] at hs
    have h1 : (A.term (q + 1)).aug ((A.K ∅).d q s) = (A.term (q + 1)).aug x := by
      have e : (dcx A).dv 0 q ((A.term q).aug s) = (A.term (q + 1)).aug ((A.K ∅).d q s) :=
        funext fun i => (A.res _).comm q s
      rw [← e, hs, map_sub, hv, sub_zero, hu]
    have h2 := (hD (q + 1)).2.1 ((A.K ∅).d q s - x) (by rw [map_sub, h1, sub_self])
    rw [one_smul, sub_eq_zero] at h2
    exact ⟨s, h2⟩
  exact ⟨fun h₁ h₂ => by rw [hall h₁, hall h₂]⟩

theorem oneRes_of_oneLow : OneLow → OneRes := by
  intro hL R _ ι _ A a hD hO hres
  obtain ⟨hlow, hinj, hex⟩ := hL R ι A a hD hO
  have hZ : ∀ q, EZ (dcx A) q := ez (hrow A hD) a (hcol A a hO) (hA A a hres)
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hj with h | h
    · exact hlow j h
    · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      exact high A a hD hO hZ q hj
  · unfold PM.Ex Cx.ResUpTo
    refine ⟨fun x => (hex _).2 ⟨x, rfl⟩, fun x hx => ?_, fun y hy => ?_, hres.2.2.2⟩
    · rw [one_smul]
      exact hinj (hx.trans (map_zero _).symm)
    · obtain ⟨x, rfl⟩ := (hex y).1 hy
      exact ⟨x, (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.OneResProof

end
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem mirChar_eq_thetaA_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : GlobalTheory.BZMir.Fun.MirCharEq k := by
  intro ψ n
  have h : chrV k ψ n = chrA k ψ (Pi.single (Fin.last n) 1) := by
    ext v
    simp [chrV, chrA]
  rw [mirChar, thetaA, h]

end GlobalTheory.CompanionTheory.BZMir
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k]

theorem thetaA_eq_of_unip (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (x : MirUin k n)
    (w : Multiplicative (Fin n → k))
    (hx : ((x : Mir k n) : GL (Fin (n + 1)) k) = unip k n w) :
    thetaA k ψ a x = Circle.toUnits (ψ (a ⬝ᵥ w.toAdd)) := by
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hx
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) x)).toAdd)) = _
  rw [key]

theorem thetaConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : ThetaConj k := by
  intro ψ n a m u
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  have e : glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ =
      unip k n (Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v.toAdd)) := by
    rw [hv', glEmb_mul_unip', mul_inv_cancel_right]
  have h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n := by
    show glEmb k n m * ((u : Mir k n) : GL (Fin (n + 1)) k) * (glEmb k n m)⁻¹ ∈ MirU k n
    rw [e]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  rw [thetaA_eq_of_unip ψ _ u v hv', thetaA_eq_of_unip ψ a ⟨_, h⟩ _ e]
  simp only [toAdd_ofAdd]
  rw [dotProduct_mulVec]

end GlobalTheory.CompanionTheory.BZMirabolic

end
end
