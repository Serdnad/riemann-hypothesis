module

public import Development.EtaleCohomology.EtaleSheaves.Bundle050
public import Development.EtaleCohomology.EtaleSheaves.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.StepSPf

namespace LateralTheory.E.ChasePf

theorem pp_comp {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {h : A ⟶ C} (hfg : f ≫ g = h) (y : H R (sch.obj C) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map h) F n y := by
  rw [← pull_comp, ← Functor.map_comp, hfg]

theorem pp_id {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A : Scheme.{0}} {f : A ⟶ A} (hf : f = 𝟙 A)
    (y : H R (sch.obj A) F n) : pull R (sch.map f) F n y = y := by
  rw [hf, CategoryTheory.Functor.map_id, pull_id]

def psi {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) : pullback A.ι B.ι ≅ C.toScheme :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst A.ι B.ι ≫ A.ι) C.ι (by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hC]; rfl)

@[reassoc (attr := simp)]
theorem psi_hom_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).hom ≫ C.ι = pullback.fst A.ι B.ι ≫ A.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem psi_inv_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.fst A.ι B.ι ≫ A.ι = C.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc (attr := simp)]
theorem psi_inv_snd {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.snd A.ι B.ι ≫ B.ι = C.ι := by
  rw [← pullback.condition, psi_inv_fst]

theorem cover2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) (hAB : A ⊔ B = ⊤) :
    Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ A)).ι ∪ Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ B)).ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  refine Set.eq_univ_of_forall fun y => ?_
  have : ψ.base (φ.base y) ∈ A ⊔ B := by rw [hAB]; trivial
  simpa using this

theorem inf2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) :
    φ ⁻¹ᵁ (ψ ⁻¹ᵁ (A ⊓ B)) = φ ⁻¹ᵁ (ψ ⁻¹ᵁ A) ⊓ φ ⁻¹ᵁ (ψ ⁻¹ᵁ B) := by
  ext; simp

section
variable {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens)

abbrev rL {k : J} (f : k ⟶ j0) : (c.π.app j0 ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, c.w])

abbrev rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    (D.map f' ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map f' ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, h])

theorem rL_rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    rL D c j0 W f' ≫ rT D j0 W g f f' h = rL D c j0 W f := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp [rL, rT, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

end

theorem pp3' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' C' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g' ≫ k') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n (pull R (sch.map k') F n y)) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp3 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {l : A ⟶ E} (h : f ≫ g ≫ k = l) (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) = pull R (sch.map l) F n y := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp2' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp32 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp24 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' C' E' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E'} {l' : E' ⟶ E} (h : f ≫ g = f' ≫ g' ≫ k' ≫ l')
    (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n
      (pull R (sch.map k') F n (pull R (sch.map l') F n y))) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem Chase_of : DiagramChase₂ := by
  intro hH hmv q J _ _ D c hc ha hcs hqs hu j0 X e U V hUV pU pV pW n i
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  intro x
  obtain ⟨δ, hex, hnat⟩ := hmv hH (ZMod q) (tw q i)
  have cov : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι ∪ Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι = Set.univ :=
    fun φ => cover2 φ e.hom U V hUV
  have hinf : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      φ ⁻¹ᵁ (e.hom ⁻¹ᵁ (U ⊓ V)) = φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U) ⊓ φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V) :=
    fun φ => inf2 φ e.hom U V

  obtain ⟨k1, f1, a1, ha1⟩ := (pU (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x)
  obtain ⟨k2, f2, b1, hb1⟩ := (pV (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x)
  obtain ⟨k3, g1, g2, hg⟩ := IsCofiltered.cospan f1 f2

  obtain ⟨a2, ha2d⟩ : ∃ a2, a2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g1 f1 (g1 ≫ f1) rfl)) (tw q i) (m + 1) a1 :=
    ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b2, b2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g2 f2 (g1 ≫ f1) hg.symm)) (tw q i) (m + 1) b1 :=
    ⟨_, rfl⟩
  have ha2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1))) (tw q i) (m + 1) a2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x := by
    rw [ha2d, pp_comp (rL_rT D c j0 _ g1 f1 _ rfl)]; exact ha1
  have hb2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1))) (tw q i) (m + 1) b2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x := by
    rw [hb2d, pp_comp (rL_rT D c j0 _ g2 f2 _ hg.symm)]; exact hb1

  obtain ⟨dC, hdC⟩ : ∃ dC, dC = pull _ (sch.map (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv) (tw q i) (m + 1)
      (pull _ (sch.map (pullback.fst _ _)) _ _ a2 - pull _ (sch.map (pullback.snd _ _)) _ _ b2) := ⟨_, rfl⟩
  have hd : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) (g1 ≫ f1))) (tw q i) (m + 1) dC = 0 := by
    rw [hdC, map_sub, map_sub,
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.fst _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1)) (by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
        all_goals simp [← Category.assoc, psi_inv_fst, pullback.condition]),
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.snd _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1)) (by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
        all_goals simp [← Category.assoc, psi_inv_fst, pullback.condition]),
      ha2, hb2, pp3 (psi_inv_fst _ _ _ _), pp3 (psi_inv_snd _ _ _ _), sub_self]
  obtain ⟨k4, g4, hk4⟩ := (pW (m + 1) i).2 k3 (g1 ≫ f1) dC hd

  obtain ⟨a3, ha3d⟩ : ∃ a3, a3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) a2 := ⟨_, rfl⟩
  obtain ⟨b3, hb3d⟩ : ∃ b3, b3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) b2 := ⟨_, rfl⟩
  have hab : pull _ (sch.map (pullback.fst _ _)) _ _ a3 = pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
      (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 := by
    have key : pull _ (sch.map (pullback.fst _ _)) _ _ a3 - pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
        (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 =
        pull _ (sch.map (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom) _ _
          (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl)) _ _ dC) := by
      have E3 : (pullback.fst (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.fst (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
      have E4 : (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.snd (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
      rw [hdC, ha3d, hb3d]; simp only [map_sub]; rw [pp24 E3, pp24 E4]
    rw [hk4, map_zero] at key
    exact sub_eq_zero.mp key
  obtain ⟨xk, hxa, hxb⟩ := (hex (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (cov _) (m + 1)).1 a3 b3 hab

  obtain ⟨x', hx'⟩ : ∃ x' : Ht q (sch.obj c.pt) (m + 1) i, x' = x -
      (show Ht q (sch.obj c.pt) (m + 1) i from pull _ (sch.map (c.π.app k4)) (tw q i) (m + 1) xk) := ⟨_, rfl⟩
  have h1 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) (by simp [rL]), hxa, ha3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), ha2, sub_self]
  have h2 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) (by simp [rL]), hxb, hb3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), hb2, sub_self]
  obtain ⟨w, hw⟩ := ((hex (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) m).2.2 x').mp
    ⟨h1, h2⟩

  obtain ⟨k5, f5, w5, hw5⟩ := (pW m i).1 (pull _ (sch.map (psi _ _ _ (hinf (c.π.app j0))).inv) _ _ w)
  obtain ⟨k6, h4, h5, hh⟩ := IsCofiltered.cospan (g4 ≫ g1 ≫ f1) f5
  obtain ⟨w6, hw6⟩ : ∃ w6, w6 = pull _ (sch.map (psi _ _ _ (hinf (D.map (h4 ≫ g4 ≫ g1 ≫ f1)))).hom) (tw q i) m
      (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) h5 f5 (h4 ≫ g4 ≫ g1 ≫ f1) hh.symm)) _ _ w5) := ⟨_, rfl⟩
  have hn := hnat (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) (cov _)
    (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6)
    (by simp [rL]) (by simp [rL]) m w6
  have hpb : pull _ (sch.map (pullback.map _ _ _ _ (rL D c j0 (e.hom ⁻¹ᵁ U) (h4 ≫ g4 ≫ g1 ≫ f1))
      (rL D c j0 (e.hom ⁻¹ᵁ V) (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6) (by simp [rL]) (by simp [rL]))) (tw q i) m w6 = w := by
    rw [hw6, pp32 (f' := (psi _ _ _ (hinf (c.π.app j0))).hom) (g' := rL D c j0 _ f5) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp only [Category.assoc, rT, rL, Scheme.Hom.resLE_comp_ι, psi_hom_fst_assoc]
      simp [Scheme.Hom.resLE_comp_ι_assoc, Cone.w]), hw5,
      pp_comp (Iso.hom_inv_id _), pp_id rfl]
  refine ⟨k6, δ _ _ m w6 + pull _ (sch.map (D.map h4)) _ _ xk, ?_⟩
  rw [map_add (f := _), ← hn, hpb, hw, pp_comp (c.w h4), hx', sub_add_cancel]

end LateralTheory.E.ChasePf
end
end

section

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.DescendPf

def Spread : Prop := ∀ (A O : CommRingCat.{0}) (f : A ⟶ O), IE f →
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C],
  ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (d : B ⟶ O) (C' : CommRingCat.{0}) (e : B ⟶ C') (c : C' →+* C),
    Et g ∧ Et e ∧ g ≫ d = f ∧
    IsPushout e d (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap O C))

theorem Descend_of (hS : Spread) : LateralTheory.E.ColimPf.Descend := by
  intro A O f hf C _ _ _
  obtain ⟨B, g, d, C', e, c, hg, he, hgd, hP⟩ := hS A O f hf C
  refine ⟨B, g, d, C', e, c, hg, he, hgd, ?_, ?_, ?_⟩
  · ext y
    have := congrArg (fun φ => φ.hom y) hP.w
    simpa using this
  · intro k hk
    have hw : e ≫ k = d ≫ 𝟙 O := by rw [hk, Category.comp_id]
    let s := hP.desc k (𝟙 O) hw
    have h1 : CommRingCat.ofHom c ≫ s = k := hP.inl_desc k (𝟙 O) hw
    have h2 : CommRingCat.ofHom (algebraMap O C) ≫ s = 𝟙 O := hP.inr_desc k (𝟙 O) hw
    refine ⟨{ s.hom with commutes' := fun r => ?_ }, ?_⟩
    · have := congrArg (fun φ => φ.hom r) h2
      change s.hom (algebraMap O C r) = (𝟙 O : O ⟶ O).hom r
      exact this
    · ext y
      have := congrArg (fun φ => φ.hom y) h1
      simpa using this
  · intro R _ α β h1 h2
    have := hP.hom_ext (W := CommRingCat.of R) (k := CommRingCat.ofHom α) (l := CommRingCat.ofHom β) ?_ ?_
    · exact congrArg CommRingCat.Hom.hom this
    · ext y
      exact DFunLike.congr_fun h2 y
    · ext y
      exact DFunLike.congr_fun h1 y

end LateralTheory.E.DescendPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf LateralTheory.E.StepKPf

namespace LateralTheory.E.RestrPf

theorem pull_zero {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (y : Ht q (sch.obj C) n i)
    (h : pull _ (sch.map b) _ _ y = 0) : pull _ (sch.map (a ≫ b)) _ _ y = 0 := by
  rw [Functor.map_comp, pull_comp, h, map_zero]

theorem Restr_of : Restr := by
  intro h q J _ _ D c hc ha hcs hqs hu j0 X e U hU pU
  have : ∀ {a b : J} (g : a ⟶ b), IsAffineHom (D.map g) := ha
  let W : (D.obj j0).Opens := e.hom ⁻¹ᵁ U
  have haff : ∀ {a b : Over j0} (g : a ⟶ b), IsAffineHom ((opensDiagram D j0 W).map g) := fun g => inferInstance
  have hcpt : ∀ a : Over j0, CompactSpace ((opensDiagram D j0 W).obj a) := fun a =>
    isCompact_iff_compactSpace.mp ((D.map a.hom).isCompact_preimage hU)
  have hqs' : ∀ a : Over j0, QuasiSeparatedSpace ((opensDiagram D j0 W).obj a) := fun a => by
    have := hqs a.left
    exact (D.map a.hom ⁻¹ᵁ W).isOpen.isOpenEmbedding_subtypeVal.quasiSeparatedSpace
  have hu' : ∀ a : Over j0, IsUnit (q : Γ((opensDiagram D j0 W).obj a, ⊤)) := fun a => by
    show IsUnit (q : Γ((D.map a.hom ⁻¹ᵁ W).toScheme, ⊤))
    simpa using (hu a.left).map (Scheme.Hom.appTop (Scheme.Opens.ι (D.map a.hom ⁻¹ᵁ W))).hom
  have hiso : Nonempty ((opensDiagram D j0 W).obj (Over.mk (𝟙 j0)) ≅ U.toScheme) := by
    refine ⟨(D.obj j0).isoOfEq ?_ ≪≫ asIso (e.hom ∣_ U)⟩
    simp [W]
  have P := pU q (opensDiagram D j0 W) (opensCone D c j0 W) (isLimitOpensCone D c hc j0 W) haff hcpt hqs' hu'
    (Over.mk (𝟙 j0)) hiso
  intro n i
  obtain ⟨P1, P2⟩ := P n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j', y, hy⟩ := P1 x
    exact ⟨j'.left, j'.hom, y, hy⟩
  · obtain ⟨k', g', hg'⟩ := P2 (Over.mk f) y hy
    refine ⟨k'.left, g'.left, ?_⟩
    have hle : lv D e U (g'.left ≫ f) ≤ D.map k'.hom ⁻¹ᵁ W := by
      rw [← Over.w g']; exact le_rfl
    let ι0 : (lv D e U (g'.left ≫ f)).toScheme ⟶ (opensDiagram D j0 W).obj k' := (D.obj k'.left).homOfLE hle
    have heq : rD D e U f g'.left = ι0 ≫ (opensDiagram D j0 W).map g' := by
      apply (cancel_mono (lv D e U f).ι).mp
      have e1 : (opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι =
          (D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left := Scheme.Hom.resLE_comp_ι _ _
      have e2 : ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι = (lv D e U (g'.left ≫ f)).ι := Scheme.homOfLE_ι _ _
      calc rD D e U f g'.left ≫ (lv D e U f).ι = (lv D e U (g'.left ≫ f)).ι ≫ D.map g'.left :=
            Scheme.Hom.resLE_comp_ι _ _
        _ = (ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι) ≫ D.map g'.left := by rw [e2]
        _ = ι0 ≫ ((D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left) := Category.assoc _ _ _
        _ = ι0 ≫ ((opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι) :=
            congrArg (fun t => ι0 ≫ t) e1.symm
        _ = (ι0 ≫ (opensDiagram D j0 W).map g') ≫ (lv D e U f).ι := (Category.assoc _ _ _).symm
    rw [heq]; exact pull_zero ι0 ((opensDiagram D j0 W).map g') y hg'

end LateralTheory.E.RestrPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces

namespace LateralTheory.E.FiltPf

namespace Tri

open Pretriangulated
universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]

def RelY (Y : ℤ → D) (n : ℤ) {A B : D} (g : A ⟶ B) : Prop :=
  Function.Surjective (fun x : B ⟶ Y (n - 1) => g ≫ x) ∧ Function.Injective (fun x : B ⟶ Y n => g ≫ x)

omit [HasZeroObject D] [HasShift D ℤ] [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] in
theorem inj_iff {A B X : D} (g : A ⟶ B) :
    Function.Injective (fun x : B ⟶ X => g ≫ x) ↔ ∀ x : B ⟶ X, g ≫ x = 0 → x = 0 := by
  constructor
  · intro h x hx; exact h (by simpa using hx)
  · intro h x y hxy
    have := h (x - y) (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.2 hxy)
    exact sub_eq_zero.1 this

theorem relY_mid (T₁ T₂ : Triangle D) (h₁ : T₁ ∈ distTriang D) (h₂ : T₂ ∈ distTriang D) (φ : T₁ ⟶ T₂)
    (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧) (n : ℤ)
    (ha : RelY Y n φ.hom₁) (hc : RelY Y n φ.hom₃) : RelY Y n φ.hom₂ := by
  have hci := (inj_iff _).1 hc.2
  have hai := (inj_iff _).1 ha.2
  refine ⟨fun x => ?_, (inj_iff _).2 fun d hd => ?_⟩
  · obtain ⟨y, hy⟩ := ha.1 (T₁.mor₁ ≫ x)
    simp only at hy
    have ho : T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y ≫ (e n).inv = 0 := by
      apply hci
      rw [← Category.assoc, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc, hy, Functor.map_comp_assoc,
        ← Category.assoc, comp_distTriang_mor_zero₃₁ T₁ h₁, zero_comp]
    have ho' : T₂.rotate.mor₂ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map y = 0 := by
      have := congrArg (· ≫ (e n).hom) ho
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] at this
      exact this
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ h₂) _ ho'
    obtain ⟨(z : T₂.obj₂ ⟶ Y (n - 1)), rfl⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective g
    have hyz : y = T₂.mor₁ ≫ (-z) := by
      apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
      rw [hg]
      simp only [Triangle.rotate_mor₃, Functor.map_comp, Functor.map_neg, Preadditive.comp_neg]
      exact Preadditive.neg_comp _ _
    have hw : T₁.mor₁ ≫ (x - φ.hom₂ ≫ (-z)) = 0 := by
      rw [Preadditive.comp_sub, ← hy, hyz, ← Category.assoc, ← φ.comm₁, Category.assoc, sub_self]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ h₁ _ hw
    obtain ⟨w', hw'⟩ := hc.1 w
    simp only at hw'
    refine ⟨-z + T₂.mor₂ ≫ w', ?_⟩
    simp only
    rw [Preadditive.comp_add, ← Category.assoc, ← φ.comm₂, Category.assoc, hw', ← hw]
    abel
  · have h1 : T₂.mor₁ ≫ d = 0 := by
      apply hai
      rw [← Category.assoc, ← φ.comm₁, Category.assoc, hd, comp_zero]
    obtain ⟨h, rfl⟩ := Triangle.yoneda_exact₂ _ h₂ _ h1
    have h3 : T₁.mor₂ ≫ φ.hom₃ ≫ h = 0 := by
      rw [← Category.assoc, φ.comm₂, Category.assoc, hd]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ h₁ _ h3
    obtain ⟨k', hk'⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (k ≫ (e n).hom)
    obtain ⟨k'', hk''⟩ := ha.1 k'
    simp only at hk''
    have hm : h = T₂.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map k'' ≫ (e n).inv := by
      rw [← sub_eq_zero]
      apply hci
      rw [Preadditive.comp_sub, hk, ← Category.assoc φ.hom₃, ← φ.comm₃, Category.assoc, ← Functor.map_comp_assoc,
        hk'', hk', Category.assoc, Iso.hom_inv_id, Category.comp_id, sub_self]
    rw [hm, ← Category.assoc, comp_distTriang_mor_zero₂₃ _ h₂, zero_comp]

end Tri

section Bridge
open CochainComplex CochainComplex.HomComplex
variable (R : Type) [CommRing R]

abbrev Yres (F : Shv R) (m : ℤ) : HomotopyCategory (Shv R) (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦m⟧)

theorem pull_eq_comp {K L : Cx R} (f : K ⟶ L) (F : Shv R) (m : ℤ) :
    (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶ Yres R F m =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R f F m) ∘ (CohomologyClass.homAddEquiv.symm) := by
  funext g
  simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  congr 1
  exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm

theorem relK_iff {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) :
    RelK R F n f ↔ Tri.RelY (Yres R F) n ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map f) := by
  unfold Tri.RelY RelK
  rw [pull_eq_comp, pull_eq_comp, EquivLike.comp_surjective, EquivLike.surjective_comp,
    EquivLike.comp_injective, EquivLike.injective_comp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 (n - 1) (by omega), h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨fun m hm => ?_, h2⟩; obtain rfl : m = n - 1 := (by omega)
    exact h1

def yresIso (F : Shv R) (m : ℤ) : Yres R F m ≅ (Yres R F (m - 1))⟦(1 : ℤ)⟧ :=
  LateralTheory.E.E8.ExciseCut.ConeZeroPf.shIso R (res R F) m

end Bridge

def pieceC (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (K.X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (L.X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (f.f (-(p : ℤ)))

def Tower : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def TowerFin : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ) (P : ℕ),
  (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K.X i) ∧ IsZero (L.X i)) →
  (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f

def Trunc : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧
    ((∀ p : ℕ, RelK R F n (pieceC R f p)) → ∀ p : ℕ, RelK R F n (pieceC R f' p)) ∧
    (RelK R F n f' → RelK R F n f)

theorem tower_of (hB : TowerFin) (hT : Trunc) : Tower := by
  intro R _ F K L f n hz hp
  obtain ⟨P, K', L', f', hz', hpp, hback⟩ := hT R F f n hz
  exact hback (hB R F f' n P hz' (hpp hp))

theorem chains_X_isZero (R : Type) [CommRing R] (U : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj U).X i) := by
  change IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  have e : ComplexShape.embeddingDownNat.f j = -(j : ℤ) := rfl
  omega

end LateralTheory.E.FiltPf

open LateralTheory.E.FiltPf in
theorem LateralTheory.E.TruncationPieces.Filt_of_tower (hT : Tower) : LateralTheory.E.TruncationPieces.Filt := by
  intro R _ F U E u n h
  exact hT R F ((chains R).map u) n (fun i hi => ⟨chains_X_isZero R U i hi, chains_X_isZero R E i hi⟩) h

end
end
