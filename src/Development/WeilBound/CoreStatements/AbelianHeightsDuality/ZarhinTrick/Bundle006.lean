module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle004
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem ker_memKL {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (l : A ⟶ B) [IsMonHom l] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) [IsCommMonObj ((Over.pullback s).obj A)]
    (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj A) (hx : x ≫ (Over.pullback s).map l = 1) :
    GlobalTheory.MemKL ((Over.pullback s).obj A) L x := by
  have hx0 : lam (cls L hL) (fst T ((Over.pullback s).obj A) ≫ x) (snd T ((Over.pullback s).obj A)) = 0 := by
    rw [lam_comm, lam_cL_pt s hD.isLB l L hL e, ← toBase_map, Category.assoc, hx, MonObj.comp_one, toBase_one]
    exact evc_one_right hD.isLB hD.zero _
  have hD' : (Out.translDiff ((Over.pullback s).obj A) L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T _) (snd T _)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = GlobalTheory.CechPic.pull (fst T ((Over.pullback s).obj A)).left
      (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T _).left ⁻¹ᵁ V).ι ≫ (fst T _).left) (fun z ↦ z.2) hc

end PositivityTheory.PrwZar.Z2
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem g4lift_prj {X G : Over S} (c : Fin 4 → (X ⟶ G)) (i : Fin 4) : fourfoldProductLift c ≫ prj G i = c i := by
  fin_cases i <;> simp [fourfoldProductLift, prj]

@[reassoc] theorem g4lift_prj' {X G : Over S} (c : Fin 4 → (X ⟶ G)) (i : Fin 4) : fourfoldProductLift c ≫ prj G i = c i :=
  g4lift_prj c i

theorem fourfold_product_ext {X G : Over S} {f f' : X ⟶ G4 G} (h : ∀ i, f ≫ prj G i = f' ≫ prj G i) : f = f' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [prj] at h0 h1 h2 h3
  refine CartesianMonoidalCategory.hom_ext _ _ h0 (CartesianMonoidalCategory.hom_ext _ _ ?_
    (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)) <;> simpa only [Category.assoc] using ‹_›

instance prj.isMonHom (G : Over S) [GrpObj G] (i : Fin 4) : IsMonHom (prj G i) := by
  fin_cases i <;> simp only [prj] <;> infer_instance

def precompMH {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' a b := MonObj.comp_mul f a b

theorem comp_zpow' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (k : ℤ) : f ≫ g ^ k = (f ≫ g) ^ k :=
  map_zpow (precompMH f) g k

theorem comp_inv' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) : f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
  map_inv (precompMH f) g

theorem comp_pow' {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (k : ℕ) : f ≫ g ^ k = (f ≫ g) ^ k :=
  map_pow (precompMH f) g k

def postcompMH {X G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] : (X ⟶ G) →* (X ⟶ H) where
  toFun g := g ≫ f
  map_one' := MonObj.one_comp f
  map_mul' a b := MonObj.mul_comp a b f

theorem pow_comp' {X G H : Over S} [GrpObj G] [GrpObj H] (g : X ⟶ G) (f : G ⟶ H) [IsMonHom f] (k : ℕ) :
    (g ^ k) ≫ f = (g ≫ f) ^ k :=
  map_pow (postcompMH f) g k

theorem comp_prod_zpow {X Y G : Over S} [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) (c : Fin 4 → (Y ⟶ G))
    (k : Fin 4 → ℤ) : f ≫ (∏ j, c j ^ k j) = ∏ j, (f ≫ c j) ^ k j := by
  simp [Fin.prod_univ_four, MonObj.comp_mul, comp_zpow']

theorem eMap'_comp_eMap (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) :
    eMap' mu α m ≫ eMap mu α m = 𝟙 (G4 (A ⊗ B)) ^ (2 * m) := by
  apply fourfold_product_ext
  intro i
  rw [Category.assoc, eMap, g4lift_prj]
  ext1
  · rw [Category.assoc, lift_fst, Category.assoc, pow_comp', Category.id_comp, MonObj.comp_mul, comp_inv',
      comp_prod_zpow]
    simp only [← Category.assoc, eMap', g4lift_prj, lift_fst, lift_snd]
    simp only [mul_inv_cancel_right]
  · rw [Category.assoc, lift_snd, Category.assoc, pow_comp', Category.id_comp, comp_pow', ← Category.assoc, eMap',
      g4lift_prj, lift_snd]

end PositivityTheory.PrwZar
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def pr8 (A : Over S) : Fin 8 → (G4 (A ⊗ A) ⟶ A)
  | 0 => prj (A ⊗ A) 0 ≫ fst A A
  | 1 => prj (A ⊗ A) 0 ≫ snd A A
  | 2 => prj (A ⊗ A) 1 ≫ fst A A
  | 3 => prj (A ⊗ A) 1 ≫ snd A A
  | 4 => prj (A ⊗ A) 2 ≫ fst A A
  | 5 => prj (A ⊗ A) 2 ≫ snd A A
  | 6 => prj (A ⊗ A) 3 ≫ fst A A
  | 7 => prj (A ⊗ A) 3 ≫ snd A A

def lim8 (A : Over S) : IsLimit (Fan.mk (G4 (A ⊗ A)) (pr8 A)) :=
  mkFanLimit _ (fun s => fourfoldProductLift ![lift (s.proj 0) (s.proj 1), lift (s.proj 2) (s.proj 3),
      lift (s.proj 4) (s.proj 5), lift (s.proj 6) (s.proj 7)])
    (fun s k => by fin_cases k <;> simp [pr8, fourfoldProductLift, prj])
    (fun s m hm => by
      have h0 : m ≫ pr8 A 0 = s.proj 0 := hm 0
      have h1 : m ≫ pr8 A 1 = s.proj 1 := hm 1
      have h2 : m ≫ pr8 A 2 = s.proj 2 := hm 2
      have h3 : m ≫ pr8 A 3 = s.proj 3 := hm 3
      have h4 : m ≫ pr8 A 4 = s.proj 4 := hm 4
      have h5 : m ≫ pr8 A 5 = s.proj 5 := hm 5
      have h6 : m ≫ pr8 A 6 = s.proj 6 := hm 6
      have h7 : m ≫ pr8 A 7 = s.proj 7 := hm 7
      simp only [pr8, prj, ← Category.assoc] at h0 h1 h2 h3 h4 h5 h6 h7
      refine CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
        (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
          (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
            (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_))) <;>
        simp [fourfoldProductLift, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7])

variable {T : Scheme.{0}} (s : T ⟶ S)

theorem isFinite_map_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : IsFinite ((Over.pullback s).map f).left) (hg : IsFinite ((Over.pullback s).map g).left) :
    IsFinite ((Over.pullback s).map (f ⊗ₘ g)).left := by
  set F := Over.pullback s
  have he : F.map (f ⊗ₘ g) =
      CartesianMonoidalCategory.prodComparison F X X' ≫ (F.map f ⊗ₘ F.map g) ≫
        inv (CartesianMonoidalCategory.prodComparison F Y Y') := by
    rw [← Category.assoc, ← CartesianMonoidalCategory.prodComparison_natural, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have ht : IsFinite (Over.Hom.left (F.map f ⊗ₘ F.map g)) :=
    GlobalTheory.TensorFinite.isFinite_tensorHom _ _ hf hg
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F X X') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F X X'
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F Y Y') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F Y Y'
  haveI : IsIso (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) :=
    (Over.forget T).map_isIso (CartesianMonoidalCategory.prodComparison F X X')
  haveI : IsIso (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    (Over.forget T).map_isIso (inv (CartesianMonoidalCategory.prodComparison F Y Y'))
  have h1 : IsFinite (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) := inferInstance
  have h2 : IsFinite (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    inferInstance
  rw [he, Over.comp_left, Over.comp_left]
  exact MorphismProperty.comp_mem @IsFinite _ _ h1 (MorphismProperty.comp_mem @IsFinite _ _ ht h2)

end PositivityTheory.PrwZar.XB
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]


omit [GrpObj A] [GrpObj B] in
theorem pull_zcPair {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y Z : Over S} (w : Z ⟶ Y) (u u' : Y ⟶ G4 (A ⊗ B)) :
    pull w.left (zcPair hP lm mu α u u') = zcPair hP lm mu α (w ≫ u) (w ≫ u') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zcPair, map_add (f := _), map_sum, map_nsmul, map_zsmul, pull_evc, Category.assoc]

section Pieces

noncomputable local instance (priority := high) grpObjPairingPullback {S T : Scheme.{0}} (f : T ⟶ S)
    (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

noncomputable local instance (priority := high) overHomOfNatOne {S : Scheme.{0}} {Y G : Over S} [MonObj G] :
    OfNat (Y ⟶ G) 1 := ⟨toUnit Y ≫ η⟩

variable {P : LB (A ⊗ B).left} (hD : IsDual A B P) (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l]
  (mu : B ⟶ A) [IsMonHom mu] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left)
  (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
  {T : Over (Sp Ω)} (u u' : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B)))

include e in
theorem line_bundle_pairing_zeroth (i : Fin 4) :
    lam (pull (phiL mu s (0, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ fst A B) (T := T)
  show lam (pull (pA s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pA s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pA, toBase_map, Category.assoc]

include e hD' in
theorem line_bundle_pairing_first [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (1, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ fst A B) (toBase _ s u' ≫ prj _ i ≫ fst A B ≫ l) := by
  have hm0 := map_mul_pt s (prj (A ⊗ B) i ≫ fst A B) u u'
  have hm : (u * u') ≫ (pA (B := B) s i)⁻¹ = u ≫ (pA s i)⁻¹ * u' ≫ (pA s i)⁻¹ := by
    rw [GrpObj.comp_inv, GrpObj.comp_inv, GrpObj.comp_inv]
    show ((u * u') ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B))⁻¹ = _
    rw [hm0, mul_inv]
    rfl
  have h1 : (1 : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) ≫ (pA (B := B) s i)⁻¹ = 1 := by
    rw [GrpObj.comp_inv]
    show ((1 : T ⟶ _) ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B))⁻¹ = 1
    rw [map_one_pt, inv_one]
  show lam (pull ((pA (B := B) s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_pt ((pA s i)⁻¹) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e,
    GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pA, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include e in
theorem line_bundle_pairing_second (i : Fin 4) :
    lam (pull (phiL mu s (2, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  have hm := map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u'
  have h1 := map_one_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) (T := T)
  show lam (pull (pM mu s i).left (cls L hL)) u u' = _
  rw [lam_pull_pt (pM mu s i) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e]
  simp only [pM, toBase_map, Category.assoc]

include e hD' in
theorem line_bundle_pairing_third [IsCommMonObj A] (i : Fin 4) :
    lam (pull (phiL mu s (3, i)) (cls L hL)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ i ≫ snd A B ≫ mu) (toBase _ s u' ≫ prj _ i ≫ snd A B ≫ mu ≫ l) := by
  have hm0 := map_mul_pt s (prj (A ⊗ B) i ≫ snd A B ≫ mu) u u'
  have hm : (u * u') ≫ (pM mu s i)⁻¹ = u ≫ (pM mu s i)⁻¹ * u' ≫ (pM mu s i)⁻¹ := by
    rw [GrpObj.comp_inv, GrpObj.comp_inv, GrpObj.comp_inv]
    show ((u * u') ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu))⁻¹ = _
    rw [hm0, mul_inv]
    rfl
  have h1 : (1 : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) ≫ (pM mu s i)⁻¹ = 1 := by
    rw [GrpObj.comp_inv]
    show ((1 : T ⟶ _) ≫ (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu))⁻¹ = 1
    rw [map_one_pt, inv_one]
  show lam (pull ((pM mu s i)⁻¹).left (cls L hL)) u u' = _
  rw [lam_pull_pt ((pM mu s i)⁻¹) _ u u' hm h1, lam_cL_pt s hD.isLB l L hL e,
    GrpObj.comp_inv, GrpObj.comp_inv, toBase_inv, toBase_inv, GrpObj.inv_comp]
  simp only [pM, toBase_map, Category.assoc]
  exact evc_inv_inv hD hD' _ _

include hD hD' in
theorem evc_lam_key {Y : Over S} (a a' : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB (a * a') (b * b') - evc hD.isLB a b - evc hD.isLB a' b' + evc hD.isLB (1 : Y ⟶ A) (1 : Y ⟶ B) =
      evc hD.isLB a b' + evc hD.isLB a' b := by
  rw [evc_mul_left hD, evc_mul_right hD hD', evc_mul_right hD hD',
    IsAdditive.evc_one hD.isLB hD.additive]
  abel

private theorem pull_pull_phiP_eq_evc (ij : Fin 4 × Fin 4) (v : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) :
    pull v.left (pull (phiP s ij) (cls P hD.isLB)) =
      evc hD.isLB (toBase _ s v ≫ prj _ ij.1 ≫ fst A B) (toBase _ s v ≫ prj _ ij.2 ≫ snd A B) := by
  have hv := toBase_comp s (G4 (A ⊗ B)) v (𝟙 _)
  rw [Category.comp_id] at hv
  rw [evc, ← pull_comp, hv]
  congr 2
  simp only [phiP, ← comp_lift, Over.comp_left]
  rfl

include hD' in
theorem lam_phiP (ij : Fin 4 × Fin 4) :
    lam (pull (phiP s ij) (cls P hD.isLB)) u u' =
      evc hD.isLB (toBase _ s u ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u' ≫ prj _ ij.2 ≫ snd A B) +
        evc hD.isLB (toBase _ s u' ≫ prj _ ij.1 ≫ fst A B) (toBase _ s u ≫ prj _ ij.2 ≫ snd A B) := by
  simp only [GlobalTheory.CechPic.lam, pull_pull_phiP_eq_evc hD, toBase_mul, toBase_one, MonObj.mul_comp, MonObj.one_comp]
  exact evc_lam_key hD hD' _ _ _ _

end Pieces

end PositivityTheory.PrwZar
end
end
