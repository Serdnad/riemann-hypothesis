module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfLiftTranslationFiniteIndexLattices
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle907
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.UpperTransvection

theorem upper_mem_closure (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R)
    (hc : ∀ a b, b ≤ a → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  set S := Submonoid.closure
      {M : Matrix (Fin N) (Fin N) R | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}
  suffices key : ∀ n : ℕ, ∀ c : Matrix (Fin N) (Fin N) R, (∀ a b, b ≤ a → c a b = 0) →
      (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0).card ≤ n → 1 + c ∈ S from
    key _ c hc le_rfl
  intro n
  induction n with
  | zero =>
    intro c _ hcard
    have hc0 : c = 0 := by
      ext i j
      by_contra h
      have : (i, j) ∈ (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) := by
        simpa using h
      rw [Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard] at this
    subst hc0
    simpa using S.one_mem
  | succ n ih =>
    intro c hc hcard
    set T := (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) with hT
    rcases T.eq_empty_or_nonempty with hE | hne
    · exact ih c hc (by rw [← hT, hE]; simp)
    obtain ⟨p, hpT, hpmin⟩ := Finset.exists_min_image T (fun p => p.1) hne
    obtain ⟨a, b⟩ := p
    have hab : c a b ≠ 0 := by simpa [hT] using hpT
    have hlt : a < b := by
      by_contra h
      exact hab (hc a b (not_lt.mp h))

    have hcol : ∀ i, c i a = 0 := by
      intro i
      by_contra h
      have hi : (i, a) ∈ T := by simpa [hT] using h
      have h1 := hpmin _ hi
      have h2 : a ≤ i := h1
      exact h (hc i a h2)
    set r := c a b
    set c' := c - Matrix.single a b r with hc'
    have hc'_apply : ∀ i j, c' i j = if i = a ∧ j = b then 0 else c i j := by
      intro i j
      simp only [hc', Matrix.sub_apply, Matrix.single_apply]
      by_cases h : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h; simp [r]
      · have h' : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
        simp [h, h']
    have hc'up : ∀ i j, j ≤ i → c' i j = 0 := by
      intro i j hji
      rw [hc'_apply]; split_ifs
      · rfl
      · exact hc i j hji
    have hT' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0) ⊆ T.erase (a, b) := by
      intro q hq
      obtain ⟨i, j⟩ := q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [hc'_apply] at hq
      split_ifs at hq with h
      · exact absurd rfl hq
      · rw [Finset.mem_erase]
        refine ⟨?_, by simpa [hT] using hq⟩
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact h heq
    have hcard' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0).card ≤ n := by
      have := Finset.card_le_card hT'
      rw [Finset.card_erase_of_mem hpT] at this
      omega
    have hmem' : 1 + c' ∈ S := ih c' hc'up hcard'
    have hcolz : c' * Matrix.single a b r = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [hc'_apply]; split_ifs
        · simp
        · rw [hcol]; simp
      · simp
    have heq : 1 + c = (1 + c') * Matrix.transvection a b r := by
      rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, hcolz, add_zero, hc']
      abel
    rw [heq]
    refine S.mul_mem hmem' (Submonoid.subset_closure ⟨a, b, r, hlt.ne, rfl⟩)

end GlobalTheory.UpperTransvection
end

section

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pull {P Q Xa Xb Xa' Xb' : Scheme.{0}} {L : LB P} {M : LB Q} (hL : L.IsLB) (hM : M.IsLB)
    {a : Xa ⟶ P} {b : Xb ⟶ Q} {c : Xa ⟶ Xb} {a' : Xa' ⟶ P} {b' : Xb' ⟶ Q} {c' : Xa' ⟶ Xb'} (e : Xa' ⟶ Xa)
    (ha : a' = e ≫ a) (hc : c' ≫ b' = e ≫ c ≫ b) (H : LBIso (L.pull a) ((M.pull b).pull c)) :
    LBIso (L.pull a') ((M.pull b').pull c') := by
  have h1 : LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
    LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))
  have h2 : LBIso (L.pull a) (M.pull (c ≫ b)) :=
    LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) H h1
  exact LBIso.chartPull (chartPullSame L (fun _ : PUnit => a') (fun _ => a) (fun _ => 1) e fun _ => ha)
    (chartPullLinComb M b' (fun _ : PUnit => c') (fun _ => c ≫ b) (fun _ => 1) e fun _ => hc) h2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

def Wit {Z : Scheme.{0}} (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left) : Prop :=
  ∃ (A' B' : Over Z) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B'),
    IsGrpPullback A' A t φA ∧ IsGrpPullback B' B t φB ∧ IsMonHom Φ ∧ LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∃ e : A'.left ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = φA ∧ e ≫ pullback.snd _ _ = A'.hom ∧ e ≫ f = Φ.left ≫ φB

abbrev pmap {Z Z' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) : pullback A.hom (g ≫ t) ⟶ pullback A.hom t :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by rw [pullback.condition, Category.assoc])

variable {A B L M}

theorem wit_pull (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (h : Wit A B L M t f) (g : Z' ⟶ Z) : Wit A B L M (g ≫ t) (pmap A t g ≫ f) := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, hΦ, hI, e, e1, e2, e3⟩ := h
  refine ⟨(Over.pullback g).obj A', (Over.pullback g).obj B', inferInstance, inferInstance,
    pullback.fst _ _ ≫ φA, pullback.fst _ _ ≫ φB, (Over.pullback g).map Φ,
    (isGrpPullback_pullback A' g).comp hA, (isGrpPullback_pullback B' g).comp hB, inferInstance, ?_, ?_⟩
  · refine lbIso_pull hL hM (pullback.fst _ _) rfl ?_ hI
    rw [← Category.assoc, show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
      pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _, Category.assoc]
  · have hw : (pullback.fst A'.hom g ≫ φA) ≫ A.hom = pullback.snd A'.hom g ≫ g ≫ t := by
      rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc]
    have key : pullback.lift (pullback.fst A'.hom g ≫ φA) (pullback.snd A'.hom g) hw ≫ pmap A t g =
        pullback.fst A'.hom g ≫ e := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, e1]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, e2, pullback.condition]
    refine ⟨pullback.lift (pullback.fst _ _ ≫ φA) (pullback.snd _ _) hw, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    rw [← Category.assoc, key, Category.assoc, e3, ← Category.assoc, ← Category.assoc,
      show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
        pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _]


variable (A B L M) in
structure Pt (Z : Scheme.{0}) where

  t : Z ⟶ S

  f : pullback A.hom t ⟶ B.left
  wit : Wit A B L M t f

theorem Pt.ext' {Z : Scheme.{0}} {x y : Pt A B L M Z} (e : x.t = y.t)
    (h : pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition, e]) ≫ x.f = y.f) :
    x = y := by
  obtain ⟨t, f, w⟩ := x
  obtain ⟨t', f', w'⟩ := y
  dsimp only at e h
  revert h
  subst e
  intro h
  rw [pullback.lift_fst_snd, Category.id_comp] at h
  cases h
  rfl

theorem lift_pmap_id {Z : Scheme.{0}} (t : Z ⟶ S) (h : pullback.fst A.hom t ≫ A.hom = pullback.snd A.hom t ≫ 𝟙 Z ≫ t) :
    pullback.lift (pullback.fst A.hom t) (pullback.snd A.hom t) h ≫ pmap A t (𝟙 Z) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

theorem lift_pmap_comp {Z Z' Z'' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (h : pullback.fst A.hom (g' ≫ g ≫ t) ≫ A.hom = pullback.snd A.hom (g' ≫ g ≫ t) ≫ (g' ≫ g) ≫ t) :
    pullback.lift (pullback.fst A.hom (g' ≫ g ≫ t)) (pullback.snd A.hom (g' ≫ g ≫ t)) h ≫ pmap A t (g' ≫ g) =
      pmap A (g ≫ t) g' ≫ pmap A t g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc]

def Pt.map (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) : Pt A B L M Z' :=
  ⟨g ≫ x.t, pmap A x.t g ≫ x.f, wit_pull hL hM x.wit g⟩

theorem Pt.map_id (hL : L.IsLB) (hM : M.IsLB) {Z : Scheme.{0}} (x : Pt A B L M Z) : x.map hL hM (𝟙 Z) = x := by
  refine Pt.ext' (Category.id_comp _) ?_
  show _ ≫ pmap A x.t (𝟙 Z) ≫ x.f = x.f
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_id x.t _)).trans (Category.id_comp _))

theorem Pt.map_comp (hL : L.IsLB) (hM : M.IsLB) {Z Z' Z'' : Scheme.{0}} (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (x : Pt A B L M Z) : x.map hL hM (g' ≫ g) = (x.map hL hM g).map hL hM g' := by
  refine Pt.ext' (Category.assoc _ _ _) ?_
  show _ ≫ pmap A x.t (g' ≫ g) ≫ x.f = pmap A (g ≫ x.t) g' ≫ pmap A x.t g ≫ x.f
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_comp x.t g g' _)).trans
    (Category.assoc _ _ _))


variable (A B L M) in
def homFun (hL : L.IsLB) (hM : M.IsLB) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt A B L M Z.unop
  map g := TypeCat.ofHom (Pt.map hL hM g.unop)
  map_id Z := by
    ext x
    exact Pt.map_id hL hM x
  map_comp g g' := by
    ext x
    exact Pt.map_comp hL hM _ _ x


variable (A B L M) in
def homProj (hL : L.IsLB) (hM : M.IsLB) : homFun A B L M hL hM ⟶ yoneda.obj S where
  app Z := TypeCat.ofHom fun x => x.t

@[simp] theorem Pt.map_t (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) :
    (x.map hL hM g).t = g ≫ x.t := rfl

def Pt.ofData {Z : Scheme.{0}} (t : Z ⟶ S) (A' B' : Over Z) [GrpObj A'] [GrpObj B'] (φA : A'.left ⟶ A.left)
    (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B') (hA : IsGrpPullback A' A t φA) (hB : IsGrpPullback B' B t φB)
    (hΦ : IsMonHom Φ) (hI : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)) : Pt A B L M Z :=
  ⟨t, hA.1.isoPullback.inv ≫ Φ.left ≫ φB, A', B', inferInstance, inferInstance, φA, φB, Φ, hA, hB, hΦ, hI,
    hA.1.isoPullback.hom, by simp, by simp, by simp⟩

end GlobalTheory.EndLoc.HomGlue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 TopologicalSpace

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RelAmpleFixed

theorem veryAmpleAt_baseChange : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] [IsCommMonObj B] (M : LB B.left),
    IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ k : ℕ, 1 ≤ k ∧ ∀ (R' : Type) [CommRing R'] (φ : Rg →+* R')
      (B' : Over (Sp R')) [GrpObj B'] (φB : B'.left ⟶ B.left), IsGrpPullback B' B (spMap φ) φB →
      Out.VeryAmpleAt B' (M.pull φB) k := by
  intro Rg _ B _ _ L _ hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  refine ⟨N, hN, fun R' _ fr B' _ φ hg => ?_⟩
  have h : IsPullback φ B'.hom B.hom (spMap fr) := hg.1
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  obtain ⟨w, hw'⟩ := PolBaseChange.lbIso_refl hL'
  have hw := (isGen_iff w).1 hw'
  intro U' hU'
  have le : U' ≤ (spMap fr) ⁻¹ᵁ (⊤ : (Sp Rg).Opens) := fun y _ => trivial
  have le' : B'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (B.hom ⁻¹ᵁ ⊤) := fun y _ => trivial
  let ψ := φ.resLE (B.hom ⁻¹ᵁ ⊤) (B'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (B.hom ⁻¹ᵁ ⊤).ι = (B'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (B'.hom ∣_ U') (B.hom ∣_ ⊤) ((spMap fr).resLE ⊤ U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict B.hom ⊤).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict B'.hom U').flip.paste_horiz h
    · rw [← cancel_mono (⊤ : (Sp Rg).Opens).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w,
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine (⊤ : (Sp Rg).Opens) := isAffineOpen_top _
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1)
  have hP' := linComb_isLB (L.pull φ) hL' (K := Fin N) (fun _ => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ y).trans
      (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver B L ⊤ N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map (((spMap fr).resLE ⊤ U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.RelAmpleFixed
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbBaseChange

theorem isAbelianScheme_and_relDim_of_isGrpPullback : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left) (g : ℕ), IsGrpPullback A' A (spMap f) φ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  intro R R' _ _ f A _ A' _ φ g h hA hg
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  exact ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg⟩

end GlobalTheory.AbBaseChange
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_grpObj_isGrpPullback_of_isPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s' : Over (Sp R')), IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ ∧ (IsAbelianScheme A → IsAbelianScheme (Over.mk s' : Over (Sp R'))) ∧ ∀ g, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g s' := by
  intro R R' _ _ σ A _ X' s' φ h
  letI : (Over.pullback (spMap σ)).Monoidal :=
    (Over.instBraidedPullback (f := spMap σ)).toMonoidal
  letI : GrpObj ((Over.pullback (spMap σ)).obj A) := Functor.grpObjObj (F := Over.pullback (spMap σ))
  let e : Over.mk s' ≅ (Over.pullback (spMap σ)).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  letI I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (spMap σ))).congr (Category.id_comp _)
      (by simp [e])
  exact ⟨I, hP, fun hA => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hP,
    fun g hg => (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg⟩

end GlobalTheory.AbCoh
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isAffineHom_of_lift_translation_finiteIndex_lattices : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (B : Over (Sp ℂ)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB A.left) (L' : LB B.left) (u : HolUnif A L g) (u' : HolUnif B L' g) (a : Fin g → ℂ) (N : ℕ),
    0 < N → u.Λ ≤ u'.Λ → (∀ x ∈ u'.Λ, N • x ∈ u.Λ) →
    ∀ ψ : A.left ⟶ B.left, ψ ≫ B.hom = A.hom → (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) → IsAffineHom ψ := by
  first | exact @GlobalTheory.LiftAffine.isAffineHom_of_lift | exact GlobalTheory.LiftAffine.isAffineHom_of_lift | (intros; apply GlobalTheory.LiftAffine.isAffineHom_of_lift <;> assumption)
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_shift_semicharacters_nested_lattices : ∀ (g : ℕ) (Λ Λ₁ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (χ₁ : Λ₁ → ℂ)
    (h : Λ ≤ Λ₁), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ l, ‖χ l‖ = 1) → (∀ l, ‖χ₁ l‖ = 1) →
    (∀ l m : Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    (∀ l m : Λ₁, χ₁ (l + m) = χ₁ l * χ₁ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    ∃ a : Fin g → ℂ, ∀ l : Λ,
      χ l = χ₁ (Submodule.inclusion h l) * Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) := by
  first | exact @GlobalTheory.SemicharShift.exists_shift_of_semichar | exact GlobalTheory.SemicharShift.exists_shift_of_semichar | (intros; apply GlobalTheory.SemicharShift.exists_shift_of_semichar <;> assumption)
end
end
