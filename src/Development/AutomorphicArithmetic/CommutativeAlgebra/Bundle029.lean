module

public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingExistsUniqueAdditiveExact
public import Development.EtaleCohomology.EtaleSheaves.Bundle055
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle037
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle024
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Mathlib.Tactic.Polynomial.Basic
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem cast_zero' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht.cast hn hi (0 : Ht q E n i) = 0 := by
  subst hn hi
  rfl

private theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : Ht.cast hn hi x = 0) : x = 0 := by
  subst hn hi
  exact h

private theorem pull_cast' {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem inj_of_LH {q : ℕ} {N : ℕ} (hN : 1 ≤ N) {E X : Spc} (πX : X ⟶ E) (ξX : Ht q X 2 1)
    (hLH : LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j))
    {n i : ℤ} (a : Ht q E n i) (ha : pull _ πX _ _ a = 0) : a = 0 := by
  classical
  obtain ⟨hinj, -⟩ := hLH n i
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin N, (j0 : ℕ) = 0 := ⟨⟨0, hN⟩, rfl⟩
  have e1 : n = n - 2 * (((j0 : ℕ) : ℤ)) := by simp [hj0]
  have e2 : i = i - ((j0 : ℕ) : ℤ) := by simp [hj0]
  let a' : (j : Fin N) → Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ)) :=
    Pi.single (M := fun j : Fin N => Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))) j0 (a.cast e1 e2)
  have hp : ∀ j, pull _ πX _ _ (a' j) = 0 := by
    intro j
    by_cases hj : j = j0
    · subst hj
      simp only [a', Pi.single_eq_same]
      rw [pull_cast', ha, cast_zero']
    · simp only [a', Pi.single_eq_of_ne hj, map_zero]
  have h0 : a' = 0 := hinj (by simp [hp, cast_zero'])
  have h1 := congrFun h0 j0
  simp only [a', Pi.single_eq_same, Pi.zero_apply] at h1
  exact eq_zero_of_cast e1 e2 a h1

theorem UpperTheory.leray_hirsch_of_two_element_cover :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 1 ≤ N → ∀ {E X Y B W₁ W₂ B₁ B₂ : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
            (f₁ : W₁ ⟶ Y) (f₂ : W₂ ⟶ Y) (g₁ : B₁ ⟶ B) (g₂ : B₂ ⟶ B) (b₁ : B₁ ⟶ W₁) (b₂ : B₂ ⟶ W₂)
            (h₁ : g₁ ≫ β = b₁ ≫ f₁) (h₂ : g₂ ≫ β = b₂ ≫ f₂) (_ : p ≫ πX = β ≫ πY) (ξX : Ht q X 2 1),
            Inv q X → Cover2 (ZMod q) f₁ f₂ → Cover2 (ZMod q) g₁ g₂ →
            LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j) →
            (∀ i, Eqv _ (f₁ ≫ πY) (tw q i)) → (∀ i, Eqv _ (g₁ ≫ p) (tw q i)) → (∀ i, Eqv _ b₂ (tw q i)) →
            (∀ i, Eqv _ (pullback.map g₁ g₂ f₁ f₂ b₁ b₂ β h₁ h₂) (tw q i)) →
            ∀ (n i : ℤ) (x : Ht q Y n i), pull _ β _ _ x = 0 → x = 0 := by
  intro q _ N hN E X Y B W₁ W₂ B₁ B₂ πX πY p β f₁ f₂ g₁ g₂ b₁ b₂ h₁ h₂ hsq ξX hX hcW hcB hLH hW₁ hB₁ hb₂
    hmap n i x hx
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have MW := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) m).1 f₁ f₂ hcW
  have MB := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) m).1 g₁ g₂ hcB
  have nat := (UpperTheory.mayerVietorisConnecting_exists_unique_additive_exact (ZMod q) (tw q i) m).2 g₁ g₂ f₁ f₂ β b₁ b₂ h₁ h₂ hcB hcW
  have hA : pull _ f₁ _ _ x = 0 := by
    obtain ⟨e, he⟩ := (hW₁ i (m + 1)).2 (pull _ f₁ _ _ x)
    have key : (g₁ ≫ p) ≫ πX = b₁ ≫ (f₁ ≫ πY) := by
      rw [Category.assoc, hsq, ← Category.assoc, h₁, Category.assoc]
    have h0 : pull _ (g₁ ≫ p) _ _ (pull _ πX _ _ e) = 0 := by
      rw [← pull_comp, key, pull_comp, he, ← pull_comp, ← h₁, pull_comp, hx, map_zero]
    have h1 : pull _ πX _ _ e = 0 := (hB₁ i (m + 1)).1 (h0.trans (map_zero _).symm)
    have h2 : e = 0 := inj_of_LH hN πX ξX hLH e h1
    rw [← he, h2, map_zero]
  have hB : pull _ f₂ _ _ x = 0 := by
    apply (hb₂ i (m + 1)).1
    rw [map_zero, ← pull_comp, ← h₂, pull_comp, hx, map_zero]
  obtain ⟨c, hc⟩ := (MW.2.2.2.2.1 x).1 ⟨hA, hB⟩
  have hc' := nat c x hc
  rw [hx] at hc'
  obtain ⟨a, b, hab⟩ := (MB.2.2.2.1 _ _ hc').1 rfl
  obtain ⟨a₀, ha₀⟩ := (hB₁ i m).2 a
  have hfst : pull _ (pullback.fst g₁ g₂) _ _ a =
      pull _ (pullback.snd g₁ g₂) _ _ (pull _ g₂ _ _ (pull _ p _ _ a₀)) := by
    rw [← ha₀]
    simp only [← pull_comp]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨w, hw⟩ := (hb₂ i m).2 (pull _ g₂ _ _ (pull _ p _ _ a₀) - b)
  have hm : pullback.map g₁ g₂ f₁ f₂ b₁ b₂ β h₁ h₂ ≫ pullback.snd f₁ f₂ = pullback.snd g₁ g₂ ≫ b₂ :=
    pullback.lift_snd _ _ _
  have hcw : c = pull _ (pullback.snd f₁ f₂) _ _ w := by
    apply (hmap i m).1
    rw [hab, hfst, ← map_sub, ← hw, ← pull_comp, ← pull_comp, hm]
  exact (MW.2.2.2.1 c x hc).2 ⟨0, -w, by rw [hcw, map_zero, map_neg, zero_sub, neg_neg]⟩
end

section

open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsMultivariableHensel

namespace UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem closure_chart (i j : Fin 2) (hij : i ≠ j) :
    Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} = ⊤ := by
  have hiso : IsIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i)) := by
    rw [← Proj.basicOpenIsoAway_hom (grading ℤ 1) (MvPolynomial.X i) (X_mem i) one_pos]
    infer_instance
  have hsurj := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i))).2
  have hpoly : ∀ a : MvPolynomial (Fin (1 + 1)) ℤ,
      chartHom (A := ℤ) (n := 1) i a ∈ Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      rw [show (MvPolynomial.C c : MvPolynomial (Fin (1 + 1)) ℤ) = (c : MvPolynomial (Fin (1 + 1)) ℤ) from
        eq_intCast MvPolynomial.C c, map_intCast]
      exact intCast_mem _ c
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      by_cases hn : n = i
      · subst hn
        rw [chartHom_X_self]
        exact one_mem _
      · have hnj : n = j := by
          fin_cases n <;> fin_cases i <;> fin_cases j <;> simp_all
        subst hnj
        exact Subring.subset_closure rfl
  rw [eq_top_iff]
  intro s _
  obtain ⟨y, rfl⟩ := hsurj s
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem i) y
  have ha' : a ∈ grading ℤ 1 k := by simpa using ha
  convert hpoly a using 1
  exact (chartHom_of_mem i ha').symm

private theorem chartHom_eq_ratio (i j : Fin 2) :
    chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j) =
      ProjTwist.ratio (grading ℤ 1) (X_mem i) (X_mem j) := by
  rw [chartHom_of_mem i (X_mem j)]
  unfold ProjTwist.ratio
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk]

private theorem mul_res :
    resR (inf_le_left : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 0)
        (chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1)) *
      resR (inf_le_right : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 1)
        (chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0)) = 1 := by
  letI : CommRing (ringOn (projectiveSpace ℤ 1) (stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1)) :=
    inferInstanceAs (CommRing Γ(projectiveSpace ℤ 1, stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1))
  have h := ProjTwist.ratio_mul_ratio' (𝒜 := grading ℤ 1) (X_mem (A := ℤ) (n := 1) 0)
    (X_mem (A := ℤ) (n := 1) 1) (X_mem (A := ℤ) (n := 1) 0)
  rw [ProjTwist.ratio_self, map_one] at h
  rw [← chartHom_eq_ratio, ← chartHom_eq_ratio] at h
  change resR (inf_le_right : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 1)
      (chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0)) *
    resR (inf_le_left : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 0)
      (chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1)) = 1 at h
  exact (mul_comm _ _).trans h

end UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace UpperTheory.ProjectiveLineClosure in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem UpperTheory.projectiveLine_std_opens_basicOpen_generators :
    ∃ (τ : Γ(P1, stdOpen 0)) (σ : Γ(P1, stdOpen 1)),
        IsAffineOpen (stdOpen 0) ∧ IsAffineOpen (stdOpen 1) ∧
        Subring.closure {τ} = ⊤ ∧ Subring.closure {σ} = ⊤ ∧
        P1.basicOpen τ = stdOpen 0 ⊓ stdOpen 1 ∧ P1.basicOpen σ = stdOpen 0 ⊓ stdOpen 1 ∧
        P1.presheaf.map (homOfLE (inf_le_left : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 0)).op τ *
          P1.presheaf.map (homOfLE (inf_le_right : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 1)).op σ = 1 := by
  refine ⟨chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1),
    chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0),
    isAffineOpen_stdOpen (A := ℤ) (n := 1) 0, isAffineOpen_stdOpen (A := ℤ) (n := 1) 1,
    closure_chart 0 1 (by decide), closure_chart 1 0 (by decide),
    basicOpen_chartHom_X (A := ℤ) (n := 1) 0 1, ?_, ?_⟩
  · refine (basicOpen_chartHom_X (A := ℤ) (n := 1) 1 0).trans ?_
    exact inf_comm _ _
  · exact mul_res
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

theorem UpperTheory.descent_of_integral_descent_truncation :
    LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels → LateralTheory.E.t_E2Cut.Desc := by
  intro hT hH q i A _ _ hq P p hyp
  have neg : ∀ n : ℤ, n < 0 → ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A))) := by
    intro n hn X g
    refine ⟨fun m hm => ?_, fun x y _ => ?_⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1
        (sch.obj (pullback g (LateralTheory.E.t_E2Cut.cpt A))) m (by omega)
      exact fun y => ⟨0, Subsingleton.elim _ _⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj X) n hn
      exact Subsingleton.elim _ _
  let C : ℤ → Prop := fun n => ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      (∃ h : X ⟶ P, IsIntegralHom h ∧ g = h ≫ p) →
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A)))
  have step : ∀ n : ℤ, (∀ m, m < n → C m) → C n := by
    intro n ih X g hg
    obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨Y, k, hk, hks, hpb⟩ := hyp X h hh
    haveI := hk
    haveI := hks
    obtain ⟨U, E, u, a', a, hcomm, ha, ha', hall, h0⟩ :=
      UpperTheory.cohomology_base_change_integral_surjective_cech hH.b4 q i k (h ≫ p) (LateralTheory.E.t_E2Cut.cpt A)
        (LateralTheory.E.t_E2Cut.unit_of hq (h ≫ p))
    have hu : RelZS (ZMod q) (tw q i) n u := by
      refine hT (ZMod q) (tw q i) u n (fun p' m hm => ?_) ?_
      · obtain ⟨L, l, hl, hL⟩ := hall p'
        apply hL m
        haveI := hl
        haveI := hh
        exact ih m hm (l ≫ h ≫ p) ⟨l ≫ h, inferInstance, by simp [Category.assoc]⟩
      · apply h0 n
        exact ⟨fun m' _ => (hpb m').2, (hpb n).1⟩
    exact transfer (ZMod q) (tw q i) u _ a' a hcomm ha ha' n hu
  have all : ∀ n, C n := by
    have key : ∀ k : ℕ, ∀ n : ℤ, n < k → C n := by
      intro k
      induction k with
      | zero =>
        intro n hn X g _
        exact neg n (by exact_mod_cast hn) g
      | succ k ihk =>
        intro n hn
        by_cases hn' : n < k
        · exact ihk n hn'
        · exact step n (fun m hm => ihk m (by push_cast at hn ⊢; omega))
    intro n
    exact key (n.toNat + 1) n (by omega)
  have hp : ∃ h : P ⟶ P, IsIntegralHom h ∧ p = h ≫ p := ⟨𝟙 P, inferInstance, by simp⟩
  intro n
  exact ⟨(all n p hp).2, (all (n + 1) p hp).1 n rfl⟩
end
