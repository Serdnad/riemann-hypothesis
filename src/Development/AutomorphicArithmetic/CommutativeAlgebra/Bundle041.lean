module

public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle029
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle037
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow
namespace UpperTheory.ChaseS

variable {q : ℕ}

private theorem c_cc {E : Spc} {n i n' i' n'' i'' : ℤ} (a : n = n') (b : i = i') (c : n' = n'') (d : i' = i'')
    (x : Ht q E n i) : (x.cast a b).cast c d = x.cast (a.trans c) (b.trans d) := by
  subst a b c d
  rfl

private theorem c_zero {E : Spc} {n i n' i' : ℤ} (a : n = n') (b : i = i') :
    (0 : Ht q E n i).cast a b = 0 := by
  subst a b
  rfl

private theorem c_sum {E : Spc} {n i n' i' : ℤ} (a : n = n') (b : i = i') {ι : Type} (s : Finset ι)
    (f : ι → Ht q E n i) : (∑ j ∈ s, f j).cast a b = ∑ j ∈ s, (f j).cast a b := by
  subst a b
  rfl

private theorem pull_c {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem pull_u {X Y : Spc} (f : X ⟶ Y) {n m i j : ℤ} (a : Ht q Y n i) (b : Ht q Y m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a : Ht q X n i) (pull _ f _ _ b : Ht q X m j) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem cup_cl {E : Spc} {n m i j n' i' : ℤ} (hn : n = n') (hi : i = i') (a : Ht q E n i) (b : Ht q E m j) :
    cup q (a.cast hn hi) b = (cup q a b).cast (by rw [hn]) (by rw [hi]) := by
  subst hn hi
  rfl

private theorem cup_cr {E : Spc} {n m i j m' j' : ℤ} (hm : m = m') (hj : j = j') (a : Ht q E n i) (b : Ht q E m j) :
    cup q a (b.cast hm hj) = (cup q a b).cast (by rw [hm]) (by rw [hj]) := by
  subst hm hj
  rfl

variable [NeZero q]

private theorem cup_one_r {E : Spc} (hE : Inv q E) {n i : ℤ} (a : Ht q E n i) :
    cup q a (one q E) = a.cast (by ring) (by ring) := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q E a (one q E)]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  rw [(GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a, c_cc]

private theorem cup_pow_zero {E : Spc} (hE : Inv q E) (ξ : Ht q E 2 1) {k : ℕ} (hk : k = 0) {n i : ℤ} (a : Ht q E n i) :
    cup q a (cpow q ξ k) = a.cast (by subst hk; simp) (by subst hk; simp) := by
  subst hk
  rw [cpow_zero, cup_cr, cup_one_r hE, c_cc]

private theorem cpow_one' {E : Spc} (hE : Inv q E) (ξ : Ht q E 2 1) :
    cpow q ξ 1 = ξ.cast (by simp) (by simp) := by
  refine (cpow_succ q ξ 0).trans ?_
  rw [cpow_zero, cup_cl, (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE ξ, c_cc, c_cc]

private theorem cpow_zero_one {E : Spc} : cpow q (0 : Ht q E 2 1) 1 = 0 := by
  refine (cpow_succ q (0 : Ht q E 2 1) 0).trans ?_
  rw [map_zero, c_zero]

private theorem two_terms {X B : Spc} (p : B ⟶ X) (ξ : Ht q B 2 1) (hB : Inv q B) (n i : ℤ)
    (y : ∀ j : Fin 2, Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ))) :
    ∑ j, ((cup q (pull _ p _ _ (y j)) (cpow q ξ j)).cast (by ring) (by ring) : Ht q B n i) =
      pull _ p _ _ ((y 0).cast (by simp) (by simp) : Ht q X n i) +
      (cup q (pull _ p _ _ ((y 1).cast (by simp) (by simp) : Ht q X (n - 2) (i - 1))) (cpow q ξ 1)).cast
        (by push_cast; ring) (by push_cast; ring) := by
  rw [Fin.sum_univ_two]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [cup_pow_zero hB ξ (k := ((0 : Fin 2) : ℕ)) rfl, c_cc, pull_c]
  · rw [pull_c, cup_cl, c_cc]
    rfl

private theorem succ_terms {E Y : Spc} (πY : Y ⟶ E) (ξ : Ht q Y 2 1) (hY : Inv q Y) (N : ℕ) (n i : ℤ)
    (a : Ht q E n i) (b : ∀ j : Fin N, Ht q E (n - 2 - 2 * (((j : ℕ) : ℤ))) (i - 1 - ((j : ℕ) : ℤ))) :
    ∑ j : Fin (N + 1), ((cup q (pull _ πY _ _ ((Fin.cases (motive := fun j : Fin (N + 1) =>
        Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ))) (a.cast (by simp) (by simp))
        (fun j => (b j).cast (by rw [Fin.val_succ]; push_cast; ring) (by rw [Fin.val_succ]; push_cast; ring)) j))) (cpow q ξ j)).cast
        (by ring) (by ring) : Ht q Y n i) =
      pull _ πY _ _ a + ∑ j : Fin N, ((cup q (pull _ πY _ _ (b j)) (cpow q ξ ((j : ℕ) + 1))).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q Y n i) := by
  rw [Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun j _ => ?_)
  · rw [cup_pow_zero hY ξ (k := ((0 : Fin (N + 1)) : ℕ)) rfl, c_cc]
    simp only [Fin.cases_zero]
    rw [pull_c, c_cc]
    rfl
  · simp only [Fin.cases_succ]
    rw [pull_c, cup_cl, c_cc]
    rfl

private theorem rel_term {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y) (hp : p ≫ πX = β ≫ πY)
    (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1) (iX : Inv q X) (iY : Inv q Y) (iB : Inv q B)
    (hrel : ∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) =
      (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring))
    {m e n i : ℤ} (k : ℕ) (hn : m + 2 * (k : ℤ) = n - 2) (hi : e + (k : ℤ) = i - 1) (b : Ht q E m e) :
    ((cup q (pull _ p _ _ ((cup q (pull _ πX _ _ b) (cpow q ξX k)).cast hn hi)) (cpow q (pull _ β _ _ ξY) 1)).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q B n i) =
      pull _ β _ _ ((cup q (pull _ πY _ _ b) (cpow q ξY (k + 1))).cast (by push_cast; omega) (by push_cast; omega) : Ht q Y n i) := by
  have e1 : (pull _ p _ _ (pull _ πX _ _ b) : Ht q B m e) = pull _ β _ _ (pull _ πY _ _ b) := by
    rw [← pull_comp, ← pull_comp, hp]
  rw [pull_c, pull_u, pull_c, pull_u, UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX k iX, UpperTheory.pull_cupPow_eq_cupPow_pull q β ξY (k + 1) iY, e1, hrel k,
    cpow_one' iB, cup_cl, cup_cr, c_cc, GlobalTheory.T.tateTwistCupProduct_assoc, cup_cr, c_cc, c_cc, c_cc]

private theorem rel_sum {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y) (hp : p ≫ πX = β ≫ πY)
    (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1) (iX : Inv q X) (iY : Inv q Y) (iB : Inv q B)
    (hrel : ∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) =
      (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring))
    (N : ℕ) (n i : ℤ) (b : ∀ j : Fin N, Ht q E (n - 2 - 2 * (((j : ℕ) : ℤ))) (i - 1 - ((j : ℕ) : ℤ))) :
    ((cup q (pull _ p _ _ (∑ j : Fin N, ((cup q (pull _ πX _ _ (b j)) (cpow q ξX j)).cast (by ring) (by ring) : Ht q X (n - 2) (i - 1))))
        (cpow q (pull _ β _ _ ξY) 1)).cast (by push_cast; ring) (by push_cast; ring) : Ht q B n i) =
      pull _ β _ _ (∑ j : Fin N, ((cup q (pull _ πY _ _ (b j)) (cpow q ξY ((j : ℕ) + 1))).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q Y n i)) := by

  simp only [map_sum, AddMonoidHom.finsetSum_apply, c_sum]
  exact Finset.sum_congr rfl fun j _ => rel_term πX πY p β hp ξX ξY iX iY iB hrel _ (by ring) (by ring) (b j)

private theorem gysin_chase_identity {E X Y B W₁ B₁ : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
    (f₁ : W₁ ⟶ Y) (g₁ : B₁ ⟶ B) (b₁ : B₁ ⟶ W₁) (h₁ : g₁ ≫ β = b₁ ≫ f₁) (hp : p ≫ πX = β ≫ πY) (ξ : Ht q B 2 1)
    (iB : Inv q B) (hg : pull _ g₁ _ _ ξ = 0) {n i : ℤ} (hinj : Function.Injective (pull _ (g₁ ≫ p) (tw q i) n))
    (x : Ht q Y n i) (y0 : Ht q X n i) (y1 : Ht q X (n - 2) (i - 1)) (a0 : Ht q E n i)
    (hy : pull _ β _ _ x = pull _ p _ _ y0 + ((cup q (pull _ p _ _ y1) (cpow q ξ 1)).cast
      (by push_cast; ring) (by push_cast; ring) : Ht q B n i))
    (ha : pull _ (f₁ ≫ πY) _ _ a0 = pull _ f₁ _ _ x) : y0 = pull _ πX _ _ a0 := by
  apply hinj
  have e1 : pull _ g₁ _ _ ((cup q (pull _ p _ _ y1) (cpow q ξ 1)).cast
      (by push_cast; ring) (by push_cast; ring) : Ht q B n i) = 0 := by
    rw [pull_c, pull_u, UpperTheory.pull_cupPow_eq_cupPow_pull q g₁ ξ 1 iB, hg, cpow_zero_one, map_zero, c_zero]
  calc pull _ (g₁ ≫ p) _ _ y0 = pull _ g₁ _ _ (pull _ β _ _ x) := by
        rw [hy, map_add (f := _), e1, add_zero, pull_comp]
    _ = pull _ b₁ _ _ (pull _ f₁ _ _ x) := by rw [← pull_comp, h₁, pull_comp]
    _ = pull _ ((b₁ ≫ f₁) ≫ πY) _ _ a0 := by rw [← ha, ← pull_comp, Category.assoc]
    _ = pull _ (g₁ ≫ p) _ _ (pull _ πX _ _ a0) := by
        rw [← h₁, ← pull_comp, Category.assoc, Category.assoc, hp]

end UpperTheory.ChaseS

open UpperTheory.ChaseS in
theorem UpperTheory.leray_hirsch_of_two_covers_pullback_square :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 1 ≤ N → ∀ {E X Y B W₁ W₂ B₁ B₂ : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
        (f₁ : W₁ ⟶ Y) (f₂ : W₂ ⟶ Y) (g₁ : B₁ ⟶ B) (g₂ : B₂ ⟶ B) (b₁ : B₁ ⟶ W₁) (b₂ : B₂ ⟶ W₂)
        (h₁ : g₁ ≫ β = b₁ ≫ f₁) (h₂ : g₂ ≫ β = b₂ ≫ f₂) (_ : p ≫ πX = β ≫ πY) (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1),
        Inv q X → Inv q Y → Inv q B → Cover2 (ZMod q) f₁ f₂ → Cover2 (ZMod q) g₁ g₂ →
        LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j) →
        LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j) →
        (∀ i, Eqv _ (f₁ ≫ πY) (tw q i)) → (∀ i, Eqv _ (g₁ ≫ p) (tw q i)) → (∀ i, Eqv _ b₂ (tw q i)) →
        (∀ i, Eqv _ (pullback.map g₁ g₂ f₁ f₂ b₁ b₂ β h₁ h₂) (tw q i)) →
        pull _ g₁ _ _ (pull _ β _ _ ξY) = 0 →
        (∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring)) →
        ∀ n i : ℤ, Function.Surjective fun a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) =>
          ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := by
  intro q _ N hN E X Y B W₁ W₂ B₁ B₂ πX πY p β f₁ f₂ g₁ g₂ b₁ b₂ h₁ h₂ hp ξX ξY iX iY iB c1 c2 lX lp ef eg eb eM hg hrel n i x
  obtain ⟨y, hy⟩ := (lp n i).2 (pull _ β _ _ x)
  have hy2 := (two_terms p (pull _ β _ _ ξY) iB n i y).symm.trans hy
  obtain ⟨y0, y1, hy3⟩ : ∃ (y0 : Ht q X n i) (y1 : Ht q X (n - 2) (i - 1)), pull _ β _ _ x = pull _ p _ _ y0 +
      ((cup q (pull _ p _ _ y1) (cpow q (pull _ β _ _ ξY) 1)).cast (by push_cast; ring) (by push_cast; ring) : Ht q B n i) :=
    ⟨_, _, hy2.symm⟩
  obtain ⟨a0, ha0⟩ := (ef i n).2 (pull _ f₁ _ _ x)
  have hy0 := gysin_chase_identity πX πY p β f₁ g₁ b₁ h₁ hp _ iB hg ((eg i n).1) x y0 y1 a0 hy3 ha0
  obtain ⟨b, hb⟩ := (lX (n - 2) (i - 1)).2 y1
  have hb' : ∑ j : Fin N, ((cup q (pull _ πX _ _ (b j)) (cpow q ξX j)).cast (by ring) (by ring) : Ht q X (n - 2) (i - 1)) = y1 := hb
  have hR := rel_sum πX πY p β hp ξX ξY iX iY iB hrel N n i b
  rw [hb'] at hR
  have hv := UpperTheory.leray_hirsch_of_two_element_cover q N hN πX πY p β f₁ f₂ g₁ g₂ b₁ b₂ h₁ h₂ hp ξX iX c1 c2 lX ef eg eb eM n i
    (x - pull _ πY _ _ a0 - ∑ j : Fin N, ((cup q (pull _ πY _ _ (b j)) (cpow q ξY ((j : ℕ) + 1))).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q Y n i))
    (by
      rw [map_sub, map_sub, ← hR, hy3, hy0, ← pull_comp, ← pull_comp, hp]
      abel)
  refine ⟨Fin.cases (motive := fun j : Fin (N + 1) => Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
    (Ht.cast (by simp) (by simp) a0)
    (fun j => Ht.cast (by rw [Fin.val_succ]; push_cast; ring) (by rw [Fin.val_succ]; push_cast; ring) (b j)), ?_⟩
  refine (succ_terms πY ξY iY N n i a0 b).trans ?_
  rw [sub_sub, sub_eq_zero] at hv
  exact hv.symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem ht_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 x) = Ht.cast (h1.trans h3) (h2.trans h4) x := by
  subst h1 h2 h3 h4
  rfl

private theorem ht_cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Ht.cast h1 h2 (0 : Ht q E n i) = 0 := by
  subst h1 h2
  rfl

private theorem ht_cast_sub {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    Ht.cast h1 h2 (x - y) = Ht.cast h1 h2 x - Ht.cast h1 h2 y := by
  subst h1 h2
  rfl

private theorem ht_cast_sum {q : ℕ} {E : Spc} {n i n' i' : ℤ} {ι : Type} (h1 : n = n') (h2 : i = i') (s : Finset ι)
    (f : ι → Ht q E n i) : Ht.cast h1 h2 (∑ j ∈ s, f j) = ∑ j ∈ s, Ht.cast h1 h2 (f j) := by
  subst h1 h2
  rfl

private theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (h : Ht.cast h1 h2 x = 0) : x = 0 := by
  subst h1 h2
  exact h

private theorem cup_cast_left {q : ℕ} {E : Spc} {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (y : Ht q E m j) : cup q (Ht.cast h1 h2 x) y = Ht.cast (by rw [h1]) (by rw [h2]) (cup q x y) := by
  subst h1 h2
  rfl

private theorem cup_cast_right {q : ℕ} {E : Spc} {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (x : Ht q E n i)
    (y : Ht q E m j) : cup q x (Ht.cast h1 h2 y) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q x y) := by
  subst h1 h2
  rfl

private theorem pull_cast {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem pull_cup {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n m i j : ℤ} (a : Ht q Y n i) (b : Ht q Y m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a : Ht q X n i) (pull _ f _ _ b : Ht q X m j) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem cup_one_right {q : ℕ} [NeZero q] {E : Spc} (hE : Inv q E) {n i : ℤ} (a : Ht q E n i) :
    cup q a (one q E) = Ht.cast (by ring) (by ring) a := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q E a (one q E), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a, ht_cast_cast, mul_zero, Int.negOnePow_zero, one_smul]

private theorem cup_assoc' {q : ℕ} [NeZero q] {E : Spc} {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l) :
    cup q a (cup q b c) = Ht.cast (by ring) (by ring) (cup q (cup q a b) c) := by
  rw [GlobalTheory.T.tateTwistCupProduct_assoc q E a b c, ht_cast_cast]
  rfl

private theorem step_term {q : ℕ} [NeZero q] {X B : Spc} (p : B ⟶ X) (ξX : Ht q X 2 1) (ξ : Ht q B 2 1) (hX : Inv q X)
    (hrel : ∀ j : ℕ, cpow q ξ (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) ξ).cast (by push_cast; ring) (by push_cast; ring))
    {u v n i : ℤ} (x : Ht q X u v) (j : ℕ) (h1 : u + 2 * ((j + 1 : ℕ) : ℤ) = n) (h2 : v + ((j + 1 : ℕ) : ℤ) = i)
    (h3 : u + 2 * (j : ℤ) + 2 * ((1 : ℕ) : ℤ) = n) (h4 : v + (j : ℤ) + ((1 : ℕ) : ℤ) = i) :
    Ht.cast h1 h2 (cup q (pull _ p _ _ x) (cpow q ξ (j + 1))) =
      Ht.cast h3 h4 (cup q (pull _ p _ _ (cup q x (cpow q ξX j))) (cpow q ξ 1)) := by
  have e0 : cpow q ξ 1 = (cup q (cpow q (pull _ p _ _ ξX) 0) ξ).cast (by simp) (by simp) := hrel 0
  rw [hrel j, e0, cup_cast_right, cup_cast_right, ht_cast_cast, ht_cast_cast, ← UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX j hX,
    ← UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX 0 hX, cup_assoc', cup_assoc', ht_cast_cast, ht_cast_cast, ← pull_cup, ← pull_cup, cpow_zero,
    cup_cast_right, cup_one_right hX, ht_cast_cast, pull_cast, cup_cast_left, ht_cast_cast]

private theorem gysin_injective {q : ℕ} {X B : Spc} (p : B ⟶ X) (ξ : Ht q B 2 1)
    (LHp : LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q ξ j))
    (n i : ℤ) (y0 : Ht q X n i) (y1 : Ht q X (n - 2) (i - 1))
    (h : Ht.cast (n' := n) (i' := i) (by simp) (by simp) (cup q (pull _ p _ _ y0) (cpow q ξ 0)) +
      Ht.cast (n' := n) (i' := i) (by push_cast; ring) (by push_cast; ring) (cup q (pull _ p _ _ y1) (cpow q ξ 1)) = 0) :
    y0 = 0 ∧ y1 = 0 := by
  let a' : ∀ j : Fin 2, Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) := fun j =>
    Fin.cases (motive := fun j : Fin 2 => Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
      (Ht.cast (by simp) (by simp) y0)
      (fun k => Ht.cast (by have : (k : ℕ) = 0 := by omega
                            simp [this]) (by have : (k : ℕ) = 0 := by omega
                                             simp [this]) y1) j
  have e0 : a' 0 = Ht.cast (by simp) (by simp) y0 := rfl
  have e1 : a' 1 = Ht.cast (by simp) (by simp) y1 := rfl
  have hz := (LHp n i).1 (a₁ := a') (a₂ := 0) (by
    simp only [Fin.sum_univ_two, Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, add_zero]
    rw [e0, e1, pull_cast, pull_cast, cup_cast_left, cup_cast_left, ht_cast_cast, ht_cast_cast]
    exact h)
  exact ⟨eq_zero_of_cast _ _ _ (e0.symm.trans (congrFun hz 0)), eq_zero_of_cast _ _ _ (e1.symm.trans (congrFun hz 1))⟩

private theorem core {q : ℕ} [NeZero q] (N : ℕ) (hN : 1 ≤ N) {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
    (hc : p ≫ πX = β ≫ πY) (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1) (hX : Inv q X) (hY : Inv q Y)
    (LHX : LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j))
    (LHp : LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j))
    (hrel : ∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring))
    (n i : ℤ) (a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
    (h : ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) = 0) : a = 0 := by
  have pp : ∀ {m k : ℤ} (x : Ht q E m k), (pull _ β _ _ (pull _ πY _ _ x) : Ht q B m k) = pull _ p _ _ (pull _ πX _ _ x) := by
    intro m k x
    rw [← pull_comp, ← pull_comp, hc]
  have h1 : ∑ j : Fin (N + 1), ((cup q (pull _ p _ _ (pull _ πX _ _ (a j))) (cpow q (pull _ β _ _ ξY) j)).cast (by ring) (by ring) : Ht q B n i) = 0 := by
    have h' := congrArg (pull _ β (tw q i) n) h

    rw [map_sum, map_zero] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast, pull_cup, UpperTheory.pull_cupPow_eq_cupPow_pull q β ξY j hY, pp]
  rw [Fin.sum_univ_succ] at h1
  let y0 : Ht q X n i := Ht.cast (by simp) (by simp) (pull _ πX _ _ (a 0))
  let y1 : Ht q X (n - 2) (i - 1) := ∑ k : Fin N, Ht.cast (by simp only [Fin.val_succ]; push_cast; ring) (by simp only [Fin.val_succ]; push_cast; ring)
    (cup q (pull _ πX _ _ (a k.succ)) (cpow q ξX k))
  have hy := gysin_injective p (pull _ β _ _ ξY) LHp n i y0 y1 (by
    rw [← h1]
    congr 1
    · simp only [y0]
      rw [pull_cast, cup_cast_left, ht_cast_cast]
      rfl
    · simp only [y1]
      have sum_apply {A B : Type 1} [AddCommMonoid A] [AddCommMonoid B]
          {ι : Type} (s : Finset ι) (f : ι → A →+ B) (x : A) :
          (s.sum f) x = s.sum (fun j => f j x) := by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => simp [ha, ih]

      rw [map_sum, map_sum, sum_apply, ht_cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pull_cast, cup_cast_left, ht_cast_cast]
      exact (step_term p ξX (pull _ β _ _ ξY) hX hrel _ k _ _ _ _).symm)
  have hb := (LHX (n - 2) (i - 1)).1
    (a₁ := fun k => Ht.cast (by simp only [Fin.val_succ]; push_cast; ring) (by simp only [Fin.val_succ]; push_cast; ring) (a k.succ)) (a₂ := 0) (by
      simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, Finset.sum_const_zero]
      rw [← hy.2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pull_cast, cup_cast_left, ht_cast_cast])
  have ha := fun k : Fin N => eq_zero_of_cast _ _ _ (congrFun hb k)
  let k0 : Fin N := ⟨0, hN⟩
  let f : ∀ j : Fin N, Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) := Pi.single k0 (Ht.cast (by simp [k0]) (by simp [k0]) (a 0))
  have hf := (LHX n i).1 (a₁ := f) (a₂ := 0) (by
    simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single k0 (fun j _ hj => by simp only [f, Pi.single_eq_of_ne hj, map_zero, AddMonoidHom.zero_apply, ht_cast_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [f, Pi.single_eq_same]
    have e : cpow q ξX (k0 : ℕ) = (one q X).cast (by simp [k0]) (by simp [k0]) := rfl
    have hy0 : (pull _ πX _ _ (a 0) : Ht q X _ _) = 0 := eq_zero_of_cast _ _ _ hy.1
    rw [e, cup_cast_right, cup_one_right hX, pull_cast, hy0]
    simp only [ht_cast_zero])
  have h0 : a 0 = 0 := eq_zero_of_cast _ _ _ ((Pi.single_eq_same (M := fun j : Fin N => Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ))) k0 _).symm.trans (congrFun hf k0))
  funext j
  refine Fin.cases h0 ha j

theorem UpperTheory.leray_hirsch_of_pullback_square :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 1 ≤ N → ∀ {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y) (_ : p ≫ πX = β ≫ πY)
        (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1), Inv q X → Inv q Y →
        LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j) →
        LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j) →
        (∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring)) →
        ∀ n i : ℤ, Function.Injective fun a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) =>
          ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := by
  intro q _ N hN E X Y B πX πY p β hc ξX ξY hX hY LHX LHp hrel n i a b hab
  have hab' : ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) =
      ∑ j, ((cup q (pull _ πY _ _ (b j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := hab
  refine sub_eq_zero.1 (core N hN πX πY p β hc ξX ξY hX hY LHX LHp hrel n i (a - b) ?_)
  simp only [Pi.sub_apply, map_sub, AddMonoidHom.sub_apply, ht_cast_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.2 hab'
end
