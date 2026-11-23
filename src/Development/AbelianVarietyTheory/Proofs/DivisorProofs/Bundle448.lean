module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
import Mathlib.Algebra.Category.Grp.Zero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle431
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanOne

variable {T : Type 1} [Category.{0} T]

lemma nat_el {C D : T ⥤ AbCx} (φ : C ⟶ D) {U V : T} (g : U ⟶ V) (n : ℤ) (c : (C.obj U).X n) :
    (φ.app V).f n ((C.map g).f n c) = (D.map g).f n ((φ.app U).f n c) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, φ.naturality]

lemma comm_el {A B : AbCx} (f : A ⟶ B) (n m : ℤ) (a : A.X n) : f.f m (A.d n m a) = B.d n m (f.f n a) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, f.comm]

lemma map_comp_el (C : T ⥤ AbCx) {U V W : T} (g : U ⟶ V) (h : V ⟶ W) (n : ℤ) (c : (C.obj U).X n) :
    (C.map (g ≫ h)).f n c = (C.map h).f n ((C.map g).f n c) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

lemma hom_zero' {A B : AddCommGrpCat.{1}} (f : A ⟶ B) : f (0 : A) = 0 := map_zero f.hom

lemma locInj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocInj Cov φ) (k m : ℤ) (hk : k + 1 = m)
    (U : T) (c : (C.obj U).X m) (hc : (C.obj U).d m (m + 1) c = 0)
    (hy : ∃ y : (D.obj U).X k, (φ.app U).f m c = (D.obj U).d k m y) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ b : (C.obj V).X k, (C.obj V).d k m b = (C.map g).f m c := by
  obtain rfl : k = m - 1 := by omega
  exact h m U c hc hy

lemma locSurj' {Cov : MorphismProperty T} {C D : T ⥤ AbCx} {φ : C ⟶ D} (h : LocSurj Cov φ) (k n : ℤ) (hk : k + 1 = n)
    (U : T) (z : (D.obj U).X n) (hz : (D.obj U).d n (n + 1) z = 0) :
    ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ (c : (C.obj V).X n) (y : (D.obj V).X k), (C.obj V).d n (n + 1) c = 0 ∧
      (φ.app V).f n c = (D.map g).f n z + (D.obj V).d k n y := by
  obtain rfl : k = n - 1 := by omega
  exact h n U z hz

theorem cartan_one : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition]
    (C D : T ⥤ AbCx) (φ : C ⟶ D), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n) ∧ IsZero ((D.obj U).X n)) →
    Refines Cov (fun U X a => ∀ n, WExact (term C n) a ∧ WExact (term D n) a) → LocSurj Cov φ → LocInj Cov φ →
    ∀ U, SurjH (φ.app U) ∧ InjH (φ.app U) := by
  intro T _ Cov _ C D φ hb hR hS hI
  obtain ⟨K, p, q, hbij, hd⟩ := GlobalTheory.EtC.coneEl_exists T C D φ
  have ext : ∀ n U (x y : (K.obj U).X n), (p n).app U x = (p n).app U y → (q n).app U x = (q n).app U y → x = y :=
    fun n U x y h1 h2 => (hbij n U).1 (Prod.ext h1 h2)
  have mk : ∀ n U (c : (C.obj U).X (n + 1)) (z : (D.obj U).X n), ∃ x : (K.obj U).X n, (p n).app U x = c ∧ (q n).app U x = z := by
    intro n U c z
    obtain ⟨x, hx⟩ := (hbij n U).2 (c, z)
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  have dp := fun n U x => (hd n U x).1
  have dq := fun n U x => (hd n U x).2
  have natP : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (p n).app V ((K.map g).f n x) = (C.map g).f (n + 1) ((p n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (p n) g x
  have natQ : ∀ n {U V : T} (g : U ⟶ V) (x : (K.obj U).X n),
      (q n).app V ((K.map g).f n x) = (D.map g).f n ((q n).app U x) :=
    fun n _ _ g x => NatTrans.naturality_apply (q n) g x
  have cyc : ∀ n U (x : (K.obj U).X n), (C.obj U).d (n + 1) (n + 1 + 1) ((p n).app U x) = 0 →
      (φ.app U).f (n + 1) ((p n).app U x) + (D.obj U).d n (n + 1) ((q n).app U x) = 0 →
      (K.obj U).d n (n + 1) x = 0 := by
    intro n U x h1 h2
    apply ext
    · rw [dp, h1, neg_zero]; exact (hom_zero' _).symm
    · rw [dq, h2]; exact (hom_zero' _).symm

  have hbK : ∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((K.obj U).X n) := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b - 1, fun n hn U => ?_⟩
    have h1 := AddCommGrpCat.subsingleton_of_isZero (hb (n + 1) (by omega) U).1
    have h2 := AddCommGrpCat.subsingleton_of_isZero (hb n (by omega) U).2
    haveI : Subsingleton ((K.obj U).X n) :=
      ⟨fun x y => ext n U x y (@Subsingleton.elim _ h1 _ _) (@Subsingleton.elim _ h2 _ _)⟩
    exact AddCommGrpCat.isZero_of_subsingleton _

  have hRK : Refines Cov (fun U X a => ∀ n, WExact (term K n) a) := by
    intro U V g hg
    obtain ⟨X, a, h, hga, hQ⟩ := hR U V g hg
    refine ⟨X, a, h, hga, fun n => ?_⟩
    refine GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a Bool (fun i => cond i (term C (n + 1)) (term D n)) (term K n)
      (fun i => match i with | true => p n | false => q n) ?_ ?_
    · intro W
      constructor
      · intro x y hxy
        exact ext n W x y (congrFun hxy true) (congrFun hxy false)
      · intro f
        obtain ⟨x, hx1, hx2⟩ := mk n W (f true) (f false)
        refine ⟨x, funext fun i => ?_⟩
        cases i
        · exact hx2
        · exact hx1
    · intro i
      cases i
      · exact (hQ n).2
      · exact (hQ (n + 1)).1

  have gen : ∀ (j : ℤ) (U : T) (x : (K.obj U).X (j + 1)), (K.obj U).d (j + 1) (j + 1 + 1) x = 0 →
      ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X j, (K.obj V).d j (j + 1) y = (K.map g).f (j + 1) x := by
    intro j U x hx
    obtain ⟨c, hc⟩ : ∃ c : (C.obj U).X (j + 1 + 1), (p (j + 1)).app U x = c := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : (D.obj U).X (j + 1), (q (j + 1)).app U x = z := ⟨_, rfl⟩
    have h1 : (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 := by
      have := dp (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc] at this
      exact neg_eq_zero.mp this.symm
    have h2 : (D.obj U).d (j + 1) (j + 1 + 1) z + (φ.app U).f (j + 1 + 1) c = 0 := by
      have := dq (j + 1) U x
      rw [hx] at this
      erw [hom_zero'] at this
      rw [hc, hz] at this
      exact (add_comm _ _).trans this.symm
    obtain ⟨V₁, g₁, hg₁, b, hb⟩ := locInj' hI (j + 1) (j + 1 + 1) rfl U c h1
      ⟨-z, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h2)⟩
    obtain ⟨w, hw⟩ : ∃ w : (D.obj V₁).X (j + 1), (D.map g₁).f (j + 1) z + (φ.app V₁).f (j + 1) b = w := ⟨_, rfl⟩
    have hw0 : (D.obj V₁).d (j + 1) (j + 1 + 1) w = 0 := by
      rw [← hw, map_add (f := _), ← comm_el (D.map g₁), ← comm_el (φ.app V₁), hb, nat_el, ← map_add (f := _), h2, map_zero]
    obtain ⟨V₂, g₂, hg₂, c', y', hc', hy'⟩ := locSurj' hS j (j + 1) rfl V₁ w hw0
    obtain ⟨y, hyp, hyq⟩ := mk j V₂ (c' - (C.map g₂).f (j + 1) b) (-y')
    refine ⟨V₂, g₁ ≫ g₂, Cov.comp_mem _ _ hg₁ hg₂, y, ?_⟩
    apply ext
    · rw [dp, hyp, natP, hc, map_sub, hc', ← comm_el (C.map g₂), hb, map_comp_el, zero_sub, neg_neg]
    · rw [dq, hyp, hyq, natQ, hz, map_sub, map_neg, hy', ← hw, map_add (f := _), nat_el, map_comp_el]
      abel
  have hLK : LocExact Cov K := by
    have gen' : ∀ k n : ℤ, k + 1 = n → ∀ (U : T) (x : (K.obj U).X n), (K.obj U).d n (n + 1) x = 0 →
        ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : (K.obj V).X k, (K.obj V).d k n y = (K.map g).f n x := by
      intro k n hkn
      subst hkn
      exact gen k
    intro n U x hx
    exact gen' (n - 1) n (by omega) U x hx

  have exK : ∀ (U : T) (k n : ℤ), k + 1 = n → ∀ x : (K.obj U).X n, (K.obj U).d n (n + 1) x = 0 →
      ∃ y : (K.obj U).X k, (K.obj U).d k n y = x := by
    intro U k n hkn x hx
    obtain rfl : k = n - 1 := by omega
    exact GlobalTheory.CartanZero.cartan_zero T Cov K hbK hRK hLK U n x hx
  intro U
  constructor
  · have sg : ∀ (j : ℤ) (z : (D.obj U).X (j + 1)), (D.obj U).d (j + 1) (j + 1 + 1) z = 0 →
        ∃ (c : (C.obj U).X (j + 1)) (y : (D.obj U).X j), (C.obj U).d (j + 1) (j + 1 + 1) c = 0 ∧
          (φ.app U).f (j + 1) c = z + (D.obj U).d j (j + 1) y := by
      intro j z hz
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U 0 z
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, map_zero]) (by rw [hxp, hxq, map_zero, zero_add, hz])
      obtain ⟨y, hy⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨u, hu⟩ : ∃ u : (D.obj U).X j, (q j).app U y = u := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y = v := ⟨_, rfl⟩
      refine ⟨v, -u, ?_, ?_⟩
      · have := dp j U y
        rw [hy, hxp, hv] at this
        exact neg_eq_zero.mp this.symm
      · have := dq j U y
        rw [hy, hxq, hu, hv] at this
        rw [map_neg, this]
        abel
    have sg' : ∀ k n : ℤ, k + 1 = n → ∀ (z : (D.obj U).X n), (D.obj U).d n (n + 1) z = 0 →
        ∃ (c : (C.obj U).X n) (y : (D.obj U).X k), (C.obj U).d n (n + 1) c = 0 ∧
          (φ.app U).f n c = z + (D.obj U).d k n y := by
      intro k n hkn
      subst hkn
      exact sg k
    intro n z hz
    exact sg' (n - 1) n (by omega) z hz
  · have ij : ∀ (j : ℤ) (c : (C.obj U).X (j + 1 + 1)), (C.obj U).d (j + 1 + 1) (j + 1 + 1 + 1) c = 0 →
        ∀ y : (D.obj U).X (j + 1), (φ.app U).f (j + 1 + 1) c = (D.obj U).d (j + 1) (j + 1 + 1) y →
        ∃ b : (C.obj U).X (j + 1), (C.obj U).d (j + 1) (j + 1 + 1) b = c := by
      intro j c hc y hy
      obtain ⟨x, hxp, hxq⟩ := mk (j + 1) U c (-y)
      have hx : (K.obj U).d (j + 1) (j + 1 + 1) x = 0 :=
        cyc _ _ _ (by rw [hxp, hc]) (by rw [hxp, hxq, map_neg, hy, add_neg_cancel])
      obtain ⟨y', hy'⟩ := exK U j (j + 1) rfl x hx
      obtain ⟨v, hv⟩ : ∃ v : (C.obj U).X (j + 1), (p j).app U y' = v := ⟨_, rfl⟩
      refine ⟨-v, ?_⟩
      have := dp j U y'
      rw [hy', hxp, hv] at this
      rw [map_neg]
      exact this.symm
    have ij' : ∀ i n : ℤ, i + 1 = n → ∀ c : (C.obj U).X n, (C.obj U).d n (n + 1) c = 0 →
        ∀ y : (D.obj U).X i, (φ.app U).f n c = (D.obj U).d i n y → ∃ b : (C.obj U).X i, (C.obj U).d i n b = c := by
      intro i n hin
      subst hin
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact ij j
    intro n c hc ⟨y, hy⟩
    exact ij' (n - 1) n (by omega) c hc y hy

end GlobalTheory.CartanOne
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

private lemma twist_estimate_first (a b e M : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 2 ≤ e) (hb : 0 < b)
    (hM : 0 ≤ M) (h : e + a ^ 2 / b ≤ 8 * (1 + M)) :
    0 ≤ a / e ∧ a / e ≤ 1 ∧ 0 < (b * e + a ^ 2) / e ^ 2 ∧ (a / e) ^ 2 ≤ (b * e + a ^ 2) / e ^ 2 ∧
      1 / (1 + M) / 8 ≤ (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_one he0]; linarith
  · rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 < b * e := by positivity
    linarith
  · have e1 : (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ = 1 / (e + a ^ 2 / b) := by
      field_simp
      ring
    have e2 : 1 / (1 + M) / 8 = 1 / (8 * (1 + M)) := by
      field_simp
    rw [e1, e2]
    exact one_div_le_one_div_of_le (by positivity) h

private lemma twist_estimate_second (a b e m : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 300 ≤ e) (hb : 3 / 16 ≤ b)
    (h : e ≤ 2 + 2 * m) :
    e⁻¹ / ((b * e + a ^ 2) / e ^ 2) ≤ 16 / 3 ∧
      1 / (1 + m ^ 2) / 8 ≤ (1 - 5 * ((a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2))) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hb0 : 0 < b := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  have hbe : 3 / 16 * e ≤ b * e := mul_le_mul_of_nonneg_right hb he0.le
  have ha4 : a ^ 2 ≤ 4 := by nlinarith
  have ha0 : 0 ≤ a ^ 2 := by positivity
  constructor
  · have e1 : e⁻¹ / ((b * e + a ^ 2) / e ^ 2) = e / (b * e + a ^ 2) := by
      field_simp
    rw [e1, div_le_iff₀ hD]
    linarith
  · have e1 : (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2) = a ^ 2 / (b * e + a ^ 2) := by
      field_simp
    have h1 : a ^ 2 / (b * e + a ^ 2) ≤ 1 / 10 := by
      rw [div_le_iff₀ hD]; linarith
    have e2 : 1 / (1 + m ^ 2) / 8 = 1 / 2 * (4 * (1 + m ^ 2))⁻¹ := by
      field_simp
      norm_num
    have h2 : (4 * (1 + m ^ 2))⁻¹ ≤ e⁻¹ := by
      apply inv_anti₀ he0
      nlinarith [sq_nonneg (m - 1 / 4)]
    rw [e1, e2]
    apply mul_le_mul (by linarith) h2 (by positivity) (by linarith)

theorem exists_log_twist : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  intro T hT
  obtain ⟨η, η1, η2, hs, hd, hp, hw⟩ := GlobalTheory.T.exists_concaveTwist_eta_inequalities T hT
  set κ : ℝ → ℝ := fun x => Real.smoothTransition (2 - 16 * x) * (-Real.log (η (-x))) with hκ
  have hloc : ∀ x : ℝ, x < 1 / 16 → κ x = -Real.log (η (-x)) := by
    intro x hx
    simp only [hκ]
    rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  have hη : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η (-x)) (-η1 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.1
    have h' := HasDerivAt.comp x (h₂ := η) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hη1 : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η1 (-x)) (-η2 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.2
    have h' := HasDerivAt.comp x (h₂ := η1) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hd1 : ∀ x : ℝ, x < 1 / 16 → deriv κ x = η1 (-x) / η (-x) := by
    intro x hx
    have hev : κ =ᶠ[𝓝 x] fun x => -Real.log (η (-x)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hloc y hy
    rw [hev.deriv_eq]
    have h := ((hη x hx).log (hd (-x) (by linarith)).1.ne').neg
    have h2 : HasDerivAt (fun x => -Real.log (η (-x))) (-(-η1 (-x) / η (-x))) x := h
    rw [h2.deriv]; ring
  have hd2 : ∀ x : ℝ, x < 1 / 16 →
      deriv (deriv κ) x = ((-η2 (-x)) * η (-x) + η1 (-x) ^ 2) / η (-x) ^ 2 := by
    intro x hx
    have hev : deriv κ =ᶠ[𝓝 x] fun x => η1 (-x) / η (-x) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hd1 y hy
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun x => η1 (-x) / η (-x)) _ x :=
      (hη1 x hx).div (hη x hx) (hd (-x) (by linarith)).1.ne'
    rw [h2.deriv]; ring
  have hexp : ∀ x : ℝ, x < 1 / 16 → Real.exp (κ x) = (η (-x))⁻¹ := by
    intro x hx
    rw [hloc x hx, Real.exp_neg, Real.exp_log (hd (-x) (by linarith)).1]
  have hwT : ∀ x : ℝ, x ≤ 0 → wT T x = 1 / (1 + (min (-x) (T + 1)) ^ 2) := by
    intro x hx
    unfold wT
    congr 2
    rcases le_total (-x) (T + 1) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]; ring
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  refine ⟨κ, ?_, ⟨Real.log (2 * T + 4), ?_⟩, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1 / 4
    · have h1 : ContDiffAt ℝ ∞ η (-x) :=
        hs.contDiffAt (Ioi_mem_nhds (by linarith))
      have h2 : ContDiffAt ℝ ∞ (fun x : ℝ => η (-x)) x :=
        ContDiffAt.comp x (g := η) (f := fun x : ℝ => -x) h1 contDiff_neg.contDiffAt
      have h3 := (h2.log (hd (-x) (by linarith)).1.ne').neg
      have h4 : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (2 - 16 * x)) :=
        Real.smoothTransition.contDiff.comp (by fun_prop)
      exact h4.contDiffAt.mul h3
    · have hev : κ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds (show (1 / 8 : ℝ) < x by linarith)] with y hy
        have hy' : (1 / 8 : ℝ) < y := hy
        simp only [hκ]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    obtain ⟨-, -, h2, -, h3, -⟩ := hp (-x) (by linarith)
    rw [hloc x (by linarith), abs_neg, abs_of_nonneg (Real.log_nonneg (by linarith))]
    apply Real.log_le_log (by linarith)
    have := min_le_right (-x) (T + 1)
    linarith
  · intro x hx
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, h2, h3, -, h5⟩ := hp (-x) (by linarith)
    rw [hd1 x hx', hd2 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_first _ _ _ _ h0 h1 h2 (by linarith) (sq_nonneg _) h5
  · intro x hx1 hx2
    have hx : x ≤ 0 := by linarith
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, -, -, h4, -⟩ := hp (-x) (by linarith)
    obtain ⟨h6, h7⟩ := hw (-x) (by linarith) (by linarith)
    rw [hd2 x hx', hd1 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_second _ _ _ _ h0 h1 (by linarith) h6 h4

end GlobalTheory.OTY
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_laurentConstantTermForm_functionField : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∃ ρ : F →ₗ[k] k, IsRes k x ρ := by
  first | (exact @GlobalTheory.exists_isRes) | (exact GlobalTheory.exists_isRes) | (intros; apply GlobalTheory.exists_isRes <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧ ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  first | (exact @GlobalTheory.PD.isTop_exists_and_eq) | (exact GlobalTheory.PD.isTop_exists_and_eq) | (intros; apply GlobalTheory.PD.isTop_exists_and_eq <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_sign_iMulti_D_chart_change : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i : Fin (d + 1), ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) = ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  first | (exact @GlobalTheory.PD.volume_chart_change) | (exact GlobalTheory.PD.volume_chart_change) | (intros; apply GlobalTheory.PD.volume_chart_change <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.dlog_basis_and_vanishing_above_dimension : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  first | (exact @GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (exact GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (intros; apply GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  first | (exact @GlobalTheory.PD.omB_comap_span_eq_top) | (exact GlobalTheory.PD.omB_comap_span_eq_top) | (intros; apply GlobalTheory.PD.omB_comap_span_eq_top  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K, Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧ ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) = ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  first | (exact @GlobalTheory.PD.omB_eq_range_exteriorPower) | (exact GlobalTheory.PD.omB_eq_range_exteriorPower) | (intros; apply GlobalTheory.PD.omB_eq_range_exteriorPower  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.residue_functional_vanishes_on_omega_forms : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I → ∀ y ∈ omA k x I, ρ y = 0 := by
  first | (exact @GlobalTheory.PD.ResVan.resvan) | (exact GlobalTheory.PD.ResVan.resvan) | (intros; apply GlobalTheory.PD.ResVan.resvan <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ p q : ℕ, p + q = d → (∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ ⋀[K]^p Ω[K⁄k], Algebra.trace F K (τ (a * y)) = 0) → y = 0) ∧ Module.finrank K (⋀[K]^p Ω[K⁄k]) = Module.finrank K (⋀[K]^q Ω[K⁄k]) ∧ FiniteDimensional K (⋀[K]^p Ω[K⁄k]) := by
  first | (exact @GlobalTheory.PD.IsFinCover.trace_wedge_perfect) | (exact GlobalTheory.PD.IsFinCover.trace_wedge_perfect) | (intros; apply GlobalTheory.PD.IsFinCover.trace_wedge_perfect <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD


set_option autoImplicit false in
open KaehlerDifferential in
theorem _root_.GlobalTheory.PD.rA_single_polyEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x →
    ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] _root_.GlobalTheory.PD.rA k x {i},
      ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  intro k _ F _ _ d x hP i
  refine ⟨_root_.GlobalTheory.PD.Model.chartEquiv k x hP i, fun j => ?_⟩
  simp [_root_.GlobalTheory.PD.Model.chartEquiv, _root_.GlobalTheory.PD.Model.yc,
    AlgebraicIndependent.aevalEquiv_apply_coe]

end GlobalTheory.PD
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) → ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 → ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'), ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.AwayCont.kill_of_loc) | (exact GlobalTheory.EtC.AwayCont.kill_of_loc) | (intros; apply GlobalTheory.EtC.AwayCont.kill_of_loc <;> assumption)
end
