module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle095
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle069
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle072
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.FiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle097
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open Polynomial in

theorem _root_.GlobalTheory.T.newton_approximation_of_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA
  have hStep : Step ϖ := by
    intro Q n hQ hd hn
    have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
    have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
    have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
      Ideal.subset_span (by simp)
    rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
    · refine ⟨0, ?_, ?_⟩
      · rw [← hq0]; exact hdiv
      · rw [zero_pow hd.ne']; exact dvd_zero _
    ·
      have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
      have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
        intro x hx
        obtain ⟨e, he⟩ := hdiv
        have h0 : ϖ ^ (n + 1) * x = 0 := by
          rw [he]; linear_combination e * hx
        exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
      obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := GlobalTheory.T.newton_polygon_slope_existence ϖ hD hRoots (fun i => Q.coeff i)
        Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
      have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
          (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
        intro i
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
        · by_cases hid : i ≤ Q.natDegree
          · obtain ⟨t, ht⟩ := hc1 i hi hid
            exact ⟨t, fun h => by omega, fun _ => ht⟩
          · exact ⟨0, fun h => by omega, fun h => by omega⟩
      choose s hs0 hsd using hs
      have hunit : IsUnit (s i0) := by
        obtain ⟨t, ht⟩ := hi3
        have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
          have h6 := hsd i0 hi2
          rw [h6] at ht
          linear_combination -ht
        have h7 := hcancel _ h5
        exact IsUnit.of_mul_eq_one t (by linear_combination h7)
      let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (s i) * Polynomial.X ^ i
      have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
        intro j hj'
        simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_ite_eq]
        simp [Nat.lt_succ_of_le hj']
      have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
        intro y
        simp [R, Polynomial.eval_finsetSum]
      let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
      have hP0 : P.coeff 0 = 1 := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
      have hPi : IsUnit (P.coeff i0) := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc i0 hi2]
        exact hunit.map _
      have hroot : ∃ y', P.eval y' = 0 := by
        let T := S ⧸ Ideal.span {ϖ ^ 2}
        rcases subsingleton_or_nontrivial T with hT | hT
        · exact ⟨0, Subsingleton.elim _ _⟩
        have hAdd : ∀ a b : T, IsUnit (a + b) → IsUnit a ∨ IsUnit b :=
          GlobalTheory.CompanionTheory.NewtonStep.isUnit_or_of_add_quot ϖ hj hD
        have unitRoot : ∀ (d : ℕ) (F : Polynomial T), F.Monic → F.natDegree = d →
            ∀ k < d, IsUnit (F.coeff k) → ∃ u : Tˣ, F.eval (u : T) = 0 := by
          intro d
          induction d with
          | zero =>
            intro F hF hdeg k hk
            omega
          | succ d ih =>
            intro F hF hdeg k hk hcoeff
            obtain ⟨x, hx⟩ := hA F hF (by omega)
            by_cases hxu : IsUnit x
            · obtain ⟨u, rfl⟩ := hxu
              exact ⟨u, hx⟩
            let G := F /ₘ (X - C x)
            have hfactor : (X - C x) * G = F := mul_divByMonic_eq_iff_isRoot.mpr hx
            have hG : G.Monic := (monic_X_sub_C x).of_mul_monic_left (hfactor.symm ▸ hF)
            have hGdeg : G.natDegree = d := by
              have h := (monic_X_sub_C x).natDegree_mul hG
              rw [hfactor, hdeg, natDegree_X_sub_C] at h
              omega
            cases k with
            | zero =>
              rw [← hfactor, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub] at hcoeff
              have hprod : IsUnit (x * G.coeff 0) := by simpa only [neg_neg] using hcoeff.neg
              exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
            | succ k =>
              rw [← hfactor, coeff_X_sub_C_mul, sub_eq_add_neg] at hcoeff
              rcases hAdd _ _ hcoeff with hGu | hneg
              · obtain ⟨u, hu⟩ := ih G hG hGdeg k (by omega) hGu
                exact ⟨u, by rw [← hfactor, eval_mul, hu, mul_zero]⟩
              · have hprod : IsUnit (x * G.coeff (k + 1)) := by
                  simpa only [neg_neg] using hneg.neg
                exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
        have htd : P.natTrailingDegree = 0 :=
          Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [hP0]; exact one_ne_zero))
        have hmon : P.reverse.Monic := by
          rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, hP0]
        have hdeg : P.reverse.natDegree = P.natDegree := by
          rw [reverse_natDegree, htd, Nat.sub_zero]
        have hle : i0 ≤ P.natDegree := le_natDegree_of_ne_zero hPi.ne_zero
        have hcoeff : P.reverse.coeff (P.natDegree - i0) = P.coeff i0 := by
          rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
          congr 1
          omega
        obtain ⟨u, hu⟩ := unitRoot P.natDegree P.reverse hmon hdeg (P.natDegree - i0)
          (by omega) (hcoeff.symm ▸ hPi)
        refine ⟨↑(u⁻¹), ?_⟩
        let : Invertible ((u⁻¹ : Tˣ) : T) := (u⁻¹).invertible
        have hre := eval₂_reverse_mul_pow (RingHom.id T) ((u⁻¹ : Tˣ) : T) P
        have hinv : ⅟((u⁻¹ : Tˣ) : T) = (u : T) := by simp
        rw [hinv, eval₂_id, eval₂_id, hu, zero_mul] at hre
        exact hre.symm
      obtain ⟨y', hy'⟩ := hroot
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
      have hRy : ϖ ^ 2 ∣ R.eval y := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
        simp only [P, Polynomial.eval_map] at hy'
        rwa [Polynomial.eval₂_at_apply] at hy'
      have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
        rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        rw [mul_pow]
        linear_combination (y ^ i) * h8
      have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
      refine ⟨c * y, ?_, ?_⟩
      · rw [hQz]
        have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
        refine dvd_trans ?_ h9
        rw [← pow_add]
        exact pow_dvd_pow _ (by omega)
      · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
          have h11 := hc1 Q.natDegree hd le_rfl
          simpa [hQ.coeff_natDegree] using h11
        rw [mul_pow]
        exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _
  exact hStep
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe u v w

namespace GlobalTheory.CompanionTheory.CechFull

section Complexes

variable {R : Type} [CommRing R]

theorem mapH_mapH_of_inv {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R))
    (ψ : Cx.Hom L K (RingHom.id R)) (h : ∀ n x, ψ.f n (φ.f n x) = x) (p : ℕ) (x : K.H p) :
    ψ.mapH p (φ.mapH p x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ψ.mapZ p (φ.mapZ p z)) = Submodule.Quotient.mk z
  exact congrArg _ (Subtype.ext (h p z.1))

def equivH {K : Cx.{w} R} {L : Cx.{w} R} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L K (RingHom.id R))
    (h : ∀ n x, ψ.f n (φ.f n x) = x) (h' : ∀ n x, φ.f n (ψ.f n x) = x) (p : ℕ) : K.H p ≃ₗ[R] L.H p :=
  LinearEquiv.ofLinear (φ.mapH p) (ψ.mapH p)
    (LinearMap.ext (mapH_mapH_of_inv ψ φ h' p)) (LinearMap.ext (mapH_mapH_of_inv φ ψ h p))

def cosHom {K L : Cos.{w} R} (f : ∀ n, K.X n →ₗ[R] L.X n)
    (h : ∀ n k x, L.δ n k (f n x) = f (n + 1) (K.δ n k x)) : Cx.Hom K.cx L.cx (RingHom.id R) :=
  ⟨f, fun n x => by
    change L.d n (f n x) = f (n + 1) (K.d n x)

    rw [Cos.d_apply, Cos.d_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_zsmul, h]⟩

end Complexes

section Cat

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem pull_pull_of_inv {C' : Type u} [Category.{v} C'] {G : C ⥤ ModuleCat.{w} R} {G' : C' ⥤ ModuleCat.{w} R}
    (m : CH.Mor G G' (RingHom.id R)) (m' : CH.Mor G' G (RingHom.id R))
    (h : ∀ n f, m'.pullC n (m.pullC n f) = f) (p : ℕ) (x : CH.H G p) : m'.pull p (m.pull p x) = x :=
  mapH_mapH_of_inv m.hom m'.hom h p x

variable (F : C ⥤ ModuleCat.{w} R) (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C)

abbrev subFam : ι → ObjectProperty Q.FullSubcategory := fun α T => W α T.obj

variable {Q W}

def upG (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT W i).FullSubcategory ⥤ (capT (subFam Q W) i).FullSubcategory :=
  (capT (subFam Q W) i).lift (Q.lift (capT W i).ι fun T => hW (i 0) _ (T.property 0)) fun T => T.property

def downG {n : ℕ} (i : Fin (n + 1) → ι) :
    (capT (subFam Q W) i).FullSubcategory ⥤ (capT W i).FullSubcategory :=
  (capT W i).lift ((capT (subFam Q W) i).ι ⋙ Q.ι) fun T => T.property

def upM (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) ((capT W i).ι ⋙ F) (RingHom.id R) where
  G := upG hW i
  τ _ := LinearMap.id
  nat _ _ := rfl

def downM {n : ℕ} (i : Fin (n + 1) → ι) :
    CH.Mor ((capT W i).ι ⋙ F) ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) (RingHom.id R) where
  G := downG i
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem down_up_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT (subFam Q W) i).ι ⋙ Q.ι ⋙ F) m) :
    (downM F i).pullC m ((upM F hW i).pullC m f) = f := rfl

theorem up_down_pullC (hW : ∀ α, W α ≤ Q) {n : ℕ} (i : Fin (n + 1) → ι) (m : ℕ)
    (f : CH.Cn ((capT W i).ι ⋙ F) m) :
    (upM F hW i).pullC m ((downM F i).pullC m f) = f := rfl

end Cat

section Assemble

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) {Q : ObjectProperty C} {ι : Type} {W : ι → ObjectProperty C}

def upX (hW : ∀ α, W α ≤ Q) (q n : ℕ) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).X n →ₗ[R] (cechH F W q).X n :=
  LinearMap.pi fun i => ((upM F hW i).pull q).comp (LinearMap.proj i)

def downX (q n : ℕ) :
    (cechH F W q).X n →ₗ[R] (cechH (Q.ι ⋙ F) (subFam Q W) q).X n :=
  LinearMap.pi fun i => ((downM F i).pull q).comp (LinearMap.proj i)

theorem upX_δ (hW : ∀ α, W α ≤ Q) (q n : ℕ) (k : Fin (n + 2))
    (x : (cechH (Q.ι ⋙ F) (subFam Q W) q).X n) :
    (cechH F W q).δ n k (upX F hW q n x) = upX F hW q (n + 1) ((cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU F _).pull q ((upM F hW (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (upM F hW t).pull q ((resU (Q.ι ⋙ F) _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

theorem downX_δ (q n : ℕ) (k : Fin (n + 2)) (x : (cechH F W q).X n) :
    (cechH (Q.ι ⋙ F) (subFam Q W) q).δ n k (downX (Q := Q) F q n x) =
      downX (Q := Q) F q (n + 1) ((cechH F W q).δ n k x) := by
  funext t
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x (t ∘ k.succAbove))
  change (resU (Q.ι ⋙ F) _).pull q ((downM F (t ∘ k.succAbove)).pull q (x (t ∘ k.succAbove))) =
    (downM F t).pull q ((resU F _).pull q (x (t ∘ k.succAbove)))
  rw [← hz]
  rfl

end Assemble

theorem cechH_fullSubcategory_H : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    (Q : ObjectProperty C) {ι : Type} (W : ι → ObjectProperty C), (∀ α, W α ≤ Q) → ∀ q p,
    Nonempty ((cechH (Q.ι ⋙ F) (fun α (T : Q.FullSubcategory) => W α T.obj) q).cx.H p ≃ₗ[R] (cechH F W q).cx.H p) := by
  intro R _ C _ F Q ι W hW q p
  exact ⟨equivH (cosHom (upX F hW q) (upX_δ F hW q)) (cosHom (downX (Q := Q) F q) (downX_δ F q))
    (fun n x => funext fun i => pull_pull_of_inv (upM F hW i) (downM F i) (down_up_pullC F hW i) q (x i))
    (fun n x => funext fun i => pull_pull_of_inv (downM F i) (upM F hW i) (up_down_pullC F hW i) q (x i)) p⟩

end GlobalTheory.CompanionTheory.CechFull
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeRepExact

universe v u

section Gen

variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def Rp {j : ℕ} (y : CH.Cn (sq a b) j) (z : CH.Cn (CH.modF A) j) : Prop :=
  ∀ s, (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) (show A.obj _ from z s)

variable {a b}

theorem sqMap_val {T T' : D} (φ : T ⟶ T') (w : sqM a b T) (x : A.obj T) (h : w.1 = Ideal.Quotient.mk (b.S T) x) :
    (sqMap a b φ w).1 = Ideal.Quotient.mk (b.S T') ((A.map φ).hom x) := by
  obtain ⟨w, hw⟩ := w
  obtain rfl : w = _ := h
  rfl

theorem Rp.d {j : ℕ} {y : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) :
    Rp a b (CH.d _ j y) (CH.d _ j z) := by
  intro s
  change (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • sqMap a b (toLast i s) (y (face i s)) : sqM a b _).1 =
    Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (z (face i s)))

  rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s) (y (face i s))).1 = _
  rw [sqMap_val _ _ _ (h (face i s))]

theorem Rp.sub {j : ℕ} {y y' : CH.Cn (sq a b) j} {z z' : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z') :
    Rp a b (y - y') (z - z') := by
  intro s
  change (show sqM a b _ from y s).1 - (show sqM a b _ from y' s).1 =
    Ideal.Quotient.mk _ ((show A.obj _ from z s) - (show A.obj _ from z' s))
  rw [map_sub, h s, h' s]

theorem Rp.unique {j : ℕ} {y y' : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z) :
    y = y' :=
  funext fun s => Subtype.ext ((h s).trans (h' s).symm)

theorem Rp.mem {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : Rp a b 0 z) (s) : z s ∈ b.S _ :=
  (Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).1 (h s).symm

theorem Rp.zero {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : ∀ s, z s ∈ b.S _) : Rp a b 0 z := fun s =>
  ((Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).2 (h s)).symm

theorem exists_rp {j : ℕ} (z : CH.Cn (CH.modF A) j) (hz : ∀ s, z s ∈ a.S _) : ∃ y, Rp a b y z :=
  ⟨fun s => sqMk a b (show A.obj _ from z s) (hz s), fun _ => rfl⟩

theorem exists_lift {j : ℕ} (y : CH.Cn (sq a b) j) : ∃ z : CH.Cn (CH.modF A) j, (∀ s, z s ∈ a.S _) ∧ Rp a b y z := by
  have key : ∀ s : ComposableArrows D j, ∃ x : A.obj (s.obj (Fin.last j)), x ∈ a.S _ ∧
      (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) x := fun s => by
    obtain ⟨x, hx, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from y s).2
    exact ⟨x, hx, e.symm⟩
  choose z hz hr using key
  exact ⟨z, hz, hr⟩

theorem exists_of_mem_B {n : ℕ} {w : CH.Cn (sq a b) n} {z : CH.Cn (CH.modF A) n} (hr : Rp a b w z)
    (hw : w ∈ (CH.cx (sq a b)).B n) : ∃ e : CH.Cn (CH.modF A) n, (∀ s, e s ∈ b.S _) ∧ CH.d _ n z = CH.d _ n e := by
  cases n with
  | zero =>
    have h0 : w = 0 := hw
    subst h0
    exact ⟨z, hr.mem, rfl⟩
  | succ n =>
    obtain ⟨t, rfl⟩ := hw
    obtain ⟨g, -, hg⟩ := exists_lift t
    have h0 : Rp a b 0 (z - CH.d _ n g) := by
      have := hr.sub hg.d
      rwa [sub_self] at this
    refine ⟨_, h0.mem, ?_⟩
    rw [map_sub, CH.d_d, sub_zero]

end Gen

section Cls

variable {R : Type} [CommRing R]

theorem sub_mem_B (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (e : K.cls x hx = K.cls y hy) :
    x - y ∈ K.B n :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).1 e

theorem cls_eq_of_sub_mem (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (h : x - y ∈ K.B n) :
    K.cls x hx = K.cls y hy :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).2 h

end Cls

section Res

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R}

theorem Rp.res (a b : IdF A) {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} {y : CH.Cn (sq (a.res U.ι) (b.res U.ι)) j}
    {z : CH.Cn (CH.modF (U.ι ⋙ A)) j} (hr : Rp _ _ y z) :
    Rp (a.res V.ι) (b.res V.ι) ((resU (sq a b) h).pullC j y) ((resU (CH.modF A) h).pullC j z) := fun s =>
  hr (s ⋙ ObjectProperty.ιOfLE h)

end Res

theorem exact_lift : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {U V : ObjectProperty C} (h : V ≤ U) (n : ℕ),
    Function.Surjective ((resU (gr Fil n) h).pull n) →
    ∀ (f : CH.Cn (CH.modF (V.ι ⋙ Φ.A)) n), (∀ σ, f σ ∈ (Fil n).S _) → (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) →
    ∃ f' : CH.Cn (CH.modF (U.ι ⋙ Φ.A)) n, (∀ σ, f' σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f' σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      ∀ (x : HU (gr Fil ((n : ℤ) + 1)) V (n + 1)) (x' : HU (gr Fil ((n : ℤ) + 1)) U (n + 1)),
        Rep ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι) (CH.d _ n f) x →
        Rep ((Fil ((n : ℤ) + 1)).res U.ι) ((Fil ((n : ℤ) + 1 + 1)).res U.ι) (CH.d _ n f') x' →
        x = (resU (gr Fil ((n : ℤ) + 1)) h).pull (n + 1) x' := by
  intro R _ C _ Φ Fil hF U V h n hs f hf hdf
  obtain ⟨y, hy⟩ := exists_rp (a := (Fil n).res V.ι) (b := (Fil ((n : ℤ) + 1)).res V.ι) f hf
  have hdy : CH.d _ n y = 0 := hy.d.unique (Rp.zero hdf)
  obtain ⟨c', hc'⟩ := hs ((CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι))).cls y hdy)
  obtain ⟨⟨y', hy'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  obtain ⟨f', hf'a, hf'⟩ := exists_lift (a := (Fil n).res U.ι) (b := (Fil ((n : ℤ) + 1)).res U.ι)
    (show CH.Cn (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n from y')
  have hdy' : CH.d (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n y' = 0 := hy'
  have hz : CH.d (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)) n ((resU (gr Fil n) h).pullC n y') = 0 :=
    ((resU (gr Fil n) h).hom.mapZ n ⟨y', hy'⟩).2
  have hB := sub_mem_B (CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)))
    (x := (resU (gr Fil n) h).pullC n y') (y := y) hz hdy hc'
  refine ⟨f', hf'a, ?_, ?_⟩
  · have := hf'.d
    rw [hdy'] at this
    exact this.mem
  · rintro x x' ⟨u, hu, rfl, hur⟩ ⟨u', hu', rfl, hur'⟩
    have hur1 : Rp _ _ u (CH.d _ n f) := hur
    have hur2 : Rp _ _ u' (CH.d _ n f') := hur'
    have hw := (Rp.res (Fil n) (Fil ((n : ℤ) + 1)) h hf').sub hy
    obtain ⟨e, he, hde⟩ := exists_of_mem_B hw hB
    obtain ⟨t, ht⟩ := exists_rp (a := (Fil ((n : ℤ) + 1)).res V.ι) (b := (Fil ((n : ℤ) + 1 + 1)).res V.ι) e he
    have h1 := (Rp.res (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) h hur2).sub hur1
    have e1 : (resU (CH.modF Φ.A) h).pullC (n + 1) (CH.d (CH.modF (U.ι ⋙ Φ.A)) n f') =
        CH.d (CH.modF (V.ι ⋙ Φ.A)) n ((resU (CH.modF Φ.A) h).pullC n f') :=
      ((resU (CH.modF Φ.A) h).d_pullC n f').symm
    rw [e1, ← map_sub, hde] at h1
    have h2 := h1.unique ht.d
    have hz' : CH.d (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)) (n + 1)
        ((resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') = 0 :=
      ((resU (gr Fil ((n : ℤ) + 1)) h).hom.mapZ (n + 1) ⟨u', hu'⟩).2
    exact (cls_eq_of_sub_mem (CH.cx (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)))
      (x := (resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') (y := u) hz' hu ⟨t, h2.symm⟩).symm

end GlobalTheory.CompanionTheory.ConeRepExact
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.finite_length_of_lseq_first : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  first | exact @GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | exact GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | (intros; apply GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level <;> assumption)
end
