module

public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclint_degreeOf_none_rename_some {B : Type*} [CommRing B] {σ : Type*}
    (p : MvPolynomial σ B) : degreeOf none (rename (some : σ → Option σ) p) = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero ((degreeOf_le_iff).2 ?_)
  intro m hm
  rw [support_rename_of_injective (Option.some_injective σ)] at hm
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.1 hm
  exact (Finsupp.mapDomain_of_notMem_range m' none (by simp)).le

private theorem colAddGen_eq_rename_some_of_mem_dualWeyl {B : Type*} [CommRing B] {r n : ℕ}
    {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) B} (hf : f ∈ dualWeyl B r n ν)
    {l j : Fin n} (hlj : l < j) :
    colAddGen B l j f = rename some f := by
  unfold dualWeyl at hf
  rw [Submodule.mem_inf] at hf
  have h := hf.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply] at h
  exact sub_eq_zero.mp (h l j hlj)

theorem leadInterlaced_of (h1 : CompDeg) (h2 : LeadComp) (h3 : TwoColumn) : LeadInterlaced := by
  intro B _ _ r n ν f hf hf0
  intro l j hlj
  have hlt : l < j := Fin.lt_def.mpr (by omega)
  have hdeg : (colLex r n).degree
      (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f) =
      (colLex r n).degree f :=
    h2 B r n (Fin r × Fin n →₀ ℕ) (pairW (r := r) l j) f
  have hcoeff : AddMonoidAlgebra.coeff (weightedHomogeneousComponent (pairW (r := r) l j)
        (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f)
      ((colLex r n).degree f) =
      AddMonoidAlgebra.coeff f ((colLex r n).degree f) := by
    simp only [coeff_weightedHomogeneousComponent, ↓reduceIte]
  have hg0 : weightedHomogeneousComponent (pairW (r := r) l j)
      (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f ≠ 0 := by
    intro h
    have hne : AddMonoidAlgebra.coeff f ((colLex r n).degree f) ≠ 0 :=
      (colLex r n).coeff_degree_ne_zero_iff.mpr hf0
    apply hne
    rw [← hcoeff, h]
    rfl
  have hcol : degreeOf none (colAddGen B l j f) ≤ 0 := by
    rw [colAddGen_eq_rename_some_of_mem_dualWeyl hf hlt, lclint_degreeOf_none_rename_some]
  have hcomp := h1 B r n l j
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) 0 f hcol
  have hhom := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := pairW (r := r) l j)
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) f
  have key := h3 B r n l j hlt 0 0
    (Finsupp.weight (pairW (r := r) l j) ((colLex r n).degree f)) _ hg0 hhom
    (fun b hb => absurd hb (Nat.not_lt_zero _)) hcomp
  rw [hdeg] at key
  exact key

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

def lccompW {r n : ℕ} (l j : Fin n) : Option (Fin r × Fin n) → (Fin r × Fin n →₀ ℕ) :=
  fun o => match o with
    | none => 0
    | some v => pairW l j v

theorem lccomp_pairW_col {r n : ℕ} (l j : Fin n) (b : Fin r) :
    pairW (r := r) l j (b, l) = Finsupp.single (b, l) 1 := by
  unfold pairW
  split_ifs <;> rfl

theorem lccomp_image_var_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    IsWeightedHomogeneous (lccompW l j)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) (pairW l j v) := by
  split_ifs with h
  · refine IsWeightedHomogeneous.add (isWeightedHomogeneous_X B (lccompW l j) (some v)) ?_
    have hm := (isWeightedHomogeneous_X B (lccompW l j) none).mul
      (isWeightedHomogeneous_X B (lccompW l j) (some (v.1, l)))
    convert hm using 1
    show pairW l j v = 0 + pairW l j (v.1, l)
    rw [lccomp_pairW_col, zero_add]
    simp only [pairW, if_pos h]
  · exact isWeightedHomogeneous_X B (lccompW l j) (some v)

theorem lccomp_colAddGen_monomial_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (a : B) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j (monomial d a))
      (Finsupp.weight (pairW l j) d) := by
  classical
  have hp : IsWeightedHomogeneous (lccompW l j)
      (∏ v ∈ d.support, ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) ^ d v)
      (∑ v ∈ d.support, d v • pairW l j v) :=
    IsWeightedHomogeneous.prod _ _ _ fun v _ => (lccomp_image_var_homog l j v).pow _
  have hc : IsWeightedHomogeneous (lccompW l j) (C a : MvPolynomial (Option (Fin r × Fin n)) B) 0 :=
    isWeightedHomogeneous_C _ a
  have h := hc.mul hp
  rw [zero_add] at h
  rw [colAddGen, aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.weight_apply]
  exact h

theorem lccomp_colAddGen_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B)
    (hf : IsWeightedHomogeneous (pairW l j) f ω) :
    IsWeightedHomogeneous (lccompW l j) (colAddGen B l j f) ω := by
  classical

  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have h := lccomp_colAddGen_monomial_homog (B := B) l j d (AddMonoidAlgebra.coeff f d)
  rwa [hf (mem_support_iff.mp hd)] at h

theorem lccomp_sum_components {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (f : MvPolynomial σ R) (T : Finset M)
    (hT : ∀ d ∈ f.support, Finsupp.weight w d ∈ T) :
    f = ∑ ω' ∈ T, weightedHomogeneousComponent w ω' f := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hT d (mem_support_iff.mpr hne))

private lemma weightedHomogeneousComponent_self_of_isWH_ring {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hne
    exact hd (h (Ne.symm hne))

private lemma weightedHomogeneousComponent_eq_zero_of_ne_isWH {σ M R : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} {m n : M}
    {p : MvPolynomial σ R} (h : IsWeightedHomogeneous w p m) (hn : n ≠ m) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with hd
  · by_contra hne
    exact hn (hd.symm.trans (h hne))
  · rfl

theorem lccomp_component_colAddGen {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n)
    (ω : Fin r × Fin n →₀ ℕ) (f : MvPolynomial (Fin r × Fin n) B) :
    weightedHomogeneousComponent (lccompW l j) ω (colAddGen B l j f) =
      colAddGen B l j (weightedHomogeneousComponent (pairW l j) ω f) := by
  classical
  have hf := lccomp_sum_components (pairW l j) f (f.support.image (Finsupp.weight (pairW l j)))
    (fun d hd => Finset.mem_image_of_mem _ hd)
  conv_lhs => rw [hf]

  rw [map_sum, map_sum]
  by_cases hω : ω ∈ f.support.image (Finsupp.weight (pairW l j))
  · rw [Finset.sum_eq_single ω]
    · exact weightedHomogeneousComponent_self_of_isWH_ring
        (lccomp_colAddGen_homog l j ω _ (weightedHomogeneousComponent_isWeightedHomogeneous ω f))
    · intro b _ hb
      exact weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f))
        (Ne.symm hb)
    · intro h
      exact absurd hω h
  · rw [Finset.sum_eq_zero]
    · have h0 : weightedHomogeneousComponent (pairW l j) ω f = 0 := by
        ext d
        rw [coeff_weightedHomogeneousComponent]
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        split_ifs with h
        · by_contra hne
          exact hω (h ▸ Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
        · rfl
      rw [h0, map_zero]
    · intro b hb
      refine weightedHomogeneousComponent_eq_zero_of_ne_isWH
        (lccomp_colAddGen_homog l j b _ (weightedHomogeneousComponent_isWeightedHomogeneous b f)) ?_
      rintro rfl
      exact hω hb

theorem lccomp_degreeOf_component_le {R : Type*} [CommRing R] {σ M : Type*} [AddCommMonoid M]
    (w : σ → M) (ω : M) (p : MvPolynomial σ R) (i : σ) :
    degreeOf i (weightedHomogeneousComponent w ω p) ≤ degreeOf i p := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  apply monomial_le_degreeOf i
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact mem_support_iff.mpr hm
  · exact absurd rfl hm

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lcminor_initMinor_eq (R : Type) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    initMinor R I hs = ∑ σ : Equiv.Perm (Fin s),
      monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
        (((Equiv.Perm.sign σ : ℤ) : R)) := by
  rw [initMinor, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply]
  rw [← mul_one (((Equiv.Perm.sign σ : ℤ) : R)), ← C_mul_monomial, monomial_sum_one,
    Units.smul_def, zsmul_eq_mul]
  congr 1

theorem colLexInitMinor_of (h : MinorExpLt) : ColLexInitMinor := by
  intro R _ _ r n s I hs hI
  rw [lcminor_initMinor_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin s)))]
  simp only [Equiv.Perm.one_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one]
  set g := ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin s)),
    monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
      (((Equiv.Perm.sign σ : ℤ) : R)) with hg_def
  set e := ∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 with he
  have hdf : (colLex r n).degree (monomial e (1 : R)) = e := by
    classical
    rw [MonomialOrder.degree_monomial]
    simp
  by_cases hg : g = 0
  · rw [hg, add_zero, hdf, MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩
  · have hne : (Finset.univ.erase (1 : Equiv.Perm (Fin s))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      apply hg
      rw [hg_def, h0, Finset.sum_empty]
    have hlt : (colLex r n).toSyn ((colLex r n).degree g) <
        (colLex r n).toSyn ((colLex r n).degree (monomial e (1 : R))) := by
      rw [hdf]
      refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
      obtain ⟨σ0, hσ0⟩ := hne
      rw [Finset.sup_lt_iff (lt_of_le_of_lt bot_le (h r n s I hs hI σ0 (Finset.ne_of_mem_erase hσ0)))]
      intro σ hσ
      exact lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (h r n s I hs hI σ (Finset.ne_of_mem_erase hσ))
    rw [MonomialOrder.degree_add_of_lt hlt, MonomialOrder.leadingCoeff_add_of_lt hlt, hdf,
      MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem columnLexBideterminant_of_initialMinor (h : ColLexInitMinor) : ColumnLexBideterminant := by
  intro R _ _ r n K sz hsz I hI
  have hm : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      (colLex r n).leadingCoeff (initMinor R (I k) (hsz k)) = 1 :=
    fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).2
  have hreg : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      IsRegular ((colLex r n).leadingCoeff (initMinor R (I k) (hsz k))) := by
    intro k hk
    rw [hm k hk]
    exact isRegular_one
  refine ⟨?_, ?_⟩
  · unfold bideterminant bidetExp
    rw [MonomialOrder.degree_prod_of_regular hreg]
    exact Finset.sum_congr rfl fun k _ => (h R r n (sz k) (I k) (hsz k) (hI k)).1
  · unfold bideterminant
    rw [MonomialOrder.leadingCoeff_prod_of_regular hreg]
    exact Finset.prod_eq_one hm

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcssyt_shapeDeg_cons {n K : ℕ} (h : ℕ) (sz : Fin K → ℕ) (t : Fin n) :
    shapeDeg (Fin.cons h sz : Fin (K + 1) → ℕ) t = (if t.val < h then 1 else 0) + shapeDeg sz t := by
  unfold shapeDeg
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem lcssyt_consSz {n K h : ℕ} (hh : h ≤ n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) :
    ∀ k : Fin (K + 1), (Fin.cons h sz : Fin (K + 1) → ℕ) k ≤ n := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using hh
  · simpa using hsz i

def lcssyt_consI {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∀ k : Fin (K + 1), Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r :=
  fun k => Fin.cases (motive := fun k => Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r) c I k

theorem lcssyt_bidetExp_cons {r n K h : ℕ} (hh : h ≤ n) (c : Fin h → Fin r) (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    bidetExp (Fin.cons h sz : Fin (K + 1) → ℕ) (lcssyt_consSz hh sz hsz) (lcssyt_consI sz c I) =
      colExp c hh + bidetExp sz hsz I := by
  unfold bidetExp
  rw [Fin.sum_univ_succ]
  rfl

theorem lcssyt_consI_strictMono {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r)
    (hc : StrictMono c) (hI : ∀ k, StrictMono (I k)) : ∀ k, StrictMono (lcssyt_consI sz c I k) := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · exact hc
  · exact hI i

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem leadingComponent : LeadComp := by
  intro R _ r n M _ w f
  classical
  by_cases hf : f = 0
  · subst hf; simp
  have hd : (colLex r n).degree f ∈
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f).support := by
    rw [mem_support_iff, coeff_weightedHomogeneousComponent, if_pos rfl]
    exact (colLex r n).coeff_degree_ne_zero_iff.mpr hf
  have hg0 : weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f ≠ 0 := by
    intro h; rw [h] at hd; simp at hd
  have h1 := (colLex r n).le_degree hd
  have h2 : (colLex r n).toSyn ((colLex r n).degree
      (weightedHomogeneousComponent w (Finsupp.weight w ((colLex r n).degree f)) f)) ≤
      (colLex r n).toSyn ((colLex r n).degree f) := by
    apply (colLex r n).le_degree
    have h3 := (colLex r n).degree_mem_support hg0
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at h3
    split_ifs at h3 with h
    · exact mem_support_iff.mpr h3
    · exact absurd rfl h3
  exact (colLex r n).toSyn.injective (le_antisymm h2 h1)

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem evalDegree : EvalDeg := by
  intro B _ τ _ x y c _ _ _ p
  apply lcdeg_degreeOf_aeval_le
  intro m hm
  have hf : ∀ v, degreeOf c ((fun v : τ => if v = x then (1 : MvPolynomial τ B)
      else if v = y then -X c else X v) v) ≤ (if v = y then 1 else 0) + (if v = c then 1 else 0) := by
    intro v
    by_cases hvx : v = x
    · subst hvx
      simp only [if_true]
      have h1 : degreeOf c (1 : MvPolynomial τ B) = 0 := by rw [← C_1, degreeOf_C]
      rw [h1]
      exact Nat.zero_le _
    · by_cases hvy : v = y
      · subst hvy
        simp only [hvx, if_false, if_true, degreeOf_neg]
        have h2 := lcdeg_degreeOf_X_le (R := B) c c
        simp only [if_true] at h2
        omega
      · simp only [hvx, hvy, if_false, zero_add]
        exact lcdeg_degreeOf_X_le (R := B) c v
  refine le_trans (Finset.sum_le_sum (g := fun v => m v * (if v = y then 1 else 0) +
    m v * (if v = c then 1 else 0)) fun v _ => ?_) ?_
  · rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (hf v)
  · rw [Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq]
    have hy := monomial_le_degreeOf y hm
    have hc := monomial_le_degreeOf c hm
    split_ifs <;> omega

end Formalism.GradedWeylDivisibility
end
end
