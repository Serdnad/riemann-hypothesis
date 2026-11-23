module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem vandermondeOf_succ {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) :
    vandermondeOf v =
      (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ) := by
  have key : ∀ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (v i - v j) =
      ∏ j : Fin (n + 1), if i < j then v i - v j else 1 := by
    intro i
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  unfold vandermondeOf
  simp only [key]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_lt_succ_iff, Fin.not_lt_zero, if_false, one_mul]
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

theorem numStandardTable_zero (m : ℕ) : numStandardTable (fun _ : Fin m => (0 : ℕ)) = 1 := by
  have hc : youngCells (fun _ : Fin m => (0 : ℕ)) = ∅ := by
    ext c
    simp [youngCells]
  have : IsEmpty (youngCells (fun _ : Fin m => (0 : ℕ))) :=
    ⟨fun p => by simpa [hc] using p.2⟩
  have : IsEmpty (Fin (youngCells (fun _ : Fin m => (0 : ℕ))).card) := by
    rw [hc]
    exact Fin.isEmpty'
  unfold numStandardTable
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Equiv.ext fun p => isEmptyElim p)⟩,
    ⟨⟨Equiv.equivOfIsEmpty _ _, fun p => isEmptyElim p⟩⟩⟩

theorem prod_range_sub_eq_descFactorial (n l : ℕ) :
    ∏ j ∈ Finset.range l, (n - j) = n.descFactorial l := by
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, mul_comm]

theorem prod_fin_sub_eq_factorial (l : ℕ) : ∏ j : Fin l, (l - (j : ℕ)) = l.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun j => l - j) l,
    ← Finset.prod_range_reflect (fun j => l - j) l]
  have : ∀ j ∈ Finset.range l, l - (l - 1 - j) = j + 1 := by
    intro j hj
    have := Finset.mem_range.1 hj
    omega
  rw [Finset.prod_congr rfl this, Finset.prod_range_add_one_eq_factorial]

theorem vandermondeOf_add_const {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (c : R) :
    vandermondeOf (fun j => v j + c) = vandermondeOf v := by
  unfold vandermondeOf
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem numStandardTable_hookShape_succ (h : FrobeniusDimensionFormula.Statement) {k l : ℕ}
    (hlk : l < k) : numStandardTable (hookShape (l + 1) k l) = Nat.choose (k - 1) l := by
  have hanti : Antitone (hookShape (l + 1) k l) := by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    unfold hookShape
    split_ifs <;> omega
  have e0 : hookShape (l + 1) k l 0 + (l + 1 - 1 - ((0 : Fin (l + 1)) : ℕ)) = k := by
    simp [hookShape]
    omega
  have es : ∀ j : Fin l, hookShape (l + 1) k l j.succ + (l + 1 - 1 - ((j.succ : Fin (l + 1)) : ℕ)) =
      (0 + (l - 1 - (j : ℕ))) + 1 := by
    intro j
    have := j.isLt
    unfold hookShape
    rw [Fin.val_succ, if_neg (by omega), if_pos (by omega)]
    omega
  have hsum : ∑ i, hookShape (l + 1) k l i = k := by
    rw [Fin.sum_univ_succ]
    have hs1 : ∀ j : Fin l, hookShape (l + 1) k l j.succ = 1 := fun j => by
      have h1 := es j
      have h2 := j.isLt
      have h3 : ((j.succ : Fin (l + 1)) : ℕ) = j + 1 := Fin.val_succ j
      omega
    simp only [hs1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have := e0
    have hval : ((0 : Fin (l + 1)) : ℕ) = 0 := rfl
    omega
  have hf := h (l + 1) (hookShape (l + 1) k l) hanti
  simp only [vandermondeOf_succ, Fin.prod_univ_succ] at hf
  rw [e0, hsum] at hf
  simp only [es] at hf
  have hz := h l (fun _ => 0) antitone_const
  beta_reduce at hz
  rw [numStandardTable_zero] at hz
  simp only [Finset.sum_const_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at hz
  set V := vandermondeOf (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) with hV
  set P := ∏ j : Fin l, ((0 + (l - 1 - (j : ℕ))).factorial : ℚ) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  have hVP : V = P := by
    field_simp at hz
    exact hz.symm
  have hshift : vandermondeOf (fun j : Fin l => (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) = V := by
    rw [hV, ← vandermondeOf_add_const (fun j : Fin l => ((0 + (l - 1 - (j : ℕ)) : ℕ) : ℚ)) 1]
    congr 1
    funext j
    push_cast
    ring
  have hnum : ∏ j : Fin l, ((k : ℚ) - (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ) : ℚ)) =
      ((k - 1).descFactorial l : ℚ) := by
    rw [← prod_range_sub_eq_descFactorial, Nat.cast_prod,
      ← Finset.prod_range_reflect (fun j => ((k - 1 - j : ℕ) : ℚ)) l,
      ← Fin.prod_univ_eq_prod_range (fun j => ((k - 1 - (l - 1 - j) : ℕ) : ℚ)) l]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hden : ∏ j : Fin l, (((0 + (l - 1 - (j : ℕ))) + 1 : ℕ).factorial : ℚ) =
      (l.factorial : ℚ) * P := by
    rw [hP, ← prod_fin_sub_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := j.isLt
    rw [Nat.factorial_succ, Nat.cast_mul]
    congr 2
    omega
  rw [hnum, hshift, hden, hVP, Nat.descFactorial_eq_factorial_mul_choose] at hf
  have hk0 : ((k.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hl0 : ((l.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have : (numStandardTable (hookShape (l + 1) k l) : ℚ) = ((k - 1).choose l : ℚ) := by
    rw [hf]
    push_cast
    field_simp
  exact_mod_cast this

theorem HookTableauCount.proof (h : FrobeniusDimensionFormula.Statement) :
    HookTableauCount.Statement := by
  intro r k l hlk hlr
  rw [← YoungDiagramCombinatorics.numSYT_hookShape r k l hlr, YoungDiagramCombinatorics.numSYT_hookShape (l + 1) k l (by omega)]
  exact numStandardTable_hookShape_succ h hlk

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace RestBoundEq

def lieSign (bot b : Bool) (m : ℕ) : ℚ := if bot = b then (-1) ^ m else -1

theorem lieSign_cases (bot b : Bool) (m : ℕ) : lieSign bot b m = 1 ∨ lieSign bot b m = -1 := by
  unfold lieSign
  split_ifs
  · rcases neg_one_pow_eq_or ℚ m with h | h <;> simp [h]
  · right; rfl

theorem le_dimFl (f j k : ℕ) (hf : 1 ≤ f) : j + k ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 := by
  unfold IndefiniteRowSideFullHecke.RestTerms.dimFl
  have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
    rcases Nat.lt_or_ge (j + k) 2 with h | h
    · have : j + k - 1 = 0 := by omega
      simp [this]
    · rw [mul_comm (j + k)]; exact Nat.mul_le_mul_left _ h
  have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
  have h3 : (j + k) * (j + k - 1) / 2 ≤ f * ((j + k) * (j + k - 1) / 2) :=
    Nat.le_mul_of_pos_left _ hf
  omega

theorem lieClass_reduce (f j k : ℕ) (hf : 1 ≤ f) (bot : Bool)
    (I : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ) (hI : IndefiniteRowSideFullHecke.RestTerms.IsFlagIntegral f j k I)
    (Q : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ : ∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 - m))
    (σ : Fin f × Bool) (τ : Fin f) (m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ j + k) :
    I (IndefiniteRowSideFullHecke.RestTerms.lieClass f j k (m - 1) σ * Q τ m) =
      (lieSign bot σ.2 (m - 1) : ℝ) *
        I (IndefiniteRowSideFullHecke.RestTerms.smallPsum f j k bot (m - 1) σ.1 * Q τ m) := by
  have hD := le_dimFl f j k hf
  have hkill := hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega)
    (by convert hQ τ m (by omega) hmN using 1; omega)
  have hsplit : IndefiniteRowSideFullHecke.RestTerms.psumAt f j k (m - 1) σ.1 =
      (∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ (m - 1)) +
        ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ (m - 1) := by
    unfold IndefiniteRowSideFullHecke.RestTerms.psumAt
    exact Fin.sum_univ_add _
  rw [hsplit, add_mul, map_add (f := _)] at hkill
  obtain ⟨τ', b⟩ := σ
  rcases Nat.even_or_odd (m - 1) with he | ho
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, he.neg_pow] <;> linarith
  · cases bot <;> cases b <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.lieClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, lieSign, ho.neg_pow,
        Finset.sum_neg_distrib, neg_mul, map_neg] <;> linarith

theorem smallPowerSum_isHomogeneous (f r a : ℕ) (c : SmallBlock) (m : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c m τ).IsHomogeneous m := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  have h := (isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)).pow m
  rw [one_mul] at h
  exact h

theorem degPolynomial_isHomogeneous (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by
  have h1 := VandermondeOfHomogeneous.proof
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a))).mul hfib
  have hdeg : 1 * (f * (r * a)) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF

end RestBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

theorem CombStripSum.proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombSortShiftDistinct.Statement) (h4 : CombExtendWord.Statement) :
    CombStripSum.Statement := by
  classical
  intro m n q lam hlam hq
  set l : Fin m → ℕ := fun j => lam j + stair m j with hl
  have hAlt : IsAlt (alternantPsum m (List.replicate n 1)) := isAlt_vandermonde_mul_prod _
  have hl_inj : Function.Injective l := by
    intro a b hab
    simp only [hl, stair] at hab
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_trichotomy a b with h | h | h
    · have h' := hlam h.le
      have : (a : ℕ) < b := h
      omega
    · exact h
    · have h' := hlam h.le
      have : (b : ℕ) < a := h
      omega

  have key : ∀ i : Fin m, q ≤ l i → Function.Injective (Function.update l i (l i - q)) →
      ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i hqi hinj
    obtain ⟨σ, μ, hμ, hμle, hσ0⟩ := h2 m lam hlam q i hqi hinj
    have hσ : ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k := hσ0
    have hsum : ∑ k, lam k = ∑ k, μ k + q := by
      have e1 : ∑ k, (μ k + stair m k) = ∑ k, Function.update l i (l i - q) k := by
        rw [← Equiv.sum_comp σ (Function.update l i (l i - q))]
        exact Finset.sum_congr rfl fun k _ => (hσ k).symm
      have e4 : ∑ k, l k = ∑ k, lam k + ∑ k, stair m k := Finset.sum_add_distrib
      have e3 : ∀ k, l k = Function.update l i (l i - q) k + if k = i then q else 0 := by
        intro k
        by_cases hk : k = i
        · subst hk; simp only [Function.update_self, if_true]; omega
        · simp [hk]
      have e2 : ∑ k, l k = ∑ k, Function.update l i (l i - q) k + q := by
        rw [Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [Finset.sum_add_distrib] at e1
      omega
    obtain ⟨s, hs⟩ := h4 m n q μ lam hμ hlam hμle hsum
    refine ⟨μ, s, ⟨σ, hσ⟩, ?_, hs⟩
    have hu : Function.update l i (l i - q) = (fun k => μ k + stair m k) ∘ σ.symm := by
      funext k
      rw [Function.comp_apply, ← hσ (σ.symm k), Equiv.apply_symm_apply]
    rw [hu, cf_perm hAlt, abs_mul, h1 m n μ hμ]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
  have key' : ∀ i : Fin m, ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
      (q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) →
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i
    by_cases h : q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))
    · obtain ⟨μ, s, hs⟩ := key i h.1 h.2
      exact ⟨μ, s, fun _ => hs⟩
    · exact ⟨fun _ => 0, fun _ => i, fun h' => absurd h' h⟩
  choose μ s hμs using key'
  set S := univ.filter
    (fun i : Fin m => q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) with hS
  change ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) ≤ _
  have hsum_eq : ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) =
      ∑ i ∈ S, ((latticeWords n (μ i)).card : ℚ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hqi : q ≤ l i
    · by_cases hinj : Function.Injective (Function.update l i (l i - q))
      · rw [if_pos hqi, if_pos ⟨hqi, hinj⟩, (hμs i ⟨hqi, hinj⟩).2.1]
      · rw [if_pos hqi, if_neg (fun h => hinj h.2)]
        simp only [Function.Injective, not_forall] at hinj
        obtain ⟨a, b, hab, hne⟩ := hinj
        rw [cf_eq_zero_of_eq hAlt hne hab, abs_zero]
    · rw [if_neg hqi, if_neg (fun h => hqi h.1)]
  rw [hsum_eq]
  have hcard : ∑ i ∈ S, (latticeWords n (μ i)).card ≤ (latticeWords (n + q) lam).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun x => Fin.append x.2 (s x.1)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      exact (hμs x.1 (Finset.mem_filter.mp hx.1).2).2.2 x.2 hx.2
    · rintro ⟨i, w⟩ hx ⟨j, w'⟩ hy hxy
      rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
      simp only at hxy hx hy
      have hw : w = w' := by
        funext k
        have := congrFun hxy (Fin.castAdd q k)
        simpa only [Fin.append_left] using this
      subst hw
      have hμij : μ i = μ j := by
        funext k
        have a1 := (Finset.mem_filter.mp hx.2).2.2 k
        have a2 := (Finset.mem_filter.mp hy.2).2.2 k
        rw [← a1, ← a2]
      have hSi := (Finset.mem_filter.mp hx.1).2
      have hSj := (Finset.mem_filter.mp hy.1).2
      have hij : i = j := by
        by_contra hij
        obtain ⟨σ, hσ⟩ := (hμs i hSi).1
        obtain ⟨τ, hτ⟩ := (hμs j hSj).1
        refine h3 m l hl_inj q hq i j hij hSi.1 hSj.1 σ τ ?_
        funext k
        rw [Function.comp_apply, Function.comp_apply, hσ k, hτ k, hμij]
      subst hij
      rfl
  exact_mod_cast hcard

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho = cf (fun i => lam i + stair m i) (alternantPsum m rho) :=
  rfl

theorem CharacterBound.proof (h1 : CombTableEqWords.Statement) (h2 : CombCfBound.Statement) :
    CharacterBound.Statement := by
  intro m lam rho hlam hrho
  rw [symmetricGroupCharacter_eq_cf]
  refine (h2 m rho hrho lam hlam).trans ?_
  by_cases hs : ∑ i, lam i = rho.sum
  · rw [h1 m lam hlam, hs]
  · rw [latticeWords_eq_empty_of_sum_ne _ _ hs, Finset.card_empty, Nat.cast_zero]
    exact Nat.cast_nonneg _

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_lt_of_lt_of_eq {m n : ℕ} (w : Fin n → Fin m) {s t : Fin n} (hst : s < t)
    (i : Fin m) (hs : w s = i) : pcnt w s i < pcnt w t i := by
  unfold pcnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact ⟨Fin.lt_def.mp hst, hs⟩
    · simp
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 (Fin.lt_def.mp hst), hx.2⟩

theorem CombCellOfWordInj.proof : CombCellOfWordInj.Statement := by
  intro m n w s t h
  simp only [cellOfWord, Prod.mk.injEq] at h
  obtain ⟨hw, hc⟩ := h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w s) rfl
    rw [hc, hw] at this
    exact lt_irrefl _ (hw ▸ this)
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w t) rfl
    rw [← hc, ← hw] at this
    exact lt_irrefl _ (hw ▸ this)

end GroundTheory.Heights₂.Heights.RestTerms
end
