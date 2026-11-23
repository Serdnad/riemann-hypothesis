module

public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics

theorem valS_congr_supp {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S S' L : Set ι)
    (A : MvPolynomial (ι × Fin n) R) (hA : A ∈ supported R {v : ι × Fin n | v.1 ∈ L})
    (h : ∀ y ∈ L, y ∈ S ↔ y ∈ S') : valS LL S A = valS LL S' A := by
  unfold valS sDegs
  have ht : twistSub LL S (lastIdx n) A = twistSub LL S' (lastIdx n) A := by
    unfold twistSub
    simp only [MvPolynomial.coe_eval₂Hom]
    apply MvPolynomial.eval₂_congr
    intro v c hv hc
    have hvL : v.1 ∈ L := (MvPolynomial.mem_supported.mp hA)
      ((MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨c, MvPolynomial.mem_support_iff.mpr hc, hv⟩)
    by_cases hS : v.1 ∈ S
    · have hS' : v.1 ∈ S' := (h v.1 hvL).mp hS
      simp only [hS, hS', if_true]
    · have hS' : v.1 ∉ S' := fun h' => hS ((h v.1 hvL).mpr h')
      simp only [hS, hS', if_false]
  rw [ht]

theorem sl_le_g2mg (p n' : ℕ) [NeZero n'] (r K : ℕ) (F : Frames n' r) (deg : Fin n' → ℕ) (mS : ℕ) (Y : ℝ) (j x : ℤ) :
    (mS : ℤ) + sl p F deg Y (r + K) j x ≤ g2mg p n' r K F deg mS Y j x := by
  unfold sl g2mg Bo levDeg
  rw [show Y * (((r + K : ℕ) : ℝ)) ^ 2 = (((r + K : ℕ) : ℝ)) ^ 2 * Y from mul_comm _ _]
  have h1 := Int.self_le_toNat
    ⌊(deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) / ((((r + K : ℕ) : ℝ)) ^ 2 * Y)⌋
  rw [Int.floor_toNat] at h1
  omega

section Geo

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

private theorem false_of_mem_between_adjacent_of_pairwise_lt (L : List ℤ) (hs : L.Pairwise (· < ·)) (a b : ℕ) (hb : b < L.length)
    (hab : b = a + 1) (y : ℤ) (hy : y ∈ L) (h1 : L[a]'(by omega) < y) (h2 : y < L[b]) : False := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hy
  have hp := List.pairwise_iff_getElem.1 hs
  rcases Nat.lt_or_ge k b with h | h
  · rcases Nat.lt_or_ge k a with h' | h'
    · exact lt_asymm h1 (hp k a hk (by omega) h')
    · have : k = a := by omega
      subst this
      exact lt_irrefl _ h1
  · rcases Nat.lt_or_ge b k with h' | h'
    · exact lt_asymm h2 (hp b k hb hk h')
    · have : k = b := by omega
      subst this
      exact lt_irrefl _ h2

private theorem false_of_mem_gt_last_of_pairwise_lt (L : List ℤ) (hs : L.Pairwise (· < ·)) (a : ℕ) (ha : a + 1 = L.length)
    (y : ℤ) (hy : y ∈ L) (h1 : L[a]'(by omega) < y) : False := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hy
  have hp := List.pairwise_iff_getElem.1 hs
  rcases Nat.lt_or_ge k a with h | h
  · exact lt_asymm h1 (hp k a hk (by omega) h)
  · have : k = a := by omega
    subst this
    exact lt_irrefl _ h1

theorem le_pred_iff (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (h1 : 1 ≤ u) (hu : u < (Fr.LLset j).card + r)
    (y : ℤ) (hy : y ∈ Fr.letters j) :
    y ≤ posU Fr (Fr.LLset j).card j (u - 1) ↔ y < posU Fr (Fr.LLset j).card j u := by
  classical
  obtain ⟨hJ, hper, hmono, hgap, hpos, hnot, hLL, hN1, hold⟩ := hV
  set N := (Fr.LLset j).card with hNdef
  set L := (Fr.LLset j).sort (· ≤ ·) with hLdef
  have hLlen : L.length = N := Finset.length_sort _
  have hsorted : L.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have hNr : r ≤ N := (hLL j).1
  have hLpos : ∀ k (hk : k < N), llPos Fr j k = L[k]'(by omega) := fun k hk => by
    unfold llPos
    rw [← hLdef, List.getD_eq_getElem]
  have hLmem : ∀ k (hk : k < N), L[k]'(by omega) ∈ Fr.LLset j := fun k hk =>
    (Finset.mem_sort _).1 (List.getElem_mem _)
  have hLLb : ∀ z ∈ Fr.LLset j, Fr.fr (j - 1) (r - 1) < z ∧ z < Fr.fr j 0 := fun z hz =>
    Finset.mem_Ioo.1 (Finset.mem_filter.1 hz).1
  have hinLL : ∀ z ∈ Fr.letters j, Fr.fr (j - 1) (r - 1) < z → z < Fr.fr j 0 → z ∈ Fr.LLset j :=
    fun z hz h1 h2 => Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨h1, h2⟩, (Finset.mem_filter.1 hz).2⟩
  have key : posU Fr N j (u - 1) < posU Fr N j u ∧
      ∀ z ∈ Fr.letters j, posU Fr N j (u - 1) < z → z < posU Fr N j u → False := by
    by_cases hu1 : u < N
    · have hpu : posU Fr N j u = L[u]'(by omega) := by
        unfold posU
        rw [if_pos hu1, hLpos u hu1]
      have hpu1 : posU Fr N j (u - 1) = L[u - 1]'(by omega) := by
        unfold posU
        rw [if_pos (by omega), hLpos (u - 1) (by omega)]
      rw [hpu, hpu1]
      refine ⟨List.pairwise_iff_getElem.1 hsorted _ _ _ _ (by omega), fun z hz hz1 hz2 => ?_⟩
      have hzLL := hinLL z hz (lt_trans (hLLb _ (hLmem (u - 1) (by omega))).1 hz1)
        (lt_trans hz2 (hLLb _ (hLmem u hu1)).2)
      exact false_of_mem_between_adjacent_of_pairwise_lt L hsorted (u - 1) u (by omega) (by omega) z ((Finset.mem_sort _).2 hzLL) hz1 hz2
    · by_cases hu2 : u = N
      · have hpu : posU Fr N j u = Fr.fr j 0 := by
          unfold posU
          rw [if_neg hu1, show u - N = 0 by omega]
        have hpu1 : posU Fr N j (u - 1) = L[u - 1]'(by omega) := by
          unfold posU
          rw [if_pos (by omega), hLpos (u - 1) (by omega)]
        rw [hpu, hpu1]
        refine ⟨(hLLb _ (hLmem (u - 1) (by omega))).2, fun z hz hz1 hz2 => ?_⟩
        have hzLL := hinLL z hz (lt_trans (hLLb _ (hLmem (u - 1) (by omega))).1 hz1) hz2
        exact false_of_mem_gt_last_of_pairwise_lt L hsorted (u - 1) (by omega) z ((Finset.mem_sort _).2 hzLL) hz1
      · have hpu : posU Fr N j u = Fr.fr j (u - N) := by
          unfold posU
          rw [if_neg hu1]
        have hpu1 : posU Fr N j (u - 1) = Fr.fr j (u - 1 - N) := by
          unfold posU
          rw [if_neg (by omega)]
        rw [hpu, hpu1]
        have hi : u - 1 - N + 1 = u - N := by omega
        have hir : u - 1 - N + 1 < r := by omega
        refine ⟨by rw [← hi]; exact hmono j _ hir, fun z hz hz1 hz2 => ?_⟩
        exact hnot j (u - 1 - N) z hir hz1 (by rw [hi]; exact hz2) (Finset.mem_filter.1 hz).2
  constructor
  · intro hle
    exact lt_of_le_of_lt hle key.1
  · intro hlt
    by_contra hgt
    push_neg at hgt
    exact key.2 y hy hgt hlt

theorem oldest_pred (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (h1 : 1 ≤ u) (hu : u < (Fr.LLset j).card + r)
    (hodd : ¬ Even (posU Fr (Fr.LLset j).card j (u - 1))) :
    Fr.oldest j (posU Fr (Fr.LLset j).card j (u - 1)) = Fr.oldest j (posU Fr (Fr.LLset j).card j u) := by
  have hfilt : (Fr.letters j).filter (fun z => Even z ∧ z < posU Fr (Fr.LLset j).card j (u - 1)) =
      (Fr.letters j).filter (fun z => Even z ∧ z < posU Fr (Fr.LLset j).card j u) := by
    apply Finset.filter_congr
    intro z hz
    have hiff := le_pred_iff hV hr j u h1 hu z hz
    constructor
    · rintro ⟨he, hlt⟩
      exact ⟨he, hiff.1 hlt.le⟩
    · rintro ⟨he, hlt⟩
      refine ⟨he, lt_of_le_of_ne (hiff.2 hlt) ?_⟩
      rintro rfl
      exact hodd he
  simp only [Frames.oldest, hfilt]

end Geo

theorem restTh : RestTh := by
  intro p n' r K _ _ _ O _ Fr L₁ N₁ hV deg Y mS J _ nL hJ hnL j A G M hA hc ka hN u hu
  have hr : 1 ≤ r := NeZero.pos r
  have e := hnL j
  unfold thStar
  simp only [e] at hu hN ⊢
  obtain ⟨hxm, hxw⟩ := posU_mem' hV hr (segZ j) u hu
  obtain ⟨c1, c2, c3⟩ := hc _ hxm hxw
  intro k hk
  have hB : Bo p Fr deg (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) / 2 ≤ (k : ℝ) := c3 k hk
  refine max_le hB (max_le ?_ ?_)
  · split_ifs with h1
    · obtain ⟨d1, d2⟩ := c1 h1
      have k1 := (hN u hu _).2 d1
      rw [hk] at d2
      have d3 := WithTop.coe_le_coe.1 d2
      have s1 := sl_le_g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u)
      have : ka j (u + 1) 0 + (mS : ℤ) + sl p Fr deg Y (r + K) (segZ j)
          (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) ≤ k := by linarith
      exact_mod_cast this
    · exact hB
  · split_ifs with h2
    · obtain ⟨h21, h22⟩ := h2
      obtain ⟨hxm', hxw'⟩ := posU_mem' hV hr (segZ j) (u - 1) (by omega)
      obtain ⟨-, c2', -⟩ := hc _ hxm' hxw'
      obtain ⟨d1, d2⟩ := c2' h22
      have k1 := (hN (u - 1) (by omega) _).1 d1
      have ev : valS LZ {y | y ≤ posU Fr (Fr.LLset (segZ j)).card (segZ j) (u - 1)} A =
          valS LZ {y | y < posU Fr (Fr.LLset (segZ j)).card (segZ j) u} A :=
        valS_congr_supp LZ _ _ {y | y ∈ Fr.letters (segZ j)} A hA
          (fun y hy => le_pred_iff hV hr (segZ j) u h21 hu y hy)
      rw [ev, hk] at d2
      have d3 := WithTop.coe_le_coe.1 d2
      have s1 := sl_le_g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u)
      have eo := oldest_pred hV hr (segZ j) u h21 hu h22
      have eg : g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) (u - 1)) =
          g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) := by
        unfold g2mg
        rw [eo]
      rw [eg] at d3
      have : ka j (u - 1) 0 + (mS : ℤ) + sl p Fr deg Y (r + K) (segZ j)
          (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) ≤ k := by linarith
      exact_mod_cast this
    · exact hB

end Formalism.MainNotions.PairMembershipBlocks
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks.T5

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.PairMembershipBlocks

section Lin

variable {σ τ Kf : Type} [Field Kf]

theorem tens_monomial (mo : σ →₀ ℕ) (c : Kf) (G : MvPolynomial τ Kf) :
    tens (monomial mo c) G = monomial mo (c • G) := by
  unfold tens
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

def tensH (G : MvPolynomial τ Kf) (mo : σ →₀ ℕ) : Kf →+ MvPolynomial σ (MvPolynomial τ Kf) where
  toFun c := monomial mo (c • G)
  map_zero' := by simp
  map_add' c c' := by rw [add_smul, map_add (f := _)]

theorem tens_add_left (A A' : MvPolynomial σ Kf) (G : MvPolynomial τ Kf) :
    tens (A + A') G = tens A G + tens A' G :=
  sumSupp_add (tensH G) A A'

theorem tens_add_right (A : MvPolynomial σ Kf) (G G' : MvPolynomial τ Kf) :
    tens A (G + G') = tens A G + tens A G' := by
  unfold tens
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [smul_add, map_add (f := _)]

theorem tens_zero_left (G : MvPolynomial τ Kf) : tens (0 : MvPolynomial σ Kf) G = 0 := by simp [tens]

theorem tens_zero_right (A : MvPolynomial σ Kf) : tens A (0 : MvPolynomial τ Kf) = 0 := by simp [tens]

theorem compD_add {ι : Type} {s : ℕ} (d : ι → ℕ) (H H' : MvPolynomial (ι × Fin s) Kf) :
    compD d (H + H') = compD d H + compD d H' :=
  sumFilt_add (fun mo => ∀ x, multideg mo x = d x) (fun mo => (monomial mo : Kf →ₗ[Kf] _).toAddMonoidHom) H H'

theorem compD_zero {ι : Type} {s : ℕ} (d : ι → ℕ) : compD d (0 : MvPolynomial (ι × Fin s) Kf) = 0 := by simp [compD]

theorem compD_monomial {ι : Type} {s : ℕ} (d : ι → ℕ) (mo : ι × Fin s →₀ ℕ) (c : Kf) :
    compD d (monomial mo c) = if (∀ x, multideg mo x = d x) then monomial mo c else 0 := by
  unfold compD
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl]
    · rw [Finset.sum_empty]

theorem add_expand {R M : Type*} [CommSemiring R] [AddCommMonoid M] (f : MvPolynomial σ R → M) (h0 : f 0 = 0)
    (hadd : ∀ x y, f (x + y) = f x + f y) (P : MvPolynomial σ R) :
    f P = ∑ a ∈ P.support, f (monomial a (P.coeff a)) := by
  have h := map_sum (AddMonoidHom.mk ⟨f, h0⟩ hadd) (fun a => monomial a (P.coeff a)) P.support
  conv_lhs => rw [P.as_sum]
  exact h

end Lin

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem monomialSubstitution_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levP Fr p hk nL (F + G) = levP Fr p hk nL F + levP Fr p hk nL G :=
  sumSupp_add (fun mo => (monomial (plMon Fr p hk nL mo) : KK O →ₗ[KK O] _).toAddMonoidHom) F G

theorem levN_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levN Fr p hk nL (F + G) = levN Fr p hk nL F + levN Fr p hk nL G :=
  sumSupp_add (fun mo => (monomial (noMon Fr p hk nL mo) : KK O →ₗ[KK O] _).toAddMonoidHom) F G

theorem monomialSubstitution_zero : levP Fr p hk nL (0 : MvPolynomial (TV n' (m + 1)) (KK O)) = 0 := by simp [levP]

theorem levN_zero : levN Fr p hk nL (0 : MvPolynomial (TV n' (m + 1)) (KK O)) = 0 := by simp [levN]

theorem monomialSubstitution_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levP Fr p hk nL (monomial mo c) = monomial (plMon Fr p hk nL mo) c := by
  unfold levP
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem levN_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levN Fr p hk nL (monomial mo c) = monomial (noMon Fr p hk nL mo) c := by
  unfold levN
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem levImg_monomial (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (c : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial mo c) =
      if InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo then
        monomial (plMon Fr p hk nL mo) (monomial (noMon Fr p hk nL mo) c) else 0 := by
  unfold levImg
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl]
    · rw [Finset.sum_empty]

theorem inBlock_iff (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ) :
    InBlock Fr p hk nL dPl dNo mo ↔
      (∀ x, multideg (plMon Fr p hk nL mo) x = dPl x) ∧ ∀ x, multideg (noMon Fr p hk nL mo) x = dNo x := by
  unfold InBlock multideg plMon noMon
  simp only [Finsupp.coe_equivFunOnFinite_symm]

theorem plMon_eq_zero (mo : TV n' (m + 1) →₀ ℕ) (h : ∀ x a, mo (plVar Fr hk nL x a) = 0) :
    plMon Fr p hk nL mo = 0 := by
  ext v
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply, h, Nat.zero_div]

theorem noMon_eq_zero (mo : TV n' (m + 1) →₀ ℕ) (h : ∀ x b, mo (noVar Fr hk nL x b) < lowP Fr p x) :
    noMon Fr p hk nL mo = 0 := by
  ext v
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
  exact Nat.div_eq_of_lt (h v.1 v.2)

theorem lev_term (hp : 0 < p) (base d b : TV n' (m + 1) →₀ ℕ) (hd : LowDiv Fr p hk nL d)
    (hd0 : ∀ x c, d (noVar Fr hk nL x c) = 0) (hb : LowDiv Fr p hk nL b) (hb0 : ∀ x a, b (plVar Fr hk nL x a) = 0)
    (hbase : ∀ x c, base (noVar Fr hk nL x c) < lowP Fr p x)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (u v : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial (base + d) u * monomial b v) =
      if InLow Fr p hk nL rho base then
        tens (compD dPl (levP Fr p hk nL (monomial (base + d) u))) (compD dNo (levN Fr p hk nL (monomial b v)))
      else 0 := by
  have e1 : InLow Fr p hk nL rho (base + d + b) ↔ InLow Fr p hk nL rho base := by
    rw [add_assoc]
    exact inLow_add Fr p hk nL rho base (d + b) (lowDiv_add Fr p hk nL hd hb)
  have e2 : plMon Fr p hk nL (base + d + b) = plMon Fr p hk nL (base + d) := by
    rw [plMon_add Fr p hk nL hp _ _ hb, plMon_eq_zero Fr p hk nL b hb0, add_zero]
  have e3 : noMon Fr p hk nL (base + d + b) = noMon Fr p hk nL b := by
    rw [noMon_add Fr p hk nL hp _ _ hb, noMon_eq_zero Fr p hk nL (base + d), zero_add]
    intro x c
    rw [Finsupp.add_apply, hd0, add_zero]
    exact hbase x c
  rw [monomial_mul, levImg_monomial, monomialSubstitution_monomial, levN_monomial, compD_monomial, compD_monomial, inBlock_iff, e1, e2,
    e3]
  by_cases h1 : InLow Fr p hk nL rho base
  · rw [if_pos h1]
    by_cases h2 : ∀ x, multideg (plMon Fr p hk nL (base + d)) x = dPl x
    · by_cases h3 : ∀ x, multideg (noMon Fr p hk nL b) x = dNo x
      · rw [if_pos ⟨h1, h2, h3⟩, if_pos h2, if_pos h3, tens_monomial, smul_monomial, smul_eq_mul]
      · rw [if_neg (fun h => h3 h.2.2), if_neg h3, tens_zero_right]
    · rw [if_neg (fun h => h2 h.2.1), if_neg h2, tens_zero_left]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

theorem lev_mul (hp : 0 < p) (base : TV n' (m + 1) →₀ ℕ) (P Q : MvPolynomial (TV n' (m + 1)) (KK O))
    (hP : ∀ a ∈ P.support, ∃ d, LowDiv Fr p hk nL d ∧ (∀ x c, d (noVar Fr hk nL x c) = 0) ∧ a = base + d)
    (hQ : ∀ b ∈ Q.support, LowDiv Fr p hk nL b ∧ ∀ x a, b (plVar Fr hk nL x a) = 0)
    (hbase : ∀ x c, base (noVar Fr hk nL x c) < lowP Fr p x)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) :
    levImg Fr p hk nL rho dPl dNo (P * Q) =
      if InLow Fr p hk nL rho base then
        tens (compD dPl (levP Fr p hk nL P)) (compD dNo (levN Fr p hk nL Q))
      else 0 := by
  have hL : levImg Fr p hk nL rho dPl dNo (P * Q) = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * monomial b (Q.coeff b)) := by
    rw [add_expand (fun X => levImg Fr p hk nL rho dPl dNo (X * Q)) (by simp [levImg_zero])
      (fun x y => by simp only [add_mul, levImg_add]) P]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact add_expand (fun Y => levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * Y)) (by simp [levImg_zero])
      (fun x y => by simp only [mul_add, levImg_add]) Q
  have hR : tens (compD dPl (levP Fr p hk nL P)) (compD dNo (levN Fr p hk nL Q)) = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
        (compD dNo (levN Fr p hk nL (monomial b (Q.coeff b)))) := by
    rw [add_expand (fun X => tens (compD dPl (levP Fr p hk nL X)) (compD dNo (levN Fr p hk nL Q)))
      (by simp only [monomialSubstitution_zero, compD_zero, tens_zero_left])
      (fun x y => by simp only [monomialSubstitution_add, compD_add, tens_add_left]) P]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact add_expand (fun Y => tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
      (compD dNo (levN Fr p hk nL Y))) (by simp only [levN_zero, compD_zero, tens_zero_right])
      (fun x y => by simp only [levN_add, compD_add, tens_add_right]) Q
  have hterm : ∀ a ∈ P.support, ∀ b ∈ Q.support,
      levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * monomial b (Q.coeff b)) =
        if InLow Fr p hk nL rho base then
          tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
            (compD dNo (levN Fr p hk nL (monomial b (Q.coeff b))))
        else 0 := by
    intro a ha b hb
    obtain ⟨d, hd, hd0, rfl⟩ := hP a ha
    exact lev_term Fr p hk nL hp base d b hd hd0 (hQ b hb).1 (hQ b hb).2 hbase rho dPl dNo _ _
  rw [hL]
  split_ifs with h
  · rw [hR]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [hterm a ha b hb, if_pos h]
  · refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [hterm a ha b hb, if_neg h]

end Lev

end Formalism.MainNotions.PairMembershipBlocks.T5
end
end
