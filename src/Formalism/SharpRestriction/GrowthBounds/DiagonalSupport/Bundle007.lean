module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ThresholdGeOddPosition
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeOfOneLeMul
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle002
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundJoint
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Ord2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem posU_lt_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a < posU Fr N j b ↔ a < b := by
  subst hN; exact posU_lt_iff hV j a b ha hb

theorem posU_le_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a ≤ posU Fr N j b ↔ a ≤ b := by
  subst hN; exact posU_le_iff hV j a b ha hb

theorem posU_ll' (j : ℤ) (N : ℕ) (l : ℕ) (hl : l < N) : posU Fr N j l = llPos Fr j l := by
  unfold posU
  rw [if_pos hl]

theorem posU_fr' (j : ℤ) (N : ℕ) (i : ℕ) : posU Fr N j (N + i) = Fr.fr j i := by
  unfold posU
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem w_lt_posU' (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (i u : ℕ) (hi : i < r)
    (hu : u < N + r) : Fr.fr (j - 1) i < posU Fr N j u := by
  subst hN; exact w_lt_posU hV hr j i u hi hu

end Ord2

section Pre

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} {nL : ZMod J → ℕ}

theorem ml_ll_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLt j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val < u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val < _) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt] at h
    exact (posU_lt_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
    exact (posU_lt_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mpr h

theorem ml_ll_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLe j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val ≤ u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val ≤ _) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt] at h
    exact (posU_le_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
    exact (posU_le_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mpr h

theorem fr_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) < posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) < u := by
  have hm := m.isLt
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')] at h
    exact (posU_lt_iff' hV _ _ (hnL j') _ u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
    exact (posU_lt_iff' hV _ _ (hnL j') _ u (by omega) hu).mpr h

theorem fr_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) ≤ posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) ≤ u := by
  have hm := m.isLt
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')] at h
    exact (posU_le_iff' hV _ _ (hnL j') _ u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
    exact (posU_le_iff' hV _ _ (hnL j') _ u (by omega) hu).mpr h

theorem tl_pre_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLt j (posU Fr (nL j) (segZ j) u) = NSet nL j u := by
  ext ⟨j', x⟩
  rcases x with l | m
  · rw [Set.mem_preimage]
    refine (ml_ll_lt hV hnL j u hu j' l).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inl ⟨l, rfl, h⟩
    · rintro (⟨l', he, h⟩ | ⟨m', he, _⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, h⟩
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
  · rw [Set.mem_preimage]
    refine (fr_lt hV hnL j u hu j' m).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inr ⟨m, rfl, h⟩
    · rintro (⟨l', he, _⟩ | ⟨m', he, h⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, h⟩

theorem tl_pre_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLe j (posU Fr (nL j) (segZ j) u) = NSet nL j (u + 1) := by
  ext ⟨j', x⟩
  rcases x with l | m
  · rw [Set.mem_preimage]
    refine (ml_ll_le hV hnL j u hu j' l).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inl ⟨l, rfl, by omega⟩
    · rintro (⟨l', he, h⟩ | ⟨m', he, _⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, by omega⟩
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
  · rw [Set.mem_preimage]
    refine (fr_le hV hnL j u hu j' m).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inr ⟨m, rfl, by omega⟩
    · rintro (⟨l', he, _⟩ | ⟨m', he, h⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, by omega⟩

end Pre

end Formalism.MainNotions.Proposition5Numerics
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

namespace XXb

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)

def Mx (j : ZMod J) (x : ℤ) : ℤ :=
  if h : ∃ u, u < Dt.nL j + r ∧ pU p O Fr Dt j u = x then
    (if Even x then ka j (Classical.choose h + 1) 0 + 4 * (cP : ℤ) else ka j (Classical.choose h) 0 + 4 * (cP : ℤ))
  else 0

theorem Mx_even {L₁ N₁' : ℕ} (hV : Fr.Valid L₁ N₁') (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < Dt.nL j + r) (he : Even (pU p O Fr Dt j u)) :
    Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) = ka j (u + 1) 0 + 4 * (cP : ℤ) := by
  have hinj : ∀ a b, a < Dt.nL j + r → b < Dt.nL j + r → pU p O Fr Dt j a = pU p O Fr Dt j b → a = b := by
    intro a b ha hb hab
    unfold pU at hab
    rw [hnL j] at ha hb hab
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd hab (ne_of_lt ((posU_lt_iff hV (segZ j) a b ha hb).mpr h1))
    · exact h1
    · exact absurd hab (ne_of_gt ((posU_lt_iff hV (segZ j) b a hb ha).mpr h1))
  have hex : ∃ u', u' < Dt.nL j + r ∧ pU p O Fr Dt j u' = pU p O Fr Dt j u := ⟨u, hu, rfl⟩
  have hc := Classical.choose_spec hex
  have heq : Classical.choose hex = u := hinj _ _ hc.1 hu hc.2
  unfold Mx
  rw [dite_eq_left hex, if_pos he, heq]

theorem Mx_odd {L₁ N₁' : ℕ} (hV : Fr.Valid L₁ N₁') (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < Dt.nL j + r) (he : ¬ Even (pU p O Fr Dt j u)) :
    Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) = ka j u 0 + 4 * (cP : ℤ) := by
  have hinj : ∀ a b, a < Dt.nL j + r → b < Dt.nL j + r → pU p O Fr Dt j a = pU p O Fr Dt j b → a = b := by
    intro a b ha hb hab
    unfold pU at hab
    rw [hnL j] at ha hb hab
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd hab (ne_of_lt ((posU_lt_iff hV (segZ j) a b ha hb).mpr h1))
    · exact h1
    · exact absurd hab (ne_of_gt ((posU_lt_iff hV (segZ j) b a hb ha).mpr h1))
  have hex : ∃ u', u' < Dt.nL j + r ∧ pU p O Fr Dt j u' = pU p O Fr Dt j u := ⟨u, hu, rfl⟩
  have hc := Classical.choose_spec hex
  have heq : Classical.choose hex = u := hinj _ _ hc.1 hu hc.2
  unfold Mx
  rw [dite_eq_left hex, if_neg he, heq]

theorem cond_at {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {d : Fin n' → ℕ}
    (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (B : MvPolynomial (ℤ × Fin K) O)
    (hPl : PlOK p O Fr deg Y N₁ G' cP Dt ka δ j A) (hNo : NoOK p O Fr cP Dt dNo ka j B) (u : ℕ)
    (hu : u < Dt.nL j + r) (hx : pU p O Fr Dt j u ∈ Fr.letters (segZ j)) (hW : ¬ Fr.IsW (segZ j) (pU p O Fr Dt j u)) :
    (Even (pU p O Fr Dt j u) →
      lam1S LZ {y | y ≤ pU p O Fr Dt j u} B ≤ ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) : ℤ) : WithBot ℤ) ∧
      ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) + (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ) : ℤ) : WithTop ℤ) ≤
        valS LZ {y | y < pU p O Fr Dt j u} A) ∧
    (¬ Even (pU p O Fr Dt j u) →
      lam1S LZ {y | y < pU p O Fr Dt j u} B ≤ ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) : ℤ) : WithBot ℤ) ∧
      ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) + (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ) : ℤ) : WithTop ℤ) ≤
        valS LZ {y | y ≤ pU p O Fr Dt j u} A) ∧
    geR (valS LZ {y | y < pU p O Fr Dt j u} A)
      (Bo p Fr deg (segZ j) (pU p O Fr Dt j u) / 2 - sl p Fr deg Y (r + K) (segZ j) (pU p O Fr Dt j u)) := by
  have hV := hM.frames.2.1
  have hr1 : 1 ≤ r := by have := hM.two_le_r; omega
  have hc0 : (0 : ℝ) ≤ (cP : ℝ) := Nat.cast_nonneg _
  have hs : 128 * (cP : ℝ) ≤ slU Fr p deg Y (r + K) Dt.nL j u := hM.margin (segZ j) _ hx hW
  refine ⟨fun he => ?_, fun he => ?_, ?_⟩
  · rw [Mx_even p O Fr cP Dt ka hV hnL j u hu he]
    refine ⟨(hNo.2.2 u hu).2, int_le_val ?_ (hPl.2.2.1 u hu)⟩
    have h1 := threshold_ge_even_position Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u he
    have h2 := ar1 _ _ _ _ _ h1 hs
    unfold tauU
    push_cast
    exact h2
  · rw [Mx_odd p O Fr cP Dt ka hV hnL j u hu he]
    have huN : u < Dt.nL j := by
      by_contra hcon
      exact he (posU_even hV (segZ j) (Dt.nL j) u (by omega) hu)
    refine ⟨(hNo.2.2 u hu).1, int_le_val ?_ (hPl.2.2.2 u huN)⟩
    obtain ⟨l1, l2⟩ := posU_letter hV hr1 (segZ j) (Dt.nL j) (hnL j) (u + 1) (by omega)
    have hs' : 128 * (cP : ℝ) ≤ slU Fr p deg Y (r + K) Dt.nL j (u + 1) := hM.margin (segZ j) _ l1 l2
    have h1 := threshold_ge_odd_position Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u he
    have h2 := ar1 _ _ _ _ _ h1 hs'
    unfold tauU
    push_cast
    exact h2
  · refine geR_of_ceil ?_ (hPl.2.2.1 u hu)
    have h1 := th_ge_B Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u
    exact ar3 _ _ _ _ h1 hs hc0

end At

end XXb


open XXb in
theorem restXXG_b : RestXXG := by
  intro p _ n' r K _ _ _ O _ _ _ S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka hT δ j A B hPl hNo
  have hV := hM.frames.2.1
  have hr1 : 1 ≤ r := by have := hM.two_le_r; omega
  have hnL := hT.1.2.1
  have hdeg : ∀ mm ∈ (plEmb O r K A * nmEmb O r K B).support, ∀ x,
      ∑ c : Fin (r + K), mm (x, c) = δ (j, x) + dNoOf p O Fr Dt dNo (j, x) ∧
      ordDeg mm x ≤ δ (j, x) + dNoOf p O Fr Dt dNo (j, x) := by
    intro mm hmm x
    obtain ⟨ua, hua, ub, hub, h⟩ := XXb.deg_mul A B mm hmm
    have e1 : ∑ c : Fin r, mm (x, Fin.castAdd K c) = δ (j, x) := by
      rw [← hPl.2.1 ua hua x]
      exact Finset.sum_congr rfl fun c _ => (h x).1 c
    have e2 : ∑ c : Fin K, mm (x, Fin.natAdd r c) = dNoOf p O Fr Dt dNo (j, x) := by
      rw [← hNo.2.1 ub hub x]
      exact Finset.sum_congr rfl fun c _ => (h x).2 c
    refine ⟨by rw [Fin.sum_univ_add, e1, e2], ?_⟩
    unfold ordDeg
    split_ifs
    · rw [e2]; omega
    · rw [e1]; omega
  refine ⟨?_, ?_⟩
  · unfold XX'
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨A, B, XXb.Mx p O Fr cP Dt ka j, hPl.1, hNo.1, ?_, rfl⟩, ?_⟩
    · intro x hx hW
      obtain ⟨u, hu, rfl⟩ := XXb.exists_posU hV hr1 (segZ j) (Dt.nL j) (hnL j) x hx hW
      exact XXb.cond_at p O Fr deg Y N₁ G' cP Dt dNo ka hM hnL δ j A B hPl hNo u hu hx hW
    · rw [mem_restrictSupport_iff]
      intro mm hmm x _ _
      show (ordDeg mm x : ℝ) ≤ ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ)
      exact Nat.cast_le.2 (hdeg mm hmm x).2
  · rw [mem_restrictSupport_iff]
    intro mm hmm x _
    exact (hdeg mm hmm x).1

end Formalism.MainNotions.Proposition5Numerics
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem le_cube_mul (k N : ℝ) (hk : 1 ≤ k) (hN : 1 ≤ N) : k ≤ k ^ 3 * N := by
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have h1 : k ≤ k ^ 3 := by nlinarith
  calc k ≤ k ^ 3 := h1
    _ = k ^ 3 * 1 := (mul_one _).symm
    _ ≤ k ^ 3 * N := mul_le_mul_of_nonneg_left hN (by positivity)

theorem k_le_a {C : ℝ} (hC1 : 1 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) : ((m + 1 : ℕ) : ℝ) ≤ a := by
  have hB := hyps_basic hC1 H
  obtain ⟨h1, h2, _, _, _, _, _, _, _, _, h11, h12⟩ := H
  have hr1 : 1 ≤ r := by omega
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hN1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hcc : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h8' : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
    have : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  obtain ⟨z1, _, _⟩ := factor_le_product_seven C (((m + 1 : ℕ) : ℝ) ^ 3) ((r : ℝ) ^ 2) (TT.card : ℝ)
    (((p : ℝ) ^ goodG' r de h x) ^ 5) ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) Y hC1
    (one_le_pow₀ hk1) (one_le_pow₀ hrr) hN1 (one_le_pow₀ hQ1) hcc (by linarith [hB.two_le_Y])
  exact le_trans (le_cube_mul _ _ hk1 hN1) (le_trans z1 h12)

section Geo

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem posU_mem' (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (hu : u < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j u ∈ Fr.letters j ∧ ¬ Fr.IsW j (posU Fr (Fr.LLset j).card j u) := by
  unfold posU
  split_ifs with h
  · exact LL_sub_letters hV hr j _ (llPos_mem Fr j u h)
  · have hi : u - (Fr.LLset j).card < r := by omega
    have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    have h2 := frame_row_monotone Fr L₁ N₁ hV (j - 1) (r - 1) (by omega)
    have h3 := frame_row_monotone Fr L₁ N₁ hV j _ hi
    have h4 := frame_entry_le_last Fr L₁ N₁ hV j _ hi
    refine ⟨?_, ?_⟩
    · unfold Frames.letters
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, h4⟩, (hV.2.2.2.2.1 j _ hi).1⟩
    · unfold Frames.IsW
      omega

theorem sl_lt_Bo (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (deg : Fin n' → ℕ) (a : ℝ) (ha : 0 < a)
    (hdeg : ∀ s ∈ Fr.TT, a ≤ (deg s : ℝ)) (Y : ℝ) (k : ℕ) (hY : 2 ≤ Y) (hk : 1 ≤ k) {J : ℕ} (nL : ZMod J → ℕ)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ) (hu : u < nL j + r) :
    3 / 8 * slU Fr p deg Y k nL j u < Bo p Fr deg (segZ j) (posU Fr (nL j) (segZ j) u) / 2 := by
  have hu' : u < (Fr.LLset (segZ j)).card + r := by rw [← hnL j]; exact hu
  obtain ⟨hx1, hx2⟩ := posU_mem' hV hr (segZ j) u hu'
  rw [← hnL j] at hx1 hx2
  have hB := Bo_ge hV hr p hp deg a hdeg (segZ j) _ hx1 hx2
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpos : 0 < Bo p Fr deg (segZ j) (posU Fr (nL j) (segZ j) u) := lt_of_lt_of_le (by positivity) hB
  unfold slU
  exact sl_lt_real _ Y (k : ℝ) _ rfl hpos hY (by exact_mod_cast hk)

end Geo

section At

variable {p n' m r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r}
  {lam0 : Fin n' → Fin (m + 1) → ℤ} {a : ℝ}

theorem sizeAt_of [hpF : Fact p.Prime] (hk : m + 1 = r + K) (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r)
    (hnb : NB p m r TT.card a) (hka : ((m + 1 : ℕ) : ℝ) ≤ a)
    (hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a)
    {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (hJ : J = F.J) (hnL : ∀ j, nL j = (F.LLset (segZ j)).card) :
    SizeAt (K := K) p F nL (dT TT lam0) (9 * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) := by
  have hV := hF.2.1
  have hp2 : 2 ≤ p := hpF.out.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have ha2 := hnb.two_le_a
  intro rho dPl dNo hBk bp bn hbp hbn
  have hsum : ∀ x, ((dPl x + dNo x : ℕ) : ℝ) ≤ 2 * a := by
    intro x
    have htop : posOf n' (posTL F x) ∈ TT := by
      have := (posTL_seg F hV hr hnL x).2.2
      rwa [hF.1] at this
    have e := hBk.2 x
    have e2 : dT TT lam0 (posOf n' (posTL F x)) = flatDeg lam0 (posOf n' (posTL F x)) := by
      unfold dT; rw [if_pos htop]
    rw [e2] at e
    have hl : 1 ≤ lowP F p x := Nat.one_le_pow _ _ (by omega)
    have e3 : dPl x + dNo x ≤ flatDeg lam0 (posOf n' (posTL F x)) := by
      have := Nat.mul_le_mul_right (dPl x + dNo x) hl
      omega
    have e4 : ((dPl x + dNo x : ℕ) : ℝ) ≤ (flatDeg lam0 (posOf n' (posTL F x)) : ℝ) := by exact_mod_cast e3
    have := (hfd _ htop).2
    linarith
  have hdp : ∀ x, (dPl x : ℝ) ≤ 2 * a := by
    intro x
    have := hsum x
    push_cast at this
    have h0 : (0 : ℝ) ≤ (dNo x : ℝ) := Nat.cast_nonneg _
    linarith
  have hdn : ∀ x, (dNo x : ℝ) ≤ 2 * a := by
    intro x
    have := hsum x
    push_cast at this
    have h0 : (0 : ℝ) ≤ (dPl x : ℝ) := Nat.cast_nonneg _
    linarith
  have hcard : Fintype.card (TL J nL r) ≤ TT.card := by
    have := card_TL_le F hV hr hJ hnL
    rwa [hF.1] at this
  have A := DnoOf_le (K := K) p hp2 nL dNo TT.card (m + 1) a hr (by omega) hcard hdn ha2 hnb.fourN hka
  have B := mult_level_real p dPl bp hbp TT.card a ha2 hcard hdp
  have Cc := mult_level_real p dNo bn hbn TT.card a ha2 hcard hdn
  have hrk : (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r ≤ m + 1)
  have hKk : (K : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ m + 1)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  exact size_fin (TT.card : ℝ) ((m + 1 : ℕ) : ℝ) (r : ℝ) (K : ℝ) (Real.logb p a) _ _ _ (Nat.cast_nonneg _)
    (by linarith [hnb.one_le_log]) hk1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hrk hKk A B Cc

end At

end Formalism.MainNotions.Proposition5Numerics
end
end
