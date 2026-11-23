module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopCountLowerBoundsOfOccurrence
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle011
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TauDegreeOnPathBound
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle013
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LDigits
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Occ

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

open Classical in
theorem occ_Ioc (hV : F.Valid L₁ N₁) (c : ℤ) (t : Fin n') :
    ∑ j ∈ Finset.range F.J, ((Finset.Ioc (eFr F ((j : ℤ) + c)) (eFr F (((j + 1 : ℕ) : ℤ) + c))).filter
      fun y => posOf n' y = t).card ≤ 1 := by
  have hm := eFr_strictMono hV
  have h3 := sum_card_Ioc (fun i : ℕ => eFr F ((i : ℤ) + c)) (fun a b hab => hm.monotone (by omega))
    (fun y => posOf n' y = t) F.J
  rw [h3]
  have h2 : eFr F ((F.J : ℤ) + c) = eFr F (((0 : ℕ) : ℤ) + c) + n' := by
    have := hV.2.1 c (r - 1)
    simp only [eFr]
    rw [show (F.J : ℤ) + c = c + F.J by ring, show ((0 : ℕ) : ℤ) + c = c by simp, this]
  simp only [h2]
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact posOf_injOn _ (Finset.mem_Ioc.mp ha'.1) (Finset.mem_Ioc.mp hb'.1) (ha'.2.trans hb'.2.symm)

end Occ

theorem top_occurs_in_at_most_two_segments : LeadingLetterInAtMostTwoSegments := by
  intro p n' r K _ _ _ X hX t
  classical
  have hV := hX.valid
  have h1 := occ_Ioc hV (-2) t
  have h2 := occ_Ioc hV (-1) t
  have key : ∀ j ∈ Finset.range X.F.J, ((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card ≤
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -2)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -2))).filter fun y => posOf n' y = t).card +
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -1)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -1))).filter fun y => posOf n' y = t).card := by
    intro j _
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro y hy
    obtain ⟨hyl, hyt⟩ := Finset.mem_filter.mp hy
    have hb := mem_letters_bounds hyl
    have e1 : ((j + 1 : ℕ) : ℤ) + -2 = (j : ℤ) - 1 := by push_cast; ring
    have e2 : ((j + 1 : ℕ) : ℤ) + -1 = (j : ℤ) := by push_cast; ring
    have e3 : (j : ℤ) + -1 = (j : ℤ) - 1 := by ring
    have h4 := hV.2.2.2.1 ((j : ℤ) + -2)
    have e4 : (j : ℤ) + -2 + 1 = (j : ℤ) - 1 := by ring
    rw [e4] at h4
    rw [e1, e2, e3, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
    simp only [eFr]
    by_cases hc : y ≤ X.F.fr ((j : ℤ) - 1) (r - 1)
    · exact Or.inl ⟨⟨lt_of_lt_of_le h4 hb.1, hc⟩, hyt⟩
    · exact Or.inr ⟨⟨not_le.mp hc, hb.2.1⟩, hyt⟩
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [Finset.sum_add_distrib]
  omega

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem residue_class_count : ResidueClassCount := by
  classical
  intro r Q be c ρ hr hQ
  have hQ0 : 0 < Q := by omega
  have hcore := Formalism.InvariantFactorPaths.BranchingDimensions.residueClassLowerBound r Q be (ρ % Q + (Q - c % Q)) hr hQ
  refine le_trans hcore ?_
  have hle : ((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
      (fun u => (∑ l, (u l : ℕ)) % Q = (ρ % Q + (Q - c % Q)) % Q)).card ≤
      ((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card := by
    refine Finset.card_le_card_of_injOn (fun u => fun l => (u l : ℕ)) ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun l =>
        Finset.mem_range.mpr (u l).isLt, ?_⟩)
      have h1 : (∑ l, (u l : ℕ)) ≡ ρ % Q + (Q - c % Q) [MOD Q] := hu'
      have h2 : c + ∑ l, (u l : ℕ) ≡ c + (ρ % Q + (Q - c % Q)) [MOD Q] := Nat.ModEq.add_left c h1
      have h3 : c + (ρ % Q + (Q - c % Q)) ≡ ρ [MOD Q] := by
        have hc : c % Q < Q := Nat.mod_lt _ hQ0
        have e1 : c + (ρ % Q + (Q - c % Q)) = (c - c % Q + Q) + ρ % Q := by
          have := Nat.mod_le c Q
          omega
        rw [e1]
        have e2 : c - c % Q + Q ≡ 0 [MOD Q] := by
          have hd : Q ∣ c - c % Q := Nat.dvd_sub_mod c
          exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.add hd (dvd_refl Q)))
        have e3 : ρ % Q ≡ ρ [MOD Q] := Nat.mod_modEq ρ Q
        simpa using e2.add e3
      exact h2.trans h3
    · intro u _ u' _ huu
      funext l
      exact Fin.ext (congrFun huu l)
  exact_mod_cast hle

theorem tele_le : ∀ (n : ℕ) (hn : 0 < n) (f g : Fin n → ℤ),
    (∀ (a : Fin n) (h : a.val + 1 < n), f ⟨a.val + 1, h⟩ ≤ g a) →
    ∑ a, (f a - g a) ≤ f ⟨0, hn⟩ - g ⟨n - 1, by omega⟩ := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro f g h
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
  have h1 : ∑ i : Fin m, f i.succ ≤ ∑ i : Fin m, g i.castSucc :=
    Finset.sum_le_sum fun i _ => h i.castSucc (by simp)
  have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [e]
  have e0 : (⟨0, hn⟩ : Fin (m + 1)) = 0 := rfl
  rw [e0]
  linarith

section D21

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dminus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) :
    T.dminus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  unfold T.dminus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · exfalso
    have hl := l.isLt
    have ht : l.val - (segN X.F j - r) < r := by omega
    have hseg : segE X.F j l = X.F.fr j (l.val - (segN X.F j - r)) :=
      (segE_eq_fr_iff X.F hV j l ht).mpr (by omega)
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
    rw [hvec] at h1
    exact absurd h1.2 (by simp)
  · exact Nat.zero_le _
  · exact le_rfl

end D21

theorem tau_degree_on_path_bound : TauDegreeOnPathBound := by
  intro p n' r K _ _ _ X hX j b μ dd hP i hi
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  obtain ⟨P, hPμ⟩ := hP.path
  have hil := i.isLt
  have hnot : ¬ i.val < segN X.F j - r := fun h => by
    have := (segE_lt_fr_iff X.F hV hr j i).mpr h
    omega
  have ht : i.val - (segN X.F j - r) < r := by omega
  have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
    (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
  have hvec : (segLL X.F j).vec i = true := by
    rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
  have hs := T.step_vec P i hvec
  rw [hPμ] at hs
  have hn : 0 < r + K := by omega
  have h1 := tele_le (r + K) hn (μ i.succ) (μ i.castSucc) hs.2.1
  rw [hs.2.2] at h1
  have h2 : μ i.succ ⟨0, hn⟩ = (X.beS p K j b : ℤ) :=
    hP.head i ⟨i.val - (segN X.F j - r), ht⟩ hseg ⟨0, hn⟩ (Nat.zero_le _)
  have h3 := T.neg_dminus_le_mu P i.val (by omega) ⟨r + K - 1, by omega⟩
  rw [hPμ] at h3
  have h4 := dminus_le_beS X p K hX j b μ dd hP i.val
  have h5 : μ i.castSucc = μ ⟨i.val, by omega⟩ := rfl
  rw [h2, h5] at h1
  have h4' : (T.dminus (segLL X.F j) dd i.val : ℤ) ≤ (X.beS p K j b : ℤ) := by exact_mod_cast h4
  have : (dd i : ℤ) ≤ 2 * (X.beS p K j b : ℤ) := by linarith
  exact_mod_cast this

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
