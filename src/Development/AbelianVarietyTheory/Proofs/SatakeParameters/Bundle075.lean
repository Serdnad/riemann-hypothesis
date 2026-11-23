module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  first | exact @GlobalTheory.RowTie.howeUp_of_pairLift | exact GlobalTheory.RowTie.howeUp_of_pairLift | (intros; apply GlobalTheory.RowTie.howeUp_of_pairLift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  first | exact @GlobalTheory.PtOfLocSplit.main | exact GlobalTheory.PtOfLocSplit.main | (intros; apply GlobalTheory.PtOfLocSplit.main <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem cc_mul_self (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 := by
  ext <;> simp [Formalism.HC.Frame.cc, c0]

theorem hcAt_eq_hc : ∀ (D : D7) (ρ : D.what₂.Tau) (g : D.R.GG), (((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨ ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g) → hcAt D g = D.hc ρ := by
  intro D ρ g h
  have hm : ((D.eTau ρ : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2
  have hp : plc g = ((D.eTau ρ : D.R.Psi) : D.R.GG) := by
    rcases h with rfl | rfl
    · simp [plc, hm]
    · unfold plc
      have h2 : (((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc).1.2 ≠ 1 := by
        simp [Formalism.HC.Frame.cc, c0, hm]
      rw [if_neg h2, mul_comm, mul_assoc, cc_mul_self, mul_one]
  unfold hcAt
  have : (⟨plc g, plc_mem g⟩ : D.R.Psi) = D.eTau ρ := Subtype.ext hp
  rw [this, Equiv.symm_apply_apply]

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem half_int_eq (R : Ranks) : ((((R.t : ℤ) - 1) / 2 : ℤ) : ℚ) = ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨k, hk⟩ := R.t_odd
  rw [hk]
  push_cast
  have : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [this]; push_cast; ring

theorem mem_cloud_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ cloud P j ↔ ∃ a, (X : ℚ) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold cloud
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_lows_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ lows P j ↔ ∃ a, (X : ℚ) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold lows
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_twistedDualJumpsWithoutBlock_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    u ∈ jT2 P j s ↔ (if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) ∈ cloud P j + lows P j := by
  unfold jT2 jW
  cases s
  · simp only [Bool.false_eq_true, if_false, Multiset.map_map, Function.comp_def, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩
  · simp only [if_true, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩

theorem jumps_rat {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    (u ∈ jT2 P j s ↔ ((∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2) ∨ ∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2)) ∧ (u ∈ jT1 P j s ↔ u ∈ jT2 P j s ∨ ∃ c : ℕ, c < R.t ∧ -u - 1 = c) := by
  have hcast : (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) =
      (((if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) : ℤ) : ℚ) := by
    split_ifs <;> push_cast <;> ring
  refine ⟨?_, ?_⟩
  · rw [mem_twistedDualJumpsWithoutBlock_iff, Multiset.mem_add, hcast, mem_cloud_iff, mem_lows_iff]
  · unfold jT1 jR
    rw [Multiset.map_add (f := _), Multiset.mem_add]
    show u ∈ jT2 P j s ∨ _ ↔ _
    apply or_congr Iff.rfl
    unfold block
    simp only [Multiset.map_map, Function.comp_def, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, by ring⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by omega⟩

end GlobalTheory.HTW.Rec
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem clusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  intro n th j hC t ht
  obtain ⟨F, sp, hF, huniq⟩ := hC
  obtain ⟨x, ⟨hxF, hxt⟩, -⟩ := huniq t ht
  obtain ⟨hthx, hspj, -, -, hbetween, hbefore⟩ := hF x hxF
  rcases hxt with rfl | rfl
  · exact Or.inl hbefore
  · by_cases hsp0 : sp x = 0
    · left
      rw [hsp0, Nat.cast_zero, add_zero]
      exact hbefore
    · right
      refine ⟨sp x, Nat.one_le_iff_ne_zero.2 hsp0, hspj, by simpa using hthx, fun k hk1 hk2 hkd => ?_⟩
      rcases lt_or_gt_of_ne hkd with hlt | hgt
      · have e : x + (sp x : ZMod n) - k = x + ((sp x - k : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hlt.le]
          ring
        rw [e]
        exact hbetween (sp x - k) (by omega) (by omega)
      · have e : x + (sp x : ZMod n) - k = x - ((k - sp x : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hgt.le]
          ring
        rw [e]
        exact hbefore (k - sp x) (by omega) (by omega)

end GlobalTheory.HTW.Rec
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly : SSRankUnique := by
  first | exact @GlobalTheory.SSRank.ssRankUnique_holds | exact GlobalTheory.SSRank.ssRankUnique_holds | (intros; apply GlobalTheory.SSRank.ssRankUnique_holds <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.roundedSizeBound_window : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (bHat L : ℝ) ∧ (bHat L : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1 := by
  first | exact @GlobalTheory.HTW.bHat_window | exact GlobalTheory.HTW.bHat_window | (intros; apply GlobalTheory.HTW.bHat_window <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.cloudLowJumps_reflect_and_card : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m), jR P j false = (jR P j true).map (fun u => (R.t : ℤ) - 1 - u) ∧ ∀ s, (jW P j s).card = R.r ∧ (jR P j s).card = R.nV ∧ (jT2 P j s).card = R.r ∧ jT2 P j s ≤ jT1 P j s := by
  first | exact @GlobalTheory.HTW.jR_symm_card | exact GlobalTheory.HTW.jR_symm_card | (intros; apply GlobalTheory.HTW.jR_symm_card <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.sum_roundedSizes_le_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  first | exact @GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | exact GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | (intros; apply GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualJumps_mem_windows : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ), (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) → (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s, (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ) else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨ |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.jT1_mem_window_of_bounded_v | exact GlobalTheory.jT1_mem_window_of_bounded_v | (intros; apply GlobalTheory.jT1_mem_window_of_bounded_v <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton : Numerics ∧ Rest := by
  first | exact @GlobalTheory.SixthNumerics.numerics_and_rest | exact GlobalTheory.SixthNumerics.numerics_and_rest | (intros; apply GlobalTheory.SixthNumerics.numerics_and_rest <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

section Param

variable {R : Ranks} (P : HCParam R)

theorem v_step (a : ℕ) : ∀ (n : ℕ) (h : a + n + 1 < R.k - 1),
    P.v ⟨a + n + 1, h⟩ < P.v ⟨a, by omega⟩
  | 0, h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
  | n + 1, h => by
    have h1 := v_step a n (by omega)
    have h2 : P.v ⟨a + (n + 1) + 1, h⟩ < P.v ⟨a + n + 1, by omega⟩ :=
      (P.u_gt_v ⟨a + (n + 1) + 1, h⟩).trans (P.v_gt_u ⟨a + n + 1, by omega⟩)
    exact h2.trans h1

theorem b_step (a : ℕ) : ∀ (n : ℕ) (h : a + n + 1 < R.m),
    P.b ⟨a, by omega⟩ < P.b ⟨a + n + 1, h⟩
  | 0, h => by
    have h1 := P.gap_be ⟨a, by omega⟩
    have h2 := P.gap_eb ⟨a, by omega⟩ h
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith
  | n + 1, h => by
    have h0 := b_step a n (by omega)
    have h1 := P.gap_be ⟨a + n + 1, by omega⟩
    have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨a + (n + 1) + 1, h⟩ - P.e ⟨a + n + 1, by omega⟩ :=
      P.gap_eb ⟨a + n + 1, by omega⟩ h
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith

theorem v_lt {a c : Fin (R.k - 1)} (h : a < c) : P.v c < P.v a := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := v_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

theorem b_lt {a c : Fin R.m} (h : a < c) : P.b a < P.b c := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := b_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

theorem floor_v_inj : Function.Injective fun a : Fin (R.k - 1) => ⌊P.v a⌋ := by
  intro a c hac
  obtain ⟨x, hx⟩ := P.v_int a
  obtain ⟨y, hy⟩ := P.v_int c
  have hxy : P.v a = P.v c := by
    simp only [hx, hy, Int.floor_intCast] at hac
    rw [hx, hy, hac]
  rcases lt_trichotomy a c with h | h | h
  · exact absurd hxy (v_lt P h).ne'
  · exact h
  · exact absurd hxy (v_lt P h).ne

theorem floor_b_inj : Function.Injective fun a : Fin R.m => ⌊P.b a⌋ := by
  intro a c hac
  obtain ⟨x, hx⟩ := P.b_int a
  obtain ⟨y, hy⟩ := P.b_int c
  have hxy : P.b a = P.b c := by
    simp only [hx, hy, Int.floor_intCast] at hac
    rw [hx, hy, hac]
  rcases lt_trichotomy a c with h | h | h
  · exact absurd hxy (b_lt P h).ne
  · exact h
  · exact absurd hxy (b_lt P h).ne'

theorem cloud_add_lows_nodup (j : Fin R.m) (hv : ∀ a, 0 ≤ P.v a) (hb : ∀ i, 0 < P.b i) :
    (cloud P j + lows P j).Nodup := by
  rw [Multiset.nodup_add]
  refine ⟨?_, ?_, ?_⟩
  · refine Multiset.Nodup.map (fun a c h => floor_v_inj P ?_) Finset.univ.nodup
    simpa using h
  · refine Multiset.Nodup.map (fun a c h => floor_b_inj P ?_) Finset.univ.nodup
    simpa using h
  · rw [Multiset.disjoint_left]
    intro u hu hu'
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hu
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hu'
    obtain ⟨x, hx⟩ := P.v_int a
    obtain ⟨y, hy⟩ := P.b_int i
    have hx0 : 0 ≤ x := by
      have := hv a
      rw [hx] at this
      exact_mod_cast this
    have hy0 : 0 < y := by
      have := hb i
      rw [hy] at this
      exact_mod_cast this
    simp only [hx, hy, Int.floor_intCast] at hi
    omega

theorem twistedDualJumpsWithoutBlock_nodup_of_signs (j : Fin R.m) (s : Bool) (hv : ∀ a, 0 ≤ P.v a) (hb : ∀ i, 0 < P.b i) :
    (jT2 P j s).Nodup := by
  have h := cloud_add_lows_nodup P j hv hb
  have h1 : Function.Injective fun u : ℤ => -u - 1 := fun a c h => by
    have : -a - 1 = -c - 1 := h
    omega
  have h2 : Function.Injective fun u : ℤ => (R.t : ℤ) - 1 - u := fun a c h => by
    have : (R.t : ℤ) - 1 - a = (R.t : ℤ) - 1 - c := h
    omega
  unfold jT2 jW
  refine Multiset.Nodup.map h1 ?_
  cases s
  · simpa using Multiset.Nodup.map h2 h
  · simpa using h

end Param

theorem twistedDualJumpsWithoutBlock_nodup_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (g : D.R.GG) (s : Bool),
    Roomy L C → (jT2 (hcAt D g) j s).Nodup := by
  intro D L C j g s hR
  obtain ⟨hC, h100, hη, hwb, -, hCb⟩ := id hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have hηw : L.etaSz < L.sc.w'' D.R.n := by linarith
  have hbig : L.etaSz < (⌊(hcAt D g).e j⌋ : ℝ) := by
    by_cases hT : Thick D.host g
    · have h1 := (SizeThick.size_thick L g j hT).1
      have hL : (0 : ℝ) ≤ (D.host.Lw : ℝ) := by positivity
      have hb' : 0 < L.sc.b' := by linarith
      have h2 : L.sc.b' ≤ C * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
        have : (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
        nlinarith
      linarith
    · exact lt_of_lt_of_le hηw (size_not_thick L C g j hR hT).1
  refine twistedDualJumpsWithoutBlock_nodup_of_signs _ j s ?_ ?_
  · intro a
    have h := (L.cloud_v (D.eTau.symm ⟨plc g, plc_mem g⟩) a).1
    exact_mod_cast h
  · intro i
    have h := L.be_close (D.eTau.symm ⟨plc g, plc_mem g⟩) i j
    have h' : |((((hcAt D g).b i - (hcAt D g).e j : ℚ)) : ℝ)| ≤ L.etaSz := h
    obtain ⟨z, hz⟩ := (hcAt D g).e_int j
    rw [hz, Int.floor_intCast] at hbig
    rw [hz] at h'
    have h2 := (abs_le.1 h').1
    push_cast at h2
    have : (0 : ℝ) < (((hcAt D g).b i : ℚ) : ℝ) := by linarith
    exact_mod_cast this

end GlobalTheory.HTW.Rec
end
