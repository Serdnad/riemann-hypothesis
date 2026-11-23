module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Transported
public import Formalism.SharpRestriction.GrowthBounds.ColumnSystems
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

variable {n' : ℕ}

def rot (n : ℕ) (j : Fin n) : Fin n := ⟨(j.val + 1) % n, Nat.mod_lt _ j.pos⟩

theorem rot_val (n : ℕ) (j : Fin n) :
    (j.val + 1 < n ∧ (rot n j).val = j.val + 1) ∨ (j.val + 1 = n ∧ (rot n j).val = 0) := by
  have hj := j.isLt
  by_cases h : j.val + 1 < n
  · left
    exact ⟨h, Nat.mod_eq_of_lt h⟩
  · right
    have e : j.val + 1 = n := by omega
    refine ⟨e, ?_⟩
    show (j.val + 1) % n = 0
    rw [e, Nat.mod_self]

theorem rot_inj (n : ℕ) : Function.Injective (rot n) := by
  intro j j' h
  have h' := congrArg Fin.val h
  have a := rot_val n j
  have b := rot_val n j'
  apply Fin.ext
  omega

theorem rot_bij (n : ℕ) : Function.Bijective (rot n) := Finite.injective_iff_bijective.mp (rot_inj n)

theorem next_eq (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : segNext TT j = segStart TT (rot _ j) := rfl

theorem prod_next (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segNext TT j) = ∏ j, h (segStart TT j) :=
  (rot_bij (numSeg TT)).prod_comp (fun j => h (segStart TT j))

theorem other_start (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    ∃ e, e ∈ TT ∧ Even e.val ∧ e ≠ segStart TT j := by
  by_cases h0 : j.val = 0
  · refine ⟨segStart TT ⟨1, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega
  · refine ⟨segStart TT ⟨0, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega

theorem segG_eq (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    segG TT j = cdist (segStart TT j) (segNext TT j) ∧ 0 < cdist (segStart TT j) (segNext TT j) := by
  obtain ⟨e, he, hev, hne⟩ := other_start TT h2 j
  obtain ⟨m1, -⟩ := next_min TT j e he hev hne
  refine ⟨?_, m1⟩
  unfold segG
  rw [if_neg (by omega)]

theorem sum_segG (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) : ∑ j, segG TT j = n' := by
  have key : ∀ j : Fin (numSeg TT), (segG TT j : ℤ) =
      ((segStart TT (rot _ j)).val : ℤ) - ((segStart TT j).val : ℤ) +
        (if j = ⟨numSeg TT - 1, by omega⟩ then (n' : ℤ) else 0) := by
    intro j
    obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g, next_eq] at *
    have c := cd_cases (segStart TT j) (segStart TT (rot _ j))
    have l1 := (segStart TT j).isLt
    have l2 := (segStart TT (rot _ j)).isLt
    rcases rot_val _ j with ⟨r1, r2⟩ | ⟨r1, r2⟩
    · have hlt : (segStart TT j).val < (segStart TT (rot _ j)).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have hne : j ≠ ⟨numSeg TT - 1, by omega⟩ := by
        intro e
        have := congrArg Fin.val e
        simp at this
        omega
      rw [if_neg hne]
      omega
    · have hlt : (segStart TT (rot _ j)).val < (segStart TT j).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have he : j = ⟨numSeg TT - 1, by omega⟩ := by
        apply Fin.ext
        show j.val = numSeg TT - 1
        omega
      rw [if_pos he]
      omega
  have hs : (∑ j, ((segStart TT (rot _ j)).val : ℤ)) = ∑ j, ((segStart TT j).val : ℤ) :=
    (rot_bij (numSeg TT)).sum_comp (fun j => ((segStart TT j).val : ℤ))
  have : ((∑ j, segG TT j : ℕ) : ℤ) = (n' : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
    simp
  exact_mod_cast this

theorem prod_starts (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segStart TT j) = ∏ s ∈ TT.filter (fun s => Even s.val), h s := by
  refine Finset.prod_nbij (fun j => segStart TT j) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j _
    exact Finset.mem_filter.mpr (start_mem TT j)
  · intro j _ j' _ e
    exact (ev_mono TT).injective e
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp ((ev_mem TT s).mpr hs')
    exact ⟨k, Finset.mem_coe.mpr (Finset.mem_univ _), hk⟩

theorem pos_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ oddSet TT j ∧ cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i := by
  obtain ⟨s, hs, h5⟩ := get_spec TT j i
  have : segPos TT j i = s := by
    unfold segPos
    rw [← h5, posAdd_cdist]
  rw [this]
  exact ⟨Finset.mem_filter.mpr hs, h5⟩

theorem prod_pos (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (h : Fin n' → ℝ) :
    ∏ i, h (segPos TT j i) = ∏ s ∈ oddSet TT j, h s := by
  refine Finset.prod_nbij (fun i => segPos TT j i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    exact (pos_spec TT j i).1
  · intro i _ i' _ e
    have e' : segPos TT j i = segPos TT j i' := e
    have h1 := (pos_spec TT j i).2
    have h2 := (pos_spec TT j i').2
    rw [e'] at h1
    exact (dist_strictMono TT j).injective (h1.symm.trans h2)
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    have hd : cdist (segStart TT j) s ∈ segDists TT j := mem_dists.mpr ⟨s, hs', rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    refine ⟨i, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    show segPos TT j i = s
    unfold segPos
    rw [hi, posAdd_cdist]

theorem odd_covered (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (s : Fin n') (hs : s ∈ TT) (ho : ¬ Even s.val) :
    ∃ j, s ∈ oddSet TT j := by
  have hne : (TT.filter (fun x => Even x.val)).Nonempty :=
    ⟨segStart TT ⟨0, by omega⟩, Finset.mem_filter.mpr (start_mem TT _)⟩
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image (TT.filter (fun x => Even x.val)) (fun x => cdist x s) hne
  have hx' := Finset.mem_filter.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((ev_mem TT x).mpr hx')
  have hj' : segStart TT j = x := hj
  refine ⟨j, Finset.mem_filter.mpr ⟨hs, ho, ?_, ?_⟩⟩
  · rw [hj']
    have c := cd_cases x s
    have l1 := x.isLt
    have l2 := s.isLt
    have hxs : x.val ≠ s.val := by
      intro e
      rw [← e] at ho
      exact ho hx'.2
    omega
  · obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g]
    by_contra hcon
    have hy := hmin (segNext TT j) (Finset.mem_filter.mpr (next_mem TT j))
    rw [hj'] at g0 hcon
    have c1 := cd_cases x s
    have c2 := cd_cases x (segNext TT j)
    have c3 := cd_cases (segNext TT j) s
    have l1 := x.isLt
    have l2 := s.isLt
    have l3 := (segNext TT j).isLt
    omega

theorem biUnion_odd (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) :
    Finset.univ.biUnion (oddSet TT) = TT.filter (fun s => ¬ Even s.val) := by
  ext s
  constructor
  · intro hs
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨a0, a1, -⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨a0, a1⟩
  · intro hs
    obtain ⟨a0, a1⟩ := Finset.mem_filter.mp hs
    obtain ⟨j, hj⟩ := odd_covered TT h2 s a0 a1
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩

theorem prod_tops (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (h : Fin n' → ℝ) :
    ∏ s ∈ TT, h s = ∏ j, (h (segStart TT j) * ∏ i, h (segPos TT j i)) := by
  rw [Finset.prod_mul_distrib, prod_starts, Finset.prod_congr rfl fun j _ => prod_pos TT j h,
    ← Finset.prod_biUnion (fun j _ j' _ hjj => oddSet_disj TT j j' hjj), biUnion_odd TT h2,
    Finset.prod_filter_mul_prod_filter_not]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def FamilyFifthBound (D : Formalism.BasicNotions.D7) : Prop := ∀ C0 CE1 CE2, PointsLemma D C0 CE1 CE2

def RestFree (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => FreeTopRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RemainderSegmentBoundFirst (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ExtendedDichotomy D C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def FamilyFourthBound (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∀ Ckap : ℝ, 0 < Ckap → ∃ Cs : ℝ, 0 < Cs ∧
    ExtendedKappaBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs

def RemainderSegmentBoundThird (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    ExtendedOrderBound D C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc

def RootMultiplicityTwoBeyond (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => RootMultiplicityTwo D C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RemainderSegmentBoundSecond (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ∃ Ck0 : ℝ, 0 < Ck0 ∧ ∀ Ckap : ℝ, Ck0 ≤ Ckap →
    ExtendedModelRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc

def RestExt (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ck0 Ct0 : ℝ, 0 < Ck0 ∧ 0 < Ct0 ∧ ∀ Ckap Ct : ℝ, Ck0 ≤ Ckap → Ct0 ≤ Ct →
    HerrExtensionClass D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc

theorem closed_of_rests {D : Formalism.BasicNotions.D7} (h3 : FamilyFifthBound D) (hF : RestFree D) (hA1 : RemainderSegmentBoundFirst D) (h2 : FamilyFourthBound D)
    (hA3 : RemainderSegmentBoundThird D) (hR : RootMultiplicityTwoBeyond D) (hA2 : RemainderSegmentBoundSecond D) (hE : RestExt D) : Closed (ExtendedAllConclusions D) := by
  apply closed_of_thr
  refine TransportedAlt.mono ?_ ((((((hF.and hA1).and h2).and hA3).and hR).and hA2).and hE)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨⟨⟨⟨f, a1⟩, k2⟩, ⟨Ct0, hCt0, a3⟩⟩, r2⟩, ⟨Ck0, hCk0, a2⟩⟩,
    ⟨Ck1, Ct1, hCk1, hCt1, e⟩⟩
  obtain ⟨Cs, hCs, k2⟩ := k2 (max Ck0 Ck1) (lt_max_of_lt_left hCk0)
  refine ⟨max Ck0 Ck1, max Ct0 Ct1, Cs, lt_max_of_lt_left hCk0, lt_max_of_lt_left hCt0, hCs, ?_⟩
  exact ⟨e _ _ (le_max_right _ _) (le_max_right _ _), k2, h3 _ _ _, r2.toExtendedDigitRankBound.toDigitRankBound, a1, a2 _ (le_max_left _ _),
    a3 _ (le_max_left _ _), r2.toExtendedDigitRankBound, r2, f⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def sd (m g : ℕ) : ℕ := Nat.choose (g + m) m

def mmB (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) : ℕ :=
  dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p)
      (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
      (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i) *
    symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ)

def UpAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      rankOnDigits O C0 CE1 CE2 X j m rz ry ≤ mmB C0 CE1 CE2 X j rz ry

def lowFac (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (m : ℕ) : ℝ :=
  (1 - Real.exp (-(X.La C0) / 8)) * (1 - Real.exp (-(X.La C0) / 3)) *
    (1 - (X.m : ℝ) * (m : ℝ) / ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ))

def LowAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j rz ry : ℝ) ≤ (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℝ)

def SegLowAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ *
        ((symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
          (∏ i, sd X.m (X.bT (segPos X.TT j i)) * sd X.m (X.aT (segPos X.TT j i))) *
          sd X.m (X.bT (segNext X.TT j)) : ℕ) : ℝ) ≤
        (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ)

def DimHHAt : Prop :=
  ∀ (Kf : Type) [Field Kf] [CharZero Kf] (n' m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    dimHH (m := m) Kf TT aT bT = ∏ s ∈ TT, sd m (aT s) * sd m (bT s)

def CharZeroAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ jO w → CharZero Kf

def RestUp : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => UpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestLow : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => LowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestSegLow : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SegLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def topOdd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT :=
  ⟨segPos X.TT j i, (pos_mem X.TT j i).1⟩

def topEnd (X : Loc) (j : Fin (numSeg X.TT)) : X.TT :=
  ⟨segNext X.TT j, (next_mem X.TT j).1⟩

def symVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → (X.TT × Bool) × Fin (X.m + 1)
  | Sum.inl (a, c) =>
    if h : (a : ℕ) < 2 * segS X.TT j then
      ((topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0)), c.succ)
    else ((topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j)), c.succ)
  | Sum.inr (l, b) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then
      ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩), !b), 0)
    else ((topEnd X j, !b), 0)

def symLev (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ
  | Sum.inl (a, _) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (X.seg C0 CE1 CE2 j).P p ⟨(a : ℕ) / 2, by omega⟩ else 1
  | Sum.inr (l, _) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then (X.seg C0 CE1 CE2 j).P p (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩) else 1

def digitMon (K : Type*) [CommSemiring K] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    MvPolynomial.X ((topOdd X j i, true), c) ^ b.rz i c * MvPolynomial.X ((topOdd X j i, false), c) ^ b.ry i c

def sTopMon (K : Type*) [CommSemiring K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    MvPolynomial.X ((topOdd X j i, true), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * (coarseA p (X.seg C0 CE1 CE2 j) b i - b.w i)) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * b.sg i)
  else 1

def ioBlock (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b *
    aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v) u

def symFam (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ j, ioBlock K p C0 CE1 CE2 X j (β j) (s j)

def Lemma44At (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) (β j)).SSZ O (r := X.m)) →
      ∃ F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        InA (C (algebraMap O (KK O) (S.w ^ (∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)))) * F) ∧
        InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c ∧
        ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
          ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g → InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g' F X.c

def IsFlatTheta {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O) (φ : WF p n' ≃+* W) {m : ℕ} (TT : Finset (Fin n'))
    (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT)) : Prop :=
  letI : Algebra (WF p n') O := algOfIdent jO φ
  (∀ F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O),
      InA (O := O) (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) ↔
      Θ F ∈ HHL (O := O) ι σ TT aT bT (colSpan W h)) ∧
    (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
      ∀ e : Edge W Qq (m + 1), IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
        ∀ (F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (i : ℕ),
          InWjRg p n' O w 1 (hhLetters TT) g (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) i ↔
          Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (ReHH p ι σ w TT aT bT e)) ∧
    ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → e.src = colSpan W h →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g ∧ IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose)

end Formalism.MainNotions.ColumnSystems.Pf
end
end
