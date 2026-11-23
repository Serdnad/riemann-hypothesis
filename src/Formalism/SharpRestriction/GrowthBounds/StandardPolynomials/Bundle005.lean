module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockSupported
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle004
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem prod_uTop {M : Type} [CommMonoid M] {s : ℕ} (S : SegData s) (f : Fin s → M) :
    ∏ i, f i = (∏ i : Fin s, if (i : ℕ) < S.sigma then f i else 1) * ∏ l : Fin S.t, f (uTop S l) := by
  classical
  have h1 : ∏ l : Fin S.t, f (uTop S l) = ∏ i : Fin s, if S.sigma ≤ i.val then f i else 1 := by
    rw [← Finset.prod_filter]
    refine Finset.prod_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro l _
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
    · intro l _ l' _ h
      apply Fin.ext
      have h' : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
      omega
    · intro i hi
      have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
      have := i.2
      exact ⟨⟨i.val - S.sigma, by unfold SegData.t; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _),
        Fin.ext (by show S.sigma + (i.val - S.sigma) = i.val; omega)⟩
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < S.sigma
  · rw [if_pos h, if_neg (by omega), mul_one]
  · rw [if_neg h, if_pos (by omega), one_mul]

def mEps (K : Type) [CommRing K] {s r : ℕ} (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    MvPolynomial (Fin (2 * s + 1) × Fin r) K :=
  (∏ i, ∏ c, (X (chW i, c) ^ ez i c * X (chE i, c) ^ ey i c)) * ∏ c, X (chU s, c) ^ ax c

section A

variable (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))

def ezA (A : MonH X) (i : Fin (segS X.TT j)) (c : Fin X.m) : ℕ :=
  A ((topOdd X j i, true), c.succ) / (X.seg C0 CE1 CE2 j).P X.p i
def eyA (A : MonH X) (i : Fin (segS X.TT j)) (c : Fin X.m) : ℕ :=
  A ((topOdd X j i, false), c.succ) / (X.seg C0 CE1 CE2 j).P X.p i
def axA (A : MonH X) (c : Fin X.m) : ℕ := A ((topEnd X j, true), c.succ)
def z0A (A : MonH X) (i : Fin (segS X.TT j)) : ℕ := A ((topOdd X j i, true), 0) / (X.seg C0 CE1 CE2 j).P X.p i
def y0A (A : MonH X) (i : Fin (segS X.TT j)) : ℕ := A ((topOdd X j i, false), 0) / (X.seg C0 CE1 CE2 j).P X.p i

def segmentBlockOfMonomial (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) :
    SegBlock (segS X.TT j) X.m where
  rz := fun i c => A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i
  ry := fun i c => A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i
  o := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
    jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c
  w := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then du (chW i) + ∑ c, ezA C0 CE1 CE2 X j A i c else 0
  sg := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then y0A C0 CE1 CE2 X j A i else 0
  oPlus := jp + du (chU _) + ∑ c, axA X j A c

theorem ioA_X (v : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :
    ioA (KK O) X.p C0 CE1 CE2 X j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioA
  rw [aeval_X]

theorem ioA_mEps (ez ey : Fin (segS X.TT j) → Fin X.m → ℕ) (ax : Fin X.m → ℕ) :
    ioA (KK O) X.p C0 CE1 CE2 X j (rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (mEps (KK O) ez ey ax)) =
      (∏ i, ∏ c : Fin X.m, ((MvPolynomial.X ((topOdd X j i, true), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^ ez i c *
        (MvPolynomial.X ((topOdd X j i, false), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^ ey i c)) *
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, true), c.succ) ^ ax c := by
  unfold mEps
  simp only [map_mul, map_prod, map_pow, rename_X, chainEmb, ioA_X]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun c _ => ?_
    have a1 := symbol_variable_lower_letter C0 CE1 CE2 X j i c
    have a2 := symbol_level_lower_letter C0 CE1 CE2 X j i c
    have a3 := sv_E C0 CE1 CE2 X j i c
    have a4 := sl_E C0 CE1 CE2 X j i c
    unfold chW chE
    rw [a1, a2, a3, a4]
  · refine Finset.prod_congr rfl fun c _ => ?_
    have a1 := sv_U C0 CE1 CE2 X j c
    have a2 := sl_U C0 CE1 CE2 X j c
    unfold chU
    rw [a1, a2, pow_one]

theorem segMon_eq (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X)
    (γ : Fin X.m → ℕ)
    (hz0 : ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
      coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i - (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).w i =
        z0A C0 CE1 CE2 X j A i)
    (hy0 : A ((topEnd X j, false), 0) = 0) (hγ : ∀ c : Fin X.m, A ((topEnd X j, false), c.succ) = γ c) :
    segMon O X j A =
      digitMon (KK O) C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) *
        sTopMon (KK O) X.p C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) *
      (ioA (KK O) X.p C0 CE1 CE2 X j (rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t)
          (mEps (KK O) (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A))) *
        ioA (KK O) X.p C0 CE1 CE2 X j (∏ l : Fin (X.seg C0 CE1 CE2 j).t,
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) *
            MvPolynomial.X (scalS (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))) *
        ioA (KK O) X.p C0 CE1 CE2 X j
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _)) ^ A ((topEnd X j, true), 0)) *
        ioA (KK O) X.p C0 CE1 CE2 X j (∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t c) ^ γ c)) := by
  classical
  set P := fun i => (X.seg C0 CE1 CE2 j).P X.p i with hP
  set Xz : Fin (segS X.TT j) → Fin (X.m + 1) → RHH O X := fun i c => MvPolynomial.X ((topOdd X j i, true), c) with hXz
  set Xy : Fin (segS X.TT j) → Fin (X.m + 1) → RHH O X := fun i c => MvPolynomial.X ((topOdd X j i, false), c) with hXy

  have i2 : ioA (KK O) X.p C0 CE1 CE2 X j (∏ l : Fin (X.seg C0 CE1 CE2 j).t,
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) *
            MvPolynomial.X (scalS (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))) =
      ∏ l : Fin (X.seg C0 CE1 CE2 j).t, ((fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i *
        (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) (uTop (X.seg C0 CE1 CE2 j) l)) := by
    simp only [map_prod, map_mul, map_pow, ioA_X]
    refine Finset.prod_congr rfl fun l _ => ?_
    unfold scalZ scalS
    rw [sv_Z, sl_Z, sv_Z, sl_Z]
    rfl
  have i3 : ioA (KK O) X.p C0 CE1 CE2 X j
      (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _)) ^ A ((topEnd X j, true), 0)) =
      MvPolynomial.X ((topEnd X j, true), 0) ^ A ((topEnd X j, true), 0) := by
    rw [map_pow, ioA_X]
    unfold scalZ
    rw [symbol_variable_last, symbol_level_last, pow_one]
    rfl
  have i4 : ioA (KK O) X.p C0 CE1 CE2 X j
      (∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t c) ^ γ c) =
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ γ c := by
    simp only [map_prod, map_pow, ioA_X]
    refine Finset.prod_congr rfl fun c _ => ?_
    unfold xiVar
    rw [sv_xi, sl_xi, pow_one]
  rw [ioA_mEps, i2, i3, i4]

  have hS : sTopMon (KK O) X.p C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) =
      ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) i else 1 := by
    unfold sTopMon
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, hz0 i h]
      have : (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).sg i = y0A C0 CE1 CE2 X j A i := by
        show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
        rw [if_pos h]
      rw [this, pow_mul, pow_mul]
    · rw [if_neg h, if_neg h]
  rw [hS]

  have hodd : ∀ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      (Xz i c ^ A ((topOdd X j i, true), c) * Xy i c ^ A ((topOdd X j i, false), c)) =
      (∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) * Xy i c ^ (A ((topOdd X j i, false), c) % P i))) *
      ((Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) *
      ∏ c : Fin X.m, ((Xz i c.succ ^ P i) ^ ezA C0 CE1 CE2 X j A i c * (Xy i c.succ ^ P i) ^ eyA C0 CE1 CE2 X j A i c) := by
    intro i
    have e1 : ∀ c : Fin (X.m + 1), Xz i c ^ A ((topOdd X j i, true), c) * Xy i c ^ A ((topOdd X j i, false), c) =
        (Xz i c ^ (A ((topOdd X j i, true), c) % P i) * Xy i c ^ (A ((topOdd X j i, false), c) % P i)) *
        ((Xz i c ^ P i) ^ (A ((topOdd X j i, true), c) / P i) * (Xy i c ^ P i) ^ (A ((topOdd X j i, false), c) / P i)) := by
      intro c
      conv_lhs => rw [← Nat.mod_add_div (A ((topOdd X j i, true), c)) (P i),
        ← Nat.mod_add_div (A ((topOdd X j i, false), c)) (P i)]
      rw [pow_add, pow_add, pow_mul, pow_mul]
      ring
    rw [Finset.prod_congr rfl fun c _ => e1 c, Finset.prod_mul_distrib, mul_assoc]
    congr 1
    rw [Fin.prod_univ_succ]
    rfl
  unfold segMon digitMon
  rw [Finset.prod_congr rfl fun i _ => hodd i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_uTop (X.seg C0 CE1 CE2 j) (fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i)]
  have hend : ∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^ A ((topEnd X j, true), c) *
      MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c)) =
      (∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, true), c.succ) ^ axA X j A c) *
      MvPolynomial.X ((topEnd X j, true), 0) ^ A ((topEnd X j, true), 0) *
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ γ c := by
    rw [Fin.prod_univ_succ, hy0, pow_zero, mul_one, Finset.prod_mul_distrib]
    simp only [hγ]
    unfold axA
    ring
  rw [hend]
  show (∏ i, ∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) *
      Xy i c ^ (A ((topOdd X j i, false), c) % P i))) * _ * _ * _ =
    (∏ i, ∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) *
      Xy i c ^ (A ((topOdd X j i, false), c) % P i))) * _ * _
  ring

end A

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev TgPlace (X : Loc) := Σ j : Fin (numSeg X.TT), Option (Fin (segS X.TT j))

def tgTop (X : Loc) : TgPlace X → X.TT
  | ⟨j, none⟩ => topEnd X j
  | ⟨j, some i⟩ => topOdd X j i

theorem tg_end_ne_odd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topEnd X j ≠ topOdd X j i := by
  intro h
  have e : segNext X.TT j = segPos X.TT j i := congrArg Subtype.val h
  exact (pos_mem X.TT j i).2 (e ▸ (next_mem X.TT j).2)

theorem tgTop_mem (X : Loc) (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)) :
    ((tgTop X pl, b), c) ∈ segVars X pl.1 := by
  obtain ⟨j, a⟩ := pl
  cases a with
  | none => exact Or.inl rfl
  | some i => exact Or.inr ⟨i, rfl⟩

theorem tgTop_inj (X : Loc) : Function.Injective (tgTop X) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  have hj : j = j' := by
    by_contra hne
    have h1 := tgTop_mem X ⟨j, a⟩ true 0
    have h2 := tgTop_mem X ⟨j', a'⟩ true 0
    rw [← h] at h2
    exact Set.disjoint_left.1 (segVars_disj X j j' hne) h1 h2
  subst hj
  cases a with
  | none =>
    cases a' with
    | none => rfl
    | some i => exact absurd h (tg_end_ne_odd X j i)
  | some i =>
    cases a' with
    | none => exact absurd h.symm (tg_end_ne_odd X j i)
    | some i' => rw [topOdd_inj X j h]

theorem tgTop_surj (X : Loc) (h2 : 2 ≤ numSeg X.TT) : Function.Surjective (tgTop X) := by
  rintro ⟨t, ht⟩
  by_cases he : Even t.val
  · obtain ⟨j0, hj0⟩ := List.mem_iff_get.mp ((ev_mem X.TT t).mpr ⟨ht, he⟩)
    obtain ⟨j, hj⟩ := (rot_bij (numSeg X.TT)).2 j0
    refine ⟨⟨j, none⟩, Subtype.ext ?_⟩
    show segNext X.TT j = t
    rw [next_eq, hj]
    exact hj0
  · obtain ⟨j, hj⟩ := odd_covered X.TT h2 t ht he
    have hs := Finset.mem_filter.mp hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (mem_dists.mpr ⟨t, hs, rfl⟩)
    refine ⟨⟨j, some i⟩, Subtype.ext ?_⟩
    show segPos X.TT j i = t
    unfold segPos
    rw [hi, posAdd_cdist]

theorem tgTop_bij (X : Loc) (h2 : 2 ≤ numSeg X.TT) : Function.Bijective (tgTop X) :=
  ⟨tgTop_inj X, tgTop_surj X h2⟩

theorem tg_prod_places {M : Type} [CommMonoid M] (X : Loc) (h2 : 2 ≤ numSeg X.TT) (f : X.TT → M) :
    ∏ t, f t = ∏ j, (f (topEnd X j) * ∏ i, f (topOdd X j i)) := by
  rw [← (tgTop_bij X h2).prod_comp f, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.prod_option]
  rfl

theorem tg_mono_split (O : Type) [CommRing O] [IsDomain O] (X : Loc) (h2 : 2 ≤ numSeg X.TT) (A : MonH X) :
    (monomial A (1 : KK O) : RHH O X) = ∏ j, segMon O X j A := by
  rw [MvPolynomial.monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fintype.prod_prod_type, tg_prod_places X h2]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold segMon
  simp only [Fintype.prod_bool, Finset.prod_mul_distrib]
  ring

theorem tg_prod_uTop {M : Type} [CommMonoid M] {s : ℕ} (S : SegData s) (g : Fin s → M) :
    ∏ l : Fin S.t, g (uTop S l) = ∏ i : Fin s, if S.sigma ≤ i.val then g i else 1 := by
  rw [← Finset.prod_filter]
  refine Finset.prod_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro l _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
  · intro l _ l' _ h
    have : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  · intro i hi
    have hi' : S.sigma ≤ i.val := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    refine ⟨⟨i.val - S.sigma, by unfold SegData.t; have := i.2; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    apply Fin.ext
    show S.sigma + (i.val - S.sigma) = i.val
    omega

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def PreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β)
      (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)),
      (∀ j, ColSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L j (G j)) → (∀ j, G j ≠ 0) →
    ∀ Std : MonH X, (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j →
      Nonempty (PreSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L G Std)

def RestPre : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [instance] PreSys.finC PreSys.finM

def TCoreBody (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (mm : ℝ) (n : ℕ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (Std : MonH X) : Prop :=
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (ju : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ j i, ju j i ≤ L.lv j i) →
    ∀ (Gu : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
      (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ),
      (∀ j, Gu j ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)) →
      (∀ j, Gu j ∈ Pol (KK O) X.m (du j)) → (∀ j a, du j a ≤ (L.LL j).deg a) →
      (∀ j k, Gu j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,
      (∀ l, ∑ c, (Std (l, c) - A (l, c)) ≤ X.p ^ X.G' * e) → (∀ l, ∑ c, (A (l, c) - Std (l, c)) ≤ X.p ^ X.G' * e) →
      (∀ j c, A ((topEnd X j, false), c) = Std ((topEnd X j, false), c)) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) →
      (∀ m ∈ ((∏ j, L.head O j (ju j) (Gu j)) * monomial A 1).support, ndM X m ≤ ordFam C0 CE1 CE2 X β + e) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e

section Small

theorem sum_split {κ : Type} [Fintype κ] (mult u d : κ → ℕ) (hu : ∀ a, u a ≤ mult a) :
    ∑ a, (mult a - u a) * d a + ∑ a, u a * d a = ∑ a, mult a * d a := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Nat.add_mul, Nat.sub_add_cancel (hu a)]

theorem chain_pol_one (K : Type) [CommRing K] {ι : Type} {n : ℕ} : (1 : MvPolynomial (ι × Fin n) K) ∈ Pol K n (fun _ : ι => 0) := by
  have h := Formalism.MainNotions.G.Joints.StandardMonomialSpace.hom_Pol_C K (ι := ι) (n := n) (1 : K)
  rw [C_1] at h
  exact h

theorem chain_pol_pow (K : Type) [CommRing K] {ι : Type} {n : ℕ} {d : ι → ℕ} {P : MvPolynomial (ι × Fin n) K}
    (h : P ∈ Pol K n d) (u : ℕ) : P ^ u ∈ Pol K n (fun i => u * d i) := by
  induction u with
  | zero => simpa using chain_pol_one K (ι := ι) (n := n)
  | succ u ih =>
    rw [pow_succ]
    have := Formalism.MainNotions.G.Joints.StandardMonomialSpace.hom_Pol_mul K ih h
    have e : ((fun i => u * d i) + d) = fun i => (u + 1) * d i := by funext i; simp [Nat.succ_mul]
    rwa [e] at this

theorem chain_pol_prod (K : Type) [CommRing K] {ι κ : Type} {n : ℕ} (s : Finset κ) (d : κ → ι → ℕ)
    (P : κ → MvPolynomial (ι × Fin n) K) (h : ∀ a ∈ s, P a ∈ Pol K n (d a)) :
    ∏ a ∈ s, P a ∈ Pol K n (fun i => ∑ a ∈ s, d a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using chain_pol_one K (ι := ι) (n := n)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have := Formalism.MainNotions.G.Joints.StandardMonomialSpace.hom_Pol_mul K (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    have e : (d a + fun i => ∑ a ∈ s, d a i) = fun i => ∑ b ∈ insert a s, d b i := by
      funext i; simp [Finset.sum_insert ha]
    rwa [e] at this

theorem glIntOne {O : Type} [CommRing O] [IsDomain O] {σ : Type} : (1 : MvPolynomial σ (KK O)) ∈ IntPol O σ := ⟨1, by simp⟩

theorem glIntMul {O : Type} [CommRing O] [IsDomain O] {σ : Type} {x y : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ)
    (hy : y ∈ IntPol O σ) : x * y ∈ IntPol O σ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

theorem glIntPow {O : Type} [CommRing O] [IsDomain O] {σ : Type} {x : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (u : ℕ) :
    x ^ u ∈ IntPol O σ := by
  induction u with
  | zero => simpa using glIntOne (O := O) (σ := σ)
  | succ u ih => rw [pow_succ]; exact glIntMul ih hx

theorem glIntProd {O : Type} [CommRing O] [IsDomain O] {σ κ : Type} (s : Finset κ) (P : κ → MvPolynomial σ (KK O))
    (h : ∀ a ∈ s, P a ∈ IntPol O σ) : ∏ a ∈ s, P a ∈ IntPol O σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using glIntOne (O := O) (σ := σ)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact glIntMul (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem monomial_sum_eq_prod_tensor {X : Loc} {O : Type} [CommRing O] [IsDomain O] {ι : Type} (s : Finset ι) (a : ι → MonH X) :
    (monomial (∑ i ∈ s, a i) (1 : KK O) : RHH O X) = ∏ i ∈ s, (monomial (a i) (1 : KK O) : RHH O X) := by
  have := mono_sum (O := O) s (fun _ => 1) a
  simpa using this

end Small

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mu : ℝ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 mu X β} {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

def PreSys.sgR (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : RHH O X :=
  (∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) * monomial P.R 1

def PreSys.sgC (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (j : Fin (numSeg X.TT)) (a : P.ιC j) : RHH O X :=
  monomial (P.pl j a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (P.Kc j a))

def PreSys.sgH (_P : PreSys C0 CE1 CE2 X O w mu β L G Std) (j : Fin (numSeg X.TT))
    (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) : RHH O X :=
  ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i)

theorem PreSys.ident (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (nC : ∀ j, P.ιC j → ℕ)
    (nH : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ) (nM : P.ιM → ℕ) (M : MonH X) :
    P.sgR * ((∏ j, ∏ a, P.sgC j a ^ nC j a) * ((∏ j, ∏ i, P.sgH j i ^ nH j i) *
        ∏ a, (monomial (P.aM a) (1 : KK O) : RHH O X) ^ nM a)) * monomial M 1 =
      (∏ j, L.head O j (nH j) (∏ a, P.Kc j a ^ nC j a)) *
        monomial (P.R + ((∑ j, ∑ a, nC j a • P.pl j a) + ∑ a, nM a • P.aM a) + M) 1 := by
  have e1 : (monomial (P.R + ((∑ j, ∑ a, nC j a • P.pl j a) + ∑ a, nM a • P.aM a) + M) (1 : KK O) : RHH O X) =
      monomial P.R 1 * ((∏ j, ∏ a, (monomial (P.pl j a) (1 : KK O) : RHH O X) ^ nC j a) *
        ∏ a, (monomial (P.aM a) (1 : KK O) : RHH O X) ^ nM a) * monomial M 1 := by
    rw [← mono_sum, ← Finset.prod_congr rfl (fun j _ => mono_sum (O := O) Finset.univ (nC j) (P.pl j)), ← monomial_sum_eq_prod_tensor]
    simp only [monomial_mul, one_mul]
  rw [e1]
  unfold PreSys.sgR PreSys.sgC PreSys.sgH LvDat.head
  simp only [map_mul, map_prod, map_pow, mul_pow, Finset.prod_mul_distrib]
  ring

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
end
end
