module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle003
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def prodFrom (r K n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∏ i : Fin N, if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

theorem prodFrom_succ (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (hs : s < N) (hsn : s < n0) :
    prodFrom r K n0 B s = Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) * prodFrom r K n0 B (s + 1) := by
  classical
  unfold prodFrom
  have hpt : ∀ i : Fin N, (if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) =
      (if i = ⟨s, hs⟩ then Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) else 1) *
      (if s + 1 ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) := by
    intro i
    by_cases he : i = ⟨s, hs⟩
    · subst he
      rw [if_pos ⟨le_rfl, hsn⟩, if_pos rfl, if_neg (by simp), mul_one]
    · have hne : i.val ≠ s := fun h => he (Fin.ext h)
      rw [if_neg he, one_mul]
      by_cases h1 : s ≤ i.val ∧ i.val < n0
      · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
      · rw [if_neg h1, if_neg (by omega)]
  rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq' ]
  simp

theorem prodFrom_self_eq_one (n0 : ℕ) (B : Fin N → ℕ) : prodFrom r K n0 B n0 = 1 := by
  unfold prodFrom
  refine Finset.prod_eq_one fun i _ => ?_
  rw [if_neg (by omega)]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem pre_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D)
    (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (u s : ℕ) (hsu : s + u = n0) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (r + K) (μ0 ⟨s, by have := H.hN; omega⟩) * prodFrom r K n0 B s := by
  have hN := H.hN
  have hn : 0 < r + K := by have := H.r1; omega
  intro u
  induction u with
  | zero =>
    intro s hsu μ0 hv
    have hs : s = n0 := by omega
    subst hs
    rw [tau_count D h3 h4 H hfin r s (by omega) le_rfl μ0 hv, prodFrom_self_eq_one, mul_one,
      ← stCount_cast (Nat.add_comm K r) (μ0 ⟨s, by omega⟩)]
    congr 1
    funext l
    rw [tailT_apply r le_rfl]
    congr 1
    exact Fin.ext (by simp)
  | succ u ih =>
    intro s hsu μ0 hv
    have hsn : s < n0 := by omega
    have hs : s < N := by omega
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    rw [prodFrom_succ n0 B s hs hsn, ← mul_assoc]
    show _ = stCount (r + K) (μ0 (⟨s, hs⟩ : Fin N).castSucc) * _ * _
    cases hvec : LL.vec ⟨s, hs⟩ with
    | true =>
      rw [pieri_vec D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_pos hvec]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_up hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_pos hvec] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun x => Finset.mem_Icc.mpr ⟨hS.1 x, strip_le_add hS x⟩, hS⟩
    | false =>
      rw [pieri_cov D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_neg (by simp [hvec])]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_down hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_neg (by simp [hvec])] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun x => Finset.mem_Icc.mpr ⟨?_, hS.1 x⟩, hS⟩
        have := strip_le_add hS x
        linarith

end

theorem path_weight_eq_rank (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D) : PathWeightEqRank := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hfin := finite_SAll H
  refine ⟨hfin, ?_⟩
  have hv : VP (r := r) (K := K) LL n0 B 0 (fun _ => 0) :=
    ⟨rfl, fun _ _ _ _ _ => le_rfl, fun i hi => absurd hi (by omega)⟩
  have h := pre_count D h3 h4 h5 H hfin n0 0 (by omega) (fun _ => 0) hv
  have hA : Af hfin 0 (fun _ => 0) = hfin.toFinset := by
    unfold Af
    rw [Finset.filter_eq_self]
    intro q hq t ht
    rw [Set.Finite.mem_toFinset] at hq
    have ht0 : t = 0 := Fin.ext (by simpa using ht)
    rw [ht0]
    exact ((sp_iff H q.1).1 hq.1).1
  rw [Set.ncard_eq_toFinset_card _ hfin, ← hA, h]
  have h0 : stCount (r + K) ((fun _ => 0 : Fin (N + 1) → Fin (r + K) → ℤ) ⟨0, by omega⟩) = 1 := stCount_zero D h3 (r + K)
  rw [h0, one_mul]
  unfold prodFrom rkA
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumBin (r K n : ℕ) : ℝ := ((Nat.choose (n + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

theorem sum_one_le_bin (r K n : ℕ) : 1 ≤ sumBin r K n := by
  unfold sumBin
  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos (by omega))

theorem sum_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1

theorem sum_single_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) {a : ι} (ha : a ∈ s) :
    f a ≤ ∏ i ∈ s, f i := by
  classical
  rw [← Finset.mul_prod_erase s f ha]
  have h2 : (1 : ℝ) ≤ ∏ i ∈ s.erase a, f i := sum_one_le_prod _ _ fun i hi => h1 i (Finset.mem_of_mem_erase hi)
  have h3 : 0 ≤ f a := le_trans zero_le_one (h1 a ha)
  nlinarith

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def sumTset (la : Fin n' → Fin (r + K) → ℕ) (j : ℤ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = X.nz p K la j (X.F.fr j i.val) % X.Qc p K j

def sumhT (t : Fin n') (v : Fin (r + K) → ℕ) : ℝ :=
  ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ),
    if posOf n' x = t then sumBin r K ((X.a' p K t - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1

def sumSt (t : Fin n') : ℝ := ∑ v ∈ X.laSet p K t, X.sumhT p K t v


omit [NeZero n'] in
def firstSumFactor : ℝ := 1 - 1 / X.a ^ (X.Ns ^ 2)

def sumWf (j : ℤ) : ℝ := ∏ i : Fin r, sumBin r K ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat)

def sumTf (j : ℤ) : ℝ := (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r

theorem sum_segBound_eq (j : ℤ) (b : ℤ → ℕ) :
    X.segBound p K j b = (X.firstSumFactor * X.sumWf p K j * X.sumTf p K j) * ∏ x ∈ X.F.LLset j, sumBin r K (b x) := by
  unfold segBound firstSumFactor sumWf sumTf sumBin
  ring

end Dat

structure SumFacts {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  tiling : ∀ φ : Fin n' → ℝ,
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x)
  split : ∀ (j : ℤ) (ψ : ℤ → ℝ),
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val)
  LLsub : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j ∧ x < X.F.fr j 0
  frlate : ∀ j (i : Fin r), X.F.fr j i.val ∈ X.toLate j
  uniqP : ∀ j j' x x', x ∈ X.toLate j → x' ∈ X.toLate j' → posOf n' x = posOf n' x' →
    X.Pz p K j x = X.Pz p K j' x'
  kP : ∀ j x, x ∈ X.toLate j → (r + K) * X.Pz p K j x ≤ X.a' p K (posOf n' x)
  compA : ∀ t ∈ X.F.TT, sumBin r K (X.deg t) * (1 - 5 / X.Y) ≤ sumBin r K (X.a' p K t)
  compW : ∀ j (i : Fin r), sumBin r K (X.a' p K (posOf n' (X.F.fr j i.val))) * (1 - 1 / X.Y) ≤
    (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) ^ (r + K - 1) *
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  prodQ : ∏ j ∈ Finset.range X.F.J, X.Qc p K (j : ℤ) = p ^ n'
  perW : ∀ j (i : Fin r),
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val)
  JN : X.F.J ≤ X.F.TT.card
  a32 : 32 * X.Y ≤ X.a

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

omit [NeZero n'] in
theorem sum_eZ_val (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) : X.eZ e (j.val : ℤ) = e j := by
  have hJ : 0 < X.F.J := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  unfold Dat.eZ
  rw [dite_eq_left hJ]
  congr 1
  apply Fin.ext
  have h1 : ((j.val : ℤ) % (X.F.J : ℤ)) = j.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  simp only [h1, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt j.isLt

theorem sum_late_mem {j x : ℤ} (hx : x ∈ X.toLate j) :
    x ∈ X.F.letters j ∧ ¬ X.F.IsW j x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have hx' := Finset.mem_filter.mp hx
  have h2 := Finset.mem_filter.mp hx'.1
  exact ⟨hx'.1, hx'.2, (Finset.mem_Icc.mp h2.1).2, h2.2⟩

theorem sum_bfam_late (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (x : ℤ)
    (hx : x ∈ X.toLate (j.val : ℤ)) :
    X.bfam p K la e (j.val : ℤ) x = X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j) x := by
  obtain ⟨h1, h2, h3, -⟩ := sum_late_mem hx
  unfold Dat.bfam Dat.setTau
  rw [if_pos h1, if_neg h2, sum_eZ_val]
  by_cases h : X.F.fr (j.val : ℤ) 0 ≤ x
  · rw [if_pos h, if_pos ⟨h, h3⟩]
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

theorem family_degrees_admissible (hr : 0 < r) (hp : 0 < p) (hLL : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j)
    (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j : ℤ) :
    X.AdmLL p K j (X.nz p K la j) := by
  classical
  intro x hx
  have hv : la (posOf n' x) ∈ X.laSet p K (posOf n' x) := (Fintype.mem_piFinset.mp hla) _
  obtain ⟨-, hle, hall⟩ := Finset.mem_filter.mp hv
  obtain ⟨hlt, hmod⟩ := hall j x (hLL j x hx) rfl
  set P := X.Pz p K j x with hPdef
  set n := X.a' p K (posOf n' x) with hn
  set s := ∑ c, la (posOf n' x) c with hs
  have hP : 0 < P := by rw [hPdef]; unfold Dat.Pz; exact pow_pos hp _
  have hdvd : P ∣ n - s := (Nat.modEq_iff_dvd' hle).mp hmod
  have hnz : X.nz p K la j x = (n - s) / P := rfl
  have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hcast : ((X.nz p K la j x : ℕ) : ℝ) = ((n : ℝ) - s) / P := by
    rw [hnz, Nat.cast_div hdvd hPr.ne', Nat.cast_sub hle]
  have hslt : s < (r + K) * P := by
    calc s < ∑ _c : Fin (r + K), P := by
            rw [hs]
            exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun c _ => hlt c
      _ = (r + K) * P := by simp
  have hslt' : (s : ℝ) < Dat.k (r := r) K * P := by
    unfold Dat.k
    exact_mod_cast hslt
  rw [hcast]
  constructor
  · rw [sub_div, sub_lt_sub_iff_left, div_lt_iff₀ hPr]
    exact hslt'
  · exact div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg _; linarith) hPr.le

theorem first_sum_factor_bounds (hY : 1 ≤ X.Y) (ha : 32 * X.Y ≤ X.a) (hNs : 1 ≤ X.Ns) :
    1 - 1 / (32 * X.Y) ≤ X.firstSumFactor ∧ 0 ≤ X.firstSumFactor := by
  have ha1 : 1 ≤ X.a := by linarith
  have h1 : X.a ≤ X.a ^ (X.Ns ^ 2) := by
    calc X.a = X.a ^ 1 := (pow_one _).symm
      _ ≤ X.a ^ (X.Ns ^ 2) := pow_le_pow_right₀ ha1 (Nat.one_le_pow _ _ hNs)
  have h2 : 1 / X.a ^ (X.Ns ^ 2) ≤ 1 / (32 * X.Y) :=
    one_div_le_one_div_of_le (by linarith) (ha.trans h1)
  have h3 : 1 / (32 * X.Y) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  unfold Dat.firstSumFactor
  constructor <;> linarith

end Steps

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)


open Classical in
def restr (j : ℤ) (b : ℤ → ℕ) : ℤ → ℕ := fun x => if x ∈ X.toLate j then b x else 0


open Classical in
def Bdeg (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  if X.F.IsW j x then (X.Bw p K j x - (X.m0 K : ℤ)).toNat else b x

def beS (j : ℤ) (b : ℤ → ℕ) : ℕ := ∑ x ∈ (X.F.letters j).filter (· < X.F.fr j 0), X.Bdeg p K j b x

structure IsPATH (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) : Prop where
  path : ∃ P : PPath (r + K) (segN X.F j) (segLL X.F j) dd, P.mu = μ
  degs : ∀ i, segE X.F j i < X.F.fr j 0 → dd i = X.Bdeg p K j b (segE X.F j i)
  head : ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
    ∀ m : Fin (r + K), m.val ≤ i'.val → μ i.succ m = (X.beS p K j b : ℤ)

def IsGood [NeZero r] (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin (segN X.F j), ¬ X.F.IsW j (segE X.F j i) →
    X.thc p K j b (segE X.F j i) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (Even (segE X.F j i) →
      ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i)) ∧
    (¬ Even (segE X.F j i) →
      ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i))

def Tset [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2}

def Idx [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2.1 ∧
      (∀ v, q.2.2 v + 2 * X.beS p K j b < X.Qc p K j) ∧
      ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
        dd i + ∑ c, q.2.2 (i', c) = b (X.F.fr j i'.val)}


omit [NeZero n'] in
def Dw (O : Type) [CommRing O] (j : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  Matrix.det (Matrix.of fun a c : Fin r => (MvPolynomial.X (X.F.fr (j - 1) a.val, c) : MvPolynomial (ℤ × Fin r) O))

def famEl [NeZero r] (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  plEmb O r K (X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) *
      ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ q.2.2 v) *
    segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

def BOK (j : ℤ) (b : ℤ → ℕ) : Prop :=
  (∀ x, x ∉ X.F.letters j → b x = 0) ∧
  (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (b x : ℤ)) ∧ X.AdmLL p K j b

end Dat

def RestMem (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b), X.famEl p K O j b q.1 ∈ X.Mj p K O j b

def RestInd (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1

def RestFin : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : ℤ) (b : ℤ → ℕ), (∀ x, x ∉ X.F.letters j → b x = 0) →
    Module.Finite O (X.Mj p K O j b)

def GoodPathWeight (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) ∧
      (1 - 1 / X.a ^ (X.Ns ^ 2)) *
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ≤ (Nat.card (X.Tset p K j (X.restr j b)) : ℝ)


open Classical in
def RestMon (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) → ∀ ρ : Fin r → ℕ,
      (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) *
          (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r ≤
        ∑ e ∈ Fintype.piFinset fun i : Fin r =>
          (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
            (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ)

theorem restSeg_of (C₀ : ℝ) (hM : RestMem C₀) (hI : RestInd C₀) (hF : RestFin) (hT : GoodPathWeight C₀) (hN : RestMon C₀) :
    RestSeg C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j
  refine ⟨fun b => (Nat.card (X.Idx p K j (X.restr j b)) : ℝ), fun b => Nat.cast_nonneg _, ?_, ?_, ?_⟩
  · intro b b' hbb
    have : X.restr j b = X.restr j b' := by
      funext x
      unfold Dat.restr
      split_ifs with hx
      · exact hbb x hx
      · rfl
    simp only [this]
  · intro b h0 hW hA
    have hB : X.BOK p K j b := ⟨h0, hW, hA⟩
    have hfin := hF p n' r K X O j b h0
    have hli := hI p n' r K X O S hX hLa hk j b hB
    have hmem := hM p n' r K X O S hX hLa hk j b hB
    have hli' : LinearIndependent O
        (fun q : X.Idx p K j (X.restr j b) => (⟨X.famEl p K O j b q.1, hmem q⟩ : X.Mj p K O j b)) := by
      refine LinearIndependent.of_comp (X.Mj p K O j b).subtype ?_
      exact hli
    have hfinI : Finite (X.Idx p K j (X.restr j b)) := hli'.finite
    have := Fintype.ofFinite (X.Idx p K j (X.restr j b))
    have h := hli'.fintype_card_le_finrank
    beta_reduce
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast h
  · intro b hA ρ
    obtain ⟨hfin, hT1⟩ := hT p n' r K X hX hLa hk j b hA
    refine le_trans ?_ (hN p n' r K X hX hLa hk j b hA hfin ρ)
    unfold Dat.segBound
    exact mul_le_mul_of_nonneg_right hT1 (by positivity)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
