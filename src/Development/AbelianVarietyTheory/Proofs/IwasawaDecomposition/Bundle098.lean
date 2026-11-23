module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.XiSat

section general
variable {R : Type} [CommRing R]

theorem smodEq_iff (p : R) (k : ℕ) (a b : R) :
    (a ≡ b [SMOD (Ideal.span {p} ^ k • ⊤ : Submodule R R)]) ↔ p ^ k ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem sat_pow [IsDomain R] (p x : R) (h : ∀ a, x ∣ p * a → x ∣ a) (n : ℕ) :
    ∀ a, x ^ n ∣ p * a → x ^ n ∣ a := by
  by_cases hx : x = 0
  · cases n with
    | zero => intro a _; simp
    | succ n => subst hx; simpa using h
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a ha
    obtain ⟨b, rfl⟩ := h a ((dvd_pow_self x n.succ_ne_zero).trans ha)
    rw [pow_succ'] at ha ⊢
    rw [mul_left_comm, mul_dvd_mul_iff_left hx] at ha
    exact mul_dvd_mul_left x (ih b ha)

theorem sat_ppow (p y : R) (h : ∀ a, y ∣ p * a → y ∣ a) (k : ℕ) :
    ∀ a, y ∣ p ^ k * a → y ∣ a := by
  induction k with
  | zero => intro a ha; simpa using ha
  | succ k ih =>
    intro a ha
    rw [pow_succ', mul_assoc] at ha
    exact ih a (h _ ha)

theorem quot_dvd_iff (p y : R) (k : ℕ) (a : R) :
    (Ideal.Quotient.mk (Ideal.span {y}) p) ^ k ∣ Ideal.Quotient.mk (Ideal.span {y}) a ↔
      ∃ b c, a = y * b + p ^ k * c := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
    obtain ⟨b, hb⟩ := hc
    exact ⟨b, c, by linear_combination hb⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨b, by ring⟩

theorem complete_quot [IsDomain R] (p y : R) [hc : IsAdicComplete (Ideal.span {p}) R]
    (h : ∀ a, y ∣ p * a → y ∣ a) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {y}) p}) (R ⧸ Ideal.span {y}) := by
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [smodEq_iff, sub_zero, quot_dvd_iff] at hx
    choose b c hbc using hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    by_cases hy : y = 0
    · subst hy
      have : a = 0 := IsHausdorff.haus' (I := Ideal.span {p}) a fun k => by
        rw [smodEq_iff]
        exact ⟨c k, by linear_combination hbc k⟩
      simp [this]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) b fun {m n} hmn => by
      rw [smodEq_iff]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have e : y * (b m - b (m + d)) = p ^ m * (p ^ d * c (m + d) - c m) := by
        linear_combination hbc (m + d) - hbc m
      obtain ⟨w, hw⟩ := sat_ppow p y h m _ ⟨_, e.symm⟩
      refine ⟨w, mul_left_cancel₀ hy ?_⟩
      rw [e, hw]; ring
    have : a - y * L = 0 := IsHausdorff.haus' (I := Ideal.span {p}) _ fun k => by
      obtain ⟨w, hw⟩ := (smodEq_iff p k _ _).1 (hL k)
      rw [smodEq_iff]
      exact ⟨c k + y * w, by linear_combination hbc k + y * hw⟩
    exact ⟨L, by linear_combination this⟩
  · intro f hf
    choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    have h1 : ∀ n, ∃ b c, g n - g (n + 1) = y * b + p ^ n * c := fun n => by
      have := (smodEq_iff _ n _ _).1 (hf (Nat.le_succ n))
      rwa [← hg, ← hg, ← map_sub, quot_dvd_iff] at this
    choose b c hbc using h1
    let u : ℕ → R := fun n => g n + y * ∑ i ∈ Finset.range n, b i
    have hu : ∀ n, p ^ n ∣ u n - u (n + 1) := fun n =>
      ⟨c n, by simp only [u, Finset.sum_range_succ]; linear_combination hbc n⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) u fun {m n} hmn => by
      rw [smodEq_iff]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := dvd_add ih ((pow_dvd_pow p hmn).trans (hu n))
        rwa [sub_add_sub_cancel] at this
    refine ⟨Ideal.Quotient.mk _ L, fun n => ?_⟩
    obtain ⟨w, hw⟩ := (smodEq_iff p n _ _).1 (hL n)
    rw [smodEq_iff, ← hg, ← map_sub, quot_dvd_iff]
    exact ⟨-∑ i ∈ Finset.range n, b i, w, by simp only [u] at hw; linear_combination hw⟩

end general

theorem xi_sat : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ (l : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ IsAdicComplete (Ideal.span {(l : Per.Ainf l ⧸ Ideal.span {xi e ^ n})}) (Per.Ainf l ⧸ Ideal.span {xi e ^ n}) := by
  intro l _ e he n
  have := (GlobalTheory.T.usage l).1
  have hk := GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he
  have h1 : ∀ a : Per.Ainf l, xi e ∣ (l : Per.Ainf l) * a → xi e ∣ a := fun a ha => by
    rw [← hk] at ha ⊢
    rw [map_mul, map_natCast, mul_eq_zero] at ha
    refine ha.resolve_left fun h0 => GlobalTheory.RingBasics.p_ne_zero (p := l) ?_
    simpa using congrArg Subtype.val h0
  have h2 := sat_pow _ _ h1 n
  refine ⟨h2, ?_⟩
  have : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  have := complete_quot (l : Per.Ainf l) (xi e ^ n) h2
  rwa [map_natCast] at this

end GlobalTheory.MemLoc.XiSat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogEx

theorem mul_pred_lt_pow (l v : ℕ) (hl : 1 ≤ l) : v * (l - 1) + 1 ≤ l ^ v := by
  obtain ⟨d, rfl⟩ : ∃ d, l = d + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    nlinarith [Nat.zero_le (v * d * d)]

theorem exists_term {R : Type} [CommRing R] (l : ℕ) (hl : l.Prime)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) (k : ℕ) :
    ∃ c : R, ((k + 1 : ℕ) : R) * c = m ^ k ∧ (l : R) ^ (k / (l - 1) / l) ∣ c ∧
      (k ≠ 0 → c ∈ (Ideal.span {(l : R)}).radical) := by
  obtain ⟨v, a, ha, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
  obtain ⟨b, hb⟩ := (hu a ha).exists_right_inv
  have hl2 := hl.two_le
  have ha0 : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; exact ha (dvd_zero _))
  have hv : v ≤ k / (l - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 := mul_pred_lt_pow l v hl.one_le
    have h2 : l ^ v ≤ l ^ v * a := Nat.le_mul_of_pos_right _ ha0
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hv
  have hqr := Nat.div_add_mod k (l - 1)
  set q := k / (l - 1) with hq
  set r := k % (l - 1) with hr
  have hwr : w ∈ (Ideal.span {(l : R)}).radical := ⟨l, Ideal.mem_span_singleton.2 hwl⟩
  have hmr : m ∈ (Ideal.span {(l : R)}).radical := ⟨l - 1, Ideal.mem_span_singleton.2 ⟨w, hw.symm⟩⟩
  refine ⟨b * (l : R) ^ d * m ^ r * w ^ q, ?_, ?_, fun hk0 => ?_⟩
  · have e : m ^ k = ((l : R) * w) ^ q * m ^ r := by
      rw [hw, ← pow_mul, ← pow_add, hqr]
    have e2 : ((k + 1 : ℕ) : R) = (l : R) ^ v * a := by
      rw [show k + 1 = l ^ v * a from hk]; push_cast; rfl
    rw [e, e2, mul_pow]
    have e3 : (l : R) ^ q = (l : R) ^ v * (l : R) ^ d := by rw [hd, pow_add]
    rw [e3]
    linear_combination ((l : R) ^ v * (l : R) ^ d * m ^ r * w ^ q) * hb
  · refine Dvd.dvd.mul_left ?_ _
    refine (pow_dvd_pow_of_dvd hwl _).trans ?_
    rw [← pow_mul]
    exact pow_dvd_pow _ (Nat.mul_div_le q l)
  · rcases Nat.eq_zero_or_pos q with h | h
    · have : 0 < r := by
        rw [h] at hqr
        omega
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hmr _ this))
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hwr _ h)

theorem exists_sum {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A]
    (c : ℕ → A) (N : ℕ → ℕ) (hN : Monotone N) (hc : ∀ r k, N r ≤ k → p ^ r ∣ c k) :
    ∃ u : A, ∀ r n, N r ≤ n → p ^ r ∣ u - ∑ k ∈ Finset.range n, c k := by
  have key : ∀ r n, N r ≤ n →
      p ^ r ∣ ∑ k ∈ Finset.range n, c k - ∑ k ∈ Finset.range (N r), c k := by
    intro r n h
    rw [← Finset.sum_Ico_eq_sub _ h]
    exact Finset.dvd_sum fun k hk => hc r k (Finset.mem_Ico.1 hk).1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {p}) (M := A) inferInstance
    (f := fun r => ∑ k ∈ Finset.range (N r), c k) (fun {a b} hab => by
      rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact key a _ (hN hab))
  refine ⟨L, fun r n h => ?_⟩
  have h1 := hL r
  rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h1
  have := dvd_sub h1 (key r n h)
  rwa [sub_sub_sub_cancel_right] at this

theorem exists_unit {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : l.Prime)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A)
    (hu : ∀ a : ℕ, ¬ l ∣ a → IsUnit (a : R)) (m w : R) (hw : (l : R) * w = m ^ (l - 1))
    (hwl : (l : R) ∣ w ^ l) :
    ∃ (c : ℕ → R) (u : A), (∀ k, ((k + 1 : ℕ) : R) * c k = m ^ k) ∧ IsUnit u ∧
      ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N,
        (l : A) ^ r ∣ u - f (∑ k ∈ Finset.range n, (-1) ^ k * c k) := by
  choose c h1 h2 h3 using exists_term l hl hu m w hw hwl
  have hl2 := hl.two_le
  obtain ⟨u, hs⟩ := exists_sum (l : A) (fun k => f ((-1) ^ k * c k)) (fun r => r * l * (l - 1))
    (fun a b hab => Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hab)) (fun r k hk => by
      have hr : r ≤ k / (l - 1) / l := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by omega)]
        exact hk
      have := map_dvd f (((pow_dvd_pow (l : R) hr).trans (h2 k)).mul_left ((-1) ^ k))
      rwa [map_pow, map_natCast] at this)
  refine ⟨c, u, h1, ?_, fun r => ⟨_, fun n hn => by rw [map_sum]; exact hs r n hn⟩⟩
  have hc0 : c 0 = 1 := by simpa using h1 0
  have hrad : u - 1 ∈ (Ideal.span {(l : A)}).radical := by
    have h := hs 1 (1 * l * (l - 1) + 1) (Nat.le_succ _)
    rw [Finset.sum_range_succ', pow_one, hc0, pow_zero, mul_one, map_one] at h
    have h' := Ideal.le_radical (Ideal.mem_span_singleton.2 h)
    have h'' : ∑ k ∈ Finset.range (1 * l * (l - 1)), f ((-1) ^ (k + 1) * c (k + 1)) ∈
        (Ideal.span {(l : A)}).radical := by
      refine Ideal.sum_mem _ fun k _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      obtain ⟨n, hn⟩ := h3 (k + 1) (Nat.succ_ne_zero k)
      refine ⟨n, Ideal.mem_span_singleton.2 ?_⟩
      have := map_dvd f (Ideal.mem_span_singleton.1 hn)
      rwa [map_pow, map_natCast] at this
    have := add_mem h' h''
    convert this using 1
    ring
  have hj : u - 1 ∈ Ideal.jacobson (⊥ : Ideal A) := by
    have h := Ideal.radical_le_jacobson hrad
    have h' := Ideal.jacobson_mono (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : A)})) h
    rwa [Ideal.jacobson_idem] at h'
  exact Ideal.isUnit_of_sub_one_mem_jacobson_bot u hj

theorem isUnit_nat_acris0 (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : ¬ l ∣ a) :
    IsUnit (a : Per.Acris0 l) := by
  have h : IsUnit (a : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ha
  have := h.map ((algebraMap (Per.Ainf l) (Per.Acris0 l)).comp (Per.zA l))
  rwa [map_natCast] at this

theorem algebraMap_acris (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem factorial_mul_sum {P : Type} [CommRing P] (m : P) (c : ℕ → P)
    (h : ∀ k, ((k + 1 : ℕ) : P) * c k = m ^ k) (n : ℕ) :
    ((n.factorial : ℕ) : P) * (m * ∑ k ∈ Finset.range n, (-1) ^ k * c k) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : P) * m ^ (k + 1) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hd : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
  have e : ((n.factorial : ℕ) : P) = ((n.factorial / (k + 1) : ℕ) : P) * ((k + 1 : ℕ) : P) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
  rw [pow_succ m, ← h k]
  linear_combination (m * (-1) ^ k * c k) * e

end GlobalTheory.MemLoc.LogEx

namespace GlobalTheory.MemLoc
open LogEx

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_isLogA : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ (t u : Per.Acris l), IsLogA e t ∧ IsUnit u ∧
      t = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * u := by
  intro l _ e he
  obtain ⟨w, hw, hwl⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he
  obtain ⟨c, u, h1, hu, h2⟩ := exists_unit (algebraMap (Per.Acris0 l) (Per.Acris l)) l Fact.out
    (acris_basic l).1 (isUnit_nat_acris0 l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) w
    (Subtype.ext (by simpa using hw)) hwl
  refine ⟨_, u, fun r => ?_, hu, rfl⟩
  obtain ⟨N, hN⟩ := h2 r
  refine ⟨N, fun n hn => ⟨algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) *
    ∑ k ∈ Finset.range n, (-1) ^ k * c k, ?_, ?_⟩⟩
  · have := congrArg (Per.Acris0 l).val
      (factorial_mul_sum (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) c h1 n)

    rw [map_mul, map_natCast, map_sum] at this
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_neg, map_one, AlgHom.commutes]
  · obtain ⟨z, hz⟩ := hN n hn
    refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * z, ?_⟩
    rw [map_mul, ← algebraMap_acris, ← mul_sub, hz]
    ring

end GlobalTheory.MemLoc
end

section

noncomputable section

namespace GlobalTheory.PtSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem map_MjSig_eq (D : D7) (i : D.nd.Loc) (hInt : Rows.IsotInternal D.what₂) (h42 : SumRepresentations.At.Conclusion42 D.nd D.naut i)
    (hUp : ParUpRec D.nd D.naut i) (hDown : DownMemRec D.nd D.naut i) (hNZ : TypeNZRec D.nd D.naut i) :
    ∀ x ∈ ZgoodN D.nd D.naut i, ∀ Sig, HasParamX D.nd D.naut i x Sig →
      (MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = eigC D.nd D.naut i x := by
  intro x hx Sig hS
  refine Submodule.eq_of_le_of_finrank_le (hUp x hx Sig hS) ?_
  have hinj := SumRepresentations.thetaT_injective D.nd D.naut i hInt h42
  have h1 : Module.finrank ℂ ↥((MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i))) =
      Module.finrank ℂ ↥(MjSig D.nd D.naut i Sig) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (MjSig D.nd D.naut i Sig))).symm
  have hfi : Function.Injective ((D.what₂.thetaP (D.nd.mu i) (D.nd.j i)).domRestrict (eigC D.nd D.naut i x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    exact Subtype.ext (hNZ x hx F.1 F.2 hF)
  have h2 : Module.finrank ℂ ↥(eigC D.nd D.naut i x) =
      Module.finrank ℂ ↥((eigC D.nd D.naut i x).map (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))) := by
    rw [← LinearMap.range_domRestrict]
    exact (LinearMap.finrank_range_of_inj hfi).symm
  rw [h1, h2]
  exact Submodule.finrank_mono (hDown x hx Sig hS)

end GlobalTheory.PtSt

end
end

section

open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

theorem zOf_character {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) :
    GlobalTheory.GLq.zOf τ.character = Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ := by
  unfold GlobalTheory.GLq.zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  rw [FDRep.char_one]
  rfl

theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (GlobalTheory.GLq.zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  classical
  unfold GlobalTheory.GLq.zOf
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem character_eq_zero_of_finrank {G : Type} [Group G] (τ : FDRep ℂ G)
    (h : Module.finrank ℂ τ.V = 0) (x : G) : τ.character x = 0 := by
  have : Subsingleton τ.V := Module.finrank_zero_iff.mp h
  unfold FDRep.character
  rw [Subsingleton.elim (τ.ρ x) 0]
  exact map_zero _

theorem character_eq_of_zOf_eq {G : Type} [Group G] [Fintype G] (σ τ : FDRep ℂ G)
    (h : GlobalTheory.GLq.zOf σ.character = GlobalTheory.GLq.zOf τ.character) : σ.character = τ.character := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy : ∀ y : G, σ.character 1 * σ.character y = τ.character 1 * τ.character y := by
    intro y
    have h1 := zOf_coeff σ.character y⁻¹
    have h2 := zOf_coeff τ.character y⁻¹
    rw [h, h2, inv_inv] at h1
    field_simp at h1
    first | exact h1.symm | linear_combination (-1 : ℂ) * h1
  have h1 := hy 1
  rw [FDRep.char_one, FDRep.char_one] at h1
  have h2 : Module.finrank ℂ σ.V * Module.finrank ℂ σ.V = Module.finrank ℂ τ.V * Module.finrank ℂ τ.V := by
    exact_mod_cast h1
  have h3 : Module.finrank ℂ σ.V = Module.finrank ℂ τ.V := Nat.mul_self_inj.mp h2
  funext y
  by_cases h0 : Module.finrank ℂ τ.V = 0
  · rw [character_eq_zero_of_finrank τ h0, character_eq_zero_of_finrank σ (h3.trans h0)]
  · have h4 := hy y
    rw [FDRep.char_one, FDRep.char_one, h3] at h4
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr h0) h4

theorem finsum_zOf_eq_finsum_zIdem {G : Type} [Group G] [Fintype G] (Q : (G → ℂ) → Prop) :
    ∑ᶠ χ ∈ {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}, GlobalTheory.GLq.zOf χ =
      ∑ᶠ (z : MonoidAlgebra ℂ G) (_ : ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧
        Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character), z := by
  have hinj : Set.InjOn (GlobalTheory.GLq.zOf (G := G)) {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ} := by
    rintro a ⟨⟨V, -, hV⟩, -⟩ b ⟨⟨U, -, hU⟩, -⟩ hab
    obtain rfl : V.character = a := funext hV
    obtain rfl : U.character = b := funext hU
    exact character_eq_of_zOf_eq V U hab
  rw [← finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) hinj]
  refine finsum_congr fun z => ?_
  have hiff : (z ∈ GlobalTheory.GLq.zOf '' {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}) =
      ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character := by
    apply propext
    constructor
    · rintro ⟨a, ⟨⟨V, hs, hV⟩, hQ⟩, rfl⟩
      obtain rfl : V.character = a := funext hV
      exact ⟨V, hs, (zOf_character V).symm, hQ⟩
    · rintro ⟨V, hs, rfl, hQ⟩
      exact ⟨V.character, ⟨⟨V, hs, fun _ => rfl⟩, hQ⟩, zOf_character V⟩
  rw [hiff]

end GlobalTheory.SerCmp
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

def upSec {S : Scheme.{0}} (G : Over S) {L : LB G.left} {k : ℕ} (σ : H0 L k) :
    LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S))) :=
  GlobalTheory.VVRank.pullTo σ (snd (Over.mk (𝟙 S)) G).left (fun _ => Category.comp_id _)

end GlobalTheory.TorRef
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.product_formula_haarModulus_cmField_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ u : E, u ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)).Finite ∧ modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) = 1 := by
  first | exact @GlobalTheory.GaugeEx.prod_modu_inclR | exact GlobalTheory.GaugeEx.prod_modu_inclR | (intros; apply GlobalTheory.GaugeEx.prod_modu_inclR <;> assumption)
end
