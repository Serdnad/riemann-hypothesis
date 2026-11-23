module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GFaceSnGCastSucc
public import Development.AutomorphicArithmetic.EtaleIdempotents.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

section Factor

variable {R : Type} [CommRing R] {e : R}

private abbrev factorMk (e : R) : R →+* R ⧸ Ideal.span {1 - e} :=
  Ideal.Quotient.mk _

private theorem mk_eq_iff (he : IsIdempotentElem e) (a b : R) :
    factorMk e a = factorMk e b ↔ e * a = e * b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    linear_combination e * hc - c * he.eq
  · intro h
    exact ⟨a - b, by linear_combination h⟩

private theorem mk_self (he : IsIdempotentElem e) : factorMk e e = 1 := by
  rw [← map_one (factorMk e), mk_eq_iff he, mul_one, he.eq]

private theorem dvd_of_mk_dvd (he : IsIdempotentElem e) {a b : R} (h : factorMk e a ∣ factorMk e b) : a ∣ e * b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, mk_eq_iff he] at hc
  exact ⟨e * c, by linear_combination hc⟩

private theorem mem_pow_iff {S : Type} [CommRing S] (a x : S) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule S S) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem perfect_quot (he : IsIdempotentElem e) {p : ℕ} (hp : 0 < p) [PerfectRing R p] :
    PerfectRing (R ⧸ Ideal.span {1 - e}) p := by
  have hep : e ^ p = e := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    exact he.pow_succ_eq k
  have hb := PerfectRing.bijective_frobenius (R := R) (p := p)
  refine ⟨⟨fun x y h => ?_, fun x => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h' : factorMk e (a ^ p) = factorMk e (b ^ p) := by simpa only [map_pow] using h
    rw [mk_eq_iff he] at h' ⊢
    apply hb.1
    show (e * a) ^ p = (e * b) ^ p
    rw [mul_pow, mul_pow, hep, h']
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb'⟩ := hb.2 a
    exact ⟨factorMk e b, by rw [← hb']; simp only [map_pow]⟩

private theorem nzd_quot (he : IsIdempotentElem e) {π : R} (h : π ∈ nonZeroDivisors R) :
    factorMk e π ∈ nonZeroDivisors (R ⧸ Ideal.span {1 - e}) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, ← map_zero (factorMk e), mk_eq_iff he, mul_zero] at hx
  rw [← map_zero (factorMk e), mk_eq_iff he, mul_zero]
  rw [mem_nonZeroDivisors_iff_right] at h
  exact h _ (by linear_combination hx)

private theorem complete_quot (he : IsIdempotentElem e) {π : R} (h : IsAdicComplete (Ideal.span {π}) R) :
    IsAdicComplete (Ideal.span {factorMk e π}) (R ⧸ Ideal.span {1 - e}) := by
  have hH := h.toIsHausdorff
  have hP := h.toIsPrecomplete
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_zero (factorMk e), mk_eq_iff he, mul_zero]
    refine hH.haus' _ fun n => ?_
    rw [SModEq.zero, mem_pow_iff]
    have := (hx n)
    rw [SModEq.zero, mem_pow_iff, ← map_pow] at this
    exact dvd_of_mk_dvd he this
  · choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    obtain ⟨L, hL⟩ := hP.prec' (fun n => e * g n) (fun {m n} hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, mem_pow_iff, ← map_pow, ← hg m, ← hg n, ← map_sub] at this
      rw [SModEq.sub_mem, mem_pow_iff]
      have h2 := dvd_of_mk_dvd he this
      rwa [mul_sub] at h2)
    refine ⟨factorMk e L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, mem_pow_iff] at this ⊢
    have h3 := map_dvd (factorMk e) this
    rw [map_pow, map_sub, map_mul, mk_self he, one_mul, hg n] at h3
    exact h3

private theorem aic_quot (I : Ideal R) (h : ∀ P : R[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x) :
    ∀ P : (R ⧸ I)[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x := by
  intro P hP hd
  have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P)
  obtain ⟨q, rfl, hdeg, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
  obtain ⟨x, hx⟩ := h q hq (hdeg ▸ hd)
  exact ⟨_, hx.map (Ideal.Quotient.mk I)⟩

private theorem val_quot (he : IsIdempotentElem e) {π : R}
    (h : ∀ f g : R, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f}) :
    ∀ f g : R ⧸ Ideal.span {1 - e}, (∃ N : ℕ, factorMk e π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R ⧸ Ideal.span {1 - e}, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f} := by
  intro f g ⟨N, hN⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨c', d', hcd⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d'
  have hE : e * (c * a + d * b) = e * π ^ N := by
    rw [← mk_eq_iff he]
    simpa only [map_add (f := _), map_mul, map_pow] using hcd
  obtain ⟨u, hu, h1, h2⟩ := h (a * e + (1 - e)) (b * e) ⟨N, Ideal.mem_span_pair.2
    ⟨c * e + π ^ N * (1 - e), d, by
      linear_combination hE + (c * a - c - π ^ N * a + π ^ N) * he.eq⟩⟩
  have hm : factorMk e (1 - e) = 0 := by rw [map_sub, map_one, mk_self he, sub_self]
  have ha : factorMk e (a * e + (1 - e)) = factorMk e a := by
    rw [map_add (f := _), map_mul, mk_self he, hm, mul_one, add_zero]
  have hb : factorMk e (b * e) = factorMk e b := by rw [map_mul, mk_self he, mul_one]
  rw [Ideal.mem_span_singleton] at h1 h2
  refine ⟨factorMk e u, ?_, ?_, ?_⟩
  · show factorMk e u * factorMk e u = factorMk e u
    rw [← map_mul, hu.eq]
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (factorMk e) h1
    rwa [hb, map_mul, ha] at this
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (factorMk e) h2
    rwa [ha, map_mul, hb, map_sub, map_one] at this

end Factor

variable {l : ℕ} [Fact l.Prime]

private def factor (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) : PAlg l where
  A := A.A ⧸ Ideal.span {1 - e}
  s := (Ideal.Quotient.mk _).comp A.s
  perf := perfect_quot he (Fact.out : l.Prime).pos
  compl := complete_quot he A.compl
  tf := nzd_quot he A.tf

private theorem factor_isTest (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) (h : A.IsTest) :
    (factor A he).IsTest :=
  ⟨aic_quot _ h.1, val_quot he h.2⟩

theorem decEx : DecEx := by
  intro l _ A ι _ e he
  refine ⟨fun i => ⟨factor A.obj (he.idem i), factor_isTest _ _ A.property⟩,
    fun i => ObjectProperty.homMk ⟨Ideal.Quotient.mk _, rfl⟩, ?_, fun i => ?_⟩
  · exact he.bijective_pi
  · exact mk_self (he.idem i)

end UpperTheory.Ru.crystallineComparison
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

section Ring

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, CommRing (T i)]
  (f : ∀ i, R →+* T i)

private theorem wit_bij (h : Function.Bijective fun (a : R) i => f i a) :
    Function.Bijective fun (x : WittVector l R) i => WittVector.map (f i) x := by
  constructor
  · intro x y e
    ext n
    refine h.1 (funext fun i => ?_)
    have := congrArg (fun w => WittVector.coeff w n) (congrFun e i)
    simpa only [WittVector.map_coeff] using this
  · intro y
    choose c hc using fun n => h.2 (fun i => (y i).coeff n)
    refine ⟨WittVector.mk l c, funext fun i => ?_⟩
    ext n
    rw [WittVector.map_coeff]
    exact congrFun (hc n) i

private theorem l_unit (S : Type) [CommRing S] (k : ℕ) :
    IsUnit ((l : WL l S) ^ k) := by
  have : IsUnit (algebraMap (WittVector l S) (WL l S) (l : WittVector l S)) :=
    IsLocalization.Away.algebraMap_isUnit (l : WittVector l S)
  rw [map_natCast] at this
  exact this.pow k

private theorem exists_num {S : Type} [CommRing S] (x : WL l S) :
    ∃ (a : WittVector l S) (k : ℕ), x * (l : WL l S) ^ k = algebraMap _ (WL l S) a := by
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (l : WittVector l S)) x
  refine ⟨a, k, ?_⟩
  simpa only [map_pow, map_natCast] using h

private theorem away_bij (h : Function.Bijective fun (a : R) i => f i a) :
    Function.Bijective fun (x : WL l R) i => awayW (f i) x := by
  have hw := wit_bij (l := l) f h
  constructor
  · have hz : ∀ x : WL l R, (∀ i, awayW (f i) x = 0) → x = 0 := by
      intro x hx
      obtain ⟨a, k, hk⟩ := exists_num x
      have h1 : ∀ i, ∃ m : ℕ, (l : WittVector l (T i)) ^ m * WittVector.map (f i) a = 0 := by
        intro i
        have : algebraMap _ (WL l (T i)) (WittVector.map (f i) a) = 0 := by
          rw [← awayW_algebraMap, ← hk, map_mul, hx i, zero_mul]
        obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (l : WittVector l (T i))) _ _).1 this
        exact ⟨m, hm⟩
      choose m hm using h1
      have h2 : (l : WittVector l R) ^ (∑ i, m i) * a = 0 := by
        refine hw.1 (funext fun i => ?_)
        have hd : m i ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        change WittVector.map (f i) _ = WittVector.map (f i) 0
        rw [map_mul, map_pow, map_natCast, map_zero, ← Nat.sub_add_cancel hd, pow_add, mul_assoc, hm i, mul_zero]
      have h3 : (l : WL l R) ^ (∑ i, m i) * (x * (l : WL l R) ^ k) = 0 := by
        rw [hk]
        have := congrArg (algebraMap _ (WL l R)) h2
        rwa [map_mul, map_pow, map_natCast, map_zero] at this
      exact ((l_unit R _).mul_right_eq_zero.1 h3 |> (l_unit R k).mul_left_eq_zero.1)
    intro x y e
    have := hz (x - y) fun i => by
      have := congrFun e i
      simp only at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.1 this
  · intro y
    choose a k hk using fun i => exists_num (y i)
    have hd : ∀ i, k i ≤ ∑ j, k j := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    obtain ⟨c, hc⟩ := hw.2 fun i => a i * (l : WittVector l (T i)) ^ (∑ j, k j - k i)
    obtain ⟨u, hu⟩ := l_unit (l := l) R (∑ j, k j) |>.exists_right_inv
    refine ⟨algebraMap _ (WL l R) c * u, funext fun i => ?_⟩
    refine (l_unit (l := l) (T i) (∑ j, k j)).mul_right_cancel ?_
    have e1 : awayW (f i) ((l : WL l R) ^ ∑ j, k j) = (l : WL l (T i)) ^ ∑ j, k j := by
      rw [map_pow, map_natCast]
    have e2 : awayW (f i) (algebraMap _ (WL l R) c * u) * (l : WL l (T i)) ^ ∑ j, k j =
        algebraMap _ (WL l (T i)) (WittVector.map (f i) c) := by
      rw [← e1, ← map_mul, mul_assoc, mul_comm u, hu, mul_one, awayW_algebraMap]
    have hci : WittVector.map (f i) c = a i * (l : WittVector l (T i)) ^ (∑ j, k j - k i) := congrFun hc i
    rw [e2, hci, map_mul, ← hk i, map_pow, map_natCast, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hd i)]

end Ring

section Acr

variable {A : PAlg l} {ι : Type} [Fintype ι] {B : ι → PAlg l} (f : ∀ i, A ⟶ B i)

private theorem crystallineAlgebra_algebraMap {C D : PAlg l} (g : C ⟶ D) (w : C.W) :
    (pdOk_hom g).acr0 (algebraMap C.W C.Acr0 w) = algebraMap D.W D.Acr0 (mapW g w) :=
  Subtype.ext (awayW_algebraMap (Hom.f g) w)

private theorem crystallineAlgebra_bijective (h : Function.Bijective fun (a : A.A) i => Hom.f (f i) a) :
    Function.Bijective fun (x : A.Acr0) i => (pdOk_hom (f i)).acr0 x := by
  classical
  have hw := wit_bij (l := l) (fun i => Hom.f (f i)) h
  have ha := away_bij (l := l) (fun i => Hom.f (f i)) h
  constructor
  · intro x y e
    exact Subtype.ext (ha.1 (funext fun i => congrArg Subtype.val (congrFun e i)))
  · have hs : ∀ i (y : WL l (B i).A), y ∈ (B i).Acr0 → ∃ z : A.Acr0, awayW (Hom.f (f i)) z.1 = y := by
      intro i y hy
      induction hy using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        refine ⟨A.dxi0 k, ?_⟩
        have := awayW_dpw (Hom.f (f i)) k (A.isUnit_natCast k.factorial_ne_zero) A.xi
        exact this.trans (congrArg (dpw k) (mapW_xi (f i)))
      | algebraMap w =>
        obtain ⟨c, hc⟩ := hw.2 (Pi.single i w)
        have hci : WittVector.map (Hom.f (f i)) c = w := by simpa using congrFun hc i
        refine ⟨algebraMap A.W A.Acr0 c, ?_⟩
        have := awayW_algebraMap (l := l) (Hom.f (f i)) c
        rw [hci] at this
        exact this
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a * b, map_mul _ _ _⟩
    intro y
    choose z hz using fun i => hs i (y i).1 (y i).2
    choose E hE using fun i => hw.2 (Pi.single i (1 : WittVector l (B i).A))
    refine ⟨∑ i, algebraMap A.W A.Acr0 (E i) * z i, funext fun j => ?_⟩
    simp only
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single j]
    · have e0 : mapW (f j) (E j) = 1 := (congrFun (hE j) j).trans (Pi.single_eq_same _ _)
      have e1 : (pdOk_hom (f j)).acr0 (algebraMap A.W A.Acr0 (E j)) = 1 := by
        rw [crystallineAlgebra_algebraMap, e0]; exact map_one _
      rw [map_mul, e1, one_mul]
      exact Subtype.ext (hz j)
    · intro i _ hij
      have e0 : mapW (f j) (E i) = 0 := (congrFun (hE i) j).trans (Pi.single_eq_of_ne hij.symm _)
      have e1 : (pdOk_hom (f j)).acr0 (algebraMap A.W A.Acr0 (E i)) = 0 := by
        rw [crystallineAlgebra_algebraMap, e0]; exact map_zero _
      rw [map_mul, e1, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

private theorem acr_bij (n : ℕ) (h : Function.Bijective fun (a : A.A) i => Hom.f (f i) a) :
    Function.Bijective fun (x : A.Acr n) i => mapAcr (f i) n x := by
  have h0 := crystallineAlgebra_bijective f h
  constructor
  · have hz : ∀ x : A.Acr n, (∀ i, mapAcr (f i) n x = 0) → x = 0 := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h1 : ∀ i, ∃ c : (B i).Acr0, c * (l : (B i).Acr0) ^ n = (pdOk_hom (f i)).acr0 y := fun i =>
        Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 (hx i))
      choose c hc using h1
      obtain ⟨d, hd⟩ := h0.2 c
      have hy : y = d * (l : A.Acr0) ^ n := h0.1 (funext fun i => by
        have hdi : (pdOk_hom (f i)).acr0 d = c i := congrFun hd i
        simp only
        rw [map_mul, map_pow, map_natCast, hdi, hc i])
      rw [hy]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    intro x y e
    have := hz (x - y) fun i => by
      have := congrFun e i
      simp only at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.1 this
  · intro y
    choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    obtain ⟨d, hd⟩ := h0.2 z
    refine ⟨A.mkAcr n d, funext fun i => ?_⟩
    have hdi : (pdOk_hom (f i)).acr0 d = z i := congrFun hd i
    have : mapAcr (f i) n (A.mkAcr n d) = (B i).mkAcr n ((pdOk_hom (f i)).acr0 d) := rfl
    simp only
    rw [this, hdi]
    exact hz i

end Acr

end UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.acrAdd :
    UpperTheory.Ru.crystallineComparison.AcrAdd := fun _ _ n _ S hS => UpperTheory.Ru.crystallineComparison.acr_bij (fun i => (S.f i).hom) n hS
end
end

section

theorem UpperTheory.Ru.crystallineComparison.theoryEx :
    UpperTheory.Ru.crystallineComparison.TheoryEx := by
  intro C _
  obtain ⟨z, hz₁, hz₂⟩ := UpperTheory.exists_cohomology_zero_equiv_sections_natural C
  refine ⟨{ H := UpperTheory.Ru.crystallineComparison.Th.TH
            ab := fun _ _ _ => inferInstance
            pull := fun u F j => UpperTheory.Ru.crystallineComparison.Th.tPull u F j
            map := fun P _ _ α j => UpperTheory.Ru.crystallineComparison.Th.tMap P α j
            pull_map := fun u _ _ α j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tMap u α j x
            δ := UpperTheory.Ru.crystallineComparison.Th.tδ
            pull_δ := fun u S h j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tδ u S h j x
            ex₃ := UpperTheory.Ru.crystallineComparison.Th.ex₃
            ex₁ := UpperTheory.Ru.crystallineComparison.Th.ex₁
            zero := z
            zero_pull := hz₁
            zero_map := hz₂
            inj := UpperTheory.Ru.crystallineComparison.Th.vanish }, fun R _ F => ?_⟩
  obtain ⟨F', c, e, h₁, h₂⟩ := UpperTheory.exists_coefficient_equiv_cohomology_of_elements C R F
  exact ⟨F', c, e, h₁, h₂⟩
end
