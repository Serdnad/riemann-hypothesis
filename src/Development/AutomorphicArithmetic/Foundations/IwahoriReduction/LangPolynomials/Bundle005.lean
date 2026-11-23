module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle003
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle002
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle001
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.IntShift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.ToBasisLogarithm

variable {l : ℕ} [Fact l.Prime]

private theorem norm_alg_le (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact z.2

private theorem norm_nat_le (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 := by
  simpa using norm_alg_le (l := l) (a : ℤ_[l])

private theorem cg_sum {ι : Type} [Fintype ι] (n : ℕ) (f g : ι → Qbar l) (h : ∀ i, Cg n (f i) (g i)) :
    Cg n (∑ i, f i) (∑ i, g i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => h i

private theorem cg_mul {n : ℕ} {a b y : Qbar l} (h : Cg n a b) (hy : ‖y‖ ≤ 1) : Cg n (a * y) (b * y) := by
  unfold Cg at *
  rw [← sub_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans h

private theorem cg_trans {n : ℕ} {a b c : Qbar l} (h : Cg n a b) (h' : Cg n b c) : Cg n a c := by
  unfold Cg at *
  rw [show a - c = (a - b) + (b - c) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cg_nat {n x y : ℕ} (h : (x : ZMod (l ^ n)) = y) : Cg n (x : Qbar l) y := by
  obtain ⟨e, he⟩ := (Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm)
  have he' : (x : Qbar l) - y = (l : Qbar l) ^ n * (e : Qbar l) := by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) he
  have hn : ‖(e : Qbar l)‖ ≤ 1 := by simpa using norm_alg_le (l := l) (e : ℤ_[l])
  unfold Cg
  rw [he', norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hn

private theorem coords {c : Coef l} (β : Bas c) (hβ : ∀ i, ‖β.val i‖ ≤ 1) (n : ℕ) (o : Qbar l) (ho : o ∈ c.O) :
    ∃ a : Fin β.d → ℕ, Cg n o (∑ i, β.val i * (a i : Qbar l)) := by
  refine ⟨fun i => (β.e.repr ⟨o, ho⟩ i).appr n, ?_⟩
  have h1 : o = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i) := by
    have := congrArg (fun x : c.O => (x : PadicAlgCl l)) (β.e.sum_repr ⟨o, ho⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]; rfl
  refine cg_trans (b := ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i)) ?_ (cg_sum n _ _ fun i => ?_)
  · unfold Cg; rw [← h1, sub_self, norm_zero]; exact norm_nonneg _
  · rw [mul_comm (β.val i), mul_comm (β.val i)]
    refine cg_mul ?_ (hβ i)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n (β.e.repr ⟨o, ho⟩ i))
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
    rw [map_mul, map_pow, map_natCast, map_sub, map_natCast] at this
    unfold Cg
    rw [← this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_alg_le e)

private theorem cg_swap {ι : Type} [Fintype ι] {d n : ℕ} (b : Fin d → Qbar l) (o y : ι → Qbar l) (a : ι → Fin d → ℕ)
    (h : ∀ k, Cg n (o k) (∑ i, b i * (a k i : Qbar l))) (hy : ∀ k, ‖y k‖ ≤ 1) :
    Cg n (∑ k, o k * y k) (∑ i, b i * ∑ k, (a k i : Qbar l) * y k) := by
  have e : ∑ i, b i * ∑ k, (a k i : Qbar l) * y k = ∑ k, (∑ i, b i * (a k i : Qbar l)) * y k := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e]
  exact cg_sum n _ _ fun k => cg_mul (h k) (hy k)

private theorem logd {Ω : Type} [Field Ω] {ι : Type} (S : Finset ι) (P : ι → Polynomial Ω) (a : ι → ℕ) (z : Ω)
    (hP : ∀ k, (P k).eval z ≠ 0) :
    z * (Polynomial.derivative (∏ k ∈ S, P k ^ a k)).eval z / (∏ k ∈ S, P k ^ a k).eval z =
      ∑ k ∈ S, (a k : Ω) * (z * (Polynomial.derivative (P k)).eval z / (P k).eval z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h0 : (∏ k ∈ S, P k ^ a k).eval z ≠ 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [Polynomial.eval_pow]; exact pow_ne_zero _ (hP k)
    have hk0 := hP k
    rw [Finset.prod_insert hk, Finset.sum_insert hk, ← ih, Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rcases a k with _ | r
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      field_simp

private theorem pv_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) {z : Ω} (hz : z ∈ A) :
    (P.map (R0 A).subtype).eval z ∈ A := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.eval_add]; exact A.add_mem _ _ hp hq
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    exact A.mul_mem _ _ a.2.1 (A.toSubring.pow_mem hz n)

private theorem pv_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (z : Ω)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    (P.map (R0 A).subtype).eval (s z) = s ((P.map (R0 A).subtype).eval z) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.eval_add, Polynomial.eval_add, map_add (f := _), hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial, map_mul, map_pow]
    congr 1
    exact (a.2.2 s hs).symm

private theorem root_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {z : Ω} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with h | h
  · exact h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have e : z = (z⁻¹) ^ k := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_right (by rw [← hz, pow_succ])
    rw [e]; exact A.toSubring.pow_mem h k

private theorem ex_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}
    (h : ∀ u : ℤ_[l]ˣ, ∃ s ∈ Ine (F := ℚ) A, cycZ ℚ Ω l s = u) {m : ℕ} (hm : 1 ≤ m) {z : Ω} (hz : z ^ l ^ m = 1)
    (b : (ZMod (l ^ m))ˣ) : ∃ s ∈ Ine (F := ℚ) A, s z = z ^ (b : ZMod (l ^ m)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hc : ((b : ZMod (l ^ m)).val).Coprime l :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self l (by omega)) (ZMod.val_coe_unit_coprime b)
  have hu : IsUnit (((b : ZMod (l ^ m)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 hc.symm
  obtain ⟨s, hs, hs'⟩ := h hu.unit
  refine ⟨s, hs, ?_⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) z hz
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)) = hu.unit := hs'
  rw [h2, IsUnit.unit_spec, map_natCast, ZMod.natCast_zmod_val] at h1
  exact h1

end UpperTheory.Kd.C7.ToBasisLogarithm

open UpperTheory.Kd.C7.ToBasisLogarithm in
theorem UpperTheory.Kd.C7.pToBasis :
    UpperTheory.Kd.C7.SToBasis := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ j hj Z m n ι _ P o hm hP ho hK
  classical
  obtain ⟨hprim, hnm, hu, ho1, hpres⟩ := hK
  have hβ := ((pBasEx l c).2 β).1
  have hfr := (pFrobEx l hl Ω A hA).2.2
  choose a ha using fun k => coords β hβ n (o k) (ho k)
  have hQ : ∀ k, ∃ Q : Polynomial (R0 A), Q.map (R0 A).subtype = P k := fun k =>
    ⟨(P k).toSubring (R0 A) (fun x hx => hP k x hx), Polynomial.map_toSubring _ _ _⟩
  choose Q hQ using hQ
  have hmap : ∀ i, (∏ k, Q k ^ a k i).map (R0 A).subtype = ∏ k, P k ^ a k i := fun i => by
    simp only [Polynomial.map_prod, Polynomial.map_pow, hQ]
  have hpv : ∀ i, pv (∏ k, Q k ^ a k i) (ζ m) = ∏ k, (P k).eval (ζ m) ^ a k i := fun i => by
    rw [pv, Polynomial.eval₂_eq_eval_map, hmap, Polynomial.eval_prod]
    simp only [Polynomial.eval_pow]
  refine ⟨fun i => ∏ k, Q k ^ a k i, ⟨hprim, hnm, fun i => ?_, hβ, fun s hs hc hz => ?_⟩, fun b => ?_⟩
  · dsimp only
    rw [hpv]
    refine ⟨A.toSubring.prod_mem fun k _ => A.toSubring.pow_mem (hu k).1 _,
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hu k).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact A.toSubring.prod_mem fun k _ => by rw [← inv_pow]; exact A.toSubring.pow_mem (hu k).2.2 _
  · obtain ⟨κ, hκ, hcg⟩ := hpres s hs hc hz
    have hKA := (pKumAlg l hl Ω A hA ζ hζ m n hnm s ⟨hs, hc⟩).1
    refine ⟨fun i => ∑ k, (a k i : ZMod (l ^ n)) * κ k, fun i => ?_, ?_⟩
    · dsimp only
      rw [hpv]
      generalize (Finset.univ : Finset ι) = S
      induction S using Finset.induction_on with
      | empty => simpa using kumVal_one (l := l) n (ζ n) s
      | insert k S hk ih =>
        rw [Finset.prod_insert hk, Finset.sum_insert hk]
        exact (hKA _ _ _ _ ((hKA _ _ _ _ (hκ k) (hκ k)).2.2 (a k i)) ih).1
    · refine cg_trans hcg (cg_trans (cg_swap β.val o _ a ha fun k => norm_nat_le _) (cg_sum n _ _ fun i => ?_))
      rw [mul_comm (β.val i), mul_comm (β.val i)]
      refine cg_mul ?_ (hβ i)
      haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      have := cg_nat (l := l) (n := n) (x := ∑ k, a k i * (κ k).val) (y := (∑ k, (a k i : ZMod (l ^ n)) * κ k).val)
        (by simp)
      simpa using this
  · obtain ⟨s, hs, hsz⟩ := ex_conj hfr hm (hζ m).1.pow_eq_one b
    have hzA : ζ m ∈ A := root_mem A (pow_pos (Fact.out : l.Prime).pos m) (hζ m).1.pow_eq_one
    have hz : ζ m ^ (b : ZMod (l ^ m)).val ∈ A := A.toSubring.pow_mem hzA _
    have hev : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) = s ((P k).eval (ζ m)) := fun k => by
      rw [← hsz, ← hQ, pv_conj _ _ hs]
    have hne : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) ≠ 0 := fun k => by
      rw [hev]; exact (map_ne_zero s).2 (hu k).2.1
    unfold htv

    simp only [hmap, logd _ P _ _ hne, map_sum, map_mul j, map_natCast]
    refine cg_swap β.val o _ a ha fun k => hj _ ?_
    rw [div_eq_mul_inv]
    refine A.mul_mem _ _ (A.mul_mem _ _ hz ?_) ?_
    · rw [← hQ, Polynomial.derivative_map]; exact pv_mem _ hz
    · rw [hev, ← map_inv₀, apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs)]; exact (hu k).2.2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

noncomputable section
namespace UpperTheory.Kd.C7.C2

private theorem map_sb {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (b : ℕ) (h : PowerSeries R) :
    PowerSeries.map f (sb b h) = sb b (PowerSeries.map f h) := by
  have key := PowerSeries.map_subst (hasSubst_pow (R := R) b) (h := f) h
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  have e : MvPowerSeries.map f (((1 + PowerSeries.X : PowerSeries R) ^ b) - 1) = (((1 + PowerSeries.X : PowerSeries S) ^ b) - 1) := by
    change PowerSeries.map f _ = _
    simp
  rw [e] at key
  exact key

private theorem sb_C {R : Type} [CommRing R] (b : ℕ) (x : R) (h : PowerSeries R) :
    sb b (PowerSeries.C x * h) = PowerSeries.C x * sb b h := by
  rw [map_mul]
  congr 1
  exact (sb (R := R) b).commutes x

variable {l : ℕ} [Fact l.Prime]

private theorem norm_sum_le_one {K ι : Type} [NormedField K] [IsUltrametricDist K] (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

private theorem norm_sub_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

private theorem nmul {K : Type} [NormedField K] {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

private theorem npow {K : Type} [NormedField K] {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

private theorem norm_root {K : Type} [NormedField K] {a : K} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = 1) : ‖a‖ ≤ 1 := by
  have : ‖a‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this).le

private theorem norm_chi (φ : DirichletCharacter (Qbar l) l) (x : ZMod l) : ‖φ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    refine norm_root (n := Fintype.card (ZMod l)ˣ) Fintype.card_ne_zero ?_
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  · rw [φ.map_nonunit hx, norm_zero]; exact zero_le_one

private theorem intg_lin (φ : DirichletCharacter (Qbar l) l) (k r : ℕ) (ξ : Qbar l) (hξ : IsPrimitiveRoot ξ (l ^ r)) :
    ∃ a : ℕ → Qbar l, (∀ n, ‖a n‖ ≤ 1) ∧ ∀ L, intg φ k L r ξ = ∑ n ∈ Finset.range (l ^ (3 * r)), a n * L.coeff n := by
  have h1 : ‖ξ‖ ≤ 1 := norm_root (pow_ne_zero r (Fact.out : l.Prime).ne_zero) hξ.pow_eq_one
  refine ⟨fun n => ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), ∑ i ∈ Finset.range (l ^ r),
    φ (x : ZMod l) * ((x : Qbar l) ^ k) * (ξ ^ (l ^ r - (i * x) % l ^ r) * (ξ ^ i - 1) ^ n), fun n => ?_, fun L => ?_⟩
  · refine norm_sum_le_one _ _ fun x _ => norm_sum_le_one _ _ fun i _ => ?_
    exact nmul (nmul (norm_chi φ _) (npow (IsUltrametricDist.norm_natCast_le_one _ _) _))
      (nmul (npow h1 _) (npow (norm_sub_le_one (npow h1 _) norm_one.le) _))
  · simp only [intg, mass, tval, Finset.mul_sum, Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => ?_
    ring

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (Φ : Fr l A j) {c : Coef l} (β : Bas c)

private def abelian₂ (D : Fin β.d → PowerSeries Φ.R) : PowerSeries ℂ_[l] :=
  ∑ i, PowerSeries.C (algebraMap (PadicAlgCl l) ℂ_[l] (β.val i)) * PowerSeries.map Φ.jh (D i)

private theorem Lam_coeff (D : Fin β.d → PowerSeries Φ.R) (n : ℕ) :
    (abelian₂ Φ β D).coeff n = Φ.lam β (fun i => (D i).coeff n) := by
  simp [abelian₂, Fr.lam, PowerSeries.coeff_C_mul]

private theorem Lam_sub (D E : Fin β.d → PowerSeries Φ.R) :
    abelian₂ Φ β (fun i => D i - E i) = abelian₂ Φ β D - abelian₂ Φ β E := by
  simp [abelian₂, mul_sub, Finset.sum_sub_distrib]

private theorem Lam_sb (g : ℕ) (D : Fin β.d → PowerSeries Φ.R) :
    abelian₂ Φ β (fun i => sb g (D i)) = sb g (abelian₂ Φ β D) := by

  simp only [abelian₂, map_sum, sb_C, map_sb]

private theorem val_mul (b : c.O) (k : Fin β.d) :
    ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.mat b i k) = (b : PadicAlgCl l) * β.val k := by
  have h := β.e.sum_repr (b * β.e k)
  have h2 := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
  simp only [Bas.val, Bas.mat, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, ← Algebra.smul_def]
  rfl

private theorem Lam_act (b : c.O) (D : Fin β.d → PowerSeries Φ.R) :
    abelian₂ Φ β (Φ.act (β.mat b) D) = PowerSeries.C (algebraMap (PadicAlgCl l) ℂ_[l] (b : PadicAlgCl l)) * abelian₂ Φ β D := by

  simp only [abelian₂, Fr.act, map_sum, map_mul, PowerSeries.map_C, Φ.jh_alg, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_

  rw [← mul_assoc, ← map_mul, ← map_mul, ← val_mul β b k, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, mul_assoc]

private theorem nf (x : PadicAlgCl l) : ‖algebraMap (PadicAlgCl l) ℂ_[l] x‖ = ‖x‖ := PadicComplex.norm_extends l x

private theorem Lam_le (hβ : ∀ i, ‖β.val i‖ ≤ 1) (D : Fin β.d → PowerSeries Φ.R) (n : ℕ) : ‖(abelian₂ Φ β D).coeff n‖ ≤ 1 := by
  rw [Lam_coeff, Fr.lam]
  exact norm_sum_le_one _ _ fun i _ => nmul (by rw [nf]; exact hβ i) (Φ.jh_le _)

private theorem approx (hj : ∀ x ∈ A, ‖j x‖ ≤ 1) (hβ : ∀ i, ‖β.val i‖ ≤ 1) (D : Fin β.d → PowerSeries Φ.R) (N : ℕ) :
    ∃ (H : PowerSeries (Qbar l)) (E : Fin β.d → PowerSeries Φ.R), (∀ n, ‖H.coeff n‖ ≤ 1) ∧
      abelian₂ Φ β D = PowerSeries.map (algebraMap (PadicAlgCl l) ℂ_[l]) H + PowerSeries.C ((l : ℂ_[l]) ^ N) * abelian₂ Φ β E := by
  have h : ∀ (i : Fin β.d) (n : ℕ), ∃ (y : R0 A) (e : Φ.R), (D i).coeff n = Φ.i0 y + (l : Φ.R) ^ N * e := by
    intro i n
    obtain ⟨y, hy⟩ := Φ.dense ((D i).coeff n) N
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hy
    exact ⟨y, e, by linear_combination -he⟩
  choose y e hye using h
  refine ⟨PowerSeries.mk fun n => ∑ i, β.val i * j (y i n), fun i => PowerSeries.mk (e i), fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_mk]
    exact norm_sum_le_one _ _ fun i _ => nmul (hβ i) (hj _ (y i n).2.1)
  · ext n

    rw [map_add (f := _), PowerSeries.coeff_C_mul, Lam_coeff, Lam_coeff, PowerSeries.coeff_map, PowerSeries.coeff_mk, Fr.lam, Fr.lam,
    map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hye, PowerSeries.coeff_mk, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, Φ.jh_comp_incl]
    ring

end UpperTheory.Kd.C7.C2

open UpperTheory.Kd.C7.C2 in
theorem UpperTheory.Kd.C7.pClause2 :
    UpperTheory.Kd.C7.SClause2 := by
  intro l _ _ Ω _ _ _ A _ j Φ hj c β D D' Gs v g c₂ k φ θ hg hθ hv _ hD hrel n
  have hβ := ((pBasEx l c).2 β).1
  refine ⟨n + c₂ + 1, fun r hr ξ hξ => ?_⟩
  obtain ⟨a, ha, hint⟩ := intg_lin φ k r ξ hξ
  obtain ⟨H, E, hH, hHE⟩ := approx Φ β hj hβ D' (2 * r)
  have hS := pIntShift l H hH g hg φ k r ξ (by omega) hξ
  set f := algebraMap (PadicAlgCl l) ℂ_[l] with hf
  have h1 : abelian₂ Φ β D = PowerSeries.C v * PowerSeries.map f Gs := by
    ext m
    rw [Lam_coeff, hD, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  have h2 : abelian₂ Φ β (Φ.act (β.mat ((l : c.O) ^ c₂)) D) = abelian₂ Φ β (fun i => sb g (D' i) - Φ.act (β.mat θ) D' i) :=
    congrArg _ (funext hrel)
  rw [Lam_sub, Lam_sb, Lam_act, Lam_act, h1, hHE, map_add (f := _), sb_C, ← map_sb, ← Lam_sb] at h2
  set W := abelian₂ Φ β (fun i => sb g (E i) - Φ.act (β.mat θ) E i) with hW
  have hWle : ∀ m, ‖W.coeff m‖ ≤ 1 := Lam_le Φ β hβ _
  rw [Lam_sub, Lam_act] at hW
  have hl : algebraMap (PadicAlgCl l) ℂ_[l] (((l : c.O) ^ c₂ : c.O) : PadicAlgCl l) = (l : ℂ_[l]) ^ c₂ := by
    simp
  have h3 : ∀ m, (l : ℂ_[l]) ^ c₂ * v * f (Gs.coeff m) =
      f ((sb g H).coeff m - (θ : PadicAlgCl l) * H.coeff m) + (l : ℂ_[l]) ^ (2 * r) * W.coeff m := by
    intro m
    have h4 := congrArg (PowerSeries.coeff m) h2
    rw [hW]
    simp only [map_sub, map_add (f := _), mul_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, map_mul f] at h4 ⊢
    linear_combination h4 - v * f (Gs.coeff m) * hl
  have h5 : (l : ℂ_[l]) ^ c₂ * v * f (intg φ k Gs r ξ) =
      f (intg φ k (sb g H) r ξ - φ (g : ZMod l) * (g : Qbar l) ^ k * intg φ k H r ξ) +
        (l : ℂ_[l]) ^ (2 * r) * ∑ m ∈ Finset.range (l ^ (3 * r)), f (a m) * W.coeff m := by

    rw [← hθ, hint, hint, hint, Finset.mul_sum, ← Finset.sum_sub_distrib, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h6 := h3 m
    simp only [map_sub, map_mul] at h6 ⊢
    linear_combination f (a m) * h6
  have hfl : ‖(l : ℂ_[l])‖ = ‖(l : Qbar l)‖ := by rw [← nf, map_natCast]
  have h7 : ‖(l : ℂ_[l]) ^ c₂ * v * f (intg φ k Gs r ξ)‖ ≤ ‖(l : Qbar l)‖ ^ (2 * r) := by
    rw [h5]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [hf, nf, ← norm_pow]; exact hS
    · rw [norm_mul, norm_pow, hfl]
      refine mul_le_of_le_one_right (by positivity) (norm_sum_le_one _ _ fun m _ => nmul ?_ (hWle m))
      rw [hf, nf]; exact ha m
  rw [norm_mul, norm_mul, norm_pow, hv, hfl, mul_one, hf, nf] at h7
  have hpos : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hle : ‖(l : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  rw [Cg, sub_zero, norm_pow]
  refine le_of_mul_le_mul_left (h7.trans ?_) (pow_pos hpos c₂)
  rw [← pow_add]
  exact pow_le_pow_of_le_one hpos.le hle (by omega)
end
end
