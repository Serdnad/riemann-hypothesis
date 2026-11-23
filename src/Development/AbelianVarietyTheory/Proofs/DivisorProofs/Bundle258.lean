module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Polynomial.Basis
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

open Polynomial

variable {k L : Type} [Field k] [Field L] [Algebra k L]

theorem place_aeval_le_one (x : L) (u : Place k L) (hx : u.1 x ≤ 1) (p : k[X]) :
    u.1 (aeval x p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  refine mul_le_one' ?_ (pow_le_one' hx _)
  by_cases hc : p.coeff i = 0
  · simp [hc]
  · rw [u.2.2 _ hc]

theorem place_aeval_eq_one (x : L) (u : Place k L) (hx : u.1 x < 1) (q : k[X]) (hq : q.coeff 0 ≠ 0) :
    u.1 (aeval x q) = 1 := by
  have h1 : u.1 (algebraMap k L (q.coeff 0)) = 1 := u.2.2 _ hq
  have h2 : u.1 (x * aeval x q.divX) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hx (place_aeval_le_one x u hx.le _)
  conv_lhs => rw [← X_mul_divX_add q]
  rw [map_add (f := _), map_mul, aeval_X, aeval_C, Valuation.map_add_eq_of_lt_right u.1 (by rw [h1]; exact h2), h1]

theorem place_aeval_eq_pow (x : L) (u : Place k L) (hx : u.1 x < 1) (p : k[X]) (hp : p ≠ 0) :
    u.1 (aeval x p) = u.1 x ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h; apply hq; simpa [X_dvd_iff] using h
  conv_lhs => rw [hpq]
  simp [map_mul, map_pow, place_aeval_eq_one x u hx q hq0]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

theorem exists_unique_place_ord_eq_one (k L : Type) [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x) (htop : k⟮x⟯ = ⊤) :
    ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  have hmem : ∀ y : L, ∃ r s : k[X], y = aeval x r / aeval x s := fun y =>
    (IntermediateField.mem_adjoin_simple_iff (F := k) (α := x) y).1 (by rw [htop]; trivial)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h => hx ⟨p, hp, h⟩
  have hval : ∀ u : Place k L, u.1 x < 1 → u.1 x = WithZero.exp (-1 : ℤ) := by
    intro u hu
    have hx0 : u.1 x ≠ 0 := by
      rw [Valuation.ne_zero_iff]; intro h; apply hne X X_ne_zero; simpa using h
    set b := WithZero.log (u.1 x) with hb
    have hub : u.1 x = WithZero.exp b := (WithZero.exp_log hx0).symm
    have hb0 : b < 0 := by
      have : WithZero.exp b < WithZero.exp (0 : ℤ) := by rw [← hub, WithZero.exp_zero]; exact hu
      exact WithZero.exp_lt_exp.1 this
    obtain ⟨y, hy⟩ := u.2.1 (WithZero.exp (-1 : ℤ))
    obtain ⟨r, s, rfl⟩ := hmem y
    have hr : r ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    have hs : s ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    rw [map_div₀, place_aeval_eq_pow x u hu r hr, place_aeval_eq_pow x u hu s hs, hub,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_inj] at hy
    have hmul : b * ((r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0) = -1 := by
      rw [← hy]; simp only [nsmul_eq_mul]; ring
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hmul with h | h
    · omega
    · rw [hub, h]
  have hpol : ∀ u : Place k L, u.1 x < 1 → ∀ p : k[X], p ≠ 0 →
      u.1 (aeval x p) = WithZero.exp (-1 : ℤ) ^ p.rootMultiplicity 0 := fun u hu p hp => by
    rw [place_aeval_eq_pow x u hu p hp, hval u hu]
  let e : RatFunc k ≃ₐ[k] L := ((RatFunc.algEquivOfTranscendental x hx).trans
    (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv
  have heX : e RatFunc.X = x := by simp [e]
  have heXs : e.symm x = RatFunc.X := by rw [← heX, AlgEquiv.symm_apply_apply]
  let V := (Polynomial.idealX k).valuation (RatFunc k)
  let v0 : Valuation L (WithZero (Multiplicative ℤ)) := V.comap (e.symm : L →+* RatFunc k)
  have hv0 : ∀ y, v0 y = V (e.symm y) := fun y => rfl
  have hVX : V RatFunc.X = WithZero.exp (-1 : ℤ) := by
    rw [← RatFunc.algebraMap_X, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ X_ne_zero (Polynomial.idealX_span k)
  let v : Place k L := ⟨v0, fun γ => by
      obtain ⟨r, hr⟩ := RatFunc.valuation_surjective (K := k) γ
      exact ⟨e r, by rw [hv0, AlgEquiv.symm_apply_apply]; exact hr⟩,
    fun c hc => by
      rw [hv0, AlgEquiv.commutes, IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      intro hmem'
      rw [Polynomial.idealX_span, Ideal.mem_span_singleton, X_dvd_iff] at hmem'
      simp [hc] at hmem'⟩
  have hvx : v.1 x = WithZero.exp (-1 : ℤ) := by
    show v0 x = _; rw [hv0, heXs, hVX]
  refine ⟨v, by simp [ord, hvx], fun w hw => ?_⟩
  have hvl : v.1 x < 1 := by rw [hvx]; exact WithZero.exp_lt_exp.2 (by norm_num) |>.trans_eq WithZero.exp_zero
  apply Subtype.ext
  ext y
  obtain ⟨r, s, rfl⟩ := hmem y
  rw [map_div₀, map_div₀]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  rw [hpol w hw r hr, hpol w hw s hs, hpol v hvl r hr, hpol v hvl s hs]

end GlobalTheory.Nef
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Mx (t : F) (v : Place k F) : WithZero (Multiplicative ℤ) := max 1 (v.1 t)

theorem one_le_Mx (t : F) (v : Place k F) : 1 ≤ Mx t v := le_max_left _ _

theorem val_aeval_le (t : F) (p : k[X]) (v : Place k F) :
    v.1 (aeval t p) ≤ Mx t v ^ p.natDegree := by
  rw [aeval_eq_sum_range]
  refine v.1.map_sum_le fun i hi => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : v.1 (algebraMap k F (p.coeff i)) ≤ 1 := by
    by_cases h : p.coeff i = 0
    · simp [h]
    · exact (v.2.2 _ h).le
  calc v.1 (algebraMap k F (p.coeff i)) * v.1 t ^ i ≤ 1 * Mx t v ^ i :=
        mul_le_mul' hc (pow_le_pow_left₀ zero_le' (le_max_right _ _) i)
    _ = Mx t v ^ i := one_mul _
    _ ≤ Mx t v ^ p.natDegree := pow_le_pow_right₀ (one_le_Mx t v) hi'

theorem val_le_of_monic (t y : F) (P : F[X]) (hP : P.Monic) (hy : P.eval y = 0) (c : ℕ)
    (v : Place k F) (hc : ∀ i < P.natDegree, v.1 (P.coeff i) ≤ Mx t v ^ c) :
    v.1 y ≤ Mx t v ^ c := by
  by_contra hlt
  push_neg at hlt
  have hM : 1 ≤ Mx t v ^ c := one_le_pow₀ (one_le_Mx t v)
  have hy1 : 1 < v.1 y := lt_of_le_of_lt hM hlt
  have hy0 : v.1 y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy1)
  rw [hP.as_sum, eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum] at hy
  have heq := eq_neg_of_add_eq_zero_left hy
  have hlt2 : v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) <
      v.1 y ^ P.natDegree := by
    refine v.1.map_sum_lt (pow_ne_zero _ hy0) fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [eval_mul, eval_C, eval_pow, eval_X, map_mul, map_pow]
    calc v.1 (P.coeff i) * v.1 y ^ i ≤ Mx t v ^ c * v.1 y ^ i := mul_le_mul' (hc i hi') le_rfl
      _ < v.1 y * v.1 y ^ i := mul_lt_mul_of_pos_right hlt (pow_pos (lt_trans zero_lt_one hy1) _)
      _ = v.1 y ^ (i + 1) := (pow_succ' _ _).symm
      _ ≤ v.1 y ^ P.natDegree := pow_le_pow_right₀ hy1.le hi'
  have h3 : v.1 (y ^ P.natDegree) = v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) := by
    rw [heq, Valuation.map_neg]
  rw [map_pow] at h3
  rw [← h3] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem exists_mul_bdd (t y : F) (hy : IsAlgebraic k⟮t⟯ y) :
    ∃ q : k[X], aeval t q ≠ 0 ∧ ∃ c : ℕ, ∀ v : Place k F, v.1 (aeval t q * y) ≤ Mx t v ^ c := by
  classical
  obtain ⟨p, hp0, hpy⟩ := hy
  set A : Subalgebra k F := (aeval t : k[X] →ₐ[k] F).range with hA
  set P : F[X] := p.map (algebraMap k⟮t⟯ F) with hPdef
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap k⟮t⟯ F).injective).mpr hp0
  have hPy : P.eval y = 0 := by rw [hPdef, eval_map, ← aeval_def]; exact hpy
  have hcoef : ∀ i, ∃ s : k[X], aeval t s ≠ 0 ∧ aeval t s * P.coeff i ∈ A := by
    intro i
    rw [hPdef, coeff_map]
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k (p.coeff i : F)).mp (p.coeff i).2
    by_cases hs : aeval t s = 0
    · refine ⟨1, by simp, ?_⟩
      have : algebraMap k⟮t⟯ F (p.coeff i) = 0 := by
        change (p.coeff i : F) = 0
        rw [hrs, hs, div_zero]
      rw [this, mul_zero]; exact A.zero_mem
    · refine ⟨s, hs, ?_⟩
      change aeval t s * (p.coeff i : F) ∈ A
      rw [hrs, mul_div_cancel₀ _ hs]
      exact ⟨r, rfl⟩
  choose s hs0 hsA using hcoef
  set D : F := ∏ i ∈ Finset.range (P.natDegree + 1), aeval t (s i) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i
  set Q : F[X] := C D * P with hQdef
  have hQA : ∀ i, Q.coeff i ∈ A := by
    intro i
    rw [hQdef, coeff_C_mul]
    by_cases hi : i ∈ Finset.range (P.natDegree + 1)
    · rw [hD, ← Finset.prod_erase_mul _ _ hi, mul_assoc]
      refine A.mul_mem (A.prod_mem fun j _ => ⟨s j, rfl⟩) (hsA i)
    · have : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hi; omega)
      rw [this, mul_zero]; exact A.zero_mem
  have hQ0 : Q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hD0) hP0
  have hQy : Q.eval y = 0 := by rw [hQdef, eval_mul, hPy, mul_zero]
  set R : F[X] := integralNormalization Q with hRdef
  have hRmon : R.Monic := monic_integralNormalization hQ0
  have hRy : R.eval (Q.leadingCoeff * y) = 0 :=
    integralNormalization_eval₂_eq_zero (RingHom.id F) hQy (fun x hx => hx)
  have hRA : ∀ i, R.coeff i ∈ A := by
    intro i
    rw [hRdef, integralNormalization_coeff]
    split_ifs
    · exact A.one_mem
    · exact A.mul_mem (hQA i) (A.pow_mem (hQA _) _)
  choose pr hpr using hRA
  obtain ⟨q, hq⟩ := hQA Q.natDegree
  have hq' : aeval t q = Q.leadingCoeff := hq
  refine ⟨q, by rw [hq']; exact leadingCoeff_ne_zero.mpr hQ0,
    (Finset.range R.natDegree).sup fun i => (pr i).natDegree, fun v => ?_⟩
  rw [hq']
  refine val_le_of_monic t _ R hRmon hRy _ v fun i hi => ?_
  have h1 : R.coeff i = aeval t (pr i) := (hpr i).symm
  rw [h1]
  exact (val_aeval_le t (pr i) v).trans
    (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (f := fun i => (pr i).natDegree) (Finset.mem_range.mpr hi)))

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef

open Polynomial PolesOfT

theorem exists_many_bounded_by_pow : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  intro k F _ _ _ _ _ _ t ht
  by_cases hfin : FiniteDimensional k⟮t⟯ F
  swap
  · refine ⟨0, fun N => ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, fun i => i.elim0⟩⟩
    rw [Module.finrank_of_infinite_dimensional hfin]; simp
  set d := Module.finrank k⟮t⟯ F with hd
  let b := Module.finBasis k⟮t⟯ F
  have halg : ∀ j, IsAlgebraic k⟮t⟯ (b j) := fun j => Algebra.IsAlgebraic.isAlgebraic _
  choose q hq0 cj hcj using fun j => exists_mul_bdd t (b j) (halg j)
  refine ⟨Finset.univ.sup cj, fun N => ?_⟩
  set c := Finset.univ.sup cj with hc
  set L := N - c with hL
  let w : Fin d → k⟮t⟯ := fun j => aeval (IntermediateField.AdjoinSimple.gen k t) (q j)
  have hw : ∀ j, algebraMap k⟮t⟯ F (w j) = aeval t (q j) := fun j => by
    simp only [w]; rw [← aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hw0 : ∀ j, w j ≠ 0 := fun j h => hq0 j (by rw [← hw j, h, map_zero])
  let y : Fin d → F := fun j => aeval t (q j) * b j
  have hyli : LinearIndependent k⟮t⟯ y := by
    have := b.linearIndependent.units_smul (fun j => Units.mk0 (w j) (hw0 j))
    convert this using 1
    funext j
    simp [y, Algebra.smul_def, hw]
  have hpowF : LinearIndependent k (fun n : ℕ => t ^ n) := by
    have h1 := (Polynomial.basisMonomials k).linearIndependent.map' (aeval t).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp ht))
    have heq : (fun n : ℕ => t ^ n) = (aeval t).toLinearMap ∘ Polynomial.basisMonomials k := by
      funext n
      simp [Polynomial.coe_basisMonomials]
    rw [heq]
    exact h1
  have hpow : LinearIndependent k (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) := by
    have heq : (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap ∘
        (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) =
        (fun n : ℕ => t ^ n) ∘ (fun i : Fin L => (i : ℕ)) := by
      funext i
      simp
    apply LinearIndependent.of_comp (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap
    rw [heq]
    exact hpowF.comp _ Fin.val_injective
  have hprod := linearIndependent_smul hpow hyli
  refine ⟨L * d, fun i => (fun p : Fin L × Fin d => (IntermediateField.AdjoinSimple.gen k t) ^ (p.1 : ℕ) • y p.2)
    (finProdFinEquiv.symm i), hprod.comp _ finProdFinEquiv.symm.injective, ?_, ?_⟩
  · push_cast
    have h1 : ((N : ℤ) - c) ≤ (L : ℤ) := by omega
    exact mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg _)
  · intro i v
    dsimp only
    generalize finProdFinEquiv.symm i = p
    obtain ⟨a, j⟩ := p
    have hsm : (IntermediateField.AdjoinSimple.gen k t) ^ (a : ℕ) • y j = t ^ (a : ℕ) * (aeval t (q j) * b j) := by
      rw [Algebra.smul_def, map_pow, IntermediateField.AdjoinSimple.algebraMap_gen]
    dsimp only
    rw [hsm, map_mul, map_pow]
    have ha : (a : ℕ) + c ≤ N := by have := a.2; omega
    calc v.1 t ^ (a : ℕ) * v.1 (aeval t (q j) * b j) ≤ Mx t v ^ (a : ℕ) * Mx t v ^ c :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (le_max_right _ _) _)
            ((hcj j v).trans (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (Finset.mem_univ j))))
      _ = Mx t v ^ ((a : ℕ) + c) := (pow_add _ _ _).symm
      _ ≤ max 1 (v.1 t) ^ N := pow_le_pow_right₀ (one_le_Mx t v) ha

end GlobalTheory.Nef
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

namespace RatDilation

theorem coe_comp_C_mul_X {F : Type} [Field F] (a : F) (f : F[X]) :
    ((f.comp (C a * X) : F[X]) : PowerSeries F) = PowerSeries.rescale a (f : PowerSeries F) := by
  ext n
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
    split_ifs with h <;> simp [h, mul_comm]

theorem natDegree_comp_two {F : Type} [Field F] [CharZero F] (f : F[X]) :
    (f.comp (C (2:F) * X)).natDegree = f.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X _ two_ne_zero, mul_one]

theorem natDegree_eq_zero_of_sq_dvd {F : Type} [Field F] [CharZero F] (f g : F[X]) (hf : f ≠ 0)
    (hc : IsCoprime f g) (h : f.comp (C (2:F) * X) * g ^ 2 = g.comp (C (2:F) * X) * f ^ 2) :
    f.natDegree = 0 := by
  have hd : f ^ 2 ∣ f.comp (C (2:F) * X) := by
    have : f ^ 2 ∣ f.comp (C (2:F) * X) * g ^ 2 := h ▸ dvd_mul_left _ _
    exact (hc.pow).dvd_of_dvd_mul_right this
  have hne : f.comp (C (2:F) * X) ≠ 0 := by
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · exact hf h0
    · have := congrArg natDegree h0
      rw [natDegree_C_mul_X _ two_ne_zero, natDegree_C] at this
      exact one_ne_zero this
  have := natDegree_le_of_dvd hd hne
  rw [natDegree_comp_two, natDegree_pow] at this
  omega

end RatDilation


open RatDilation in
theorem rat_dilation_eq_one (F : Type) [Field F] [CharZero F] (φ : PowerSeries F) (hr : IsRat φ)
    (h0 : PowerSeries.constantCoeff φ = 1) (h2 : PowerSeries.rescale 2 φ = φ ^ 2) : φ = 1 := by
  classical
  obtain ⟨p₀, q₀, hq₀, hpq₀⟩ := hr
  set g := GCDMonoid.gcd p₀ q₀ with hg
  have hg0 : g ≠ 0 := fun h => hq₀ ((gcd_eq_zero_iff _ _).1 h).2
  set p := p₀ / g
  set q := q₀ / g
  have hcop : IsCoprime p q := isCoprime_div_gcd_div_gcd hq₀
  have hp₀ : p₀ = g * p := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)).symm
  have hq₀' : q₀ = g * q := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)).symm
  have hq : q ≠ 0 := by rintro h; rw [h, mul_zero] at hq₀'; exact hq₀ hq₀'
  have hgc : ((g : F[X]) : PowerSeries F) ≠ 0 := by
    rwa [Ne, Polynomial.coe_eq_zero_iff]
  have hpq : (q : PowerSeries F) * φ = (p : PowerSeries F) := by
    rw [hp₀, hq₀', Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc] at hpq₀
    exact mul_left_cancel₀ hgc hpq₀
  have hφ0 : φ ≠ 0 := by
    rintro rfl; simp at h0
  have hp : p ≠ 0 := by
    rintro h
    rw [h, Polynomial.coe_zero] at hpq
    rcases mul_eq_zero.1 hpq with h' | h'
    · exact hq ((Polynomial.coe_eq_zero_iff).1 h')
    · exact hφ0 h'
  have key : p.comp (C (2:F) * X) * q ^ 2 = q.comp (C (2:F) * X) * p ^ 2 := by
    apply Polynomial.coe_inj.1
    have e := congrArg (PowerSeries.rescale (2:F)) hpq
    rw [map_mul, h2, ← RatDilation.coe_comp_C_mul_X, ← RatDilation.coe_comp_C_mul_X] at e
    simp only [Polynomial.coe_mul, Polynomial.coe_pow]
    rw [← e, ← hpq]; ring
  have dq := RatDilation.natDegree_eq_zero_of_sq_dvd q p hq hcop.symm key.symm
  have dp := RatDilation.natDegree_eq_zero_of_sq_dvd p q hp hcop key
  rw [eq_C_of_natDegree_eq_zero dq, eq_C_of_natDegree_eq_zero dp] at hpq
  rw [Polynomial.coe_C, Polynomial.coe_C] at hpq
  have hc := congrArg PowerSeries.constantCoeff hpq
  simp only [map_mul, h0, mul_one, PowerSeries.constantCoeff_C] at hc
  rw [← hc] at hpq
  have ha : (PowerSeries.C (q.coeff 0) : PowerSeries F) ≠ 0 := by
    intro h
    have h0 : PowerSeries.C (q.coeff 0) = PowerSeries.C 0 := by simpa using h
    have h' : q.coeff 0 = 0 := PowerSeries.C_injective h0
    apply hq; rw [eq_C_of_natDegree_eq_zero dq, h', C_0]
  exact mul_left_cancel₀ ha (hpq.trans (mul_one _).symm)

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.comma_descent_restriction_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → Function.Surjective (CoefMap.restrict F G).pull2 := by
  first | exact @GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma | exact GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma | (intros; apply GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma <;> assumption)
end

section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

theorem _root_.GlobalTheory.T.tensor_holomorphic_ext_of_values : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  first | exact @GlobalTheory.tensor_hol_ext_of_values | exact GlobalTheory.tensor_hol_ext_of_values | (intros; apply GlobalTheory.tensor_hol_ext_of_values <;> assumption)
end
