module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle228
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle188
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
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
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.MvPolynomial.Ideal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.PhiFree

open PowerSeries

theorem bijective_of_congr {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (a : R) [IsPrecomplete (Ideal.span {a}) M] [IsHausdorff (Ideal.span {a}) M]
    [IsHausdorff (Ideal.span {a}) N] (ha : ∀ y : N, a • y = 0 → y = 0) (S T : M →ₗ[R] N)
    (hS : Function.Bijective S) (h : ∀ z, T z - S z ∈ (Ideal.span {a} • ⊤ : Submodule R N)) :
    Function.Bijective T := by
  constructor
  · rw [injective_iff_map_eq_zero]
    have step : ∀ z, T z = 0 → ∃ z', T z' = 0 ∧ z = a • z' := fun z hz => by
      have h1 := h z
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨u, -, hu⟩ := h1
      obtain ⟨v, rfl⟩ := hS.2 u
      have h2 : z = a • (-v) := hS.1 (by rw [map_smul, map_neg, smul_neg, hu, hz]; simp)
      exact ⟨-v, ha _ (by rw [← map_smul, ← h2, hz]), h2⟩
    have all : ∀ (n : ℕ) z, T z = 0 → ∃ z', z = a ^ n • z' := fun n => by
      induction n with
      | zero => exact fun z _ => ⟨z, by simp⟩
      | succ n ih =>
        intro z hz
        obtain ⟨z', h1, rfl⟩ := step z hz
        obtain ⟨w, rfl⟩ := ih z' h1
        exact ⟨w, by rw [smul_smul, pow_succ']⟩
    intro z hz
    refine IsHausdorff.haus' (I := Ideal.span {a}) z fun n => ?_
    obtain ⟨w, rfl⟩ := all n z hz
    rw [SModEq.zero]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) n) trivial
  · refine surjective_of_mkQ_comp_surjective (I := Ideal.span {a}) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    obtain ⟨z, rfl⟩ := hS.2 G
    exact ⟨z, (Submodule.Quotient.eq _).2 (h z)⟩

theorem bijective_one_add {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : B) (n : ℕ)
    (h : Function.Bijective fun z : Fin n → A => ∑ j : Fin n, x ^ (j : ℕ) * f (z j)) :
    Function.Bijective fun z : Fin n → A => ∑ j : Fin n, (1 + x) ^ (j : ℕ) * f (z j) := by
  have key : ∀ (t : B) (p : Polynomial.degreeLT A n),
      ∑ j : Fin n, t ^ (j : ℕ) * f (Polynomial.degreeLTEquiv A n p j) = p.1.eval₂ f t := fun t p => by
    rw [Polynomial.eval₂_eq_sum, ← Polynomial.sum_fin _ (by simp) (Polynomial.mem_degreeLT.1 p.2)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let e : (Fin n → A) ≃ₗ[A] (Fin n → A) := (Polynomial.degreeLTEquiv A n).symm.trans
    ((Polynomial.taylorLinearEquiv 1 n).trans (Polynomial.degreeLTEquiv A n))
  convert h.comp e.bijective using 1
  funext z
  obtain ⟨p, rfl⟩ := (Polynomial.degreeLTEquiv A n).surjective z
  simp only [e, Function.comp, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, key]
  change _ = (Polynomial.taylor 1 p.1).eval₂ f x
  rw [Polynomial.taylor_apply, Polynomial.eval₂_comp]
  simp [add_comm]

theorem coeff_sum_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) (z : Fin n → R⟦X⟧) (i : Fin n)
    (m : ℕ) : coeff (n * m + i) (∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j)) = coeff m (z i) := by

  rw [map_sum, Finset.sum_eq_single i]
  · rw [coeff_X_pow_mul, coeff_expand_mul]
  · intro j _ hj
    rw [coeff_X_pow_mul']
    split_ifs with h
    · refine coeff_expand_of_not_dvd _ _ _ fun hd => hj (Fin.ext ?_)
      have h1 : (j : ℕ) ≡ n * m + i [MOD n] := (Nat.modEq_iff_dvd' h).2 hd
      have h2 : n * m + i ≡ i [MOD n] := by simp [Nat.ModEq]
      exact (h1.trans h2).eq_of_lt_of_lt j.2 i.2
    · rfl
  · simp

theorem bijective_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective fun z : Fin n → R⟦X⟧ => ∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j) := by
  constructor
  · intro z z' h
    funext i
    ext m
    rw [← coeff_sum_expand n hn z, ← coeff_sum_expand n hn z']
    exact congrArg _ h
  · intro y
    refine ⟨fun i => PowerSeries.mk fun m => coeff (n * m + i) y, ?_⟩
    ext k
    have h := coeff_sum_expand n hn (fun i => PowerSeries.mk fun m => coeff (n * m + i) y)
      ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩ (k / n)
    simpa [Nat.div_add_mod] using h

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem coeff_phi_sub_expand_mem (J : Ideal O) (hl : (l : O) ∈ J) (z : O⟦X⟧) (k : ℕ) :
    coeff k (phi l O z - expand l (Fact.out : l.Prime).ne_zero z) ∈ J := by
  have h : (PowerSeries.map (Ideal.Quotient.mk J)).comp (phi l O : O⟦X⟧ →+* O⟦X⟧) =
      (PowerSeries.map (Ideal.Quotient.mk J)).comp
        (expand l (Fact.out : l.Prime).ne_zero : O⟦X⟧ →ₐ[O] O⟦X⟧) := by
    have hX : PowerSeries.map (Ideal.Quotient.mk J) (phi l O X) = X ^ l := by
      obtain ⟨r, hr⟩ := Series.phi_X_mod l O
      have h0 : ((l : ℕ) : (O ⧸ J)⟦X⟧) = 0 := by
        rw [← map_natCast (C (R := O ⧸ J)), ← map_natCast (Ideal.Quotient.mk J),
          Ideal.Quotient.eq_zero_iff_mem.2 hl, map_zero]
      rw [hr]
      simp [h0]
    refine Fon.ps_hom_ext (fun r => ?_) ?_ ?_
    · exact congrArg (PowerSeries.map (Ideal.Quotient.mk J))
        (((phi l O).commutes r).trans ((expand l (Fact.out : l.Prime).ne_zero).commutes r).symm)
    · exact hX.trans (by simp)
    · refine Fon.eq_zero_of_pow_dvd ?_
      change constantCoeff (PowerSeries.map (Ideal.Quotient.mk J) (phi l O X)) = 0
      rw [hX]
      simp [(Fact.out : l.Prime).ne_zero]
  have h1 := congrArg (coeff k) (RingHom.congr_fun h z)
  rw [map_sub, ← Ideal.Quotient.eq]
  simpa only [RingHom.comp_apply, coeff_map, RingHom.coe_coe] using h1

end GlobalTheory.Cyc.PhiFree

namespace GlobalTheory.Cyc

open PhiFree CompleteBaseChange

theorem phi_free : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  intro l _ O _ _ _ _ _ _ hl y
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := ha.maximalIdeal_eq
  have hla : (l : O) ∈ Ideal.span {a} := hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hl
  have : IsAdicComplete (Ideal.span {a}) O := hm ▸ ‹_›
  have hJ : (Ideal.span {a}).FG := Submodule.fg_span_singleton a
  have : IsPrecomplete (Ideal.span {a}) (PowerSeries O) := GlobalTheory.CompleteBaseChange.isPrecomplete_pi (Unit →₀ ℕ) hJ
  have : IsHausdorff (Ideal.span {a}) (PowerSeries O) := GlobalTheory.CompleteBaseChange.isHausdorff_pi (Unit →₀ ℕ) hJ
  have : IsPrecomplete (Ideal.span {a}) (Fin l → PowerSeries O) := GlobalTheory.CompleteBaseChange.isPrecomplete_pi _ hJ
  have : IsHausdorff (Ideal.span {a}) (Fin l → PowerSeries O) := GlobalTheory.CompleteBaseChange.isHausdorff_pi _ hJ
  let F : (PowerSeries O →ₐ[O] PowerSeries O) → (Fin l → PowerSeries O) →ₗ[O] PowerSeries O := fun f =>
    { toFun := fun z => ∑ j : Fin l, PowerSeries.X ^ (j : ℕ) * f (z j)
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum] }
  have hT : Function.Bijective (F (phi l O)) := by
    refine bijective_of_congr a (fun y hy => ?_) (F (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)) _
      (bijective_expand l _) fun z => ?_
    · ext k
      have h1 := congrArg (PowerSeries.coeff k) hy
      rw [map_smul, map_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left ha.ne_zero
    · change (∑ j : Fin l, _) - (∑ j : Fin l, _) ∈ _
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 : phi l O (z j) - PowerSeries.expand l (Fact.out : l.Prime).ne_zero (z j) ∈
          (Ideal.span {a} • ⊤ : Submodule O (PowerSeries O)) :=
        (mem_smul_top_pi (ι := Unit →₀ ℕ) hJ _).2 fun d => by
          have h2 := coeff_phi_sub_expand_mem l O _ hla (z j) (d ())
          rw [PowerSeries.coeff, Finsupp.unique_single d |>.symm] at h2
          rw [smul_eq_mul, Ideal.mul_top]
          exact h2
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
      obtain ⟨u, -, hu⟩ := h1
      exact ⟨PowerSeries.X ^ (j : ℕ) * u, trivial, by rw [← mul_sub, ← hu, mul_smul_comm]⟩
  have h := (bijective_one_add (phi l O : PowerSeries O →+* PowerSeries O) PowerSeries.X l hT).existsUnique y
  simpa only [eq_comm (a := y), RingHom.coe_coe] using h

end GlobalTheory.Cyc
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.WindowArith

theorem sg_ineq (l n : ℕ) [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    h i + sg l h i + 1 ≤ l * (sg l h (i - 1) + 1) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hshift : ∀ j : ℕ, (h (i - 1 + ((j + 1 + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1 + 1)
      = (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) / l := by
    intro j
    have e : i - 1 + ((j + 1 + 1 : ℕ) : ZMod n) = i + ((j + 1 : ℕ) : ZMod n) := by
      push_cast; ring
    rw [e, pow_succ, div_div]
  have e0 : i - 1 + ((0 + 1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hrec : (l : ℝ) * (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
      = h i + ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
    rw [(summable_sg hl h (i - 1)).tsum_eq_zero_add, e0]
    simp only [hshift, tsum_div_const]
    field_simp
    ring
  have hS0 : 0 ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  have h1 := Nat.floor_le hS0
  have h2 := Nat.lt_floor_add_one
    (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
  have h3 := mul_lt_mul_of_pos_left h2 hl0
  have key : (h i : ℝ) + (⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ)
      < (l : ℝ) * ((⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ) + 1) := by
    linarith
  have key' : h i + ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊
      < l * (⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ + 1) := by
    exact_mod_cast key
  simp only [sg]
  omega

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ u - y := ((CharP.intCast_eq_intCast k l).mp h).symm.dvd
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by linarith, h1⟩)
  linarith

private theorem cast_ne_of_mem_cloud_of_typeG {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hG : Dt.ty i = LType.G) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ y) (hy2 : y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) :
    (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu y hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hG]
  exact hm

private theorem natCast_ne_of_mem_cloud_of_bd_of_mem_range {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hB : Dt.ty i = LType.Bd) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ (Dt.h i : ℤ) - y)
    (hy2 : (Dt.h i : ℤ) - y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) : (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu ((Dt.h i : ℤ) - y) hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hB]
  exact Int.ModEq.sub (Int.ModEq.refl _) hm

theorem windows : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  intro k _ l n r _ _ _ Dt hT1 hT2 hT3 i
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hT1i := hT1 i
  have ht := Dt.one_le_letterBlockLength
  have hwB : Dt.w i ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩))
  have heB : Dt.w i + Dt.t - 1 ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩))
  have factsG : Dt.ty i = LType.G → (∀ u ∈ Dt.lows i, 1 ≤ u ∧ u ≤ (Dt.η i : ℤ)) ∧
      1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i := fun hG =>
    ⟨fun u hu => Dt.lowG i hG u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowG i hG _ hwB).1,
      (Dt.lowG i hG _ heB).2⟩
  have factsBd : Dt.ty i = LType.Bd → (∀ u ∈ Dt.lows i, (Dt.h i : ℤ) - Dt.η i ≤ u ∧ u ≤ (Dt.h i : ℤ) - 1) ∧
      (Dt.h i : ℤ) - Dt.η i ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ (Dt.h i : ℤ) - 1 := fun hB =>
    ⟨fun u hu => Dt.lowBd i hB u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowBd i hB _ hwB).1,
      (Dt.lowBd i hB _ heB).2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsg := sg_ineq l n hl2 Dt.h i
    have e1 : Dt.sg l i = sg l Dt.h i := rfl
    have e2 : Dt.sg l (i - 1) = sg l Dt.h (i - 1) := rfl
    rw [e1, e2]
    zify at hsg
    linarith
  · intro u hu y hy1 hy2 he
    rcases Multiset.mem_add.1 hu with hu | hu
    · have huy : u = y := by
        cases hty : Dt.ty i
        · obtain ⟨hL, hw1, hw2⟩ := factsG hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
        · obtain ⟨hL, hw1, hw2⟩ := factsBd hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
      have key : ∃ β ∈ Dt.B i, |u - β| ≤ (Dt.sg l i : ℤ) + 2 := by
        by_cases hyw : y < Dt.w i
        · exact ⟨Dt.w i, mem_block.2 ⟨le_rfl, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        by_cases hye : Dt.w i + Dt.t - 1 < y
        · exact ⟨Dt.w i + Dt.t - 1, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        · exact ⟨y, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
      obtain ⟨β, hβ, hb⟩ := key
      have := hT2 i u hu β hβ
      linarith
    · cases hty : Dt.ty i
      · obtain ⟨-, hw1, hw2⟩ := factsG hty
        exact cast_ne_of_mem_cloud_of_typeG hT3 hty hu y (by omega) (by omega) he
      · obtain ⟨-, hw1, hw2⟩ := factsBd hty
        exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hty hu y (by omega) (by omega) he
  · intro hG
    obtain ⟨hL, hw1, hw2⟩ := factsG hG
    refine ⟨?_, ?_, hw1, hw2⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
  · intro hB
    obtain ⟨hL, hw1, hw2⟩ := factsBd hB
    have ew : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    refine ⟨?_, ?_, by rw [ew]; omega, by rw [ew]; omega⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he

end GlobalTheory.WindowArith
end

section

open GlobalTheory.LogU

namespace GlobalTheory.LogU

open MvPolynomial

theorem logDefect_coeff_eq_zero : ∀ (n i j : ℕ), i + j < n →
    AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  intro n i j hij
  let J : Ideal (MvPolynomial (Fin 2) ℚ) := MvPolynomial.idealOfVars (Fin 2) ℚ
  let q : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ ⧸ J ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin 2) ℚ ⧸ J ^ n) := fun m hm => by
    have hu : IsUnit ((m : ℚ)) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hu.map (q.comp MvPolynomial.C)
  have hI : (J.map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]; exact Ideal.map_quotient_self _
  have hXJ : ∀ k, (X k : MvPolynomial (Fin 2) ℚ) ∈ J := fun k =>
    Ideal.subset_span (Set.mem_range_self k)
  have key := GlobalTheory.MemLoc.LogAdd.trunc_add hR n _ hI (q (X 0)) (q (X 1))
    (Ideal.mem_map_of_mem q (hXJ 0)) (Ideal.mem_map_of_mem q (hXJ 1))
  have h0 : MvPolynomial.aeval ![q (X 0), q (X 1)] (logDefect n) = 0 := by
    refine (aeval_logDefect n (q (X 0)) (q (X 1))).trans ?_
    simp only [truncLogF]; rw [key]; ring
  have hcomp : q.comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.aeval (R := ℤ) ![q (X 0), q (X 1)]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro k; fin_cases k <;> simp
  have hφ : q (MvPolynomial.map (Int.castRingHom ℚ) (logDefect n)) = 0 := by
    have := RingHom.congr_fun hcomp (logDefect n)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, h0]
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff'] at hφ
  have hd : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree < n := by
    first
      | simpa [Finsupp.degree_single] using hij
      | simpa [Finsupp.degree, Finsupp.support_single_ne_zero] using hij
  have := hφ _ hd
  rw [MvPolynomial.coeff_map] at this
  simpa using this

end GlobalTheory.LogU
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem N_overExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ x : B.A, (overExt φ B ψ hψ hσ).N x = B.N x := by
  intro K K' d φ hU B ψ hψ hσ hO x
  refine (@GlobalTheory.T.weightedOrbitSum_congr_coefficientRing K.O K'.O B.A _ _ B.cA B.aO (overExt φ B ψ hψ hσ).aO B.T (B.X x) ((overExt φ B ψ hψ hσ).X x) ?_ ?_ ?_)
  · intro L hL
    let S : Subalgebra K.O B.A :=
      { carrier := {a | ∀ z ∈ L, a * z ∈ L}
        mul_mem' := fun {a b} ha hb z hz => by rw [mul_assoc]; exact ha _ (hb z hz)
        add_mem' := fun {a b} ha hb z hz => by rw [add_mul]; exact L.add_mem (ha z hz) (hb z hz)
        algebraMap_mem' := fun c z hz => by rw [← Algebra.smul_def]; exact L.smul_mem c hz }
    have hS : Algebra.adjoin K.O ({B.g} : Set B.A) ≤ S := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact fun z hz => hL.2.1 z hz
    let L' : Submodule K'.O (overExt φ B ψ hψ hσ).A :=
      { carrier := (L : Set B.A)
        add_mem' := fun ha hb => L.add_mem ha hb
        zero_mem' := L.zero_mem
        smul_mem' := fun c z hz => hS (hO c) z hz }
    refine ⟨L', ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' L rfl).2 hL.1, fun y hy => hL.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y).symm
  · intro L' hL'
    let M : Submodule K.O B.A :=
      { carrier := (L' : Set B.A)
        add_mem' := fun ha hb => L'.add_mem ha hb
        zero_mem' := L'.zero_mem
        smul_mem' := fun c z hz => by
          obtain ⟨b, hb⟩ := exists_int_image hU c
          have h : c • z = ψ (algebraMap K'.O K'.E b) * z := by
            rw [Algebra.smul_def, hb, hψ, ← IsScalarTower.algebraMap_apply]
          rw [h]; exact L'.smul_mem b hz }
    refine ⟨M, ⟨(GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff K K' d φ hU B ψ hψ hσ L' M rfl).1 hL'.1, fun y hy => hL'.2.1 y hy, fun y => ?_⟩, rfl⟩
    exact (hL'.2.2 y).trans (GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff K K' d φ hU B ψ hψ hσ L' x y)
  · ext t
    simp only [Subgroup.mem_inf]
    refine and_congr_left' ?_
    change (IsIntegral K.O (t : B.A) ∧ IsIntegral K.O ((t⁻¹ : B.Aˣ) : B.A)) ↔
      (@IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ (t : B.A) ∧ @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ ((t⁻¹ : B.Aˣ) : B.A))
    rw [GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ, GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base K K' d φ hU B ψ hψ hσ]

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.exists_unramified_involution_field_embedding : ∀ (K : UQ), K.Odd → ∀ B : InvAlg K, B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_unr_embedding | exact GlobalTheory.UnitLemma.Unr.exists_unr_embedding | (intros; apply GlobalTheory.UnitLemma.Unr.exists_unr_embedding <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  first | exact @GlobalTheory.JR.LinDesc.unitsMeas_isHaar | exact GlobalTheory.JR.LinDesc.unitsMeas_isHaar | (intros; apply GlobalTheory.JR.LinDesc.unitsMeas_isHaar <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

theorem _root_.GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  first | exact @GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | exact GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | (intros; apply GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem <;> assumption)
end
