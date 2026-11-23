module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

section

open ModularForm UpperHalfPlane Matrix EisensteinSeries Filter Topology
open scoped MatrixGroups

namespace UpperTheory.V.Sd

private def cSet {N : ℕ} (b : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) := {v | (↑) ∘ v = b}

private lemma vecMul_mem_cSet {N : ℕ} {b : Fin 2 → ZMod N} {v : Fin 2 → ℤ} (hv : v ∈ cSet b)
    (γ : SL(2, ℤ)) : v ᵥ* γ ∈ cSet (b ᵥ* γ) := by
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  have hv' : (fun x : ℤ => (x : ZMod N)) ∘ v = b := hv
  change (Int.cast : ℤ → ZMod N) ∘ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) = b ᵥ* _
  funext i
  rw [Function.comp_apply, this i, hv']
  simp [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

private def cEquiv {N : ℕ} (b : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : cSet b ≃ cSet (b ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_mem_cSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_mem_cSet v.2 γ⁻¹
      have h1 : ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
          (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
        have h0 : (γ : SL(2, ZMod N)) * ((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) = 1 :=
          (map_mul (SpecialLinearGroup.map (Int.castRingHom (ZMod N))) γ γ⁻¹).symm.trans (by simp)
        exact congrArg Subtype.val h0
      rwa [vecMul_vecMul, h1, vecMul_one] at this⟩
  left_inv v := by
    have h : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])
  right_inv v := by
    have h : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])

private noncomputable def cSer {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (z : ℍ) : ℂ :=
  ∑' x : cSet b, eisSummand k x z

private lemma cSer_slash {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (γ : SL(2, ℤ)) :
    cSer b k ∣[k] γ = cSer (b ᵥ* γ) k := by
  ext1 z
  simp_rw [SL_slash_apply, _root_.zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    cSer, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (cEquiv b γ).tsum_eq (eisSummand k · z)

private noncomputable def cSIF {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) :
    SlashInvariantForm (CongruenceSubgroup.Gamma N) k where
  toFun := cSer b k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ CongruenceSubgroup.Gamma N), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, cSer_slash, CongruenceSubgroup.Gamma_mem'.mp hA]

private lemma summand_le {k : ℕ} (v : Fin 2 → ℤ) (hv : v 0 ≠ 0) (z : ℍ) :
    ‖eisSummand k v z‖ ≤ (z.im ^ k)⁻¹ := by
  have hz := z.im_pos
  have him : z.im ≤ ‖(v 0 : ℂ) * (z : ℂ) + v 1‖ := by
    have h1 : ((v 0 : ℂ) * (z : ℂ) + v 1).im = (v 0 : ℝ) * z.im := by simp
    have h2 : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hv
    calc z.im ≤ |(v 0 : ℝ)| * z.im := by nlinarith
      _ = |((v 0 : ℂ) * (z : ℂ) + v 1).im| := by rw [h1, abs_mul, abs_of_pos hz]
      _ ≤ _ := Complex.abs_im_le_norm _
  simp only [eisSummand, norm_zpow]
  rw [_root_.zpow_neg, zpow_natCast]
  exact inv_anti₀ (pow_pos hz k) (pow_le_pow_left₀ hz.le him k)

private lemma cSer_zero {N : ℕ} [NeZero N] (b : Fin 2 → ZMod N) (hb : b 0 ≠ 0) {k : ℕ}
    (hk : 3 ≤ k) : IsZeroAtImInfty (cSer b k) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hkr : (2 : ℝ) < k := by exact_mod_cast (show 2 < k by omega)
  have hv0 : ∀ v : cSet b, v.1 0 ≠ 0 := by
    intro v h
    apply hb
    have h2 := congrFun v.2 0
    simp only [Function.comp_apply, h, Int.cast_zero] at h2
    exact h2.symm
  have hper : ∀ (n : ℤ) (z : ℍ), cSer b k ((N : ℝ) * (n : ℝ) +ᵥ z) = cSer b k z :=
    fun n z => SlashInvariantForm.vAdd_width_periodic N k n (cSIF b k) z
  set F : Filter ℍ := atImInfty ⊓ 𝓟 (verticalStrip N 1) with hF
  set C : ℝ := r ⟨⟨N, 1⟩, one_pos⟩ with hC
  have hsum : Summable (fun v : cSet b => C ^ (-(k : ℝ)) * ‖v.1‖ ^ (-(k : ℝ))) :=
    ((summable_one_div_norm_rpow hkr).subtype (fun v => v ∈ cSet b)).mul_left _
  have hT : Tendsto (fun z => cSer b k z) F (𝓝 0) := by
    have h0 : (0 : ℂ) = ∑' v : cSet b, (0 : ℂ) := by simp
    rw [h0]
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro v
      have him : Tendsto (fun z : ℍ => z.im) F atTop :=
        tendsto_comap.mono_left inf_le_left
      have hdec : Tendsto (fun z : ℍ => (z.im ^ k)⁻¹) F (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by omega)).comp him)
      exact squeeze_zero_norm' (Eventually.of_forall (fun z => summand_le v.1 (hv0 v) z)) hdec
    · rw [hF, eventually_inf_principal]
      apply Eventually.of_forall
      intro z hz v
      have h1 := summand_bound_of_mem_verticalStrip (k := (k : ℝ)) (by positivity) v.1 one_pos hz
      calc ‖eisSummand k v.1 z‖ = ‖(v.1 0 : ℂ) * z + v.1 1‖ ^ (-(k : ℝ)) := by
            rw [eisSummand, norm_zpow, ← Real.rpow_intCast]
            push_cast
            rfl
        _ ≤ _ := h1
  have hn : Tendsto (fun z => ‖cSer b k z‖) F (𝓝 0) := by simpa using hT.norm
  rw [isZeroAtImInfty_iff]
  intro ε hε
  have hev : ∀ᶠ z in F, ‖cSer b k z‖ ≤ ε := hn.eventually (Iic_mem_nhds hε)
  rw [hF, eventually_inf_principal] at hev
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  refine ⟨max A 1, fun z hz => ?_⟩
  have hfl1 := Int.floor_le (z.re / N)
  have hfl2 := Int.lt_floor_add_one (z.re / N)
  have e1 : (N : ℝ) * ⌊z.re / N⌋ ≤ z.re := by
    have := mul_le_mul_of_nonneg_left hfl1 hN.le
    rwa [mul_div_cancel₀ _ hN.ne'] at this
  have e2 : z.re < (N : ℝ) * ⌊z.re / N⌋ + N := by
    have := mul_lt_mul_of_pos_left hfl2 hN
    rwa [mul_div_cancel₀ _ hN.ne', mul_add, mul_one] at this
  have hmem : ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z) ∈ verticalStrip N 1 := by
    rw [mem_verticalStrip_iff, vadd_re, vadd_im, abs_le]
    push_cast
    refine ⟨⟨by nlinarith, by nlinarith⟩, by linarith [le_max_right A 1]⟩
  have hz' := hA ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z)
    (by rw [vadd_im]; linarith [le_max_left A 1]) hmem
  rwa [hper] at hz'

private lemma eisFun_eq (N k : ℕ) (a : ZMod N) :
    eisFun N k a = ((N : ℂ) ^ k / lipC k) • cSer ![0, a] k := by
  let e : {v : ℤ × ℤ // ((v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = a)} ≃ cSet (![0, a] : Fin 2 → ZMod N) :=
    { toFun := fun v => ⟨![v.1.1, v.1.2], by
        show (Int.cast : ℤ → ZMod N) ∘ ![v.1.1, v.1.2] = ![0, a]
        funext i
        fin_cases i
        · simpa using v.2.1
        · simpa using v.2.2⟩
      invFun := fun w => ⟨(w.1 0, w.1 1), by
        have h := w.2
        change (Int.cast : ℤ → ZMod N) ∘ w.1 = ![0, a] at h
        exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        funext i
        fin_cases i <;> simp }
  funext z
  simp only [eisFun, cSer, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← e.tsum_eq]
  congr 1

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.eisVan :
    UpperTheory.V.Sd.EisVan := by
  intro N k _ hk a ha hN γ hγ
  rw [UpperTheory.V.Sd.eisFun_eq, ModularForm.SL_smul_slash, UpperTheory.V.Sd.cSer_slash]
  apply Filter.ZeroAtFilter.smul
  apply UpperTheory.V.Sd.cSer_zero _ _ hk
  have hc : ((γ 1 0 : ℤ) : ZMod N) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hγ
  have e : (![0, a] ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) 0 = a * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
  rw [e]
  intro h
  exact hc ((ha.mul_right_eq_zero).mp h)
end

section

noncomputable section

open Polynomial

namespace UpperTheory.V.Sd

private lemma lk_deriv (k : ℕ) (x : ℂ) (hx : x ≠ 1) :
    ∃ d : ℂ, HasDerivAt (fun y : ℂ => Lk (k + 1) y) d x ∧ x * d = Lk (k + 2) x := by
  have hne : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hp := Polynomial.hasDerivAt_aeval (numL (k + 1)) x
  have hq : HasDerivAt (fun y : ℂ => (1 - y) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (1 - x) ^ k * (-1)) x := by
    have h1 : HasDerivAt (fun y : ℂ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℂ)
    have h2 := h1.pow (k + 1)
    simp only [Nat.add_sub_cancel] at h2
    exact h2
  refine ⟨_, hp.div hq (pow_ne_zero _ hne), ?_⟩
  have e : numL (k + 2) = X * (derivative (numL (k + 1)) * (1 - X) + C ((k : ℤ) + 1) * numL (k + 1)) := numL.eq_3 k
  unfold Lk
  rw [e]
  simp only [map_mul, map_add (f := _), map_sub, map_one, aeval_X, aeval_C]
  field_simp
  push_cast
  ring

private lemma lk_one (w : ℕ) (hw : 1 ≤ w) (ζ x : ℂ) (hζ : IsPrimitiveRoot ζ w) (hx : x ^ w ≠ 1) :
    ∑ j ∈ Finset.range w, Lk 1 (x * ζ ^ j) = (w : ℂ) ^ 1 * Lk 1 (x ^ w) := by
  have hy : ∀ j : ℕ, (x * ζ ^ j) ^ w = x ^ w := by
    intro j
    rw [mul_pow, ← pow_mul, mul_comm j w, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hxw : 1 - x ^ w ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hne : ∀ j : ℕ, 1 - x * ζ ^ j ≠ 0 := by
    intro j h
    apply hx
    rw [← hy j, ← sub_eq_zero.mp h, one_pow]
  have term : ∀ j : ℕ, Lk 1 (x * ζ ^ j) = (∑ m ∈ Finset.range w, (x * ζ ^ j) ^ m) / (1 - x ^ w) - 1 := by
    intro j
    have g := geom_sum_mul (x * ζ ^ j) w
    rw [hy j] at g
    unfold Lk
    simp only [numL.eq_2, aeval_X, pow_one]
    rw [eq_sub_iff_add_eq, div_add_one (hne j), div_eq_div_iff (hne j) hxw]
    linear_combination g
  have inner : ∀ m ∈ Finset.range w, ∑ j ∈ Finset.range w, (x * ζ ^ j) ^ m = if m = 0 then (w : ℂ) else 0 := by
    intro m hm
    split_ifs with h0
    · simp [h0]
    · have hm' : m < w := Finset.mem_range.mp hm
      have hq : ζ ^ m ≠ 1 := hζ.pow_ne_one_of_pos_of_lt h0 hm'
      have g := geom_sum_mul (ζ ^ m) w
      rw [← pow_mul, mul_comm m w, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at g
      have hs : ∑ i ∈ Finset.range w, (ζ ^ m) ^ i = 0 := by
        rcases mul_eq_zero.mp g with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hq
      calc ∑ j ∈ Finset.range w, (x * ζ ^ j) ^ m = x ^ m * ∑ i ∈ Finset.range w, (ζ ^ m) ^ i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j m]
        _ = 0 := by rw [hs, mul_zero]
  have total : ∑ j ∈ Finset.range w, ∑ m ∈ Finset.range w, (x * ζ ^ j) ^ m = w := by
    rw [Finset.sum_comm, Finset.sum_congr rfl inner, Finset.sum_ite_eq' (Finset.range w) 0]
    simp [Finset.mem_range.mpr (by omega : 0 < w)]
  rw [Finset.sum_congr rfl (fun j _ => term j), Finset.sum_sub_distrib, ← Finset.sum_div, total]
  unfold Lk
  simp only [numL.eq_2, aeval_X, pow_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp
  ring

theorem lkDist : LkDist := by
  intro w k hw hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro ζ x hζ hx
    exact lk_one w hw ζ x hζ hx
  | succ k hk ih =>
    intro ζ x hζ hx
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hy : ∀ j : ℕ, (x * ζ ^ j) ^ w = x ^ w := by
      intro j
      rw [mul_pow, ← pow_mul, mul_comm j w, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hne : ∀ j : ℕ, x * ζ ^ j ≠ 1 := by
      intro j h
      apply hx
      rw [← hy j, h, one_pow]
    choose d hd hdx using fun j : ℕ => lk_deriv m (x * ζ ^ j) (hne j)
    obtain ⟨e, he, hex⟩ := lk_deriv m (x ^ w) hx
    have hj : ∀ j : ℕ, HasDerivAt (fun y : ℂ => Lk (m + 1) (y * ζ ^ j)) (d j * ζ ^ j) x := by
      intro j
      exact (hd j).comp x (hasDerivAt_mul_const (ζ ^ j))
    have hF : HasDerivAt (fun y : ℂ => ∑ j ∈ Finset.range w, Lk (m + 1) (y * ζ ^ j))
        (∑ j ∈ Finset.range w, d j * ζ ^ j) x :=
      HasDerivAt.fun_sum (u := Finset.range w) (A := fun j (y : ℂ) => Lk (m + 1) (y * ζ ^ j))
        (A' := fun j => d j * ζ ^ j) (fun j _ => hj j)
    have hG : HasDerivAt (fun y : ℂ => (w : ℂ) ^ (m + 1) * Lk (m + 1) (y ^ w))
        ((w : ℂ) ^ (m + 1) * (e * ((w : ℂ) * x ^ (w - 1)))) x :=
      (he.comp x (hasDerivAt_pow w x)).const_mul _
    have hev : (fun y : ℂ => ∑ j ∈ Finset.range w, Lk (m + 1) (y * ζ ^ j)) =ᶠ[nhds x]
        (fun y : ℂ => (w : ℂ) ^ (m + 1) * Lk (m + 1) (y ^ w)) := by
      have ho : IsOpen {y : ℂ | y ^ w ≠ 1} := isOpen_ne_fun (continuous_pow w) continuous_const
      filter_upwards [ho.mem_nhds hx] with y hy'
      exact ih ζ y hζ hy'
    have heq := hF.unique (hG.congr_of_eventuallyEq hev)
    have hw' : x * x ^ (w - 1) = x ^ w := by
      rw [← pow_succ']
      congr 1
      omega
    calc ∑ j ∈ Finset.range w, Lk (m + 1 + 1) (x * ζ ^ j)
        = x * ∑ j ∈ Finset.range w, d j * ζ ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← hdx j]
          ring
      _ = (w : ℂ) ^ (m + 1 + 1) * Lk (m + 1 + 1) (x ^ w) := by
          rw [heq, ← hex, ← hw']
          ring

end UpperTheory.V.Sd
end
end

section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

theorem UpperTheory.V.Sd.cuspOf :
    UpperTheory.V.Sd.CuspOf := by
  intro N k _ χ f hχ hv h0
  have hT : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, ?_, ?_⟩
    · rw [SetLike.mem_coe, Gamma1_mem]
      simp [ModularGroup.T]
    · ext i j
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hinf : IsZeroAtImInfty f := by
    apply ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero f
    rw [← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hT)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hT)]
    exact h0
  refine ⟨⟨f.toSlashInvariantForm, f.holo', fun {c} hc => ?_⟩, rfl⟩
  have hc' : IsCusp c 𝒮ℒ := by
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
  intro γ _
  by_cases hd : (N:ℤ) ∣ γ 1 0
  · have hγ : γ ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hd)
    change IsZeroAtImInfty (⇑f ∣[(k:ℤ)] γ)
    rw [hχ γ hγ]
    exact hinf.smul _
  · exact hv γ hd
end

section

open UpperHalfPlane CongruenceSubgroup UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def GoodWt (k : ℕ) : Prop :=
  ∃ f : ModularForm 𝒮ℒ (k : ℤ), coef f 0 = 1 ∧ ∀ n, ∃ c : ℤ, coef f n = c

private lemma bern4 : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]
  norm_num

private lemma bern6 : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  norm_num [Finset.sum_range_succ, h5, Nat.choose, bernoulli'_four, bernoulli'_three, bernoulli'_two]

private lemma good0 : GoodWt 0 := by
  refine ⟨(1 : ModularForm 𝒮ℒ 0), ?_, fun n => ?_⟩
  · simp [coef, qExpansion_one]
  · refine ⟨if n = 0 then 1 else 0, ?_⟩
    simp [coef, qExpansion_one, PowerSeries.coeff_one]

private lemma good4 : GoodWt 4 := by
  refine ⟨ModularForm.E (k := 4) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern4]
    split_ifs
    · simp
    · push_cast; ring

private lemma good6 : GoodWt 6 := by
  refine ⟨ModularForm.E (k := 6) (by norm_num), ?_, fun n => ?_⟩
  · exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  · refine ⟨if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ), ?_⟩
    unfold coef
    rw [EisensteinSeries.E_qExpansion_coeff _ (by decide), bern6]
    split_ifs
    · simp
    · push_cast; ring

private lemma good_add {a b : ℕ} (ha : GoodWt a) (hb : GoodWt b) : GoodWt (a + b) := by
  obtain ⟨f, hf0, hf⟩ := ha
  obtain ⟨g, hg0, hg⟩ := hb
  have h := ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g
  have key : ∀ n, coef (ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g)) n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coef f p.1 * coef g p.2 := by
    intro n
    unfold coef
    rw [ModularForm.coe_mcast, h, PowerSeries.coeff_mul]
  refine ⟨ModularForm.mcast (show (a : ℤ) + b = ((a + b : ℕ) : ℤ) by push_cast; ring) (f.mul g), ?_, fun n => ?_⟩
  · rw [key]; simp [hf0, hg0]
  · choose c hc using hf
    choose d hd using hg
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2, ?_⟩
    rw [key]
    simp [hc, hd]

private lemma good_all (k : ℕ) (hk : Even k) (h2 : k ≠ 2) : GoodWt k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨m, hm⟩ := hk
    by_cases h0 : k = 0
    · subst h0; exact good0
    by_cases h6 : k = 6
    · subst h6; exact good6
    have : k = (k - 4) + 4 := by omega
    rw [this]
    exact good_add (ih _ (by omega) ⟨m - 2, by omega⟩ (by omega)) good4

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.levelOne :
    UpperTheory.V.Sd.LevelOne := by
  intro N k _ hk h2
  obtain ⟨f, hf0, hf⟩ := UpperTheory.V.Sd.good_all k hk h2
  have hle : (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _
  refine ⟨⟨⟨f, fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)⟩, ModularFormClass.holo f,
    fun hc => f.bdd_at_cusps' (hc.mono hle)⟩, fun γ => ?_, hf0, hf⟩
  exact SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
end
