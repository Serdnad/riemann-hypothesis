module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Mathlib.Topology.LocallyConstant.Basic
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle069
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

@[expose] public section

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.WDivE

theorem coeff_vanish_mul {K : Type} [CommRing K] {F G : K⟦X⟧} {a b : ℕ}
    (hF : ∀ k, a < k → coeff k F = 0) (hG : ∀ k, b < k → coeff k G = 0) (k : ℕ) (hk : a + b < k) :
    coeff k (F * G) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : a < p.1
  · rw [hF _ h, zero_mul]
  · rw [hG _ (by omega), mul_zero]

theorem eq_sum_of_vanish {K : Type} [CommRing K] {P : K⟦X⟧} {N : ℕ}
    (hP : ∀ k, N ≤ k → coeff k P = 0) : P = ∑ k : Fin N, C (coeff (k : ℕ) P) * X ^ (k : ℕ) := by
  ext m

  rw [map_sum]
  simp only [coeff_C_mul_X_pow]
  by_cases hm : m < N
  · rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
    · simp
  · rw [hP m (by omega), Finset.sum_eq_zero]
    intro b _; rw [if_neg]; omega

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [CompleteSpace K] [NeZero e] in
theorem quotE_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : quotE l e f ∈ A O K := fun n => by
  rw [quotE, coeff_mk]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun j => ?_
  rw [norm_mul, norm_pow, norm_neg]
  exact mul_le_one₀ (hf _) (by positivity) (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)

theorem div_E_step {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e * g :=
  ⟨f - E K l e * quotE l e f, quotE l e f,
    sub_mem hf (mul_mem (E_mem l e _) (quotE_mem_A l e hf)),
    fun k hk => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact coeff_sub_E_mul_quotE l e (A_le_Rpi l e hf) m,
    quotE_mem_A l e hf, by ring⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem coeff_E_pow_vanish (n : ℕ) : ∀ k, e * n < k → coeff k (E K l e ^ n) = 0 := by
  induction n with
  | zero => intro k hk; simp [coeff_one]; omega
  | succ n ih =>
    intro k hk
    rw [pow_succ]
    refine coeff_vanish_mul ih (b := e) (fun j hj => ?_) k (by rw [Nat.mul_succ] at hk; exact hk)
    rw [E, map_add (f := _), coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

theorem div_E_pow (n : ℕ) {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e * n ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e ^ n * g := by
  induction n with
  | zero => exact ⟨0, f, zero_mem _, fun _ _ => by simp, hf, by simp⟩
  | succ n ih =>
    obtain ⟨P, g, hP, hPv, hg, rfl⟩ := ih
    obtain ⟨Q, h, hQ, hQv, hh, rfl⟩ := div_E_step l e hg
    refine ⟨P + E K l e ^ n * Q, h, add_mem hP (mul_mem (pow_mem (E_mem l e _) n) hQ),
      fun k hk => ?_, hh, by ring⟩
    have he := NeZero.pos e
    rw [map_add (f := _), hPv k (by rw [Nat.mul_succ] at hk; omega), zero_add]
    exact coeff_vanish_mul (coeff_E_pow_vanish l e n) (b := e - 1)
      (fun j hj => hQv j (by omega)) k (by rw [Nat.mul_succ] at hk; omega)

end GlobalTheory.WDivE

theorem GlobalTheory.weierstrassDiv_E_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  intro O K _ _ _ _ _ _ l e _ _ _ n f hf
  obtain ⟨P, g, hP, hPv, hg, rfl⟩ := GlobalTheory.WDivE.div_E_pow l e n hf
  choose c hc using fun k : Fin (e * n) => (IsUnitBall.mem_range_iff (O := O) (coeff (k : ℕ) P)).2 (hP k)
  refine ⟨c, g, hg, ?_⟩
  simp only [hc]
  rw [← GlobalTheory.WDivE.eq_sum_of_vanish hPv]
end

section

open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK.HatInj

def LastMax (w : ℕ → ℝ) (d : ℕ) : Prop := (∀ n, w n ≤ w d) ∧ ∀ n, d < n → w n < w d

theorem LastMax.unique {w : ℕ → ℝ} {d d' : ℕ} (h : LastMax w d) (h' : LastMax w d') : d = d' := by
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · exact absurd (h.2 d' hlt) (not_lt.mpr (h'.1 d))
  · exact heq
  · exact absurd (h'.2 d hgt) (not_lt.mpr (h.1 d'))

theorem exists_lastMax {w : ℕ → ℝ} (hw : Tendsto w atTop (𝓝 0)) {n₀ : ℕ} (h₀ : 0 < w n₀) :
    ∃ d, LastMax w d := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hw.eventually (gt_mem_nhds h₀))
  have hn₀ : n₀ < N := by
    by_contra hc
    exact lt_irrefl _ (hN n₀ (not_lt.mp hc))
  obtain ⟨a, ha, hmax⟩ := (Finset.range N).exists_max_image w ⟨n₀, Finset.mem_range.mpr hn₀⟩
  have hbig : ∀ n, N ≤ n → w n < w a := fun n hn =>
    (hN n hn).trans_le (hmax n₀ (Finset.mem_range.mpr hn₀))
  let T := (Finset.range N).filter (fun n => w n = w a)
  have hTne : T.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  have hda : w (T.max' hTne) = w a := (Finset.mem_filter.mp (T.max'_mem hTne)).2
  refine ⟨T.max' hTne, fun n => ?_, fun n hn => ?_⟩
  · rw [hda]
    rcases lt_or_ge n N with hnN | hnN
    · exact hmax n (Finset.mem_range.mpr hnN)
    · exact (hbig n hnN).le
  · rw [hda]
    rcases lt_or_ge n N with hnN | hnN
    · refine lt_of_le_of_ne (hmax n (Finset.mem_range.mpr hnN)) fun heq => ?_
      have hT : n ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN, heq⟩
      exact absurd (T.le_max' n hT) (not_le.mpr hn)
    · exact hbig n hnN
private theorem coeff_E_mul' {K : Type} [NormedField K] [IsUltrametricDist K] (l e : ℕ)
    (h : K⟦X⟧) (n : ℕ) :
    coeff n (E K l e * h) = (if e ≤ n then coeff (n - e) h else 0) + (l : K) * coeff n h := by
  rw [E, add_mul, map_add (f := _), coeff_X_pow_mul', ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul]

variable {K : Type} [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem lastMax_E_mul {h : K⟦X⟧} {d : ℕ}
    (H : LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d) :
    LastMax (fun n => ‖coeff n (E K l e * h)‖ * rad l (1 / e) ^ n) (d + e) := by
  have hr : 0 < rad l (1 / (e : ℝ)) := rad_pos l _
  have hre : rad l (1 / (e : ℝ)) ^ e = ‖(l : K)‖ := rad_pow l e
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (l_ne_zero (K := K) l)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hlow : ∀ n, n < e → ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n =
      ‖(l : K)‖ * (‖coeff n h‖ * rad l (1 / (e : ℝ)) ^ n) := by
    intro n hn
    rw [coeff_E_mul', if_neg (not_le.mpr hn), zero_add, norm_mul]
    ring
  have hhigh : ∀ k, ‖coeff (k + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (k + e) ≤
      max (‖(l : K)‖ * (‖coeff k h‖ * rad l (1 / (e : ℝ)) ^ k))
        (‖(l : K)‖ * (‖coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e))) := by
    intro k
    rw [coeff_E_mul', if_pos (Nat.le_add_left e k), Nat.add_sub_cancel]
    calc ‖coeff k h + (l : K) * coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e)
        ≤ max ‖coeff k h‖ ‖(l : K) * coeff (k + e) h‖ * rad l (1 / (e : ℝ)) ^ (k + e) :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (pow_nonneg hr.le _)
      _ = _ := by
          rw [max_mul_of_nonneg _ _ (pow_nonneg hr.le _)]
          congr 1
          · rw [pow_add, hre]; ring
          · rw [norm_mul]; ring
  have htop : ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e) =
      ‖(l : K)‖ * (‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ d) := by
    rw [coeff_E_mul', if_pos (Nat.le_add_left e d), Nat.add_sub_cancel]
    have hsmall : ‖(l : K) * coeff (d + e) h‖ < ‖coeff d h‖ := by
      have hlt := mul_lt_mul_of_pos_left (H.2 (d + e) (by omega)) hl
      refine lt_of_mul_lt_mul_right ?_ (pow_pos hr (d + e)).le
      calc ‖(l : K) * coeff (d + e) h‖ * rad l (1 / (e : ℝ)) ^ (d + e)
          = ‖(l : K)‖ * (‖coeff (d + e) h‖ * rad l (1 / (e : ℝ)) ^ (d + e)) := by
            rw [norm_mul]; ring
        _ < ‖(l : K)‖ * (‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ d) := hlt
        _ = ‖coeff d h‖ * rad l (1 / (e : ℝ)) ^ (d + e) := by rw [pow_add, hre]; ring
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsmall.ne', max_eq_left hsmall.le,
      pow_add, hre]
    ring
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · show ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n ≤ ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e)
    rw [htop]
    rcases lt_or_ge n e with hne | hne
    · rw [hlow n hne]
      exact mul_le_mul_of_nonneg_left (H.1 n) hl.le
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hne
      exact (hhigh k).trans (max_le (mul_le_mul_of_nonneg_left (H.1 k) hl.le)
        (mul_le_mul_of_nonneg_left (H.1 (k + e)) hl.le))
  · show ‖coeff n (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ n < ‖coeff (d + e) (E K l e * h)‖ * rad l (1 / (e : ℝ)) ^ (d + e)
    rw [htop]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show e ≤ n by omega)
    exact (hhigh k).trans_lt (max_lt (mul_lt_mul_of_pos_left (H.2 k (by omega)) hl)
      (mul_lt_mul_of_pos_left (H.2 (k + e) (by omega)) hl))

theorem lastMax_E_pow_mul {h : K⟦X⟧} {d : ℕ}
    (H : LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d) (m : ℕ) :
    LastMax (fun n => ‖coeff n (E K l e ^ m * h)‖ * rad l (1 / e) ^ n) (d + m * e) := by
  induction m with
  | zero => simpa using H
  | succ m ih =>
    have h' := lastMax_E_mul l e ih
    rw [← mul_assoc, ← pow_succ'] at h'
    have hidx : d + (m + 1) * e = d + m * e + e := by ring
    rw [hidx]
    exact h'

theorem exists_lastMax_of_mem {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {h : K⟦X⟧}
    (hh : h ∈ Rpi O K l e) (h0 : h ≠ 0) :
    ∃ d, LastMax (fun n => ‖coeff n h‖ * rad l (1 / e) ^ n) d := by
  have hmem : Tendsto (fun n => ‖coeff n h‖ * rad l (1 / (e : ℝ)) ^ n) atTop (𝓝 0) :=
    mem_R.mp (show h ∈ R O K l (1 / (e : ℝ)) from hh)
  obtain ⟨n₀, hn₀⟩ : ∃ n, coeff n h ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (PowerSeries.ext fun n => by simpa using hc n)
  exact exists_lastMax hmem (mul_pos (norm_pos_iff.mpr hn₀) (pow_pos (rad_pos l _) n₀))

end GlobalTheory.BK.HatInj

namespace GlobalTheory.BK


open HatInj in
theorem toHat_injective (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Function.Injective (toHat O K l e) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hdiv : ∀ m : ℕ, ∃ y : Rpi O K l e, (x : K⟦X⟧) = E K l e ^ m * y := by
    intro m
    have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {EIn l e (invL l (A O K))}) m) hx
    unfold toHat at h1
    generalize_proofs p1 p2 p3 p4 p5 p6 p7 at h1
    unfold SameJets.toCompl SameJets.jet at h1
    erw [AdicCompletion.evalₐ_liftRingHom, map_zero, RingHom.comp_apply] at h1
    have h2 := (map_eq_zero_iff _ (RingEquiv.injective _)).mp h1
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
    obtain ⟨y, hy⟩ := h2
    refine ⟨y, ?_⟩
    rw [← hy]
    simp [mul_comm]
  by_contra hx0
  have hx0' : (x : K⟦X⟧) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨d, hd⟩ := exists_lastMax_of_mem (l := l) (e := e) x.2 hx0'
  obtain ⟨y, hy⟩ := hdiv (d + 1)
  have hy0 : (y : K⟦X⟧) ≠ 0 := by
    intro h
    apply hx0'
    rw [hy, h, mul_zero]
  obtain ⟨d', hd'⟩ := exists_lastMax_of_mem (l := l) (e := e) y.2 hy0
  have h3 := lastMax_E_pow_mul (l := l) (e := e) hd' (d + 1)
  rw [← hy] at h3
  have h4 := hd.unique h3
  have he : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (NeZero.ne e)
  have h5 : d + 1 ≤ (d + 1) * e := Nat.le_mul_of_pos_right _ he
  omega

end GlobalTheory.BK
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def homSpace : Submodule ℂ (Y →ₗ[ℂ] X) where
  carrier := {φ | ∀ h v, φ (ρ h v) = τ (1, h) (φ v)}
  add_mem' := by
    intro a b ha hb h v
    simp [ha h v, hb h v]
  zero_mem' := by intro h v; simp
  smul_mem' := by
    intro c a ha h v
    simp [ha h v]

theorem commute_apply (g : G) (h : H) (x : X) : τ (g, 1) (τ (1, h) x) = τ (1, h) (τ (g, 1) x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem apply_pair (g : G) (h : H) (x : X) : τ (g, h) x = τ (g, 1) (τ (1, h) x) := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

def homRep : Representation ℂ G (homSpace τ ρ) where
  toFun g :=
    { toFun := fun φ => ⟨(τ (g, 1)).comp φ.1, fun h v => by
        simp only [LinearMap.comp_apply]
        rw [φ.2 h v, commute_apply]⟩
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by
    ext φ v
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    simp [this]
  map_mul' a b := by
    ext φ v
    have : ((a * b, (1 : H)) : G × H) = (a, 1) * (b, 1) := by simp
    show τ (a * b, 1) _ = τ (a, 1) (τ (b, 1) _)
    rw [this, map_mul, Module.End.mul_apply]

@[simp] theorem homRep_apply_coe (g : G) (φ : homSpace τ ρ) :
    ((homRep τ ρ g φ : homSpace τ ρ) : Y →ₗ[ℂ] X) = (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) := rfl

def evMap : (extTensor (homRep τ ρ) ρ).IntertwiningMap τ where
  toLinearMap := TensorProduct.lift (homSpace τ ρ).subtype
  isIntertwining' gh := by
    apply TensorProduct.ext'
    intro φ v
    obtain ⟨g, h⟩ := gh
    simp only [LinearMap.comp_apply, extTensor_tmul, TensorProduct.lift.tmul, Submodule.subtype_apply,
      homRep_apply_coe]
    rw [φ.2 h v, ← apply_pair]

end GlobalTheory.TensorFactor

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def diffMap (g : G) (φ : homSpace τ ρ) :
    ρ.IntertwiningMap (τ.comp (MonoidHom.inr G H)) where
  toLinearMap := (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) - (φ : Y →ₗ[ℂ] X)
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.inr_apply, map_sub]
    rw [φ.2 h v, commute_apply]

theorem homRep_eq_of_apply_eq [ρ.IsIrreducible] {g : G} {φ : homSpace τ ρ} {y : Y} (hy : y ≠ 0)
    (h : τ (g, 1) ((φ : Y →ₗ[ℂ] X) y) = (φ : Y →ₗ[ℂ] X) y) : homRep τ ρ g φ = φ := by
  rcases Representation.IsIrreducible.injective_or_eq_zero (diffMap τ ρ g φ) with hi | h0
  · refine absurd (hi (a₁ := y) (a₂ := 0) ?_) hy
    simp [diffMap, h]
  · apply Subtype.ext
    ext v
    have := congrArg (fun f => f v) h0
    simpa [diffMap, sub_eq_zero] using this

end GlobalTheory.TensorFactor


open GlobalTheory.TensorFactor in
theorem GlobalTheory.TensorFactor.exists_equiv_extTensor : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  intro G H X Y _ _ _ _ _ _ _ _ _ _ τ ρ hτs hτ hρ hinj hex
  obtain ⟨ι, hι0, hι⟩ := hex
  haveI := hτ
  haveI := hρ
  have hev : Function.Injective (evMap τ ρ) := hinj (homSpace τ ρ) fun φ hφ => hφ
  let ι' : homSpace τ ρ := ⟨ι, hι⟩
  obtain ⟨y0, hy0⟩ : ∃ v, ι v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hι0 (LinearMap.ext h)
  have hy0' : y0 ≠ 0 := fun h => hy0 (by simp [h])
  have hsurj : Function.Surjective (evMap τ ρ) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (evMap τ ρ)).resolve_right fun h0 =>
      hy0 (by simpa [evMap, ι'] using congrArg (fun f => f (ι' ⊗ₜ y0)) h0)
  refine ⟨homSpace τ ρ, inferInstance, inferInstance, homRep τ ρ, ?_, ?_,
    ⟨(Representation.IntertwiningMap.ofBijective (evMap τ ρ) ⟨hev, hsurj⟩).symm⟩⟩
  · refine isSmooth_of_nhds fun φ => ?_
    have hc : Continuous fun g : G => ((g, (1 : H)) : G × H) := by fun_prop
    refine Filter.mem_of_superset (((hτs ((φ : Y →ₗ[ℂ] X) y0)).preimage hc).mem_nhds ?_)
      fun g hg => homRep_eq_of_apply_eq τ ρ hy0' hg
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    show τ ((1 : G), (1 : H)) _ = _
    simp [this]
  · haveI : Nontrivial (Subrepresentation (homRep τ ρ)) := ⟨⊥, ⊤, fun h => by
      have h1 : ι' ∈ (⊤ : Subrepresentation (homRep τ ρ)).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      have h2 : ι' = 0 := (Submodule.mem_bot ℂ).1 h1
      exact hι0 (congrArg Subtype.val h2)⟩
    refine ⟨fun S => ?_⟩
    let U : Subrepresentation τ :=
      { toSubmodule :=
          LinearMap.range ((evMap τ ρ).toLinearMap ∘ₗ LinearMap.rTensor Y S.toSubmodule.subtype)
        apply_mem_toSubmodule := by
          rintro ⟨g, h⟩ _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul ψ z =>
            refine ⟨⟨homRep τ ρ g ψ, S.apply_mem_toSubmodule g ψ.2⟩ ⊗ₜ ρ h z, ?_⟩
            show ((homRep τ ρ g ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) (ρ h z) =
              τ (g, h) (((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z)
            rw [homRep_apply_coe, LinearMap.comp_apply, (ψ : homSpace τ ρ).2 h z, ← apply_pair]
          | add a b ha hb =>
            rw [map_add (f := _), map_add (f := _)]
            exact add_mem ha hb }
    rcases IsSimpleOrder.eq_bot_or_eq_top U with hU | hU
    · left
      apply Subrepresentation.toSubmodule_injective
      refine eq_bot_iff.2 fun ψ hψ => (Submodule.mem_bot ℂ).2 (Subtype.ext (LinearMap.ext fun z => ?_))
      have hm : (evMap τ ρ).toLinearMap (LinearMap.rTensor Y S.toSubmodule.subtype (⟨ψ, hψ⟩ ⊗ₜ z)) ∈
          U.toSubmodule := ⟨⟨ψ, hψ⟩ ⊗ₜ z, rfl⟩
      rw [hU] at hm
      have h2 := (Submodule.mem_bot ℂ).1 hm
      have h3 : ((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z = 0 := by simpa [evMap] using h2
      simpa using h3
    · right
      apply Subrepresentation.toSubmodule_injective
      refine eq_top_iff.2 fun φ _ => ?_
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy0'
      let P : homSpace τ ρ ⊗[ℂ] Y →ₗ[ℂ] homSpace τ ρ :=
        (TensorProduct.rid ℂ (homSpace τ ρ)).toLinearMap ∘ₗ LinearMap.lTensor (homSpace τ ρ) l
      have hP : ∀ t, P (LinearMap.rTensor Y S.toSubmodule.subtype t) ∈ S.toSubmodule := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul ψ z => simpa [P] using S.toSubmodule.smul_mem (l z) ψ.2
        | add a b ha hb =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem ha hb
      have hmem : evMap τ ρ (φ ⊗ₜ y0) ∈ U.toSubmodule := by
        rw [hU]
        exact Submodule.mem_top
      obtain ⟨t, ht⟩ := hmem
      have ht' : LinearMap.rTensor Y S.toSubmodule.subtype t = φ ⊗ₜ y0 :=
        hev (a₁ := LinearMap.rTensor Y S.toSubmodule.subtype t) (a₂ := φ ⊗ₜ y0) ht
      have := hP t
      rw [ht'] at this
      simpa [P, hl] using this
end
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant : ∀ {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    (∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) →
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  first | exact @GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | exact GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | (intros; apply GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant <;> assumption)
end
