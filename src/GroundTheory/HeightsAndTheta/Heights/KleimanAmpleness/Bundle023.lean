module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.OnW.Lift.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ s : Chart x → Ω,
      (∀ I, s I ∈ ((T.L.pow b).twist (twistSys k x c)).sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I₂) →
      ∃ t ∈ ((T.L.pow b).twist (twistSys k x c)).secs, ∀ I, t - s I ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace VeryAmpleSecs

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]

theorem mem_secs_pow_twistSys_one_iff {r : ℕ} (h : Fin (r + 1) → Ω) (n : ℕ) (s : Ω) :
    s ∈ ((twistSys k h 1).pow n).secs ↔ ∀ j, h j ≠ 0 → s / h j ^ n ∈ ampleBase (S := k) h j := by
  constructor
  · intro hs j hj
    have hsj := (Submodule.mem_iInf _).mp hs (singleChart hj)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hsj)
    rw [chartRing_smul_def] at hb
    rw [← hb, mul_div_cancel_right₀ _ (pow_ne_zero n hj)]
    exact mem_ampleBase_of_mem_chartRing hj b.2
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hhi : h i ≠ 0 := (mem_support h).mp (I.2.2 hi)
    have hbase : ampleBase (S := k) h i ≤ chartRing k h (singleChart hhi) := by
      rw [ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      exact (ratio (S := k) hhi l).2
    have hmem : s / h i ^ n ∈ chartRing k h I :=
      chartRing_mono (Finset.singleton_subset_iff.mpr hi) (hbase (H i hhi))
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    have hs : s = (⟨s / h i ^ n, hmem⟩ : chartRing k h I) • h i ^ n := by
      rw [chartRing_smul_def, div_mul_cancel₀ _ (pow_ne_zero n hhi)]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ (mem_twistMod_one I i) n)

theorem mem_pow_of_pow_mul_mem {A : Type*} [CommRing A] [Algebra A Ω] {L Q : Submodule A Ω}
    (hLQ : L * Q = 1) {r : ℕ} {h : Fin (r + 1) → Ω} (hL : Submodule.span A (Set.range h) = L)
    {s : Ω} {n : ℕ} (hs : ∀ j, ∃ e, h j ^ e * s ∈ L ^ (n + e)) : s ∈ L ^ n := by
  set C : Ideal A := (L ^ n).colon {s}
  have key : ∀ j, ∀ q ∈ Q, ∀ a : A, algebraMap A Ω a = h j * q → a ∈ C.radical := by
    intro j q hq a ha
    obtain ⟨e, he⟩ := hs j
    refine ⟨e, ?_⟩
    rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha]
    have hm := Submodule.mul_mem_mul (Submodule.pow_mem_pow Q hq e) he
    have hQL : Q ^ e * L ^ (n + e) = L ^ n := by
      calc Q ^ e * L ^ (n + e) = L ^ n * (L * Q) ^ e := by ring
        _ = L ^ n := by rw [hLQ, one_pow, mul_one]
    rw [hQL] at hm
    convert hm using 1
    ring
  have h1 : (1 : Submodule A Ω) ≤ Submodule.map (Algebra.linearMap A Ω) (C.radical : Submodule A A) := by
    rw [← hLQ, ← hL, ← Submodule.span_eq Q, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, q, hq, rfl⟩
    have hjq : h j * q ∈ L * Q := Submodule.mul_mem_mul (hL ▸ Submodule.subset_span ⟨j, rfl⟩) hq
    rw [hLQ, Submodule.mem_one] at hjq
    obtain ⟨a, ha⟩ := hjq
    exact ⟨a, key j q hq a ha, ha⟩
  obtain ⟨a, ⟨m, hm⟩, ha1⟩ := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have ha1' : algebraMap A Ω a = 1 := ha1
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha1', one_pow, one_mul] at hm
  exact hm

theorem exists_pow_mul_mem_pow {A : Subalgebra k Ω} {L : Submodule A Ω} {r : ℕ}
    {h : Fin (r + 1) → Ω} (hL : ∀ l, h l ∈ L) {j : Fin (r + 1)} (hj : h j ≠ 0) {t : Ω}
    (ht : t ∈ ampleBase (S := k) h j) : ∃ e, h j ^ e * t ∈ L ^ e := by
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨l, rfl⟩ := ht
    exact ⟨1, by rw [pow_one, pow_one, mul_div_cancel₀ _ hj]; exact hL l⟩
  | algebraMap c =>
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_zero, one_mul, Submodule.mem_one]
    exact ⟨⟨_, Subalgebra.algebraMap_mem A c⟩, rfl⟩
  | add t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ + t₂) = h j ^ e₂ * (h j ^ e₁ * t₁) + h j ^ e₁ * (h j ^ e₂ * t₂) := by
      ring
    rw [hs, pow_add]
    exact Submodule.add_mem _
      (by rw [mul_comm (L ^ e₁)]; exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₁)
      (Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₂)
  | mul t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ * t₂) = (h j ^ e₁ * t₁) * (h j ^ e₂ * t₂) := by ring
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul he₁ he₂

end VeryAmpleSecs


open VeryAmpleSecs in
theorem VeryAmpleSecs.proof : VeryAmpleSecs.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hv n
  ext s
  rw [mem_secs_pow_twistSys_one_iff]
  have hL : ∀ I l, h l ∈ Nb.sub I := fun I l => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  constructor
  · intro hs j hj
    refine hv.closed j hj (Set.mem_iInter.mpr fun I => ⟨n, ?_⟩)
    rw [div_mul_cancel₀ _ (pow_ne_zero n hj), one_mul]
    exact (Submodule.mem_iInf _).mp hs I
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    obtain ⟨Q, hQ⟩ := Nb.invertible I
    refine mem_pow_of_pow_mul_mem hQ (hv.generates I) fun j => ?_
    by_cases hj : h j = 0
    · exact ⟨1, by rw [hj, pow_one, zero_mul]; exact Submodule.zero_mem _⟩
    obtain ⟨e, he⟩ := exists_pow_mul_mem_pow (hL I) hj (H j hj)
    refine ⟨e, ?_⟩
    have hs : h j ^ e * s = h j ^ n * (h j ^ e * (s / h j ^ n)) := by
      field_simp
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL I j) n) he

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem VeryAmpleProductPos.proof (hR : GenericPointSectionInput.Statement.{u, w}) (hP : PointDegreePos.Statement.{u, w})
    (hC : CutComponent.Statement.{u, w}) (hM : CutMultPos.Statement.{u}) :
    VeryAmpleProductPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x e
  induction e with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact_mod_cast hP k Ω N x pp hW
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    obtain ⟨q₀, hq₀, hq₀W⟩ := hC k Ω N x n pp (L (Fin.last n)) s hW (hL _) hs hsI

    have hterm : ∀ qq (h : qq ∈ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s).minimalPrimes),
        IsSubvar x qq n → haveI : qq.IsPrime := h.1.1
        0 < (((cutMult (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s) qq).toNat : ℤ) *
          interNum qq (fun i => (L (Fin.castSucc i)).toSubSystem)) := by
      intro qq h hqW
      have hm := hM k N _ qq h
      exact mul_pos (by exact_mod_cast ENat.toNat_pos hm.1.ne' hm.2.ne) (ih qq _ hqW fun i => hL _)
    refine lt_of_lt_of_le ?_ (single_le_finsum q₀ ?_ ?_)
    · rw [dite_eq_left ⟨hq₀, hq₀W⟩]
      exact hterm q₀ hq₀ hq₀W
    · refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
        (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s)).subset fun qq hqq => ?_
      by_contra hn
      exact hqq (dif_neg fun h => hn h.1)
    · intro qq
      split_ifs with h
      · exact (hterm qq h.1 h.2).le
      · exact le_rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem exists_pos_of_eventually_lower {d : ℕ} {A : ℤ} (hA : 0 < A) {C : ℝ} {f : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (A : ℝ) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n)
    (D : ℕ) (hD : 0 < D) : ∃ n₁ : ℕ, 0 < n₁ ∧ 0 < f (D * n₁) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  obtain ⟨K, hK⟩ := exists_nat_gt (C * ((d + 1).factorial : ℝ) / A)
  refine ⟨n₀ + K + 1, by omega, ?_⟩
  have hle : n₀ + K + 1 ≤ D * (n₀ + K + 1) := Nat.le_mul_of_pos_left _ hD
  refine lt_of_lt_of_le ?_ (hn₀ _ (le_trans (by omega) hle))
  have hnK : (K : ℝ) < ((D * (n₀ + K + 1) : ℕ) : ℝ) := by
    have : K < D * (n₀ + K + 1) := lt_of_lt_of_le (by omega) hle
    exact_mod_cast this
  generalize ((D * (n₀ + K + 1) : ℕ) : ℝ) = n at hnK ⊢
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hF : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg K) hnK
  have h1 : C * ((d + 1).factorial : ℝ) < A * n := by
    have := lt_trans hK hnK
    rwa [div_lt_iff₀ hA', mul_comm n] at this
  have h2 : C < A * n / ((d + 1).factorial : ℝ) := by rw [lt_div_iff₀ hF]; exact h1
  have h3 : (A : ℝ) * n ^ (d + 1) / ((d + 1).factorial : ℝ) - C * n ^ d =
      n ^ d * (A * n / ((d + 1).factorial : ℝ) - C) := by ring
  rw [h3]
  exact mul_pos (pow_pos hnpos d) (by linarith)

theorem sectionExists_of_gap (hcount : SectionCount.Statement.{u, w})
    (hlead : LeadingCoeffPos.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {d : ℕ} {M : LineBundle k x} {t s' : ℚ}
    (hZ : IsSubvar x (primeOf (S := k) x) (d + 1)) (hM : Nef M.toSubSystem) (hs' : 0 < s')
    {Q : ℕ} {mQ : ℤ} (hQ : 0 < Q) (hmQ : (mQ : ℚ) = Q * t)
    (hva : IsVeryAmple (twistMul M.toSubSystem Q mQ))
    (hgap : 1 < (Q : ℚ) * (t / (d + 1) - s')) :
    ∃ (p : ℕ) (m c₁ : ℤ), 1 ≤ p ∧ (m : ℚ) = p * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ (twistMul M.toSubSystem p (m - c₁)).secs, σ ≠ 0 := by
  obtain ⟨Nb, hNb⟩ := exists_lineBundle_twistMul M Q mQ
  have hvaN : IsVeryAmple Nb.toSubSystem := hNb ▸ hva

  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = ⌊(Q : ℚ) * s'⌋₊ + 1 := ⟨_, rfl⟩
  have hQs'0 : 0 ≤ (Q : ℚ) * s' := by positivity
  have hb_gt : (Q : ℚ) * s' < b := by rw [hb]; push_cast; exact Nat.lt_floor_add_one _
  have hb_le : (b : ℚ) ≤ Q * s' + 1 := by rw [hb]; push_cast; linarith [Nat.floor_le hQs'0]
  have hd0 : (d : ℚ) + 1 ≠ 0 := by positivity
  have hd : (0 : ℚ) < d + 1 := by positivity
  have hbT : (b : ℚ) < Q * (t / (d + 1)) := by
    have := hgap
    rw [mul_sub] at this
    linarith
  have hbm : ((d + 1 : ℕ) : ℤ) * b < mQ := by
    have h1 : ((d : ℚ) + 1) * b < (d + 1) * (Q * (t / (d + 1))) := mul_lt_mul_of_pos_left hbT hd
    have h2 : ((d : ℚ) + 1) * (Q * (t / (d + 1))) = Q * t := by field_simp
    have h3 : ((((d + 1 : ℕ) : ℤ) * b : ℤ) : ℚ) < (mQ : ℚ) := by
      push_cast
      rw [hmQ]
      linarith
    exact_mod_cast h3
  have hb1 : 1 ≤ b := by omega
  obtain ⟨C, hC⟩ := hcount k Ω N x d Nb b hZ hvaN hb1
  have hcoef := hlead k Ω N x d M Nb Q mQ b hZ hM hNb hvaN hbm

  have hden := Rat.mul_den_eq_num ((Q : ℚ) * s')
  have hD1 : 0 < ((Q : ℚ) * s').den := Rat.den_pos _
  generalize ((Q : ℚ) * s').den = D at hden hD1
  generalize ((Q : ℚ) * s').num = E at hden
  obtain ⟨n₁, hn₁, hpos⟩ := exists_pos_of_eventually_lower hcoef hC D hD1
  have hne : (twistMul Nb.toSubSystem (D * n₁) (-(((D * n₁ : ℕ) : ℤ) * b))).secs ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    simp at hpos
  obtain ⟨σ, hσ, hσne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [hNb, twistMul_twistMul] at hσ
  refine ⟨D * n₁ * Q, ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E, ((D * n₁ : ℕ) : ℤ) * b - n₁ * E,
    Nat.mul_pos (Nat.mul_pos hD1 hn₁) hQ, ?_, ?_, σ, ?_, hσne⟩
  · push_cast
    rw [hmQ, ← hden]
    ring
  · have hDn : (0 : ℚ) < (D : ℚ) * n₁ := by positivity
    have hpos' : (0 : ℚ) < ((((D * n₁ : ℕ) : ℤ) * b - n₁ * E : ℤ) : ℚ) := by
      push_cast
      rw [← hden]
      have key : (D : ℚ) * n₁ * (b - Q * s') = D * n₁ * b - n₁ * (Q * s' * D) := by ring
      have := mul_pos hDn (sub_pos.mpr hb_gt)
      linarith
    have : (0 : ℤ) < ((D * n₁ : ℕ) : ℤ) * b - n₁ * E := by exact_mod_cast hpos'
    omega
  · have hm : ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E - (((D * n₁ : ℕ) : ℤ) * b - n₁ * E) =
        ((D * n₁ : ℕ) : ℤ) * mQ + -(((D * n₁ : ℕ) : ℤ) * b) := by ring
    rw [hm]
    exact hσ

theorem SectionExists.proof (hcount : SectionCount.Statement.{u, w})
    (hpow : VeryAmplePow.Statement.{u, w}) (hlead : LeadingCoeffPos.Statement.{u, w}) :
    SectionExists.Statement.{u, w} := by
  intro k _ Ω _ _ N x d M t s' hZ hM hs' hst hq
  obtain ⟨q, m, hq1, hm, hva⟩ := hq
  have hδ : 0 < t / (d + 1) - s' := by linarith
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq1
  have hqδ := mul_pos hqpos hδ
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (1 / ((q : ℚ) * (t / (d + 1) - s')))
  rw [div_lt_iff₀ hqδ] at hj₀
  have hgap : 1 < (((j₀ + 1) * q : ℕ) : ℚ) * (t / (d + 1) - s') := by
    push_cast
    have : ((j₀ : ℚ) + 1) * q * (t / (d + 1) - s') =
        j₀ * (q * (t / (d + 1) - s')) + q * (t / (d + 1) - s') := by ring
    rw [this]
    linarith
  obtain ⟨Nb0, hNb0⟩ := exists_lineBundle_twistMul M q m
  have hvaQ : IsVeryAmple (twistMul M.toSubSystem ((j₀ + 1) * q) (((j₀ + 1 : ℕ) : ℤ) * m)) := by
    have := hpow k Ω N x Nb0 (j₀ + 1) (by rw [hNb0]; exact hva) (by omega)
    rw [hNb0, pow_twistMul] at this
    exact this
  exact sectionExists_of_gap hcount hlead hZ hM hs' (Nat.mul_pos (Nat.succ_pos _) hq1)
    (by push_cast; rw [hm]; ring) hvaQ hgap

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)

theorem Cdeg_top (i : ℕ) : Cdeg G (fun I => (⊤ : Submodule R (G I))) i = ⊤ := by
  ext s
  simp [Cdeg]

theorem cocyDeg_top (i : ℕ) :
    cocyDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = LinearMap.ker (d G ρ i) := by
  rw [cocyDeg, Cdeg_top, inf_top_eq]

theorem bdryDeg_top (i : ℕ) :
    bdryDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i =>
    change (Cdeg G _ i).map (d G ρ i) = LinearMap.range (d G ρ i)
    rw [Cdeg_top, Submodule.map_top]

def hEquivHdegTop (i : ℕ) : H G ρ i ≃ₗ[R] Hdeg G (fun I => (⊤ : Submodule R (G I))) ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i).symm) (by
    ext z
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    change (z : Cochain G i) ∈ bdry G ρ i ↔ (z : Cochain G i) ∈ bdryDeg G _ ρ i
    rw [bdryDeg_top])

end Cech

theorem CechHdegOfSub.proof : CechHdegOfSub.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ T n
  let φ : ∀ I : Chart x, T.sub I →ₗ[S] E := fun I =>
    { toFun := fun y => (y : E)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (m : T.sub I),
      φ J (T.res I J h m) = Cech.idRes S E (support x) I J h (φ I m) := fun _ _ _ _ => rfl
  have hdeg : ∀ (I : Chart x) (m : T.sub I), m ∈ (⊤ : Submodule S (T.sub I)) →
      φ I m ∈ (T.sub I).restrictScalars S := fun _ m _ => m.2
  have hinj : ∀ I, Function.Injective (φ I) := fun _ => Subtype.val_injective
  have hmap : ∀ I, (⊤ : Submodule S (T.sub I)).map (φ I) = (T.sub I).restrictScalars S := by
    intro I
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro h
      exact ⟨⟨y, h⟩, trivial, rfl⟩
  exact ⟨(Cech.hEquivHdegTop (fun I => T.sub I) T.res n).trans
    (LinearEquiv.ofBijective (Cech.mapHdeg _ _ φ hφ hdeg n)
      (Cech.Transport.proof.{u, v, v} (N + 1) (support x) S (fun I => T.sub I) (fun _ => E) T.res
        (Cech.idRes S E (support x)) _ _ φ hφ hdeg hinj hmap n))⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechDouble.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (N r : ℕ) (x : Fin (N + 1) → Ω) (h : Fin (r + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module S E]
    (A : Chart x → Submodule S E) (B : Chart h → Submodule S E) (M : Chart x → Chart h → Submodule S E),
    (∀ (I I' : Chart x) (J : Chart h), I.1 ⊆ I'.1 → M I J ≤ M I' J) →
    (∀ (I : Chart x) (J J' : Chart h), J.1 ⊆ J'.1 → M I J ≤ M I J') →
    (∀ I, Cech.AugExact S (M I) (A I)) → (∀ J, Cech.AugExact S (fun I => M I J) (B J)) →
    ∀ n : ℕ, Nonempty (Cech.Hdeg (fun _ : Chart x => E) A (Cech.idRes S E (support x)) n ≃ₗ[S]
      Cech.Hdeg (fun _ : Chart h => E) B (Cech.idRes S E (support h)) n)

end

end GroundTheory.Heights₂.Heights.Kleiman
end
