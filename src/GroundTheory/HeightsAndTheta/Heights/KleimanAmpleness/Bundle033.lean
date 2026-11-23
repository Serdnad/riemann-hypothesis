module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionLocal
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionPowers
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace VeryAmpleZTwist

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]

theorem chart_smul_eq {I : Chart x} (c : chartRing S x I) (z : E) : c • z = (c : Ω) • z := rfl

theorem smul_mem_twist_twist (G : SubSystem S x E) (P Q : SubSystem S x Ω) (I : Chart x) {q : Ω}
    (hq : q ∈ P.sub I) {z : E} (hz : z ∈ (G.twist Q).sub I) : q • z ∈ ((G.twist P).twist Q).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => q • z ∈ ((G.twist P).twist Q).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q', hq', y, hy, rfl⟩
    refine Submodule.subset_span ⟨q', hq', q • y, Submodule.subset_span ⟨q, hq, y, hy, rfl⟩, ?_⟩
    rw [smul_smul, smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b c _ _ hb hc; rw [smul_add]; exact Submodule.add_mem _ hb hc
  · intro c z _ hz
    rw [chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]
    exact Submodule.smul_mem _ c hz

theorem smul_mem_twist_pow (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {w : Ω}
    (hw : w ∈ (H.pow c).sub I) {z : E} (hz : z ∈ (G.twist (H.pow d)).sub I) :
    w • z ∈ (G.twist (H.pow (d + c))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => w • z ∈ (G.twist (H.pow (d + c))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq c hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
  · intro c' z _ hz
    rw [chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]
    exact Submodule.smul_mem _ c' hz

theorem mem_twist_pow_add (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    (hz : z ∈ ((G.twist (H.pow a)).twist (H.pow b)).sub I) : z ∈ (G.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => z ∈ (G.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    exact smul_mem_twist_pow G H I hq hy
  · exact Submodule.zero_mem _
  · intro b e _ _ hb he; exact Submodule.add_mem _ hb he
  · intro c z _ hz; exact Submodule.smul_mem _ c hz

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.sub I) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span ⟨h l, hh l, _, ih, rfl⟩

theorem proof (hFam : VeryAmpleZFamily.Statement.{u, v, w}) : VeryAmpleZTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hH a J
  obtain ⟨F', hF'⟩ := hFam S Ω N x E F H r h hH
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hmem : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hH.mem_secs l) I
  have hpow : ∀ I, h j ^ a ∈ (H.pow a).sub I := fun I => by
    have h1 : h j ∈ (H.pow 1).sub I := by rw [SubSystem.pow_sub, pow_one]; exact hmem j I
    simpa using AmpleTwistLocal.pow_mem_pow H.toSubSystem I h1 a

  have fwd : ∀ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J,
      h j ^ a • y ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J := by
    intro y hy
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have hyI : y ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J := (Submodule.mem_iInf _).mp hy I
    refine Submodule.span_induction (p := fun y _ =>
      h j ^ a • y ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J) ?_ ?_ ?_ ?_ hyI
    · rintro y ⟨n, hn⟩
      refine Submodule.subset_span ⟨n, ?_⟩
      rw [smul_smul, mul_comm (xProd J ^ n), ← smul_smul]
      exact smul_mem_twist_twist _ _ _ I (hpow I) hn
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he

  have bwd : ∀ e ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J,
      (h j ^ a)⁻¹ • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    classical
    intro e he
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have heI : e ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J := (Submodule.mem_iInf _).mp he I
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hua : u ^ a ∈ (H.pow ((J.1.erase j).card * a)).sub I :=
      AmpleTwistLocal.pow_mem_pow H.toSubSystem I (prod_mem_pow H.toSubSystem I (fun l => hmem l I) _) a
    refine Submodule.span_induction (p := fun e _ =>
      (h j ^ a)⁻¹ • e ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ heI
    · rintro e ⟨n, hn⟩
      refine Submodule.subset_span ⟨n + a, ?_⟩
      have heq : xProd J ^ (n + a) • (h j ^ a)⁻¹ • e = u ^ a • (xProd J ^ n • e) := by
        rw [smul_smul, smul_smul, hxu]
        congr 1
        field_simp
        ring
      have hdeg : a + J.1.card * n + (J.1.erase j).card * a = J.1.card * (n + a) := by
        rw [hk]; ring
      rw [heq, ← hdeg]
      exact smul_mem_twist_pow _ _ I hua (mem_twist_pow_add _ _ I hn)
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
    · intro s e _ he; rw [smul_comm]; exact Submodule.smul_mem _ s he
  have hq : h j ^ a ∈ twistMod S h (a : ℤ) J := by
    rw [twistMod_eq_span (a : ℤ) J hj, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    suffices H1 : ∀ c : chartRing S h J, c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J by
      simpa using H1 1
    refine Submodule.span_induction (p := fun z _ => ∀ c : chartRing S h J,
      c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, y, hy, rfl⟩ c
      rw [twistMod_eq_span (a : ℤ) J hj, Submodule.mem_span_singleton] at hq
      obtain ⟨d, rfl⟩ := hq
      have hy' : y ∈ F'.sub J := by
        have : y ∈ (F'.sub J).restrictScalars S := by rw [hF' J]; exact hy
        exact this
      have hcd : (c * d) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
        rw [← hF' J]; exact Submodule.smul_mem _ (c * d) hy'
      have heq : c • ((d • h j ^ (a : ℤ)) • y) = h j ^ a • ((c * d) • y) := by
        rw [chart_smul_eq, chart_smul_eq, smul_eq_mul, zpow_natCast, smul_smul, chart_smul_eq (c * d),
          smul_smul]
        congr 1
        push_cast
        ring
      rw [heq]
      exact fwd _ hcd
    · intro c; rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he c; rw [smul_add]; exact Submodule.add_mem _ (hb c) (he c)
    · intro c' e _ he c; rw [smul_smul]; exact he (c * c')
  · intro e he
    have heq : e = h j ^ a • ((h j ^ a)⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hj0), one_smul]
    rw [Submodule.restrictScalars_mem, heq]
    exact Submodule.subset_span ⟨h j ^ a, by exact_mod_cast hq, _, bwd e he, rfl⟩

end VeryAmpleZTwist

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def redSys (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : SubSystem k y K' where
  sub I := Submodule.span (chartRing k y I)
    ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy I))
  mono I J h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing k y J)
      ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy J))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨q, P.mono _ _ h q hq, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz

def RedGood (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : Prop :=
  ∀ (I : Chart y), ∀ q ∈ P.sub (liftChart hxy I), q / γ ∈ locAt k x y

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem mem_redSys_iff {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (I : Chart y) (z : K') :
    z ∈ (redSys hxy P γ).sub I ↔ ∃ q ∈ P.sub (liftChart hxy I), redAt k x y (q / γ) = z := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ q ∈ P.sub (liftChart hxy I),
      redAt k x y (q / γ) = z) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · exact ⟨0, Submodule.zero_mem _, by rw [zero_div]; exact (locAt_zero hsp).2⟩
    · rintro u v _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
      refine ⟨q + q', Submodule.add_mem _ hq hq', ?_⟩
      rw [add_div]; exact (locAt_add hsp (hP I q hq) (hP I q' hq')).2
    · rintro c u _ ⟨q, hq, rfl⟩
      obtain ⟨a, ha, hac⟩ := exists_redAt_eq (k := k) (x := x) (y := y) hsp hxy I c.2
      refine ⟨a * q, ?_, ?_⟩
      · have := Submodule.smul_mem _ (⟨a, ha⟩ : chartRing k x (liftChart hxy I)) hq
        rwa [chartRing_smul_def] at this
      · rw [chartRing_smul_def, ← hac, mul_div_assoc]
        exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I ha).1 (hP I q hq)).2
  · rintro ⟨q, hq, rfl⟩; exact Submodule.subset_span ⟨q, hq, rfl⟩

theorem redGood_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) : RedGood hxy (P.twist Q) (γ * δ) := by
  intro I z hz
  refine Submodule.span_induction (p := fun z _ => z / (γ * δ) ∈ locAt k x y) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, p, hp, rfl⟩
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    rw [this]; exact (locAt_mul hsp (hQ I q hq) (hP I p hp)).1
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1

theorem redSys_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) :
    redSys hxy (P.twist Q) (γ * δ) = (redSys hxy P γ).twist (redSys hxy Q δ) := by
  have hPQ := redGood_twist hsp hxy hP hQ
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    refine Submodule.span_induction (p := fun z _ => redAt k x y (z / (γ * δ)) ∈
      ((redSys hxy P γ).twist (redSys hxy Q δ)).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, p, hp, rfl⟩
      have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
      rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨q, hq, rfl⟩, _,
        Submodule.subset_span ⟨p, hp, rfl⟩, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hPQ I u hu) (hPQ I v hv)).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hPQ I u hu)).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q', hq', p', hp', rfl⟩
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hQ I q').mp hq'
    obtain ⟨p, hp, rfl⟩ := (mem_redSys_iff hsp hxy hP I p').mp hp'
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    refine Submodule.subset_span ⟨q • p, Submodule.subset_span ⟨q, hq, p, hp, rfl⟩, ?_⟩
    change redAt k x y (q • p / (γ * δ)) = redAt k x y (q / δ) * redAt k x y (p / γ)
    rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]

theorem redGood_twistSys_zero : RedGood hxy (twistSys k x 0) 1 := by
  intro I q hq
  rw [div_one]; exact (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).1

theorem redSys_twistSys_zero : redSys hxy (twistSys k x 0) 1 = twistSys k y 0 := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    change redAt k x y (q / 1) ∈ twistMod k y 0 I
    rw [div_one]
    exact res_mem_twistMod_zero_of_mem_chartRing
      (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_redAt_eq (k := k) (x := x) (y := y) hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hz)
    exact Submodule.subset_span ⟨a, res_mem_twistMod_zero_of_mem_chartRing ha, by
      change redAt k x y (a / 1) = redAt k x y a
      rw [div_one]⟩

theorem redSys_pow {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (n : ℕ) :
    RedGood hxy (P.pow n) (γ ^ n) ∧ redSys hxy (P.pow n) (γ ^ n) = (redSys hxy P γ).pow n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨redGood_twistSys_zero hsp hxy, redSys_twistSys_zero hsp hxy⟩
  | succ n ih =>
    rw [pow_succ]
    change RedGood hxy ((P.pow n).twist P) (γ ^ n * γ) ∧
      redSys hxy ((P.pow n).twist P) (γ ^ n * γ) = ((redSys hxy P γ).pow n).twist (redSys hxy P γ)
    exact ⟨redGood_twist hsp hxy ih.1 hP, by rw [redSys_twist hsp hxy ih.1 hP, ih.2]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

theorem QuotSectionsFinite.proof (hE : Extension.Statement.{u, w, w})
    (hI : IdealTwistFamily.Statement.{u, w}) (hT : TildeFinite.Statement.{u, w})
    (hQ : QuotientH0Finite.Statement.{u, w, w}) : QuotSectionsFinite.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q J

  let J' : Ideal (Poly k N) := Ideal.span {f | f ∈ J ∧ ∃ e, f.IsHomogeneous e}
  have hJ'hom : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J' := by
    have h : J'.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
      Ideal.homogeneous_span _ _ fun f hf =>
        ⟨_, (mem_homogeneousSubmodule _ f).mpr hf.2.choose_spec⟩
    exact fun p hp d => homogeneousComponent_mem_of_mem h hp d
  have hforms : ∀ (f : Poly k N) (e : ℕ), f.IsHomogeneous e → (f ∈ J ↔ f ∈ J') := fun f e hf =>
    ⟨fun h => Ideal.subset_span ⟨h, e, hf⟩, fun h => (show J' ≤ J from Ideal.span_le.mpr (by
      intro g hg
      exact hg.1)) h⟩
  have hsys : idealSys x J = idealSys x J' := SubSystem.ext_sub fun I => by
    change idealMod J I = idealMod J' I
    unfold idealMod
    congr 1
    ext a
    constructor <;> rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mp hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mpr hf, hs, hfe, hse, rfl⟩

  obtain ⟨F, hF, hFfg⟩ := hI k Ω N x Q J' hJ'hom
  obtain ⟨M, -, hM⟩ := hE k Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨M', -, hM'⟩ := hE k Ω N x Ω F hFfg
  have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
  have h1 : M'.tildeSys 0 = Q.toSubSystem.twist (idealSys x J) := by
    rw [hsys, ← hF]
    exact SubSystem.ext_sub hM'

  have hle : ∀ I, (Q.toSubSystem.twist (idealSys x J)).sub I ≤ Q.toSubSystem.sub I := by
    intro I
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.span_induction (p := fun q _ => q • y ∈ Q.sub I) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨f, s, e, _, hs, hf, hse, rfl⟩
      exact (Q.sub I).smul_mem ⟨_, ⟨f, s, e, hs, hf, hse, rfl⟩⟩ hy
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq'; rw [smul_assoc]; exact Submodule.smul_mem _ a hq'
  have hH0 : Module.Finite k (Q.toSubSystem.H 0) := by
    rw [← h0]; exact hT k Ω N x M 0 0
  have hH1 : Module.Finite k ((Q.toSubSystem.twist (idealSys x J)).H 1) := by
    rw [← h1]; exact hT k Ω N x M' 1 0
  exact hQ k Ω N x Ω Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) hle hH0 hH1

end

end GroundTheory.Heights₂.Heights.Kleiman
end
