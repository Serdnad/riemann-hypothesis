module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle025
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

open Filter

noncomputable section

universe u v w

namespace VeryAmpleZExtend

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem prod_mem_pow {r : ℕ} (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ H.secs)
    (I : Chart x) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]
      exact (Submodule.restrictScalars_mem _ _ _).mp ((Submodule.mem_iInf _).mp (hh a) I)
    exact AmpleTwistLocal.mul_mem_pow H I ih 1 h1


omit [Module S E] [IsScalarTower S Ω E] in
theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    {w : Ω} (hz : z ∈ (F.twist (H.pow a)).sub I) (hw : w ∈ (H.pow b).sub I) :
    w • z ∈ (F.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => w • z ∈ (F.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq b hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro z z' _ _ hz hz'; rw [smul_add]; exact Submodule.add_mem _ hz hz'
  · intro t z _ hz
    have e : w • (t • z) = t • (w • z) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ t hz


omit [Module S E] [IsScalarTower S Ω E] in
theorem gen_smul {r : ℕ} (F : SubSystem S x E) (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (I : Chart x) (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) {c : Ω} {a : ℕ}
    (hc : c * h j ^ a ∈ (H.pow a).sub I) {y : E}
    (hy : ∃ m : ℕ, xProd J ^ m • y ∈ (F.twist (H.pow (J.1.card * m))).sub I) :
    ∃ m : ℕ, xProd J ^ m • (c • y) ∈ (F.twist (H.pow (J.1.card * m))).sub I := by
  classical
  obtain ⟨m, hm⟩ := hy
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  have hw := AmpleTwistLocal.mul_mem_pow H I hc _
    (AmpleTwistLocal.pow_mem_pow H I (prod_mem_pow H hh I (J.1.erase j)) a)
  refine ⟨m + a, ?_⟩
  have e1 : xProd J ^ (m + a) • (c • y) =
      (c * h j ^ a * (∏ l ∈ J.1.erase j, h l) ^ a) • (xProd J ^ m • y) := by
    rw [smul_smul, smul_smul, hJ]
    congr 1
    ring
  have e2 : J.1.card * (m + a) = J.1.card * m + (a + (J.1.erase j).card * a) := by
    rw [← hcard]; ring
  rw [e1, e2]
  exact smul_mem_twist_pow F H I hm hw

theorem proof : VeryAmpleZExtend.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh J j hj c hc K hK f hf
  classical
  have key : ∀ I : Chart x, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZChart F.toSubSystem H h I J := by
    intro I
    obtain ⟨a, ha⟩ := Set.mem_iInter.mp hc I
    rw [one_mul] at ha
    obtain ⟨e, n, hn⟩ := hK I
    rw [one_mul] at hn
    change c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n ∈ (H.pow n).sub I at hn

    have hfU := F.mono K (AmpleAffineGen.unionChart I K) (AmpleAffineGen.subset_unionChart_right I K) f hf
    obtain ⟨t, ht, htf⟩ := (F.mem_iff I (AmpleAffineGen.unionChart I K)
      (AmpleAffineGen.subset_unionChart_left I K) f).mp hfU
    obtain ⟨v, hv⟩ := ht.exists_left_inv
    obtain ⟨D, hD⟩ := AmpleAffineGen.exists_pow_mul_mem I K v.2
    have hv' : (v : Ω) * (t : Ω) = 1 := congrArg Subtype.val hv
    have hρf : AmpleAffineGen.chartRatio I K ^ D • f ∈ F.sub I := by
      have e1 : AmpleAffineGen.chartRatio I K ^ D • f =
          (⟨_, hD⟩ : chartRing S x I) • ((t : Ω) • f) := by
        rw [Subalgebra.smul_def, smul_smul]
        congr 1
        change _ = AmpleAffineGen.chartRatio I K ^ D * (v : Ω) * (t : Ω)
        rw [mul_assoc, hv', mul_one]
      rw [e1]
      exact Submodule.smul_mem _ _ htf

    have hP := prod_mem_pow H hh I (J.1.erase j)
    have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
    have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
    have hz : (c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
        (AmpleAffineGen.chartRatio I K ^ D • f) ∈ (F.toSubSystem.twist (H.pow (n * D))).sub I :=
      Submodule.subset_span ⟨_, AmpleTwistLocal.pow_mem_pow H I hn D, _, hρf, rfl⟩
    have hz2 := smul_mem_twist_pow F.toSubSystem H I hz
      (AmpleTwistLocal.pow_mem_pow H I hP (n * D))
    have h0 : ∃ m : ℕ, xProd J ^ m • (c ^ (e * D) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      refine ⟨n * D, ?_⟩
      have e1 : xProd J ^ (n * D) • (c ^ (e * D) • f) =
          (∏ l ∈ J.1.erase j, h l) ^ (n * D) • ((c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
            (AmpleAffineGen.chartRatio I K ^ D • f)) := by
        rw [smul_smul, smul_smul, smul_smul, hJ]
        congr 1
        have hr := AmpleAffineGen.chartRatio_mul_chartRatio I K
        calc (h j * ∏ l ∈ J.1.erase j, h l) ^ (n * D) * c ^ (e * D)
            = (∏ l ∈ J.1.erase j, h l) ^ (n * D) * ((c ^ e * h j ^ n) ^ D *
                (AmpleAffineGen.chartRatio K I * AmpleAffineGen.chartRatio I K) ^ D) := by
              rw [hr, one_pow, mul_one]; ring
          _ = _ := by ring
      have e2 : J.1.card * (n * D) = n * D + (J.1.erase j).card * (n * D) := by
        rw [← hcard]; ring
      rw [e1, e2]
      exact hz2

    have hstep : ∀ q : ℕ, ∃ m : ℕ, xProd J ^ m • (c ^ (e * D + q) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      intro q
      induction q with
      | zero => exact h0
      | succ q ih =>
        rw [← Nat.add_assoc, pow_succ', ← smul_smul]
        exact gen_smul F.toSubSystem H hh I J hj ha ih
    refine eventually_atTop.mpr ⟨e * D, fun M hM => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hM
    exact Submodule.subset_span (hstep q)
  exact (eventually_all.mpr key).mono fun M hM => (Submodule.mem_iInf _).mpr hM

end VeryAmpleZExtend

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace ZChartLocal

open AmpleAffineGen AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ}
    {y : E} {w : Ω} (hy : y ∈ (F.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    w • y ∈ (F.twist (H.pow (c + d))).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction
    (p := fun y _ => w • y ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    exact Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, z, hz, by rw [smul_smul, mul_comm]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have e : w • (a • z) = a • (w • z) := by
      change w • ((a : Ω) • z) = (a : Ω) • (w • z)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ a hz

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]; exact (Submodule.mem_iInf _).mp (hh a) I
    exact mul_mem_pow H I ih 1 h1


omit [Module S E] [IsScalarTower S Ω E] in
theorem ratio_pow_smul_mem (F : SubSystem S x E) (I K : Chart x) (k : ℕ) {y : E} (hy : y ∈ F.sub I) :
    chartRatio I K ^ k • y ∈ F.sub I :=
  Submodule.smul_mem (F.sub I) (⟨_, pow_mem (chartRatio_mem I K) k⟩ : chartRing S x I) hy


omit [Module S E] [IsScalarTower S Ω E] in
theorem loc_subFamily (G : SubFamily S x E) (I K : Chart x) {y : E}
    (hy : y ∈ G.sub (unionChart I K)) : ∃ c : ℕ, chartRatio I K ^ c • y ∈ G.sub I := by
  obtain ⟨a, ha, hay⟩ := (G.mem_iff I (unionChart I K) (subset_unionChart_left I K) y).mp hy
  obtain ⟨w, hw⟩ := ha.exists_left_inv
  obtain ⟨D, hD⟩ := exists_pow_mul_mem I K w.2
  refine ⟨D, ?_⟩
  have hw' : (w : Ω) * (a : Ω) = 1 := congrArg Subtype.val hw
  have e : chartRatio I K ^ D • y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y) := by
    change _ = (chartRatio I K ^ D * (w : Ω)) • ((a : Ω) • y)
    rw [smul_smul, mul_assoc, hw', mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ hay


omit [Module S E] [IsScalarTower S Ω E] in
theorem loc_twist (G : SubFamily S x E) (H : LineBundle S x) (I K : Chart x) (q : ℕ) {y : E}
    (hy : y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub (unionChart I K)) :
    ∃ c : ℕ, chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction (p := fun y _ => ∃ c : ℕ,
    chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨p, hp, z, hz, rfl⟩
    obtain ⟨D₁, h₁⟩ := exists_pow_mul_mem_of_eq (H.powBundle q)
      (LineBundle.powBundle_toSubSystem H q) I K hp
    obtain ⟨D₂, h₂⟩ := loc_subFamily G I K hz
    refine ⟨D₁ + D₂, Submodule.subset_span ⟨_, h₁, _, h₂, ?_⟩⟩
    rw [smul_smul, smul_smul, pow_add]
    congr 1
    ring
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    have e : chartRatio I K ^ (c₁ + c₂) • (y₁ + y₂) =
        chartRatio I K ^ c₂ • (chartRatio I K ^ c₁ • y₁) + chartRatio I K ^ c₁ • (chartRatio I K ^ c₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm c₂ c₁]
    rw [e]
    exact Submodule.add_mem _ (ratio_pow_smul_mem _ I K c₂ h₁) (ratio_pow_smul_mem _ I K c₁ h₂)
  · rintro a y - ⟨c, hc⟩
    obtain ⟨D, hD⟩ := exists_pow_mul_mem I K a.2
    refine ⟨D + c, ?_⟩
    have e : chartRatio I K ^ (D + c) • (a • y) = (⟨_, hD⟩ : chartRing S x I) • (chartRatio I K ^ c • y) := by
      change chartRatio I K ^ (D + c) • ((a : Ω) • y) = (chartRatio I K ^ D * (a : Ω)) • (chartRatio I K ^ c • y)
      rw [smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hc

end ZChartLocal


open AmpleAffineGen AmpleTwistLocal ZChartLocal in
theorem ZChartLocal.proof (hSmul : ZChartSmul.Statement.{u, v, w}) : ZChartLocal.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj b hb K hK j₀ hj₀ I I' hI' z hz
  classical
  have hbpow : ∀ (k : ℕ) {y : E}, y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J →
      b ^ k • y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J := by
    intro k
    induction k with
    | zero => intro y hy; rwa [pow_zero, one_smul]
    | succ k ih =>
      intro y hy
      rw [pow_succ', mul_smul]
      exact hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hh J j hj I b hb _ (ih hy)
  have hIU : I'.1 ⊆ (unionChart I K).1 := by
    rw [hI']; exact Finset.insert_subset (Finset.mem_union_right _ hj₀) Finset.subset_union_left
  have hzU : z ∈ secsOnZChart G.toSubSystem H.toSubSystem h (unionChart I K) J := by
    refine Submodule.span_mono ?_ hz
    rintro y ⟨n, hn⟩
    exact ⟨n, (G.toSubSystem.twist (H.toSubSystem.pow _)).mono I' _ hIU _ hn⟩
  obtain ⟨e, n, hn⟩ := hK I
  have hR := prod_mem_pow H.toSubSystem I hh (J.1.erase j)
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  generalize ∏ l ∈ J.1.erase j, h l = R at hR hJ
  have hu := mul_mem_pow H.toSubSystem I hn _ (pow_mem_pow H.toSubSystem I hR n)
  generalize hud : b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) * h j ^ n * R ^ n = u at hu
  have huv : u * chartRatio I K = b ^ e * xProd J ^ n := by
    have h1 := chartRatio_mul_chartRatio I K
    rw [chartRatio, chartRatio] at h1
    rw [← hud, hJ, chartRatio]
    linear_combination (b ^ e * (h j * R) ^ n) * h1
  change z ∈ Submodule.span S _ at hzU
  refine Submodule.span_induction (p := fun z _ =>
    ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ hzU
  · rintro y ⟨m, hm⟩
    obtain ⟨c, hc⟩ := loc_twist G H I K _ hm
    refine ⟨e * c, Submodule.subset_span ⟨m + n * c, ?_⟩⟩
    have h2 := smul_mem_twist_pow G.toSubSystem H.toSubSystem I hc (pow_mem_pow H.toSubSystem I hu c)
    have e1 : xProd J ^ (m + n * c) • b ^ (e * c) • y = u ^ c • chartRatio I K ^ c • xProd J ^ m • y := by
      rw [smul_smul, smul_smul, smul_smul, ← mul_pow, huv]
      congr 1
      ring
    have e2 : J.1.card * m + (1 * n + (J.1.erase j).card * n) * c = J.1.card * (m + n * c) := by
      rw [← hcard]; ring
    rw [e1, ← e2]
    exact h2
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
    refine ⟨e₁ + e₂, ?_⟩
    have e3 : b ^ (e₁ + e₂) • (y₁ + y₂) = b ^ e₂ • (b ^ e₁ • y₁) + b ^ e₁ • (b ^ e₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm e₂ e₁]
    rw [e3]
    exact Submodule.add_mem _ (hbpow _ h₁) (hbpow _ h₂)
  · rintro s y - ⟨e', h'⟩
    exact ⟨e', by rw [smul_comm]; exact Submodule.smul_mem _ s h'⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace VeryAmpleZChartRing

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_pow_mul_mem_ampleRing (H : LineBundle S x) {m : ℕ} {h : Ω}
    (hh : ∀ I, h ∈ (H.pow m).sub I) {c : Ω} (hc : c ∈ ampleRing H.toSubSystem m h) (K : Chart x)
    (hrat : ∀ I : Chart x, ∃ e : ℕ,
      c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem m h I)
    {y : Ω} (hy : y ∈ ampleChart H.toSubSystem m h K) : ∃ M : ℕ, c ^ M * y ∈ ampleRing H.toSubSystem m h := by
  classical
  have hI : ∀ I : Chart x, ∃ M, c ^ M * y ∈ ampleChart H.toSubSystem m h I := by
    intro I
    have h1 : y ∈ ampleChart H.toSubSystem m h (AmpleAffineGen.unionChart I K) :=
      AmpleAffineGen.ampleChart_mono (AmpleAffineGen.subset_unionChart_right I K) hy
    obtain ⟨D, hD⟩ := AmpleAffineGen.ampleChart_loc H I K h1
    obtain ⟨e, he⟩ := hrat I
    refine ⟨e * D, ?_⟩
    have := mul_mem
      (pow_mem (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from he) D)
      (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hD)
    rwa [show c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) =
        c ^ e * AmpleAffineGen.chartRatio K I from rfl,
      AmpleAffineGen.pow_mul_cancel (AmpleAffineGen.chartRatio_mul_chartRatio I K)] at this
  choose M hM using hI
  refine ⟨Finset.univ.sup M, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : M I ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ I)
  have e1 : c ^ Finset.univ.sup M * y = c ^ (Finset.univ.sup M - M I) * (c ^ M I * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e1]
  exact mul_mem
    (pow_mem (show c ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from
      Set.mem_iInter.mp hc I) _)
    (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hM I)

theorem ampleBase_le_chartRing {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J :=
  Algebra.adjoin_le (by
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X j, 1, X_mem_monos hj, isHomogeneous_X S l, isHomogeneous_X S j, by simp⟩)

theorem pow_div_xProd_mem {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) (j : Fin (r + 1)) :
    h j ^ J.1.card / xProd J ∈ chartRing S h J :=
  ⟨X j ^ J.1.card, AmpleAffineGen.monoProd J.1, J.1.card, AmpleAffineGen.monoProd_mem_monos subset_rfl,
    by simpa using (isHomogeneous_X S j).pow J.1.card, AmpleAffineGen.monoProd_isHomogeneous J.1,
    by rw [map_pow, aeval_X, AmpleAffineGen.aeval_monoProd, xProd]⟩

end VeryAmpleZChartRing


open VeryAmpleZChartRing in
theorem VeryAmpleZChartRing.proof : VeryAmpleZChartRing.Statement.{u, w} := by
  intro S _ Ω _ _ N x H r h hv J j hjJ c hc K hrat α hα
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
  have hh : ∀ I : Chart x, h j ∈ (H.pow 1).sub I := fun I => by
    rw [SubSystem.pow_sub, pow_one]
    exact (Submodule.mem_iInf _).mp (hv.mem_secs j) I
  have hJ0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  obtain ⟨n, hn⟩ := hα
  set g : Ω := xProd J / h j ^ J.1.card with hg
  have hy : α * g ^ n ∈ ampleChart H.toSubSystem 1 (h j) K := by
    refine ⟨J.1.card * n, ?_⟩
    have e1 : α * g ^ n * h j ^ (J.1.card * n) = α * xProd J ^ n := by
      rw [hg, div_pow, pow_mul, ← pow_mul, mul_comm J.1.card n, pow_mul, mul_assoc,
        div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hj0))]
    rw [e1, one_mul]
    exact hn
  obtain ⟨M₀, hM₀⟩ := exists_pow_mul_mem_ampleRing H hh hc K hrat hy
  have hbase := ampleBase_le_chartRing (S := S) J hjJ
  have h1 : c ^ M₀ * (α * g ^ n) ∈ chartRing S h J := hbase (hv.closed j hj0 hM₀)
  have hcJ : c ∈ chartRing S h J := hbase (hv.closed j hj0 hc)
  have h2 : c ^ M₀ * α ∈ chartRing S h J := by
    have e2 : c ^ M₀ * α = c ^ M₀ * (α * g ^ n) * (h j ^ J.1.card / xProd J) ^ n := by
      rw [hg, mul_assoc (c ^ M₀), mul_assoc α, ← mul_pow, div_mul_div_cancel₀ (pow_ne_zero _ hj0),
        div_self hJ0, one_pow, mul_one]
    rw [e2]
    exact mul_mem h1 (pow_mem (pow_div_xProd_mem J j) n)
  refine eventually_atTop.mpr ⟨M₀, fun M hM => ?_⟩
  have e3 : c ^ M * α = c ^ (M - M₀) * (c ^ M₀ * α) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hM]
  rw [e3]
  exact mul_mem (pow_mem hcJ _) h2

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

def CellPosExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) : Prop :=
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

end

def CellContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (c : ∀ k, ι k),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I → G I = ⊥) →
    (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' → G I ≤ G I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
      G (Function.update I k (insert (c k) (I k))) = G I) →
    CellPosExact S y G

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
