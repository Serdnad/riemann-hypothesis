module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle016
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise

noncomputable section

universe u w

namespace VeryAmplePow

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def mono {r j : ℕ} (h : Fin (r + 1) → Ω) (w : Fin j → Fin (r + 1)) : Ω := ∏ t, h (w t)

theorem range_mono {r j : ℕ} (h : Fin (r + 1) → Ω) :
    Set.range (mono (j := j) h) = Set.range h ^ j := by
  ext a
  rw [Set.mem_pow_iff_prod]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨fun t => h (w t), fun t => ⟨w t, rfl⟩, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    choose w hw using hf
    exact ⟨w, by simp only [mono, hw]⟩

theorem mono_mem {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hH : ∀ l I, h l ∈ H.sub I) (w : Fin j → Fin (r + 1)) (I : Chart x) :
    mono h w ∈ H.sub I ^ j := by
  rw [Submodule.pow_eq_span_pow_set]
  exact Submodule.subset_span (Set.mem_pow_iff_prod.mpr ⟨fun t => h (w t), fun t => hH _ I, rfl⟩)

theorem mono_succ {r j : ℕ} (h : Fin (r + 1) → Ω) (w : Fin (j + 1) → Fin (r + 1)) :
    mono h w = h (w 0) * mono h (Fin.tail w) := by
  simp only [mono, Fin.prod_univ_succ, Fin.tail]

theorem mono_cons {r j : ℕ} (h : Fin (r + 1) → Ω) (v : Fin (r + 1)) (t : Fin j → Fin (r + 1)) :
    mono h (Fin.cons v t : Fin (j + 1) → Fin (r + 1)) = h v * mono h t := by
  simp only [mono, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem ampleChart_le {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hH : ∀ l I, h l ∈ H.sub I) (w : Fin (j + 1) → Fin (r + 1)) (I : Chart x) :
    ampleChart H 1 (h (w 0)) I ⊆ ampleChart (H.pow (j + 1)) 1 (mono h w) I := by
  rintro a ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [SubSystem.pow_sub, one_mul] at hn
  rw [SubSystem.pow_sub, SubSystem.pow_sub, one_mul, ← pow_mul, mono_succ, mul_pow, ← mul_assoc,
    show (j + 1) * n = n + j * n by ring, pow_add, pow_mul]
  exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ (mono_mem hH _ I) n)

theorem isVeryAmpleBy_mono {H : SubSystem S x Ω} {r j : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy H h) {m : ℕ} (E : (Fin (j + 1) → Fin (r + 1)) ≃ Fin (m + 1)) :
    IsVeryAmpleBy (H.pow (j + 1)) (fun k => mono h (E.symm k)) := by
  have hH : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  have hgen : ∀ k w', mono h w' / mono h (E.symm k) ∈
      ampleBase (S := S) (fun k => mono h (E.symm k)) k :=
    fun k w' => Algebra.subset_adjoin ⟨E w', by simp⟩
  refine ⟨fun k => ?_, fun I => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · exact (Submodule.mem_iInf _).mpr fun I => by
      rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
      exact mono_mem hH _ I
  · change Submodule.span _ (Set.range (mono h ∘ E.symm)) = _
    rw [EquivLike.range_comp, range_mono, ← Submodule.span_pow, hv.generates I, SubSystem.pow_sub]
  · have hk' : mono h (E.symm k) ≠ 0 := hk
    rw [mono_succ] at hk'
    have hl : h (E.symm k 0) ≠ 0 := left_ne_zero_of_mul hk'
    have hq : mono h (Fin.tail (E.symm k)) ≠ 0 := right_ne_zero_of_mul hk'
    intro a ha
    have hI : ∀ I, ∃ n, a * mono h (E.symm k) ^ n ∈ H.sub I ^ ((j + 1) * n) := fun I => by
      obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha I
      refine ⟨n, ?_⟩
      rwa [SubSystem.pow_sub, SubSystem.pow_sub, one_mul, ← pow_mul] at hn
    choose nI hnI using hI
    classical
    have hn0 : ∀ I, a * mono h (E.symm k) ^ (∑ I', nI I') ∈ H.sub I ^ ((j + 1) * ∑ I', nI I') :=
      fun I => by
        obtain ⟨d, hd⟩ : ∃ d, ∑ I', nI I' = nI I + d :=
          ⟨_, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ I))).symm⟩
        rw [hd, pow_add, ← mul_assoc, mul_add, pow_add]
        exact Submodule.mul_mem_mul (hnI I)
          (by rw [pow_mul]; exact Submodule.pow_mem_pow _ (mono_mem hH _ I) d)
    have hb : a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') ∈
        ampleRing H 1 (h (E.symm k 0)) := Set.mem_iInter.mpr fun I => ⟨(j + 1) * ∑ I', nI I', by
      rw [SubSystem.pow_sub, one_mul]
      have : a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') *
          h (E.symm k 0) ^ ((j + 1) * ∑ I', nI I') = a * mono h (E.symm k) ^ (∑ I', nI I') := by
        rw [pow_mul, div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hl))]
      rw [this]
      exact hn0 I⟩
    have hbase : ampleBase (S := S) h (E.symm k 0) ≤
        ampleBase (S := S) (fun k => mono h (E.symm k)) k := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨v, rfl⟩
      have : h v / h (E.symm k 0) =
          mono h (Fin.cons v (Fin.tail (E.symm k)) : Fin (j + 1) → Fin (r + 1)) / mono h (E.symm k) := by
        rw [mono_cons, mono_succ h (E.symm k), mul_div_mul_right _ _ hq]
      change h v / h (E.symm k 0) ∈ _
      rw [this]
      exact hgen k _
    have hinv : h (E.symm k 0) ^ (j + 1) / mono h (E.symm k) ∈
        ampleBase (S := S) (fun k => mono h (E.symm k)) k := by
      have : h (E.symm k 0) ^ (j + 1) = mono h (fun _ => E.symm k 0 : Fin (j + 1) → Fin (r + 1)) := by
        simp [mono, Finset.prod_const]
      rw [this]
      exact hgen k _
    have ha' : a = a * (mono h (E.symm k) / h (E.symm k 0) ^ (j + 1)) ^ (∑ I', nI I') *
        (h (E.symm k 0) ^ (j + 1) / mono h (E.symm k)) ^ (∑ I', nI I') := by
      rw [mul_assoc, ← mul_pow, div_mul_div_cancel₀ (pow_ne_zero _ hl),
        div_self (by rw [mono_succ]; exact hk'), one_pow, mul_one]
    rw [ha']
    exact Subalgebra.mul_mem _ (hbase (hv.closed _ hl hb)) (Subalgebra.pow_mem _ hinv _)
  · have hk' : mono h (E.symm k) ≠ 0 := hk
    rw [mono_succ] at hk'
    have hl : h (E.symm k 0) ≠ 0 := left_ne_zero_of_mul hk'
    obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hv.affine (E.symm k 0) hl
    have hR : ampleRing H 1 (h (E.symm k 0)) ⊆ ampleRing (H.pow (j + 1)) 1 (mono h (E.symm k)) :=
      fun c hc => Set.mem_iInter.mpr fun I => ampleChart_le hH _ I (Set.mem_iInter.mp hc I)
    refine ⟨n, a, b, J, fun i => hR (ha i), fun i => hR (hb i), hsum, fun i I => ?_⟩
    obtain ⟨e, he⟩ := hJ i I
    exact ⟨e, ampleChart_le hH _ I he⟩

end VeryAmplePow

theorem VeryAmplePow.proof : VeryAmplePow.Statement.{u, w} := by
  intro S _ Ω _ _ N x H j hH hj
  obtain ⟨r, h, hv⟩ := hH
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have hc : (r + 1) ^ (j + 1) - 1 + 1 = (r + 1) ^ (j + 1) :=
    Nat.sub_add_cancel (Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.succ_ne_zero r)))
  exact ⟨_, _, VeryAmplePow.isVeryAmpleBy_mono hv (finFunctionFinEquiv.trans (finCongr hc.symm))⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ClaimLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coordGraded_tilde_mem_chartRing {I : Chart x} {y : Ω}
    (hy : y ∈ (coordGraded k x).tilde 0 I) : y ∈ chartRing k x I := by
  refine Submodule.span_induction (p := fun y _ => y ∈ chartRing k x I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ chartRing k x I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact ⟨f, s, e', hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact (chartRing k x I).zero_mem
    · intro a b _ _ ha hb; rw [smul_add]; exact (chartRing k x I).add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact (chartRing k x I).smul_mem ha r
  · exact (chartRing k x I).zero_mem
  · intro a b _ _ ha hb; exact (chartRing k x I).add_mem ha hb
  · intro a y _ hy; rw [chartRing_smul_def]; exact (chartRing k x I).mul_mem a.2 hy

theorem coordGraded_tildeSys_twist (X : SubSystem k x Ω) :
    ((coordGraded k x).tildeSys 0).twist X = X := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    have hyA := coordGraded_tilde_mem_chartRing hy
    have hqy : q • y = (⟨y, hyA⟩ : chartRing k x I) • q := by
      rw [smul_eq_mul, chartRing_smul_def, mul_comm]
    rw [SetLike.mem_coe, hqy]
    exact (X.sub I).smul_mem _ hq
  · intro q hq
    refine Submodule.subset_span ⟨q, hq, 1, ?_, by rw [smul_eq_mul, mul_one]⟩
    exact Submodule.subset_span ⟨1, 1, 0, 0, one_mem _, isHomogeneous_one _ _,
      Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩, by simp, by simp⟩

theorem twist_tildeSys_mono {M₁ M₂ : FinGradedSub (S := k) (x := x) Ω}
    (h : ∀ c, M₂.piece c ≤ M₁.piece c) (X : SubSystem k x Ω) (I : Chart x) :
    ∀ y ∈ ((M₂.tildeSys 0).twist X).sub I, y ∈ ((M₁.tildeSys 0).twist X).sub I := by
  intro y hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨q, hq, z, hz, rfl⟩
  refine ⟨q, hq, z, Submodule.span_mono ?_ hz, rfl⟩
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

variable (T : StepData k x) (Jg : FinGradedSub (S := k) (x := x) Ω)
  (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
    f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f})


include hJg in
theorem claim_le : ∀ c, Jg.piece c ≤ (coordGraded k x).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, -, hf, he, rfl⟩
  exact ⟨f, e, hf, he, rfl⟩


include hJg in
theorem claim_kill : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ),
    ∀ z ∈ (coordGraded k x).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Jg.piece (a + e)) ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', hg, he', rfl⟩
    rw [hJg]
    exact Submodule.subset_span ⟨f * g, e + e', T.J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha

end ClaimLemmas

theorem ClaimVanish.proof (h₁ : StepTwo.Statement.{u, w, w}) (h₂ : TwistVanish.Statement.{u, w})
    (h₃ : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  obtain ⟨Jg, hJg, hseq⟩ := h₃ k Ω N x T
  obtain ⟨cS, hS⟩ := h₁ k Ω N x T hK Ω (coordGraded k x) Jg (claim_le T Jg hJg)
    (claim_kill T Jg hJg)
  obtain ⟨cB, hB⟩ := h₂ k Ω N x (twistBundle k x 0) (twistBundle k x 1) N x (twist_hyps k N x).1
    (twist_hyps k N x).2
  refine ⟨max cS cB, fun b => ?_⟩
  induction b with
  | zero =>
    intro c hc
    have h0 := hB 0 c (le_trans (le_max_right _ _) hc)
    have e : ((twistBundle k x 0).twist ((twistBundle k x 1).pow 0)).twist (twistSys k x c) =
        (T.L.pow 0).twist (twistSys k x c) := by
      show ((twistSys k x 0).twist (twistSys k x 0)).twist (twistSys k x c) =
        (twistSys k x 0).twist (twistSys k x c)
      rw [twistSys_zero_twist]
    rw [e] at h0
    exact h0
  | succ b ih =>
    intro c hc
    have hq := hS (b + 1) c (le_trans (le_max_left _ _) hc)
    rw [coordGraded_tildeSys_twist] at hq
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))) ?_ ?_ hq
    · intro I y hy
      have hy' := twist_tildeSys_mono (claim_le T Jg hJg) _ I y hy
      rwa [coordGraded_tildeSys_twist] at hy'
    · exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b c)
        (ih (c + T.c₁) (le_trans hc (by linarith [T.c₁_pos])))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def ZChartLocal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    (∀ l, h l ∈ H.secs) → ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 →
    ∀ (b : Ω), b ∈ ampleRing H.toSubSystem 1 (h j) → ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ j₀ ∈ K.1, ∀ I I' : Chart x, I'.1 = insert j₀ I.1 →
        ∀ z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I' J,
          ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def ZChartSmul.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubSystem S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω),
    (∀ l, h l ∈ H.secs) → ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ (I : Chart x) (a : Ω),
      a ∈ ampleRing H 1 (h j) → ∀ z ∈ secsOnZChart G H h I J, a • z ∈ secsOnZChart G H h I J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

def VeryAmpleZExtend.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ, c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H 1 (h j) I) →
      ∀ f ∈ F.sub K, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZ F.toSubSystem H h J

def VeryAmpleZChartSpan.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubSystem S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (I : Chart x) (J : Chart h) (g : Finset E), F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E) →
      ∀ e ∈ secsOnZChart F H h I J, ∃ β : E → Ω,
        (∀ y ∈ g, β y ∈ ampleChart H J.1.card (xProd J) I) ∧ e = ∑ y ∈ g, β y • y

def VeryAmpleZChartRing.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy H.toSubSystem h →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H.toSubSystem 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ α ∈ ampleChart H.toSubSystem J.1.card (xProd J) K, ∀ᶠ M in atTop, c ^ M * α ∈ chartRing S h J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZColumns.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ I : Chart x,
      (∀ J J' : Chart h, J.1 ⊆ J'.1 →
        secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I J') ∧
      Cech.AugExact S (secsOnZChart G.toSubSystem H.toSubSystem h I) ((G.sub I).restrictScalars S)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZFamily.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h →
    ∃ F' : SubFamily S h E, ∀ J, (F'.sub J).restrictScalars S = secsOnZ F.toSubSystem H.toSubSystem h J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ J : Chart h, ∃ t : Finset E,
      (t : Set E) ⊆ secsOnZ F.toSubSystem H.toSubSystem h J ∧
      secsOnZ F.toSubSystem H.toSubSystem h J ≤ (Submodule.span (chartRing S h J) (t : Set E)).restrictScalars S

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CellZeroConst.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω),
    cellD S y 0 s = 0 →
      ∀ c c' : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, CellMeets y c.1 → CellMeets y c'.1 → s c = s c'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
