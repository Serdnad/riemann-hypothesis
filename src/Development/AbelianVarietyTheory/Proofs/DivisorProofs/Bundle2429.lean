module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

set_option autoImplicit false


noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.ToWeight

theorem sum_padicValNat_log_le (N : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q ≤ Real.log N := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ q ∈ S, (padicValNat q N : ℝ) * Real.log q = ∑ q ∈ S, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_congr rfl fun q hq => by rw [Nat.factorization_def N (hS q hq), Nat.padicValNat_def]
    _ ≤ ∑ q ∈ S ∪ N.factorization.support, (N.factorization q : ℝ) * Real.log q :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun q _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    _ = _ := (Finset.sum_subset Finset.subset_union_right fun q _ hq => by
          rw [Finsupp.notMem_support_iff.1 hq]; simp).symm

theorem sum_different_le (E : Type) [Field E] [NumberField E] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∑ q ∈ S, (different_vp E q : ℝ) * Real.log q ≤ lrd E := by
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h := sum_padicValNat_log_le (discr E).natAbs S hS
  have e1 : lrd E = Real.log ((discr E).natAbs : ℝ) / Module.finrank ℚ E := by
    unfold lrd
    rw [rootDiscr_def, Real.log_rpow (by exact_mod_cast abs_pos.2 (discr_ne_zero E)), Nat.cast_natAbs]
    field_simp
  rw [e1, le_div_iff₀ hn, Finset.sum_mul]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun q _ => ?_) h
  unfold different_vp
  push_cast
  field_simp

theorem different_nonneg (E : Type) [Field E] [NumberField E] (q : ℕ) : (0 : ℝ) ≤ (different_vp E q : ℝ) := by
  unfold different_vp
  push_cast
  positivity

theorem primeSum_add (E : Type) [Field E] [NumberField E] {S B : Finset ℕ} {e : ℕ → ℝ} {s a : ℝ} (h : PrimeSum S e s)
    (hB : ∀ q ∈ B, q.Prime) (ha : 0 ≤ a) :
    PrimeSum (S ∪ B) (fun q => e q + if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) (s + (a * lrd E + logSum B)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => (Finset.mem_union.1 hq).elim (h1 q) (hB q), fun q => add_nonneg (h2 q) ?_, fun q hq => ?_, ?_⟩
  · have := different_nonneg E q
    split_ifs
    · positivity
    · exact le_rfl
  · rw [Finset.mem_union, not_or] at hq
    simp [h3 q hq.1, hq.2]
  · simp only [add_mul, Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [← Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]]
      exact h4
    · rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      rw [Finset.sum_congr rfl fun q hq => show (if q ∈ B then a * (different_vp E q : ℝ) + 1 else 0) * Real.log q =
        a * ((different_vp E q : ℝ) * Real.log q) + Real.log q by rw [if_pos hq]; ring,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left (sum_different_le E B hB) ha) le_rfl

theorem size_le {f r l n m d σ c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hm0 : 0 ≤ m) (hm : 2 * m ≤ n)
    (hn : n ≤ 20 * f * r ^ 2) (hd : d ≤ 3 * l) (hc : 0 ≤ c) (hσ : σ ≤ c * (f * r * l)) :
    m * (f * r) * d + σ ≤ (30 + c) * (f * r * l) ^ 12 := by
  have hz : 1 ≤ f * r * l := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hl
  have h1 : f * r * l ≤ (f * r * l) ^ 12 := le_self_pow₀ hz (by norm_num)
  have h3 : (f * r * l) ^ 3 ≤ (f * r * l) ^ 12 := pow_le_pow_right₀ hz (by norm_num)
  have h4 : f ^ 2 * r ^ 3 * l ≤ f ^ 3 * r ^ 3 * l ^ 3 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hf (by norm_num)) (by positivity))
      (le_self_pow₀ hl (by norm_num)) (by positivity) (by positivity)
  have h5 : m * (f * r) * d ≤ m * (f * r) * (3 * l) := mul_le_mul_of_nonneg_left hd (by positivity)
  have h6 : m * (f * r * (3 * l)) ≤ 10 * f * r ^ 2 * (f * r * (3 * l)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h7 := mul_le_mul_of_nonneg_left h1 hc
  nlinarith

end GlobalTheory.RefSum.ToWeight

end
end

section



noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.AnchorRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem anchor_eq (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) =
      ⌊Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) + (D.hc t).e i -
        (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ +
        (((p.κ i).n / 2 : ℕ) : ℤ) := by
  have hk := D.R.m_add_three_le_k
  have hmain := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have hpq : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 := hmain.1
  have hlt : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by omega
  have hj : D.R.k - 2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
  obtain ⟨-, hnn⟩ := GlobalTheory.RecGaps.bigEnt p P i t (D.R.k - 2) hj
  unfold anchor
  rw [dite_eq_left hlt, GlobalTheory.CovTop.WtRead.laOf_big D p.T p.fw.laws i (p.κ i) t τ hτ _ ⟨D.R.k - 2, hj⟩ (by simp; omega),
    (p.fw.kap i t).1 ⟨D.R.k - 2, hj⟩]
  rw [GlobalTheory.RecGaps.sig_Wc]
  unfold aPl
  rw [if_pos hj, Int.toNat_of_nonneg hnn]

theorem abs_anchor_sub_le (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)| ≤
      L.Sc + D.R.nV + D.R.m + D.R.t + 2 := by
  have hk := D.R.m_add_three_le_k
  have ha := anchor_eq p i P t τ hτ
  have hn : (p.κ i).n = D.R.nV := (p.fw.kap i t).2.2
  have hv : Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) = (D.hc t).v ⟨D.R.k - 2, by omega⟩ := by
    unfold Formalism.L2.NTheta.lamAt; rw [dite_eq_left (by omega)]
  have hc := L.cloud_v t ⟨D.R.k - 2, by omega⟩
  have hsw : ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1) = (i : ℚ) + 1 := by
    rw [show (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) by simp only [Ranks.sigW]; omega,
      Nat.cast_sub (by omega : 2 ≤ D.R.k)]
    push_cast; ring
  rw [hsw, hv] at ha
  rw [ha, hn]
  have h1 := Int.floor_le ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h2 := Int.lt_floor_add_one ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h1' : ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) ≤
      (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) <
      ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast h2
  have hnv : ((D.R.nV / 2 : ℕ) : ℝ) ≤ D.R.nV := by exact_mod_cast Nat.div_le_self _ _
  have hnv0 : (0 : ℝ) ≤ ((D.R.nV / 2 : ℕ) : ℝ) := by positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  rw [Int.cast_add, Int.cast_natCast]
  push_cast at h1' h2'
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2]



theorem anchorAt_of {PP A : ℝ} (P : ParameterChoice' D L) (hw : WtNum p i PP) (hh : HostNum D L PP A 1) : AnchorAt p i 100 := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  obtain ⟨hp, hq, hcard, -, -, E, hE, -⟩ := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hL10 := hh.big.2.1
  have hLx := hh.big.2.2.1
  have hll := hh.big.2.2.2
  have hxA : 1 ≤ L.sc.x ^ A := Real.one_le_rpow (by linarith) (by linarith [hh.poly.1])
  have hb : L.sc.x ^ A ≤ L.sc.b := by simpa using hh.room
  have hb1 : 1 ≤ L.sc.b := hxA.trans hb
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hh.f8
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hunit := hw.unit
  have hom := hw.om
  have hanc : ∀ τ, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤ 4 * L.sc.b := by
    intro τ
    unfold anchor
    split_ifs with h
    · exact hw.up τ _
    · simp only [Int.cast_zero, abs_zero]; linarith

  have hpr : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by
    rw [hp, hq]; exact_mod_cast GlobalTheory.CovTop.WtRead.sigW_add D i
  have hp0 : (0 : ℝ) ≤ (dat p i).p := by positivity
  have hq0 : (0 : ℝ) ≤ (dat p i).q := by positivity
  have hcr : |((dat p i).p : ℝ) - (dat p i).q| ≤ D.R.r := abs_le.2 ⟨by linarith, by linarith⟩
  have hqm : ((dat p i).q : ℝ) ≤ D.R.m := by
    rw [hq]; exact_mod_cast (by simp only [Ranks.sigW]; omega : (D.R.sigW ((i : ℕ) + 1)).2 ≤ D.R.m)
  have hc_eq : ((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ)) =
      ((dat p i).p : ℝ) - (dat p i).q := by
    rw [hp, hq]
    simp only [Ranks.sigW]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring

  have hmainS : mainT p i = ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm := by
    show ∑ ρ : RPl D.R, (((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ))) *
      (ofRecord D L p.Del p.h0).w ((i : ℕ) + 1) ρ * (ofRecord D L p.Del p.h0).logOm = _
    rw [hc_eq, ← (tauPl_bijective D).sum_comp (fun t => (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp only [NumDatum.w, NumDatum.eQ]
    rw [dite_eq_left ⟨by omega, by omega⟩]
    congr 3
  have hancS : ∑ τ : Psi p.T.Q.H, (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm =
      ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm :=
    (Equiv.sum_comp E (fun τ => (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm)).symm
  have hcardT : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by exact_mod_cast Formalism.MainNotions.Lnk.card_Tau D

  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.Lnk.card_Tau]; have := hh.f8; omega)
  obtain ⟨t0⟩ := hne
  have hw'' : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
    have a1 := hw.low (E t0)
    have a2 := (abs_le.1 (hanc (E t0))).2
    linarith
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hSc0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hrS : (D.R.r : ℝ) * L.Sc ≤ 16 * L.sc.b := by
    have a1 := P.kS_le
    have a2 : (D.R.r : ℝ) * L.Sc ≤ 2 * D.R.k * L.Sc := mul_le_mul_of_nonneg_right hr2k hSc0
    linarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : D.R.m ≤ D.R.r)
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hrnV : (D.R.r : ℝ) * D.R.nV ≤ L.sc.b := by
    have a1 := hh.poly.2.2
    have e0 : (0 : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by positivity
    have a2 : (D.R.r : ℝ) * D.R.nV * 1 ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) e0
    calc (D.R.r : ℝ) * D.R.nV = (D.R.r : ℝ) * D.R.nV * 1 := by ring
      _ ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) := a2
      _ = D.R.f * D.R.r * D.R.nV * L.sc.L := by ring
      _ ≤ L.sc.x ^ A := a1
      _ ≤ L.sc.b := hb
  have hB : (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) ≤ 20 * L.sc.b := by
    have e1 : (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ 4 * ((D.R.r : ℝ) * D.R.nV) := by
      calc (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ (D.R.r : ℝ) * (4 * D.R.nV) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * ((D.R.r : ℝ) * D.R.nV) := by ring
    calc (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) =
          (D.R.r : ℝ) * L.Sc + (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) := by ring
      _ ≤ 16 * L.sc.b + 4 * L.sc.b := add_le_add hrS (by linarith)
      _ = 20 * L.sc.b := by ring
  refine ⟨?_, ?_, hh.poly.2.2.trans hb⟩
  · rw [hmainS, hancS, ← Finset.sum_sub_distrib]
    have hterm : ∀ t : D.what₂.Tau, |(((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
        (ofRecord D L p.Del p.h0).logOm - (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm| ≤
        (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) := by
      intro t
      have a1 := abs_anchor_sub_le p i P t (E t) (hE t)
      rw [show (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) * (ofRecord D L p.Del p.h0).logOm -
          (((dat p i).p : ℝ) - (dat p i).q) * ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) *
          (ofRecord D L p.Del p.h0).logOm = -((((dat p i).p : ℝ) - (dat p i).q) *
          (((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)) *
          (ofRecord D L p.Del p.h0).logOm) by ring, abs_neg, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hcr a1 (abs_nonneg _) (by positivity)) hom (abs_nonneg _) (by positivity)
    calc _ ≤ ∑ t : D.what₂.Tau, (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hterm t)
      _ = D.R.f * ((D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2)) * (3 * L.sc.L) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardT]; ring
      _ ≤ D.R.f * (20 * L.sc.b) * (3 * L.sc.L) := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * L.sc.L * 1 ≤ D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) :=
            mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) hll) e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) := by ring
          have e4 : (D.R.f : ℝ) * (20 * L.sc.b) * (3 * L.sc.L) = 60 * (D.R.f * L.sc.b * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith
  · have hsum : ∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤
        D.R.f * (4 * L.sc.b) := by
      calc _ ≤ ∑ τ : Psi p.T.Q.H, 4 * L.sc.b := Finset.sum_le_sum fun τ _ => hanc τ
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]
    calc (∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)|) *
          ((dat p i).q : ℝ) * L.sc.L ≤ D.R.f * (4 * L.sc.b) * D.R.m * L.sc.L := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * D.R.m * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * D.R.m * L.sc.L * 1 ≤ D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) :=
            mul_le_mul_of_nonneg_left hll e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by ring
          have e4 : (D.R.f : ℝ) * (4 * L.sc.b) * D.R.m * L.sc.L = 4 * (D.R.f * L.sc.b * D.R.m * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith

end GlobalTheory.CovTop.AnchorRd

namespace GlobalTheory.CovTop

end GlobalTheory.CovTop
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameAut

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

section Op

variable (K : Type) [CommRing K] (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)

def wtOp (g : ι → GL (Fin n) K) : Module.End K (NablaT K n mu) :=
  ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g

theorem wtOp_apply (g : ι → GL (Fin n) K) (u : NablaT K n mu) :
    wtOp K n mu sh g u = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g u := rfl

theorem wtOp_one : wtOp K n mu sh 1 = 1 := by
  simp [wtOp, grp]

theorem wtOp_mul (g h : ι → GL (Fin n) K) : wtOp K n mu sh (g * h) = wtOp K n mu sh g * wtOp K n mu sh h := by
  simp only [wtOp, grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

def wtHom : (ι → GL (Fin n) K) →* Module.End K (NablaT K n mu) where
  toFun := wtOp K n mu sh
  map_one' := wtOp_one K n mu sh
  map_mul' := wtOp_mul K n mu sh

end Op

end GlobalTheory.FrameAut

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL

namespace GlobalTheory.FrameAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def labOf (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) : HeightOneSpectrum (𝓞 D.host.E) := Formalism.DivisionValues.conjPl (plOf p j t Q)

def IsSystemOf (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} {F : Frame l D.what₂.Tau N} {e0 : D.what₂.LL →+* PadicAlgCl l}
    {ix : F.I → (blk p j t).Pl × ℕ} {inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)} (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (π : Submodule ℂ (UA D.host.E N → ℂ)) : Prop :=
  IsAutRepU π ∧
  (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
    HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
  (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
  ∀ Q : (blk p j t).Pl, IsUnramU π (labOf p j t Q) ∧
    ∃ (σ : SmIrr (GL (Fin N) ((labOf p j t Q).adicCompletion D.host.E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU N (labOf p j t Q)) ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype) σ.ρ ∧
      GlobalTheory.LFun.HasSatGL (labOf p j t Q) σ.ρ S ∧
      ∀ i, (ix i).1 = Q → T.io (θ i) = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E (labOf p j t Q)) N S (ix i).2

def PlacesOk (j : Fin D.R.m) (t : p.P.T) (l : ℕ) : Prop :=
  (∀ Q : (blk p j t).Pl, IsSplitAt (labOf p j t Q) ∧
    (labOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
    Ideal.absNorm (labOf p j t Q).asIdeal = (blk p j t).q Q ∧
    (((l : ℕ) : 𝓞 D.host.E) ∈ (labOf p j t Q).asIdeal ↔ ((l : ℕ) : 𝓞 D.host.E) ∈ (plOf p j t Q).asIdeal)) ∧
  {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
    ¬ ∃ Q : (blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite ∧
  ∀ ν ∈ (blk p j t).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j t).q Q : ℝ) ^ ((blk p j t).n - (blk p j t).t)


open Classical in
def AutAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  PlacesOk p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) ∧
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π, IsSystemOf p j (p.R.mu w) T mu θ π

end GlobalTheory.FrameAut

end
end

section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hs E
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hs
  let V : ValuationSubring Y.functionField := E.ring.comap e.symm.toRingHom
  have hV (f : X.functionField) : f ∈ E.ring ↔ functionFieldMap s f ∈ V := by
    change f ∈ E.ring ↔ e.symm (e f) ∈ E.ring
    rw [e.symm_apply_apply]
  let φ : E.ring →+* V :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict V fun a => (hV _).1 a.2
  have hφ : Function.Bijective φ :=
    ⟨fun _ _ h => Subtype.ext (hs.1 (congrArg Subtype.val h)),
      fun f => ⟨⟨e.symm f.1, f.2⟩, Subtype.ext (e.apply_symm_apply f.1)⟩⟩
  have hc (a : k) : functionFieldMap s (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a :=
    RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s) a
  refine ⟨⟨V, fun a => hc a ▸ (hV _).1 (E.const_mem a),
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective φ hφ), ?_⟩, hV⟩
  have h3 := E.essFiniteType.comp (RingHom.FiniteType.of_surjective φ hφ.2).essFiniteType
  convert h3 using 1
  exact RingHom.ext fun a => Subtype.ext (hc a).symm

end GlobalTheory.Discrepancy
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.darboux_coords_rational_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (M₁ : Model σ X W) (om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      M₁.co = co ∧ IsPair B M₁ χX χW om₁ r s r' s' ∧ c₀ ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d) ∧ thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧
        ∀ x, e (om x Φ) = om₁ x (e Φ) := by
  first | exact @GlobalTheory.ModelChangeTo.change_to_coordinates | exact GlobalTheory.ModelChangeTo.change_to_coordinates | (intros; apply GlobalTheory.ModelChangeTo.change_to_coordinates <;> assumption)
end
