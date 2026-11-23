module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle062
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.SharpRestriction.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle003
import Formalism.LocalRingCardinality.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle001
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

def wd (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau) : WeightData where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  j := (j : ℕ) + 1
  e := ((D.hc τ).e_int j).choose
  v := fun n => if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0
  b := fun n => if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_e : ((wd D j τ).e : ℚ) = (D.hc τ).e j := ((D.hc τ).e_int j).choose_spec.symm

theorem wd_v (n : ℕ) (h : 2 ≤ n ∧ n - 2 < D.R.k - 1) : ((wd D j τ).v n : ℚ) = (D.hc τ).v ⟨n - 2, h.2⟩ := by
  show (((if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dite_eq_left h]
  exact ((D.hc τ).v_int _).choose_spec.symm

theorem wd_b (n : ℕ) (h : 1 ≤ n ∧ n - 1 < D.R.m) : ((wd D j τ).b n : ℚ) = (D.hc τ).b ⟨n - 1, h.2⟩ := by
  show (((if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dite_eq_left h]
  exact ((D.hc τ).b_int _).choose_spec.symm

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_lam_lo (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k - 1) :
    ((wd D j τ).lam i : ℚ) = (D.hc τ).v ⟨i - 1, by omega⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_pos (by rw [hk]; exact h2), wd_v D j τ (i + 1) ⟨by omega, by omega⟩]
  exact congrArg _ (Fin.ext (by simp))

theorem wd_lam_hi (i : ℕ) (h1 : D.R.k - 1 < i) (h2 : i - (D.R.k - 1) - 1 < D.R.m) :
    ((wd D j τ).lam i : ℚ) = -(D.hc τ).b ⟨i - (D.R.k - 1) - 1, h2⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_neg (by rw [hk]; omega)]
  push_cast
  rw [hk, wd_b D j τ _ ⟨by omega, h2⟩]

theorem wd_hyp : (wd D j τ).Hyp := by
  have hR := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hjm := j.2
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  set P := D.hc τ with hP
  have hu : ∀ a b : Fin D.R.k, a.1 = b.1 → P.u a = P.u b := fun a b h => congrArg _ (Fin.ext h)
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨show 1 ≤ D.R.k by omega, show 1 ≤ (j : ℕ) + 1 by omega, show (j : ℕ) + 1 ≤ D.R.m by omega, ?_, D.R.t_odd, ?_, ?_, ?_⟩
  · show Odd (D.R.k + D.R.m - 1)
    exact Nat.Even.sub_odd (by omega) (D.R.k_even.add D.R.m_even) odd_one
  · intro i hi1 hi2
    have hi2' : i < D.R.k + D.R.m - 1 := hi2
    suffices ((wd D j τ).lam (i + 1) : ℚ) < (wd D j τ).lam i by exact_mod_cast this
    rcases lt_trichotomy (i + 1) (D.R.k) with h | h | h
    · rw [wd_lam_lo D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_gt_v ⟨i, by omega⟩
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨i, by omega⟩ (by simp; omega)] at h2
      have e1 : (⟨i + 1 - 1, by omega⟩ : Fin (D.R.k - 1)) = ⟨i, by omega⟩ := Fin.ext (by simp)
      rw [e1]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_last_gt (by omega) (by omega)
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨D.R.k - 1, by omega⟩ (by simp; omega)] at h2
      rw [hb ⟨i + 1 - (D.R.k - 1) - 1, _⟩ ⟨0, by omega⟩ (by simp; omega)]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_hi D j τ i (by omega) (by omega)]
      have h1 := P.gap_be ⟨i - (D.R.k - 1) - 1, by omega⟩
      have h2 := P.gap_eb ⟨i - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)
      rw [hb ⟨i - (D.R.k - 1) - 1 + 1, _⟩ ⟨i + 1 - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)] at h2
      linarith
  · show (((wd D j τ).b ((j : ℕ) + 1)) : ℤ) < (wd D j τ).e
    suffices ((wd D j τ).b ((j : ℕ) + 1) : ℚ) < (wd D j τ).e by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    have := P.gap_be j
    linarith
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((wd D j τ).e : ℤ) < (wd D j τ).b ((j : ℕ) + 1 + 1)
    suffices ((wd D j τ).e : ℚ) < (wd D j τ).b ((j : ℕ) + 1 + 1) by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    have := P.gap_eb j hj''
    linarith

theorem wd_gap : (wd D j τ).GapHyp := by
  have hjm := j.2
  set P := D.hc τ with hP
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨?_, ?_⟩
  · show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).e : ℚ) - (wd D j τ).b ((j : ℕ) + 1)
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    exact P.gap_be j
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).b ((j : ℕ) + 1 + 1) : ℚ) - (wd D j τ).e
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    exact P.gap_eb j hj''

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem exists_isLamPrime :
    ∃ lam : DomWeight (Vc D j).rank, Formalism.IndefR.Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
  have hjm := j.2
  have hC := GlobalTheory.LowestKType.thetaSide (wd D j τ) (wd_hyp D j τ) (wd_gap D j τ)
  have hint := hC.2.2.2.1
  have hdom := hC.2.2.2.2.1
  have hN : (Vc D j).rank = (wd D j τ).nV := D.sp.V_rank _ (by omega) (by omega)

  have hmono : ∀ d a : ℕ, 1 ≤ a → a + d ≤ (wd D j τ).nV →
      (wd D j τ).lamPrime (a + d) ≤ (wd D j τ).lamPrime a := by
    intro d
    induction d with
    | zero => intro a _ _; simp
    | succ d ih =>
      intro a ha had
      have := hdom (a + d) (by omega) (by omega)
      rw [← add_assoc]
      exact this.trans (ih a ha (by omega))
  let w : Fin (Vc D j).rank → ℤ := fun i => (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose
  have hw : ∀ i, (w i : ℚ) = (wd D j τ).lamPrime (i.1 + 1) := fun i =>
    (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose_spec.symm
  have hanti : Antitone w := by
    intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    have := hmono (b.1 - a.1) (a.1 + 1) (by omega) (by have := b.2; omega)
    rw [show a.1 + 1 + (b.1 - a.1) = b.1 + 1 by omega] at this
    have h' : (w b : ℚ) ≤ w a := by rw [hw, hw]; exact this
    exact_mod_cast h'
  refine ⟨⟨w, hanti⟩, ⟨by omega, by omega⟩, wd D j τ, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [wd_e]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_v D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_b D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro i
    exact hw i

theorem isLamPrime_lamLdef :
    Formalism.IndefR.Bridge.IsLamPrime (D := D)
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  have hex := exists_isLamPrime D j τ
  unfold Formalism.IndefR.Bridge.lamLdef
  rw [dite_eq_left hex]
  exact hex.choose_spec

end GlobalTheory.LiftWeightForced
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.IntCuspLat

theorem exists_dataX (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D := by
  obtain ⟨-, -, -, hx0, hx1, -⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have habs := h.xiAbs j hj σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hM : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar
    (xiR D) T.Q.l.M
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (fun γ => gamAt_of_lawsM D T h j hj σ hσ k γ)
  exact ⟨{ Xx with
    k0 := 2 * xiR D
    minWeight_pos := by positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring }, h1, h2, h3, rfl⟩

theorem exists_lowerBound (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    ∃ B : ℝ, ∀ F ∈ T.C j w, (∀ la, ∀ v ∈ T.Vs j la, 0 ≤ v F) → F ≠ 0 →
      -B ≤ ∑ σ : T.Q.c.F →+* ℂ, Real.log (T.Ns j w σ F) := by
  classical
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.room_of_constants
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := (h.unf j hj T.σ₀ T.good_σ₀).1.symm
  have hf := GlobalTheory.WtSizes.fdeg_eq D
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hts := GlobalTheory.WtSizes.tot_le_size w
  have hwf : ∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size := fun k => by
    refine (Finset.sum_le_sum fun τ _ => GlobalTheory.WtSizes.spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast GlobalTheory.WtSizes.sum_cm_le ((T.U j T.σ₀).X k) (GlobalTheory.WtSizes.tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), hf, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  have hsz : ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) +
      ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
    refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => GlobalTheory.WtSizes.sum_wtA_le_tot w b _
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd4 : D.host.d % 4 = 3 := by
    have := T.Q.H.d_mod
    rw [h.pins.1.1] at this
    omega
  obtain ⟨_, χ, hχ, -⟩ := GlobalTheory.LamF.exists_kronecker_logOm_re D.host.E h.pins.1.1 hd4
  have g0 := (D.host.g_prime 0).pos
  have g1 := (D.host.g_prime 1).pos
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ((D.host.g 0 * D.host.g 1 * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hM : (0 : ℝ) < M := by
    rw [hMdef]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos g0 g1) (Nat.mul_pos hN hdpos)
  refine ⟨(C0 * ((fdeg D.host.E : ℝ) * D.R.r + |Real.log (M * (2 * xiR D))| + Real.log (dE D.host.E) +
    |(GlobalTheory.CM.logOm D.host.E χ).re|) ^ (2 : ℝ) * (1 + Real.log w.size) * w.size) *
      (Module.finrank ℚ T.Q.c.F : ℝ), fun F hFC hF hF1 => ?_⟩
  have hhol : rdU (T.U j T.σ₀) F ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) :=
    ((mem_cusp _ _ _ _ _ F).1 hFC).2 T.σ₀ T.good_σ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) hhol
  have hfin : supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) ≠ ⊤ :=
    supE_cusp_ne_top T.good_σ₀ hFC
  have hpos : 0 < supN (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
      (rdU (T.U j T.σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (h.supDef j hj (wtA w) w.n (dom_wtA w) T.σ₀ T.good_σ₀ F hFC heq.symm) hF1
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
    (rdU (T.U j T.σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k)
      (rdU (T.U j T.σ₀) F k) x ≤
      2 * ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 := by
    linarith
  obtain ⟨Xx, hX, hXg, hΛ, hk0⟩ := exists_dataX D T h j hj T.σ₀ T.good_σ₀ k
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← GlobalTheory.TransvModel.xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  have htr : ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ,
        (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b) := by
    rw [← hX]
    intro v hv hiso b hb hbi
    have := GlobalTheory.TransvModel.transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xx.toData hN hdpos D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hXg.trans h.pins.2.1.1, ← hMdef] at this
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((T.U j T.σ₀).X k) hX _ _ z0 M w.size (hSS k) hM
    (hwf k) w.one_le_size hr (fun v hv hvv b hb hbi => by
      obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
      exact ⟨γ, hγ, h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA w) k γ hγ, hγ'⟩) hz0 hhalf hposz
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * (2 * xiR D))| + 3 + Real.log (dE D.host.E) := by
    rw [hk0]
    have := le_abs_self (Real.log (M * (2 * xiR D)))
    have := abs_nonneg (Real.log (M * (2 * xiR D)))
    have := Real.log_nonneg hd1
    linarith
  obtain ⟨hLa1, hr'⟩ := hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) _ (GlobalTheory.CM.logOm D.host.E χ).re M Xx.k0 w.size
    hf1 hr Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos w.one_le_size hlog
  have hr'' := hr' _ _ (Nat.cast_nonneg _) (by positivity) hsz C0 2 le_rfl le_rfl
  have hNs : ∀ σ, IsNormOn (T.C j w) σ (T.Ns j w σ) := fun σ =>
    (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf
  have hSpos : ∀ σ, 0 < supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F := fun σ =>
    lt_of_le_of_ne ((hNs σ).nonneg F hFC) fun h0 => hF1 ((hNs σ).defin F hFC h0.symm)
  have h5 := GlobalTheory.LamT.meanLogSup_lowerBound D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D)
    (h.unf j hj) (h.xiAbs j hj) (by rw [hpq]; exact hr) χ hχ (wtA w) w.n (dom_wtA w) F hFC hF hSpos k ⟨x, hx⟩ Xx hX
    D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  have hf' : Module.finrank ℚ D.host.E / 2 = D.R.f := hf
  rw [hf'] at h5
  have hK : (0 : ℝ) < Module.finrank ℚ T.Q.c.F := by exact_mod_cast Module.finrank_pos
  rw [← neg_mul, ← le_div_iff₀ hK]
  refine le_trans ?_ h5
  linarith

theorem fg_latOf_of_lowerBound {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R) [FiniteDimensional K C]
    (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (N : (K →+* ℂ) → R → ℝ) (hN : ∀ σ, IsNormOn C σ (N σ)) (B : ℝ)
    (hB : ∀ F ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v F) → F ≠ 0 → -B ≤ ∑ σ : K →+* ℂ, Real.log (N σ F)) :
    (latOf C Vs hV).FG := by
  let Nf : TB.NormFam K C :=
    { N := fun σ F => N σ F
      nonneg := fun σ F => (hN σ).nonneg _ F.2
      eq_zero := fun σ F h0 => Subtype.ext ((hN σ).defin _ F.2 h0)
      smul := fun σ a F => (hN σ).smul a _ F.2
      add := fun σ F G => (hN σ).add _ F.2 _ G.2 }
  exact formalGroup_of_discriminant _ _ Nf _ (discriminant_of_product_lower _ _ Nf _ B fun F hF h0 =>
    hB F.1 F.2 hF fun h1 => h0 (Subtype.ext h1))

end GlobalTheory.IntCuspLat
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.IPbProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_b {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  have hx := L.sc.one_lt_alt
  have h0 : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith) _
  unfold Scale.b
  exact Real.one_le_exp h0

theorem La_le_three {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : L.La ≤ 3 * L.sc.L := by
  obtain ⟨hN, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have hx := L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.n_pos'
    exact_mod_cast this
  have hq : (1 : ℝ) ≤ (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.one_le
  have hd : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.one_le
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hb := one_le_b L
  have hnc : (D.R.n : ℝ) ≤ szCond L := by
    have h := D.host.four_ord_le_condN
    have h' : D.R.n ≤ D.host.QS * D.host.q * D.host.d := by rw [D.R.n_eq_ord]; omega
    unfold szCond; exact_mod_cast h'
  have hc1 : 1 ≤ szCond L := hn.trans hnc
  have hcb : szCond L ≤ L.sc.b := by
    have h1 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
    have h3 : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have h4 : szCond L ^ 36 ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) h2
    have h5 : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := hC
    linarith
  have hxn : L.sc.x ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    have he := L.sc.eps_pos
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by unfold szTh; linarith)
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hxb : L.sc.x ≤ L.sc.b := (hxn.trans hnc).trans hcb
  have hrb : D.host.rdE ≤ L.sc.b := (UpperTheory.Ram.Rd.rdE_le_cond D.host).trans hcb
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have l1 := Real.log_le_log (by linarith) hxb
  have l2 := Real.log_le_log (by linarith) hrb
  have hx0 : 0 < L.sc.x := by linarith
  have hr0 : 0 < D.host.rdE := by linarith
  have e : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a Scale.b
    rw [Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  linarith

end GlobalTheory.BigTop.Fun.IPbProof

namespace GlobalTheory.BigTop.Fun

open GlobalTheory.BigTop.Fun.IPbProof

end GlobalTheory.BigTop.Fun

end
end
