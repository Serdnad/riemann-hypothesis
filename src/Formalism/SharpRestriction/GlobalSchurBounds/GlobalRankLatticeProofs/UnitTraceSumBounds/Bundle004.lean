module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AddPtW
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLatticeHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle003
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle014
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

noncomputable def conjK : D.host.K →+* D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)

theorem conjK_coe (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x

noncomputable def tauKp : D.host.K →+* ℂ_[p] :=
  lam.comp ((D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun _ => test_vector_mem_schwartz_bruhat D _))

theorem tauKp_apply (x : D.host.K) : tauKp D lam x = lamC lam (D.host.φ₀ (x : D.host.E)) := by
  unfold tauKp lamC
  first
  | rfl
  | (simp [test_vector_mem_schwartz_bruhat]; done)
  | (rw [dif_pos (test_vector_mem_schwartz_bruhat D _)]; rfl)

end Formalism.MainNotions.Ext
end

section

namespace Formalism.MainNotions.Ext

theorem addPtW_holds : AddPtW :=
  fun p _ g hOk hF σ a b ha hb =>
    formal_group_add_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF σ a b ha hb

theorem mulPtW_holds : MulPtW :=
  fun p _ g hOk c hc σ a ha =>
    formal_group_mul_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 c hc σ a ha

end Formalism.MainNotions.Ext
end

section

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ :=
  lamOf_lat idealLattice_holds D cc hc δ hδ

theorem delta_ne_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne' idealLattice_holds D cc hc δ hδ

theorem sgStar_spec (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Differentiable ℂ (sgStar (lamOf D cc δ)) ∧ deriv (sgStar (lamOf D cc δ)) 0 = 1 ∧
      (∀ z, sgStar (lamOf D cc δ) (-z) = -sgStar (lamOf D cc δ) z) := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat_holds D cc hc δ (delta_ne_holds D cc hc δ hδ)
  have h := sigmaStarEx_holds w₁ w₂ hw
  rw [hL]
  unfold sgStar
  have hs := Classical.epsilon_spec h
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem area_lamOf (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(NumberField.discr D.host.K : ℝ)| / 2 := by
  have h := idealLattice_holds D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
    (Formalism.MainNotions.Ext.finrank_K D.host) (Formalism.MainNotions.Ext.no_real_K D.host) cc δ hc hδ
  exact h.2

end Formalism.MainNotions.Ext
end

section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

def EPhiOne (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1

def PAdicSigmaAdditionFormula (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) *
        PowerSeries.subst (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) *
        PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) =
      ((Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2

theorem addition_identity_of_sigma_formula (H31 : UnitTraceSumSecondBound) (HC : CubeIdentityFromAdditionFormula) (D : D7) (hQ : PAdicSigmaAdditionFormula D) (hE : EPhiOne D) (ha : addInt D) :
    cube2 D := by
  intro p _ cc δ g hA
  have ok : g.Ok := hA.2.2.2.2
  exact HC p g ok (hE p cc δ g hA) (hQ p cc δ g hA) (H31 p g ok (ha p cc δ g hA).1)

end Formalism.MainNotions.Ext.CutA
end

section

namespace Formalism.MainNotions.Ext

theorem biaddOfCube_holds : BiaddOfCube :=
  fun p _ g hOk hc => biadditiveOfCube_holds p g.l g.ex g.ph hOk.2.2.1 hOk.2.2.2 hc

theorem beBiadd_of_cube (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.GL3Theta.cube D) : Formalism.MainNotions.GL3Theta.beBiadd D := by
  intro p _ cc δ g hA
  exact biaddOfCube_holds p g hA.2.2.2.2 (h p cc δ g hA)

theorem addIntG_holds : AddIntG := fun p _ g hOk =>
  additive_integral_generation p g.W g.wq g.ex hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1 hOk.2.2.2

theorem addInt_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.addInt D := by
  intro p _ cc δ g hA
  exact addIntG_holds p g hA.2.2.2.2

end Formalism.MainNotions.Ext
end

section

namespace Formalism.MainNotions.Ext.CutA

theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

end Formalism.MainNotions.Ext.CutA
end

section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext

def OkpSwap (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, α.swap ∈ OKp D lam

def OkpTrace (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, ∃ n : ℤ_[p], α.1 + α.2 = zc n

def OkpNeg (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((-1 : ℂ_[p]), (-1 : ℂ_[p])) ∈ OKp D lam

def OkpTwo (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ OKp D lam

def OkpDiff (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 →
    ∃ α ∈ OKp D lam, ‖α.1 - α.2‖ = if p = D.host.d then ((p : ℝ) ^ ((1 : ℝ) / 2))⁻¹ else 1

theorem okpSwap_holds (D : D7) : OkpSwap D := by
  intro p _ lam α hα
  have hsq : D.host.conj D.host.sqd ∈ D.host.K := by
    rw [Formalism.HC.HostRaw.conj_sqd]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hK : ∀ x ∈ D.host.K, D.host.conj x ∈ D.host.K := by
    intro x hx
    have hle : (D.host.K).map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) ≤ D.host.K := by
      show (IntermediateField.adjoin ℚ {D.host.sqd}).map
        (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) ≤ D.host.K
      rw [IntermediateField.adjoin_map, Set.image_singleton,
        IntermediateField.adjoin_simple_le_iff]
      exact hsq
    exact hle ((IntermediateField.mem_map _).2 ⟨x, hx, rfl⟩)
  have hint : ∀ a : NumberField.RingOfIntegers D.host.K, IsIntegral ℤ (D.host.conj ((a : D.host.K) : D.host.E)) := by
    intro a
    have h0 : IsIntegral ℤ ((a : D.host.K) : D.host.E) :=
      (NumberField.RingOfIntegers.isIntegral_coe a).map ((D.host.K).val.restrictScalars ℤ)
    exact h0.map ((D.host.conj : D.host.E →ₐ[ℚ] D.host.E).restrictScalars ℤ)
  have key : ∀ a : NumberField.RingOfIntegers D.host.K, ∃ b : NumberField.RingOfIntegers D.host.K,
      ((b : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    intro a
    have hy : IsIntegral ℤ
        (⟨D.host.conj ((a : D.host.K) : D.host.E), hK _ (a : D.host.K).2⟩ : D.host.K) :=
      (isIntegral_algHom_iff ((D.host.K).val.restrictScalars ℤ)
        (fun x y h => Subtype.ext h)).1 (hint a)
    exact ⟨⟨⟨D.host.conj ((a : D.host.K) : D.host.E), hK _ (a : D.host.K).2⟩, hy⟩, rfl⟩
  have hmaps : Set.MapsTo Prod.swap
      (Set.range fun a : NumberField.RingOfIntegers D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)))
      (Set.range fun a : NumberField.RingOfIntegers D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K))) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := key a
    refine ⟨b, ?_⟩
    simp only [Prod.swap_prod_mk, tauK, tauKc, hb, Formalism.HC.HostRaw.conj_conj]
  unfold OKp at hα ⊢
  exact map_mem_closure continuous_swap hα hmaps

theorem okpNeg_holds (D : D7) : OkpNeg D := by
  intro p _ lam
  have hQ : (-1 : ℂ) ∈ Qbar := neg_mem (one_mem _)
  have hl : lamC lam (-1 : ℂ) = -1 := by
    unfold lamC
    rw [dite_eq_left hQ]
    have e : (⟨-1, hQ⟩ : Qbar) = -1 := Subtype.ext (by first | rfl | simp | norm_num)
    rw [e, map_neg, map_one]
  have hc : D.host.conj (-1 : D.host.E) = -1 := by simp
  unfold OKp
  refine subset_closure ⟨-1, ?_⟩
  simp [tauK, tauKc, hc, hl]

theorem okpTwo_holds (D : D7) : OkpTwo D := by
  intro p _ lam
  have hQ : (2 : ℂ) ∈ Qbar := by
    first
      | norm_num
      | simp
      | (have h := add_mem (one_mem Qbar) (one_mem Qbar); rwa [one_add_one_eq_two] at h)
  have hl : lamC lam (2 : ℂ) = 2 := by
    unfold lamC
    rw [dite_eq_left hQ]
    have e : (⟨2, hQ⟩ : Qbar) = 1 + 1 := Subtype.ext (by
      first
        | (show (2 : ℂ) = ((1 : Qbar) : ℂ) + ((1 : Qbar) : ℂ); norm_num)
        | (push_cast; norm_num)
        | rfl)
    rw [e, map_add (f := _), map_one] <;> norm_num
  have hc : D.host.conj (2 : D.host.E) = 2 := by
    first
      | (rw [show (2 : D.host.E) = 1 + 1 by norm_num, map_add (f := _), map_one])
      | exact map_ofNat _ 2
  have hz : (((2 : NumberField.RingOfIntegers D.host.K) : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : NumberField.RingOfIntegers D.host.K) = 1 + 1 by norm_num]
    first
      | (push_cast; norm_num)
      | simp
      | norm_num
  have hφ : D.host.φ₀ (2 : D.host.E) = 2 := by
    first
      | (rw [show (2 : D.host.E) = 1 + 1 by norm_num, map_add (f := _), map_one]; norm_num)
      | simp
  unfold OKp
  refine subset_closure ⟨2, ?_⟩
  simp only [tauK, tauKc, hz, hc, hφ, hl, Prod.mk.injEq, and_self]

theorem cube_of (H : CubeOfTwoIdentities) (D : D7) (h2 : cube2 D) (h3 : cube3 D) : cube D := by
  intro p _ cc δ g hA
  exact H p g hA.2.2.2.2 (h2 p cc δ g hA) (h3 p cc δ g hA)

theorem jetsPh_of (HH : JetsHigh) (H1 : JetsOne) (H2 : JetsTwo) (D : D7) (hc : cube D) (hn : phNorm D)
    (hb : beConj D) (hdf : OkpDiff D) : jetsPh D := by
  intro p _ cc δ g hA hp
  have hok := hA.2.2.2.2
  obtain ⟨α₀, hα₀, hnorm⟩ := hdf p g.lam hp
  have hprod : ‖(α₀.1 - α₀.2) * g.jetPh 2‖ ≤ 1 :=
    H2 p g α₀.1 α₀.2 hok (hb p cc δ g hA hp α₀ hα₀)
  rw [norm_mul] at hprod
  refine ⟨fun i hi2 => ?_, fun α hα => H2 p g α.1 α.2 hok (hb p cc δ g hA hp α hα),
    fun hpd => ?_, fun hpd => ?_⟩
  · by_cases hi1 : i = 1
    · subst hi1
      have hn1 := hn p cc δ g hA hp ((-1 : ℂ_[p]), (-1 : ℂ_[p])) (okpNeg_holds D p g.lam)
      have hm : ((-1 : ℂ_[p]), (-1 : ℂ_[p])).1 * ((-1 : ℂ_[p]), (-1 : ℂ_[p])).2 = 1 := by
        norm_num
      rw [hm, map_one, one_mul] at hn1
      exact H1 p g hok hp hn1
    · exact HH p g hok (hc p cc δ g hA) i hi1 hi2
  · rw [if_neg hpd] at hnorm
    rw [hnorm, one_mul] at hprod
    exact hprod
  · rw [if_pos hpd] at hnorm
    rw [hnorm] at hprod
    have hpos : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
    have h3 := mul_le_mul_of_nonneg_left hprod hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_one] at h3
    exact h3


end Formalism.MainNotions.Ext.CutA
end
