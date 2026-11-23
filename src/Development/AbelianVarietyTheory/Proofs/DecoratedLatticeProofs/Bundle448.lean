module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle422
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle424
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle434
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FinPl.SelfDualIdeal

variable {D : D7}
open GlobalTheory.FinPlLoc

theorem alg₁ {R : Type} [CommRing R] {u u' w w' e : R} (hU : u' * u = 1) (hC : w' * w = 1) (he : e * e = e)
    (c d h : R) : e * (c * d * h) = u * w * h * (u' * (e * d) * (w' * (e * c))) := by
  calc _ = (u' * u) * (w' * w) * (e * e) * (c * d * h) := by rw [hU, hC, he, one_mul, one_mul]
    _ = _ := by ring

theorem alg₂ {R : Type} [CommRing R] {u u' : R} (hU : u' * u = 1) (w e d h : R) :
    u * w * h * (u' * (e * d)) = d * h * (w * e) := by
  calc _ = (u' * u) * (d * h * (w * e)) := by ring
    _ = _ := by rw [hU, one_mul]

theorem alg₃ {R : Type} [CommRing R] {u u' e : R} (hU : u' * u = 1) (he : e * e = e) (d y : R) :
    e * (d * y) = u' * (e * d) * (y * (u * e)) := by
  calc _ = (u' * u) * (e * e) * (d * y) := by rw [hU, he, one_mul]
    _ = _ := by ring

theorem intAt_mul {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [RingHom.map_mul (finPart D) a b]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem cA_mem_intAt {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := congrArg (cA D) ((mem_idAt_iff _ a).1 ha.1)
  rw [RingHom.map_mul (cA D), cA_idem] at h
  exact (mem_idAt_iff _ _).2 h

theorem idem_mul_incA (P : Pl D → Prop) (y : D.host.E) :
    idem D P * incA D y = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] y := by
  rw [mul_comm, idem, GlobalTheory.IdVGen.incA_mul_tmul, mul_one]

theorem idem_mul_incA_mem {𝔞 : FI D} {c : D.host.E} (hc : c ∈ 𝔞) (v : Pl D) : idem D (· = v) * incA D c ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg hw], c, hc,
    idem_mul_incA _ c⟩

theorem mul_incA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    rw [GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

theorem mul_cA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * star c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * cA D s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    have e : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star c := rfl
    rw [e, GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [RingHom.map_zero, mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [RingHom.map_add (f := _), mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [RingHom.map_neg, mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

theorem exists_int_mul (y : D.host.E) : ∃ t : 𝓞 D.host.F, t ≠ 0 ∧ ∃ b : 𝓞 D.host.E,
    (b : D.host.E) = algebraMap D.host.F D.host.E (t : D.host.F) * y := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) (Rₘ := ℚ) y
    (Algebra.IsIntegral.isIntegral y)
  refine ⟨((m : ℤ) : 𝓞 D.host.F), Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero m), ⟨m • y, hm⟩, ?_⟩
  change (m : ℤ) • y = _
  simp [zsmul_eq_mul]

theorem one_eq_sum (T : Finset (Pl D)) :
    (1 : Af D.host.F) = ∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T) := by
  classical
  have key : ∀ w, evalV D.host.F w (1 : Af D.host.F) =
      evalV D.host.F w (∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T)) := by
    intro w

    rw [map_one, map_add (f := _), map_sum]
    simp only [evalV_ePl]
    by_cases hw : w ∈ T <;> simp [hw]
  exact RestrictedProduct.ext _ _ fun w => key w

theorem exists_integer_of_forall (y : D.host.E) (h : ∀ v : Pl D, idem D (· = v) * incA D y ∈ intAt D (· = v)) :
    ∃ b : 𝓞 D.host.E, (b : D.host.E) = y := by
  classical
  obtain ⟨t, ht0, b, hb⟩ := exists_int_mul y
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hfin := Ideal.finite_factors (I := Ideal.span {t}) (by simpa using ht0)
  have h1 : (1 : Af D.host.F) ⊗ₜ[D.host.F] y ∈ intAE D := by
    rw [one_eq_sum hfin.toFinset, TensorProduct.add_tmul, TensorProduct.sum_tmul]
    refine add_mem (sum_mem fun v _ => ?_) ?_
    · have := (h v).2
      rwa [idem_mul_incA, finPart_pair] at this
    · refine AddSubgroup.subset_closure ⟨(t : D.host.F)⁻¹ • ePl D (· ∉ hfin.toFinset), fun w => ?_, b, ?_⟩
      · rw [map_smul, evalV_ePl]
        by_cases hw : w ∈ hfin.toFinset
        · rw [if_neg (not_not.2 hw), smul_zero]; exact zero_mem _
        · rw [if_pos hw, Algebra.smul_def, mul_one]
          refine GlobalTheory.IdVGen.inv_mem_integers fun hm => hw ?_
          rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
          exact hm
      · rw [hb, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hF, one_smul]
  have h2 : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F ((1 : FI D) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 y).1 (h2 h1))

theorem idem_ne_zero (v : Pl D) : idem D (· = v) ≠ 0 := by
  intro h
  have := compAt_idem (· = v) v
  rw [h, if_pos rfl, RingHom.map_zero] at this
  exact zero_ne_one this

theorem selfDual_of_local : ∀ (D : D7) (h : D.host.E) (𝔞 : FI D) (u : (AE D)ˣ), (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ idV 𝔞 x ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) → (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (u : AE D) * cA D (u : AE D) * incA D h * a ∈ intAt D (· = x)) → ∀ d : D.host.E, d ∈ 𝔞 ↔ ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * h := by
  intro D h 𝔞 u H1 H2 d
  have hU : ((u⁻¹ : (AE D)ˣ) : AE D) * (u : AE D) = 1 := u.inv_mul
  have hC : cA D ((u⁻¹ : (AE D)ˣ) : AE D) * cA D (u : AE D) = 1 := by
    rw [← RingHom.map_mul (cA D), hU, RingHom.map_one]
  generalize ((u⁻¹ : (AE D)ˣ) : AE D) = u' at H1 hU hC
  generalize (u : AE D) = u at H2 hU hC
  have hue : ∀ v, u * idem D (· = v) ∈ idV 𝔞 v := fun v =>
    (H1 v _ (Ideal.mul_mem_left _ _ (idem_mem_idAt _))).2 (by rw [← mul_assoc, hU, one_mul]; exact idem_mem_intAt _)
  have loc : ∀ v, ∀ x ∈ 𝔞, u' * (idem D (· = v) * incA D x) ∈ intAt D (· = v) := fun v x hx =>
    (H1 v _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _))).1 (idem_mul_incA_mem hx v)
  constructor
  · intro hd c hc
    refine exists_integer_of_forall _ fun v => ?_
    have h3 := intAt_mul (loc v d hd) (cA_mem_intAt (loc v c hc))
    have h4 := (H2 v _ h3.1).1 h3
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (cA D), RingHom.map_mul (cA D), cA_idem, GlobalTheory.FinPl.FrameLat.cA_incA] at h4
    rw [RingHom.map_mul (incA D), RingHom.map_mul (incA D), alg₁ hU hC he]
    exact h4
  · intro hd
    have h𝔞 : 𝔞 ≠ 0 := by
      rintro rfl
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : Pl D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      have h0 := hue v
      rw [idV_zero, AddSubgroup.mem_bot] at h0
      apply idem_ne_zero v
      rw [← one_mul (idem D (· = v)), ← hU, mul_assoc, h0, mul_zero]
    have s1 : ∀ v, u' * (idem D (· = v) * incA D d) ∈ intAt D (· = v) := by
      intro v
      have hc := mul_cA_mem (y := d * h) (fun c hc => by
        obtain ⟨b, hb⟩ := hd c hc
        exact ⟨b, by rw [hb]; ring⟩) (hue v)
      refine (H2 v _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _)))).2 ?_
      rw [RingHom.map_mul (cA D), cA_idem, RingHom.map_mul (incA D)] at hc
      rw [alg₂ hU]; exact hc
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff (inv_ne_zero h𝔞)]
    intro y hy
    refine (FractionalIdeal.mem_one_iff _).2 (exists_integer_of_forall _ fun v => ?_)
    have t := mul_incA_mem (y := y) (fun c hc =>
      (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff h𝔞).1 hy c hc)) (hue v)
    have h5 := intAt_mul (s1 v) t
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (incA D), alg₃ hU he]
    exact h5

end GlobalTheory.FinPl.SelfDualIdeal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_scaledLatticeCompletion_iff_polarisationInverse : ∀ (D : D7) (v : Pl D) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  first | exact @GlobalTheory.SeeSaw.mem_latA_iff_mul_inv | exact GlobalTheory.SeeSaw.mem_latA_iff_mul_inv | (intros; apply GlobalTheory.SeeSaw.mem_latA_iff_mul_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fractionalIdealCompletion_locally_principal : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ x : D.host.E, x ≠ 0 ∧ ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  first | exact @GlobalTheory.IdVGen.idV_gen | exact GlobalTheory.IdVGen.idV_gen | (intros; apply GlobalTheory.IdVGen.idV_gen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.rowLineIdeal_eq_inverseDifferent_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow | exact GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow | (intros; apply GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nonzero_jetScale_trueColumns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∃ s, JetS I l Z ψ θ s := by
  first | exact @GlobalTheory.AdForm.JetScales.exists_jetS | exact GlobalTheory.AdForm.JetScales.exists_jetS | (intros; apply GlobalTheory.AdForm.JetScales.exists_jetS <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_translates_of_values_frames : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  first | exact @GlobalTheory.AdForm.jOf_exists | exact GlobalTheory.AdForm.jOf_exists | (intros; apply GlobalTheory.AdForm.jOf_exists <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  first | exact @GlobalTheory.TrueBranch.branching_true_columns | exact GlobalTheory.TrueBranch.branching_true_columns | (intros; apply GlobalTheory.TrueBranch.branching_true_columns <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Inhab

open GlobalTheory.SymBridge

section Frames

variable {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

def stdFr (k : Type) [Field k] (e : Y ≃ Fin N) : GlobalTheory.LocMod.Frame k N Y where
  β := (1 : Matrix (Fin N) (Fin N) k).submatrix id e
  γ := (1 : Matrix (Fin N) (Fin N) k).submatrix e id
  βγ := by rw [Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]
  γβ := by
    have h := Matrix.submatrix_mul_equiv (1 : Matrix (Fin N) (Fin N) k) (1 : Matrix (Fin N) (Fin N) k) e (Equiv.refl _) e
    rw [Matrix.one_mul, Matrix.submatrix_one_equiv] at h
    exact h

theorem isStdFr_stdFr {pos : Y → ℕ} {e : Y ≃ Fin N} (h : IsOrd pos e) : IsStdFr pos (stdFr k e) := ⟨e, h, rfl⟩

def blockOrd (κ τ l j : ℕ) : (Fin κ ⊕ Fin l) ⊕ Fin j × Fin τ ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem isOrd_xPos (κ τ j : ℕ) : IsOrd (xPos (κ := κ) (τ := τ) (j := j)) (blockOrd κ τ j j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, xPos, finProdFinEquiv]
  ring

theorem isOrd_zPos (κ τ l j : ℕ) : IsOrd (zPos (κ := κ) (τ := τ) (l := l) (j := j)) (blockOrd κ τ l j) := by
  rintro ((i | i) | ⟨a, b⟩) <;> simp [blockOrd, zPos, finProdFinEquiv]
  ring

end Frames

section True

open GlobalTheory.Mem

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end True

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) {Rc : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} (y : RealIn a.x Rc S)

end Built

end GlobalTheory.Fam.Inhab

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TopTranslate

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift

theorem infM_eq_reindex {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = (infMat D.sp.cm.sig V.gram (θ τ) g).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

theorem infPt_eq_infM {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    ((infPt θ x τ : GL _ ℂ) : Matrix _ _ ℂ) = infM θ D.sp.X' (rankP D) x τ := by
  rw [infM_eq_reindex]
  exact GlobalTheory.Core.Rk.TopOnto.infN_eq (rankP D) x τ

theorem infPt_mul_inv {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    (infPt θ x τ).1 * (infPt θ x⁻¹ τ).1 = 1 := by
  rw [← Units.val_mul, ← Pi.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem top_translate : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w _ UT ε _ bad K eW _ _ hbT _ _ h hh G' hG' f v c x hx
  obtain ⟨v', e1, e2⟩ := GlobalTheory.Core.Rk.TopOnto.real_translate (J := levS _ R.βX (datXP R P t))
    (χ := levChi _ R.βX (datXP R P t)) hX.inf hj x hx v
  have ex : h c * x * g.bT = h c * g.bT * x := by
    rw [mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem _ hx hbT, ← mul_assoc]
  have key : j v' = fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩ := by
    funext y
    have h1 : j v' y = j v (frL _ (infPt R.θ x⁻¹) y) := by
      rw [← e1, lT_apply]
      refine congrArg (j v') (Subtype.ext (funext fun τ => ?_))
      show y.1 τ = _ * (_ * y.1 τ)
      rw [← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
    rw [h1]
    refine (hJ v x hx ⟨(frL _ (infPt R.θ x⁻¹) y).1, (frL _ (infPt R.θ x⁻¹) y).2⟩ ⟨y.1, y.2⟩ fun τ => ?_).symm
    show y.1 τ = infM R.θ _ (rankP (I.rec7 l Z)) x τ * (_ * y.1 τ)
    rw [← infPt_eq_infM, ← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
  rw [ex, ← e2 f.1 f.2 (h c * g.bT), hG' f c v' (h c) (hh c), key]

end GlobalTheory.AdForm.TopTranslate

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergCombination_eq_on_vacua_of_eq_one : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ c₁ c₂ : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P c₁ → GlobalTheory.FinPl.CombAt P c₂ → ∀ f₀, GlobalTheory.FinPl.Vac ψ S T LS LT P f₀ → f₀ ≠ 0 → comb ψ S T c₁ f₀ = comb ψ S T c₂ f₀ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → comb ψ S T c₁ f = comb ψ S T c₂ f := by
  first | exact @GlobalTheory.FinPl.Transfer.comb_eq_on_vacua | exact GlobalTheory.FinPl.Transfer.comb_eq_on_vacua | (intros; apply GlobalTheory.FinPl.Transfer.comb_eq_on_vacua <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.type_places_split_idempotents : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ PP ∈ (pk W).Pg, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) = GlobalTheory.FinPl.latV V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := by
  first | exact @GlobalTheory.LevelPlaces.split_unit | exact GlobalTheory.LevelPlaces.split_unit | (intros; apply GlobalTheory.LevelPlaces.split_unit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_self_dual_lattice_chain : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∃ L : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) L := by
  first | exact @GlobalTheory.SDLatY.exists_selfDual_latY | exact GlobalTheory.SDLatY.exists_selfDual_latY | (intros; apply GlobalTheory.SDLatY.exists_selfDual_latY <;> assumption)
end
