module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle613
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle269
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle570
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle615
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.OffIdemLat

open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

variable {D : D7}

abbrev conjProd (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) := ∏ PP ∈ SS, conjI PP.asIdeal

theorem cP_mem_of_le {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (h : conjProd SS ≤ Q.asIdeal) : cP Q ∈ SS := by
  obtain ⟨PP, hPP, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have : PP = cP Q := eq_of_le fun x hx => by
    rw [mem_cP]
    exact hle (Ideal.subset_span ⟨x, hx, rfl⟩)
  exact this ▸ hPP

theorem conjProd_ne_bot (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) : conjProd SS ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
  rw [Ne, Ideal.zero_eq_bot, GlobalTheory.LiftIdeal.conjI_eq_map,
    Ideal.map_eq_bot_iff_of_injective (f := (GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
      (GlobalTheory.LiftIdeal.conjO D).injective]
  exact PP.ne_bot

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen
variable {D : D7}

theorem finPart_mul_mem (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e SS) (x : D.host.E)
    (hx : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E)) :
    finPart D ((1 - e - cA D e) * incA D x) ∈ intAE D := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hd : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hd P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  by_cases hQ : Q ∈ SS ∨ cP Q ∈ SS
  · have h0 : Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
      rw [hO]
      rcases hQ with hQ | hQ
      · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
          rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hd P hP).2.2 Q (Ne.symm hne))
            (fun h => absurd hQ h), (hd Q hQ).2.1]
        have h2 := hprod Q
        rw [h1, one_mul] at h2
        rw [h1, h2, sub_self, sub_zero]
      · have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
          rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
              rw [h, cP_cP])))
            (fun h => absurd hQ h)]
          have := (hdc (cP Q) hQ).2.1
          rwa [cP_cP] at this
        have h2 := hprod Q
        rw [h1, mul_one] at h2
        rw [h1, h2, sub_zero, sub_self]
    rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · push_neg at hQ
    refine mul_mem ?_ ?_
    · rw [hO, hE, hC]
      exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
        (sum_mem fun P hP => delta_mem (hd P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
    · have hnle : ¬ conjProd SS ≤ Q.asIdeal := fun h => hQ.2 (cP_mem_of_le h)
      obtain ⟨j, hj, hjQ⟩ := Set.not_subset.1 hnle
      obtain ⟨o, ho⟩ := hx j hj
      have hj0 : j ≠ 0 := fun h => hjQ (h ▸ zero_mem _)
      have hj0' : ((j : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hj0 (RingOfIntegers.ext (h.trans rfl))
      have hxe : x = (o : D.host.E) * ((j : D.host.E))⁻¹ := by
        rw [ho, mul_assoc, mul_inv_cancel₀ hj0', mul_one]
      have hinv := (inv_mem_iff Q hj0).2 hjQ
      have ho' : algebraMap D.host.E (Q.adicCompletion D.host.E) (o : D.host.E) ∈
          Q.adicCompletionIntegers D.host.E := HeightOneSpectrum.coe_mem_adicCompletionIntegers Q o
      change algebraMap D.host.E (Q.adicCompletion D.host.E) x ∈ Q.adicCompletionIntegers D.host.E
      rw [hxe, map_mul]
      exact mul_mem ho' hinv

end GlobalTheory.OffIdemLat

namespace GlobalTheory.OffIdemLat
open GlobalTheory.IdemSupport
variable {D : D7}

theorem fin_smul_mem {S T : HSp D} {J : Ideal (𝓞 D.host.E)} {M N : Lt D.host.E T.rank} (hMN : J • M ≤ N)
    {j : 𝓞 D.host.E} (hj : j ∈ J) {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) M)) :
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N) := by
  refine GlobalTheory.Ker.SignVac.hatA_induction (p := fun u => (pairA D.host.F 0 1 ⊗ₜ[D.host.F]
      ((j : 𝓞 D.host.E) : D.host.E) : AE D) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N)) ?_ ?_ ?_ ?_ hu
  · intro α hα y hy
    rw [GlobalTheory.LatVac.tmul_smul_finTens, one_mul, ← Matrix.transpose_smul]
    exact GlobalTheory.Ker.SignVac.finTens_mem hα
      (GlobalTheory.LiftLevel.smul_mem_tens _ (fun v hv => hMN (Submodule.smul_mem_smul hj hv)) hy)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem partAt_off_mem : ∀ (D : D7) (S T : HSp D) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (M N : Lt D.host.E T.rank), (∏ PP ∈ SS, conjI PP.asIdeal) • M ≤ N → ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) M), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
  intro D S T e SS he M N hMN u hu
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens (stdL D.host.E S.rank) N,
      (o : D.host.E) • y ∈ tens (stdL D.host.E S.rank) N :=
    fun o y hy => GlobalTheory.LiftLevel.smul_mem_tens o (fun v hv => Submodule.smul_mem _ o hv) hy
  have hJ : ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (conjProd_ne_bot SS)
  have h1 : (1 : D.host.E) ∈ ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      ((conjProd SS : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    rw [mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have key : ((1 - e - cA D e) * incA D 1) • u ∈ hatA S T (tens (stdL D.host.E S.rank) N) := by
    refine FractionalIdeal.mul_induction_on (C := fun z => ((1 - e - cA D e) * incA D z) • u ∈
      hatA S T (tens (stdL D.host.E S.rank) N)) h1 ?_ ?_
    · intro i hi x hx
      obtain ⟨i', hi', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
      have hxJ : ∀ j ∈ conjProd SS, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (j : D.host.E) := by
        intro j hj
        obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hJ).1 hx
          (algebraMap (𝓞 D.host.E) D.host.E j) ((FractionalIdeal.mem_coeIdeal _).2 ⟨j, hj, rfl⟩))
        exact ⟨o, ho⟩
      have hint := finPart_mul_mem e SS he x hxJ
      have e1 : ((1 - e - cA D e) * incA D (algebraMap (𝓞 D.host.E) D.host.E i' * x)) • u =
          ((1 - e - cA D e) * incA D x) •
            (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) • u := by
        have e2 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E) : AE D) =
            incA D ((i' : 𝓞 D.host.E) : D.host.E) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          change _ = ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((i' : 𝓞 D.host.E) : D.host.E)) * _
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [e2, mul_smul (incA D ((i' : 𝓞 D.host.E) : D.host.E)), GlobalTheory.Ker.SignVac.one_smul_hatA hu, smul_smul,
          mul_assoc, ← map_mul, mul_comm x]
      rw [e1]
      exact GlobalTheory.LiftLevel.smul_mem_hatA_of_int hA hint (fin_smul_mem hMN hi' hu)
    · intro x y hx hy
      rw [map_add (f := _), mul_add, add_smul]
      exact add_mem hx hy
  rw [map_one, mul_one] at key
  rw [GlobalTheory.LiftLevel.partAt_eq_smul]
  exact key

end GlobalTheory.OffIdemLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacCoef

theorem frameLat_eq_latFrame {D : D7} (V : HSp D) : frameLat V = GlobalTheory.PlaceModel.latFrame V := by
  ext y; rw [mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  rw [frameLat_eq_latFrame]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem isUnram_host (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := by
  have hu : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := D.host.isCMField_hostE
    exact GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  rw [GlobalTheory.LFun.isUnram_iff]
  intro P hP
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 hu ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have hv : P.asIdeal.under (𝓞 D.host.F) = v.asIdeal := by rw [← hP]; rfl
  have : P.asIdeal.LiesOver v.asIdeal := ⟨hv.symm⟩
  rw [hv] at h1
  rwa [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal _ v.ne_bot] at h1

theorem exists_place (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v ∧
      (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w) := by
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (isUnram_host D v) with hs | ⟨w, hw⟩
  · obtain ⟨w, -, -, h, -⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨w, h, fun h' => absurd hs h'⟩
  · exact ⟨w, GlobalTheory.LFun.under_eq_of_isInertAt hw, fun _ => hw⟩

theorem val_inert (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (hr : ResEta D χ n)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : IsInertAt D.host.F D.host.E v w) (hu : UnrAt χ w) : val χ w = (-1) ^ n :=
  GlobalTheory.LFun.ResEta.val_of_isInertAt (isCMExt_host D).2.2.1 hr hw hu

theorem l2_smul {D : D7} {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (c : ℂ) (f g : WO S T → ℂ) :
    l2 μ 𝓕 (c • f) g = c * l2 μ 𝓕 f g := by
  simp [l2, Formalism.IndefR.Lift.pet, mul_assoc, integral_const_mul]

theorem locChar_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (lam : ℕ →* ℂ)
    (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T))
    (hL : GlobalTheory.FinWeilO.IsLatRep hom.std.1 (frameLat S) (frameLat T) w₀ lam Om)
    (hlam : GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam)
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hs : IsSplit (E := D.host.E) v) {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v) (a : Gv T v) :
    ((locChar χS w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h a)) : ℂˣ) : ℂ) =
      ((locChar χS w' (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h' a)) : ℂˣ) : ℂ) := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hom.std S T
  let g : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f, hf⟩
  have e1 := (GlobalTheory.T.weilDatum_at_place_eq_latticeIntertwiner_mul_det_char D ψ S T χS χT om hom hom.std lam w₀ Om hL hlam hsq v w h a g).1 hs
  have e2 := (GlobalTheory.T.weilDatum_at_place_eq_latticeIntertwiner_mul_det_char D ψ S T χS χT om hom hom.std lam w₀ Om hL hlam hsq v w' h' a g).1 hs
  have hne : (Om (1, embV T v a) g : WO S T → ℂ) ≠ 0 := by
    intro h0
    have h3 : Om (1, embV T v a)⁻¹ (Om (1, embV T v a) g) = g := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have h1 : Om (1, embV T v a) g = 0 := Subtype.ext h0
    rw [h1, map_zero] at h3
    exact f0 (congrArg Subtype.val h3).symm
  exact smul_left_injective ℂ hne (e1.symm.trans e2)

theorem detval : ∀ (D : D7) (T : HSp D) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), UnrAt χ w → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ((locChar χ w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)))) : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ (∑ i, d i) := GlobalTheory.T.localHeckeChar_det_doubleCoset_splitPlace

theorem lamsplit : ∀ (D : D7) (lam : ℕ →* ℂ), (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ m : ℕ, lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := GlobalTheory.T.split_place_eigenvalue_is_sqrt_norm

theorem laminert : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := GlobalTheory.T.indexNormalization_inert_norm_eq_neg

theorem inv_neg_pow_mul (x : ℂ) (N M : ℕ) :
    ((-x) ^ (N * M))⁻¹ = ((((-1 : ℂˣ) ^ N : ℂˣ) : ℂ) * (x ^ N)⁻¹) ^ (M : ℤ) := by
  rw [zpow_natCast, pow_mul, ← inv_pow, neg_pow, mul_inv, ← inv_pow (-1 : ℂ), inv_neg_one]
  push_cast
  rfl

theorem vac_coef : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χS w ∧ UnrAt χT w) → ∃ φ : Gv T v → ℂ, IsLocKer T S.rank (val χS) v φ ∧ ∀ (a : Gv T v) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → l2 μ 𝓕 (om (1, embV T v a) f₁) f₂ = φ a * l2 μ 𝓕 f₁ f₂ := by
  intro D ψ S T χS χT om hom μ 𝓕 hμ v hunr
  classical
  have hψ := hom.std
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w₀, Om, hL⟩ := GlobalTheory.FinWeilO.exists_isLatRep hψ (isSelfDualC_frameLat S) (isSelfDualC_frameLat T) hlam
  obtain ⟨w₁, hw₁, hin₁⟩ := exists_place D v
  let I : Gv T v → ℕ := fun a => GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
    ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v a)))
  let ν : Gv T v → ℂ := fun a => if IsSplit (E := D.host.E) v then
    ((locChar χS w₁ (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram hw₁ a)) : ℂˣ) : ℂ) else 1
  refine ⟨fun a => ν a * (lam (I a))⁻¹, fun w h => ⟨fun hs e he => ?_, fun hw c ϖ e hϖ he => ?_⟩,
    fun a f₁ f₂ h₁ h₂ => ?_⟩
  · intro ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
    have hν : ν (e.symm (k₁ * t * k₂)) = ((val χS w : ℂˣ) : ℂ) ^ (∑ i, d i) := by
      simp only [ν, if_pos hs]
      rw [locChar_eq hom lam w₀ Om hL hlam hsq hs hw₁ h]
      exact detval D T χS v w h (hunr w h).1 e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
    have hI : I (e.symm (k₁ * t * k₂)) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) :=
      GlobalTheory.T.index_movedHomLattice_splitPlaceChart D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
    show ν _ * (lam (I _))⁻¹ = _
    rw [hν, hI, lamsplit D lam hsq v w h hs]
    congr 1
    have hs0 : 0 ≤ ∑ i, |d i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hM : ((∑ i, |d i| : ℤ) : ℂ) = (((∑ i, |d i|).toNat : ℕ) : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hs0).symm
    rw [hM]
    generalize (∑ i, |d i|).toNat = M
    rw [Real.sqrt_eq_rpow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  · intro d t ht k₁ hk₁ k₂ hk₂
    have hns : ¬ IsSplit (E := D.host.E) v := not_isSplit_of_isInertAt hw
    have hν : ν (e.symm (k₁ * t * k₂)) = 1 := if_neg hns
    have hI : I (e.symm (k₁ * t * k₂)) = qV D.host.E w ^ (S.rank * (∑ i, max (d i) 0).toNat) :=
      GlobalTheory.T.index_moved_homLattice_inertPlace D S T v w h hw c ϖ e hϖ he d t ht k₁ hk₁ k₂ hk₂
    have hval := val_inert D χS S.rank hom.resS v w hw (hunr w h).1
    have hq := laminert D lam hlam v w hw
    show ν _ * (lam (I _))⁻¹ = _
    rw [hν, hI, map_pow, hq, hval, one_mul]
    have hs0 : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    rw [← Int.toNat_of_nonneg hs0, zpow_natCast]
    generalize (∑ i, max (d i) 0).toNat = M
    clear hs0 hq hval hI hν hns hk₁ hk₂ ht
    exact inv_neg_pow_mul _ _ _
  · have hf₁ : IsThetaFunO ψ S T f₁ := h₁.1
    have hf₂ : IsThetaFunO ψ S T f₂ := h₂.1
    let g₁ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₁, hf₁⟩
    let g₂ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₂, hf₂⟩
    have hc := GlobalTheory.T.weil_latticeIntertwiner_coefficient_at_place D ψ S T hψ lam w₀ Om hL μ 𝓕 hμ v a g₁ g₂ h₁ h₂
    have hn := GlobalTheory.T.weilDatum_at_place_eq_latticeIntertwiner_mul_det_char D ψ S T χS χT om hom hψ lam w₀ Om hL hlam hsq v w₁ hw₁ a g₁
    show l2 μ 𝓕 (om (1, embV T v a) (g₁ : WO S T → ℂ)) (g₂ : WO S T → ℂ) =
      (ν a * (lam (I a))⁻¹) * l2 μ 𝓕 (g₁ : WO S T → ℂ) (g₂ : WO S T → ℂ)
    by_cases hs : IsSplit (E := D.host.E) v
    · rw [hn.1 hs, l2_smul, hc]
      simp only [ν, if_pos hs, I]
      ring
    · rw [hn.2 (hin₁ hs) (hunr w₁ hw₁).1 (hunr w₁ hw₁).2, hc]
      simp only [ν, if_neg hs, I]
      ring

end GlobalTheory.VacCoef
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.shiftedTensorLatticePart_mem_liftLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (cA D e) u ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  first | exact @GlobalTheory.LiftLevel.partAt_mem_liftL | exact GlobalTheory.LiftLevel.partAt_mem_liftL | (intros; apply GlobalTheory.LiftLevel.partAt_mem_liftL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar




noncomputable section

namespace GlobalTheory.LiftLevel

theorem partAt_finW_mem_hatA_sh : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  intro D S T C Pg Q e he Lv hLv y hy

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hPQ : (Pg ∪ Q).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply Lv.proper
    rw [hLv, liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPQ
    intro h
    apply htP PP hPP
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _

  have hsub : conjI Lv.𝔪 • C.X.Λ ≤ C.X.Λ := Submodule.smul_le_right
  have htL : ∀ v ∈ conjI Lv.𝔪 • C.X.Λ, t • v ∈ Lv.sh C.X.Λ := by
    intro v hv s hs
    have hv' : t • v ∈ Lv.𝔪 • C.X.Λ := Submodule.smul_mem_smul ht (hsub hv)
    exact Submodule.smul_mem _ s hv'
  have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) := smul_mem_tens t htL hy
  have h0 : finW S T ((t : D.host.E) • y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]
    exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hty

  have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
    GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
  have hA' : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ),
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) :=
    fun o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
    have e2 : finW S T ((t : D.host.E) • y) =
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
        Matrix.transpose_smul]
    have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
    rw [e2, smul_smul, mul_assoc]
    have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
    rw [e4, mul_smul, ← e3, partAt_eq_smul]
  rw [e1]
  exact smul_mem_hatA_of_int hA' hz1 h0

end GlobalTheory.LiftLevel

end
end
