module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpNZTie
public import Formalism.HermitianCurvature.StatementD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle009
import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle014
public import Formalism.PeriodIntegrals.Bundle013
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
public import Mathlib.Basic.Real.Basic
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle016
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConjDiEqSelf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle006
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

abbrev standardBesselDatumRescaled (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (κ₀ : ENNReal) : LocBessel k r :=
  { stdL L ka hka with κN := κ₀ }

def gStd (ka : ℝ) (g : Mx k r) : Mx k r := cj k r ka⁻¹ 1 (tTi k r * g * tT k r)

def muStd (ka : ℝ) (μR : Measure (Mt k r)) : Measure (Mt k r) := (μR.map (cA k r)).map (cjT k r ka⁻¹ 1)

theorem haarLie_smul (S : Set (Mx k r)) (a b : ENNReal) : haarLie S (a * b) = a • haarLie S b := by
  show (a * b) • _ = a • (b • _)
  rw [smul_smul]

theorem orbJ_std (hk : 1 ≤ k) (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ))
    (hN0 : L.κN ≠ 0) (hN1 : L.κN ≠ ⊤) (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤)
    (B : Formalism.FourierDecayAlt.B.RealPlaceData k r L.Wp L.Wq) (hBz : B.z = (stdL L ka hka).z) (hBz' : B.z' = (stdL L ka hka).z')
    (hBπ : B.π = (stdL L ka hka).π) (hBπ' : B.π' = (stdL L ka hka).π') (hBW : B.μW = (stdL L ka hka).μW)
    (hBW' : B.μW' = (stdL L ka hka).μW') (hBN : B.μN = haarLie (Nset k r) κ₀)
    (g : Mx k r) (hg : g ∈ UH (Hpk k r)) (hrel : IsRelStab L g) (μR : Measure (Mt k r)) [SFinite μR]
    (hconc : μR {x | Matrix.of x ∉ RStab k r g} = 0) (hne : μR ≠ 0) (ν : Measure (PairSp k r))
    (hq : IsOrbQuot L g μR ν) (F : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (hcut : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut B (gStd ka g) (muStd ka μR) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) B.μSS) :
    Formalism.FourierDecayAlt.D.orbJ B (gStd ka g) (muStd ka μR) (stdF L ka F) =
      (((κ₀ / (L.κN * ENNReal.ofReal (deltaN k r ka⁻¹ 1))) * (κ₀ / (L.κN * ENNReal.ofReal (deltaN k r ka⁻¹ 1)))).toReal
        : ℂ) • OrbInt L F g ν := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  have hκ : (0 : ℝ) < ka⁻¹ := inv_pos.2 hka
  have hτ : (0 : ℝ) < 1 := one_pos
  set κs : ENNReal := L.κN * ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) with hκs
  have hd : ENNReal.ofReal (deltaN (k0 + 1) r ka⁻¹ 1) ≠ 0 := (ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'
  have hs0 : κs ≠ 0 := mul_ne_zero hN0 hd
  have hs1 : κs ≠ ⊤ := ENNReal.mul_ne_top hN1 ENNReal.ofReal_ne_top
  set t : ENNReal := κ₀ / κs with ht
  set g1 := tTi (k0 + 1) r * g * tT (k0 + 1) r with hg1

  have hq1 : IsOrbQuot (turnL L ka) g1 (μR.map (cA (k0 + 1) r)) (ν.map (thP (k0 + 1) r)) := isOrbQuot_turn L ka hq
  have hrel1 : IsRelStab (turnL L ka) g1 := isRelStab_turn L ka hc hrel

  have hqs : IsOrbQuot (stdL L ka hka) (gStd ka g) (muStd ka μR) ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1)) :=
    isOrbQuot_trD hκ hτ (turnL L ka) _ _ _ _ _ _ hq1
  have hrels : IsRelStab (stdL L ka hka) (gStd ka g) := isRelStab_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ hrel1

  have hNs : (standardBesselDatumRescaled L ka hka κ₀).μN = t • (stdL L ka hka).μN := by
    show haarLie (Nset (k0 + 1) r) κ₀ = t • haarLie (Nset (k0 + 1) r) κs
    rw [← haarLie_smul, ht, ENNReal.div_mul_cancel hs0 hs1]
  have hP2 : pairMeas (standardBesselDatumRescaled L ka hka κ₀) = (t * t) • pairMeas (stdL L ka hka) :=
    pairMeas_scaleN (L := stdL L ka hka) (L' := standardBesselDatumRescaled L ka hka κ₀) rfl rfl t hNs
  have hq2 : IsOrbQuot (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g) (muStd ka μR)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) := isOrbQuot_smul hqs _ hP2
  have hrel2 : IsRelStab (standardBesselDatumRescaled L ka hka κ₀) (gStd ka g) := hrels
  have hc2 : (standardBesselDatumRescaled L ka hka κ₀).c = cStd := stdL_c L ka hka

  have hg2 : gStd ka g ∈ UH (Hpk (k0 + 1) r) := (cj_mem_UH_iff hκ hτ _).mpr (conjI_mem_UH hg)
  have hmem : ∀ x : Mt (k0 + 1) r, (Matrix.of (cjT (k0 + 1) r ka⁻¹ 1 (cA (k0 + 1) r x)) ∈ RStab (k0 + 1) r (gStd ka g)) ↔
      Matrix.of x ∈ RStab (k0 + 1) r g := by
    intro x
    rw [of_cjT, of_cA]
    exact (cj_mem_RStab_iff hκ hτ _ _).trans (conjI_mem_RStab_iff g _)
  have hconc2 : muStd ka μR {x | Matrix.of x ∉ RStab (k0 + 1) r (gStd ka g)} = 0 := by
    unfold muStd
    rw [← cjE_coe hκ hτ, MeasurableEquiv.map_apply, ← cAE_coe, MeasurableEquiv.map_apply]
    convert hconc using 2
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, cAE_coe, cjE_coe]
    exact not_congr (hmem x)
  have hne2 : muStd ka μR ≠ 0 := by
    unfold muStd
    rw [← cjE_coe hκ hτ, ← cAE_coe]
    exact (Measure.map_ne_zero_iff (cjE hκ hτ).measurable.aemeasurable).mpr
      ((Measure.map_ne_zero_iff (cAE (k0 + 1) r).measurable.aemeasurable).mpr hne)
  have : SFinite (muStd ka μR) := by unfold muStd; infer_instance

  have hμ : B.μSS = pairMeas (standardBesselDatumRescaled L ka hka κ₀) := by
    show (B.μW.prod B.μN).prod (B.μW'.prod B.μN) = _
    rw [hBW, hBN, hBW']
    rfl
  have hI : ∀ θ' : Formalism.FourierDecayAlt.B.SS (k0 + 1) r → ℝ,
      (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p) =
      fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p := by
    intro θ'
    funext p
    exact congrArg (fun X => θ' p • X)
      (Formalism.MainNotions.BigCellDensity.integrand_eq (standardBesselDatumRescaled L ka hka κ₀) B hc2 hBz hBz' hBπ hBπ' (stdF L ka F) (gStd ka g) p)
  have hW := Formalism.MainNotions.BigCellDensity.weil_L_gen (standardBesselDatumRescaled L ka hka κ₀) hc2 h0 h1 hg2 hrel2 hconc2 hne2 hq2 (stdF L ka F)
  have hfin : OrbInt (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = ((t * t).toReal : ℂ) • OrbInt L F g ν := by
    show OrbInt (stdL L ka hka) (stdF L ka F) (gStd ka g)
      ((t * t) • ((ν.map (thP (k0 + 1) r)).map (phiP (k0 + 1) r ka⁻¹ 1))) = _
    rw [gStd, OrbInt_trD hκ hτ (turnL L ka) _ _ _ _ _ _ _ (stdF L ka F) g1 (t * t) (ν.map (thP (k0 + 1) r))]
    have hfe : (fun x => stdF L ka F (cj (k0 + 1) r ka⁻¹ 1 x)) = turnF L ka F := by
      funext x
      show turnF L ka F (cjI (k0 + 1) r ka⁻¹ 1 (cj (k0 + 1) r ka⁻¹ 1 x)) = _
      rw [cjI_cj hκ hτ]
    rw [hfe, OrbInt_turn L ka hc F g ν]
  rw [Formalism.FourierDecayAlt.D.orbJ, dite_eq_left hcut]
  set θ' := hcut.choose
  have hspec := hcut.choose_spec
  have hint' : Integrable (fun p => θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p)
      (pairMeas (standardBesselDatumRescaled L ka hka κ₀)) := by
    have h2 := hspec.2
    rw [hI θ', hμ] at h2
    exact h2
  have hθ1 : ∀ p, Formalism.MainNotions.BigCellDensity.InPair (standardBesselDatumRescaled L ka hka κ₀) p →
      ∫ x, θ' (stabAct (gStd ka g) (Matrix.of x) p) ∂(muStd ka μR) = 1 := by
    intro p hp
    refine hspec.1.2.2 p ?_
    unfold Formalism.FourierDecayAlt.B.RealPlaceData.inSS
    rw [hBz, hBz']
    exact hp
  have e1 : (∫ p, θ' p • Formalism.FourierDecayAlt.D.orbIntegrand B (gStd ka g) (stdF L ka F) p ∂B.μSS) =
      ∫ p, θ' p • besselIntg (standardBesselDatumRescaled L ka hka κ₀) (stdF L ka F) (gStd ka g) p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀)) := by
    rw [hμ]
    exact congrArg (fun f => ∫ p, f p ∂(pairMeas (standardBesselDatumRescaled L ka hka κ₀))) (hI θ')
  exact e1.trans ((hW θ' hθ1 hint').trans hfin)

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

def CapFromHC : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (u : Fin k → ℝ) (π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π → ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) →
    PI.UpqRep.IsHCTypeW k r z u π →
    Formalism.FourierDecayAlt.Q.CapParam k r z π (fun i => if h : i - 1 < k then u ⟨i - 1, h⟩ else 0)

section Block

variable {k r : ℕ}

theorem mvs {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem blockW_fix (h : Matrix (Fin k) (Fin k) ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ (r ≤ j.val ∧ j.val < r + k)) :
    Formalism.MainNotions.S.blockW k r h *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j := by
  funext i
  unfold Formalism.QuantumDeterminants.bvec
  rw [mvs]
  unfold Formalism.MainNotions.S.blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dite_eq_left hi, dite_eq_right hj, Pi.single_apply, if_neg]
    intro e; rw [e] at hi; exact hj hi
  · rw [dite_eq_right hi, Pi.single_apply]

theorem blockW_UH (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (Formalism.MainNotions.S.blockW k r h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.QuantumDeterminants.Hpk k r
  have hs : hᴴ * h = 1 := Matrix.mem_unitaryGroup_iff'.mp hh
  have e1 : (Formalism.MainNotions.S.blockW k r h)ᴴ = Formalism.MainNotions.S.blockW k r hᴴ := PI.HwUniqW.blockW_conjTranspose h
  have e2 : Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r h * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.Hpk_blockW_comm h
  have e3 : Formalism.MainNotions.S.blockW k r hᴴ * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r (hᴴ * h) :=
    PI.HwUniqW.blockW_mul hᴴ h
  have e4 : Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := PI.HwUniqW.blockW_one
  rw [e1, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, e3, hs, e4, Matrix.one_mul]

theorem conj_blockW_mem {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g) (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g * Formalism.MainNotions.S.blockW k r h * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨hgU, hge, hgz⟩ := hg
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hgU
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hgU
  have hinv : ∀ x, g *ᵥ x = x → g⁻¹ *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  have hfix : ∀ x, g *ᵥ x = x → Formalism.MainNotions.S.blockW k r h *ᵥ x = x → (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) *ᵥ x = x :=
    fun x h1 h2 => by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv x h1, h2, h1]
  refine ⟨PI.HwUniqW.mul_mem_UH (PI.HwUniqW.mul_mem_UH hgU (blockW_UH h hh)) (PI.HwUniqW.inv_mem_UH hgU),
    fun a => ⟨hfix _ (hge a).1 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.eI]; omega)),
      hfix _ (hge a).2 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.esI]; omega))⟩, ?_⟩
  have hx : ∀ x, g⁻¹ *ᵥ (g *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  rw [← hgz, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul,
    blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.wI, Fin.val_last]; omega)]

end Block

theorem isType_of_hc (hcap : CapFromHC) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)}
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hHC : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, ‖π h x‖ = ‖x‖) ∧ ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z))
    (w : ℕ → ℝ) (hw : ∀ i ∈ Finset.Icc 1 k, w i = if h : i - 1 < k then u ⟨i - 1, h⟩ else 0) :
    Formalism.FourierDecayAlt.Q.IsType k r z π w := by
  obtain ⟨g, hg, hU⟩ := hHC
  refine ⟨hU.1, hrep.1, hrep.2.2, hrep.2.1, fun S hS => ?_, ?_⟩
  · have hK := hU.2.2.2.2.2.1 S le_top (fun h hh v hv => hS _ (conj_blockW_mem hg h hh.1) v hv)
    exact hK
  · intro Bs hBs x v
    rw [hcap Wp k r z u π hz hT hrep.1 hrep.2.2 ⟨g, hg, hU⟩ Bs hBs x v]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by rw [hw i hi]

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ac_le (c Cl L : ℝ) (r k f : ℕ) (hCl : 1000 + |c| ≤ Cl) (hf : 2 ≤ f) (hL : 1 / 2 ≤ L) :
    max (c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) 0 ≤
      Cl * ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
  let n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)
  let p : ℝ := ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)
  change max (c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)) 0 ≤
    Cl * n ^ 19 * (f : ℝ) ^ 5 * L / 2
  rw [mul_assoc c]
  change max (c * p) 0 ≤ _
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  have hrn : (r : ℝ) + 1 ≤ n := by
    change (r : ℝ) + 1 ≤ ((2 * r + k + 1 : ℕ) : ℝ)
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
    omega
  have hn1 : 1 ≤ n := (le_add_of_nonneg_left hr0).trans hrn
  have hn0 : 0 ≤ n := zero_le_one.trans hn1
  have htail0 : 0 ≤ (r : ℝ) * n + 1 := add_nonneg (mul_nonneg hr0 hn0) zero_le_one
  have htail : (r : ℝ) * n + 1 ≤ n ^ 2 := calc
    _ ≤ (r : ℝ) * n + n := add_le_add_right hn1 _
    _ = ((r : ℝ) + 1) * n := by rw [add_mul, one_mul]
    _ ≤ n ^ 2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hrn hn0
  have hp0 : 0 ≤ p := mul_nonneg (pow_nonneg (add_nonneg hr0 zero_le_one) 2) htail0
  have hp : p ≤ n ^ 19 := calc
    p ≤ n ^ 2 * n ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (add_nonneg hr0 zero_le_one) hrn 2) htail
        htail0 (pow_nonneg hn0 2)
    _ = n ^ 4 := (pow_add n 2 2).symm
    _ ≤ n ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hc : |c| ≤ Cl := (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1000)).trans hCl
  have hCl0 : 0 ≤ Cl := (abs_nonneg c).trans hc
  have hf' : (2 : ℝ) ≤ (f : ℝ) := by
    simpa only [Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).2 hf
  have hf4 : (4 : ℝ) ≤ (f : ℝ) ^ 5 :=
    (show (4 : ℝ) ≤ (2 : ℝ) ^ 5 by norm_num).trans (pow_le_pow_left₀ zero_le_two hf' 5)
  have hfactor : 1 ≤ (f : ℝ) ^ 5 * L / 2 := by
    apply (le_div_iff₀ (zero_lt_two : (0 : ℝ) < 2)).2
    rw [one_mul]
    calc
      (2 : ℝ) = 4 * (1 / 2) := by norm_num
      _ ≤ (f : ℝ) ^ 5 * L :=
        mul_le_mul hf4 hL (div_nonneg zero_le_one zero_le_two) (pow_nonneg f.cast_nonneg 5)
  have hbase0 : 0 ≤ Cl * n ^ 19 := mul_nonneg hCl0 (pow_nonneg hn0 19)
  have hscaled : Cl * n ^ 19 ≤ Cl * n ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
    rw [mul_assoc (Cl * n ^ 19), mul_div_assoc]
    exact le_mul_of_one_le_right hbase0 hfactor
  exact max_le ((mul_le_mul ((le_abs_self c).trans hc) hp hp0 hCl0).trans hscaled)
    (hbase0.trans hscaled)

end Formalism.L2.SG.Pf.CarrierXAll
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

theorem half_lt_int {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : a < b) : a + 1 / 2 ≤ b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : z < n := by
    have : (z : ℚ) < n := by linarith
    exact_mod_cast this
  have : (z : ℚ) + 1 ≤ n := by exact_mod_cast this
  linarith

theorem int_lt_half {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : b < a) : b + 1 / 2 ≤ a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : n ≤ z := by
    have : (n : ℚ) < z + 1 := by linarith
    have : n < z + 1 := by exact_mod_cast this
    omega
  have : (n : ℚ) ≤ z := by exact_mod_cast this
  linarith

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end
