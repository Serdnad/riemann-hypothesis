module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.StarSqrtMinusD
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApprox
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.NormRepStepOfTrace

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0) in
def MassA {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) : Prop :=
  ∀ q : {Λ // Λ ∈ rs}, wRow D F0 q.1 = ((Nat.card (Aset TR c q) : ℝ))⁻¹

theorem colPhase_holds (hTF : FrameTie X u u' F0 F0') : ColPhase F0 F0' TR cs cs' (scOf TR cs) (scOf TR cs') := by
  have hN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm cs cs' (Formalism.L2.SG.Pf.termK X cs cs') hN
  exact colPhase_of TR cs cs' (leviCols_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA)
    (phaseAt_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA hN)

theorem colFree_steps (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hCL : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK)
    (hO : Formalism.L2.SG.Pf.NormSteps.LeviOntoS TR cs) (hRep : Formalism.L2.SG.Pf.NormSteps.ColLatRepS cs hK)
    (hMass : MassA TR F0 cs) : ColFree F0 TR cs (Aset TR cs) (scOf TR cs) := fun q =>
  ⟨colFreeBij_of TR cs hK hR hCL (Formalism.L2.SG.Pf.colLatK X cs) hO hRep q, hMass q⟩

end Links

end Formalism.L2.SG.NormCut
end
end

section

namespace Formalism.L2.SG.TermOp.Vanish

theorem ratApprox_holds : RatApprox := ratApprox_of_sol ratSolApprox_holds

end Formalism.L2.SG.TermOp.Vanish
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem slabCoverC_of (hGF : GFInfInj) (hSA : NStrongApprox) (hNL : NLift) (hNR : NRatLam)
    (hRL : RatLeviC) (hPD : PsiDdC) : SlabCoverC := by
  intro D X Y u Ωs hKL hNeat hΩ
  have hK := Y.hK
  refine ⟨?_, ?_⟩
  ·
    rintro y ⟨n, h, k, hn, hk, hy⟩
    obtain ⟨ρ, ⟨γ, κ, hγκ⟩, -⟩ := Y.colReps u h
    have hs0 : ((γ : X.B.I.GA))⁻¹ ∈ Srat X u := inv_mem (gam_srat X u _ γ.2)
    obtain ⟨hn', -⟩ := nfinConj_holds X u (iotaF X u γ)⁻¹ n hn
    rw [Subgroup.coe_inv, inv_inv, iotaF_coe] at hn'
    obtain ⟨ν, hνS, hνK⟩ := hSA D X Y u ρ _ hKL hn'
    have hκ : (X.xu u)⁻¹ * (((κ : Hfin X u)) : X.B.I.Gf) * X.xu u ∈ X.K2 := κ.2
    set s1 : X.B.I.GA := ν * ((γ : X.B.I.GA))⁻¹ with hs1
    obtain ⟨t, ht, htΩ⟩ := (hΩ ρ).2.1 (s1 * y).1
    obtain ⟨s2, hs2, hs21, hs2K⟩ := hNL D X Y u ρ t ht
    refine ⟨s2 * s1, mul_mem hs2 (mul_mem hνS hs0), ρ, ?_, ?_⟩
    · show (s2 * s1 * y).1 ∈ Ωs ρ
      rw [mul_assoc, Prod.fst_mul, hs21]
      exact htΩ
    · refine ⟨_, hK.2.1 _ hs2K _ (hK.2.1 _ hνK _ (hK.2.1 _ hκ _ hk)), ?_⟩
      show _ = (s2 * s1 * y).2
      rw [hs1]
      simp only [Prod.snd_mul, Prod.snd_inv, hy, hγκ, Subgroup.coe_mul, iotaF_coe]
      group
  ·
    intro ρ ρ' y s hs hy hsy
    obtain ⟨hy1, k, hk, hyk⟩ := hy
    obtain ⟨hsy1, k', hk', hsyk⟩ := hsy
    have hyk' : ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k = y.2 := hyk
    have hsyk' : ((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u * k' = s.2 * y.2 := hsyk
    have hg : (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 := by
      have e : (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) =
          k' * k⁻¹ := by
        calc (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)
            = (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * (s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k)) * k⁻¹ := by
              group
          _ = (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u * k') * k⁻¹ := by
              rw [hyk', ← hsyk']
          _ = k' * k⁻¹ := by group
      rw [e]; exact hK.2.1 _ hk' _ (hK.2.2.1 _ hk)
    obtain ⟨hs1, hs2⟩ := sratComp_holds X u s hs
    obtain ⟨ν, η, hνη, hνG, hν1, hν2, hη⟩ := hRL D X u s (Subgroup.mem_inf.1 hs).1 hs1 hs2
    obtain ⟨ηg, hηg⟩ : ∃ ηg : Gam X u, ηg = ⟨η, hη⟩ := ⟨_, rfl⟩
    have hs2e : s.2 = ν.2 * η.2 := by rw [hνη]; rfl
    obtain ⟨hn1, -⟩ := nfinConj_holds X u ((Y.cs u).h ρ')⁻¹ ν.2 hν2
    have hLD := levelDec_of_psiDd (X := X) (u := u) (hPD D X)
    obtain ⟨h1, hh1⟩ : ∃ h1 : Hfin X u, h1 = ((Y.cs u).h ρ')⁻¹ * iotaF X u ηg * (Y.cs u).h ρ := ⟨_, rfl⟩
    have e1 : (X.xu u)⁻¹ * ((((Y.cs u).h ρ')⁻¹ : Hfin X u) * ν.2 * ((((Y.cs u).h ρ')⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
        (h1 : X.B.I.Gf)) * X.xu u =
        (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) := by
      rw [hs2e, hh1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, iotaF_coe, hηg]
      group
    have hh1K : (X.xu u)⁻¹ * (h1 : X.B.I.Gf) * X.xu u ∈ X.K2 := (hLD _ hn1 h1 (e1 ▸ hg)).1
    have hρρ : ρ' = ρ := by
      refine (Y.colReps u ((Y.cs u).h ρ)).unique ⟨ηg⁻¹, ⟨h1, hh1K⟩, ?_⟩ ⟨1, 1, by simp⟩
      show (Y.cs u).h ρ = iotaF X u ηg⁻¹ * (Y.cs u).h ρ' * h1
      rw [map_inv, hh1]
      group
    subst hρρ
    have hmem : ((Y.cs u).h ρ')⁻¹ * iotaF X u ηg * (Y.cs u).h ρ' ∈ Ku X u Y.hK := by
      rw [← hh1]; exact hh1K
    have hη1 : ηg = 1 := hNeat ((Y.cs u).h ρ') ηg hmem
    have hη1' : η = 1 := by
      have := congrArg Subtype.val hη1
      rw [hηg] at this
      exact this
    have hsν : s = ν := by rw [hνη, hη1', mul_one]
    subst hsν
    have hsN := hNR D X Y u ρ' s hKL hνG hν1 hν2 hg
    have hs1' : s.1 = 1 := (hΩ ρ').2.2 y.1 hy1 s.1 hsN hsy1
    exact ⟨hGF D X s hνG hs1', rfl⟩

theorem finite_infinite_injective : GFInfInj := by
  intro D X s hs h1
  change s ∈ X.B.I.GFset at hs
  obtain ⟨γ, -, hinf, hfin⟩ := hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hv := hinf v
  rw [h1, Pi.one_apply] at hv
  have hv' : (X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
      X.B.I.P v = 1 := by
    rw [← hv]; simp [uMat]
  have hPu : IsUnit (X.B.I.P v).det := Matrix.isUnit_det_of_left_inverse hv'
  have h2 : (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) = 1 := by
    calc (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v)
        = (X.B.I.P v * (X.B.I.P v)⁻¹) * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
            (X.B.I.P v * (X.B.I.P v)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul, Matrix.mul_one]
      _ = X.B.I.P v * ((X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
            X.B.I.P v) * (X.B.I.P v)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hv', Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
  have hγ := Matrix.map_injective (f := ⇑(X.B.I.φ v)) (RingHom.injective _)
    (h2.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)] at hfin
  unfold AutInst.fmat at hfin
  have h2' : s.2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa using hfin
  exact Prod.ext h1 h2'

theorem nLift_of (hNC : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) : NLift := by
  intro D X Y u ρ t ht
  obtain ⟨x, n, hL, rfl, hn⟩ := ht
  have hi := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ x n hL hn
  have hf := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ x n hL hn
  refine ⟨x, Subgroup.mem_inf.2 ⟨Formalism.L2.SG.TermOp.ratLink_mem (X := X) hL,
    Subgroup.subset_closure ⟨fun v => (hi v).1, ⟨hf.1, hf.2.1⟩⟩⟩, rfl, (hNC D X Y u ρ x n hn hL).1⟩

theorem nStrongApprox_of (hD : NDense) : NStrongApprox := by
  intro D X Y u ρ n hKL hn
  set a : X.B.I.Gf := ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u
  have hKo : IsOpen X.K2 := (level_subgroup_isClopen X Y.hK hKL).isOpen
  have hc : Continuous fun m : X.B.I.Gf => a⁻¹ * (m * n) * a :=
    (continuous_const.mul (continuous_id.mul continuous_const)).mul continuous_const
  have hninv : n⁻¹ ∈ X.NfinU u := (nfinGroup_holds (X := X) (u := u)).2 n hn
  obtain ⟨ν, hνG, hν1, hν2, hνU⟩ := hD D X u n⁻¹ hninv _ (hKo.preimage hc)
    (by show a⁻¹ * (n⁻¹ * n) * a ∈ X.K2; rw [inv_mul_cancel, mul_one, inv_mul_cancel]; exact Y.hK.1)
  exact ⟨ν, Subgroup.mem_inf.2 ⟨hνG, Subgroup.subset_closure ⟨fun v => (hν1 v).1, ⟨hν2.1, hν2.2.1⟩⟩⟩, hνU⟩

theorem slab_covering_of_strong_approx (hD : NDense) (hNC : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) (hRL : RatLeviC) (hPD : PsiDdC) :
    SlabCoverC :=
  slabCoverC_of finite_infinite_injective (nStrongApprox_of hD) (nLift_of hNC) nilradical_rational_lattice hRL hPD

end Formalism.L2.SG.Pf.SlabCoverPf
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

section NSAPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NDense : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

theorem nStrongApproxC_of (hD : NDense) : NStrongApproxC := by
  intro D X u hK hKL n hn c
  have hcl := Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL
  have hc : Continuous fun m : X.B.I.Gf => c⁻¹ * (m⁻¹ * n) * c :=
    (continuous_const.mul (continuous_inv.mul continuous_const)).mul continuous_const
  obtain ⟨ν, hνr, hν1, hν2, hνU⟩ := hD D X u n hn {m | c⁻¹ * (m⁻¹ * n) * c ∈ X.K2} (hcl.2.preimage hc)
    (by simpa using hK.1)
  exact ⟨ν, hνr, hν1, hν2, hνU⟩

end NSAPf

end Formalism.L2.SG.Pf.RegroupPf
end
end

section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

theorem regrouping_of_neatness (hSA : NStrongApproxC) (hO : OrbitAlgC) (hSC : Formalism.L2.SG.Pf.Slab.SlabCoverC)
    (hR : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.FoldReadyX X)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word),
      X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Formalism.L2.SG.Pf.Slab.RegroupC :=
  regrouping_of_closed_lemmas phase_well_defined_all_words column_uniqueness (colCoverC_of hSA) (slabAbsC_of phase_well_defined_all_words hSC hR hN) hO

end Formalism.L2.SG.Pf.RegroupPf
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ChiNBiAll : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), ChiNBi X

namespace ChiLeft

theorem kBB_mem {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u')
    (p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : kBB Y u u' Λ Λ' p.1.1 ∈ X.B.I.Kset := by
  obtain ⟨hRL, -, hmap, -⟩ := p.2
  have hRL' : RatLink X p.1.1 p.1.2 := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap p.1.2 Λ' = Λ := hmap
  have hb0 := (Y.cs u).base_lam Λ hΛ
  have hb1 := (Y.cs u').base_lam Λ' hΛ'
  have key : (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine LatDictK.dict_K X _ _ {y | y ∈ Λ} (fun y => ?_) (fun y => ?_)
    · show y ∈ Λ ↔ _
      conv_lhs => rw [← hb0]
      exact (Y.cs u).lat_eq _ y
    · show y ∈ Λ ↔ _
      have e1 : y ∈ Λ ↔ p.1.2.symm y ∈ Λ' := by
        constructor
        · intro hy
          rw [← hmap'] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          have : p.1.2.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          rw [← hmap']
          exact ⟨p.1.2.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ Λ' ↔ X.B.I.fmat (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := (Y.cs u').lat_eq ((Y.cs u').base Λ') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u'))⁻¹ =
          (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')⁻¹ * p.1.1.2⁻¹ from _root_.mul_inv_rev _ _,
        LatDictK.fmatK_mul, ← Matrix.mulVec_mulVec, LatDictK.ratLink_incl_inv X hRL']
  have e : kBB Y u u' Λ Λ' p.1.1 = (((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u)⁻¹ *
      (p.1.1.2 * (((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) * X.xu u')) := by
    simp only [kBB, kOf, mul_assoc]
  rw [e]
  exact key

theorem kB_inv_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {w : D.what₂.Word}
    {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (γ : Gam X w) (hk : kB c Λ γ ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (kB c Λ γ)⁻¹ *ᵥ X.f0 a) (X.f0 a) := by
  have e : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) = (kB c Λ γ)⁻¹ := by
    unfold kB
    push_cast
    group
  have hK : (((iotaF X w γ * c.h (c.base Λ) : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ *
      ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [e]; exact mem_Kset_inv X hk
  have h := (column_fixed_holds X w (iotaF X w γ * c.h (c.base Λ)) (c.h (c.base Λ)) hK).1
  rw [e] at h
  exact h

theorem one_fix {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (w : D.what₂.Word) (h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset) :
    ∀ a, CongG X (X.B.I.fmat (1 : X.B.I.Gf) *ᵥ nxt X.e0 X.z0 a) (nxt X.e0 X.z0 a) := by
  have hK : (((1 : Hfin X w) : X.B.I.Gf) * X.xu w)⁻¹ * (((1 : Hfin X w) : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset := by
    rw [inv_mul_cancel]; exact h1
  have h := (column_fixed_holds X w 1 1 hK).2
  simpa only [inv_mul_cancel] using h

end ChiLeft

theorem chiNLeft_holds (hB : ChiNBiAll) : ChiNLeft := by
  intro D X Y u u' Λ Λ' hΛ hΛ' γ hk p
  have hκ := ChiLeft.kBB_mem Y u u' hΛ hΛ' p
  have h1 : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    have h := mem_Kset_mul X hk (mem_Kset_inv X hk)
    rwa [mul_inv_cancel] at h
  have h := hB D X (kBB Y u u' Λ Λ' p.1.1) (kB (Y.cs u) Λ γ) 1 hκ hk h1
    (ChiLeft.kB_inv_fix (Y.cs u) Λ γ hk) (ChiLeft.one_fix u h1)
  rwa [mul_one] at h

end Formalism.L2.SG.Pf.SatGramActL
end
end

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.SG.Pf.NormRepX

theorem norm_representative_holds (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word)
    (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) : Formalism.L2.SG.Pf.NormRepStep D u u' :=
  PI.NRL.normRepStep_of_trace D u u' (Formalism.L2.SG.Closed.TermStable_holds D u u') hP (Or.inr (PI.NRL.traceOne D))

end Formalism.L2.SG.Pf.NormRepX
end
