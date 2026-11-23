module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle512
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle425
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle458
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle452
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle431
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IPFConv

theorem integrableOn_of_quot {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsMulLeftInvariant]
    {𝓕 : Set (GA D V)} (hFD : IsFundamentalDomain (GQ V) 𝓕 μ) {φ : GA D V → ℂ}
    (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ)
    (h : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ)) : IntegrableOn φ 𝓕 μ := by
  have h1 := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hFD).1 (memLp_one_iff_integrable.2 h)
  rw [hφ.lift_descend] at h1
  exact memLp_one_iff_integrable.1 h1

theorem thetaKO_left_snd {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χV χW ω)
    {φ : WO V W → ℂ} (hf : IsThetaFunO ψ V W φ) (h : GA D V) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ W) (fun g => thetaKO ω h g φ) := fun γ hγ g => by
  have e : ((h, γ * g) : GA D V × GA D W) = (1, γ) * (h, g) := by simp
  show thetaKO ω h (γ * g) φ = thetaKO ω h g φ
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ φ hf)

theorem innerProductFormulaC_of_convergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hConv hpar
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  intro ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v₁ v₂ Q₁ Q₂
  intro φ₁ φ₂ F₁ F₂ Z pt
  have hCore : GlobalTheory.Hk3.Core R F := hL.1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω := hL.2.2.2.2.2.1
  obtain ⟨hwitt, hrank, cA, hSet, hA0⟩ := GlobalTheory.T.liftPair_positiveDefinite_wittIndexZero_cartan R F hCore hpar i σ
  have hFo₁ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁
  have hFo₂ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₂
  have hW := hCore.models.νW i
  haveI : (R.νW i).IsHaarMeasure := hW.1.1
  have hFDW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := hW.2
  haveI : ν.IsHaarMeasure := hν.1.1
  have hFDV : IsFundamentalDomain (GQ (Vc D i)) 𝓕 ν := hν.2
  have hF₁ : F₁ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₁ hU₁ v₁
  have hF₂ : F₂ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₂ hU₂ v₂
  have hL₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₁ := (Submodule.mem_inf.1 hF₁).2.2.1
  have hL₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₂ := (Submodule.mem_inf.1 hF₂).2.2.1
  have hKP : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1)
      true (fun _ => True) (fun _ => True) (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂)
      (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂) :=
    ⟨ω, φ₁, φ₂, hω, hFo₁, hFo₂, trivial, trivial, fun _ _ => rfl, fun _ _ => rfl, μ, 𝓧, hμ, fun _ => rfl⟩
  obtain ⟨hC₁, hC₂, hInt, hEq⟩ := hConv R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1) D.R.t
    cA true (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂) (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂)
    (R.νW i) ν F₁ F₂ hSet (Or.inl hwitt) hrank hKP inferInstance inferInstance hF₁ hF₂
  have hpetW : ∀ u₁ u₂ : GA D (Wc D i) → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₁ →
      GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₂ → GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) u₁ u₂ = petW R i u₁ u₂ :=
    fun u₁ u₂ h₁ h₂ => GlobalTheory.AutomorphicL2Unitary.pet_eq hFDW h₁ h₂
  have hlift₁ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₁) F₁ = upLift R i ω φ₁ F₁ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₁.1 h) hL₁
  have hlift₂ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₂) F₂ = upLift R i ω φ₂ F₂ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₂.1 h) hL₂
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv at hC₁ hC₂
  rw [hlift₁] at hC₁ hEq
  rw [hlift₂] at hC₂ hEq
  have hZeq : ∀ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
      conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) = Z g := fun g => by
    rw [hpetW (rTr (Wc D i) g F₁) F₂ (hL₁.mul_right g) hL₂]
  have hpc := GlobalTheory.T.petersson_principal_level_continuous_right_invariant hP R F hCore i σ
  have hZc : Continuous Z :=
    (GlobalTheory.T.continuous_weilCoefficient_fockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hμ Q₁ Q₂).mul
      (Complex.continuous_conj.comp (hpc.2 U₁ hU₁ U₂ hU₂ _ _).1)
  have hZi : Integrable Z (R.νW i) := hInt.congr (ae_of_all _ hZeq)
  have hZr : ∀ g, ∀ k ∈ levW R i, Z (g * k) = Z g := fun g k hk => by
    have hk1 := GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁ k hk
    have e : (((1 : GA D (Vc D i)), g * k) : GA D (Vc D i) × GA D (Wc D i)) = (1, g) * (1, k) := by simp
    show l2 μ 𝓧 (ω (1, g * k) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) (g * k) F₁) F₂) =
      l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
    rw [e, map_mul, Module.End.mul_apply, hk1, (hpc.2 U₁ hU₁ U₂ hU₂ _ _).2 g k hk]
  obtain ⟨hfin, hdis⟩ := GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals D R.θ hSet.2.2.2.1 (Wc D i) hSet.2.2.2.2.1 _ (R.νW i) hW.1 hpc.1 Fr hFr mR
    hmR Z hZc hZi hZr
  refine ⟨fun h => ?_, ?_, hfin, ?_⟩
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) :=
      fun γ hγ g => by
        have e1 : thetaKO ω h (γ * g) φ₁ = thetaKO ω h g φ₁ := thetaKO_left_snd hω hFo₁.1 h γ hγ g
        have e2 : F₁ (γ * g) = F₁ g := hL₁ γ hγ g
        show thetaKO ω h (γ * g) φ₁ * starRingEnd ℂ (F₁ (γ * g)) = _
        rw [e1, e2]
    exact integrableOn_of_quot hFDW hLp (hC₁.1 h)
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Vc D i))
        (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) := fun γ hγ g => by
      have e1 : upLift R i ω φ₁ F₁ (γ * g) = upLift R i ω φ₁ F₁ g := hC₁.2.1 γ hγ g
      have e2 : upLift R i ω φ₂ F₂ (γ * g) = upLift R i ω φ₂ F₂ g := hC₂.2.1 γ hγ g
      show upLift R i ω φ₁ F₁ (γ * g) * starRingEnd ℂ (upLift R i ω φ₂ F₂ (γ * g)) = _
      rw [e1, e2]
    exact integrableOn_of_quot hFDV hLp (hC₁.2.integrable_mul_conj hC₂.2)
  · have hvol : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Vc D i) ν = (ν 𝓕).toReal := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hFDV]
    have hpV : GlobalTheory.Cusp.petersson (Vc D i) ν (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) =
        l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) := GlobalTheory.AutomorphicL2Unitary.pet_eq hFDV hC₁.2.1 hC₂.2.1
    have hI : ∫ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
        conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) ∂(R.νW i) = ∫ g, Z g ∂(R.νW i) :=
      integral_congr_ae (ae_of_all _ hZeq)
    rw [hpV, hvol, hI, hdis] at hEq
    exact hEq

end GlobalTheory.IPFConv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RLatMove

theorem card_eq_of_frame {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) : Fintype.card Y = n := by
  apply le_antisymm
  · calc Fintype.card Y = (1 : Matrix Y Y k).rank := Matrix.rank_one.symm
      _ = (F.γ * F.β).rank := by rw [F.γβ]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width _
      _ = n := Fintype.card_fin n
  · calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
      _ = (1 : Matrix (Fin n) (Fin n) k).rank := Matrix.rank_one.symm
      _ = (F.β * F.γ).rank := by rw [F.βγ]
      _ ≤ F.β.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_width _

def frameGL {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) : GL (Fin n) k where
  val := (F.β * B.val).submatrix id σ
  inv := ((B⁻¹).val * F.γ).submatrix σ id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv (F.β * B.val) ((B⁻¹).val * F.γ) id σ id]
    have : F.β * B.val * ((B⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc B.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul, F.βγ]
    rw [this, Matrix.submatrix_id_id]
  inv_val := by
    have h := Matrix.submatrix_mul_equiv ((B⁻¹).val * F.γ) (F.β * B.val) σ (Equiv.refl (Fin n)) σ
    simp only [Equiv.coe_refl] at h
    rw [h]
    have : (B⁻¹).val * F.γ * (F.β * B.val) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    rw [this, Matrix.submatrix_one_equiv]

theorem frameGL_val {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) :
    (frameGL F B σ).val = (F.β * B.val).submatrix id σ := rfl

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem finJ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : PkHyp W) : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := by
  haveI := hW.fin
  have : {PP | PP ∈ (pk W).Pg ∨ QAll W PP} = ((pk W).Pg : Set _) ∪ ⋃ t, ((pk W).Q t : Set _) := by
    ext PP; simp [QAll]
  have hf : Set.Finite {PP | PP ∈ (pk W).Pg ∨ QAll W PP} := by
    rw [this]; exact (Finset.finite_toSet _).union (Set.finite_iUnion fun t => Finset.finite_toSet _)
  exact hf.to_subtype

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem move_main : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j)) → ∃ b : ∀ j, GA D (Yc D j), (∀ j, b j ∈ GfC (Yc D j)) ∧ (∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (N j) P) ∧ ∀ PP h j c (hc : j + c = (l PP h).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (l PP h).q) (Yc D j) (b j) ((pk W).βY j) (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hτ hNT hζ hLT hgP htP hdisj hPre hOrth hbas FY N hN hInt
  classical
  haveI : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := finJ W hW
  letI : Fintype {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => (l i.1 i.2).q.v) := by
    intro i i' hii
    apply GlobalTheory.T.level_places_under_injective W hW
    simp only at hii
    rwa [(l i.1 i.2).under, (l i'.1 i'.2).under] at hii
  have key : ∀ j, j < D.R.m → ∃ t ∈ GfC (Yc D j),
      (∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
        GlobalTheory.FinPl.Moves (Yc D j) t ((pk W).ΛY j) (N j) P) ∧
      ∀ PP h c (hc : j + c = (l PP h).s + 1),
        ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
          GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧
          MovedTo (ofSplit (l PP h).q) (Yc D j) t ((pk W).βY j)
            (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id
              fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j hj
    have hsj : ∀ PP h, j + ((l PP h).s + 1 - j) = (l PP h).s + 1 := fun PP h => by
      have := (l PP h).hs; omega
    have hE : ∀ PP h, ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
        GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
      intro PP h
      obtain ⟨eqv, heqv⟩ := GlobalTheory.SymBridge.PhiAgreeProof.zPos_equiv D.R.k ((l PP h).s + 1) D.R.t j
      have hcard := card_eq_of_frame (FY PP h j _ (hsj PP h))
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at hcard
      have hr : D.R.k + ((l PP h).s + 1) + j * D.R.t = (Yc D j).rank := by
        rw [← hcard]; have := hsj PP h; omega
      exact ⟨eqv.trans (finCongr hr), fun x => by simp [heqv]⟩
    choose E hEo using hE
    let σ : ∀ PP h, Fin (Yc D j).rank ≃ (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((l PP h).s + 1 - j)) :=
      fun PP h => (E PP h).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j _ (hsj PP h))
    let M : ∀ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, GL (Fin (Yc D j).rank) (l i.1 i.2).k :=
      fun i => frameGL (FY i.1 i.2 j _ (hsj i.1 i.2)) (bas i.1 i.2 j _ (hsj i.1 i.2)) (σ i.1 i.2)
    have hsd := GlobalTheory.T.self_dual_lattice_frame_chain W hW j hj
    obtain ⟨t, ht, Lt, hLt, hMv, hAgree, hMT⟩ := GlobalTheory.T.exists_base_point_carrying_lattice_and_frames D (Yc D j) ((pk W).ΛY j) (N j) ((pk W).βY j)
      hsd.1 (hN j hj) {PP // PP ∈ (pk W).Pg ∨ QAll W PP} (fun i => (l i.1 i.2).k)
      (fun i => (l i.1 i.2).q) hinj M
    refine ⟨t, ht, ?_, ?_⟩
    · intro P hP
      have hloc : ∀ w, P w → GlobalTheory.FinPl.latV (Yc D j) Lt (· = w) = GlobalTheory.FinPl.latV (Yc D j) (N j) (· = w) := by
        intro w hw
        by_cases hex : ∃ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, (l i.1 i.2).q.v = w
        · obtain ⟨⟨PP, h⟩, rfl⟩ := hex
          have hPg : PP ∉ (pk W).Pg := fun hPg => hP _ hw ((hgP _).2 ⟨PP, hPg, (l PP h).under⟩)
          have hb := hbas PP h hPg j _ (hsj PP h)
          have hm := hMT ⟨PP, h⟩
          have hval : (M ⟨PP, h⟩).val = (FY PP h j _ (hsj PP h)).β.submatrix id (σ PP h) := by
            simp only [M, frameGL_val, hb, Units.val_one, Matrix.mul_one]
          rw [hval] at hm
          exact GlobalTheory.T.selfDual_lattice_eq_of_splitPlace_frame_span (Yc D j) t ((pk W).ΛY j) Lt (N j) ((pk W).βY j) _ (l PP h).q _
            (FY PP h j _ (hsj PP h)) (σ PP h) ht hsd.1 hsd.2 hLt (hN j hj) (hMv _) hm
            (hInt PP h j _ (hsj PP h))
        · push_neg at hex
          exact hAgree w (fun i => (hex i).symm)
      have hEq := GlobalTheory.T.latticeCompletion_eq_of_local_agreement (Yc D j) Lt (N j) P hLt.1 (hN j hj).1 hloc
      have := hMv P
      unfold GlobalTheory.FinPl.Moves at this ⊢
      rwa [← hEq]
    · intro PP h c hc
      obtain rfl : c = (l PP h).s + 1 - j := by omega
      exact ⟨E PP h, hEo PP h, hMT ⟨PP, h⟩⟩
  choose T hT hMovesT hFrT using key
  refine ⟨fun j => if h : j < D.R.m then T j h else 1, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < D.R.m
    · simp only [dif_pos h]; exact hT j h
    · simp only [dif_neg h]; exact one_mem _
  · intro j hj P hP
    simp only [dif_pos hj]
    exact hMovesT j hj P hP
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    simp only [dif_pos hj]
    exact hFrT j hj PP h c hc

end GlobalTheory.RLatMove
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopStep

open GlobalTheory.Fam.Inhab GlobalTheory.Fam.FamInhab

section
variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)

theorem lift_lev_pt (hl : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (t : T) (k : ℕ) (hk : k < D.R.m) {V : HSp D} (hV : V.SigOK)
    (hr : V.rank = D.R.r + (k + 1) * D.R.t) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    {om : Om (Yc D k) V} (hom : IsWeilDatumO R.ψ (Yc D k) V (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 om) {f₀ f f' : WO (Yc D k) V → ℂ}
    (hf : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k R.triv) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f)
    (hf' : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k P) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f') (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : GA D V → ℂ) (φ : PolF D V.rank (Yc D k).rank)
    (hi : ∀ g, IntegrableOn (fun h => thetaKO om g h
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) * F h) 𝓕 ν)
    (U : GA D (Yc D k) → ℂ)
    (hU : ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k P), ∀ g, U (g * κ) = levChi (Yc D k) (R.βY k) (R.datYt t k P) κ * U g)
    (he : ∀ g, Lift.liftInt ν 𝓕 (thetaKO om)
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) F g = U g) :
    liftS om ν 𝓕 F (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f' φ) =
      (Nat.card P.H : ℂ) • U := by
  haveI := finite_H P
  haveI : Fintype P.H := Fintype.ofFinite _
  choose κ hκ using fun p : P.H => GlobalTheory.ChainEquiv.lifts_chain R.toLevCh _ hl t k hk p.1
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hl t ⟨k, hk⟩
  have s1 := sd (hl.βY k hk)
  have s2 := sd hβ
  have hs := @GlobalTheory.StepVecSum.stepVec_eq_sum D R.ψ R.θ (Yc D k) V _ _ om _ _ _ _ _ _ f₀ f f' hom (D.sp.Y_sig _) hV
    (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MY k)) (GlobalTheory.Chain.VacVec.cart_isCartanInv M) s1.1 s2.1 s1.2 s2.2 D.R.r D.R.t k (r_le_Y k)
    (rankY hk.le) hr R.Pg (R.Q t) (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 R.chi (R.xiR t) P _ hf hf'
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hth : IsThetaFunO R.ψ (Yc D k) V f := (GlobalTheory.Chain.StepVac.stepVec_vac s1.1 s2.1 (by
    rw [rankY hk.le, hr]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _) hf).1
  exact (lift_sum hom hθ _ _ _ _ hth κ (fun p => (hκ p).1) _ (fun p => levChi_ne_zero _ _) hs ν 𝓕 F φ hi U he
    fun p g => hU _ (levChi_lift (L := R.datYt t k R.triv) P p (hκ p)) g).2

theorem lift_ioX_pt (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (hF : ∀ κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P), ∀ φ x g,
      (R.ioX t F).1 (R.ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ *
        (R.ioX t F).1 (R.ItX φ x) g)
    {v : WO (Yc D (j + 1)) D.sp.X' → ℂ}
    (hv : IsStepVecOf R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (R.βY (j + 1)) R.βX
      (R.datYt t (j + 1) P) (R.chi D.R.m) (R.Q t) (R.xiR t) (vacT R j h) v) (Q x) :
    liftS (omT R t j h) (R.νX t) (R.fdX t) (F.1 x) (pureTensorO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX)
      (onb (R.MY (j + 1))) (onb R.MX) v Q) = (Nat.card P.H : ℂ) • (ioXT R t j h F).1 (itXT R j h Q x) := by
  have e : R.chi D.R.m = R.chi (j + 1 + 1) := congrArg R.chi (show j + 1 + 1 = D.R.m from h).symm
  have h1 := top_vec hc t j h
  rw [e] at h1 hv
  have key : ∀ n (e : D.R.m - 1 = n), ∀ κ ∈ levS (Yc D n) (R.βY n) (R.datYt t n P), ∀ φ x g,
      ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) (g * κ) =
      levChi (Yc D n) (R.βY n) (R.datYt t n P) κ *
        ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) g := by
    intro n e; subst e; exact hF
  exact lift_lev_pt P hl hm.inf t (j + 1) (by omega) D.sp.X'_sig (rank_top h) R.MX hl.βX (top_weil hc t j h) h1 hv
    _ _ _ Q ((top_io hc t j h).integ F Q x) _ (fun κ hκ g => key _ (idx_top h) κ hκ Q x g) ((top_io hc t j h).eq F Q x)

end

end GlobalTheory.TopStep
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AmpRec

theorem exists_threshold_adm9_of_ties : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  intro Cg cb Cu cT CT C0 Cn
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨m₀, hm⟩ := GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap hH (GlobalTheory.AmpOrbGap.ampKF hH)
    GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1 Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hT => ?_⟩
  intro hH0
  obtain ⟨h1000, -, hmM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hmM
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hmM
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl h1000 hbig hT.cdScale_tie hH0

end GlobalTheory.AmpRec
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreDlGap

theorem ptDl_at_record : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨C, hC⟩ :=
    GlobalTheory.CellMinorLineGap.minor_line hH (GlobalTheory.AmpOrbGap.ampKF hH) GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1
  refine ⟨C, fun Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl h1 h2 hT => ?_⟩
  intro hH0
  obtain ⟨hCl, -, hMm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT h1 h2 hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hMm
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hMm
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl hCl hbig hT.cdScale_tie hH0

end GlobalTheory.CoreDlGap
end
