module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle562
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle552
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle458
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle545
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle474
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle564
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle568
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorsLiftsDoubleCoset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle261
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.TypesRows

theorem parts_span_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ b : Bool, (⨆ π, y.prtE F.lv2 b (rep π)) = (y.C F.lv2).EEc b ∧ ∀ π π', π ≠ π' → ∀ x ∈ y.prtE F.lv2 b (rep π), ∀ x' ∈ y.prtE F.lv2 b (rep π'), (y.C F.lv2).ipE b x x' = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 b)) h0.1.1 h0.2
  obtain ⟨s, c, hsG, he⟩ : ∃ (s : Finset (GA D (Yc D 0))) (c : GA D (Yc D 0) → ℂ), (∀ g ∈ s, g ∈ GfC (Yc D 0)) ∧
      R.e0 = ∑ g ∈ s, c g • principalLevelFrame.rtA g :=
    GlobalTheory.Mem.R3.IsotIndep.gaL_finSum (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG _
  have key := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0) (R.dat0 (R.levR F.lv2 b)) R.e0
    (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 hs.1 hs.2 ⟨s, c, hsG, he⟩

  set J := levS _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hJ
  set χ := levChi _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hχ

  have hcc : ∀ ρ : Formalism.L2.NG.FinTyp D.host.E D.R.r, (principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT ρ)).Iso ρ := by
    intro ρ
    unfold Formalism.L2.NG.FinTyp.Iso
    rw [principalLevelFrame.conjT_S, principalLevelFrame.conjT_S, principalLevelFrame.conjSub_conjSub]
    exact Formalism.L2.NG.IsoRep.refl _
  have hspan : (⨆ π, principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)) = Mult.goodPart R.θ (R.MY 0) J χ R.e0 := by
    refine le_antisymm (iSup_le fun π => inf_le_left) ?_
    rw [← key.1]
    refine iSup_le fun ρ => ?_
    by_cases h0 : principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ = ⊥
    · rw [h0]
      exact bot_le
    · have he1 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.FinTyp.conjT ρ) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ :=
        principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (hcc ρ)
      have hocc : principalLevelFrame.FinTyp.conjT ρ ∈ y.occ F.lv2 := ⟨b, by rw [he1]; exact h0⟩
      obtain ⟨π, hπ⟩ := hR.all _ hocc
      have he2 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ := by
        rw [← he1]
        exact principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.conjT_iso hπ)
      exact le_iSup_of_le π (le_of_eq he2.symm)
  refine ⟨?_, ?_⟩
  · unfold Hd.prtE
    show (⨆ π, (principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) =
      (Mult.goodPart R.θ (R.MY 0) J χ R.e0).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
    rw [← hspan, Submodule.map_iSup]
  · intro π π' hne x hx x' hx'
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨u', hu', rfl⟩ := hx'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (rep π)).Iso (principalLevelFrame.FinTyp.conjT (rep π')) :=
      principalLevelFrame.not_iso_conjT fun h => hne (hR.inj π π' h)
    have := key.2 _ _ hni u hu u' hu'
    show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 _ _ = 0
    unfold ipMT
    convert this using 2 <;> exact LinearEquiv.symm_apply_apply _ _

end GlobalTheory.Mem.R3.Rw.TypesRows
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.TypesDisj

theorem prtW_inf_eq_bot : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (i : Fin D.R.m) (π π' : Φ), π ≠ π' → y.prtW F.lv2 i (rep π) ⊓ y.prtW F.lv2 i (rep π') = ⊥ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hI hP _ y Φ rep hR i π π' hne
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have h0 := hB.models.νW i
  have hO := (GlobalTheory.FinTypesRows.isotL_span_orth D (Wc D i) _ R.θ (R.MW i (sg0 D A3.A)) (y.PW i) y.hF (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) (R.eWf i (sg0 D A3.A)) _ (R.fdW i) hI (D.sp.W_sig _)
    hB.models.inf (y.stdPsi.2 i) h0.1.1 h0.2 (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)).2
  have hHP := GlobalTheory.HilbertLevels.herm_lev hI hB.models.inf (D.sp.W_sig _) (R.MW i (sg0 D A3.A)) (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) h0.1.1 h0.2
  have hni : ¬ (rep π).Iso (rep π') := fun h => hne (hR.inj π π' h)
  rw [eq_bot_iff]
  rintro w ⟨hw, hw'⟩
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨b, hb, hab⟩ := Submodule.mem_map.1 hw'
  have hba : b = a := LinearEquiv.injective _ hab
  subst hba
  have hz := hO _ _ hni b ha b hb
  have hm : b ∈ Mult R.θ (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A)))) :=
    Mult.goodPart_le _ _ _ _ _ ha.1
  have hmT := Submodule.mem_map_of_mem (f := (PiTensorProduct.lift : MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap) hm
  by_contra hne0
  have hpos := hHP.pos ⟨_, hmT⟩ (fun h => hne0 ((Submodule.mem_bot ℂ).2 (congrArg Subtype.val h)))
  simp only at hpos
  unfold ipMT at hpos
  have hs : ∀ z, PiTensorProduct.lift.symm (((PiTensorProduct.lift : MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap) z) = z :=
    fun z => LinearEquiv.symm_apply_apply _ z
  rw [hs, hz] at hpos
  simp at hpos

end GlobalTheory.Mem.R3.Rw.TypesDisj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.BaseRowCount

theorem sum_finrank_le_of_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    ∑ i, Module.finrank K (S i) ≤ Module.finrank K V := by
  classical
  have h : Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
    exact Module.finrank_directSum (R := K) (fun i => S i)
  rw [← h]
  exact Submodule.finrank_le _



theorem nRows0_eq_finrank_isotE : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ π : D.what₂.FT, D.what₂.nRows0 π = Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHost
  classical
  have hI : Inputs D := GlobalTheory.LinksInputs.inputs_of_hypotheses hW hDS hHC hCR D
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 false)) h0.1.1 h0.2
  have hO := (GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) Y.PY Y.hF (R.βY 0)
    (R.dat0 (R.toRealDat.levR F.lv2 false)) R.e0 _ R.fd0 hI (D.sp.Y_sig _) hB.models.inf Y.stdPsi.1 hs.1 hs.2
    (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)).2
  have hT := Y.tied.base
  let f : D.what₂.EE0 →ₗ[ℂ] _ := (Submodule.subtype _) ∘ₗ Y.Iz.jE.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp Y.Iz.jE.injective
  let Wp : D.what₂.FT → Submodule ℂ D.what₂.EE0 := fun π => (Y.Iz.prt π).comap f

  have hOrth : ∀ π π', π ≠ π' → ∀ x ∈ Wp π, ∀ y ∈ Wp π', ⟪x, y⟫_ℂ = 0 := by
    intro π π' hne x hx y hy
    have hx' : f x ∈ Y.Iz.prt π := hx
    have hy' : f y ∈ Y.Iz.prt π' := hy
    rw [Y.prtE0] at hx' hy'
    obtain ⟨a, ha, hax⟩ := hx'
    obtain ⟨b, hb, hby⟩ := hy'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π))).Iso
        (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π'))) :=
      principalLevelFrame.not_iso_conjT fun h => hne (Y.eFT.injective (principalLevelFrame.rowRepR_inj R.θ _ _ h))
    have key := hO _ _ hni a ha b hb
    rw [hT.ee x y]
    unfold ChainReal.ipE ipMT
    refine Eq.trans ?_ key
    have e1 : (Y.Iz.jE x).val = f x := rfl
    have e2 : (Y.Iz.jE y).val = f y := rfl
    rw [e1, e2, ← hax, ← hby]
    congr 1
    · exact LinearEquiv.symm_apply_apply _ a
    · exact LinearEquiv.symm_apply_apply _ b
  have hInd : iSupIndep Wp := by
    apply OrthogonalFamily.independent
    rw [orthogonalFamily_iff_pairwise]
    intro σ σ' hne
    rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
    exact hOrth σ σ' hne
  have hle : ∀ π, D.what₂.nRows0 π ≤ Module.finrank ℂ (Wp π) := by
    intro π
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    let v : {σ // D.what₂.ft0 σ = π} → Wp π := fun σ => ⟨D.what₂.onb0 σ.1, by
      show f _ ∈ Y.Iz.prt π
      have := hT.ft σ.1
      rw [σ.2] at this
      exact this⟩
    have hli : LinearIndependent ℂ v := by
      apply LinearIndependent.of_comp (Wp π).subtype
      exact D.what₂.onb0.toBasis.linearIndependent.comp _ Subtype.val_injective
    exact hli.fintype_card_le_finrank
  have hdim : Module.finrank ℂ D.what₂.EE0 = D.what₂.D0 := by
    rw [Module.finrank_eq_card_basis D.what₂.onb0.toBasis, Fintype.card_fin]
  have hsum : ∑ π, D.what₂.nRows0 π = D.what₂.D0 := by
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  have hsle : ∑ π, Module.finrank ℂ (Wp π) ≤ D.what₂.D0 := hdim ▸ sum_finrank_le_of_indep Wp hInd
  have heq : ∀ π, D.what₂.nRows0 π = Module.finrank ℂ (Wp π) := by
    have h2 : ∑ π, D.what₂.nRows0 π = ∑ π, Module.finrank ℂ (Wp π) :=
      le_antisymm (Finset.sum_le_sum fun π _ => hle π) (hsle.trans hsum.ge)
    intro π
    exact (Finset.sum_eq_sum_iff_of_le (fun π _ => hle π)).1 h2 π (Finset.mem_univ π)
  intro π
  rw [heq π]
  have hrng : Y.Iz.prt π ≤ LinearMap.range f := by
    intro z hz
    rw [Y.prtE0] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hz : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap a ∈
        (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc false :=
      ⟨a, (Submodule.mem_inf.1 ha).1, rfl⟩
    refine ⟨Y.Iz.jE.symm ⟨_, hz⟩, ?_⟩
    change (Submodule.subtype _ (Y.Iz.jE (Y.Iz.jE.symm ⟨_, hz⟩))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hmap : (Wp π).map f = Y.Iz.prt π := by
    show ((Y.Iz.prt π).comap f).map f = _
    rw [Submodule.map_comap_eq, inf_eq_right.2 hrng]
  rw [(Submodule.equivMapOfInjective f hf (Wp π)).finrank_eq, hmap, Y.prtE0]
  first
    | exact LinearEquiv.finrank_map_eq _ _
    | exact LinearEquiv.finrank_map_eq (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) _
    | exact ((Submodule.equivMapOfInjective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap (LinearEquiv.injective _) _).finrank_eq).symm

end GlobalTheory.BaseRowCount
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

theorem _root_.GlobalTheory.T.iSupIndep_finiteTypeComponents_thetaLiftForms : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ i : Fin D.R.m, iSupIndep (fun σ : D.what₂.FT => D.what₂.isot ((i : ℕ) + 1) σ) := by
  first | exact @GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep | exact GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep | (intros; apply GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmCoef

theorem smul_eq_of_heq {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ a b : ℂ}
    (h1 : HEq x' (μ • y)) (h2 : HEq (a • x') (b • y)) : (a * μ) • y = b • y := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]
  exact eq_of_heq h2

theorem heq_smul {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ : ℂ}
    (h1 : HEq x' (μ • y)) (a : ℂ) : HEq (a • x') ((a * μ) • y) := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]

end GlobalTheory.Mem.R3.Rw.OmCoef



theorem GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
      (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) ∨
      ∃ c0L', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L' ∧
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hR i i' hii c0L hc
  obtain ⟨g'', c0R'', c0L'', hT''⟩ := hP.char.base.fam.tie
  have hc'' : GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' := ⟨g'', c0R'', hT''⟩
  by_cases h0 : ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
      (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0
  · exact Or.inl h0
  right
  push_neg at h0
  obtain ⟨x, hx⟩ := h0
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.coefficientMap_enlargedBase_eq_complexMultiple z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc''
  obtain ⟨v, v', u, u', n, n', hn, hun, hn', hun', hvv, hv0, hrel⟩ :=
    GlobalTheory.T.exists_coefficientMaps_agree_rootOfUnity_enlarged z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc'' x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcv, -⟩ := hR
  obtain ⟨hW, -, hnW, hiW, -⟩ := hcv i i' hii
  have key := GlobalTheory.Mem.R3.Rw.OmCoef.smul_eq_of_heq (eq_of_heq hW) hnW hiW (hμ v v' hvv) hrel
  have hμe : (w'.st Z').toD7.what₂.embLL u' * μ = (w.st Z).toD7.what₂.embLL u := smul_left_injective ℂ hv0 key
  have hu0 : (w.st Z).toD7.what₂.embLL u ≠ 0 := (map_ne_zero _).2 fun h => by
    rw [h, zero_pow hn] at hun
    exact zero_ne_one hun
  obtain ⟨b, hb⟩ : (w.st Z).toD7.what₂.embLL u ∈ Set.range (w'.st Z').toD7.what₂.embLL := hE.2.2.2 ⟨u, rfl⟩
  have hb1 : b ^ n = 1 := (w'.st Z').toD7.what₂.embLL.injective (by rw [map_pow, hb, ← map_pow, hun, map_one, map_one])
  have ha : (u' * b⁻¹) ^ (n * n') = 1 := by
    have e1 : u' ^ (n * n') = 1 := by rw [mul_comm, pow_mul, hun', one_pow]
    have e2 : b ^ (n * n') = 1 := by rw [pow_mul, hb1, one_pow]
    rw [mul_pow, inv_pow, e1, e2, inv_one, mul_one]
  refine ⟨Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i'),
    GlobalTheory.T.definiteFamilyCoefficientMaps_mul_rootOfUnity R'.toRealDat c0L'' hc'' i' (u' * b⁻¹) (n * n') (mul_ne_zero hn hn') ha, fun v1 v1' h => ?_⟩
  have eu : Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i') i' =
      (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i' := Function.update_self _ _ _
  refine (heq_of_eq ((congrArg (fun g => g v1') eu).trans (LinearMap.smul_apply _ _ _))).trans ?_
  refine (GlobalTheory.Mem.R3.Rw.OmCoef.heq_smul (eq_of_heq hW) hnW hiW (hμ v1 v1' h) _).trans (heq_of_eq ?_)
  have e1 : (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = 1 := by
    calc (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = ((w'.st Z').toD7.what₂.embLL u' * μ) * ((w.st Z).toD7.what₂.embLL u)⁻¹ := by
          rw [map_mul, map_inv₀, hb]; ring
      _ = 1 := by rw [hμe, mul_inv_cancel₀ hu0]
  rw [e1, one_smul]

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section



namespace GlobalTheory.GoodPlaceAtState

theorem natCast_mem_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
  rw [← Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  refine Ideal.subset_span ⟨(n : 𝓞 K), h, ?_⟩
  simp

theorem natCast_mem_of_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal) : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have := natCast_mem_conjPl (Formalism.DivisionValues.conjPl w) n h
  rwa [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this

end GlobalTheory.GoodPlaceAtState

theorem GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (x : St P) (v : PlE (Dof x).host), IsSplitPl (Dof x).host v → v ∉ SbD (Dof x) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace x.m.z.R.toRealDat v := by
  intro K B f T w P x v hs hv
  have hc := x.m.z.pins.char
  have hA := hc.allPl
  have hL := hc.base.lev
  have hlow : ∀ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro k hk
    apply hv
    refine (lowSet_finite (Dof x)).mem_toFinset.2 ⟨(Dof x).host.g k, ?_, ((Dof x).host.g_prime k).ne_zero, hk⟩
    fin_cases k <;> simp [lowAll]
  have hdiv : ∀ PP, PP ∈ x.m.z.R.toRealDat.Sb → ∃ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have hm : PP ∈ x.m.z.R.Pg := by rw [← hA]; exact hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    exact ⟨k, Formalism.L2.Host.PiBar.overP _ hk⟩

  unfold GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace
  refine ⟨⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hs, fun hm => ?_, fun Q hQ he => ?_⟩, fun hm => ?_⟩
  · obtain ⟨k, hk⟩ := hdiv v hm
    exact hlow k hk
  · obtain ⟨k, hk⟩ := hdiv Q hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
    rw [he] at hk
    exact hlow k (GlobalTheory.GoodPlaceAtState.natCast_mem_of_conjPl v _ hk)
  · rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    · exact hlow 0 h
    · exact hlow 1 h
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwistChoice

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev thTw (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) : TwNew D :=
  ⟨D.ntw, D.nexp, D.nStage_trivialCharacter_coeff_eq, th, D.ntwbr, D.ntwbr_ind⟩

theorem carried_thTw (D0 D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) (h : Carried D0 D) :
    Carried D0 (thTw D th).toD7 :=
  ⟨⟨{ h.exp.gal with }, { h.exp.set with }, { h.exp.frm with }, h.exp.br, h.exp.av⟩, h.emb⟩

end GlobalTheory.HeightCounting.Up

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.splitHecke_operators_lifts_doubleCoset : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).A.heckeL i t)
      (fun x => 1 ≤ x.2 ∧ x.2 ≤ (Vc X.toD7 i).rank) (LiftBrg.envL X I hX U Xg tr L cV i t).isT
      (LiftBrg.envL X I hX U Xg tr L cV i t).isLoc) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie | exact GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie <;> assumption)
end
