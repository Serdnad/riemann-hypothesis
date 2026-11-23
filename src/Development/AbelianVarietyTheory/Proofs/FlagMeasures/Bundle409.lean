module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle399
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle078
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle086
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle345
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle381
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle400
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle404
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle405
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle079
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ActQ

theorem snoc_map {α β : Type*} {r : ℕ} (f : α → β) (e : Fin r → α) (z : α) (j : Fin (r + 1)) :
    f (Fin.snoc (α := fun _ => α) e z j) = Fin.snoc (α := fun _ => β) (fun a => f (e a)) (f z) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

end GlobalTheory.ActQ

theorem GlobalTheory.realPoint_ratIsom_isMatOn : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : X.B.I.GA) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ j, n (frame s.frame j) = ∑ i, A i j • frame s.frame i) → ∀ v : NumberField.InfinitePlace X.B.I.F, GlobalTheory.LoopAct.IsMatOn (uMat (x.1 v)) (fun j => uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j) (A.map (embS D (X.pl v))) := by
  intro D X Y u u' s n x A hR hA v
  obtain ⟨M, -, hM1, -, hM3⟩ := hR
  obtain ⟨M', -, hM1', -, hM3'⟩ := s.rep.2.1
  have hP' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (↑M' : Matrix _ _ _).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1'
  have hL' : ∀ y, X.crd (s.lin y) = (↑M' : Matrix _ _ _) *ᵥ X.crd y := hM3'
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfr : ∀ j, frame s.frame j = s.lin (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j) := by
    intro j
    have e1 : s.frame = Formalism.L2.SG.TermOp.mapLF s.lin (lf D (X.Fu u')) := rfl
    rw [e1]
    unfold Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hiso]
    rw [GlobalTheory.ActQ.snoc_map (f := (s.lin : (VS D).V → (VS D).V)), ← X.Fu_e u', ← X.flagZVector u']
    rfl
  have hfrm : ∀ j, Formalism.L2.SG.RealObj.frm X u' 1 v j =
      rv X.B.I v (X.crd (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j)) := by
    intro j
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    rw [GlobalTheory.ActQ.snoc_map (f := fun y => rv X.B.I v (X.crd y))]
    rfl
  have hf : ∀ j, uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j = rv X.B.I v (X.crd (frame s.frame j)) := by
    intro j
    rw [hfrm, hfr, hL', ← Formalism.L2.SG.Pf.Level.rv_mulVec X v, ← hP' v]
  have hsum : ∀ (c : Fin (D.R.rS + 1) → D.host.E) (w : Fin (D.R.rS + 1) → (VS D).V),
      rv X.B.I v (X.crd (∑ i, c i • w i)) = ∑ i, embS D (X.pl v) (c i) • rv X.B.I v (X.crd (w i)) := by
    intro c w
    have hc : X.crd (∑ i, c i • w i) = ∑ i, X.ιE.symm (c i) • X.crd (w i) := by
      funext l

      simp [HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, map_sum, Finset.sum_apply, smul_eq_mul]
    rw [hc]
    unfold rv
    have hv : (fun l => X.B.I.φ v ((∑ i, X.ιE.symm (c i) • X.crd (w i)) l)) =
        ∑ i, embS D (X.pl v) (c i) • fun l => X.B.I.φ v (X.crd (w i) l) := by
      funext l

      simp [Finset.sum_apply, map_sum, X.φ_eq]
    rw [hv, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
  intro b
  dsimp only
  rw [hf b, hM1 v, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, hA b, hsum]
  simp_rw [hf, Matrix.map_apply]

end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqFam Formalism.MainNotions.S.LocNG GlobalTheory.SnFam

namespace GlobalTheory.SnFam.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem ampQ_not_eq_ampG' {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp)]
  · simp
  · intro A hA hne
    simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hA
    exact absurd hA.2 hne

private theorem hasPt_of_isPtG {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := h
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [genT, PB.Terms.ngSet, PB.Terms.genSet] using ht
  · simpa [genT] using hv
  · simpa [NOfG] using hpt

theorem stepFamG_of_fam : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) →
    Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam →
    Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  intro hG6 hH hGen hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH'⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨aF, bF, hF'⟩ := hGen Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW'⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE'⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max aH (max aF (max a5 (max aW (max a4 aE)))),
    max bH (max bF (max b5 (max bW (max b4 bE)))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  simp only [max_le_iff] at hC' hCl
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h4 C' Cl hC'.2.2.2.2.1 hCl.2.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0
    what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  refine ⟨s, hs1, hs2, hs3, ?_⟩
  intro γ hγ S
  have hQ := hF' C' Cl hC'.2.1 hCl.2.1 D large₂ X Y u u hc
  have hP := hasPt_of_isPtG Y u (sc s ν) ν (fun _ => 0) γ hγ
  obtain ⟨Fm, hT, hRel, hTerm, hDs, hrw⟩ :=
    hE' C' Cl hC'.2.2.2.2.2 hCl.2.2.2.2.2 D large₂ X Y u u hc _ Not _ _ hQ γ hP
  have h5' : OrbitFamilyIdentityAt Fm Fm.V0 := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hT (h5 C' Cl hC'.2.2.1 hCl.2.2.1 D large₂ X Y u u hc _ Not _ _ hQ γ hP Fm hT)
  obtain ⟨hWpos, hWle⟩ := hW' C' Cl hC'.2.2.2.1 hCl.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hbk _ Not _ _ hQ γ hP Fm hT hRel hTerm h5'
  have hHt := hH' C' Cl hC'.1 hCl.1 D large₂ X Y u u hc _ _ _ γ Fm hT
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S
    (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) (fun L => ampG L) Fm hT hRel hTerm
    hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) h5' ?_ hWpos ?_ ?_⟩
  · simpa [NOfG] using hHt
  · simpa [NOfG] using hWle
  · intro x _
    have h := hs4 _ Not _ _ hQ γ hP Fm hT x.1 x.2
    rw [ampQ_not_eq_ampG'] at h
    rw [← h]
    rfl

end GlobalTheory.SnFam.Gen
end
end

section

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.NGClass

theorem vec_eq_zero_of_oo {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word} (t : TauC Y u u')
    (h : OOt t = 0) : (Y.tO u u').vec t = 0 := by
  show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold vec ampN
  rw [h]
  simp
  rfl

theorem ngClass_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ (∀ t ∈ (Y.tO u u').ngSet, ∀ t' ∈ (Y.tO u u').ngSet, clsOf Y u u' t = clsOf Y u u' t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') ∧ ∀ t : TauC Y u u', (Y.tO u u').vec t ≠ 0 → t.relevant := by
  intro D X Y u u' hT
  refine ⟨fun t ht => ?_, fun t ht t' ht' heq => ?_, fun t hv => ?_⟩
  · intro h0
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos h0]
  · obtain ⟨hR, -, -⟩ := Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds D X Y u u' hT
    have hm : t' ∈ clsOf Y u u' t' := ⟨ht', rfl, hR t' ht'⟩
    rw [← heq] at hm
    exact hm.2.1.symm
  · by_contra hr
    exact hv (vec_eq_zero_of_oo Y t
      (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
        Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
        Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
        Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr))

end GlobalTheory.NGClass
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem transport_J_bijective_onto :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F),
      Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  intro D X u F Tr
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  have hinj : Function.Injective Tr.J := by
    intro ξ η h
    have h1 := Tr.J_isom c ξ η
    have h2 := Tr.J_isom c ξ ξ
    have h3 := Tr.J_isom c η ξ
    have h4 := Tr.J_isom c η η
    rw [h] at h1 h2 h3
    rw [h4] at h1 h2 h3
    have h0 : ⟪ξ - η, ξ - η⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, ← h1, ← h2, ← h3]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  refine ⟨hinj, ?_⟩
  obtain ⟨J₀, -, hJ₀⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u F Tr.wt ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  exact GlobalTheory.conjLinear_onto_of_injective_of_le_range (X.Vpi u) _ _ J₀ Tr.J hJ₀ hinj Tr.J_val

end GlobalTheory
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictInto_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  intro D X u F Tr hK hσ hL T
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
    (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
    ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
    (fun h => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1)
    (fun h hk hy => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).2 hk hy)
    hΓ
    (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
    (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
    (shP X u T.1) (hφ T)
  rw [Formalism.L2.Forms.Mu0_iff F.val0]
  refine ⟨_, key, ?_⟩
  funext c z
  have hc : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c :=
    Φ.symm_apply_eq.2 ((hΦ (Tr.hc c) _).1 (Tr.hc_rep c)).symm
  simp only [Formalism.L2.Forms.res, LinearMap.funLeft_apply, hc]
  show Tr.J (shP X u T.1 (Tr.hc c)) z = Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY (F.val0.eY.symm z))
  rw [Equiv.apply_symm_apply]

end GlobalTheory.St
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColClass

theorem classes_and_weight : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ClsMatch X Tr hK ∧ (Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ c, (D.mem u).C.wt 0 c = 1) := by
  intro D X u F Tr hK hsig hLM
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hsig
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  have hc : ∀ c, Tr.hc c = Φ.symm (F.cls0.y c * Tr.h0⁻¹) := fun c => by
    rw [MulEquiv.eq_symm_apply]
    exact (hΦ _ _).1 (Tr.hc_rep c)
  have hKu : ∀ h : Hfin X u, h ∈ Ku X u hK ↔
      (((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) : GL _ _) ∈ F.cls0.lev.U :=
    fun h => (hLM.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1
  have key := GlobalTheory.ClassDict.classReps_dictionary D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hfin X u) (iotaF X u) (Ku X u hK)
    Φ Tr.h0 hKu h1 h2 ((D.mem u).C.cls 0) F.cls0.y F.cls0.y_bij
  refine ⟨fun h => ?_, fun hst c => ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := key.1 h
    refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
    · obtain ⟨γ, κ, e⟩ := hc1
      exact ⟨γ, κ, by rw [hc]; exact e⟩
    · obtain ⟨γ, κ, e⟩ := hc'
      exact ⟨γ, κ, by rw [← hc]; exact e⟩
  · have hsub : Subsingleton ((D.mem u).C.stab 0 c) := by
      refine ⟨fun s t => ?_⟩
      have h1' : ∀ s : (D.mem u).C.stab 0 c, s = 1 := by
        intro s
        apply F.cls0.stabI_inj c
        rw [map_one]
        apply Subtype.ext
        have hr := (F.cls0.stabI_range c (F.cls0.stabI c s)).1 ⟨s, rfl⟩
        exact key.2 hst c _ (F.cls0.stabI c s).2 hr
      rw [h1' s, h1' t]
    have : Nat.card ((D.mem u).C.stab 0 c) = 1 := by
      haveI : Unique ((D.mem u).C.stab 0 c) := uniqueOfSubsingleton 1
      exact Nat.card_unique
    simp [Formalism.BasicNotions.ColumnChain.wt, this]

end GlobalTheory.ColClass
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.map_conj_unipotentHaar_eq_smul : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r), 0 < L.κN → L.κN ≠ ⊤ → ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ n, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ a * n * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN := by
  first | exact @GlobalTheory.NConjHaar.map_conj_eq_smul | exact GlobalTheory.NConjHaar.map_conj_eq_smul | (intros; apply GlobalTheory.NConjHaar.map_conj_eq_smul <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.gramFibreMeasure_freeTuple_ne_zero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  first | exact @GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | exact GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | (intros; apply GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreInvariant

theorem fibre_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib hfib S g
  obtain ⟨-, -, -, h4, -, -, -, -, ha⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  obtain ⟨-, hact⟩ := ha a
  haveI := h4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ k : HA (Fv F v) σ J,
      Continuous (fun X : Fin a → Fin n → Fv F v ⊗[F] E => k • X) :=
    fun k => hact.comp (Continuous.prodMk continuous_const continuous_id)
  let T : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X => g • X
      invFun := fun X => g⁻¹ • X
      left_inv := fun X => inv_smul_smul g X
      right_inv := fun X => smul_inv_smul g X
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  let Tm := T.toMeasurableEquiv
  have hTm : ∀ X, Tm X = g • X := fun X => rfl
  have hgram : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E,
      gramR (Fv F v) σ J (g • X) = gramR (Fv F v) σ J X := by
    intro X
    funext i j
    exact hR_lin g (X i) (X j)
  have hli : ∀ (k : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) X → LinearIndependent (Fv F v ⊗[F] E) (k • X) := by
    intro k X hX
    have hinj : Function.Injective (lin (Fv F v) σ J k) :=
      Function.LeftInverse.injective (g := lin (Fv F v) σ J k⁻¹) (fun x => lin_inv_lin (g := k) (x := x))
    exact hX.map' (lin (Fv F v) σ J k) (LinearMap.ker_eq_bot.mpr hinj)
  have hpre : ∀ b : HermR (Fv F v) σ a,
      Tm ⁻¹' (gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}) =
        gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro b
    ext X
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, hTm, hgram]
    refine and_congr_right fun _ => ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hU : Tm ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hTm]
    refine ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hμT : μ.map Tm = μ := GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant F E σ hCM n J hJ v a μ hμ g
  let fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E) := fun b => (fib b).map Tm
  have hfib' : IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' := by
    refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
    · show (fib b).map Tm _ = 0
      rw [Tm.map_apply, Set.preimage_compl, hpre]
      exact hfib.1 b
    · have e1 : ∀ b, ∫⁻ x, φ x ∂(fib' b) = ∫⁻ x, φ (Tm x) ∂(fib b) := fun b =>
        lintegral_map_equiv φ Tm (μ := fib b)
      simp only [e1]
      rw [← hfib.2.1 (fun x => φ (Tm x)) (hφ.comp Tm.measurable)]
      conv_lhs => rw [← hμT]
      rw [Tm.restrict_map, lintegral_map_equiv, hU]
    · have h3 := hfib.2.2 (φ ∘ Tm) (hφc.comp T.continuous) (hφs.comp_homeomorph T) (by
        show tsupport (φ ∘ T) ⊆ _
        rw [tsupport_comp_eq_preimage φ T]
        intro X hX
        have : Tm X ∈ {X | LinearIndependent (Fv F v ⊗[F] E) X} := hφU hX
        rw [← Set.mem_preimage, hU] at this
        exact this)
      refine ⟨fun b hb => (integrable_map_equiv Tm φ).mpr (h3.1 b hb), ?_⟩
      refine h3.2.congr fun b _ => ?_
      exact MeasureTheory.integral_map_equiv Tm φ
  have hu := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hCM n J hJ v a μ ν hμ hν fib hfib fib' hfib'
  show (fib S).map Tm = fib S
  exact (congrFun hu S).symm

end GlobalTheory.LocalFibreInvariant
end
