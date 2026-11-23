module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NfinOfRatN
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle004

@[expose] public section

section

noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW

def NRatBridge : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (δ : X.B.I.GA),
    (toHA X.B.I hb δ ∈ (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J :
        Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      toHA X.B.I hb δ ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ↔
    (δ ∈ X.B.I.GFset ∧ δ.1 ∈ X.NinfU u ∧ δ.2 ∈ X.NfinU u)

open NRatW in
theorem nRatBridge_holds : NRatBridge := by
  intro D X hb u δ
  obtain ⟨hinfB, hfinB⟩ := toHA_isBridge X.B.I hb δ
  constructor
  · rintro ⟨hF, hN⟩
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hF)
    have hmat : HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ) =
        Formalism.UG.bc (inclR (AF X.B.I.F)) γ := hγe.symm
    have hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ) :
        GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F)) := by
      rw [hmat]; rfl
    have hRat := ratN_of_AF X u _ _ hM hN
    have hinf : ∀ v, Formalism.MainNotions.S.uMat (δ.1 v) =
        (X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v :=
      fun v => (hinfB v).trans (ofHAInf_rat X.B.I _ γ hmat v)
    have hfin : X.B.I.fmat δ.2 =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) :=
      hfinB.trans (ofHAFin_rat X.B.I _ γ hmat)
    exact ⟨⟨γ, hγ, hinf, hfin⟩, ninf_of_ratN X u _ δ.1 hinf hRat, nfin_of_ratN X u _ δ.2 hfin hRat⟩
  · rintro ⟨⟨γ, hγ, hinf, hfin⟩, -, hNf⟩
    have hRat := ratN_of_fin X u _ δ.2 hfin hNf
    have hU : Formalism.UG.bc (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) γ ∈
        HR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
      have hγ' : Formalism.UG.cT (starRingEnd X.B.I.E) (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
          (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hγ
      have e1 : Formalism.UG.cT (sigR (AF X.B.I.F) X.B.I.cm.sig)
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) =
          (Formalism.UG.cT (starRingEnd X.B.I.E) (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)).map
            (inclR (AF X.B.I.F)) := by
        ext i j
        simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]
        rfl
      show Formalism.UG.cT (sigR (AF X.B.I.F) X.B.I.cm.sig)
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) * JR (AF X.B.I.F) X.B.I.J *
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) = JR (AF X.B.I.F) X.B.I.J
      rw [e1, JR, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
    obtain ⟨h, hmat⟩ : ∃ h : HAd X.B.I, HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h =
        Formalism.UG.bc (inclR (AF X.B.I.F)) γ :=
      ⟨(⟨_, hU⟩ : HR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J), rfl⟩
    have hq : (toHA X.B.I hb).symm h = δ := by
      obtain ⟨a1, a2⟩ := toHA_isBridge X.B.I hb ((toHA X.B.I hb).symm h)
      rw [ContinuousMulEquiv.apply_symm_apply] at a1 a2
      refine Prod.ext (funext fun v => ?_) ?_
      · exact Subtype.ext (Units.ext ((a1 v).trans ((ofHAInf_rat X.B.I h γ hmat v).trans (hinf v).symm)))
      · exact Subtype.ext (Units.ext (a2.trans ((ofHAFin_rat X.B.I h γ hmat).trans hfin.symm)))
    have hδ : toHA X.B.I hb δ = h := by
      rw [← hq]
      exact (toHA X.B.I hb).apply_symm_apply h
    rw [hδ]
    refine ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, hmat.symm⟩), ?_⟩
    have hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h :
        GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F)) := by
      rw [hmat]; rfl
    exact nsub_of_ratN X u _ h hM hRat

end MassDataMassesW
end
end

section

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

theorem nLevel_holds : NLevel := by
  intro D X u y hyN hyK
  obtain ⟨c, hc, hec, hfc, hzc⟩ := mults X u
  have hxK := X.xu_K u
  have hxiK : (X.xu u)⁻¹ ∈ X.B.I.Kset := Kset_inv hxK
  have hκK : (X.xu u)⁻¹ * y * X.xu u ∈ X.B.I.Kset := Kset_mul (Kset_mul hxiK hyK) hxK
  have hAiA := fmat_inv_mul (X.xu u)
  have hT : ∀ v, (X.B.I.fmat ((X.xu u)⁻¹ * y * X.xu u) - 1) *ᵥ v =
      Tm (X.B.I.fmat (X.xu u)⁻¹) (X.B.I.fmat y) (X.B.I.fmat (X.xu u)) v := by
    intro v
    show (X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat y * X.B.I.fmat (X.xu u) - 1) *ᵥ v = _
    simp only [Tm, sub_mulVec, one_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [sub_mul, one_mul, mul_sub, hAiA, sub_mulVec, one_mulVec]
  have hN : y ∈ Nfin X.B.I X.eR (X.zR u) := hyN
  have hcore := core X hc hec hfc (Kset_Lf hxK) (Kset_Lf hxiK) (Kset_Lf hyK) hAiA (fmat_mul_inv (X.xu u))
    (hA_fmat X.B.I (X.xu u)) (fun a => (X.xu_fix u a).1) hN.1 (incl X.B.I (X.zR u)) hN.2.1 hN.2.2 hzc
  refine ⟨hκK, ?_⟩
  unfold K2cong
  simp only [hT]
  exact hcore

end MassDataMassesW.NLev
end
end
