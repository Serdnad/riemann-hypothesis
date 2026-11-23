module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle318
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.LinSpace

variable {D : D7}

theorem heisO_add' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp [heisO, mul_add]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w; simp [heisO]; ring

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) :
    heisO ψ S T u 0 = 0 := by
  funext w; simp [heisO]

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi := by intro γ w; simp
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' ψ S T u⟩
  cont := continuous_const
  smooth := by intro k L _ _ w; exact contDiff_const }

theorem isThetaFunO_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := {
  quasi := by intro γ w; simp [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, ?_, ?_⟩
    · rw [AddSubgroup.coe_inf]; exact hU.inter hV
    · intro u hu h0
      rw [heisO_add', hUf u hu.1 h0, hVg u hu.2 h0]
  cont := hf.cont.add hg.cont
  smooth := by
    intro k L hL hL' w
    exact (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w) }

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (c : ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi := by intro γ w; simp [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', hUf u hu h0]⟩
  cont := continuous_const.mul hf.cont
  smooth := by
    intro k L hL hL' w
    exact contDiff_const.mul (hf.smooth k L hL hL' w) }

end GlobalTheory.LocMod.LinSpace


open GlobalTheory.LocMod.LinSpace in
theorem GlobalTheory.LocMod.Place.isModel_linear : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), p.IsModel ψ FS FT 0 ∧ ∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FT (T₁ + T₂) ∧ ∀ c : ℂ, p.IsModel ψ FS FT (c • T₁) := by
  intro D k _ _ _ _ p ψ Y Y' _ _ _ _ S T FS FT
  refine ⟨⟨fun Φ => isThetaFunO_zero ψ S T, ?_, ?_⟩, ?_⟩
  · intro x Φ Φ' _; simp [heisO_zero']
  · intro y _ Φ Φ' _; simp [heisO_zero']
  · intro T₁ T₂ h₁ h₂
    refine ⟨⟨fun Φ => isThetaFunO_add (h₁.theta Φ) (h₂.theta Φ), ?_, ?_⟩, fun c => ⟨fun Φ => isThetaFunO_smul c (h₁.theta Φ), ?_, ?_⟩⟩
    · intro x Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.trans x Φ Φ' h, h₂.trans x Φ Φ' h, heisO_add']
    · intro y hy Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.modul y hy Φ Φ' h, h₂.modul y hy Φ Φ' h, heisO_add']
    · intro x Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.trans x Φ Φ' h, heisO_smul']
    · intro y hy Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.modul y hy Φ Φ' h, heisO_smul']
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

namespace Place

def intInd (Y Y' : Type) : Matrix Y Y' k → ℂ := Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1

def tensorAt (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) : WO S T → ℂ :=
  fun t => Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)

def tensorL (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := p.tensorAt FS FT Φ Ψ.1
  map_add' Ψ Ψ' := by
    funext t
    simp only [tensorAt, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c Ψ := by
    funext t
    simp only [tensorAt, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorL_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : SB (Matrix Y Y' k)) :
    p.tensorL FS FT Φ Ψ = p.tensorAt FS FT Φ Ψ.1 := rfl

def tensorOne (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ (intInd Y Y')
  map_add' Φ Φ' := by
    funext t
    simp only [tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorOne_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    p.tensorOne FS FT Φ = p.tensorAt FS FT Φ (intInd Y Y') := rfl

end Place
end GlobalTheory.LocMod
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.SBOfHalf

theorem exists_sb_ext_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT Λ hAo hAc Φ hΦ
  classical
  set A : AddSubgroup (Matrix Y Y' k) := Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) with hA
  obtain ⟨hsupp, k₀, hk₀, hinv, hsup⟩ := hΦ
  have hkF : ((k₀ : D.host.F)) ≠ 0 := Nat.cast_ne_zero.2 hk₀.ne'
  have hkk : ((k₀ : k)) ≠ 0 := by
    have h := (map_ne_zero (p.π.comp (algebraMap D.host.F (AE D)))).2 hkF
    simpa using h
  have hupA : ∀ a : Matrix Y Y' k, a ∈ A ↔ p.up FS FT a ∈ Λ := fun a => Iff.rfl
  have hnsmul : ∀ (x : Matrix Y Y' k), k₀ • x = (k₀ : k) • x := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k]
  have hup_nsmul : ∀ (x : Matrix Y Y' k), p.up FS FT (k₀ • x) = k₀ • p.up FS FT x := fun x =>
    map_nsmul (GlobalTheory.LocMod.Witness.upH p FS FT) k₀ x
  let f : Matrix Y Y' k → ℂ := fun x => Φ (p.up FS FT x)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hV : IsOpen {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} :=
      hAo.preimage (continuous_const_smul _)
    have h0 : (x - x) ∈ {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} := by
      simp only [sub_self, Set.mem_setOf_eq, smul_zero]; exact A.zero_mem
    have hn := (continuous_sub_right x).continuousAt.preimage_mem_nhds (hV.mem_nhds h0)
    filter_upwards [hn] with y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hy' : y = x + k₀ • ((k₀ : k)⁻¹ • (y - x)) := by
      rw [hnsmul, smul_smul, mul_inv_cancel₀ hkk, one_smul, add_sub_cancel]
    show Φ (p.up FS FT y) = Φ (p.up FS FT x)
    rw [hy', GlobalTheory.LocMod.Witness.up_add, hup_nsmul]
    exact hinv _ hy (GlobalTheory.LocMod.Witness.up_half p FS FT _) _
  have hcpt : HasCompactSupport f := by
    refine HasCompactSupport.intro (hAc.image (continuous_const_smul ((k₀ : k)⁻¹))) fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨k₀ • x, ?_, ?_⟩
    · show p.up FS FT (k₀ • x) ∈ Λ
      rw [hup_nsmul]; exact hsup _ hne
    · show (k₀ : k)⁻¹ • k₀ • x = x
      rw [hnsmul, smul_smul, inv_mul_cancel₀ hkk, one_smul]
  refine ⟨⟨f, hloc, hcpt⟩, ?_⟩
  funext t
  rw [GlobalTheory.LocMod.Witness.ext_apply]
  split_ifs with ht
  · show Φ (p.up FS FT (p.down FS FT t)) = Φ t
    rw [GlobalTheory.LocMod.Witness.up_down p FS FT ht]
  · by_contra h
    exact ht (hsupp t (Ne.symm h))

end GlobalTheory.SBOfHalf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.LocMod.FrameChange

variable {k : Type} [Field k]
variable {N M : ℕ} {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

def chg (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : Matrix Z Z' k :=
  GT.γ * FT.β * x * (FS.γ * GS.β)

theorem chg_inv (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : chg GS GT FS FT (chg FS FT GS GT x) = x := by
  simp only [chg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GT.β GT.γ, GT.βγ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul,
    ← Matrix.mul_assoc GS.β GS.γ, GS.βγ, Matrix.one_mul, FS.γβ, Matrix.mul_one]

theorem frame_sandwich (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : GT.β * chg FS FT GS GT x * GS.γ = FT.β * x * FS.γ := by
  simp only [chg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GT.β GT.γ, GT.βγ, Matrix.one_mul, GS.βγ, Matrix.mul_one]

theorem chg_add (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x y : Matrix Y Y' k) : chg FS FT GS GT (x + y) = chg FS FT GS GT x + chg FS FT GS GT y := by
  simp only [chg, Matrix.mul_add, Matrix.add_mul]

variable [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_chg (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    Continuous (chg FS FT GS GT) := by
  unfold chg
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def chgH (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun := chg FS FT GS GT
  invFun := chg GS GT FS FT
  left_inv := chg_inv FS FT GS GT
  right_inv := chg_inv GS GT FS FT
  continuous_toFun := continuous_chg FS FT GS GT
  continuous_invFun := continuous_chg GS GT FS FT

def pull (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    SB (Matrix Z Z' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => Φ.1 (chg FS FT GS GT x),
    ⟨Φ.2.1.comp_continuous (continuous_chg FS FT GS GT),
     Φ.2.2.comp_homeomorph (chgH FS FT GS GT)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.LocMod.FrameChange

namespace GlobalTheory.LocMod.Place

open GlobalTheory.LocMod.FrameChange

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem up_chg {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (GS : Frame k S.rank Z') (GT : Frame k T.rank Z)
    (x : Matrix Y Y' k) : p.up GS GT (chg FS FT GS GT x) = p.up FS FT x := by
  unfold up
  rw [frame_sandwich]

theorem exists_isModel_chg (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Z Z' : Type) [Fintype Z]
    [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (GS : Frame k S.rank Z') (GT : Frame k T.rank Z)
    (ψ : AddChar (AF D.host.F) ℂ) :
    ∀ Tm, p.IsModel ψ FS FT Tm → ∃ Tm', p.IsModel ψ GS GT Tm' ∧
      ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)),
        (∀ x, Φ.1 x = Φ'.1 (GT.γ * FT.β * x * (FS.γ * GS.β))) → Tm' Φ' = Tm Φ := by
  intro Tm hTm
  refine ⟨Tm.comp (pull FS FT GS GT), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro Φ'
    exact hTm.theta _
  · intro x Φ' Φ'' h
    have := hTm.trans (chg GS GT FS FT x) (pull FS FT GS GT Φ') (pull FS FT GS GT Φ'') (by
      intro t
      change Φ''.1 (chg FS FT GS GT t) = Φ'.1 (chg FS FT GS GT (t + chg GS GT FS FT x))
      rw [h, chg_add, chg_inv])
    simpa [LinearMap.comp_apply, up_chg, chg_inv] using this
  · intro y hy Φ' Φ'' h
    have := hTm.modul y hy (pull FS FT GS GT Φ') (pull FS FT GS GT Φ'') (by
      intro t
      change Φ''.1 (chg FS FT GS GT t) = ψ (symplO S T (p.up FS FT t) y) * Φ'.1 (chg FS FT GS GT t)
      rw [h, up_chg])
    simpa [LinearMap.comp_apply] using this
  · intro Φ Φ' h
    change Tm (pull FS FT GS GT Φ') = Tm Φ
    congr 1
    exact Subtype.ext (funext fun x => (h x).symm)

end GlobalTheory.LocMod.Place
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.StdHomDown

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int_of_isIntegral (q : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : IsIntegral ℤ x) :
    q.pr (incA D x) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D x)) := hx.map ((q.pr.comp (incA D)).toIntAlgHom)
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h1.tower_top

theorem star_isIntegral {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem tmul_eq (α : AF D.host.F) (y : D.host.E) :
    (α ⊗ₜ[D.host.F] y : AE D) = algebraMap (AF D.host.F) (AE D) α * incA D y := by
  change _ = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem down_mem_integer : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (c : k), c ≠ 0 → (∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / c ∈ 𝒪[k]) → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = c • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k] := by
  intro D k _ _ _ _ q S T c hc hAA FS FT _ hγT hγS u hu
  set Gw : Matrix (Fin S.rank) (Fin S.rank) k := (HSpace.gram S).map (fun a => q.pr (incA D a)) with hGw
  have hGβ : Gw * FS.β = c⁻¹ • (1 : Matrix (Fin S.rank) (Fin S.rank) k) := by
    have h := FS.γβ
    rw [hγS, Matrix.smul_mul] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r j
    set lam : k := q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * q.pr (incA D a) with hlam
    let M : Matrix (Fin T.rank) (Fin S.rank) k := Matrix.of fun i l => lam * q.pr (incA D (t i)) * q.pr (incA D (star (s l)))
    have hmap : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T).map q.pr = M * Gw := by
      ext i j

      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, M, hGw, tmul_eq, map_mul, map_sum, hlam]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hd : (Place.ofSplitPt q).down FS FT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ l, star (s l) * S.gram l j)) = c⁻¹ • M := by
      have hπ : (Place.ofSplitPt q).π = q.pr := rfl
      simp only [Place.down, hπ]
      rw [hγT, Matrix.one_mul, hmap, Matrix.mul_assoc, hGβ, Matrix.mul_smul, Matrix.mul_one]
    rw [hd, Matrix.smul_apply, smul_eq_mul]
    have e : c⁻¹ * M r j = q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * (q.pr (incA D a) / c) *
        q.pr (incA D (t r)) * q.pr (incA D (star (s j))) := by
      simp only [M, Matrix.of_apply, hlam]; field_simp
    rw [e]
    refine mul_mem (mul_mem (mul_mem (GlobalTheory.SplitCharCond.pr_pair_int q hα) (hAA a ha)) ?_) ?_
    · exact pr_int_of_isIntegral q (ht r)
    · exact pr_int_of_isIntegral q (star_isIntegral (hs j))
  | zero =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT 0 = 0 := map_zero (Witness.downH (Place.ofSplitPt q) FS FT)
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro r j
    rw [Witness.down_add, Matrix.add_apply]
    exact add_mem (hx r j) (hy r j)
  | neg x _ hx =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT (-x) = -(Place.ofSplitPt q).down FS FT x :=
      map_neg (Witness.downH (Place.ofSplitPt q) FS FT) x
    rw [this, Matrix.neg_apply]
    exact neg_mem (hx r j)

end GlobalTheory.LocMod.StdHomDown
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.OutsideOrth

theorem mul_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D),
    PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  intro D k _ _ _ _ p P PP e hPP hp he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun P' hP' => ?_
  rw [mul_comm]
  exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split hp) hp (hes P' hP')
    (fun h => hPP (h ▸ hP'))

end GlobalTheory.LocMod.OutsideOrth
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChainTw.StepExpTw

theorem twStepExpVac : ∀ D : D7, ForStepQ D fun c _ k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (GlobalTheory.Chain.expS D ⟨k, hk⟩) (GlobalTheory.Chain.expT D ⟨k, hk⟩) p.ω ∧
      GlobalTheory.Chain.IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c w hw k _ s s' hs hs' p hp hk
  obtain ⟨hr, _, hsf⟩ := hs
  obtain ⟨hr', _, hsf'⟩ := hs'
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => StepExp.chrStep_exp' hw.com ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨f₀, hv⟩ := hp.vec
  have hrk : s.V.rank ≤ s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hsf.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hsf'.rank
    rw [h1, h2]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right D.R.t (Nat.le_succ k)) D.R.r
  obtain ⟨a, b, d⟩ := StepVac.stepVec_vac hsf.selfDual hsf'.selfDual hrk hv
  exact { theta := a, ne := b, vac := d }

end GlobalTheory.ChainTw.StepExpTw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.selfDualLattices_conjugate_at_finitePlace : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  first | exact @GlobalTheory.FinPl.SelfDualConj.conj_at_place | exact GlobalTheory.FinPl.SelfDualConj.conj_at_place | (intros; apply GlobalTheory.FinPl.SelfDualConj.conj_at_place <;> assumption)
end
