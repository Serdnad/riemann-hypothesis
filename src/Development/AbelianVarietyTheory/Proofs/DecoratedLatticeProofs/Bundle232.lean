module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.CoefRealSchur

theorem scalar_of_comm {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (P : Module.End ℂ W → Prop) (hirr : ∀ U : Submodule ℂ W, (∀ a, P a → U.map a ≤ U) → U = ⊥ ∨ U = ⊤)
    (T₀ : Module.End ℂ W) (hT : ∀ a, P a → a * T₀ = T₀ * a) : ∃ c : ℂ, T₀ = c • 1 := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T₀
  refine ⟨c, ?_⟩
  have hU : ∀ a, P a → (T₀.eigenspace c).map a ≤ T₀.eigenspace c := by
    intro a ha
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, ← hT a ha, Module.End.mul_apply, hv, map_smul]
  rcases hirr _ hU with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · refine LinearMap.ext fun v => ?_
    have hv : v ∈ T₀.eigenspace c := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    rfl

def repOp {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Module.End ℂ W where
  toFun x := (InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap (B x))
  map_add' x x' := by
    apply ext_inner_right ℂ
    intro w
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' a x := by
    apply ext_inner_right ℂ
    intro w
    simp [InnerProductSpace.toDual_symm_apply, inner_smul_left]

theorem inner_repOp {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (x y : W) : ⟪repOp B x, y⟫_ℂ = B x y := by
  simp [repOp, InnerProductSpace.toDual_symm_apply]

theorem form_eq_smul_inner : ∀ (D : D7) (V : HSp D) (c : CoefA V), c.Is → ∀ (B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ), (∀ u ∈ GinfC V, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y) → ∃ z : ℂ, ∀ x y, B x y = z * ⟪x, y⟫_ℂ := by
  intro D V c hc B hB
  have hirr : ∀ U : Submodule ℂ c.W, (∀ a, (∃ u ∈ GinfC V, c.ρ u = a) → U.map a ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hc.2.2.2.2 U fun h => ?_
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, hc.1 k hk, mul_one]
    exact hU _ ⟨a, ha, rfl⟩
  haveI := hc.2.2.2.1
  have hcomm : ∀ a, (∃ u ∈ GinfC V, c.ρ u = a) → a * repOp B = repOp B * a := by
    rintro _ ⟨u, hu, rfl⟩
    apply LinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    obtain ⟨y', rfl⟩ : ∃ y', y = c.ρ u y' :=
      ⟨c.ρ u⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, hc.2.1, inner_repOp, inner_repOp, hB u hu]
  obtain ⟨z, hz⟩ := scalar_of_comm _ hirr (repOp B) hcomm
  refine ⟨starRingEnd ℂ z, fun x y => ?_⟩
  rw [← inner_repOp B x y, hz, LinearMap.smul_apply, Module.End.one_apply, inner_smul_left]

end GlobalTheory.CoefRealSchur
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Aniso

theorem thetaKernel_rationalSource_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (c : GA D S) (h : GA D T) :
    thetaKO om (γ * c) h f = thetaKO om c h f := by
  unfold thetaKO
  have e : om (γ * c, h) = om (γ, (1 : GA D T)) * om (c, h) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (GQ T).one_mem _ (hω.om_pres (c, h) f hf)

end GlobalTheory.Core.Rk.Aniso

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfGenScalar

theorem addChar_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem exists_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (z : WO S T),
    z ∈ AddSubgroup.closure {u | u ∈ Λ ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e u} →
    ∃ c : ℂ, ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T z f = c • f := by
  intro D ψ S T Λ z hz
  induction hz using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨huΛ, e, he, hh⟩ := hu
    exact ⟨1, fun f hf => by rw [one_smul]; exact hf.2 e he u huΛ hh⟩
  | zero => exact ⟨1, fun f _ => by rw [one_smul]; exact GlobalTheory.SplitScalar.heisO_zero ψ S T f⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨cx, hcx⟩ := ihx
    obtain ⟨cy, hcy⟩ := ihy
    refine ⟨(ψ (symplOH S T x y))⁻¹ * (cx * cy), fun f hf => ?_⟩
    have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T x y f
    rw [hcy f hf, GlobalTheory.SplitScalar.heisO_smul, hcx f hf, smul_smul] at h1
    have hne := addChar_ne_zero ψ (symplOH S T x y)
    rw [mul_smul, mul_comm cx cy, h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
  | neg x _ ihx =>
    obtain ⟨cx, hcx⟩ := ihx
    by_cases h0 : cx = 0
    · refine ⟨0, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, h0, zero_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      have hf0 : f = 0 := by
        have h2 : heisO ψ S T (-x) (0 : WO S T → ℂ) = 0 := by
          simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
        rw [h2] at h1
        exact (smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero ψ _)
      subst hf0
      rw [zero_smul]
      simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
    · refine ⟨ψ (symplOH S T (-x) x) / cx, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, GlobalTheory.SplitScalar.heisO_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]

end GlobalTheory.HalfGenScalar

end
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.AtReal

open Formalism.IndefR.Links

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

theorem cols_heq {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    {m : Dc.Mem} {m' : Dc'.Mem} (hm : HEq m m') :
    Dc.a m = Dc'.a m' ∧ (∀ v, HEq (Dc.Xc m v) (Dc'.Xc m' v)) ∧
      ∀ t (x : Fin (Dc.a m) → K) (x' : Fin (Dc'.a m') → K) (F : Fin (Df.nV t) → K) (F' : Fin (Df'.nV t) → K),
        HEq x x' → HEq F F' → Dc.Pt m t x F = Dc'.Pt m' t x' F' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hm
  refine ⟨rfl, fun v => HEq.rfl, fun t x x' F F' hx hF => ?_⟩
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hF
  rfl

theorem cols_mem {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    (m : Dc.Mem) : ∃ m' : Dc'.Mem, HEq m m' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  exact ⟨m, HEq.rfl⟩

end Gen

theorem heq_fin {α : Type} {n n' : ℕ} (h : n = n') (x : Fin n → α) : ∃ x' : Fin n' → α, HEq x x' := by
  subst h; exact ⟨x, HEq.rfl⟩

theorem heq_fin' {α : Type} {n n' : ℕ} (h : n = n') (x' : Fin n' → α) : ∃ x : Fin n → α, HEq x x' := by
  subst h; exact ⟨x', HEq.rfl⟩

theorem heq_mat {n n' : ℕ} (h : n = n') (M' : Matrix (Fin n') (Fin n') ℂ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, HEq M M' := by
  subst h; exact ⟨M', HEq.rfl⟩

theorem heq_mulVec {n n' : ℕ} (h : n = n') {M : Matrix (Fin n) (Fin n) ℂ} {M' : Matrix (Fin n') (Fin n') ℂ}
    (hM : HEq M M') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : HEq (M.mulVec x) (M'.mulVec x') := by
  subst h; obtain rfl := eq_of_heq hM; obtain rfl := eq_of_heq hx; rfl

theorem heq_fnorm {n n' : ℕ} (h : n = n') {Y : Matrix (Fin n) (Fin n) ℂ} {Y' : Matrix (Fin n') (Fin n') ℂ}
    (hY : HEq Y Y') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : fnorm Y x = fnorm Y' x' := by
  subst h; obtain rfl := eq_of_heq hY; obtain rfl := eq_of_heq hx; rfl

theorem heq_cpt {K : Type} [Field K] (σ : K →+* ℂ) {n n' : ℕ} (h : n = n') {x : Fin n → K} {x' : Fin n' → K}
    (hx : HEq x x') : HEq (cpt σ x) (cpt σ x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

theorem heq_cjv (s : Bool) {n n' : ℕ} (h : n = n') {x : Fin n → ℂ} {x' : Fin n' → ℂ}
    (hx : HEq x x') : HEq (Formalism.L2.SG.JoinSI.cjv s x) (Formalism.L2.SG.JoinSI.cjv s x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop.AtReal

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop

open Formalism.IndefR.Links GlobalTheory.MiTop.AtReal


end GlobalTheory.MiTop

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

open Matrix Formalism.UG

namespace GlobalTheory.Core.Rk.IwArch

section IsoCol

variable {A : Type} [CommRing A]

theorem map_cT_rect (σ : A →+* A) (f : A →+* ℂ) (hσ : ∀ x, f (σ x) = star (f x)) {m p : Type}
    (M : Matrix m p A) : (cT σ M).map f = (M.map f)ᴴ := by
  ext i j
  simp [cT, conjTranspose_apply, hσ]

theorem exists_compact_keep_cols {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1))
    (X : Matrix (Fin n) (Fin r) A) (hX : cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β := by
  set F := RingEquiv.ofBijective f hf
  have hfF : ∀ z : ℂ, f (F.symm z) = z := fun z => F.apply_symm_apply z
  have hfinj : ∀ {p q : Type} (M N : Matrix p q A), M.map f = N.map f → M = N := fun M N h =>
    Matrix.ext fun i j => hf.1 (congrFun (congrFun h i) j)
  set D : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hJm : D.map f = Formalism.REAL.Jm ε := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases he : ε i <;> simp [D, Formalism.REAL.Jm, he]
    · simp [D, Formalism.REAL.Jm, h]

  set h0 := b⁻¹ * g * b with hh0def
  have hh0 : h0 ∈ UJ σ D := hb ▸ conj_mem_UJ σ b hg
  have hh0' : Formalism.REAL.inUJ ε (h0.1.map f) := by
    have e : cT σ h0.1 * D * h0.1 = D := hh0
    have := congrArg (fun M => M.map f) e
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm] at this
    exact this
  let g' : Formalism.REAL.UJ ε := ⟨bc f h0, hh0'⟩

  set Y := (b⁻¹).1 * X with hYdef
  set X' := Y.map f with hX'def
  have hY : cT σ Y * D * Y = 0 := by
    rw [← hb, hYdef, cT_mul]
    calc cT σ X * cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * ((b⁻¹).1 * X)
        = cT σ X * (cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * (b⁻¹).1) * X := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [cT_inv_cancel, hX]
  have hiso0 : X'ᴴ * Formalism.REAL.Jm ε * X' = 0 := by
    have := congrArg (fun M => M.map f) hY
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm, Matrix.map_zero _ (map_zero f)] at this
    exact this
  set W := LinearMap.range X'.mulVecLin with hWdef
  let Wf : Fin 2 → Submodule ℂ (Fin n → ℂ) := ![⊥, W]
  have hflag : GlobalTheory.FlagMeas.IsIsoFlag ε (a := 1) (fun _ => Module.finrank ℂ W) Wf := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Wf]
    · intro i
      fin_cases i
      show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
      rw [finrank_bot, zero_add]
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.mul_assoc, hiso0, Matrix.vecMul_zero, zero_dotProduct]
  obtain ⟨k0, hk0, hk0W⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hflag g'
  have hkeep : ∀ y ∈ W, Formalism.MainNotions.S.uMat (g' * k0⁻¹) *ᵥ y ∈ W := fun y hy => hk0W 1 y hy

  let k1 : GL (Fin n) A := bc (F.symm : ℂ →+* A) (k0 : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hbc : ∀ u : (Matrix (Fin n) (Fin n) ℂ)ˣ, (bc (F.symm : ℂ →+* A) u).1.map f = u.1 := by
    intro u; ext i j; simp [bc, hfF]
  have hk1f : k1.1.map f = Formalism.MainNotions.S.uMat k0 := hbc _
  have hk1if : (k1⁻¹).1.map f = Formalism.MainNotions.S.uMat k0⁻¹ := by
    have : k1⁻¹ = bc (F.symm : ℂ →+* A) ((k0⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
      simp [k1, map_inv]
    rw [this]; exact hbc _
  have hk1D : k1 ∈ UJ σ D := by
    show cT σ k1.1 * D * k1.1 = D
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, hJm]
    exact k0.2
  have hk1one : k1 ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
    show cT σ k1.1 * 1 * k1.1 = 1
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.mul_one]
    exact hk0
  refine ⟨b * k1 * b⁻¹, ?_, ?_, ?_⟩
  · have hk1' : k1 ∈ UJ σ (cT σ b.1 * J * b.1) := by rw [hb]; exact hk1D
    have := conj_mem_UJ σ b⁻¹ hk1'
    rw [cT_inv_cancel, inv_inv] at this
    exact this
  · convert hk1one using 1
    group

  set H := (h0 * k1⁻¹).1 with hHdef
  have hHf : H.map f = Formalism.MainNotions.S.uMat (g' * k0⁻¹) := by
    rw [hHdef, Units.val_mul, Matrix.map_mul, hk1if]
    rfl
  have hcol : ∀ c : Fin r, ∃ w : Fin r → ℂ, X' *ᵥ w = H.map f *ᵥ (X' *ᵥ Pi.single c 1) := by
    intro c
    have hm := hkeep _ (LinearMap.mem_range_self X'.mulVecLin (Pi.single c 1))
    rw [← hHf] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, hw⟩
  choose w hw using hcol
  let β' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i c => w c i
  have hHX : H.map f * X' = X' * β' := by
    ext i c
    have h1 := congrFun (hw c) i
    have e1 : (H.map f * X') i c = (H.map f *ᵥ (X' *ᵥ Pi.single c 1)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl
    have e2 : (X' * β') i c = (X' *ᵥ w c) i := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]; rfl
    rw [e1, e2, h1]
  refine ⟨β'.map F.symm, ?_⟩
  have hβf : (β'.map F.symm).map f = β' := by ext i j; simp [hfF]
  have hHY : H * Y = Y * β'.map F.symm := by
    have e1 : (H * Y).map f = H.map f * X' := Matrix.map_mul
    have e2 : (Y * β'.map F.symm).map f = X' * β' := by rw [Matrix.map_mul, hβf]
    apply hfinj
    rw [e1, e2]
    exact hHX
  have hgk : g * (b * k1 * b⁻¹)⁻¹ = b * (h0 * k1⁻¹) * b⁻¹ := by
    rw [hh0def]; group
  rw [hgk, Units.val_mul, Units.val_mul]
  calc b.1 * H * (b⁻¹).1 * X = b.1 * (H * Y) := by rw [hYdef]; simp only [Matrix.mul_assoc]
    _ = b.1 * ((b⁻¹).1 * X * β'.map F.symm) := by rw [hHY]
    _ = X * β'.map F.symm := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem iw_iso_cols : ∀ {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ), Function.Bijective f → (∀ x, f (σ x) = star (f x)) → ∀ {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool), Formalism.UG.cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1) → ∀ (X : Matrix (Fin n) (Fin r) A), Formalism.UG.cT σ X * J * X = 0 → ∀ g : GL (Fin n) A, g ∈ UJ σ J → ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧ ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β  := by
  intro A _ n r σ f hf hσ J b ε hb X hX g hg
  exact exists_compact_keep_cols σ f hf hσ b ε hb X hX g hg

end IsoCol

end GlobalTheory.Core.Rk.IwArch
end
