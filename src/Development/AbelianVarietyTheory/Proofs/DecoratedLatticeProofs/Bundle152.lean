module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle747
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle327
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ p ∈ K, om p f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  first | exact @GlobalTheory.LevelCompact.exists_level_compact | exact GlobalTheory.LevelCompact.exists_level_compact | (intros; apply GlobalTheory.LevelCompact.exists_level_compact <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

namespace GlobalTheory.LineFix



theorem exists_emb_of_fix_line : ∀ {D : D7} {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E),
    IsLineVec L ζ → ∀ (b : GA D S₀), (mt S₀ b *ᵥ (fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k)) →
      ∃ a : GA D A, o.emb (a, 1) = b := by
  intro D S₀ A L o ζ hζ b hb
  have hv : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ (fun k => incA D (ζ k)) := by
    funext k
    exact RingHom.map_mulVec (incA D) o.iB ζ k
  have hr := hζ.1
  obtain ⟨k0, hk0⟩ : ∃ k0 : Fin L.rank, ∀ k, k = k0 :=
    ⟨⟨0, by omega⟩, fun k => Fin.ext (by have := k.2; simp only; omega)⟩
  have hz : ζ k0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun k => by rw [hk0 k, h0]; rfl
    rw [this]; simp
  have hu : IsUnit (incA D (ζ k0)) := (isUnit_iff_ne_zero.2 hz).map (incA D)
  have h1 : mt S₀ b * o.jB = o.jB := by
    have e := hb
    rw [hv, Matrix.mulVec_mulVec] at e
    funext i k
    rw [hk0 k]
    have ei := congrFun e i
    simp only [Matrix.mulVec, dotProduct] at ei
    rw [Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk),
      Fintype.sum_eq_single k0 (fun k hk => absurd (hk0 k) hk)] at ei
    exact hu.mul_right_cancel ei
  have hu2 : GlobalTheory.MixModel.adj (mt S₀ b) * (gA S₀ * mt S₀ b) = gA S₀ := GlobalTheory.MixModel.mt_unitary S₀ b
  have h2' : GlobalTheory.MixModel.adj o.jB * (gA S₀ * (mt S₀ b * o.jA)) = 0 := by
    calc GlobalTheory.MixModel.adj o.jB * (gA S₀ * (mt S₀ b * o.jA))
        = GlobalTheory.MixModel.adj (mt S₀ b * o.jB) * (gA S₀ * (mt S₀ b * o.jA)) := by rw [h1]
      _ = GlobalTheory.MixModel.adj o.jB * (GlobalTheory.MixModel.adj (mt S₀ b) * (gA S₀ * (mt S₀ b * o.jA))) := by
          rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc]
      _ = 0 := by rw [GlobalTheory.MixModel.cancel₃ hu2, o.gram_BA]
  have h2 : o.pB * (mt S₀ b * o.jA) = 0 := by
    rw [o.pB_eq]; simp only [Matrix.mul_assoc]; rw [h2', Matrix.mul_zero]
  have h3 : mt S₀ b * o.jA = o.jA * (o.pA * (mt S₀ b * o.jA)) := by
    calc mt S₀ b * o.jA = (o.jA * o.pA + o.jB * o.pB) * (mt S₀ b * o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA * (o.pA * (mt S₀ b * o.jA)) := by
          rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc o.jB, h2, Matrix.mul_zero, add_zero]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Mx D A.rank A.rank, mt S₀ b * o.jA = o.jA * a₀ := ⟨_, h3⟩
  have h4 : GlobalTheory.MixModel.adj a₀ * (gA A * a₀) = gA A := by
    have e : GlobalTheory.MixModel.adj (mt S₀ b * o.jA) * (gA S₀ * (mt S₀ b * o.jA)) = gA A := by
      rw [GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ hu2, o.gram_AA]
    rw [ha₀, GlobalTheory.MixModel.adj_mul, Matrix.mul_assoc, GlobalTheory.MixModel.cancel₃ o.gram_AA] at e
    exact e
  have e3 : mt S₀ b * o.jA * o.pA + mt S₀ b * o.jB * o.pB = mt S₀ b * (o.jA * o.pA + o.jB * o.pB) := by
    rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
  have e4 : mt S₀ b * (o.jA * o.pA + o.jB * o.pB) = mt S₀ b := by
    rw [o.sum_eq_one]; exact Matrix.mul_one _
  refine ⟨GlobalTheory.MixModel.ofMat A a₀ h4, GlobalTheory.MixModel.mt_injective S₀ ?_⟩
  have e1 : mt S₀ (o.emb (GlobalTheory.MixModel.ofMat A a₀ h4, 1)) = o.jA * a₀ * o.pA + o.jB * o.pB := by
    rw [OrthDec.mt_emb, GlobalTheory.MixModel.mt_ofMat, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have e2 : o.jA * a₀ * o.pA + o.jB * o.pB = mt S₀ b * o.jA * o.pA + mt S₀ b * o.jB * o.pB := by
    rw [← ha₀, h1]
  rw [e1, e2, e3, e4]

end GlobalTheory.LineFix
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


theorem _root_.GlobalTheory.T.exists_rational_wittFlagCoordinates_of_mem_unipotent : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ (c : skewA D ρ) (b : Mx D ρ V₀.rank) (u : UX D ρ), γ = d.nC c * (d.nB b * d.levi u.1) ∧ c.1 ∈ ratMx D ρ ρ ∧ b ∈ ratMx D ρ V₀.rank ∧ u ∈ UXQ D ρ := by
  first | exact @GlobalTheory.RatCoord.rat_coords_of_mem_flagN | exact GlobalTheory.RatCoord.rat_coords_of_mem_flagN | (intros; apply GlobalTheory.RatCoord.rat_coords_of_mem_flagN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  first | exact @GlobalTheory.Unf.fjKer_eq_om_apply | exact GlobalTheory.Unf.fjKer_eq_om_apply | (intros; apply GlobalTheory.Unf.fjKer_eq_om_apply <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


theorem _root_.GlobalTheory.T.quasiMeasurePreserving_adelicUnitriangular_left_mul : ∀ (D : D7) (ρ n : ℕ) (μ : Measure (Mx D ρ n)), μ.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (fun b : Mx D ρ n => u.1.1 ⬝ b) μ μ := by
  first | exact @GlobalTheory.LeftUniQmp.qmp_left_uni | exact GlobalTheory.LeftUniQmp.qmp_left_uni | (intros; apply GlobalTheory.LeftUniQmp.qmp_left_uni <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


theorem _root_.GlobalTheory.T.quasiMeasurePreserving_skewHermitianCongruence_unitriangular : ∀ (D : D7) (ρ : ℕ) (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (skewConj u.1.1) lC lC := by
  first | exact @GlobalTheory.Unf.SkewConjQmp.quasiMeasurePreserving_skewConj | exact GlobalTheory.Unf.SkewConjQmp.quasiMeasurePreserving_skewConj | (intros; apply GlobalTheory.Unf.SkewConjQmp.quasiMeasurePreserving_skewConj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilRepresentation_rational_translate_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h w, om (γ * g, γ' * h) f w = om (g, h) f (mt T γ'⁻¹ ⬝ w ⬝ mt S γ) := by
  first | exact @GlobalTheory.Unf.om_rat_mul | exact GlobalTheory.Unf.om_rat_mul | (intros; apply GlobalTheory.Unf.om_rat_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealTransSm

open Formalism.MainNotions.StandardLattice

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem infMat_list_prod (hθ : IsInfFam θ) (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    ∀ l : List D.what₂.Tau, l.Nodup →
      infMat D.sp.cm.sig V.gram (θ ρ) (l.map fun τ => atTau θ V τ (u τ)).prod = if ρ ∈ l then u ρ else 1
  | [], _ => by simpa using GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  | a :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_list_prod hθ u hu ρ l hl.2]
    have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V a (hu a)
    by_cases c : ρ = a
    · subst c
      rw [hs.2.1, ite_eq_right hl.1, ite_eq_left List.mem_cons_self, Matrix.mul_one]
    · rw [hs.2.2 ρ c, Matrix.one_mul]
      by_cases d : ρ ∈ l
      · rw [ite_eq_left d, ite_eq_left (List.mem_cons_of_mem a d)]
      · rw [ite_eq_right d, ite_eq_right]
        simp [c, d]

theorem eq_realElt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    g = GlobalTheory.AdelicScalar.realElt θ V (fun τ => infMat D.sp.cm.sig V.gram (θ τ) g) := by
  set u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) g with hu_def
  have hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
  set P := GlobalTheory.AdelicScalar.realElt θ V u with hP
  have hPm : P ∈ GinfC V := by
    refine list_prod_mem fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem V τ (u τ)
  have e : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) P = infMat D.sp.cm.sig V.gram (θ ρ) g := fun ρ => by
    rw [hP, GlobalTheory.AdelicScalar.realElt, infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
      ite_eq_left (Finset.mem_toList.2 (Finset.mem_univ ρ))]
  refine mul_inv_eq_one.1 (GlobalTheory.PointAtPlace.eq_one_of_mem V _ ((GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 _ fun ρ => ?_)
    (mul_mem hg (inv_mem hPm)))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e, ← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel,
    GlobalTheory.PointAtPlaceHom.infMat_one]

def smAct (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (τ : D.what₂.Tau) :
    M.sm τ →ₗ[ℂ] M.sm τ :=
  (M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) g)).toLinearMap.restrict fun _ hw =>
    GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ) hw

theorem rTrans_eq_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → ∀ g ∈ GinfC V, ∃ σ : SmT M →ₗ[ℂ] SmT M, ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ MultT θ M J χ, ∀ x, T (σ x) = rTrans g (T x) := by
  intro D θ V S M hθ g hg
  refine ⟨PiTensorProduct.map (smAct hθ M g), fun J χ T hT x => ?_⟩
  have hU : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod]
    let u τ := infMat D.sp.cm.sig V.gram (θ τ) g
    let w : M.Vec := fun τ => smAct hθ M g τ (v τ)
    have hu (τ : D.what₂.Tau) : u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have hw (τ : D.what₂.Tau) : (w τ : M.H τ) = M.rep τ (u τ) (v τ : M.H τ) := rfl
    have translate (U : MMap M) (hU : U ∈ Mult θ M J χ) :
        U w = rTr V (GlobalTheory.AdelicScalar.realElt θ V u) (U v) := by
      induction hU using Submodule.span_induction with
      | mem U hU =>
        have onList (l : List D.what₂.Tau) (hl : l.Nodup) :
            U (fun τ => if τ ∈ l then w τ else v τ) =
              rTr V (l.map fun τ => atTau θ V τ (u τ)).prod (U v) := by
          induction l with
          | nil =>
            funext h
            simp [rTr]
          | cons a l ih =>
            rw [List.nodup_cons] at hl
            have ha := hU.equiv a (u a) (hu a) (fun τ => if τ ∈ l then w τ else v τ)
              (w a) (by simpa only [ite_eq_right hl.1] using hw a)
            rw [ih hl.2] at ha
            have hupdate : (fun τ => if τ ∈ a :: l then w τ else v τ) =
                Function.update (fun τ => if τ ∈ l then w τ else v τ) a (w a) := by
              funext τ
              by_cases hτ : τ = a
              · subst τ
                simp
              · rw [Function.update_of_ne hτ]
                simp [hτ]
            rw [hupdate, ha]
            funext h
            simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
        have hall := onList (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
        simpa [GlobalTheory.AdelicScalar.realElt] using hall
      | zero => funext h; simp [rTr]
      | add U U' _ _ h₁ h₂ =>
        funext h
        simpa only [rTr, add_apply, Pi.add_apply] using
          congrArg₂ (· + ·) (congrFun h₁ h) (congrFun h₂ h)
      | smul a U _ h₁ =>
        funext h
        simpa only [rTr, smul_apply, Pi.smul_apply] using
          congrArg (a • ·) (congrFun h₁ h)
    have key := translate _ hU
    have hreal : GlobalTheory.AdelicScalar.realElt θ V u = g := (eq_realElt hθ hg).symm
    rw [hreal, PiTensorProduct.lift_symm] at key
    simp only [LinearMap.compMultilinearMap_apply] at key
    change c • T (PiTensorProduct.tprod ℂ w) = _
    funext h
    simp only [key, rTr, rTrans, map_smul, Pi.smul_apply]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy]
    funext h
    simp [rTrans]

end GlobalTheory.RealTransSm

end
end

section

open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem position_add (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f + g) = intersection_update_fsHerm_neg_one i f + intersection_update_fsHerm_neg_one i g := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, position_tprod, LinearMap.add_apply]
  rw [← MultilinearMap.map_update_add]

theorem position_mul (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f * g) = intersection_update_fsHerm_neg_one i f ∘ₗ intersection_update_fsHerm_neg_one i g := by
  ext v
  simp [position_tprod]

theorem position_algebraMap (i : ι) (c : ℂ) :
    intersection_update_fsHerm_neg_one i (algebraMap ℂ (Module.End ℂ (K i)) c) = c • LinearMap.id := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, position_tprod, LinearMap.smul_apply, LinearMap.id_apply]
  rw [Module.algebraMap_end_apply, MultilinearMap.map_update_smul, Function.update_eq_self]
  rfl

theorem stable_adjoin_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i))
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    {r : Module.End ℂ (K i)} (hr : r ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ y ∈ N, intersection_update_fsHerm_neg_one i r y ∈ N := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g
  | algebraMap c =>
    intro y hy
    rw [position_algebraMap]
    exact N.smul_mem c hy
  | add x y _ _ hx hy =>
    intro z hz
    rw [position_add]
    exact N.add_mem (hx z hz) (hy z hz)
  | mul x y _ _ hx hy =>
    intro z hz
    rw [position_mul]
    exact hx _ (hy z hz)

theorem exists_finset_position (i : ι) (t : ⨂[ℂ] j, K j) :
    ∃ s : Finset (K i), ∀ f g : Module.End ℂ (K i), (∀ m ∈ s, f m = g m) → intersection_update_fsHerm_neg_one i f t = intersection_update_fsHerm_neg_one i g t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    refine ⟨{u i}, fun f g h => ?_⟩
    rw [map_smul, map_smul, position_tprod, position_tprod, h (u i) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun f g h => ?_⟩
    rw [map_add (f := _), map_add (f := _), hs f g fun m hm => h m (Finset.mem_union_left _ hm),
      hs' f g fun m hm => h m (Finset.mem_union_right _ hm)]

theorem eq_zero_of_subsingleton (i : ι) [Subsingleton (K i)] (t : ⨂[ℂ] j, K j) : t = 0 := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [MultilinearMap.map_coord_zero _ i (Subsingleton.elim _ _), smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end GlobalTheory.TensorIrr

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem stable_all_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i)) (ha : AbsIrr a) [Nontrivial (K i)]
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    (f : Module.End ℂ (K i)) : ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := by
  intro y hy
  obtain ⟨s, hs⟩ := exists_finset_position i y
  obtain ⟨r, hr, hfr⟩ := GlobalTheory.IrrTensor.density a ha.1 ha.2 f s
  rw [hs f r hfr]
  exact stable_adjoin_position i a N hN hr y hy

theorem stable_map (N : Submodule ℂ (⨂[ℂ] j, K j))
    (hN : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N) (f : ∀ i, Module.End ℂ (K i)) :
    ∀ y ∈ N, PiTensorProduct.map f y ∈ N := by
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      intro y hy
      rw [this, LinearMap.comp_apply]
      exact hN i (f i) _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

theorem eq_top_of_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  intro ι _ K _ _ G a ha N hN hne
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnt : ∀ i, Nontrivial (K i) := by
    intro i
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hx0 (eq_zero_of_subsingleton i x)
  have hall : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := fun i f =>
    stable_all_position i (a i) (ha i) N (hN i) f
  obtain ⟨w, hw⟩ : ∃ w, Scal.tform w x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (Scal.eq_of_tform fun w => by rw [h w, map_zero])
  have htp : ∀ v : ∀ i, K i, PiTensorProduct.tprod ℂ v ∈ N := by
    intro v
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (v i)) =
        (Scal.tform w).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext u
      simp [Scal.tform_tprod, MultilinearMap.map_smul_univ]
    have h1 := stable_map N hall (fun i => (w i).smulRight (v i)) x hxN
    rw [hm, LinearMap.smulRight_apply] at h1
    have h2 := N.smul_mem (Scal.tform w x)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hw, one_smul] at h2
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact htp v

end GlobalTheory.TensorIrr
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.petersson_principal_level_continuous_right_invariant : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i σ, IsOpen {h : GA D (Wc D i) | finE (Wc D i) h ∈ lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv)} ∧ ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec, (Continuous fun g => petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂)) ∧ ∀ g, ∀ k ∈ levW R i, petW R i (rTr (Wc D i) (g * k) (U₁ v₁)) (U₂ v₂) = petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂) := by
  exact @GlobalTheory.PrincPet.petW_continuous_rightInv
end
