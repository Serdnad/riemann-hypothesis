module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle223
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle201
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle226
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heisenbergDeriv_weilTranslate_continuous_combination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  first | exact @GlobalTheory.HeisLineComb.dLine_om_comb | exact GlobalTheory.HeisLineComb.dLine_om_comb | (intros; apply GlobalTheory.HeisLineComb.dLine_om_comb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierJacobiGroup_split_real_finite : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d := by
  first | exact @GlobalTheory.jacGrp_split_inf_fin | exact GlobalTheory.jacGrp_split_inf_fin | (intros; apply GlobalTheory.jacGrp_split_inf_fin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.JacUnimod.jacGrp_rightInv | exact GlobalTheory.JacUnimod.jacGrp_rightInv | (intros; apply GlobalTheory.JacUnimod.jacGrp_rightInv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselGroup_haar_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L) (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.BesUnimod.besGrp_isMulRightInvariant | exact GlobalTheory.BesUnimod.besGrp_isMulRightInvariant | (intros; apply GlobalTheory.BesUnimod.besGrp_isMulRightInvariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_hermitianLine_vector_prescribed_norm : ∀ (D : D7) (c : D.host.E) (ε : ℤˣ), c ≠ 0 → ∃ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ ∧ L.SigOK ∧ star ζ ⬝ᵥ L.gram *ᵥ ζ = ((ε : ℤ) : D.host.E) * (c * star c) ∧ ∀ τ, L.sig τ = if ε = 1 then (1, 0) else (0, 1) := by
  first | exact @GlobalTheory.HermLine.exists_line_vec | exact GlobalTheory.HermLine.exists_line_vec | (intros; apply GlobalTheory.HermLine.exists_line_vec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselGroup_split_real_finite : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L), ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  exact GlobalTheory.BesSplit.besGrp_split
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi



theorem colForm_of_dec {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u)
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0))
    (hθ : IsInfFam θ) (hE : _root_.GlobalTheory.Core.Mi.IdE X) (hAd : B.Adapted tr.wt) (hH0 : IsTransportAdelicCorrection tr a₀)
    (hLM : Formalism.L2.SG.ColDict.LevelMatch X tr hK) (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0))
    (c : (D.mem u).C.cls 0) (γ : GL (Fin (D.R.N 0)) D.host.E) (κ : F.cls0.lev.U)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)))
    (hx : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1) :
    (F.cls0.lev.chi κ : ℂ) * GlobalTheory.AdForm.atFr (fun z => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z)
        (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) := by
  obtain ⟨aγ, hQ, hfγ, hiγ⟩ := GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace D θ hθ γ hγ
  obtain ⟨γ', hγ'1, hγ'2⟩ := GlobalTheory.T.secondModel_image_rational_stabilizerPoint D X h u ψ B aγ hQ
  have finv : ∀ (a : GA D (D.sp.X 0)) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)),
      Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1 →
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = Bm := by
    intro a Bm hB
    have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
      rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have iinv : ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ),
      Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 →
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = Bm := by
    intro a τ Bm hB
    have h1 : GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = 1 := by
      rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ) *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have hfγi : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 := by
    apply finv
    rw [hfγ, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hh : ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    have : (tr.h0⁻¹).1.1 * tr.h0.1.1 = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    exact this
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ = (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hfa0i : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ = ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    finv _ _ (by rw [e0]; exact hh)
  have hiγi : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ := by
    intro τ
    apply iinv
    rw [hiγ τ]
    unfold Formalism.L2.Forms.atInf
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨r, hr⟩ : ∃ r, r = aγ⁻¹ * g * a₀⁻¹ := ⟨_, rfl⟩
  have hg : g * a₀⁻¹ = aγ * r := by rw [hr]; group
  have hκP : κ.1 ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((F.cls0.lev.U_eq κ.1).1 κ.2).1
  obtain ⟨yk, hyk⟩ : ∃ yk : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), yk = tr.h0 * ⟨κ.1, hκP⟩ * tr.h0⁻¹ := ⟨_, rfl⟩
  have hfr : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r =
      ((F.cls0.y c * tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    rw [hr, unitaryAdelicPointFiniteMatrix_base_space_mul, unitaryAdelicPointFiniteMatrix_base_space_mul, hfγi, hx, hfa0i]
    have : (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 *
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1 *
        (tr.h0⁻¹).1.1 = (F.cls0.y c * tr.h0⁻¹).1.1 * yk.1.1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hyk]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
      group
    exact this
  have hir : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ := by
    intro τ
    rw [hr, unitaryAdelicPointInfiniteMatrices_base_space_mul, unitaryAdelicPointInfiniteMatrices_base_space_mul, hiγi, unitaryAdelicPointInfiniteMatrices_eq_one_of_finite θ a₀⁻¹ (inv_mem hH0.1), mul_one]

  have hRfin := GlobalTheory.T.secondModel_finitePart_frameActionMatrix D X h u ψ B F tr hE hAd r
  have hreal := GlobalTheory.T.secondModel_realPart_matrix_frame D X h u ψ B F tr θ hθ hE hAd r
  obtain ⟨κ'', hκ''⟩ : ∃ κ'' : Hfin X u, κ'' = (tr.hc c)⁻¹ * (B.toH r).2 := ⟨_, rfl⟩
  have hmulκ : ((tr.hc c : Hfin X u) : X.B.I.Gf) * (κ'' : X.B.I.Gf) = ((B.toH r).2 : X.B.I.Gf) := by
    rw [hκ'', ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hRk : RepM X tr.wt tr.ιA (κ'' : X.B.I.Gf) (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine RepM_cancel (tr.hc_rep c) ?_
    rw [hmulκ, ← hfr]
    exact hRfin
  have hRF : Formalism.L2.SG.ColDict.RepF X tr.wt tr.ιA (κ'' : X.B.I.Gf) yk := hRk
  have hconj : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) = κ.1 := by
    rw [hyk]
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  have hκU : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈ F.cls0.lev.U := hconj ▸ κ.2
  obtain ⟨hmemIff, hpsi⟩ := hLM.2 κ'' yk hRF
  have hmem : κ'' ∈ Ku X u hK := hmemIff.2 hκU
  have hpsiv := hpsi hmem hκU
  have hchi : ((F.cls0.lev.chi ⟨_, hκU⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi κ : ℂˣ) : ℂ) := by
    congr 2
    exact Subtype.ext hconj

  have hdet : ∀ τ, IsUnit (GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ((F.val0.eY y).2 τ)
    refine Matrix.isUnit_det_of_right_inverse (B := GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r⁻¹ τ) ?_
    rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
  let z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) :=
    ⟨fun τ => GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ, hdet⟩
  have htr : Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH r).1 : X.B.I.Ginf)) (F.val0.eY y) z' := by
    intro τ
    show _ = _ * _
    rw [hreal τ]
  have hriesz := GlobalTheory.T.realRepresentation_moves_rieszVector_frame D X u F tr ((B.toH r).1 : X.B.I.Ginf) (B.toH r).1.2 (F.val0.eY y) z' htr

  have hlhs : GlobalTheory.AdForm.atFr (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w)
      (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hfun : (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) = z'.1 := by
      funext τ
      show _ = _ * _
      rw [hir τ]
    unfold GlobalTheory.AdForm.atFr
    rw [dite_eq_left (by rw [hfun]; exact z'.2)]
    congr 1
    exact Subtype.ext hfun
  refine Eq.trans (congrArg (fun t => ((F.cls0.lev.chi κ : ℂˣ) : ℂ) * t) hlhs) ?_

  have hT := T.2
  have hT1 := hT.1 (rieszJ tr (F.val0.eY y))
  have htoHaγ : B.toH aγ = (iotaI X u γ', iotaF X u γ') := Prod.ext hγ'1.symm hγ'2.symm
  have hdec : B.toH r = ((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'') := by
    ext
    · simp
    · simp [hκ'']
  have eR : B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) =
      ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hx1 : B.toH (g * a₀⁻¹) = (iotaI X u γ', iotaF X u γ') *
        (((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'')) :=
      (congrArg B.toH hg).trans ((toH_mul B aγ r).trans (congrArg₂ (· * ·) htoHaγ hdec))
    unfold SBes.colForm
    rewrite [hx1, hT1.1 γ', hT1.2 _ ⟨κ'', hmem⟩]
    have h3 := hT.2 (B.toH r).1 (rieszJ tr (F.val0.eY y)) ((1 : Hinf X u), tr.hc c)
    have h4 := Formalism.L2.SG.ColDict.inner_shP X u T.1 (tr.hc c) (rieszJ tr z')
    have h5 := inner_rieszJ tr z' (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c))
    have h6 := congrArg (fun v => T.1 v ((1 : Hinf X u), tr.hc c)) hriesz
    refine congrArg (fun t => ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * t) ?_
    exact h3.symm.trans (h6.trans (h4.symm.trans h5))
  refine Eq.trans ?_ eR.symm
  exact congrArg (fun t => t * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z') (hchi.symm.trans hpsiv.symm)

end GlobalTheory.Core.Mi

theorem GlobalTheory.Core.Mi.colDict_rd_eq_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0)), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → Formalism.L2.SG.ColDict.LevelMatch X tr hK → ∃ ξ : (D.mem u).C.Y 0 → X.Vpi u, Submodule.span ℂ (Set.range ξ) = ⊤ ∧ ∀ (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0)), (chart0 F).rd θ (Formalism.L2.SG.ColDict.colDictL X tr hK T) y g = B.colForm T.1 (ξ y) (g * a₀⁻¹) := by
  intro D X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM
  refine ⟨fun y => GlobalTheory.Core.Mi.rieszJ tr (F.val0.eY y), GlobalTheory.Core.Mi.span_rieszJ tr, ?_⟩
  intro T y g
  unfold GlobalTheory.AdForm.Chart.rd chart0 GlobalTheory.AdForm.rdS
  simp only
  have hd : ∃ p, GlobalTheory.AdForm.IsDec F.cls0.toChart.lev F.cls0.toChart.y
      (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p := GlobalTheory.T.exists_rationalRepLevelDecomposition_finiteUnitary D u F g
  rw [dite_eq_left hd]
  have hfe : (fun z => Formalism.L2.SG.ColDict.colDictL X tr hK T (id hd.choose.1) (F.val0.eY.symm z)) =
      (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc hd.choose.1)) w) :=
    funext (GlobalTheory.Core.Mi.colDictL_eY_symm tr hK T hd.choose.1)
  rw [hfe]
  exact GlobalTheory.Core.Mi.colForm_of_dec X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM T y g hd.choose.1 hd.choose.2.1 hd.choose.2.2
    hd.choose_spec.1 hd.choose_spec.2

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.maximal_compact_sorted_frame_acts_through_model_compact : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (hV : V.SigOK) (k : GA D V), IsInfFam θ → k ∈ GlobalTheory.Cusp.Kinf θ V (GlobalTheory.ChainOnto.RealData.sortedFrame M hV) → ∀ τ, M.fr τ * infMat D.sp.cm.sig V.gram (θ τ) k * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
  first | exact @GlobalTheory.ChainOnto.RealData.conj_mem_Kset_of_mem_Kinf | exact GlobalTheory.ChainOnto.RealData.conj_mem_Kset_of_mem_Kinf | (intros; apply GlobalTheory.ChainOnto.RealData.conj_mem_Kset_of_mem_Kinf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

namespace GlobalTheory.NrmVol

theorem suppQ_eq_valuative : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r = {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin r) : Set (GL (Fin r) (Fv D.host.F v))) ∧ (∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation (Fv D.host.F v) (x i j) < 1} ∧ {y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ 1} = {x | ∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1} := by
  intro D v a b r
  have hC : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE : (ValuativeRel.valuation (Fv D.host.F v)).IsEquiv
      (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have hle : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z ≤ 1 ↔ Valued.v z ≤ 1 :=
    fun z => hE.le_one_iff_le_one
  have hlt : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z < 1 ↔ Valued.v z < 1 :=
    fun z => hE.lt_one_iff_lt_one
  have heq : ∀ z : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) z = 1 ↔ Valued.v z = 1 :=
    fun z => hE.eq_one_iff_eq_one
  have htop : ∀ (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (i j : Fin r),
      topL r x i j = 0 ∨ ∃ i' j', topL r x i j = x i' j' := by
    intro x i j
    unfold topL
    split_ifs with h
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl rfl
  refine ⟨?_, ?_⟩
  · ext x
    simp only [suppQ, Set.mem_setOf_eq, GlobalTheory.ParahoricConjBlocks.mem_KO_val_iff,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · rintro ⟨-, hdet, hint, hlow⟩
      refine ⟨⟨fun i j => ?_, (heq _).2 hdet⟩, fun i j => (hle _).2 (hint i j),
        fun i j hi hj => (hlt _).2 (hlow i j hi hj)⟩
      rcases htop x i j with h | ⟨i', j', h⟩
      · rw [h, map_zero]; exact zero_le_one
      · rw [h]; exact (hle _).2 (hint i' j')
    · rintro ⟨⟨-, hdet⟩, hint, hlow⟩
      have hd : Valued.v (topL r x).det = 1 := (heq _).1 hdet
      refine ⟨?_, hd, fun i j => (hle _).1 (hint i j), fun i j hi hj => (hlt _).1 (hlow i j hi hj)⟩
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      rw [h0, map_zero] at hd
      exact zero_ne_one hd
  · ext y
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => (hle _).symm

end GlobalTheory.NrmVol
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

namespace GlobalTheory.HypSumWitt

open scoped ComplexOrder

theorem gramAt_hypSp (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ =
      (Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  unfold gramAt
  rw [GlobalTheory.Doubling.gram_hdbl]
  ext i j
  simp [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, GlobalTheory.OrthSumSp.posSp_gram]
  generalize finSumFinEquiv.symm i = a
  generalize finSumFinEquiv.symm j = b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, apply_ite]

theorem gsq (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ * gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ = 1 := by
  rw [gramAt_hypSp, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem gct (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    (gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ)ᴴ = gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ := by
  rw [gramAt_hypSp, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  simp

theorem exists_hypSum_orthDec_hypDec : ∀ (D : D7) (W : HSp D) (t : ℕ), HSpace.SigOK W → ∃ (H B : HSp D) (_ : OrthDec B W H) (_ : HypDec B W t), HSpace.SigOK H ∧ HSpace.SigOK B ∧ H.rank = 2 * t ∧ (∀ τ, H.sig τ = (t, t)) ∧ ∃ sH : RealMat H, ∀ τ, IsCartanInv (gramAt D H τ) (sH τ) := by
  intro D W t hW
  refine ⟨GlobalTheory.OrthSumSp.hypSp D t, _, GlobalTheory.OrthSumSp.orthSumDec D W _, GlobalTheory.OrthSumSp.hypSumDec D W t,
    GlobalTheory.OrthSumSp.hypSp_sigOK D t, GlobalTheory.Doubling.sigOK_hsum hW (GlobalTheory.OrthSumSp.hypSp_sigOK D t), ?_,
    GlobalTheory.OrthSumSp.hypSp_sig D t, fun τ => gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ, fun τ => ⟨gsq D t τ, ?_, ?_⟩⟩
  · show t + t = 2 * t; omega
  · rw [gct, Matrix.mul_assoc, gsq, Matrix.mul_one]
  · rw [gsq]; exact Matrix.PosDef.one
end GlobalTheory.HypSumWitt
end
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SW

theorem keepsDiag_of_mul_stkRows_one {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    {β : Matrix (Fin n) (Fin n) R} (h : M * stkRows 1 1 = stkRows β β) : KeepsDiag finSumFinEquiv M := by
  rw [keepsDiag_iff]
  have key : ∀ s : Fin n ⊕ Fin n, ∀ j, M (finSumFinEquiv s) (finSumFinEquiv (Sum.inl j)) +
      M (finSumFinEquiv s) (finSumFinEquiv (Sum.inr j)) = β (s.elim id id) j := by
    intro s j
    have h1 : ∑ k, M (finSumFinEquiv s) k * stkRows (1 : Matrix (Fin n) (Fin n) R) 1 k j =
        stkRows β β (finSumFinEquiv s) j := congrFun (congrFun h _) j
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at h1
    simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    rw [h1]
    rcases s with s | s <;> rfl
  intro i j
  rw [key (Sum.inr i), key (Sum.inl i)]
  rfl

variable {D : D7}

section Core

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

end Core

end GlobalTheory.Core.Rk.SW
end
end
